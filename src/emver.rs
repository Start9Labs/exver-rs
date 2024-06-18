use std::cmp::Ordering;
use std::fmt;
use std::ops::Deref;

use either::Either;
use fp_core::empty::Empty;
use fp_core::monoid::Monoid;
use fp_core::semigroup::Semigroup;
use itertools::EitherOrBoth;
use itertools::Itertools;

use pest::iterators::Pair;
use pest::iterators::Pairs;
use pest::Parser;
use pest_derive::Parser;
use yasi::InternedString;

#[derive(Clone, Debug)]
pub enum ParseError {
    InvalidVersion(String, &'static str),
    InvalidVersionRange(String, Option<pest::error::Error<Rule>>),
}
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::InvalidVersion(input, reason) => {
                write!(f, "Parse Error: {input:?} is not a valid Version: {reason}")
            }
            ParseError::InvalidVersionRange(input, error) => {
                write!(f, "Parse Error: {input:?} is not a valid VersionRange")?;
                if let Some(error) = error {
                    write!(f, ": {error}")?;
                }
                Ok(())
            }
        }
    }
}
impl std::error::Error for ParseError {}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Version {
    flavor: Option<InternedString>,
    major: usize,
    minor: usize,
    patch: usize,
    revision: usize,
    prerelease: Vec<Either<InternedString, usize>>,
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(flavor) = &self.flavor {
            write!(f, "{flavor}-")?;
        }
        if self.revision == 0 {
            write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
        } else {
            write!(
                f,
                "{}.{}.{}.{}",
                self.major, self.minor, self.patch, self.revision
            )?;
        }
        if !self.prerelease.is_empty() {
            write!(f, "-")?;
            for seg in itertools::Itertools::intersperse(
                self.prerelease
                    .iter()
                    .map(|a| a.as_ref().map_left(|a| a.as_ref())),
                Either::Left("."),
            ) {
                match seg {
                    Either::Left(a) => write!(f, "{a}"),
                    Either::Right(a) => write!(f, "{a}"),
                }?;
            }
        }
        Ok(())
    }
}
impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.flavor == other.flavor {
            Some(match self.major.cmp(&other.major) {
                Ordering::Equal => match self.minor.cmp(&other.minor) {
                    Ordering::Equal => match self.patch.cmp(&other.patch) {
                        Ordering::Equal => {
                            match (self.prerelease.is_empty(), other.prerelease.is_empty()) {
                                (true, true) => Ordering::Equal,
                                (true, false) => Ordering::Greater,
                                (false, true) => Ordering::Less,
                                (false, false) => {
                                    for pair in
                                        self.prerelease.iter().zip_longest(other.prerelease.iter())
                                    {
                                        match pair {
                                            EitherOrBoth::Left(_) => {
                                                return Some(Ordering::Greater)
                                            }
                                            EitherOrBoth::Right(_) => return Some(Ordering::Less),
                                            EitherOrBoth::Both(
                                                Either::Left(_),
                                                Either::Right(_),
                                            ) => return Some(Ordering::Greater),
                                            EitherOrBoth::Both(
                                                Either::Right(_),
                                                Either::Left(_),
                                            ) => return Some(Ordering::Less),
                                            EitherOrBoth::Both(
                                                Either::Left(l),
                                                Either::Left(r),
                                            ) => match l.cmp(r) {
                                                Ordering::Equal => (),
                                                a => return Some(a),
                                            },
                                            EitherOrBoth::Both(
                                                Either::Right(l),
                                                Either::Right(r),
                                            ) => match l.cmp(r) {
                                                Ordering::Equal => (),
                                                a => return Some(a),
                                            },
                                        }
                                    }
                                    Ordering::Equal
                                }
                            }
                        }
                        a => a,
                    },
                    a => a,
                },
                a => a,
            })
        } else {
            None
        }
    }
}
impl Default for Version {
    fn default() -> Self {
        Self {
            flavor: None,
            major: 0,
            minor: 0,
            patch: 0,
            revision: 0,
            prerelease: Vec::new(),
        }
    }
}
impl std::str::FromStr for Version {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let err_fn = |reason| ParseError::InvalidVersion(s.to_owned(), reason);
        let (flavor, s) = s
            .split_once("-")
            .filter(|(f, _)| f.chars().all(|c| c.is_ascii_lowercase()))
            .map_or((None, s), |(f, s)| (Some(f), s));
        let (version, s) = s.split_once("-").map_or((s, None), |(v, s)| (v, Some(s)));
        let mut v_iter = version.split(".");
        let [major, minor, patch, revision] = (&mut v_iter)
            .map(|v| v.parse::<usize>())
            .chain(std::iter::repeat(Ok(0)))
            .take(4)
            .collect::<Result<Vec<_>, _>>() // TODO: std::array::try_from_fn when stable
            .map_err(|_| err_fn("invalid numeric identifier"))?[..]
        else {
            return Err(err_fn("UNREACHABLE"));
        };
        if v_iter.next().is_some() {
            return Err(err_fn("too many segments"));
        }
        let prerelease = s
            .map(|s| {
                s.split(".")
                    .map(|seg| {
                        if seg.is_empty() {
                            Err(err_fn("prerelease identifier may not be empty"))
                        } else if seg.chars().all(|c| c.is_ascii_digit()) {
                            if seg.chars().next().unwrap() == '0' {
                                Err(err_fn(
                                    "numeric prerelease identifier may not have leading zero",
                                ))
                            } else {
                                Ok(Either::Right(
                                    seg.parse()
                                        .map_err(|_| err_fn("invalid numeric identifier"))?,
                                ))
                            }
                        } else if let Some(_c) = seg
                            .chars()
                            .find(|c| !matches!(c, '0'..='9'|'a'..='z'|'A'..='Z'|'-'))
                        {
                            Err(err_fn("invalid character in prerelease identifier"))
                        } else {
                            Ok(Either::Left(seg.into()))
                        }
                    })
                    .collect::<Result<_, _>>()
            })
            .transpose()?
            .unwrap_or_default();
        Ok(Self {
            flavor: flavor.map(From::from),
            major,
            minor,
            patch,
            revision,
            prerelease,
        })
    }
}
#[cfg(feature = "serde")]
impl serde::Serialize for Version {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&format!("{}", self))
    }
}
#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Version {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        s.parse().map_err(serde::de::Error::custom)
    }
}

impl Version {
    pub const fn new(major: usize, minor: usize, patch: usize, revision: usize) -> Self {
        Self {
            flavor: None,
            major,
            minor,
            patch,
            revision,
            prerelease: Vec::new(),
        }
    }

    pub fn with_flavor(mut self, flavor: impl Into<InternedString>) -> Self {
        self.flavor = Some(flavor.into());
        self
    }

    pub fn without_flavor(mut self) -> Self {
        self.flavor = None;
        self
    }

    pub fn with_prerelease_string(mut self, prerelease: impl Into<InternedString>) -> Self {
        self.prerelease.push(Either::Left(prerelease.into()));
        self
    }

    pub fn with_prerelease_number(mut self, prerelease: usize) -> Self {
        self.prerelease.push(Either::Right(prerelease));
        self
    }

    pub fn without_prerelease(mut self) -> Self {
        self.prerelease = Vec::new();
        self
    }

    pub fn flavor(&self) -> Option<&str> {
        self.flavor.as_deref()
    }

    /// A change in the value found at 'major' implies a breaking change in the API that this version number describes
    pub fn major(&self) -> usize {
        self.major
    }

    /// A change in the value found at 'minor' implies a backwards compatible addition to the API that this version
    /// number describes
    pub fn minor(&self) -> usize {
        self.minor
    }

    /// A change in the value found at 'patch' implies that the implementation of the API has changed without changing
    /// the invariants promised by the API. In many cases this will be incremented when repairing broken functionality
    pub fn patch(&self) -> usize {
        self.patch
    }

    /// This is the fundamentally new value in comparison to the original semver 2.0 specification. It is given the same
    /// semantics as 'patch' above, which begs the question, when should you update this value instead of that one.
    /// Generally speaking, if you are both the package author and maintainer, you should not ever increment this number,
    /// as it is redundant with 'patch'. However, if you maintain a package on some distribution channel, and you are
    /// /not/ the original author, then it is encouraged for you to increment 'revision' instead of 'patch'.
    pub fn revision(&self) -> usize {
        self.revision
    }

    pub fn prerelease(&self) -> Option<String> {
        if self.prerelease.is_empty() {
            None
        } else {
            Some(self.prerelease.iter().join("."))
        }
    }

    /// Predicate for deciding whether the 'Version' is in the 'VersionRange'
    pub fn satisfies(&self, spec: &VersionRange) -> bool {
        use VersionRange::*;
        match spec {
            Anchor(op, v) => {
                if let Some(cmp) = self.partial_cmp(v) {
                    match op {
                        Ok(c) => &cmp == c,
                        Err(c) => &cmp != c,
                    }
                } else {
                    if op == &NEQ {
                        true
                    } else {
                        false
                    }
                }
            }
            And(a, b) => self.satisfies(a) && self.satisfies(b),
            Or(a, b) => self.satisfies(a) || self.satisfies(b),
            Not(a) => !self.satisfies(a),
            Any => true,
            None => false,
        }
    }
}

// Left is inversion, Right is identity
type Invertable<T> = Result<T, T>;
pub type Operator = Invertable<Ordering>;
pub const GTE: Operator = Err(Ordering::Less);
pub const LT: Operator = Ok(Ordering::Less);
pub const NEQ: Operator = Err(Ordering::Equal);
pub const EQ: Operator = Ok(Ordering::Equal);
pub const LTE: Operator = Err(Ordering::Greater);
pub const GT: Operator = Ok(Ordering::Greater);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VersionRange {
    Anchor(Operator, Version),
    And(Box<VersionRange>, Box<VersionRange>),
    Or(Box<VersionRange>, Box<VersionRange>),
    Not(Box<VersionRange>),
    Any,
    None,
}
impl VersionRange {
    /// satisfied by any version
    pub fn any() -> Self {
        Self::Any
    }
    /// unsatisfiable
    pub fn none() -> Self {
        Self::None
    }
    /// defined in relation to a specific version
    pub fn anchor(op: Operator, version: Version) -> Self {
        Self::Anchor(op, version)
    }

    pub fn caret(version: Version) -> Self {
        if version.major > 0 {
            let max = Version {
                flavor: version.flavor.clone(),
                major: version.major + 1,
                minor: 0,
                patch: 0,
                revision: 0,
                prerelease: Vec::new(),
            };
            Self::and(Self::anchor(GTE, version), Self::anchor(LT, max))
        } else if version.minor > 0 {
            let max = Version {
                flavor: version.flavor.clone(),
                major: 0,
                minor: version.minor + 1,
                patch: 0,
                revision: 0,
                prerelease: Vec::new(),
            };
            Self::and(Self::anchor(GTE, version), Self::anchor(LT, max))
        } else if version.patch > 0 {
            let max = Version {
                flavor: version.flavor.clone(),
                major: 0,
                minor: 0,
                patch: version.patch + 1,
                revision: 0,
                prerelease: Vec::new(),
            };
            Self::and(Self::anchor(GTE, version), Self::anchor(LT, max))
        } else {
            let max = Version {
                flavor: version.flavor.clone(),
                major: 0,
                minor: 0,
                patch: 0,
                revision: version.revision + 1,
                prerelease: Vec::new(),
            };
            Self::and(Self::anchor(GTE, version), Self::anchor(LT, max))
        }
    }

    pub fn tilde(version: Version) -> Self {
        if version.major > 0 {
            let max = Version {
                flavor: version.flavor.clone(),
                major: version.major,
                minor: version.minor + 1,
                patch: 0,
                revision: 0,
                prerelease: Vec::new(),
            };
            Self::and(Self::anchor(GTE, version), Self::anchor(LT, max))
        } else if version.minor > 0 {
            let max = Version {
                flavor: version.flavor.clone(),
                major: 0,
                minor: version.minor,
                patch: version.patch + 1,
                revision: 0,
                prerelease: Vec::new(),
            };
            Self::and(Self::anchor(GTE, version), Self::anchor(LT, max))
        } else if version.patch > 0 {
            let max = Version {
                flavor: version.flavor.clone(),
                major: 0,
                minor: 0,
                patch: version.patch,
                revision: version.revision + 1,
                prerelease: Vec::new(),
            };
            Self::and(Self::anchor(GTE, version), Self::anchor(LT, max))
        } else {
            Self::anchor(EQ, version)
        }
    }

    /// smart constructor for And, eagerly evaluates identities and annihilators
    pub fn and(a: Self, b: Self) -> Self {
        use VersionRange::*;
        match (a, b) {
            (Any, b) => b,
            (a, Any) => a,
            (None, _) => None,
            (_, None) => None,
            (a, b) => And(Box::new(a), Box::new(b)),
        }
    }
    /// smart constructor for Or, eagerly evaluates identities and annihilators
    pub fn or(a: Self, b: Self) -> Self {
        use VersionRange::*;
        match (a, b) {
            (Any, _) => Any,
            (_, Any) => Any,
            (None, b) => b,
            (a, None) => a,
            (a, b) => Or(Box::new(a), Box::new(b)),
        }
    }

    pub fn not(a: Self) -> Self {
        use VersionRange::*;
        match a {
            Anchor(EQ, v) => Anchor(NEQ, v),
            Anchor(NEQ, v) => Anchor(EQ, v),
            And(a, b) => Or(Box::new(Self::not(*a)), Box::new(Self::not(*b))),
            Or(a, b) => And(Box::new(Self::not(*a)), Box::new(Self::not(*b))),
            Not(a) => *a,
            Any => None,
            None => Any,
            a => Not(Box::new(a)),
        }
    }

    pub fn exactly(a: Version) -> Self {
        Self::Anchor(EQ, a)
    }

    pub fn reduce(self) -> Self {
        use VersionRange::*;
        match self {
            And(a, b) => Self::and(*a, *b),
            Or(a, b) => Self::or(*a, *b),
            Not(a) => Self::not(*a),
            a => a,
        }
    }

    fn is_expr(&self) -> bool {
        match self {
            Self::Anchor(_, _) | Self::Any | Self::None => false,
            _ => true,
        }
    }

    fn write_with_parens(self: &Box<Self>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_expr() {
            write!(f, "({})", self.deref())
        } else {
            write!(f, "{}", self.deref())
        }
    }
}
impl Default for VersionRange {
    fn default() -> Self {
        VersionRange::Any
    }
}
impl fmt::Display for VersionRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use VersionRange::*;
        match self {
            Anchor(GTE, v) => write!(f, ">={}", v),
            Anchor(LT, v) => write!(f, "<{}", v),
            Anchor(NEQ, v) => write!(f, "!={}", v),
            Anchor(EQ, v) => write!(f, "={}", v), // this is equivalent to above
            Anchor(LTE, v) => write!(f, "<={}", v),
            Anchor(GT, v) => write!(f, ">{}", v),
            And(a, b) => {
                a.write_with_parens(f)?;
                write!(f, " ")?;
                b.write_with_parens(f)
            }
            Or(a, b) => {
                a.write_with_parens(f)?;
                write!(f, " || ")?;
                b.write_with_parens(f)
            }
            Not(a) => {
                write!(f, "!")?;
                a.write_with_parens(f)
            }
            Any => write!(f, "*"),
            None => write!(f, "!"),
        }
    }
}
impl std::str::FromStr for VersionRange {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_version_range(
            Grammar::parse(Rule::version_range, s)
                .map_err(|e| ParseError::InvalidVersionRange(s.into(), Some(e)))?
                .next()
                .unwrap(),
        )
    }
}
#[cfg(feature = "serde")]
impl serde::Serialize for VersionRange {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&format!("{}", self))
    }
}
#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for VersionRange {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = String::deserialize(deserializer)?;
        s.parse().map_err(serde::de::Error::custom)
    }
}

pub struct AnyRange(VersionRange);
impl Semigroup for AnyRange {
    fn combine(self, other: Self) -> Self {
        AnyRange(VersionRange::or(self.0, other.0))
    }
}
impl Empty for AnyRange {
    fn empty() -> Self {
        AnyRange(VersionRange::None)
    }
}
impl Monoid for AnyRange {}

pub struct AllRange(VersionRange);
impl Semigroup for AllRange {
    fn combine(self, other: Self) -> Self {
        AllRange(VersionRange::and(self.0, other.0))
    }
}
impl Empty for AllRange {
    fn empty() -> Self {
        AllRange(VersionRange::Any)
    }
}
impl Monoid for AllRange {}

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct Grammar;

fn parse_version_range<'i>(pair: Pair<'i, Rule>) -> Result<VersionRange, ParseError> {
    let input = pair.as_span().as_str();
    let mut prev = None;
    let mut op = None::<Pair<Rule>>;
    for tok in pair.into_inner() {
        match tok.as_rule() {
            Rule::version_range_atom => {
                let atom = parse_version_range_atom(tok)?;
                if let Some(p) = prev.take() {
                    if op
                        .as_ref()
                        .map_or(false, |op| matches!(op.as_rule(), Rule::or))
                    {
                        prev = Some(VersionRange::or(p, atom));
                    } else {
                        prev = Some(VersionRange::and(p, atom));
                    }
                } else {
                    prev = Some(atom);
                }
            }
            Rule::or | Rule::and => {
                op = Some(tok);
            }
            _ => (),
        }
    }
    prev.ok_or_else(|| ParseError::InvalidVersionRange(input.to_owned(), None))
}

fn parse_version_range_atom(pair: Pair<Rule>) -> Result<VersionRange, ParseError> {
    let input = pair.as_span().as_str();
    for tok in pair.into_inner() {
        match tok.as_rule() {
            Rule::version_range => return parse_version_range(tok),
            Rule::anchor => return parse_anchor(tok),
            Rule::not => return parse_not(tok),
            Rule::any => return Ok(VersionRange::Any),
            Rule::none => return Ok(VersionRange::None),
            _ => (),
        }
    }
    Err(ParseError::InvalidVersionRange(input.to_owned(), None))
}

fn parse_anchor(pair: Pair<Rule>) -> Result<VersionRange, ParseError> {
    let input = pair.as_span().as_str();
    let err_fn = || ParseError::InvalidVersionRange(input.to_owned(), None);

    let mut op = Rule::caret;
    let mut version = None;

    for tok in pair.into_inner() {
        match tok.as_rule() {
            Rule::cmp_op => {
                op = tok.into_inner().next().ok_or_else(err_fn)?.as_rule();
            }
            Rule::version => version = Some(tok.as_span().as_str().trim().parse()?),
            _ => (),
        }
    }

    let version = version.ok_or_else(err_fn)?;
    Ok(match op {
        Rule::caret => VersionRange::caret(version),
        Rule::tilde => VersionRange::tilde(version),
        Rule::gte => VersionRange::anchor(GTE, version),
        Rule::lt => VersionRange::anchor(LT, version),
        Rule::neq => VersionRange::anchor(NEQ, version),
        Rule::eq => VersionRange::anchor(EQ, version),
        Rule::lte => VersionRange::anchor(LTE, version),
        Rule::gt => VersionRange::anchor(GT, version),
        _ => return Err(err_fn()),
    })
}

fn parse_not(pair: Pair<Rule>) -> Result<VersionRange, ParseError> {
    let input = pair.as_span().as_str();
    for tok in pair.into_inner() {
        match tok.as_rule() {
            Rule::version_range_atom => {
                return Ok(VersionRange::not(parse_version_range_atom(tok)?))
            }
            _ => (),
        }
    }
    Err(ParseError::InvalidVersionRange(input.to_owned(), None))
}

#[cfg(test)]
mod test {
    use crate::emver::*;
    use proptest::prelude::*;

    prop_compose! {
        fn flavor_gen()(
            has_flavor in any::<bool>(),
            flavor in "[a-z]+"
        ) -> Option<InternedString> {
            if has_flavor {
                Some(flavor.into())
            } else {
                None
            }
        }
    }

    prop_compose! {
        fn prerelease_string()(
            string in "[a-zA-Z0-9-]+"
        ) -> Either<InternedString, usize> {
            if string.chars().all(|c| c.is_ascii_digit()) {
                Either::Right(string.parse().unwrap())
            } else {
                Either::Left(string.into())
            }
        }
    }

    prop_compose! {
        fn version_gen()(
            flavor in flavor_gen(),
            major in any::<usize>(),
            minor in any::<usize>(),
            patch in any::<usize>(),
            revision in any::<usize>(),
            prerelease in prop::collection::vec(prop_oneof![
                any::<usize>().prop_map(Either::Right),
                prerelease_string(),
            ], 0..3),
        ) -> Version {
            Version { flavor, major, minor, patch, revision, prerelease }
        }
    }

    prop_compose! {
        fn anchor_gen()(op in prop_oneof![Just(LT), Just(LTE), Just(EQ), Just(NEQ), Just(GT), Just(GTE)], v in version_gen()) -> VersionRange {
            VersionRange::anchor(op, v)
        }
    }

    prop_compose! {
        fn and_gen(inner: impl Strategy<Value = VersionRange> + Clone)(a in inner.clone(), b in inner) -> VersionRange {
            VersionRange::and(a, b)
        }
    }

    prop_compose! {
        fn or_gen(inner: impl Strategy<Value = VersionRange> + Clone)(a in inner.clone(), b in inner) -> VersionRange {
            VersionRange::or(a,b)
        }
    }

    fn range_gen() -> BoxedStrategy<VersionRange> {
        let leaf = prop_oneof![
            Just(VersionRange::Any),
            Just(VersionRange::None),
            anchor_gen()
        ];
        leaf.prop_recursive(4, 16, 10, |inner| {
            prop_oneof![and_gen(inner.clone()), or_gen(inner),]
        })
        .prop_map(|a| dbg!(a))
        .boxed()
    }

    proptest! {

        #[test]
        fn and_assoc(a in range_gen(), b in range_gen(), c in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::and(a.clone(), VersionRange::and(b.clone(),c.clone()))) == obs.satisfies(&VersionRange::and(VersionRange::and(a,b),c)))
        }

    }
    proptest! {
        #[test]
        fn and_commut(a in range_gen(), b in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::and(a.clone(),b.clone())) == obs.satisfies(&VersionRange::and(b, a)))
        }
    }

    proptest! {
        #[test]
        fn or_assoc(a in range_gen(), b in range_gen(), c in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::or(a.clone(), VersionRange::or(b.clone(), c.clone()))) == obs.satisfies(&VersionRange::or(VersionRange::or(a, b), c)))
        }
    }

    proptest! {
        #[test]
        fn or_commut(a in range_gen(), b in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::or(a.clone(), b.clone())) == obs.satisfies(&VersionRange::or(b.clone(), a.clone())))
        }
    }

    proptest! {
        #[test]
        fn any_ident_and(a in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&a) == obs.satisfies(&VersionRange::and(VersionRange::Any, a)))
        }
    }

    proptest! {
        #[test]
        fn none_ident_or(a in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&a) == obs.satisfies(&VersionRange::or(VersionRange::None, a)))
        }
    }

    proptest! {
        #[test]
        fn none_annihilates_and(a in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::and(VersionRange::None, a)) == obs.satisfies(&VersionRange::None))
        }
    }

    proptest! {
        #[test]
        fn any_annihilates_or(a in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::or(VersionRange::Any, a)) == obs.satisfies(&VersionRange::Any))
        }
    }

    proptest! {
        #[test]
        fn and_distributes_over_or(a in range_gen(), b in range_gen(), c in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::and(a.clone(), VersionRange::or(b.clone(),c.clone()))) == obs.satisfies(&VersionRange::or(VersionRange::and(a.clone(),b),VersionRange::and(a,c))))
        }
    }

    proptest! {
        #[test]
        fn or_distributes_over_and(a in range_gen(), b in range_gen(), c in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::or(a.clone(), VersionRange::and(b.clone(),c.clone()))) == obs.satisfies(&VersionRange::and(VersionRange::or(a.clone(),b),VersionRange::or(a,c))))
        }
    }

    proptest! {
        #[test]
        fn any_accepts_any(obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::Any))
        }
    }

    proptest! {
        #[test]
        fn none_accepts_none(obs in version_gen()) {
            assert!(!obs.satisfies(&VersionRange::None))
        }
    }

    proptest! {
        #[test]
        fn and_both(a in range_gen(), b in range_gen(), obs in version_gen()) {
            assert!((obs.satisfies(&a) && obs.satisfies(&b)) == obs.satisfies(&VersionRange::and(a,b)))
        }
    }

    proptest! {
        #[test]
        fn or_either(a in range_gen(), b in range_gen(), obs in version_gen()) {
            assert!((obs.satisfies(&a) || obs.satisfies(&b)) == obs.satisfies(&VersionRange::or(a,b)))
        }
    }

    proptest! {
        #[test]
        fn range_parse_round_trip (a in range_gen(), obs in version_gen()) {
            // println!("{:?}", a);
            match a.to_string().parse::<VersionRange>() {
                Ok(range) => {
                    assert!(obs.satisfies(&a) == obs.satisfies(&range));
                }
                Err(e) => panic!("parse after display failed {}", e),
            }
        }
    }

    #[test]
    fn caret() {
        let thing = "(^1.2.3.4 || ~2.3.4) 0.0.0-2.1.3 || 1.2.x"
            .parse::<VersionRange>()
            .map_err(|e| eprintln!("{e}"))
            .unwrap();
        println!("{}", thing);
        // match parse_atom(b"<0.0.0") {
        // Ok(a) => println!("{:#?}", a),
        // Err(e) => println!("{}", e),
        // }
        // use nom::bytes::complete::tag;
        // use nom::multi::separated_list;
        // println!("{:?}", parse_range(b"=0.0.0"));
        // println!("{:?}", decimal(b"1234"));
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deser() {
        let v: Version = serde_yaml::from_str("---\n0.2.5\n").unwrap();
    }
}
