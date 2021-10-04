use std::cmp::Ordering;
use std::fmt;
use std::ops::Deref;

use either::Either::{self, *};
use fp_core::empty::Empty;
use fp_core::monoid::Monoid;
use fp_core::semigroup::Semigroup;
use nom::character::complete::digit1;
use nom::character::complete::space0;
use nom::character::complete::space1;

use VersionRange::*;

#[derive(Clone, Debug)]
pub enum ParseError {
    InvalidVersion(String),
    InvalidVersionRange(String),
}
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::InvalidVersion(input) => {
                write!(f, "Parse Error: {:?} is not a valid Version", input)
            }
            ParseError::InvalidVersionRange(input) => {
                write!(f, "Parse Error: {:?} is not a valid VersionRange", input)
            }
        }
    }
}
impl std::error::Error for ParseError {}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub struct Version(usize, usize, usize, usize);

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.3 {
            0 => write!(f, "{}.{}.{}", self.0, self.1, self.2),
            n => write!(f, "{}.{}.{}.{}", self.0, self.1, self.2, n),
        }
    }
}
impl Default for Version {
    fn default() -> Self {
        Version(0, 0, 0, 0)
    }
}
impl std::str::FromStr for Version {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_version(s.as_bytes())
            .map(|a| a.1)
            .map_err(|_| ParseError::InvalidVersion(s.into()))
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
        Version(major, minor, patch, revision)
    }

    /// A change in the value found at 'major' implies a breaking change in the API that this version number describes
    pub fn major(&self) -> usize {
        self.0
    }
    /// A change in the value found at 'minor' implies a backwards compatible addition to the API that this version
    /// number describes
    pub fn minor(&self) -> usize {
        self.1
    }
    /// A change in the value found at 'patch' implies that the implementation of the API has changed without changing
    /// the invariants promised by the API. In many cases this will be incremented when repairing broken functionality
    pub fn patch(&self) -> usize {
        self.2
    }
    /// This is the fundamentally new value in comparison to the original semver 2.0 specification. It is given the same
    /// semantics as 'patch' above, which begs the question, when should you update this value instead of that one.
    /// Generally speaking, if you are both the package author and maintainer, you should not ever increment this number,
    /// as it is redundant with 'patch'. However, if you maintain a package on some distribution channel, and you are
    /// /not/ the original author, then it is encouraged for you to increment 'revision' instead of 'patch'.
    pub fn revision(&self) -> usize {
        self.3
    }

    /// Predicate for deciding whether the 'Version' is in the 'VersionRange'
    pub fn satisfies(&self, spec: &VersionRange) -> bool {
        match spec {
            Anchor(op, v) => {
                let pos = |c| -> Box<dyn FnOnce(&Version, &Version) -> bool> {
                    Box::new(move |x, y| Version::cmp(x, y) == c)
                };
                let neg = |c| -> Box<dyn FnOnce(&Version, &Version) -> bool> {
                    Box::new(move |x, y| Version::cmp(x, y) != c)
                };
                op.either(neg, pos)(self, v)
            }
            Conj(a, b) => self.satisfies(a) && self.satisfies(b),
            Disj(a, b) => self.satisfies(a) || self.satisfies(b),
            Any => true,
            None => false,
        }
    }
}

// Left is inversion, Right is identity
type Negatable<T> = Either<T, T>;
pub type Operator = Negatable<Ordering>;
pub const GTE: Operator = Left(Ordering::Less);
pub const LT: Operator = Right(Ordering::Less);
pub const NEQ: Operator = Left(Ordering::Equal);
pub const EQ: Operator = Right(Ordering::Equal);
pub const LTE: Operator = Left(Ordering::Greater);
pub const GT: Operator = Right(Ordering::Greater);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VersionRange {
    Anchor(Operator, Version),
    Conj(Box<VersionRange>, Box<VersionRange>),
    Disj(Box<VersionRange>, Box<VersionRange>),
    Any,
    None,
}
impl VersionRange {
    /// satisfied by any version
    pub fn any() -> Self {
        VersionRange::Any
    }
    /// unsatisfiable
    pub fn none() -> Self {
        VersionRange::None
    }
    /// defined in relation to a specific version
    pub fn anchor(op: Operator, version: Version) -> Self {
        VersionRange::Anchor(op, version)
    }
    /// smart constructor for Conj, eagerly evaluates identities and annihilators
    pub fn conj(a: VersionRange, b: VersionRange) -> Self {
        match (a, b) {
            (Any, b) => b,
            (a, Any) => a,
            (None, _) => None,
            (_, None) => None,
            (a, b) => Conj(Box::new(a), Box::new(b)),
        }
    }
    /// smart constructor for Disj, eagerly evaluates identities and annihilators
    pub fn disj(a: VersionRange, b: VersionRange) -> Self {
        match (a, b) {
            (Any, _) => Any,
            (_, Any) => Any,
            (None, b) => b,
            (a, None) => a,
            (a, b) => Disj(Box::new(a), Box::new(b)),
        }
    }
}
impl Default for VersionRange {
    fn default() -> Self {
        Any
    }
}
impl fmt::Display for VersionRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Anchor(Left(Ordering::Less), v) => write!(f, ">={}", v),
            Anchor(Right(Ordering::Less), v) => write!(f, "<{}", v),
            Anchor(Left(Ordering::Equal), v) => write!(f, "!={}", v),
            Anchor(Right(Ordering::Equal), v) => write!(f, "={}", v), // this is equivalent to above
            Anchor(Left(Ordering::Greater), v) => write!(f, "<={}", v),
            Anchor(Right(Ordering::Greater), v) => write!(f, ">{}", v),
            Conj(a, b) => match (a.deref(), b.deref()) {
                (Disj(_, _), Disj(_, _)) => write!(f, "({}) ({})", a, b),
                (Disj(_, _), _) => write!(f, "({}) {}", a, b),
                (_, Disj(_, _)) => write!(f, "{} ({})", a, b),
                (_, _) => write!(f, "{} {}", a, b),
            },
            Disj(a, b) => write!(f, "{} || {}", a, b),
            Any => write!(f, "*"),
            None => write!(f, "!"),
        }
    }
}
impl std::str::FromStr for VersionRange {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_range(s.as_bytes())
            .map(|a| a.1)
            .map_err(|_| ParseError::InvalidVersionRange(s.into()))
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
        AnyRange(VersionRange::disj(self.0, other.0))
    }
}
impl Empty for AnyRange {
    fn empty() -> Self {
        AnyRange(None)
    }
}
impl Monoid for AnyRange {}

pub struct AllRange(VersionRange);
impl Semigroup for AllRange {
    fn combine(self, other: Self) -> Self {
        AllRange(VersionRange::conj(self.0, other.0))
    }
}
impl Empty for AllRange {
    fn empty() -> Self {
        AllRange(Any)
    }
}
impl Monoid for AllRange {}

pub fn exactly(a: Version) -> VersionRange {
    Anchor(Left(Ordering::Equal), a)
}

named!(
    decimal<usize>,
    map_res!(
        map_res!(complete!(digit1), std::str::from_utf8),
        |s: &str| s.parse::<usize>()
    )
);

// fn check_length_out_of_band_cause_its_the_stone_age (i: &[u8], )
// named!(
//     minimal<Vec<char>>,
//     map_res!(
//         separated_list!(
//             nom::bytes::complete::tag("."),
//             nom::bytes::complete::tag("0")
//         ),
//         |ls: Vec<_>| Ok::<_, ()>(ls.into_iter().map(|_| '0').collect())
//     )
// );

named!(
    parse_version<Version>,
    map_res!(
        separated_list1!(complete!(char!('.')), decimal),
        |ls: Vec<usize>| {
            match &ls[..] {
                [a, b, c, d] => Ok(Version(*a, *b, *c, *d)),
                [a, b, c] => Ok(Version(*a, *b, *c, 0)),
                [a, b] => Ok(Version(*a, *b, 0, 0)),
                [a] => Ok(Version(*a, 0, 0, 0)),
                _ => Err(()),
            }
        }
    )
);

named!(
    parse_range<VersionRange>,
    alt!(sum | map!(char!('*'), |_| Any))
);

named!(
    sub<VersionRange>,
    delimited!(
        terminated!(char!('('), space0),
        parse_range,
        preceded!(space0, char!(')'))
    )
);

named!(
    sum<VersionRange>,
    do_parse!(
        ls: separated_list1!(
            complete!(delimited!(space0, tag!("||"), space0)),
            alt!(product | sub)
        ) >> (ls
            .into_iter()
            .map(|x| AnyRange(x))
            .fold(AnyRange::empty(), |a, b| a.combine(b))
            .0)
    )
);

named!(
    product<VersionRange>,
    do_parse!(
        ls: separated_list1!(complete!(space1), alt!(parse_atom | sub))
            >> (ls
                .into_iter()
                .map(|x| AllRange(x))
                .fold(AllRange::empty(), |a, b| a.combine(b))
                .0)
    )
);

named!(
    parse_operator<Operator>,
    alt!(
        map!(complete!(char!('=')), |_| EQ)
            | map!(complete!(tag!(">=")), |_| GTE)
            | map!(complete!(tag!("<=")), |_| LTE)
            | map!(complete!(char!('>')), |_| GT)
            | map!(complete!(char!('<')), |_| LT)
            | map!(complete!(tag!("!=")), |_| NEQ)
    )
);

named!(
    parse_atom<VersionRange>,
    alt!(
        complete!(do_parse!(
            o: complete!(parse_operator) >> v: parse_version >> (Anchor(o, v))
        )) | complete!(caret)
            | complete!(tilde)
            | complete!(wildcard)
            | complete!(hyphen)
    )
);
named!(
    caret<VersionRange>,
    do_parse!(
        v: preceded!(char!('^'), parse_version)
            >> (match v {
                Version(0, 0, 0, _) => Anchor(EQ, v),
                Version(0, 0, c, _) => range_ie(v, Version(0, 0, c + 1, 0)),
                Version(0, b, _, _) => range_ie(v, Version(0, b + 1, 0, 0)),
                Version(a, _, _, _) => range_ie(v, Version(a + 1, 0, 0, 0)),
            })
    )
);

named!(
    tilde<VersionRange>,
    map_res!(
        preceded!(char!('~'), separated_list1!(complete!(char!('.')), decimal)),
        |ls: Vec<usize>| {
            match ls[..] {
                [a, b, c, d] => Ok(range_ie(Version(a, b, c, d), Version(a, b, c + 1, 0))),
                [a, b, c] => Ok(range_ie(Version(a, b, c, 0), Version(a, b + 1, 0, 0))),
                [a, b] => Ok(range_ie(Version(a, b, 0, 0), Version(a, b + 1, 0, 0))),
                [a] => Ok(range_ie(Version(a, 0, 0, 0), Version(a + 1, 0, 0, 0))),
                _ => Err(()),
            }
        }
    )
);

named!(
    wildcard<VersionRange>,
    map_res!(
        terminated!(many1!(terminated!(decimal, char!('.'))), char!('x')),
        |ls: Vec<usize>| {
            match ls[..] {
                [a, b, c] => Ok(range_ie(Version(a, b, c, 0), Version(a, b, c + 1, 0))),
                [a, b] => Ok(range_ie(Version(a, b, 0, 0), Version(a, b + 1, 0, 0))),
                [a] => Ok(range_ie(Version(a, 0, 0, 0), Version(a + 1, 0, 0, 0))),
                _ => Err(()),
            }
        }
    )
);

named!(
    hyphen<VersionRange>,
    do_parse!(
        b: parse_version
            >> _x: delimited!(space0, char!('-'), space0)
            >> t: parse_version
            >> (range(true, true, b, t))
    )
);

fn range(include_bottom: bool, include_top: bool, bottom: Version, top: Version) -> VersionRange {
    let op_bottom = if include_bottom { GTE } else { GT };
    let op_top = if include_top { LTE } else { LT };
    Conj(
        Box::new(Anchor(op_bottom, bottom)),
        Box::new(Anchor(op_top, top)),
    )
}

// [bottom, top)
fn range_ie(bottom: Version, top: Version) -> VersionRange {
    range(true, false, bottom, top)
}

#[cfg(test)]
mod test {
    use crate::emver::*;
    use proptest::prelude::*;

    prop_compose! {
        fn version_gen()(a in any::<usize>(), b in any::<usize>(), c in any::<usize>(), d in any::<usize>()) -> Version {
            Version(a,b,c,d)
        }
    }

    prop_compose! {
        fn anchor_gen()(op in prop_oneof![Just(LT), Just(LTE), Just(EQ), Just(NEQ), Just(GT), Just(GTE)], v in version_gen()) -> VersionRange {
            Anchor(op, v)
        }
    }

    prop_compose! {
        fn conj_gen(inner: impl Strategy<Value = VersionRange> + Clone)(a in inner.clone(), b in inner) -> VersionRange {
            VersionRange::conj(a, b)
        }
    }

    prop_compose! {
        fn disj_gen(inner: impl Strategy<Value = VersionRange> + Clone)(a in inner.clone(), b in inner) -> VersionRange {
            VersionRange::disj(a,b)
        }
    }

    fn range_gen() -> BoxedStrategy<VersionRange> {
        let leaf = prop_oneof![Just(Any), Just(None), anchor_gen()];
        leaf.prop_recursive(4, 16, 10, |inner| {
            prop_oneof![conj_gen(inner.clone()), disj_gen(inner),]
        })
        .boxed()
    }

    proptest! {

        #[test]
        fn conj_assoc(a in range_gen(), b in range_gen(), c in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::conj(a.clone(), VersionRange::conj(b.clone(),c.clone()))) == obs.satisfies(&VersionRange::conj(VersionRange::conj(a,b),c)))
        }

    }
    proptest! {
        #[test]
        fn conj_commut(a in range_gen(), b in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::conj(a.clone(),b.clone())) == obs.satisfies(&VersionRange::conj(b, a)))
        }
    }

    proptest! {
        #[test]
        fn disj_assoc(a in range_gen(), b in range_gen(), c in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::disj(a.clone(), VersionRange::disj(b.clone(), c.clone()))) == obs.satisfies(&VersionRange::disj(VersionRange::disj(a, b), c)))
        }
    }

    proptest! {
        #[test]
        fn disj_commut(a in range_gen(), b in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::disj(a.clone(), b.clone())) == obs.satisfies(&VersionRange::disj(b.clone(), a.clone())))
        }
    }

    proptest! {
        #[test]
        fn any_ident_conj(a in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&a) == obs.satisfies(&VersionRange::conj(Any, a)))
        }
    }

    proptest! {
        #[test]
        fn none_ident_disj(a in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&a) == obs.satisfies(&VersionRange::disj(None, a)))
        }
    }

    proptest! {
        #[test]
        fn none_annihilates_conj(a in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::conj(None, a)) == obs.satisfies(&None))
        }
    }

    proptest! {
        #[test]
        fn any_annihilates_disj(a in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::disj(Any, a)) == obs.satisfies(&Any))
        }
    }

    proptest! {
        #[test]
        fn conj_distributes_over_disj(a in range_gen(), b in range_gen(), c in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::conj(a.clone(), VersionRange::disj(b.clone(),c.clone()))) == obs.satisfies(&VersionRange::disj(VersionRange::conj(a.clone(),b),VersionRange::conj(a,c))))
        }
    }

    proptest! {
        #[test]
        fn disj_distributes_over_conj(a in range_gen(), b in range_gen(), c in range_gen(), obs in version_gen()) {
            assert!(obs.satisfies(&VersionRange::disj(a.clone(), VersionRange::conj(b.clone(),c.clone()))) == obs.satisfies(&VersionRange::conj(VersionRange::disj(a.clone(),b),VersionRange::disj(a,c))))
        }
    }

    proptest! {
        #[test]
        fn any_accepts_any(obs in version_gen()) {
            assert!(obs.satisfies(&Any))
        }
    }

    proptest! {
        #[test]
        fn none_accepts_none(obs in version_gen()) {
            assert!(!obs.satisfies(&None))
        }
    }

    proptest! {
        #[test]
        fn conj_both(a in range_gen(), b in range_gen(), obs in version_gen()) {
            assert!((obs.satisfies(&a) && obs.satisfies(&b)) == obs.satisfies(&VersionRange::conj(a,b)))
        }
    }

    proptest! {
        #[test]
        fn disj_either(a in range_gen(), b in range_gen(), obs in version_gen()) {
            assert!((obs.satisfies(&a) || obs.satisfies(&b)) == obs.satisfies(&VersionRange::disj(a,b)))
        }
    }

    proptest! {
        #[test]
        fn range_parse_round_trip (a in range_gen().prop_filter("! not accepted in parser", |a| a != &None), obs in version_gen()) {
            // println!("{:?}", a);
            match parse_range(format!("{}",a).as_bytes()) {
                Ok((rest, range)) => {
                    println!("{:?}", std::str::from_utf8(rest));
                    assert!(rest == b"");
                    assert!(obs.satisfies(&a) == obs.satisfies(&range));
                }
                Err(e) => panic!("parse after display failed {}", e),
            }
        }
    }

    #[test]
    fn caret() {
        let (_, thing) = parse_range(b"(^1.2.3.4 || ~2.3.4) 0.0.0-2.1.3 || 1.2.x").unwrap();
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
