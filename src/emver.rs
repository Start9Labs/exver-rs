use std::cmp::Ordering;
use std::fmt;
use std::ops::Deref;

use either::Either::{self, *};
use fp_core::empty::Empty;
use fp_core::foldable::fold_map;
use fp_core::monoid::Monoid;
use fp_core::semigroup::Semigroup;
use nom::character::complete::digit1;
use nom::character::complete::space0;
use nom::character::complete::space1;

use VersionRange::*;

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Version(usize, usize, usize, usize);

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.3 {
            0 => write!(f, "{}.{}.{}", self.0, self.1, self.2),
            n => write!(f, "{}.{}.{}.{}", self.0, self.1, self.2, n),
        }
    }
}
impl Version {
    pub fn major(&self) -> usize {
        self.0
    }
    pub fn minor(&self) -> usize {
        self.1
    }
    pub fn patch(&self) -> usize {
        self.2
    }
    pub fn revision(&self) -> usize {
        self.3
    }
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
type Operator = Negatable<Ordering>;
pub const GTE: Operator = Left(Ordering::Less);
pub const LT: Operator = Right(Ordering::Less);
pub const NEQ: Operator = Left(Ordering::Equal);
pub const EQ: Operator = Right(Ordering::Equal);
pub const LTE: Operator = Left(Ordering::Greater);
pub const GT: Operator = Right(Ordering::Greater);

pub enum VersionRange {
    Anchor(Operator, Version),
    Conj(Box<VersionRange>, Box<VersionRange>),
    Disj(Box<VersionRange>, Box<VersionRange>),
    Any,
    None,
}
impl fmt::Display for VersionRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Anchor(Left(Ordering::Less), v) => write!(f, ">={}", v),
            Anchor(Right(Ordering::Less), v) => write!(f, "<{}", v),
            Anchor(Left(Ordering::Equal), v) => write!(f, "!{}", v),
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

pub struct AnyRange(VersionRange);
impl Semigroup for AnyRange {
    fn combine(self, other: Self) -> Self {
        AnyRange(disj(self.0, other.0))
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
        AllRange(conj(self.0, other.0))
    }
}
impl Empty for AllRange {
    fn empty() -> Self {
        AllRange(Any)
    }
}
impl Monoid for AllRange {}

// smart constructor for Conj, eagerly evaluates identities and annihilators
pub fn conj(a: VersionRange, b: VersionRange) -> VersionRange {
    match (a, b) {
        (Any, b) => b,
        (a, Any) => a,
        (None, _) => None,
        (_, None) => None,
        (a, b) => Conj(Box::new(a), Box::new(b)),
    }
}

// smart constructor for Disj, eagerly evaluates identities and annihilators
pub fn disj(a: VersionRange, b: VersionRange) -> VersionRange {
    match (a, b) {
        (Any, _) => Any,
        (_, Any) => Any,
        (None, b) => b,
        (a, None) => a,
        (a, b) => Disj(Box::new(a), Box::new(b)),
    }
}

pub fn exactly(a: Version) -> VersionRange {
    Anchor(Left(Ordering::Equal), a)
}

named!(
    decimal<usize>,
    map_res!(map_res!(digit1, std::str::from_utf8), |s: &str| s
        .parse::<usize>())
);

// fn check_length_out_of_band_cause_its_the_stone_age (i: &[u8], )

named!(
    parse_version<Version>,
    map_res!(separated_list!(char!('.'), decimal), |ls: Vec<usize>| {
        match &ls[..] {
            [a, b, c, d] => Ok(Version(*a, *b, *c, *d)),
            [a, b, c] => Ok(Version(*a, *b, *c, 0)),
            [a, b] => Ok(Version(*a, *b, 0, 0)),
            [a] => Ok(Version(*a, 0, 0, 0)),
            _ => Err(()),
        }
    })
);

// named!(
// parse_range<VersionRange>
// )

named!(sub<VersionRange>, do_parse!((Any)));

// named!(
// sum<VersionRange>
// )

// product<VersionRange>
named!(
    product<VersionRange>,
    do_parse!(
        ls: separated_list!(space1, alt!(parse_atom | sub))
            >> (fold_map(ls, |x| {
                let y: VersionRange = x.to_owned();
                AllRange(y)
            })
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
            | map!(complete!(char!('!')), |_| NEQ)
    )
);
named!(
    parse_atom<VersionRange>,
    alt!(
        do_parse!(o: parse_operator >> v: parse_version >> (Anchor(o, v)))
            | caret
            | tilde
            | wildcard
            | hyphen
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
        preceded!(char!('~'), separated_list!(char!('.'), decimal)),
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
