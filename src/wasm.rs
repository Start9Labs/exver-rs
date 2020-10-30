use crate::emver;
use std::cmp::Ord;
use std::cmp::Ordering;
use wasm_bindgen::prelude::*;

fn parse_version(s: &str) -> Result<emver::Version, JsValue> {
    s.parse().map_err(JsValue::from)
}
fn parse_range(s: &str) -> Result<emver::VersionRange, JsValue> {
    s.parse().map_err(JsValue::from)
}

#[wasm_bindgen]
pub fn major(version: &str) -> Result<usize, JsValue> {
    parse_version(version).map(|v| v.major())
}
#[wasm_bindgen]
pub fn minor(version: &str) -> Result<usize, JsValue> {
    parse_version(version).map(|v| v.minor())
}
#[wasm_bindgen]
pub fn patch(version: &str) -> Result<usize, JsValue> {
    parse_version(version).map(|v| v.patch())
}
#[wasm_bindgen]
pub fn revision(version: &str) -> Result<usize, JsValue> {
    parse_version(version).map(|v| v.revision())
}
#[wasm_bindgen]
pub fn compare(lhs: &str, rhs: &str) -> Result<isize, JsValue> {
    let s = parse_version(lhs).map_err(JsValue::from)?;
    let t = parse_version(rhs).map_err(JsValue::from)?;
    Ok(match s.cmp(&t) {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    })
}
#[wasm_bindgen]
pub fn satisfies(version: &str, range: &str) -> Result<bool, JsValue> {
    let v = parse_version(version).map_err(JsValue::from)?;
    let r = parse_range(range).map_err(JsValue::from)?;
    Ok(v.satisfies(&r))
}
