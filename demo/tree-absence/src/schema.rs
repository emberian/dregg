//! Byte tables and the regular-core schema evaluator: mirrors of `Schema.FlatTable`,
//! `Cert.tableOfJVal` / `schemaOfJVal` and the top-down `Schema.valid`. The run this produces is
//! re-checked node by node by Lean's `TreeAut.checkRun` against the compiled automaton.

use crate::json::as_nat;
use crate::merkle::find_key;
use crate::value::{canonical_obj, JVal};
use num_bigint::BigInt;
use serde_json::{json, Value};

#[derive(Clone, Debug)]
pub struct Table {
    pub num_states: usize,
    pub transitions: Vec<usize>,
    pub start: usize,
    pub accepting: Vec<usize>,
}

impl Table {
    pub fn well_formed(&self) -> bool {
        self.transitions.len() == self.num_states * 256
            && self.transitions.iter().all(|&t| t < self.num_states)
            && self.start < self.num_states
    }
    /// `Schema.tableAccepts`: run from `start`, out-of-range steps go to state 0.
    pub fn accepts(&self, w: &[u8]) -> bool {
        let mut s = self.start;
        for &b in w {
            s = self.transitions.get(s * 256 + b as usize).copied().unwrap_or(0);
        }
        self.accepting.contains(&s)
    }
    /// Read the `dfa` crate's / `policyc`'s JSON shape (extra keys ignored).
    pub fn from_json(v: &Value) -> Result<Table, String> {
        let nat = |k: &str| v.get(k).and_then(Value::as_u64).map(|x| x as usize);
        let nats = |k: &str| -> Option<Vec<usize>> {
            v.get(k)?.as_array()?.iter().map(|x| x.as_u64().map(|y| y as usize)).collect()
        };
        let t = Table {
            num_states: nat("num_states").ok_or("table: num_states")?,
            transitions: nats("transitions").ok_or("table: transitions")?,
            start: nat("start").ok_or("table: start")?,
            accepting: nats("accepting").ok_or("table: accepting")?,
        };
        if t.well_formed() {
            Ok(t)
        } else {
            Err("table: not well formed".into())
        }
    }
    /// The table as a model value (the four keys `tableOfJVal` reads, canonical order).
    pub fn to_jval(&self) -> JVal {
        let ints = |xs: &[usize]| JVal::Arr(xs.iter().map(|&x| JVal::Int(BigInt::from(x))).collect());
        canonical_obj(vec![
            (b"num_states".to_vec(), JVal::Int(BigInt::from(self.num_states))),
            (b"transitions".to_vec(), ints(&self.transitions)),
            (b"start".to_vec(), JVal::Int(BigInt::from(self.start))),
            (b"accepting".to_vec(), ints(&self.accepting)),
        ])
        .expect("distinct keys")
    }
    pub fn to_json(&self) -> Value {
        json!({ "num_states": self.num_states, "transitions": self.transitions,
                "start": self.start, "accepting": self.accepting })
    }
}

/// `Cert.tableOfJVal`.
pub fn table_of_jval(v: &JVal) -> Option<Table> {
    let JVal::Obj(kvs) = v else { return None };
    // unknown keys are refused (codex round 1, finding 2)
    const TABLE_KEYS: [&[u8]; 4] = [b"accepting", b"num_states", b"start", b"transitions"];
    if !kvs.iter().all(|(k, _)| TABLE_KEYS.contains(&k.as_slice())) {
        return None;
    }
    let nats = |x: &JVal| -> Option<Vec<usize>> {
        match x {
            JVal::Arr(xs) => xs.iter().map(as_nat).collect(),
            _ => None,
        }
    };
    let t = Table {
        num_states: as_nat(find_key(b"num_states", kvs)?)?,
        transitions: nats(find_key(b"transitions", kvs)?)?,
        start: as_nat(find_key(b"start", kvs)?)?,
        accepting: nats(find_key(b"accepting", kvs)?)?,
    };
    t.well_formed().then_some(t)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Null,
    Bool,
    Int,
    Num,
    Str,
    Arr,
    Obj,
}

#[derive(Clone, Debug)]
pub enum Addl {
    Any,
    Forbid,
    Sch(usize),
}

#[derive(Clone, Debug)]
pub struct Def {
    pub types: Vec<Ty>,
    pub enum_str: Option<Vec<Vec<u8>>>,
    pub pattern: Option<usize>,
    pub minimum: Option<BigInt>,
    pub maximum: Option<BigInt>,
    pub props: Vec<(Vec<u8>, usize)>,
    pub required: Vec<Vec<u8>>,
    pub additional: Addl,
    pub items: Option<usize>,
    pub min_items: usize,
    pub max_items: Option<usize>,
    pub all_of: Vec<usize>,
    pub any_of: Vec<usize>,
}

pub struct Schema {
    pub defs: Vec<Def>,
    pub tables: Vec<Table>,
    pub root: usize,
}

const KNOWN: [&str; 13] = [
    "type", "enum", "pattern", "minimum", "maximum", "properties", "required",
    "additionalProperties", "items", "minItems", "maxItems", "allOf", "anyOf",
];

fn ty_of_name(s: &[u8]) -> Option<Ty> {
    Some(match s {
        b"null" => Ty::Null,
        b"boolean" => Ty::Bool,
        b"integer" => Ty::Int,
        b"number" => Ty::Num,
        b"string" => Ty::Str,
        b"array" => Ty::Arr,
        b"object" => Ty::Obj,
        _ => return None,
    })
}

fn as_str(v: &JVal) -> Option<Vec<u8>> {
    match v {
        JVal::Str(s) => Some(s.clone()),
        _ => None,
    }
}

fn as_list<T>(v: &JVal, f: impl Fn(&JVal) -> Option<T>) -> Option<Vec<T>> {
    match v {
        JVal::Arr(xs) => xs.iter().map(f).collect(),
        _ => None,
    }
}

/// `Cert.defOfJVal`.
fn def_of_jval(v: &JVal) -> Option<Def> {
    let JVal::Obj(kvs) = v else { return None };
    if !kvs.iter().all(|(k, _)| KNOWN.iter().any(|n| n.as_bytes() == k.as_slice())) {
        return None;
    }
    // `opt k f`: absent → Some(None); present → f must succeed.
    fn opt<T>(kvs: &[(Vec<u8>, JVal)], k: &str, f: impl Fn(&JVal) -> Option<T>) -> Option<Option<T>> {
        match find_key(k.as_bytes(), kvs) {
            None => Some(None),
            Some(v) => f(v).map(Some),
        }
    }
    let as_int = |v: &JVal| match v {
        JVal::Int(n) => Some(n.clone()),
        _ => None,
    };
    // an explicit empty `type`, `enum`, `allOf` or `anyOf` is refused, never read as absent
    // (codex round 1, finding 2)
    fn non_empty<T>(x: Option<Vec<T>>) -> Option<Vec<T>> {
        x.filter(|l| !l.is_empty())
    }
    let types = opt(kvs, "type", |v| non_empty(match v {
        JVal::Str(s) => ty_of_name(s).map(|t| vec![t]),
        JVal::Arr(xs) => xs.iter().map(|x| as_str(x).and_then(|s| ty_of_name(&s))).collect(),
        _ => None,
    }))?;
    let enum_str = opt(kvs, "enum", |v| non_empty(as_list(v, as_str)))?;
    let pattern = opt(kvs, "pattern", as_nat)?;
    let minimum = opt(kvs, "minimum", as_int)?;
    let maximum = opt(kvs, "maximum", as_int)?;
    let props = opt(kvs, "properties", |v| match v {
        JVal::Obj(ps) => ps.iter().map(|(k, x)| as_nat(x).map(|j| (k.clone(), j))).collect(),
        _ => None,
    })?;
    let required = opt(kvs, "required", |v| as_list(v, as_str))?;
    let additional = opt(kvs, "additionalProperties", |v| match v {
        JVal::Bool(true) => Some(Addl::Any),
        JVal::Bool(false) => Some(Addl::Forbid),
        v => as_nat(v).map(Addl::Sch),
    })?;
    let items = opt(kvs, "items", as_nat)?;
    let min_items = opt(kvs, "minItems", as_nat)?;
    let max_items = opt(kvs, "maxItems", as_nat)?;
    let all_of = opt(kvs, "allOf", |v| non_empty(as_list(v, as_nat)))?;
    let any_of = opt(kvs, "anyOf", |v| non_empty(as_list(v, as_nat)))?;
    Some(Def {
        types: types.unwrap_or_default(),
        enum_str,
        pattern,
        minimum,
        maximum,
        props: props.unwrap_or_default(),
        required: required.unwrap_or_default(),
        additional: additional.unwrap_or(Addl::Any),
        items,
        min_items: min_items.unwrap_or(0),
        max_items,
        all_of: all_of.unwrap_or_default(),
        any_of: any_of.unwrap_or_default(),
    })
}

/// `Cert.schemaOfJVal` (including `Schema.ok`).
pub fn schema_of_jval(v: &JVal) -> Option<Schema> {
    let JVal::Obj(kvs) = v else { return None };
    const WRAPPER_KEYS: [&[u8]; 3] = [b"defs", b"root", b"tables"];
    if !kvs.iter().all(|(k, _)| WRAPPER_KEYS.contains(&k.as_slice())) {
        return None;
    }
    let defs = as_list(find_key(b"defs", kvs)?, def_of_jval)?;
    let root = as_nat(find_key(b"root", kvs)?)?;
    let tables = match find_key(b"tables", kvs) {
        None => vec![],
        Some(t) => as_list(t, table_of_jval)?,
    };
    let s = Schema { defs, tables, root };
    // `Schema.ok`: same-node references point lower, every child reference exists
    let m = s.defs.len();
    let ok = s.root < m
        && s.defs.iter().enumerate().all(|(d, def)| {
            def.all_of.iter().all(|&j| j < d)
                && def.any_of.iter().all(|&j| j < d)
                && def.props.iter().all(|(_, j)| *j < m)
                && (match def.additional { Addl::Sch(j) => j < m, _ => true })
                && def.items.is_none_or(|j| j < m)
                && def.pattern.is_none_or(|p| p < s.tables.len())
        });
    ok.then_some(s)
}

fn ty_of(v: &JVal) -> Ty {
    match v {
        JVal::Null => Ty::Null,
        JVal::Bool(_) => Ty::Bool,
        JVal::Int(_) => Ty::Int,
        JVal::Dec(..) => Ty::Num,
        JVal::Str(_) => Ty::Str,
        JVal::Arr(_) => Ty::Arr,
        JVal::Obj(_) => Ty::Obj,
    }
}

fn pow10(k: i64) -> BigInt {
    num_traits::pow(BigInt::from(10), (-k).max(0) as usize)
}

impl Schema {
    fn type_ok(&self, d: &Def, v: &JVal) -> bool {
        let t = ty_of(v);
        d.types.is_empty() || d.types.contains(&t) || (t == Ty::Int && d.types.contains(&Ty::Num))
    }

    fn scalar_ok(&self, d: &Def, v: &JVal) -> bool {
        match v {
            JVal::Str(s) => {
                d.enum_str.as_ref().is_none_or(|l| l.contains(s))
                    && d.pattern.is_none_or(|p| self.tables.get(p).is_some_and(|t| t.accepts(s)))
            }
            JVal::Int(n) => {
                d.enum_str.is_none()
                    && d.minimum.as_ref().is_none_or(|b| b <= n) && d.maximum.as_ref().is_none_or(|b| n <= b)
            }
            JVal::Dec(m, e) => {
                d.enum_str.is_none()
                    && d.minimum.as_ref().is_none_or(|b| *m >= b * pow10(*e))
                    && d.maximum.as_ref().is_none_or(|b| *m <= b * pow10(*e))
            }
            // `enum` is string-only: it refuses every non-string, containers included
            // (codex round 1, finding 1)
            _ => d.enum_str.is_none(),
        }
    }

    /// `Schema.valid S v d`.
    pub fn valid(&self, v: &JVal, d: usize) -> bool {
        let Some(def) = self.defs.get(d) else { return false };
        self.type_ok(def, v)
            && self.scalar_ok(def, v)
            && match v {
                JVal::Arr(xs) => {
                    xs.iter().all(|c| def.items.is_none_or(|j| self.valid(c, j)))
                        && def.min_items <= xs.len()
                        && def.max_items.is_none_or(|m| xs.len() <= m)
                }
                JVal::Obj(kvs) => {
                    kvs.iter().all(|(k, c)| {
                        match def.props.iter().find(|(k2, _)| k2 == k).map(|(_, j)| *j) {
                            Some(j) => self.valid(c, j),
                            None => match def.additional {
                                Addl::Any => true,
                                Addl::Forbid => false,
                                Addl::Sch(j) => self.valid(c, j),
                            },
                        }
                    }) && def.required.iter().all(|r| kvs.iter().any(|(k, _)| k == r))
                }
                _ => true,
            }
            && def.all_of.iter().all(|&j| j < d && self.valid(v, j))
            && (def.any_of.is_empty() || def.any_of.iter().any(|&j| j < d && self.valid(v, j)))
    }

    fn bits(&self, v: &JVal) -> String {
        (0..self.defs.len()).map(|d| if self.valid(v, d) { '1' } else { '0' }).collect()
    }

    /// The honest run (`TreeAut.annotate` at the compiled automaton, by `compile_correct`).
    pub fn run(&self, v: &JVal) -> Value {
        match v {
            JVal::Arr(xs) => json!({ "q": self.bits(v), "kids": xs.iter().map(|c| self.run(c)).collect::<Vec<_>>() }),
            JVal::Obj(kvs) => json!({ "q": self.bits(v), "kids": kvs.iter().map(|(_, c)| self.run(c)).collect::<Vec<_>>() }),
            _ => json!({ "q": self.bits(v) }),
        }
    }
}
