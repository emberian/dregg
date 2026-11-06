//! # NVIDIA Reference Integrity Manifests (driver and VBIOS SWID tags) — offline verifier.
//!
//! A RIM is a TCG RIM-IM / ISO 19770-2 SWID tag carrying, per SPDM measurement index, the
//! accepted SHA-384 values, enveloped-signed with XML-DSig. This module turns two signed RIMs
//! (driver and VBIOS) into the [`GoldenMeasurements`] that [`crate::nvidia`] compares a GPU
//! report against, so the golden values come from NVIDIA's signature and not from the report.
//!
//! Fail-closed, in order:
//!
//! 1. **Strict XML subset.** UTF-8; no DOCTYPE, comment, processing instruction (other than a
//!    leading XML declaration), CDATA, carriage return, `xml:*` attribute, or entity other
//!    than the five predefined ones and numeric character references. Anything outside the
//!    subset is a refusal, not a best-effort parse, because the signature is over the
//!    canonical form and every construct we do not parse is one whose canonicalisation we
//!    could get wrong.
//! 2. **Signature shape.** Exactly one `ds:Signature`, a child of the root
//!    `SoftwareIdentity`, and no other XML-DSig element anywhere. `SignedInfo` must be
//!    exactly: Canonical XML 1.1, ECDSA-SHA384, one `Reference URI=""` whose transforms are
//!    exactly enveloped-signature then Canonical XML 1.1, digest SHA-384.
//! 3. **Digest.** SHA-384 of the Canonical XML 1.1 form of the whole document without the
//!    `Signature` element equals `DigestValue`.
//! 4. **Signature.** The Canonical XML 1.1 form of `SignedInfo` (with its inherited namespace
//!    declarations) verifies under the leaf key of the `KeyInfo` chain (raw `r ‖ s`, P-384).
//! 5. **Chain.** The `KeyInfo` chain (leaf first) ends in the PINNED NVIDIA CoRIM signing
//!    Root CA, every link verifies, every certificate is valid at `now`.
//! 6. **Content.** Measurements are read only from the parsed tree whose canonical form was
//!    digested, so the signed bytes and the read values are the same object (no wrapping).
//!
//! What a successful [`verify_rim`] establishes: NVIDIA's CoRIM PKI signed this manifest, for
//! this product and `colloquialVersion`. Whether the certificates are revoked is
//! [`crate::nvidia_ocsp`]'s job; whether the RIM is the one for the attesting GPU's driver and
//! VBIOS is [`goldens_from_rims`]'s.
//!
//! Format sources (read, not copied): nvtrust `local_gpu_verifier` `rim/__init__.py`
//! (signxml verification, measurement parse) and `cc_admin_utils.py` (RIM ids, VBIOS version
//! formatting); W3C Canonical XML 1.1 and XML-DSig 1.1.

use std::collections::BTreeMap;

use p384::ecdsa::signature::Verifier;
use p384::ecdsa::{Signature, VerifyingKey};
use sha2::{Digest, Sha384};
use x509_parser::pem::Pem;
use x509_parser::prelude::*;

use crate::nvidia::{GoldenMeasurements, GpuReport};

/// The pinned RIM trust anchor: NVIDIA CoRIM signing Root CA (self-signed, P-384), as shipped
/// in nvtrust `verifier/certs/verifier_RIM_root.pem`.
pub const NVIDIA_CORIM_ROOT_CA_PEM: &[u8] = include_bytes!("nvidia_corim_root_ca.pem");

const NS_SWID: &str = "http://standards.iso.org/iso/19770/-2/2015/schema.xsd";
const NS_DSIG: &str = "http://www.w3.org/2000/09/xmldsig#";
const NS_HASH384: &str = "http://www.w3.org/2001/04/xmlenc#sha384";
const ALG_C14N11: &str = "http://www.w3.org/2006/12/xml-c14n11";
const ALG_ECDSA_SHA384: &str = "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha384";
const ALG_ENVELOPED: &str = "http://www.w3.org/2000/09/xmldsig#enveloped-signature";
const ALG_SHA384: &str = "http://www.w3.org/2001/04/xmldsig-more#sha384";
const SHA384_LEN: usize = 48;

// ---------------------------------------------------------------------------------------
// Strict XML subset parser
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Node {
    Elem(Elem),
    Text(String),
}

#[derive(Debug, Clone)]
struct Attr {
    qname: String,
    value: String,
}

#[derive(Debug, Clone)]
struct Elem {
    qname: String,
    /// Namespace declarations made ON this element, in document order: (prefix, uri);
    /// prefix "" is the default namespace.
    decls: Vec<(String, String)>,
    attrs: Vec<Attr>,
    kids: Vec<Node>,
}

struct Parser<'a> {
    s: &'a str,
    at: usize,
}

fn is_name_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || c == ':'
}
fn is_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | ':' | '.' | '-')
}

impl<'a> Parser<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.at..]
    }
    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }
    fn eat(&mut self, lit: &str) -> bool {
        if self.rest().starts_with(lit) {
            self.at += lit.len();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, lit: &str) -> Result<(), String> {
        if self.eat(lit) {
            Ok(())
        } else {
            Err(format!("xml: expected {lit:?} at byte {}", self.at))
        }
    }
    fn ws(&mut self) -> bool {
        let start = self.at;
        while matches!(self.peek(), Some(' ' | '\t' | '\n')) {
            self.at += 1;
        }
        self.at > start
    }
    fn name(&mut self) -> Result<String, String> {
        let start = self.at;
        match self.peek() {
            Some(c) if is_name_start(c) => self.at += 1,
            _ => return Err(format!("xml: expected a name at byte {start}")),
        }
        while matches!(self.peek(), Some(c) if is_name_char(c)) {
            self.at += 1;
        }
        let n = &self.s[start..self.at];
        if n.matches(':').count() > 1 || n.starts_with(':') || n.ends_with(':') {
            return Err(format!("xml: malformed qualified name {n:?}"));
        }
        Ok(n.to_string())
    }
    /// Decode one reference after `&`. Only the five predefined entities and numeric
    /// character references are in the subset.
    fn reference(&mut self) -> Result<char, String> {
        let end = self
            .rest()
            .find(';')
            .ok_or_else(|| "xml: unterminated reference".to_string())?;
        let body = &self.rest()[..end];
        let c = match body {
            "amp" => '&',
            "lt" => '<',
            "gt" => '>',
            "quot" => '"',
            "apos" => '\'',
            _ => {
                let code = if let Some(h) = body.strip_prefix("#x") {
                    u32::from_str_radix(h, 16)
                } else if let Some(d) = body.strip_prefix('#') {
                    d.parse::<u32>()
                } else {
                    return Err(format!("xml: entity &{body}; is outside the subset"));
                }
                .map_err(|_| format!("xml: bad character reference &{body};"))?;
                let c = char::from_u32(code)
                    .ok_or_else(|| format!("xml: invalid character reference &{body};"))?;
                if (c as u32) < 0x20 && !matches!(c, '\t' | '\n' | '\r') {
                    return Err(format!("xml: forbidden character reference &{body};"));
                }
                c
            }
        };
        self.at += end + 1;
        Ok(c)
    }
    fn attr_value(&mut self) -> Result<String, String> {
        let q = match self.peek() {
            Some(q @ ('"' | '\'')) => q,
            _ => return Err(format!("xml: expected a quoted value at byte {}", self.at)),
        };
        self.at += 1;
        let mut v = String::new();
        loop {
            let c = self
                .peek()
                .ok_or_else(|| "xml: unterminated attribute value".to_string())?;
            self.at += c.len_utf8();
            match c {
                _ if c == q => return Ok(v),
                '<' => return Err("xml: '<' in an attribute value".into()),
                '&' => v.push(self.reference()?),
                // Attribute-value normalisation (XML 1.0 §3.3.3, CDATA type): literal white
                // space becomes a space; character references are kept as written.
                '\t' | '\n' => v.push(' '),
                _ => v.push(c),
            }
        }
    }
    fn element(&mut self, depth: usize) -> Result<Elem, String> {
        if depth > 64 {
            return Err("xml: nesting deeper than 64".into());
        }
        self.expect("<")?;
        let qname = self.name()?;
        let mut decls = Vec::new();
        let mut attrs: Vec<Attr> = Vec::new();
        loop {
            let had_ws = self.ws();
            if self.eat("/>") {
                return Ok(Elem {
                    qname,
                    decls,
                    attrs,
                    kids: Vec::new(),
                });
            }
            if self.eat(">") {
                break;
            }
            if !had_ws {
                return Err(format!(
                    "xml: expected white space before an attribute at byte {}",
                    self.at
                ));
            }
            let an = self.name()?;
            self.ws();
            self.expect("=")?;
            self.ws();
            let av = self.attr_value()?;
            if an == "xmlns" {
                if decls.iter().any(|(p, _)| p.is_empty()) {
                    return Err("xml: duplicate default namespace declaration".into());
                }
                decls.push((String::new(), av));
            } else if let Some(p) = an.strip_prefix("xmlns:") {
                if av.is_empty() {
                    return Err(format!("xml: prefix {p} undeclared to the empty URI"));
                }
                if p == "xml" || p == "xmlns" {
                    return Err(format!("xml: reserved prefix {p} declared"));
                }
                if decls.iter().any(|(q, _)| q == p) {
                    return Err(format!("xml: duplicate declaration of prefix {p}"));
                }
                decls.push((p.to_string(), av));
            } else {
                if an.starts_with("xml:") {
                    return Err(format!("xml: {an} is outside the subset"));
                }
                if attrs.iter().any(|a| a.qname == an) {
                    return Err(format!("xml: duplicate attribute {an}"));
                }
                attrs.push(Attr {
                    qname: an,
                    value: av,
                });
            }
        }
        let mut kids = Vec::new();
        let mut text = String::new();
        loop {
            if self.rest().starts_with("</") {
                if !text.is_empty() {
                    kids.push(Node::Text(std::mem::take(&mut text)));
                }
                self.at += 2;
                let close = self.name()?;
                if close != qname {
                    return Err(format!("xml: </{close}> closes <{qname}>"));
                }
                self.ws();
                self.expect(">")?;
                return Ok(Elem {
                    qname,
                    decls,
                    attrs,
                    kids,
                });
            }
            if self.rest().starts_with("<!") || self.rest().starts_with("<?") {
                return Err(format!(
                    "xml: comment, CDATA, DOCTYPE or processing instruction at byte {} is outside the subset",
                    self.at
                ));
            }
            if self.rest().starts_with('<') {
                if !text.is_empty() {
                    kids.push(Node::Text(std::mem::take(&mut text)));
                }
                kids.push(Node::Elem(self.element(depth + 1)?));
                continue;
            }
            let c = self
                .peek()
                .ok_or_else(|| format!("xml: <{qname}> is never closed"))?;
            self.at += c.len_utf8();
            match c {
                '&' => text.push(self.reference()?),
                '>' if text.ends_with("]]") => return Err("xml: ']]>' in text".into()),
                _ => text.push(c),
            }
        }
    }
}

fn parse_document(s: &str) -> Result<Elem, String> {
    if s.contains('\r') {
        return Err("xml: carriage return is outside the subset".into());
    }
    if s.starts_with('\u{feff}') {
        return Err("xml: byte-order mark is outside the subset".into());
    }
    let mut p = Parser { s, at: 0 };
    if p.rest().starts_with("<?xml") {
        // The XML declaration is not part of the canonical form; accept only the plain one.
        let end = p
            .rest()
            .find("?>")
            .ok_or_else(|| "xml: unterminated XML declaration".to_string())?;
        let decl = &p.rest()[5..end];
        if decl.contains('<') || decl.contains('&') {
            return Err("xml: malformed XML declaration".into());
        }
        p.at += end + 2;
    }
    p.ws();
    if !p.rest().starts_with('<') || p.rest().starts_with("<!") || p.rest().starts_with("<?") {
        return Err("xml: expected the root element".into());
    }
    let root = p.element(0)?;
    p.ws();
    if p.at != s.len() {
        return Err(format!(
            "xml: content after the root element at byte {}",
            p.at
        ));
    }
    Ok(root)
}

// ---------------------------------------------------------------------------------------
// Namespaces and Canonical XML 1.1 (for the subset above)
// ---------------------------------------------------------------------------------------

type Scope = BTreeMap<String, String>;

fn extend_scope(scope: &Scope, e: &Elem) -> Scope {
    let mut s = scope.clone();
    for (p, u) in &e.decls {
        s.insert(p.clone(), u.clone());
    }
    s
}

fn split_qname(q: &str) -> (&str, &str) {
    match q.split_once(':') {
        Some((p, l)) => (p, l),
        None => ("", q),
    }
}

/// (namespace URI, local name) of an element in `scope` (which includes its own decls).
fn elem_name<'s>(e: &'s Elem, scope: &'s Scope) -> Result<(&'s str, &'s str), String> {
    let (p, l) = split_qname(&e.qname);
    let uri = scope
        .get(p)
        .map(String::as_str)
        .or(if p.is_empty() { Some("") } else { None })
        .ok_or_else(|| format!("xml: unbound prefix {p} on <{}>", e.qname))?;
    Ok((uri, l))
}

/// (namespace URI, local name) of an attribute. Unprefixed attributes have no namespace.
fn attr_name<'s>(a: &'s Attr, scope: &'s Scope) -> Result<(&'s str, &'s str), String> {
    let (p, l) = split_qname(&a.qname);
    if p.is_empty() {
        return Ok(("", l));
    }
    let uri = scope
        .get(p)
        .ok_or_else(|| format!("xml: unbound prefix {p} on attribute {}", a.qname))?;
    Ok((uri.as_str(), l))
}

fn esc_attr(v: &str, out: &mut String) {
    for c in v.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '"' => out.push_str("&quot;"),
            '\t' => out.push_str("&#x9;"),
            '\n' => out.push_str("&#xA;"),
            '\r' => out.push_str("&#xD;"),
            _ => out.push(c),
        }
    }
}

fn esc_text(v: &str, out: &mut String) {
    for c in v.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '\r' => out.push_str("&#xD;"),
            _ => out.push(c),
        }
    }
}

/// Canonical XML 1.1 (without comments) of the subtree at `e`, as the apex of a document
/// subset whose in-scope namespaces from ancestors are `inherited`, omitting the element
/// `skip` (compared by address) and its subtree: the enveloped-signature transform.
///
/// For the subset parsed above (no `xml:*` attributes, no comments or PIs, no relative
/// namespace URIs) the rules are: render on the apex every in-scope namespace except an empty
/// default; below it, render a declaration only if it differs from the nearest rendered
/// ancestor's; namespace declarations sorted by prefix (default first), then attributes
/// sorted by (namespace URI, local name); empty elements as start-end pairs.
fn c14n(e: &Elem, inherited: &Scope, skip: Option<*const Elem>) -> Result<String, String> {
    let mut out = String::new();
    c14n_into(e, inherited, &Scope::new(), true, skip, &mut out)?;
    Ok(out)
}

fn c14n_into(
    e: &Elem,
    parent_scope: &Scope,
    rendered: &Scope,
    apex: bool,
    skip: Option<*const Elem>,
    out: &mut String,
) -> Result<(), String> {
    let scope = extend_scope(parent_scope, e);
    let candidates: Vec<(String, String)> = if apex {
        scope.iter().map(|(p, u)| (p.clone(), u.clone())).collect()
    } else {
        e.decls.clone()
    };
    let mut ns: Vec<(String, String)> = candidates
        .into_iter()
        .filter(|(p, u)| rendered.get(p).map(String::as_str).unwrap_or("") != u.as_str())
        .collect();
    ns.sort();
    let mut now_rendered = rendered.clone();
    out.push('<');
    out.push_str(&e.qname);
    for (p, u) in &ns {
        out.push_str(if p.is_empty() { " xmlns" } else { " xmlns:" });
        out.push_str(p);
        out.push_str("=\"");
        esc_attr(u, out);
        out.push('"');
        now_rendered.insert(p.clone(), u.clone());
    }
    elem_name(e, &scope)?;
    let mut attrs = Vec::with_capacity(e.attrs.len());
    for a in &e.attrs {
        let (u, l) = attr_name(a, &scope)?;
        attrs.push(((u.to_string(), l.to_string()), a));
    }
    attrs.sort_by(|x, y| x.0.cmp(&y.0));
    if attrs.windows(2).any(|w| w[0].0 == w[1].0) {
        return Err("xml: two attributes with the same expanded name".into());
    }
    for (_, a) in attrs {
        out.push(' ');
        out.push_str(&a.qname);
        out.push_str("=\"");
        esc_attr(&a.value, out);
        out.push('"');
    }
    out.push('>');
    for k in &e.kids {
        match k {
            Node::Text(t) => esc_text(t, out),
            Node::Elem(c) if Some(c as *const Elem) == skip => {}
            Node::Elem(c) => c14n_into(c, &scope, &now_rendered, false, skip, out)?,
        }
    }
    out.push_str("</");
    out.push_str(&e.qname);
    out.push('>');
    Ok(())
}

// ---------------------------------------------------------------------------------------
// Tree helpers
// ---------------------------------------------------------------------------------------

fn child_elems(e: &Elem) -> impl Iterator<Item = &Elem> {
    e.kids.iter().filter_map(|k| match k {
        Node::Elem(c) => Some(c),
        Node::Text(_) => None,
    })
}

fn text_of(e: &Elem) -> Result<String, String> {
    let mut s = String::new();
    for k in &e.kids {
        match k {
            Node::Text(t) => s.push_str(t),
            Node::Elem(c) => {
                return Err(format!(
                    "<{}> has an unexpected child <{}>",
                    e.qname, c.qname
                ))
            }
        }
    }
    Ok(s)
}

fn attr<'e>(e: &'e Elem, scope: &Scope, ns: &str, local: &str) -> Result<Option<&'e str>, String> {
    for a in &e.attrs {
        if attr_name(a, scope)? == (ns, local) {
            return Ok(Some(&a.value));
        }
    }
    Ok(None)
}

fn req_attr<'e>(e: &'e Elem, scope: &Scope, ns: &str, local: &str) -> Result<&'e str, String> {
    attr(e, scope, ns, local)?.ok_or_else(|| format!("<{}> lacks attribute {local}", e.qname))
}

/// The children of `e` that are elements, with their scopes, checked to be exactly the
/// expected (namespace, local) sequence.
fn exact_children<'e>(
    e: &'e Elem,
    scope: &Scope,
    want: &[(&str, &str)],
) -> Result<Vec<(&'e Elem, Scope)>, String> {
    let kids: Vec<&Elem> = child_elems(e).collect();
    if kids.len() != want.len() {
        return Err(format!(
            "<{}> has {} element children, expected {}",
            e.qname,
            kids.len(),
            want.len()
        ));
    }
    let mut out = Vec::new();
    for (k, w) in kids.into_iter().zip(want) {
        let ks = extend_scope(scope, k);
        if elem_name(k, &ks)? != *w {
            return Err(format!("<{}> is not the expected {}:{}", k.qname, w.0, w.1));
        }
        out.push((k, ks));
    }
    Ok(out)
}

fn no_element_children(e: &Elem) -> Result<(), String> {
    match child_elems(e).next() {
        None => Ok(()),
        Some(c) => Err(format!(
            "<{}> has an unexpected child <{}>",
            e.qname, c.qname
        )),
    }
}

/// Count elements in namespace `ns` anywhere in the tree.
fn count_ns(e: &Elem, scope: &Scope, ns: &str) -> Result<usize, String> {
    let s = extend_scope(scope, e);
    let mut n = usize::from(elem_name(e, &s)?.0 == ns);
    for c in child_elems(e) {
        n += count_ns(c, &s, ns)?;
    }
    Ok(n)
}

fn b64(s: &str) -> Result<Vec<u8>, String> {
    use base64::Engine;
    let clean: String = s.chars().filter(|c| !c.is_ascii_whitespace()).collect();
    base64::engine::general_purpose::STANDARD
        .decode(clean)
        .map_err(|e| format!("base64: {e}"))
}

// ---------------------------------------------------------------------------------------
// RIM verification
// ---------------------------------------------------------------------------------------

/// One measurement entry of a RIM.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RimMeasurement {
    /// The RIM's index (0-based). The SPDM measurement block index is `index + 1`.
    pub index: u8,
    pub active: bool,
    pub name: String,
    /// The accepted values (`Hash0 .. Hash{alternatives-1}`), each SHA-384.
    pub values: Vec<Vec<u8>>,
}

/// A RIM whose signature, chain and shape verified.
#[derive(Debug, Clone)]
pub struct VerifiedRim {
    pub product: String,
    pub colloquial_version: String,
    pub tag_id: String,
    pub measurements: BTreeMap<u8, RimMeasurement>,
    /// SHA-256 of the signing (leaf) certificate's DER.
    pub signer_fingerprint: [u8; 32],
    /// The KeyInfo chain as DER, leaf first, ending in the pinned root (for revocation).
    pub chain_der: Vec<Vec<u8>>,
}

fn pinned_corim_root() -> Result<Vec<u8>, String> {
    let p = Pem::iter_from_buffer(NVIDIA_CORIM_ROOT_CA_PEM)
        .next()
        .ok_or_else(|| "pinned CoRIM root missing".to_string())?
        .map_err(|e| format!("pinned CoRIM root PEM: {e}"))?;
    Ok(p.contents)
}

/// Verify a chain (leaf first) ending in the pinned CoRIM root at `now`; return the leaf key.
fn verify_rim_chain(ders: &[Vec<u8>], now: ASN1Time) -> Result<(VerifyingKey, [u8; 32]), String> {
    use sha2::Sha256;
    if ders.last().map(Vec::as_slice) != Some(pinned_corim_root()?.as_slice()) {
        return Err("RIM chain does not end in the pinned NVIDIA CoRIM signing Root CA".into());
    }
    let mut parsed = Vec::with_capacity(ders.len());
    for der in ders {
        let (rest, c) =
            X509Certificate::from_der(der).map_err(|e| format!("RIM cert parse: {e}"))?;
        if !rest.is_empty() {
            return Err("RIM cert has trailing bytes".into());
        }
        parsed.push(c);
    }
    for (i, cert) in parsed.iter().enumerate() {
        if !cert.validity().is_valid_at(now) {
            return Err(format!(
                "RIM chain cert {i} ({}) not valid at the reference time",
                cert.subject()
            ));
        }
        let issuer = parsed.get(i + 1).unwrap_or(cert);
        cert.verify_signature(Some(issuer.public_key()))
            .map_err(|e| format!("RIM chain link {i} signature: {e:?}"))?;
    }
    let key = VerifyingKey::from_sec1_bytes(&parsed[0].public_key().subject_public_key.data)
        .map_err(|e| format!("RIM signer key is not P-384: {e}"))?;
    Ok((key, Sha256::digest(&ders[0]).into()))
}

/// Verify one RIM (steps 1–6 of the module doc) at `now`.
pub fn verify_rim(xml: &[u8], now: ASN1Time) -> Result<VerifiedRim, String> {
    let s = std::str::from_utf8(xml).map_err(|_| "RIM is not UTF-8".to_string())?;
    let root = parse_document(s)?;
    let empty = Scope::new();
    let rscope = extend_scope(&empty, &root);
    if elem_name(&root, &rscope)? != (NS_SWID, "SoftwareIdentity") {
        return Err("RIM root is not a SWID SoftwareIdentity".into());
    }

    // 2. signature shape: exactly one XML-DSig element tree, a direct child of the root.
    let sigs: Vec<&Elem> = child_elems(&root)
        .filter(|c| {
            let cs = extend_scope(&rscope, c);
            matches!(elem_name(c, &cs), Ok((NS_DSIG, "Signature")))
        })
        .collect();
    if sigs.len() != 1 {
        return Err(format!(
            "RIM has {} root-level ds:Signature elements, expected 1",
            sigs.len()
        ));
    }
    let sig = sigs[0];
    let sscope = extend_scope(&rscope, sig);
    let dsig_total = count_ns(&root, &empty, NS_DSIG)?;
    let dsig_in_sig = count_ns(sig, &rscope, NS_DSIG)?;
    if dsig_total != dsig_in_sig {
        return Err("XML-DSig element outside the one Signature (wrapping)".into());
    }
    let parts = exact_children(
        sig,
        &sscope,
        &[
            (NS_DSIG, "SignedInfo"),
            (NS_DSIG, "SignatureValue"),
            (NS_DSIG, "KeyInfo"),
        ],
    )?;
    let (signed_info, si_scope) = (&parts[0].0, &parts[0].1);
    let si = exact_children(
        signed_info,
        si_scope,
        &[
            (NS_DSIG, "CanonicalizationMethod"),
            (NS_DSIG, "SignatureMethod"),
            (NS_DSIG, "Reference"),
        ],
    )?;
    let alg = |e: &Elem, sc: &Scope, want: &str, what: &str| -> Result<(), String> {
        no_element_children(e)?;
        let a = req_attr(e, sc, "", "Algorithm")?;
        if a != want {
            return Err(format!("{what} algorithm {a} is not {want}"));
        }
        if e.attrs.len() != 1 {
            return Err(format!("{what} has unexpected attributes"));
        }
        Ok(())
    };
    alg(si[0].0, &si[0].1, ALG_C14N11, "CanonicalizationMethod")?;
    alg(si[1].0, &si[1].1, ALG_ECDSA_SHA384, "SignatureMethod")?;
    let (reference, ref_scope) = (si[2].0, &si[2].1);
    if reference.attrs.len() != 1 || req_attr(reference, ref_scope, "", "URI")? != "" {
        return Err("Reference must be exactly URI=\"\"".into());
    }
    let rparts = exact_children(
        reference,
        ref_scope,
        &[
            (NS_DSIG, "Transforms"),
            (NS_DSIG, "DigestMethod"),
            (NS_DSIG, "DigestValue"),
        ],
    )?;
    let tf = exact_children(
        rparts[0].0,
        &rparts[0].1,
        &[(NS_DSIG, "Transform"), (NS_DSIG, "Transform")],
    )?;
    alg(tf[0].0, &tf[0].1, ALG_ENVELOPED, "first Transform")?;
    alg(tf[1].0, &tf[1].1, ALG_C14N11, "second Transform")?;
    alg(rparts[1].0, &rparts[1].1, ALG_SHA384, "DigestMethod")?;
    let digest_value = b64(&text_of(rparts[2].0)?)?;

    // 3. digest over the document without the Signature.
    let doc_c14n = c14n(&root, &empty, Some(sig as *const Elem))?;
    let digest = Sha384::digest(doc_c14n.as_bytes());
    if digest.as_slice() != digest_value.as_slice() {
        return Err("RIM digest does not match: the signed content was altered".into());
    }

    // 5. chain, then 4. signature over canonical SignedInfo.
    let sig_value = b64(&text_of(parts[1].0)?)?;
    let key_info = exact_children(parts[2].0, &parts[2].1, &[(NS_DSIG, "X509Data")])?;
    let (x509data, xd_scope) = (key_info[0].0, &key_info[0].1);
    let mut chain_der = Vec::new();
    for c in child_elems(x509data) {
        let cs = extend_scope(xd_scope, c);
        if elem_name(c, &cs)? != (NS_DSIG, "X509Certificate") {
            return Err(format!("unexpected <{}> in X509Data", c.qname));
        }
        chain_der.push(b64(&text_of(c)?)?);
    }
    if chain_der.is_empty() {
        return Err("RIM KeyInfo carries no certificate".into());
    }
    let (key, signer_fingerprint) = verify_rim_chain(&chain_der, now)?;
    // SignedInfo's apex scope is everything in scope at the Signature (root + Signature decls).
    let si_c14n = c14n(signed_info, &sscope, None)?;
    let sig =
        Signature::from_slice(&sig_value).map_err(|e| format!("RIM signature encoding: {e}"))?;
    key.verify(si_c14n.as_bytes(), &sig)
        .map_err(|_| "RIM signature does not verify under the signer key".to_string())?;

    // 6. content, from the same verified tree.
    let mut product = None;
    let mut colloquial_version = None;
    let mut measurements = BTreeMap::new();
    let mut payloads = 0;
    for c in child_elems(&root) {
        let cs = extend_scope(&rscope, c);
        match elem_name(c, &cs)? {
            (NS_SWID, "Meta") => {
                if colloquial_version.is_some() {
                    return Err("RIM has more than one Meta".into());
                }
                colloquial_version = Some(req_attr(c, &cs, "", "colloquialVersion")?.to_string());
                product = Some(req_attr(c, &cs, "", "product")?.to_string());
            }
            (NS_SWID, "Payload") => {
                payloads += 1;
                for r in child_elems(c) {
                    let rs = extend_scope(&cs, r);
                    if elem_name(r, &rs)? != (NS_SWID, "Resource") {
                        return Err(format!("unexpected <{}> in Payload", r.qname));
                    }
                    no_element_children(r)?;
                    if req_attr(r, &rs, "", "type")? != "Measurement" {
                        return Err("Payload Resource is not a Measurement".into());
                    }
                    let index: u8 = req_attr(r, &rs, "", "index")?
                        .parse()
                        .map_err(|_| "RIM measurement index is not 0..=255".to_string())?;
                    if index >= 255 {
                        return Err("RIM measurement index 255 has no SPDM block index".into());
                    }
                    let active = match req_attr(r, &rs, "", "active")? {
                        "True" => true,
                        "False" => false,
                        other => return Err(format!("measurement {index}: active={other:?}")),
                    };
                    let alternatives: usize = req_attr(r, &rs, "", "alternatives")?
                        .parse()
                        .map_err(|_| format!("measurement {index}: bad alternatives"))?;
                    if alternatives == 0 || alternatives > 16 {
                        return Err(format!("measurement {index}: {alternatives} alternatives"));
                    }
                    if req_attr(r, &rs, "", "size")? != SHA384_LEN.to_string() {
                        return Err(format!("measurement {index}: size is not {SHA384_LEN}"));
                    }
                    let mut values = Vec::with_capacity(alternatives);
                    for k in 0..alternatives {
                        let h = req_attr(r, &rs, NS_HASH384, &format!("Hash{k}"))?;
                        let v = hex::decode(h)
                            .map_err(|_| format!("measurement {index}: Hash{k} not hex"))?;
                        if v.len() != SHA384_LEN {
                            return Err(format!("measurement {index}: Hash{k} is not 48 bytes"));
                        }
                        values.push(v);
                    }
                    let hashes = r
                        .attrs
                        .iter()
                        .filter(|a| matches!(attr_name(a, &rs), Ok((NS_HASH384, _))))
                        .count();
                    if hashes != alternatives {
                        return Err(format!(
                            "measurement {index}: {hashes} hashes for {alternatives} alternatives"
                        ));
                    }
                    let name = req_attr(r, &rs, "", "name")?.to_string();
                    let m = RimMeasurement {
                        index,
                        active,
                        name,
                        values,
                    };
                    if measurements.insert(index, m).is_some() {
                        return Err(format!("RIM measurement index {index} appears twice"));
                    }
                }
            }
            _ => {}
        }
    }
    if payloads != 1 {
        return Err(format!("RIM has {payloads} Payload elements, expected 1"));
    }
    Ok(VerifiedRim {
        product: product.ok_or_else(|| "RIM has no Meta".to_string())?,
        colloquial_version: colloquial_version.ok_or_else(|| "RIM has no Meta".to_string())?,
        tag_id: req_attr(&root, &rscope, "", "tagId")?.to_string(),
        measurements,
        signer_fingerprint,
        chain_der,
    })
}

// ---------------------------------------------------------------------------------------
// Binding RIMs to a report, and deriving the goldens
// ---------------------------------------------------------------------------------------

/// Opaque TLV types (nvtrust `OpaqueData.OPAQUE_DATA_TYPES`).
pub const OPAQUE_DRIVER_VERSION: u16 = 3;
pub const OPAQUE_VBIOS_VERSION: u16 = 6;

/// The report's driver version string (NUL-terminated ASCII), lower-cased.
pub fn report_driver_version(r: &GpuReport) -> Result<String, String> {
    let v = r
        .opaque_field(OPAQUE_DRIVER_VERSION)
        .ok_or_else(|| "report carries no driver version".to_string())?;
    let v = v.split(|&b| b == 0).next().unwrap_or(&[]);
    let s = std::str::from_utf8(v).map_err(|_| "driver version is not ASCII".to_string())?;
    if s.is_empty() || !s.is_ascii() {
        return Err("driver version is empty or not ASCII".into());
    }
    Ok(s.to_ascii_lowercase())
}

/// The report's VBIOS version as `xx.xx.xx.xx.xx` (nvtrust `format_vbios_version`): of the
/// 8-byte little-endian value, the upper 32 bits as four bytes, then the next byte down.
pub fn report_vbios_version(r: &GpuReport) -> Result<String, String> {
    let v = r
        .opaque_field(OPAQUE_VBIOS_VERSION)
        .ok_or_else(|| "report carries no VBIOS version".to_string())?;
    if v.len() != 8 {
        return Err(format!(
            "VBIOS version TLV is {} bytes, expected 8",
            v.len()
        ));
    }
    Ok(format!(
        "{:02x}.{:02x}.{:02x}.{:02x}.{:02x}",
        v[3], v[2], v[1], v[0], v[4]
    ))
}

/// Derive the goldens for `report` from a verified driver RIM and VBIOS RIM.
///
/// Refuses unless: both RIMs are for `product`; the driver RIM's version equals the report's
/// driver version and the VBIOS RIM's the report's VBIOS version (nvtrust only warns on a
/// mismatch); no index is active in both. Each index active in exactly one RIM gets that
/// RIM's alternatives. An index active in neither gets the all-zero value, so a GPU that
/// reports a non-zero measurement where neither RIM expects one is refused (stricter than
/// nvtrust, which ignores inactive indices). `allow_uncovered` is false.
pub fn goldens_from_rims(
    report: &GpuReport,
    driver: &VerifiedRim,
    vbios: &VerifiedRim,
    product: &str,
) -> Result<GoldenMeasurements, String> {
    for (what, rim) in [("driver", driver), ("VBIOS", vbios)] {
        if rim.product != product {
            return Err(format!("{what} RIM is for {}, not {product}", rim.product));
        }
    }
    let dv = report_driver_version(report)?;
    if driver.colloquial_version.to_ascii_lowercase() != dv {
        return Err(format!(
            "driver RIM is for {}, the GPU runs driver {dv}",
            driver.colloquial_version
        ));
    }
    let vv = report_vbios_version(report)?;
    if vbios.colloquial_version.to_ascii_lowercase() != vv {
        return Err(format!(
            "VBIOS RIM is for {}, the GPU runs VBIOS {vv}",
            vbios.colloquial_version
        ));
    }
    let mut values = BTreeMap::new();
    for &spdm_index in report.measurements.keys() {
        let rim_index = spdm_index
            .checked_sub(1)
            .ok_or_else(|| "SPDM measurement index 0 has no RIM entry".to_string())?;
        let d = driver.measurements.get(&rim_index).filter(|m| m.active);
        let v = vbios.measurements.get(&rim_index).filter(|m| m.active);
        let accepted = match (d, v) {
            (Some(_), Some(_)) => {
                return Err(format!("measurement {rim_index} is active in both RIMs"))
            }
            (Some(m), None) | (None, Some(m)) => m.values.clone(),
            (None, None) => vec![vec![0u8; SHA384_LEN]],
        };
        values.insert(spdm_index, accepted);
    }
    for (what, rim) in [("driver", driver), ("VBIOS", vbios)] {
        for m in rim.measurements.values().filter(|m| m.active) {
            if !report.measurements.contains_key(&(m.index + 1)) {
                return Err(format!(
                    "{what} RIM measurement {} ({}) is absent from the report",
                    m.index, m.name
                ));
            }
        }
    }
    Ok(GoldenMeasurements {
        values,
        allow_uncovered: false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    pub(crate) const DRIVER_RIM: &[u8] =
        include_bytes!("../tests/data/nvidia_rim_driver_GH100_550.90.07.swidtag");
    pub(crate) const VBIOS_RIM: &[u8] =
        include_bytes!("../tests/data/nvidia_rim_vbios_1010_0200_882_96009F0001.swidtag");

    /// 2026-03-01T00:00:00Z: inside every RIM and device certificate's validity window.
    pub(crate) fn t1() -> ASN1Time {
        ASN1Time::from_timestamp(1_772_323_200).unwrap()
    }

    fn replace_once(hay: &[u8], from: &str, to: &str) -> Vec<u8> {
        let s = std::str::from_utf8(hay).unwrap();
        assert_eq!(
            s.matches(from).count(),
            1,
            "fixture edit {from:?} must be unique"
        );
        s.replacen(from, to, 1).into_bytes()
    }

    #[test]
    fn nvidia_rims_verify() {
        let d = verify_rim(DRIVER_RIM, t1()).expect("driver RIM verifies");
        assert_eq!(
            (d.product.as_str(), d.colloquial_version.as_str()),
            ("GH100", "550.90.07")
        );
        let v = verify_rim(VBIOS_RIM, t1()).expect("VBIOS RIM verifies");
        assert_eq!(v.colloquial_version, "96.00.9F.00.01");
        assert_eq!(d.measurements.values().filter(|m| m.active).count(), 21);
        assert_eq!(v.measurements.values().filter(|m| m.active).count(), 12);
    }

    /// Each edit must refuse, so the accept above is not vacuous.
    #[test]
    fn nvidia_rim_refusals() {
        // a signed measurement value altered: digest refuses
        let i = std::str::from_utf8(VBIOS_RIM)
            .unwrap()
            .find("Hash0=\"")
            .unwrap()
            + 7;
        let mut t = VBIOS_RIM.to_vec();
        t[i] = if t[i] == b'0' { b'1' } else { b'0' };
        assert!(verify_rim(&t, t1()).unwrap_err().contains("digest"));
        // the signature value altered: signature refuses
        let s = std::str::from_utf8(VBIOS_RIM).unwrap();
        let j = s.find("<ds:SignatureValue>").unwrap() + 19;
        let mut t = VBIOS_RIM.to_vec();
        t[j] = if t[j] == b'A' { b'B' } else { b'A' };
        assert!(verify_rim(&t, t1()).is_err());
        // a comment inserted: outside the subset
        let t = replace_once(VBIOS_RIM, "<ns0:Payload", "<!-- x --><ns0:Payload");
        assert!(verify_rim(&t, t1()).unwrap_err().contains("subset"));
        // a DOCTYPE with an entity: outside the subset
        let mut t = b"<!DOCTYPE x [<!ENTITY e \"y\">]>".to_vec();
        t.extend_from_slice(VBIOS_RIM);
        assert!(verify_rim(&t, t1()).is_err());
        // a second (wrapping) Signature element: refused before any digest
        let t = replace_once(
            VBIOS_RIM,
            "<ns0:Payload",
            "<ds:Signature xmlns:ds=\"http://www.w3.org/2000/09/xmldsig#\"/><ns0:Payload",
        );
        assert!(verify_rim(&t, t1()).unwrap_err().contains("Signature"));
        // after the signer certificate's expiry: chain refuses
        let late = ASN1Time::from_timestamp(1_793_946_704).unwrap(); // 2026-11-06T06:31:44Z
        assert!(verify_rim(DRIVER_RIM, late)
            .unwrap_err()
            .contains("not valid"));
        // a RIM signed under a different root is refused: cut the root from KeyInfo
        let s = std::str::from_utf8(VBIOS_RIM).unwrap();
        let k = s.rfind("<ds:X509Certificate>").unwrap();
        let e = s.rfind("</ds:X509Certificate>").unwrap() + 21;
        let t = format!("{}{}", &s[..k], &s[e..]);
        assert!(verify_rim(t.as_bytes(), t1())
            .unwrap_err()
            .contains("pinned"));
    }
}
