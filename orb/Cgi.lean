/-
# Cgi — the CGI/1.1 gateway (RFC 3875)

A total model of the two halves of a CGI gateway:

  * **Request → meta-variable environment** (RFC 3875 §4.1): the server maps
    an HTTP request onto the fixed set of CGI meta-variables (AUTH_TYPE,
    CONTENT_LENGTH, CONTENT_TYPE, GATEWAY_INTERFACE, PATH_INFO,
    PATH_TRANSLATED, QUERY_STRING, REMOTE_ADDR, REMOTE_HOST, REMOTE_IDENT,
    REMOTE_USER, REQUEST_METHOD, SCRIPT_NAME, SERVER_NAME, SERVER_PORT,
    SERVER_PROTOCOL, SERVER_SOFTWARE). The mapping is TOTAL: every
    meta-variable receives a value (possibly the empty string for the
    optional ones, per the §4.1 `"" | ...` productions).
  * **Response framing** (RFC 3875 §6.2): the script's header fields are
    classified into one of the four CGI response types — document response
    (§6.2.1), local redirect (§6.2.2), client redirect (§6.2.3), client
    redirect with document (§6.2.4) — and the server-visible HTTP status is
    derived (document defaults to 200; a bare client redirect becomes 302).

Everything the script computes enters as opaque strings/bytes; the gateway
models only the meta-variable mapping and the response classification, not
process execution. This is the boundary: theorems are about the shape of the
environment and the response classification, not about running a program.

Theorems:
  * `cgi_env_total`            — the environment is total: every meta-variable
                                 appears in the constructed environment list
                                 with its value (full domain coverage).
  * `name_injective`           — distinct meta-variables have distinct names
                                 (no two env entries collide on a key).
  * `env_requestMethod` etc.   — the mapping is faithful to the request fields.
  * `cgi_document_default_200`  — a document response with no Status defaults
                                 to 200 (§6.2.1).
  * `cgi_client_redirect_302`   — a bare client redirect yields HTTP 302
                                 (§6.2.3).
  * `cgi_framing_total`        — at least one CGI field ⇒ the response is
                                 classified (§6.3 "at least one CGI field MUST
                                 be supplied"); with none it is malformed.

Left as a boundary / UNCLOSED:
  * NPH (non-parsed-header) responses (RFC 3875 §5.2) are out of scope.
  * The `protocol-specific` / `extension` header fields (§6.3.4/§6.3.5) are
    not carried through; only the three CGI fields (Content-Type, Location,
    Status) drive classification.
  * PATH_TRANSLATED derivation (§4.1.6, from PATH_INFO + a document-root map)
    is modeled as a supplied request field, not computed here.
-/

namespace Cgi

/-- Raw bytes, modeled as a list. -/
abbrev Bytes := List UInt8

/-! ## Meta-variables (RFC 3875 §4.1) -/

/-- The CGI/1.1 request meta-variables (RFC 3875 §4.1, the
`meta-variable-name` production). -/
inductive Meta where
  | authType | contentLength | contentType | gatewayInterface
  | pathInfo | pathTranslated | queryString | remoteAddr | remoteHost
  | remoteIdent | remoteUser | requestMethod | scriptName
  | serverName | serverPort | serverProtocol | serverSoftware
deriving DecidableEq, Repr

/-- The environment-variable name of a meta-variable (RFC 3875 §4.1). -/
def Meta.name : Meta → String
  | .authType => "AUTH_TYPE"
  | .contentLength => "CONTENT_LENGTH"
  | .contentType => "CONTENT_TYPE"
  | .gatewayInterface => "GATEWAY_INTERFACE"
  | .pathInfo => "PATH_INFO"
  | .pathTranslated => "PATH_TRANSLATED"
  | .queryString => "QUERY_STRING"
  | .remoteAddr => "REMOTE_ADDR"
  | .remoteHost => "REMOTE_HOST"
  | .remoteIdent => "REMOTE_IDENT"
  | .remoteUser => "REMOTE_USER"
  | .requestMethod => "REQUEST_METHOD"
  | .scriptName => "SCRIPT_NAME"
  | .serverName => "SERVER_NAME"
  | .serverPort => "SERVER_PORT"
  | .serverProtocol => "SERVER_PROTOCOL"
  | .serverSoftware => "SERVER_SOFTWARE"

/-- The complete list of meta-variables (RFC 3875 §4.1). -/
def allMetas : List Meta :=
  [.authType, .contentLength, .contentType, .gatewayInterface,
   .pathInfo, .pathTranslated, .queryString, .remoteAddr, .remoteHost,
   .remoteIdent, .remoteUser, .requestMethod, .scriptName,
   .serverName, .serverPort, .serverProtocol, .serverSoftware]

/-- Every meta-variable is in `allMetas` (the list is complete). -/
theorem mem_allMetas (m : Meta) : m ∈ allMetas := by
  cases m <;> decide

/-- **Names are injective**: distinct meta-variables have distinct
environment names, so the constructed environment has no key collisions. -/
theorem name_injective (a b : Meta) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

/-! ## The request the server maps to the environment -/

/-- The request fields the CGI meta-variable mapping reads. Optional
meta-variables default to the empty string, matching the RFC 3875 §4.1
`"" | ...` productions; `gatewayInterface` defaults to the required
`"CGI/1.1"` (§4.1.4). -/
structure Req where
  requestMethod : String
  scriptName : String
  pathInfo : String := ""
  pathTranslated : String := ""
  queryString : String := ""
  serverName : String
  serverPort : String
  serverProtocol : String
  serverSoftware : String
  gatewayInterface : String := "CGI/1.1"
  contentType : String := ""
  contentLength : String := ""
  authType : String := ""
  remoteAddr : String
  remoteHost : String := ""
  remoteIdent : String := ""
  remoteUser : String := ""

/-! ## The meta-variable mapping (RFC 3875 §4.1) -/

/-- Map a request onto a meta-variable's value (RFC 3875 §4.1). Total: every
meta-variable has a defined value. -/
def env (req : Req) : Meta → String
  | .authType => req.authType
  | .contentLength => req.contentLength
  | .contentType => req.contentType
  | .gatewayInterface => req.gatewayInterface
  | .pathInfo => req.pathInfo
  | .pathTranslated => req.pathTranslated
  | .queryString => req.queryString
  | .remoteAddr => req.remoteAddr
  | .remoteHost => req.remoteHost
  | .remoteIdent => req.remoteIdent
  | .remoteUser => req.remoteUser
  | .requestMethod => req.requestMethod
  | .scriptName => req.scriptName
  | .serverName => req.serverName
  | .serverPort => req.serverPort
  | .serverProtocol => req.serverProtocol
  | .serverSoftware => req.serverSoftware

/-- The constructed environment: every meta-variable paired with its value
for this request (`(NAME, value)` entries). -/
def envList (req : Req) : List (String × String) :=
  allMetas.map (fun m => (m.name, env req m))

/-- **`cgi_env_total`.** The environment is TOTAL over the meta-variable
domain: for every meta-variable `m`, the pair `(m.name, env req m)` occurs
in the constructed environment. No meta-variable is left unmapped. -/
theorem cgi_env_total (req : Req) (m : Meta) :
    (m.name, env req m) ∈ envList req := by
  unfold envList
  exact List.mem_map.mpr ⟨m, mem_allMetas m, rfl⟩

/-- The environment carries exactly one entry per meta-variable — its length
is the number of meta-variables (17), with no duplicates introduced. -/
theorem envList_length (req : Req) : (envList req).length = 17 := by
  unfold envList allMetas
  simp

/-! ### The mapping is faithful (a sampling of the §4.1 sub-sections) -/

theorem env_requestMethod (req : Req) :
    env req .requestMethod = req.requestMethod := rfl
theorem env_scriptName (req : Req) :
    env req .scriptName = req.scriptName := rfl
theorem env_pathInfo (req : Req) :
    env req .pathInfo = req.pathInfo := rfl
theorem env_queryString (req : Req) :
    env req .queryString = req.queryString := rfl
theorem env_serverProtocol (req : Req) :
    env req .serverProtocol = req.serverProtocol := rfl

/-! ## Response framing (RFC 3875 §6.2) -/

/-- The four CGI response types (RFC 3875 §6.2). -/
inductive CgiResp where
  /-- §6.2.1 Document Response: a Content-Type, a status, and a body. -/
  | document (contentType : String) (status : Nat) (body : Bytes)
  /-- §6.2.2 Local Redirect Response: a local `path?query` the server
  reprocesses (no other fields, no body). -/
  | localRedirect (pathQuery : String)
  /-- §6.2.3 Client Redirect Response: an absolute URI; the server emits a
  302 to the client. -/
  | clientRedirect (location : String)
  /-- §6.2.4 Client Redirect Response with Document. -/
  | clientRedirectDoc (location : String) (status : Nat) (contentType : String)
      (body : Bytes)
deriving Repr

/-- The script's parsed header block: the three CGI header fields (§6.3),
each optional in the raw output, plus the response body. -/
structure ScriptOut where
  contentType : Option String := none
  location : Option String := none
  status : Option Nat := none
  body : Bytes := []

/-- A `Location` value is *local* (§6.2.2) when it is a path — modeled as
beginning with `/` — as opposed to an absolute client URI (§6.2.3). -/
def isLocal (loc : String) : Bool := loc.startsWith "/"

/-- **Classify** the script output into a CGI response type (RFC 3875 §6.2),
or `none` when malformed (no CGI field at all — §6.3 requires at least one).

  * `Location` present and local → local redirect (§6.2.2).
  * `Location` present, absolute, with Status **and** Content-Type → client
    redirect with document (§6.2.4).
  * `Location` present, absolute, otherwise → client redirect (§6.2.3).
  * no `Location`, Content-Type present → document response (§6.2.1), with
    Status defaulting to 200 when omitted.
  * neither → malformed.
-/
def classify (o : ScriptOut) : Option CgiResp :=
  match o.location with
  | some loc =>
    if isLocal loc then
      some (.localRedirect loc)
    else
      match o.status, o.contentType with
      | some st, some ct => some (.clientRedirectDoc loc st ct o.body)
      | _, _ => some (.clientRedirect loc)
  | none =>
    match o.contentType with
    | some ct => some (.document ct (o.status.getD 200) o.body)
    | none => none

/-- The HTTP status a CGI response yields to the client. A document uses its
own status; a local redirect is reprocessed internally (modeled as 200 once
served); a bare client redirect becomes 302 (§6.2.3); a client redirect with
document uses its supplied status (§6.2.4). -/
def CgiResp.httpStatus : CgiResp → Nat
  | .document _ st _ => st
  | .localRedirect _ => 200
  | .clientRedirect _ => 302
  | .clientRedirectDoc _ st _ _ => st

/-- **`cgi_document_default_200`.** A document response (no Location,
Content-Type present) with no Status header defaults to status 200
(RFC 3875 §6.2.1). -/
theorem cgi_document_default_200 (ct : String) (body : Bytes) :
    classify { contentType := some ct, location := none, status := none,
               body := body }
      = some (.document ct 200 body) := by
  simp [classify]

/-- **`cgi_client_redirect_302`.** A bare client redirect (absolute Location,
no Status/Content-Type) yields HTTP 302 to the client (RFC 3875 §6.2.3). -/
theorem cgi_client_redirect_302 (loc : String) (body : Bytes)
    (habs : isLocal loc = false) :
    ∃ r, classify { location := some loc, contentType := none, status := none,
                    body := body } = some r ∧ r.httpStatus = 302 := by
  refine ⟨.clientRedirect loc, ?_, rfl⟩
  simp [classify, habs]

/-- **`cgi_framing_total`.** If the script supplies at least one CGI header
field (a Content-Type or a Location), the response is classified — `classify`
is defined (RFC 3875 §6.3: "at least one CGI field MUST be supplied"). -/
theorem cgi_framing_total (o : ScriptOut)
    (h : o.contentType.isSome ∨ o.location.isSome) :
    (classify o).isSome := by
  unfold classify
  cases hloc : o.location with
  | some loc =>
    by_cases hl : isLocal loc
    · simp [hl]
    · simp only [hl, if_false]
      cases o.status <;> cases o.contentType <;> rfl
  | none =>
    cases hct : o.contentType with
    | some ct => simp
    | none => rw [hloc, hct] at h; simp at h

/-- A response with no CGI field at all is malformed (`none`) — the
contrapositive boundary of `cgi_framing_total`. -/
theorem cgi_malformed (body : Bytes) :
    classify { contentType := none, location := none, status := none,
               body := body } = none := rfl

/-! ## Concrete witnesses (RFC 3875 §6.2) -/

/-- A local `Location` (a path) classifies as a §6.2.2 local redirect the
server reprocesses internally. -/
theorem local_redirect_classifies (loc : String) (h : isLocal loc = true) :
    classify { location := some loc } = some (.localRedirect loc) := by
  simp only [classify, h, if_true]

/-- A client redirect with document supplies its own 302 status (§6.2.4). -/
theorem client_redirectdoc_example :
    (CgiResp.clientRedirectDoc "https://example/x" 302 "text/html" []).httpStatus
      = 302 := by decide

end Cgi
