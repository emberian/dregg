//! THE STRUCTURED EGRESS DOOR — the ONE cap-gated, off-by-default, revocable way
//! a jailed agent reaches a SPECIFIC outside resource.
//!
//! ## Why this exists (the third leg of dregg-as-host)
//!
//! The jail ([`crate::confined`]) denies the agent ALL ambient authority: its own
//! base shell / file tools hit the OS sandbox walls and go inert. dregg's tools
//! ([`crate::mcp_server`]) are then the agent's only *effective* effect-path —
//! but they route to OUR containers (a deos-js World, a confined PD), never the
//! host. So by construction the jailed agent has NO reach to the real outside.
//!
//! That total denial is the safe default, but a USEFUL agent sometimes must touch
//! one specific external thing (a project directory, a docs tree). The structured
//! egress is exactly that and nothing more: a HOST-granted [`EgressGrant`] naming
//! ONE host path (or, later, one endpoint), read-only, that the host threads into
//! the jail's sandbox profile as a single SBPL/Landlock allow-rule. Everything
//! else stays denied.
//!
//! ## The three load-bearing properties (each provable by running)
//!
//!   1. **Off by default.** A jail launched with [`EgressPolicy::sealed`] (the
//!      default) carries no grant → the sandbox profile is the Endpoint-only jail
//!      → the granted path is DENIED inside the PD exactly like any other path.
//!   2. **Granted = a specific door, not a hole.** [`EgressPolicy::grant_read`]
//!      names ONE subpath. Inside the PD that subpath becomes readable; a SIBLING
//!      path (outside the grant) stays denied. The door is to a specific resource,
//!      not "the filesystem".
//!   3. **Revocable.** [`EgressPolicy::revoke`] drops the grant; the NEXT jail
//!      launched under the policy is sealed again. A grant is a capability the
//!      host holds and can take back — it never becomes ambient.
//!
//! The grant is consulted by the host when it builds the confined PD's
//! [`Confinement`](dregg_firmament::sandbox::Confinement) (via
//! [`EgressPolicy::confinement_for`]); the agent never mints its own egress.

#![cfg(unix)]

/// ONE granted egress door: a read-only host path the jailed agent may reach.
///
/// This is the capability the HOST holds. It is deliberately minimal — a single
/// canonical subpath, read-only — so the door is to a *named resource*, not a
/// class of authority. (A network-endpoint variant is the next slice; the same
/// shape — a specific, granted, revocable target — applies.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EgressGrant {
    /// The host filesystem subpath the agent is granted read access to. Becomes
    /// exactly one `(allow file-read* (subpath "<path>"))` SBPL rule on macOS / a
    /// Landlock read rule on Linux — and NOTHING else opens.
    pub read_path: String,
}

impl EgressGrant {
    /// A read-only grant for one host subpath.
    pub fn read(path: impl Into<String>) -> EgressGrant {
        EgressGrant {
            read_path: path.into(),
        }
    }
}

/// ONE granted egress SOCKET door: a single outbound network endpoint the jailed
/// agent may connect to — and NOTHING else. This is the provider-only door: a
/// jailed LIVE brain's model-provider call rides EXACTLY this host:port; every
/// other host, every other port, and all inbound stay denied.
///
/// It is the network sibling of [`EgressGrant`]: the same shape — a specific,
/// granted, revocable target the HOST holds — over a socket instead of a file.
/// Deny-default: without a grant the jail has no outbound network at all.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EgressNetGrant {
    /// The provider host — a literal IP (`127.0.0.1`, the precise case the OS
    /// network-allow matches) or a hostname (see the in-jail-DNS caveat below).
    pub host: String,
    /// The provider TCP port (e.g. 443 for an https provider, or the mock port).
    pub port: u16,
}

impl EgressNetGrant {
    /// A grant to one outbound endpoint.
    pub fn new(host: impl Into<String>, port: u16) -> EgressNetGrant {
        EgressNetGrant {
            host: host.into(),
            port,
        }
    }

    /// The `"host:port"` form the OS network-allow rule (macOS SBPL `remote ip`)
    /// matches against.
    pub fn endpoint(&self) -> String {
        format!("{}:{}", self.host, self.port)
    }
}

/// THE EGRESS POLICY — the host's standing set of granted doors for a jailed
/// agent. Sealed (no doors) by default; the host opens specific doors with
/// [`Self::grant_read`] and takes them back with [`Self::revoke`].
///
/// The policy is the bridge between a cap-gated grant and the OS sandbox profile:
/// [`Self::confinement_for`] folds every live grant into the
/// [`Confinement`](dregg_firmament::sandbox::Confinement) the host hands to
/// [`ProcessKernel::spawn_pd_confined_with`](dregg_firmament::process_kernel::ProcessKernel::spawn_pd_confined_with).
#[derive(Clone, Debug, Default)]
pub struct EgressPolicy {
    grants: Vec<EgressGrant>,
    /// The granted outbound SOCKET doors (the provider-only network endpoints).
    /// Deny-default: empty ⇒ no outbound network at all in the jail.
    net_grants: Vec<EgressNetGrant>,
}

impl EgressPolicy {
    /// The default: SEALED — no egress doors. A jail built from this denies every
    /// host path (the agent reaches the outside only through dregg's tools, which
    /// route to our containers).
    pub fn sealed() -> EgressPolicy {
        EgressPolicy {
            grants: Vec::new(),
            net_grants: Vec::new(),
        }
    }

    /// Whether the policy currently grants no egress (the safe default state) —
    /// no read doors AND no socket doors.
    pub fn is_sealed(&self) -> bool {
        self.grants.is_empty() && self.net_grants.is_empty()
    }

    /// GRANT a read-only door to one specific host subpath. Idempotent on the same
    /// path. This is the explicit, opt-in act the host performs to let the agent
    /// reach a named outside resource; without it the path stays denied.
    pub fn grant_read(&mut self, path: impl Into<String>) -> &mut EgressPolicy {
        let g = EgressGrant::read(path);
        if !self.grants.contains(&g) {
            self.grants.push(g);
        }
        self
    }

    /// REVOKE the door to `path` (if granted). The next jail built from this policy
    /// is sealed against that path again — the grant was a capability the host
    /// held, now taken back; it never became ambient authority the agent keeps.
    pub fn revoke(&mut self, path: &str) -> &mut EgressPolicy {
        self.grants.retain(|g| g.read_path != path);
        self
    }

    /// The live grants (the doors currently open), for the mandate inspector.
    pub fn grants(&self) -> &[EgressGrant] {
        &self.grants
    }

    /// GRANT the provider-only SOCKET door to exactly `host:port`. This is the
    /// explicit, opt-in act the host performs to let a jailed LIVE brain reach its
    /// model provider — and ONLY that endpoint; every other host/port stays denied.
    /// Idempotent on the same endpoint. Without it the jail has no outbound network.
    pub fn grant_provider(&mut self, host: impl Into<String>, port: u16) -> &mut EgressPolicy {
        let g = EgressNetGrant::new(host, port);
        if !self.net_grants.contains(&g) {
            self.net_grants.push(g);
        }
        self
    }

    /// GRANT the provider door from a base URL (e.g. `https://api.anthropic.com` →
    /// `api.anthropic.com:443`, `http://127.0.0.1:8899/v1` → `127.0.0.1:8899`).
    /// This is the shape the host uses: it derives the door target from the LIVE
    /// brain's configured provider base URL, so the door is exactly where the
    /// brain will call. Returns `false` (grants nothing) if the URL has no host.
    pub fn grant_provider_url(&mut self, base_url: &str) -> bool {
        match provider_host_port(base_url) {
            Some((host, port)) => {
                self.grant_provider(host, port);
                true
            }
            None => false,
        }
    }

    /// REVOKE the provider door to `host:port` (if granted). The next jail built
    /// from this policy is sealed against that endpoint again — a capability the
    /// host held, now taken back; it never became ambient network authority.
    pub fn revoke_provider(&mut self, host: &str, port: u16) -> &mut EgressPolicy {
        self.net_grants
            .retain(|g| !(g.host == host && g.port == port));
        self
    }

    /// The live socket doors (the provider endpoints currently open).
    pub fn net_grants(&self) -> &[EgressNetGrant] {
        &self.net_grants
    }

    /// Whether an outbound connect to `host:port` is admissible under THIS policy —
    /// i.e. exactly a granted endpoint. The host uses this to decide admissibility
    /// BEFORE it threads the endpoint into the sandbox; the OS sandbox is the
    /// enforcing backstop (an ungranted endpoint is physically EPERM in the PD).
    pub fn admits_connect(&self, host: &str, port: u16) -> bool {
        self.net_grants
            .iter()
            .any(|g| g.host == host && g.port == port)
    }

    /// Whether `path` is reachable under THIS policy — i.e. it is at or beneath a
    /// granted subpath. The host uses this to decide whether an egress request is
    /// admissible BEFORE it ever threads a path into the sandbox; the OS sandbox is
    /// the enforcing backstop (a path not granted is physically denied in the PD).
    pub fn admits_read(&self, path: &str) -> bool {
        self.grants.iter().any(|g| path_under(path, &g.read_path))
    }

    /// Fold every live grant into a confined-PD profile: the Endpoint-only jail
    /// (`control_fd` kept; file/net/exec denied) PLUS exactly the granted read
    /// paths. Hand the result to
    /// [`ProcessKernel::spawn_pd_confined_with`](dregg_firmament::process_kernel::ProcessKernel::spawn_pd_confined_with).
    ///
    /// Sealed policy ⇒ an Endpoint-only [`Confinement`] (identical to the implicit
    /// jail). Each grant ⇒ one allow-subpath rule and nothing more.
    pub fn confinement_for(
        &self,
        control_fd: std::os::unix::io::RawFd,
    ) -> dregg_firmament::sandbox::Confinement {
        let mut c = dregg_firmament::sandbox::Confinement::endpoint_only(control_fd);
        for g in &self.grants {
            // The OS sandbox (macOS Seatbelt `subpath` / Linux Landlock) matches the
            // CANONICAL (symlink-resolved) path the kernel sees after `open` follows
            // symlinks — e.g. macOS `$TMPDIR` (`/var/folders/…`) resolves to
            // `/private/var/folders/…`. Grant the resolved path so the rule the
            // kernel checks against actually matches the granted resource. (Falls
            // back to the literal path if it cannot be resolved yet.)
            let resolved = std::fs::canonicalize(&g.read_path)
                .ok()
                .and_then(|p| p.to_str().map(|s| s.to_string()))
                .unwrap_or_else(|| g.read_path.clone());
            c = c.with_read_path(resolved);
        }
        // Each granted provider endpoint ⇒ one outbound network-allow rule and
        // nothing more. Sealed (no net grants) ⇒ no outbound network at all.
        for g in &self.net_grants {
            c = c.with_net_out(g.endpoint());
        }
        c
    }
}

/// Extract `(host, port)` from a provider **base URL** — the door target the host
/// derives from the LIVE brain's configured provider base. Understands an optional
/// `scheme://`, an explicit `:port`, and the default ports (`https` → 443, `http`
/// → 80, no scheme → 443). The path/query are ignored. `None` if there is no host.
///
/// Examples:
///   * `https://api.anthropic.com/v1/messages` → `("api.anthropic.com", 443)`
///   * `http://127.0.0.1:8899/v1`              → `("127.0.0.1", 8899)`
///   * `api.moonshot.ai`                        → `("api.moonshot.ai", 443)`
pub fn provider_host_port(base_url: &str) -> Option<(String, u16)> {
    let s = base_url.trim();
    // Split off the scheme (default port depends on it).
    let (default_port, rest) = if let Some(r) = s.strip_prefix("https://") {
        (443u16, r)
    } else if let Some(r) = s.strip_prefix("http://") {
        (80u16, r)
    } else {
        (443u16, s)
    };
    // The authority is everything up to the first '/', '?', or '#'.
    let authority = rest.split(['/', '?', '#']).next().unwrap_or("").trim();
    if authority.is_empty() {
        return None;
    }
    // Strip any userinfo ("user:pass@host") — keep the host[:port] after '@'.
    let hostport = authority.rsplit('@').next().unwrap_or(authority);
    // host:port — a bare IPv6 (`[::1]:port`) is out of scope for the provider door
    // (providers are named hosts / IPv4); split on the LAST ':' so a scheme-less
    // "host:port" parses, but a host with no ':' takes the default port.
    match hostport.rsplit_once(':') {
        Some((host, port_str)) if !host.is_empty() => {
            let port = port_str.parse::<u16>().ok()?;
            Some((host.to_string(), port))
        }
        _ => Some((hostport.to_string(), default_port)),
    }
}

/// Whether `path` is at or beneath the granted `base` subpath (a textual subpath
/// check mirroring SBPL/Landlock `subpath` semantics: `base` itself, or `base/…`).
fn path_under(path: &str, base: &str) -> bool {
    if path == base {
        return true;
    }
    let with_sep = if base.ends_with('/') {
        base.to_string()
    } else {
        format!("{base}/")
    };
    path.starts_with(&with_sep)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sealed_by_default_admits_nothing() {
        let p = EgressPolicy::sealed();
        assert!(p.is_sealed());
        assert!(!p.admits_read("/tmp/anything"));
    }

    #[test]
    fn grant_opens_exactly_one_door_revoke_closes_it() {
        let mut p = EgressPolicy::sealed();
        p.grant_read("/tmp/deos_egress");
        assert!(!p.is_sealed());
        // The granted subpath + things beneath it are admitted.
        assert!(p.admits_read("/tmp/deos_egress"));
        assert!(p.admits_read("/tmp/deos_egress/notes.txt"));
        // A SIBLING outside the grant is NOT a door.
        assert!(!p.admits_read("/tmp/deos_egress_evil"));
        assert!(!p.admits_read("/etc/passwd"));
        // Revoke closes it.
        p.revoke("/tmp/deos_egress");
        assert!(p.is_sealed());
        assert!(!p.admits_read("/tmp/deos_egress"));
    }

    #[test]
    fn confinement_carries_the_grant_into_the_profile() {
        let mut p = EgressPolicy::sealed();
        // Sealed → endpoint-only (no read paths).
        let sealed = p.confinement_for(7);
        assert!(sealed.read_paths.is_empty());
        // Granted → exactly that read path in the profile.
        p.grant_read("/tmp/deos_egress");
        let open = p.confinement_for(7);
        assert_eq!(open.read_paths, vec!["/tmp/deos_egress".to_string()]);
    }

    #[test]
    fn provider_socket_door_grant_revoke_and_admit() {
        let mut p = EgressPolicy::sealed();
        assert!(p.is_sealed());
        // Grant one provider endpoint.
        p.grant_provider("127.0.0.1", 8899);
        assert!(!p.is_sealed(), "a socket door is an egress grant");
        assert!(
            p.admits_connect("127.0.0.1", 8899),
            "exactly the granted door"
        );
        // A DIFFERENT port / host is NOT a door.
        assert!(!p.admits_connect("127.0.0.1", 9999), "other port denied");
        assert!(!p.admits_connect("1.1.1.1", 8899), "other host denied");
        // Revoke closes it → sealed again.
        p.revoke_provider("127.0.0.1", 8899);
        assert!(p.is_sealed());
        assert!(!p.admits_connect("127.0.0.1", 8899));
    }

    #[test]
    fn provider_endpoint_folds_into_the_confinement_net_out() {
        let mut p = EgressPolicy::sealed();
        // Sealed → no outbound network at all.
        assert!(p.confinement_for(7).net_out.is_empty());
        // Granted → exactly that endpoint in the profile's net-allow list.
        p.grant_provider("127.0.0.1", 8899);
        let open = p.confinement_for(7);
        assert_eq!(open.net_out, vec!["127.0.0.1:8899".to_string()]);
        // File + socket doors coexist without collision.
        p.grant_read("/tmp/deos_egress");
        let both = p.confinement_for(7);
        assert_eq!(both.net_out, vec!["127.0.0.1:8899".to_string()]);
        assert_eq!(both.read_paths, vec!["/tmp/deos_egress".to_string()]);
    }

    #[test]
    fn grant_provider_url_derives_the_door_from_a_base_url() {
        let mut p = EgressPolicy::sealed();
        assert!(p.grant_provider_url("http://127.0.0.1:8899/v1"));
        assert!(p.admits_connect("127.0.0.1", 8899));

        let mut q = EgressPolicy::sealed();
        assert!(q.grant_provider_url("https://api.anthropic.com/v1/messages"));
        assert!(
            q.admits_connect("api.anthropic.com", 443),
            "https default 443"
        );
    }

    #[test]
    fn provider_host_port_parses_scheme_port_and_defaults() {
        assert_eq!(
            provider_host_port("https://api.anthropic.com/v1/messages"),
            Some(("api.anthropic.com".to_string(), 443))
        );
        assert_eq!(
            provider_host_port("http://127.0.0.1:8899/v1"),
            Some(("127.0.0.1".to_string(), 8899))
        );
        assert_eq!(
            provider_host_port("http://example.com/x"),
            Some(("example.com".to_string(), 80))
        );
        assert_eq!(
            provider_host_port("api.moonshot.ai"),
            Some(("api.moonshot.ai".to_string(), 443))
        );
        assert_eq!(
            provider_host_port("localhost:1234"),
            Some(("localhost".to_string(), 1234))
        );
        assert_eq!(provider_host_port(""), None);
        assert_eq!(provider_host_port("https://"), None);
    }
}
