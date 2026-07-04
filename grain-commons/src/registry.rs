//! **Registry-as-cells** — the market is *just cells* (docs/THE-GRAIN.md §Commons).
//!
//! A grain-store listing is a **cell**: the author key, the `.spk` content hash, the
//! price/lease terms, and the invariant digests the agent is bound to. The
//! [`GrainRegistry`] holds those listing cells in a real committed umem heap
//! ([`sandstorm_bridge::Umem`], content-addressed to a [`sandstorm_bridge::DataRoot`]),
//! so the whole registry is a re-witnessable object — a light client checks the
//! registry root, not the operator's word.
//!
//! - **publish a listing** → write the listing cell into the heap (keyed by App ID).
//! - **discover** → read the cell back by App ID.
//! - **rent** → price a [`RentQuote`] against the listing's terms. **Honest
//!   stand-in:** the quote is the priced agreement record, NOT the funded lease
//!   itself — THE-GRAIN.md's "rent = open a lease" is realized by feeding these
//!   terms into the REAL lease machinery (`hosted-lease::HostedLease`, as
//!   `grain-fork`'s `Grain::rent` does). That weld is the named reconcile once the
//!   detached crates join one workspace; until then this module deliberately does
//!   not ship a shadow lease that pretends to hold funds.
//! - **review** → a **receipted turn**: an append that leaves a
//!   [`sandstorm_bridge::GrainReceipt`] binding *who reviewed which listing*. (The
//!   turn is shaped like the real thing; a full on-chain review turn is the named
//!   frontier — but the receipt it leaves is the genuine artifact.)

use sandstorm_bridge::grain::GrainReceipt;
use sandstorm_bridge::manifest::AppId;
use sandstorm_bridge::{DataRoot, Umem};
use serde::{Deserialize, Serialize};

/// The rent terms a listing offers — the "price" arm of the market. Renting prices a
/// [`RentQuote`] bounded by these. Deliberately NOT named `LeaseTerms`: the real
/// lease-terms vocabulary is `hosted-lease::LeaseTerms` (what `grain-fork`'s
/// `Grain::rent` takes), and shadowing its name here bred exactly the two-vocabulary
/// confusion the grain family is trying to kill.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ListingTerms {
    /// The rent charged per lease period (uptime unit).
    pub rent_per_period: u64,
    /// A refundable deposit taken when the lease opens.
    pub deposit: u64,
    /// The maximum number of periods a single lease may run.
    pub max_periods: u64,
}

/// A **review** of a listing — a receipted turn. The `rating` and `body_hash` are the
/// content; the [`GrainReceipt`] (produced by [`GrainRegistry::review`]) is the witnessed
/// artifact binding the reviewer to the listing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Review {
    /// Who left the review (the actor subject of the receipted turn).
    pub reviewer: String,
    /// A 0–5 star rating (clamped on ingest).
    pub rating: u8,
    /// A content hash of the review body (the turn's payload commitment).
    pub body_hash: [u8; 32],
}

/// A grain-store **listing** — a cell. Discoverable by [`GrainListing::app_id`]; every
/// field is committed into the registry heap.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainListing {
    /// The App ID — the author's signing key (provenance, and the discovery key).
    pub app_id: AppId,
    /// The `.spk` content hash the listing points at (what a renter installs).
    pub spk_hash: [u8; 32],
    /// The listing's human title.
    pub title: String,
    /// The rent/listing terms.
    pub terms: ListingTerms,
    /// The content-addressed **invariant digests** (hatchery `kind_id`s) the agent is
    /// bound to — a renter can check the agent carries the invariants it advertises.
    pub invariant_digests: Vec<[u8; 32]>,
    /// Receipted reviews, in arrival order.
    pub reviews: Vec<Review>,
}

impl GrainListing {
    /// A fresh listing (no reviews yet).
    pub fn new(
        app_id: AppId,
        spk_hash: [u8; 32],
        title: impl Into<String>,
        terms: ListingTerms,
        invariant_digests: Vec<[u8; 32]>,
    ) -> Self {
        GrainListing {
            app_id,
            spk_hash,
            title: title.into(),
            terms,
            invariant_digests,
            reviews: Vec::new(),
        }
    }

    /// The mean star rating over the receipted reviews (`None` if none yet).
    pub fn average_rating(&self) -> Option<f64> {
        if self.reviews.is_empty() {
            return None;
        }
        let sum: u64 = self.reviews.iter().map(|r| r.rating as u64).sum();
        Some(sum as f64 / self.reviews.len() as f64)
    }
}

/// A priced **rent quote** against a listing — the agreement record the market hands
/// a renter. Bounded by the listing's [`ListingTerms`]; a quote that would run past
/// `max_periods` is refused.
///
/// **Honestly a quote, not a lease.** No value moves here and nothing is funded:
/// opening the REAL funded lease (rent obligor + conservation + lapse audit) is
/// `hosted-lease::HostedLease` / `grain-fork::Grain::rent`, which these numbers
/// feed. This type used to be called `Lease`, which laundered that gap.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RentQuote {
    /// The listing this quote rents.
    pub app_id: AppId,
    /// Who asked to rent.
    pub renter: String,
    /// How many periods it would fund.
    pub periods: u64,
    /// The total to charge up front (`deposit + rent_per_period * periods`).
    pub total_cost: u64,
}

/// Why a registry operation was refused.
#[derive(Debug, PartialEq, Eq)]
pub enum RegistryError {
    /// No listing exists for that App ID.
    NotListed(AppId),
    /// A rent quote asked for more periods than the listing's terms allow.
    ExceedsMaxPeriods { asked: u64, max: u64 },
    /// A listing key already exists (a re-publish must be an explicit update).
    AlreadyListed(AppId),
    /// The quoted cost overflowed u64 (absurd terms × periods) — refused rather than
    /// silently wrapped into a cheap quote.
    CostOverflow,
}

impl std::fmt::Display for RegistryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegistryError::NotListed(a) => write!(f, "no listing for app id {}", a.0),
            RegistryError::ExceedsMaxPeriods { asked, max } => {
                write!(f, "rent of {asked} periods exceeds the listing max {max}")
            }
            RegistryError::AlreadyListed(a) => write!(f, "app id {} is already listed", a.0),
            RegistryError::CostOverflow => {
                write!(f, "rent quote overflows u64 — refused, not wrapped")
            }
        }
    }
}
impl std::error::Error for RegistryError {}

/// The grain-store registry: listing cells in a committed umem heap. The heap root
/// ([`GrainRegistry::root`]) is the registry's content commitment.
#[derive(Debug, Default)]
pub struct GrainRegistry {
    heap: Umem,
}

impl GrainRegistry {
    pub fn new() -> Self {
        GrainRegistry { heap: Umem::new() }
    }

    /// The umem heap key a listing cell lives at.
    fn key(app_id: &AppId) -> String {
        format!("listing/{}", app_id.0)
    }

    /// **Publish a listing** — write the listing cell into the registry heap. Refuses a
    /// duplicate App ID (a re-publish is [`GrainRegistry::update`]). Returns a receipt
    /// binding the publish to the resulting registry root.
    pub fn publish(&mut self, listing: GrainListing) -> Result<GrainReceipt, RegistryError> {
        let key = Self::key(&listing.app_id);
        if self.heap.get(&key).is_some() {
            return Err(RegistryError::AlreadyListed(listing.app_id));
        }
        let actor = listing.app_id.0.clone();
        Ok(self.write(listing, "list", actor))
    }

    /// Update an existing listing (e.g. to append reviews / bump the `.spk` hash).
    pub fn update(&mut self, listing: GrainListing) -> Result<GrainReceipt, RegistryError> {
        let key = Self::key(&listing.app_id);
        if self.heap.get(&key).is_none() {
            return Err(RegistryError::NotListed(listing.app_id));
        }
        let actor = listing.app_id.0.clone();
        Ok(self.write(listing, "relist", actor))
    }

    /// Write the listing cell and mint the receipt: one heap write, one commit — the
    /// receipt's `data_root` IS the resulting registry root, `actor` the principal
    /// that exercised the op.
    fn write(&mut self, listing: GrainListing, op: &str, actor: String) -> GrainReceipt {
        let key = Self::key(&listing.app_id);
        let cell_id = key.clone();
        let bytes = serde_json::to_vec(&listing).expect("listing serializes");
        self.heap.put(key, bytes);
        GrainReceipt {
            op: op.to_string(),
            cell_id,
            actor,
            data_root: Some(self.heap.commit().0),
        }
    }

    /// **Discover** a listing by App ID (the market's lookup). `None` if not listed.
    pub fn discover(&self, app_id: &AppId) -> Option<GrainListing> {
        let bytes = self.heap.get(&Self::key(app_id))?;
        serde_json::from_slice(bytes).ok()
    }

    /// Every listing in the registry (catalog browse), sorted by heap key.
    pub fn list_all(&self) -> Vec<GrainListing> {
        self.heap
            .iter()
            .filter(|(k, _)| k.starts_with("listing/"))
            .filter_map(|(_, v)| serde_json::from_slice(v).ok())
            .collect()
    }

    /// **Rent** a listing — price a [`RentQuote`] against its terms. Refused if the
    /// listing is unknown, the requested periods exceed the terms' `max_periods`, or
    /// the cost overflows. The quote's numbers feed the REAL lease open (see the
    /// module docs) — nothing is funded here.
    pub fn rent(
        &self,
        app_id: &AppId,
        renter: impl Into<String>,
        periods: u64,
    ) -> Result<RentQuote, RegistryError> {
        let listing = self
            .discover(app_id)
            .ok_or_else(|| RegistryError::NotListed(app_id.clone()))?;
        if periods > listing.terms.max_periods {
            return Err(RegistryError::ExceedsMaxPeriods {
                asked: periods,
                max: listing.terms.max_periods,
            });
        }
        let total_cost = listing
            .terms
            .rent_per_period
            .checked_mul(periods)
            .and_then(|rent| rent.checked_add(listing.terms.deposit))
            .ok_or(RegistryError::CostOverflow)?;
        Ok(RentQuote {
            app_id: app_id.clone(),
            renter: renter.into(),
            periods,
            total_cost,
        })
    }

    /// **Review** a listing — a receipted turn. Appends the review to the listing cell
    /// and returns the [`GrainReceipt`] binding the reviewer to the listing + the new
    /// registry root. The rating is clamped to 0–5.
    pub fn review(
        &mut self,
        app_id: &AppId,
        reviewer: impl Into<String>,
        rating: u8,
        body_hash: [u8; 32],
    ) -> Result<GrainReceipt, RegistryError> {
        let mut listing = self
            .discover(app_id)
            .ok_or_else(|| RegistryError::NotListed(app_id.clone()))?;
        let reviewer = reviewer.into();
        listing.reviews.push(Review {
            reviewer: reviewer.clone(),
            rating: rating.min(5),
            body_hash,
        });
        // One write, one commit — the receipt is stamped with the reviewer as actor.
        Ok(self.write(listing, "review", reviewer))
    }

    /// The registry's content commitment — the umem heap root over every listing cell.
    /// Two registries with the same listings commit to the same root (order-free).
    pub fn root(&self) -> DataRoot {
        self.heap.commit()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn app(id: &str) -> AppId {
        AppId(id.to_string())
    }

    fn terms() -> ListingTerms {
        ListingTerms {
            rent_per_period: 100,
            deposit: 50,
            max_periods: 10,
        }
    }

    fn listing(id: &str) -> GrainListing {
        GrainListing::new(app(id), [1u8; 32], format!("Agent {id}"), terms(), vec![])
    }

    #[test]
    fn a_listing_is_a_cell_discoverable_by_app_id() {
        let mut reg = GrainRegistry::new();
        let empty_root = reg.root();
        reg.publish(listing("aaa")).unwrap();
        // Discover it back by App ID.
        let got = reg.discover(&app("aaa")).expect("listed");
        assert_eq!(got.title, "Agent aaa");
        // An unlisted app id resolves to nothing.
        assert!(reg.discover(&app("zzz")).is_none());
        // Publishing changed the registry's committed root (it's a real cell write).
        assert_ne!(reg.root(), empty_root);
    }

    #[test]
    fn discovery_is_content_addressed_and_order_free() {
        let mut a = GrainRegistry::new();
        a.publish(listing("aaa")).unwrap();
        a.publish(listing("bbb")).unwrap();
        let mut b = GrainRegistry::new();
        // Publish in the opposite order → same committed root.
        b.publish(listing("bbb")).unwrap();
        b.publish(listing("aaa")).unwrap();
        assert_eq!(a.root(), b.root());
        assert_eq!(a.list_all().len(), 2);
    }

    #[test]
    fn republishing_the_same_app_id_is_refused() {
        let mut reg = GrainRegistry::new();
        reg.publish(listing("aaa")).unwrap();
        assert!(matches!(
            reg.publish(listing("aaa")),
            Err(RegistryError::AlreadyListed(_))
        ));
    }

    #[test]
    fn rent_prices_a_quote_bounded_by_the_terms() {
        let mut reg = GrainRegistry::new();
        reg.publish(listing("aaa")).unwrap();
        let quote = reg.rent(&app("aaa"), "user:bob", 3).unwrap();
        assert_eq!(quote.periods, 3);
        assert_eq!(quote.total_cost, 50 + 100 * 3);
        // Over the max-periods bound → refused.
        assert!(matches!(
            reg.rent(&app("aaa"), "user:bob", 99),
            Err(RegistryError::ExceedsMaxPeriods { .. })
        ));
        // Renting an unlisted agent → refused.
        assert!(matches!(
            reg.rent(&app("zzz"), "user:bob", 1),
            Err(RegistryError::NotListed(_))
        ));
    }

    #[test]
    fn an_overflowing_quote_is_refused_not_wrapped() {
        let mut reg = GrainRegistry::new();
        let mut l = listing("aaa");
        l.terms = ListingTerms {
            rent_per_period: u64::MAX,
            deposit: 1,
            max_periods: u64::MAX,
        };
        reg.publish(l).unwrap();
        // u64::MAX * 2 (+1 deposit) wraps in u64 — must be a refusal, never a cheap quote.
        assert_eq!(
            reg.rent(&app("aaa"), "user:bob", 2),
            Err(RegistryError::CostOverflow)
        );
        // A non-overflowing ask against the same listing still quotes fine.
        assert!(reg.rent(&app("aaa"), "user:bob", 0).is_ok());
    }

    #[test]
    fn a_review_is_a_receipted_turn() {
        let mut reg = GrainRegistry::new();
        reg.publish(listing("aaa")).unwrap();
        let receipt = reg.review(&app("aaa"), "user:carol", 5, [9u8; 32]).unwrap();
        // The receipt binds who reviewed which listing, and to the new registry root.
        assert_eq!(receipt.op, "review");
        assert_eq!(receipt.actor, "user:carol");
        assert_eq!(receipt.cell_id, "listing/aaa");
        assert_eq!(receipt.data_root.as_deref(), Some(reg.root().0.as_str()));
        // The review landed on the listing cell.
        let l = reg.discover(&app("aaa")).unwrap();
        assert_eq!(l.reviews.len(), 1);
        assert_eq!(l.average_rating(), Some(5.0));
        // A 7-star rating is clamped to 5.
        reg.review(&app("aaa"), "user:dave", 7, [0u8; 32]).unwrap();
        assert_eq!(reg.discover(&app("aaa")).unwrap().reviews[1].rating, 5);
    }
}
