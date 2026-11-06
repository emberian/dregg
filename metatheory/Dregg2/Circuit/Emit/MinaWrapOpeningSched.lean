/-
# `Dregg2.Circuit.Emit.MinaWrapOpeningSched` — ⚑⚑ THE IPA **OPENING** RELATION, IN A CIRCUIT, ON THE
SCHEDULED ROW, **WITH `sg` A PINNED SLOT — NOT A FREE WITNESS AND NOT AN ELIMINATED ONE.**

## ⚑ SAY THE SUBSTRATE OUT LOUD (HOUSE LAW #1, at constraint #1)

**This is Lean-authored AIR.** Every value column is the allocator's
(`AirColumnAlloc.allocate` through `PastaCurveScheduled.valueCol`), the chain register and its
carry are `MinaWrapClosingScheduled`'s, and the only new hand-chosen indices are the block
register and the two published-`sg` blocks, both placed at `CHAIN_W + ·` rather than at literals.
Rust parses the emitted bytes, fills trace cells, proves, folds. It authors nothing.

## WHAT THIS IS, AGAINST ITS TWO NEIGHBOURS

* `MinaWrapOpeningGate` (rung 5f) proves the opening relation **(B)** of Mina devnet block 539508
  — `c·Q + delta − z₁·sg − z₁b₀·U − z₂·H = O`, `wrap_verifier.ml:383/:422`, `ipa.rs:409-425` — in
  the KERNEL, at the value layer. **It is not a circuit.** Nothing a prover produces is refused by
  it.
* `MinaWrapClosingAir` / `MinaWrapClosingScheduled` carry the **combined** check with `sg`
  ELIMINATED (`ρ = −z₁`), at the price of the `⟨s, srs.g⟩` SRS leg — a 2^15-slot manifest.
* **This file is the third object**: statement (B) alone, as an emitted descriptor — a 35-addend
  scheduled chain whose EVERY addend is a descriptor constant, with the `sg` term at slot 0 and
  the affine `sg` itself published at `PI[192..255]`. The SRS leg is NOT here: what ties this
  `sg` to `⟨s, srs.g⟩` is the deferral (`PastaIpaDeferral` §4/§5 — absorb at O(1), discharge in
  batch, the gate REFUSES an undischarged batch), or `MinaWrapClosingScheduled`'s merged check.
  Carrying (B) per block at 35 additions instead of 32,771 is the entire point of deferring (A).

## ⚑⚑ WHY THE `sg` SLOT IS THE CONTENT — the vacuity pair, retired the OTHER way

`MinaWrapVerifierAir.opening_is_vacuous_when_sg_is_free` and
`PastaIpaDeferral.opening_free_sg_is_total` are theorems: (B) with `sg` a free witness refutes
NOTHING — `sg` enters linearly with unit coefficient, so `sg := z₁⁻¹·(c·Q + delta − z₁b₀U − z₂H)`
satisfies the check at every value of everything else. `pinned_sg_makes_the_opening_refute`
(`MinaWrapVerifierAir:769`) is the other pole: at a FIXED `sg₀` the same relation refutes.

`MinaWrapClosingAir` killed the vacuity by making the `sg`-side map CONSTANT (elimination). This
file kills it by making the premise unsatisfiable the other way: **`sg` is not a witness.** The
`−z₁·sg` addend is a descriptor constant forced onto block 0's addend cells by `.first`-row window
gates, and every OTHER addend is likewise forced by its block's phase-0 gate — so the solved-`sg`
forgery family is a trace this descriptor's constraints refuse, and §4 exhibits that at the
block's own numbers: `the_solved_addend_closes_the_forged_chain` (the forgery IS an accepting
group equation) and `the_solved_addend_differs_from_the_pinned_slot` (and the pin is what says
no).

## ⚑ WHICH `sg` THIS BINDS — say it exactly, or say nothing

**Block 539508's own `opening.sg`** (`MinaWrapOpeningGate.SG`), at that block's own transcript
challenges. It is NOT dregg's own step-assembly `sg` (`KimchiStepMainCore`'s segment D), which is
a different object bound — if at all — by the step assembly's own transcript. A consumer that
wants a real `G` for THAT direction reads `PI[192..255]` of a proof of THIS descriptor, which is
a claim about the Mina block, not about dregg's own recursion slot.

## ⚑ THE TRICHOTOMY, SAID PLAINLY (CIRCUIT / EMITTER / NOWHERE)

The SCALING `[k]·P` of each term runs in the EMITTER: `openingAddends` is a literal table whose
derivation from the Gate's own `(scalar, point)` list is `the_manifest_is_the_derivation` — a
kernel `decide` through 34 real 255-bit ladders — and the AIR folds the 35 declared points. The
in-circuit alternative is priced at `PastaMsmLayouts.glvOpeningRcbAdds 34 128 = 8,773` complete
additions (wide row) — ×33 rows here; this descriptor pays **35** additions because the emitter is
trusted for the scaling, exactly `MinaAccumulatorAir` §10's trichotomy, and that trust is the
named residual, not a footnote.

## ⚠ WHAT THIS DOES **NOT** ESTABLISH

1. **P10 is untouched.** A prover who passes (B) KNOWS an opening only by the IPA extraction
   argument (rewinding + DL at Pasta), undischarged here and everywhere in this stack
   (`GOAL-P10-OPENING-SOUNDNESS.md`, `IpaOpeningExtractionFloor`). Building the opening check as
   a circuit changes WHAT IS CHECKED, not what passing it proves.
2. **Statement (A) — `sg = ⟨s, srs.g⟩` — is not here.** Deferred; the deferral gate
   (`PastaIpaDeferral.batchOk`) refuses an undischarged batch, and the merged check is
   `MinaWrapClosingScheduled`. With (A) absent, (B) says: the DECLARED `sg` satisfies the opening
   equation against the declared commitments — with `sg` declared, that refutes (contra the free
   case), but what `sg` COMMITS TO still rests on (A) + P10.
3. **The chain-level forcing walk is the same undone work as the closing chain's**: block 0's
   addend pin and the RCB formula per block are FORCED (§6); "block `b`'s addend is manifest slot
   `b` for every `b`" additionally needs the block register's cross-row indicator — the
   `[i = t mod 33]` induction `MinaWrapClosingScheduled` names, with `BLK` in place of `SEL`. The
   per-leg refinement (`CertifiedRefines`) covers every leg; the behavioural refusals run in
   release (`circuit/tests/mina_wrap_opening_sched_proves.rs`).
4. **Per-block descriptor.** A different block (or dregg's own wrap) is a re-emit of the manifest
   — one AIR shape, per-block preprocessed matrix, the `closing-srs` pattern.

## Axiom hygiene

General theorems `#assert_axioms`-clean; facts about concrete data `native_decide`, pinned
`#assert_compiled` (since 2026-11-06); no `sorry`/`admit`; zero `#guard`s. NEW file, NOT imported
by the `Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapOpeningSched`
-/
import Dregg2.Circuit.Emit.MinaWrapClosingScheduled
import Dregg2.Circuit.Emit.MinaWrapOpeningGateData

namespace Dregg2.Circuit.Emit.MinaWrapOpeningSched

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectLower (P)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TraceFamily WindowExpr mainTableDef)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB CB rangeTidW pLimb limbAt)
open Dregg2.Circuit.Emit.PastaAddSubSound (CBITS)
open Dregg2.Circuit.Emit.PastaCurveScheduled
  (SEL SEL_IDLE SCHED_W valueCol sumLoc valuePoolLegs witnessPoolLegs carryLegs scheduleLegs)
open Dregg2.Circuit.Emit.MinaAccumulatorAir (ACC_IN_PI ACC_OUT_PI ACC_PI_COUNT coordLimb)
open Dregg2.Circuit.Emit.MinaWrapClosingScheduled
  (GO CHAIN_W ACC_XS ACC_YS ACC_ZS chainSelectorLegs chainThreadLegs idleHoldLegs
   schedInPinLegs schedOutPinLegs schedDischargeLegs)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj isInfM)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt smul padd pneg FT_COMM_GOLD)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate
  (SG DELTA SRS_H U_BASE CHAL CHAL_INV C B0 CIP_N Z1 Z2 lrTerms residualTerms)

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! ## §1 — THE TERM LIST, and its identity with the Gate's own.

The opening relation's 34 scaled terms plus `delta` at coefficient 1. All coefficients are
POSITIVE residues mod `qN` (Pallas's scalar order): `[qN − k]·P = −[k]·P` on the curve group, so
no negation helper is needed and every slot is `[k]·P` for a declared `k < qN`. -/

/-- ⚑ **THE `sg` TERM — slot 0 of the manifest.** Coefficient `−z₁`, i.e. `qN − z₁`. -/
def sgTerm : Nat × Pt := ((qN - Z1 % qN) % qN, SG)

/-- The 33 non-`sg` scaled terms: the 30 IPA round terms `c·chal⁻¹·L / c·chal·R`, the aggregate
`c·CC`, the `U` term `(c·cip − z₁·b₀)·U`, and the `H` term `−z₂·H` — the Gate's own coefficient
formulas, verbatim. -/
def nonSgTerms : List (Nat × Pt) :=
  lrTerms C CHAL CHAL_INV
    ++ [ (C % qN, Dregg2.Circuit.Emit.MinaWrapAggregationGate.COMBINED_GOLD)
       , ((C * CIP_N % qN + qN - Z1 * B0 % qN) % qN, U_BASE)
       , ((qN - Z2 % qN) % qN, SRS_H) ]

/-- ⚑⚑ **THE TERMS ARE THE GATE'S OWN LIST** — `MinaWrapOpeningGate.residualTerms` at the block's
own values is exactly this file's `sgTerm :: nonSgTerms` with the `sg` entry moved from position
32 to the front. Not a permutation claim over an opaque multiset: the exact rearrangement, as a
list equation. A drifted coefficient — the classic `c·cip` vs `c·cip − z₁b₀` slip — would red
this line. -/
theorem the_terms_are_the_gates_own :
    residualTerms C Z1 Z2 CHAL CHAL_INV
        Dregg2.Circuit.Emit.MinaWrapAggregationGate.COMBINED_GOLD U_BASE SG
      = nonSgTerms.take 32 ++ [sgTerm] ++ nonSgTerms.drop 32 := by native_decide

/-! ## §2 — ⚑ THE LITERAL MANIFEST, machine-spliced, and its derivation theorem.

The 35 addends are MATERIALIZED (the `MinaFinalizeScalars` slot-table discipline): every `decide`
below walks literals, and the ONE theorem that pays the 34 real 255-bit ladders is
`the_manifest_is_the_derivation`. The literals were generated by
`scripts/gen_opening_manifest.lean` — spliced, never hand-typed (the fabricated-`hiTable`
lesson). -/

/-- Coordinates reduced at the Pallas BASE prime — canonical by construction, so a declared limb
decomposition is meaningful. -/
def redPt (Q : Pt) : Pt := (Q.1 % pN, Q.2.1 % pN, Q.2.2 % pN)

theorem redPt_lt (Q : Pt) : (redPt Q).1 < pN ∧ (redPt Q).2.1 < pN ∧ (redPt Q).2.2 < pN := by
  have hp : 0 < pN := by decide
  exact ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩

/-- ⚑ **THE 35 ADDENDS, MATERIALIZED** — spliced from `scripts/gen_opening_manifest.lean`'s
output; `the_manifest_is_the_derivation` is what makes them the derivation rather than a paste. -/
def openingAddends : List Pt :=
  [ (27376545592014689050677254165371430527403547111662543242644159197374550322512,
     9964605544618640700832409785822194621437981610748057983465090850586153397037,
     2943791575878422240291724323046869105358623457085541154093311693029162459761)
  , (11152122284838990619136013050903274340072869674284709720946710285545854279217,
     19572703121919738829138473371488811992022188913442299597754508808835529783563,
     6377775002507523496120268524194909118085966767643607959355726120353157639531)
  , (1511416545385935614050328383793318765707012319519322588471590077215129921412,
     6586984965074400301833442417445991303267942755714945017853887192244151413647,
     21905812728497012247688481101939653148691829232156716510242247391063303011355)
  , (6807575734648190238732955733499600241084560632382973334108777916908641892154,
     26057534599199926759731803531765633005387039053869327999164663038493740761118,
     23249074428629744416099632120547610130430311802949066844723978004157452772076)
  , (14772053911280744321190166142231791607558235774481467690118710928433518394576,
     25628956045933226239443029989477563973132026300050539603268800000873077101593,
     35521204321085232117294670170776286116232297127142333496534978250338153175)
  , (16525455729417896761044811778382574426909239702918567766044421791222740306615,
     16587620542796641072209824274572290083239703478866290798283950924911323562167,
     7453895609382893571196957542784823107833793057844298252419195731138154236849)
  , (22717382951687688147498192409511803204270449212587848854552363241505444029773,
     24099859374278066887280191266242138420559111727142663306954837147271127457493,
     17365638798359408044130074849512473204973167685613712677454929675838792281577)
  , (18933293372195557294700507489219729072679342415938361115550696990387051369992,
     4832560544263226415240320725911819973380925385702409845990431698618056322650,
     15151638221176134675703852769046756610648246919338389953284546244547843651689)
  , (9902994784931955688655377414477955119704168383457127322394484707601353615340,
     3534715392811460693091443125759497387582443858526549431204916288804923716264,
     2831963739762522873656897604407963324832945507211984436924422290101096959482)
  , (28127179271310739428630997447043435453973724205457161859169238967504714541633,
     3460173022985451352814207008816539358184251301994941604486836138234242029475,
     24548126301134248050744221610524778519748513300469302484426506417914894121517)
  , (18967325314814091714159925485277369251954181298284371642033566462720247253411,
     9335508695798440805395950891512344643438489968598027433406001085998767509790,
     3113555107995559810313628907069731132718137384964548349362121343039853365434)
  , (3432955238197168366843738336307987493209154817566994914439810997691430696890,
     707291429371356089536907037133027420909060606397407717067520949140223370406,
     1426737054077417257443741483594766968118370450824958553182743077018852928456)
  , (4660458058997268132041812756740026800438532704793300513023325938863931728701,
     5432974812189568808259638620728736154035280682703408379718027788864643023085,
     11648954491316107393692202444780036025808048332788862426666521914083324311041)
  , (22957836680050236047157073640843179331427518543379298315307891352319551062407,
     19948414921183230933663258531429319747720448666919543106834333161544916953068,
     27528037446856326183475563393142398145796645081639131391946946838909278709886)
  , (21284980368425764989076155732907533492511085267794500364827405411992844102212,
     26773189067215201904510384365014599710173738210702355307948671067519535899704,
     6870404838692912540083876553471340702342455167082558602982127598346353074338)
  , (5049317004222833149291120465518628174476048205725878801252092338971287635951,
     9316924174126813396971610607370902370245553265504915631198975092929061555190,
     21383970165073027335356400434160073276748448896532555208598681363581052015901)
  , (24551635692100819612086654580908673978175673628444436642039898216446483949268,
     17084642062790825558060159292242952043779084515400283147266412637644626007488,
     16527113984294454822915968156666346315784272715949467591382675346985009964621)
  , (16825097224806865636221743425075369586551881328478401434362715126424686295278,
     5555196843564468118243190238830359611628933140416825113729667351800458763162,
     20379524799131198119193720652723046207521489846796004188360297146080844612190)
  , (13178107598895911152237014771614721372349380572811456816579374872376252393188,
     8824137949324641127847555819582904842686715768232063056841136066537718261748,
     28470742733066201956108676230370941582244219013722186561786483335884029096649)
  , (889210777187571128378764352877539720028438982999224627766671289509125049515,
     11871899846675191058227760482174140545637106750424701094804408988093424211618,
     2504037515296490399342110188824705562691454869070405900917802050939494208512)
  , (26039059529586247789075829578531012787547702908996698982391089338825980823111,
     8224767853925021913505793581854564777583402946398341521099485467797108897223,
     20278580557068903506575460390752323988131140526797970615230066580914841128485)
  , (8417385007938777949124304920579448593248349862888019256789236863614193279181,
     19969152803513133777815948689826135173811893552944978733541090860685066244468,
     8923587007223448720362626892491077407013635699633982862815628035792411617905)
  , (20518953524831489202256710963678625712837240918336808569391113874676939306819,
     18880528822139468053769685324190446626706971845694984558080897459531810694742,
     6094230926278583083893788539815975937716474833589243141491313670305509695896)
  , (21255222431078395559876895659264909600814450525405658879214508693301733052211,
     8840479086671204564120048418180038186746128457232766324926455159307547435225,
     20235609595189741987213308817421493275643086758645480821376141630081558207416)
  , (19662784015358608810701109764380094759372127654506444688281891597480693570761,
     5558637003875525014738282640816340725743759226015522151928864901131995669922,
     26568706952644818352336560703550715930591349801231268785432377870099116875546)
  , (2985352841255324589438863797150742548146736045202937814285748753482915120502,
     18959064732424346478764638286537364354591194014048705181036972407813952332874,
     3278392101742128790978938052627192471212501479939303664819844703168412503782)
  , (3739439533887083783094537730415814794568770583110076966274077315917432825075,
     24018257275486905975952858219736352033584181173455914323539645098582475938346,
     28328954572031745673695022510460932332982789423125703628905653693608868675474)
  , (8661567503093627345154081317665882816731266730719216292501966458905168383994,
     367913803101778559072540591829468375000283346204054128035563896563389948022,
     21540274793730273788816254812049247690050023409983268468085469634428922323579)
  , (11173255420160445844315622002634436524431173080036182651402398127552118165087,
     23791328262678144619257781301498788077361054721215821604976934431911680705657,
     8625847487175789762994266013288105072515018741774405729278223875799887539623)
  , (3784586494923144678848945663638407363434477696466546103292060242916860009944,
     6119788118791830059232365558893842874778553856974291209822684464321836914933,
     11968777400477105515127984619211306201714683383054866289703321348682088983812)
  , (25838915910627154382642776501199143401520912664672765296978918815213529742209,
     8423523230931677923945266268637598395339360034181852924719055045593560073478,
     6045978822167257181720959214744142038677900263115146673430743299955358437443)
  , (8909685636170969262660170931121082980138607033198764076082935034127495559034,
     23826720692398761068444913824541664217679998731614808155154087292223545479532,
     3119191959324686644842504842789331620350206823085741445265480116731427659049)
  , (22521027273230177002754080535503537116730398625682093270463885366483467851560,
     14542261149483327918300756103282185710321506390121423685246053980320682288746,
     6263409992443649016093657811515661719377821985103304785896663321948405013895)
  , (8877736824207948799220655172129732590644262630234487980884650290718578634760,
     23229002636823878706283380062834034323810282977721584713409054852086205780104,
     3801148462218267995734287534605780740434120752150561818377168920516760172274)
  , (12549709920810273664906708092233375320551866741711935112842501996657168435128,
     20309267457022842418190650121197025811257123750798938466729537503415872118371,
     1)
  ]

/-- The number of chain blocks — one per addend. -/
def NBLOCKS : Nat := 35

theorem openingAddends_length : openingAddends.length = NBLOCKS := by native_decide

/-- ⚑⚑⚑ **THE MANIFEST IS THE DERIVATION** — the literal table equals `[k]·P` over the Gate's own
term list (slot 0 the `sg` term), plus `delta` at coefficient 1, every coordinate reduced at
`pN`. This is the one theorem that runs the 34 real ladders in the kernel; everything else in
this file reads the literals. -/
theorem the_manifest_is_the_derivation :
    openingAddends
      = (sgTerm :: nonSgTerms).map (fun t => redPt (smul t.1 t.2)) ++ [redPt DELTA] := by native_decide

/-- ⚑ **SLOT 0 IS THE `sg` TERM** — `[qN − z₁]·SG = −z₁·SG`, reduced. The un-eliminated relation's
fourth non-SRS addend, PRESENT and DECLARED, where `MinaWrapClosingAir`'s manifest proved it
ABSENT (`the_closing_manifest_carries_no_sg_slot`). The two files are the two ways to retire the
vacuity, and each states its slot inventory. -/
theorem the_opening_manifest_carries_the_sg_slot_at_zero :
    openingAddends.getD 0 Oproj = redPt (smul ((qN - Z1 % qN) % qN) SG) := by native_decide

/-- …and slot 34 is `delta`, the only coefficient-1 term. -/
theorem the_opening_manifest_ends_with_delta :
    openingAddends.getD 34 Oproj = redPt DELTA := by native_decide

/-! ## §3 — ⚑⚑ THE CHAIN CLOSES AT THE BLOCK'S OWN VALUES — and at no proper prefix. -/

/-- The fold the trace performs: complete additions from the projective identity, in slot order. -/
def chainFold (As : List Pt) : Pt := As.foldl padd Oproj

/-- ⚑⚑ **SATISFIABILITY, AT THE REAL BLOCK**: the 35-addend chain folds from `O` to the point at
infinity — `isInfM` is `X ≡ 0 ∧ Z ≡ 0`, exactly the shape the 64 `.last` discharge gates force.
This is `MinaWrapOpeningGate.opening_relation_holds`' physical statement, recomputed through THIS
file's own fold order and literal manifest — two independent computations, one vanishing. -/
theorem the_opening_chain_closes : isInfM pN (chainFold openingAddends) = true := by native_decide

/-- ⚑ **AND AT NO PROPER NON-EMPTY PREFIX.** The `.last` `BLK 34` gate forces a full 35-block run;
this is the algebraic half of that tooth: no early `GO`-drop lands on an accepting terminal, so
"the chain closed" cannot be a statement about a prefix. -/
theorem the_chain_has_no_accepting_proper_prefix :
    ((List.range 34).all
      (fun k => !(isInfM pN (chainFold (openingAddends.take (k + 1)))))) = true := by native_decide

/-! ## §4 — ⚑⚑ THE FORGERY, AT THE BLOCK'S OWN NUMBERS: it closes the equation, and the pin is
what says no.

The vacuity's own move (`opening_free_sg_is_total`): move the aggregate, re-solve the `sg` slot.
Here the aggregate slot is re-scaled onto `FT_COMM_GOLD` — a REAL Pallas point of the same block,
the Gate's own `tamper_aggregate` replacement — and the `sg`-slot addend is SOLVED as the negation
of everything else. The chain VANISHES: as a group equation the forgery is perfect. What refuses
it is that slot 0 is a descriptor constant. -/

/-- The forged aggregate addend: `[c]·ft_comm` in place of `[c]·CC`. -/
def ccForged : Pt := redPt (smul (C % qN) FT_COMM_GOLD)

/-- The non-`sg` tail with the aggregate slot forged (global slot 31 = tail index 30). -/
def forgedTail : List Pt := (openingAddends.drop 1).set 30 ccForged

/-- ⚑ **THE SOLVED SLOT** — `−Σ(everything else)`, the vacuity's witness made concrete. -/
def solvedAddend : Pt := redPt (pneg (chainFold forgedTail))

/-- ⚑⚑ **THE FORGED CHAIN CLOSES.** The forgery is not refused by the group equation — that is
the whole content of the vacuity theorems, exhibited at the real block. -/
theorem the_solved_addend_closes_the_forged_chain :
    isInfM pN (chainFold (solvedAddend :: forgedTail)) = true := by native_decide

/-- ⚑⚑ **AND IT IS NOT THE PINNED SLOT** — the solved addend differs from manifest slot 0 in at
least one 8-bit limb, so at least one of the 96 block-0 phase-0 window gates evaluates non-zero
on the forged trace. `the_addend_pin_refuses_a_moved_limb` below is that gate body's refusal,
with no hypotheses beyond the move itself. -/
theorem the_solved_addend_differs_from_the_pinned_slot :
    (solvedAddend != openingAddends.getD 0 Oproj
      && (List.range (3 * SK)).any
           (fun j => coordLimb solvedAddend j != coordLimb (openingAddends.getD 0 Oproj) j))
      = true := by native_decide

/-- ⚑ **THE OTHER POLE: a moved aggregate WITHOUT the solve is refused by the chain itself** —
the terminal is not the identity, so the discharge gates refuse before any pin is consulted. The
falsifier pair brackets the check: solve-and-move hits the pin, move-alone hits the discharge. -/
theorem a_moved_aggregate_alone_is_refused_by_the_chain :
    isInfM pN (chainFold (openingAddends.set 31 ccForged)) = false := by native_decide

/-! ## §5 — THE LEGS: the block register, the manifest pins, the `O` seed, and the published `sg`.

Base substrate: `MinaWrapClosingScheduled`'s chained scheduled row, verbatim — the cyclic
selector, the pools, the carries, the op gates, the phase-gated thread, the idle holds, the
endpoint pins and the discharge. Everything below APPENDS. -/

/-- The block-indicator column for block `b` — a 35-wide one-hot register past the chain flag. -/
def BLK (b : Nat) : Nat := CHAIN_W + b

/-- The published `sg`'s affine X limbs, one column each. -/
def SGX (j : Nat) : Nat := CHAIN_W + NBLOCKS + j
/-- …and Y. -/
def SGY (j : Nat) : Nat := CHAIN_W + NBLOCKS + SK + j

/-- ⚑ **THE OPENING ROW'S DECLARED WIDTH**: the chained scheduled row, 35 block indicators, and
the 64 published-`sg` columns. -/
def OPEN_W : Nat := CHAIN_W + NBLOCKS + 2 * SK

/-- PI: the accumulator endpoints (the fold interface, unchanged), then `sg.x`, then `sg.y`. -/
def OPEN_PI : Nat := ACC_PI_COUNT + 2 * SK

theorem open_w_eq : OPEN_W = 581 ∧ CHAIN_W = 482 ∧ OPEN_PI = 256 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- Booleanity of each block indicator, on every row. -/
def blockBooleanLegs : List AirLeg :=
  (List.range NBLOCKS).map (fun b =>
    .window ⟨.all, .mul (.loc (BLK b)) (.add (.loc (BLK b)) (.const (-1)))⟩)

/-- Exactly one block indicator is live on every row — including the idle tail, which parks at
`BLK 34`. -/
def blockOneHotLeg : AirLeg :=
  .window ⟨.all, .add (sumLoc ((List.range NBLOCKS).map BLK)) (.const (-1))⟩

/-- Row 0 is block 0. -/
def blockFirstLeg : AirLeg :=
  .window ⟨.first, .add (.loc (BLK 0)) (.const (-1))⟩

/-- ⚑⚑ **THE LAST ROW IS BLOCK 34** — the tooth that forces the WHOLE chain to have run. Without
it a prover drops `GO` after a prefix whose partial sum happened to vanish; §3's
`the_chain_has_no_accepting_proper_prefix` says no such prefix exists for THIS manifest, and this
leg refuses the shape structurally rather than numerically. -/
def blockLastLeg : AirLeg :=
  .window ⟨.last, .add (.loc (BLK (NBLOCKS - 1))) (.const (-1))⟩

/-- The shift condition: a block boundary is a phase-32 row with the chain continuing. Degree 2;
every use below stays inside the main-rail budget of 3. -/
private def shiftMask : WindowExpr := .mul (.loc (SEL 32)) (.loc GO)

/-- `nxt(B₀) = B₀·(1 − S)` — block 0 never returns. -/
def blockShiftLeg0 : AirLeg :=
  .window ⟨.transition,
    .add (.nxt (BLK 0))
      (.add (.mul (.const (-1)) (.loc (BLK 0)))
            (.mul (.loc (BLK 0)) shiftMask))⟩

/-- `nxt(B_{b+1}) = B_{b+1}·(1 − S) + B_b·S` — the indicator advances exactly at a live block
boundary. At `b + 1 = 34` with `GO` still up, the register would have to leave `B₃₄` with no
successor and the one-hot refuses — which is what FORCES `GO` down at the final boundary. -/
def blockShiftLeg (b : Nat) : AirLeg :=
  .window ⟨.transition,
    .add (.nxt (BLK (b + 1)))
      (.add (.mul (.const (-1)) (.loc (BLK (b + 1))))
        (.add (.mul (.loc (BLK (b + 1))) shiftMask)
              (.mul (.const (-1)) (.mul (.loc (BLK b)) shiftMask))))⟩

/-- The block register: 35 booleanity, the one-hot, the two boundary rows, and the 35 shift legs. -/
def blockRegisterLegs : List AirLeg :=
  blockBooleanLegs ++ [blockOneHotLeg, blockFirstLeg, blockLastLeg]
    ++ (blockShiftLeg0 :: (List.range (NBLOCKS - 1)).map blockShiftLeg)

theorem blockRegisterLegs_length : blockRegisterLegs.length = 73 := by native_decide

/-- The addend's X block — input value 3, at the allocator's column. ⚠ The same physical column
as `OUT_XS` (slot 8 reuse); `MinaWrapClosingScheduled.no_slot_carries_across_the_block_boundary`
is what makes that legal. -/
def ADD_XS : Nat := valueCol 3
def ADD_YS : Nat := valueCol 4
def ADD_ZS : Nat := valueCol 5

/-- The aliasing, pinned rather than trusted: the addend's X input block and the block OUTPUT's X
share physical column 290 (slot-8 reuse) — the seam
`MinaWrapClosingScheduled.no_slot_carries_across_the_block_boundary` makes legal. -/
theorem the_addend_x_shares_the_out_slot :
    ADD_XS = Dregg2.Circuit.Emit.MinaWrapClosingScheduled.OUT_XS ∧ ADD_XS = 290 := by
  refine ⟨by native_decide, by native_decide⟩

/-- The `j`-th addend limb column, `j < 3·SK` walking X ‖ Y ‖ Z. -/
def addCol (j : Nat) : Nat :=
  if j < SK then ADD_XS + j
  else if j < 2 * SK then ADD_YS + (j - SK)
  else ADD_ZS + (j - 2 * SK)

/-- ⚑⚑⚑ **ONE MANIFEST PIN**: on block `b`'s phase-0 row — the row where the allocator has the
addend's three input blocks live (`defTime = 0`, held to their last use by the carry legs) — the
`j`-th addend limb equals manifest slot `b`'s. `B_b · SEL₀ · (cell − k)`: degree 3, the budget
exactly. `.all`, so it fires wherever the two indicators do and sleeps elsewhere. -/
def addendPinLeg (b j : Nat) : AirLeg :=
  .window ⟨.all,
    .mul (.loc (BLK b))
      (.mul (.loc (SEL 0))
        (.add (.loc (addCol j))
              (.const (-(coordLimb (openingAddends.getD b Oproj) j : ℤ)))))⟩

/-- ⚑⚑ **THE 3,360 MANIFEST PINS** — 35 blocks × 96 limbs. THE difference from the `-final`-pole
descriptors: the trace supplies no addend at all. -/
def addendPinLegs : List AirLeg :=
  (List.range NBLOCKS).flatMap (fun b =>
    (List.range (3 * SK)).map (fun j => addendPinLeg b j))

theorem addendPinLegs_length : addendPinLegs.length = 3360 := by native_decide

/-- The accumulator's `j`-th limb column at row 0, `j < 3·SK` walking X ‖ Y ‖ Z. -/
def accCol (j : Nat) : Nat :=
  if j < SK then ACC_XS + j
  else if j < 2 * SK then ACC_YS + (j - SK)
  else ACC_ZS + (j - 2 * SK)

/-- ⚑ **THE CHAIN SEEDS AT `O`** — 96 `.first` gates forcing the entering accumulator to the
projective identity `(0, 1, 0)`. Without these, `acc_in` is merely published and a forger seeds
at `−Σ(addends) + O'` to land any non-vanishing manifest on an accepting terminal. With them,
"the chain closes" IS "the declared sum vanishes". -/
def accInZeroLeg (j : Nat) : AirLeg :=
  .window ⟨.first, .add (.loc (accCol j)) (.const (-(coordLimb Oproj j : ℤ)))⟩

def accInZeroLegs : List AirLeg := (List.range (3 * SK)).map accInZeroLeg

/-- ⚑ **THE PUBLISHED `sg`, FORCED**: 64 `.first` gates pinning the `SGX`/`SGY` columns to block
539508's affine `opening.sg` — descriptor constants, so the publication cannot drift from the
manifest that scales `−z₁·SG` into slot 0 (`the_published_sg_is_the_scaled_slots_preimage`). -/
def sgxyConstLegs : List AirLeg :=
  (List.range SK).map (fun j =>
      AirLeg.window ⟨.first, .add (.loc (SGX j)) (.const (-(limbAt SG.1 j)))⟩)
    ++ (List.range SK).map (fun j =>
      AirLeg.window ⟨.first, .add (.loc (SGY j)) (.const (-(limbAt SG.2.1 j)))⟩)

/-- …and PUBLISHED at `PI[192..255]`, the carried claim a consumer welds against. -/
def sgxyPinLegs : List AirLeg :=
  (List.range SK).map (fun j => AirLeg.pin ⟨.first, SGX j, ACC_PI_COUNT + j⟩)
    ++ (List.range SK).map (fun j => AirLeg.pin ⟨.first, SGY j, ACC_PI_COUNT + SK + j⟩)

/-- ⚑ The publication and the slot are ONE object: slot 0 is `[qN − z₁]` times the published
point, by the manifest's own derivation. An emitter cannot publish one `sg` and fold another. -/
theorem the_published_sg_is_the_scaled_slots_preimage :
    openingAddends.getD 0 Oproj = redPt (smul ((qN - Z1 % qN) % qN) (SG.1, SG.2.1, SG.2.2))
      ∧ SG.2.2 = 1 := by
  refine ⟨?_, by decide⟩
  · exact the_opening_manifest_carries_the_sg_slot_at_zero

/-! ## §6 — THE AIR, THE DESCRIPTOR, THE MEASUREMENT. -/

/-- The same three range pools, at the opening width. No fourth width invented. -/
def openTables : List TableDef :=
  [ mainTableDef OPEN_W
  , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
  , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
  , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]

/-- ⚑⚑ **THE OPENING DESCRIPTOR'S AIR** — the chained scheduled row plus the block register, the
3,360 manifest pins, the `O` seed, and the published `sg`. -/
def openingSchedAir : EffectAir :=
  { tables := openTables
  , legs := chainSelectorLegs
      ++ valuePoolLegs ++ witnessPoolLegs ++ carryLegs ++ scheduleLegs pLimb
      ++ chainThreadLegs ++ idleHoldLegs ++ schedInPinLegs ++ schedOutPinLegs
      ++ schedDischargeLegs
      ++ blockRegisterLegs ++ addendPinLegs ++ accInZeroLegs
      ++ sgxyConstLegs ++ sgxyPinLegs }

set_option maxHeartbeats 400000000 in
/-- ⚑ **THE COMPILER ACCEPTS THE BLOCK** — the new families are `.all`/`.first`/`.last`/
`.transition` windows reading no `nxt` except the register's own, and the pins are boundary pins.
A selector slip in any family lowers to `refuseConstraints` and this goes red. -/
theorem openingSchedAir_mainRailOk : openingSchedAir.mainRailOk = true := by native_decide

set_option maxHeartbeats 400000000 in
/-- ⚑ **NO PIN IS DECORATIVE** — the endpoint pins' columns are read by the carry/thread/
discharge families, and the `SGX`/`SGY` pins' columns by their own `.first` forcing gates. -/
theorem openingSchedAir_pinsTied : openingSchedAir.pinsTied = true := by native_decide

set_option maxHeartbeats 400000000 in
/-- Every column the constraints address is inside the declared width — `SGY 31 = OPEN_W − 1` is
the widest. -/
theorem openingSched_columns_fit :
    (openingSchedAir.legs.all (fun l => l.readCols.all (fun c => c < OPEN_W))) = true := by
  native_decide

/-- ⚑ **THE TIE, SUPPLIED FROM THE TWO NAMED THEOREMS — NOT RE-DERIVED.** `TiedAir.ok` and
`.tied` are autoParams defaulting to `by decide`; left to fire, they re-run the two 6 404-constraint
verdicts that `openingSchedAir_mainRailOk` and `openingSchedAir_pinsTied` just proved, in the
ELABORATOR's `whnf` rather than the kernel's fast path. Measured 2026-08-09: a build sampled inside
that autoParam (`elabMutualDef → synthesizeSyntheticMVars → runTactic → whnf/reduceRec`) and was
OOM-killed (exit 137) at 15 674 s. Passing the proved terms is the same two facts, same `TiedAir`,
same `CertifiedRefines` — with the work done once instead of twice. -/
def openingSchedTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := openingSchedAir
  ok := openingSchedAir_mainRailOk
  tied := openingSchedAir_pinsTied

/-- ⚑⚑ **THE EMITTED DESCRIPTOR.** -/
def openingSchedDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-opening-sched::v1" OPEN_W OPEN_PI [] openingSchedTiedAir).val

/-- ⚑ **THE CERTIFICATE, PRODUCED BY THE EMIT** — every leg of this source is forced by the
emitted constraints, per-leg, in the source's own `AirLeg.forces` vocabulary. Its two instance
verdicts (`mainRailOk`, `pinsTied` over the 6 404-constraint block) are compiled evaluation since
2026-11-06, so it is pinned `#assert_compiled`; the refinement itself is the general kernel theorem. -/
theorem openingSchedDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines openingSchedDesc [] openingSchedAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-opening-sched::v1" OPEN_W OPEN_PI [] openingSchedTiedAir).property

theorem openingSchedDesc_width : openingSchedDesc.traceWidth = 581 := rfl
theorem openingSchedDesc_piCount : openingSchedDesc.piCount = 256 := rfl

set_option maxHeartbeats 400000000 in
/-- ⚑⚑ **THE COMMITTED WIDTH — 1,599**: the chained row's 1,500 plus the 99 new declared columns;
the new families declare NO range lookup, so the aux block does not move. -/
theorem openingSchedDesc_committed :
    Dregg2.Circuit.Emit.AirColumnAlloc.committedWidth OPEN_W openingSchedAir = 1599 := by native_decide

set_option maxHeartbeats 400000000 in
theorem openingSchedDesc_constraint_count :
    openingSchedDesc.constraints.length = 6404 := by native_decide

/-- The census, so a dropped family moves a number: the chained closing row's
`34+1+1+36+352+95+352+1428+96+96+192+64 = 2747`, PLUS the block register's 73, the 3,360 manifest
pins, the 96 `O`-seed gates, the 64 `sg` forcing gates and the 64 `sg` pins.

⚑ Derived from `openingSchedDesc_constraint_count` rather than re-evaluating
`openingSchedDesc.constraints` a second time — the two were never independent (the same closed term,
walked twice), and the census still moves when a family is dropped, because the pinned `6404` reds
first. -/
theorem the_opening_census :
    2747 + 73 + 3360 + 96 + 64 + 64 = openingSchedDesc.constraints.length :=
  openingSchedDesc_constraint_count.symm

set_option maxHeartbeats 400000000 in
/-- ⚑ The selector census. The 3,360 manifest pins and the register's booleanity/one-hot are
`.all`; the shift legs are `.transition`; the seeds/`sg` gates are `.first`; `BLK 34`'s tooth and
the discharge are `.last`. -/
theorem the_opening_selector_census :
    openingSchedAir.windowCountSel RowSel.transition = 613
    ∧ openingSchedAir.windowCountSel RowSel.last = 66
    ∧ openingSchedAir.windowCountSel RowSel.first = 162
    ∧ openingSchedAir.windowCountSel RowSel.all = 3432 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **A NAME IS A KEY** — this cone's descriptors must not resolve to one another. -/
theorem the_opening_descriptor_name_is_new :
    openingSchedDesc.name ≠ Dregg2.Circuit.Emit.MinaWrapClosingScheduled.closingSchedFinalDesc.name
    ∧ openingSchedDesc.name ≠ Dregg2.Circuit.Emit.MinaWrapClosingScheduled.closingSchedSegDesc.name := by
  refine ⟨by native_decide, by native_decide⟩

/-! ### §6b — the price, re-derived for THIS shape, both halves.

35 complete additions: 1,155 live rows, padding to `2^11`. Committed cells `2^11 · 1,599 ≈
3.27 · 10⁶` — against the same 35 additions on the deployed wide row at `35 · 10,756 ≈ 3.8 · 10⁵`
committed cells: ⚑ **the leaf prover pays ~8.7× more here** (the 4.60×-per-addition figure of
`MinaWrapClosingScheduled` §4b plus this instance's padding slack — 1,155 of 2,048 rows are
live), bought against the wrap's 7.17× narrower per-query column work. And the EMITTER-side
scaling is what keeps it 35 additions at all: in-circuit scaling is `glvOpeningRcbAdds 34 128 =
8,773` additions (`PastaMsmLayouts` §6a), 251× the chain length, and moving it in-AIR on this
substrate is `8,773 × 33` rows — genuinely new work, priced and not taken. -/

theorem the_opening_shape :
    NBLOCKS * 33 = 1155 ∧ 1155 ≤ 2 ^ 11 ∧ 2 ^ 10 < 1155 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

theorem the_leaf_cells_both_halves :
    2 ^ 11 * 1599 = 3274752
    ∧ 35 * 10756 = 376460
    ∧ 8 * 376460 < 3274752 ∧ 3274752 < 9 * 376460 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-! ## §7 — FORCING: what the emitted constraints buy, and exactly where it stops.

Per-leg: `openingSchedDesc_certified` (every leg forced, `CertifiedRefines`). Composed, per
block: the chained row's own `oneBlockRows_force_the_rcb_formula` applies unchanged to this AIR's
leg list (the base families are literally `MinaWrapClosingScheduled`'s — §7a re-proves the three
membership lemmas against THIS list). New here: the row-0 facts — the seed, the block-0 addend
pin, and the published `sg` (§7b).

⚠ **The chain-level walk is the SAME undone work as the closing chain's**, plus one more
induction of the same shape for `BLK`: `PhaseIndicator` at `[i = t mod 33]` under `GO`, and the
block indicator at `[b = t / 33]`. Until those land, "block `b`'s addend is manifest slot `b`"
for `b > 0` is per-leg-forced but not composed, and the behavioural refusals in
`circuit/tests/mina_wrap_opening_sched_proves.rs` are the running evidence. Quote it that way. -/

section Forcing

open Dregg2.Circuit.Emit.AirCrossRow (RowTrace rowEnv PhaseIndicator PoolsRanged SlotsCarry gather
  slotsCarry_of_carryLegs scheduledRows_force_the_rcb_formula)
open Dregg2.Circuit.Emit.AirSelectorForcing (LegsHold rowsSat_of_scheduleLegs)
open Dregg2.Circuit.Emit.PastaFieldSound (sVal)
open Dregg2.Circuit.Emit.PastaCurveSound (IN_BASE vBase)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 rcbTraceZ)
open Dregg2.Circuit.Emit.PastaCurve (CZp)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

variable {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}

theorem chainSelectorLegs_sub : ∀ l ∈ chainSelectorLegs, l ∈ openingSchedAir.legs := by
  intro l hl
  simp only [openingSchedAir, List.mem_append] at *
  tauto

theorem carryLegs_sub : ∀ l ∈ carryLegs, l ∈ openingSchedAir.legs := by
  intro l hl
  simp only [openingSchedAir, List.mem_append] at *
  tauto

theorem scheduleLegs_sub : ∀ l ∈ scheduleLegs pLimb, l ∈ openingSchedAir.legs := by
  intro l hl
  simp only [openingSchedAir, List.mem_append] at *
  tauto

/-- ⚑⚑ **THE FIRST BLOCK'S 33 ROWS FORCE THE RCB FORMULA** — the closing chain's composition,
re-based to this AIR's leg list. Same premises, same conclusion, same first-block scope. -/
theorem openingOneBlockRows_force_the_rcb_formula
    (h : LegsHold tr tf pub chal openingSchedAir.legs) (hr : PoolsRanged tr) :
    CZp (sVal (gather tr) (vBase IN_BASE 26))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).X3g
    ∧ CZp (sVal (gather tr) (vBase IN_BASE 29))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Y3f
    ∧ CZp (sVal (gather tr) (vBase IN_BASE 32))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Z3c := by
  have hp : PhaseIndicator tr :=
    Dregg2.Circuit.Emit.MinaWrapClosingScheduled.chain_phaseIndicator
      (h.mono chainSelectorLegs_sub)
  have hc : SlotsCarry tr :=
    slotsCarry_of_carryLegs tr tf pub chal hp
      (fun t ht l hl => h t ht l (carryLegs_sub l hl))
  exact scheduledRows_force_the_rcb_formula tr hc hr
    (rowsSat_of_scheduleLegs hp (h.mono scheduleLegs_sub))

/-! ### §7b — the row-0 refusal and admission, at the gate-body level. -/

/-- ⚑ **THE MANIFEST PIN REFUSES A MOVED LIMB** — on any row where the block and phase indicators
are live, an addend limb that is not the manifest's makes the gate body non-zero. No hypotheses
beyond the three cell reads. -/
theorem the_addend_pin_refuses_a_moved_limb (b j : Nat) (env : VmRowEnv)
    (hB : env.loc (BLK b) = 1) (hS : env.loc (SEL 0) = 1)
    (h : env.loc (addCol j) ≠ (coordLimb (openingAddends.getD b Oproj) j : ℤ)) :
    (WindowExpr.mul (.loc (BLK b))
      (.mul (.loc (SEL 0))
        (.add (.loc (addCol j))
              (.const (-(coordLimb (openingAddends.getD b Oproj) j : ℤ)))))).eval env ≠ 0 := by
  intro hz
  apply h
  simp only [WindowExpr.eval, hB, hS, one_mul] at hz
  linarith

/-- …and ADMITS the manifest's own limb, so the pin family is not refusing everything. -/
theorem the_addend_pin_admits_the_manifest (b j : Nat) (env : VmRowEnv)
    (h : env.loc (addCol j) = (coordLimb (openingAddends.getD b Oproj) j : ℤ)) :
    (WindowExpr.mul (.loc (BLK b))
      (.mul (.loc (SEL 0))
        (.add (.loc (addCol j))
              (.const (-(coordLimb (openingAddends.getD b Oproj) j : ℤ)))))).eval env = 0 := by
  simp only [WindowExpr.eval, h]
  ring

end Forcing

#assert_compiled the_terms_are_the_gates_own
#assert_axioms redPt_lt
#assert_compiled openingAddends_length
#assert_compiled the_manifest_is_the_derivation
#assert_compiled the_opening_manifest_carries_the_sg_slot_at_zero
#assert_compiled the_opening_manifest_ends_with_delta
#assert_compiled the_opening_chain_closes
#assert_compiled the_chain_has_no_accepting_proper_prefix
#assert_compiled the_solved_addend_closes_the_forged_chain
#assert_compiled the_solved_addend_differs_from_the_pinned_slot
#assert_compiled a_moved_aggregate_alone_is_refused_by_the_chain
#assert_compiled open_w_eq
#assert_compiled the_addend_x_shares_the_out_slot
#assert_compiled blockRegisterLegs_length
#assert_compiled addendPinLegs_length
#assert_compiled the_published_sg_is_the_scaled_slots_preimage
#assert_compiled openingSchedAir_mainRailOk
#assert_compiled openingSchedAir_pinsTied
#assert_compiled openingSched_columns_fit
#assert_compiled openingSchedDesc_certified
#assert_compiled openingSchedDesc_width
#assert_compiled openingSchedDesc_piCount
#assert_compiled openingSchedDesc_committed
#assert_compiled openingSchedDesc_constraint_count
#assert_compiled the_opening_census
#assert_compiled the_opening_selector_census
#assert_compiled the_opening_descriptor_name_is_new
#assert_compiled the_opening_shape
#assert_compiled the_leaf_cells_both_halves
#assert_axioms chainSelectorLegs_sub
#assert_axioms carryLegs_sub
#assert_axioms scheduleLegs_sub
#assert_axioms openingOneBlockRows_force_the_rcb_formula
#assert_axioms the_addend_pin_refuses_a_moved_limb
#assert_axioms the_addend_pin_admits_the_manifest

end Dregg2.Circuit.Emit.MinaWrapOpeningSched
