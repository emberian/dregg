/-
# `Dregg2.Circuit.Emit.MinaWrapVkDigestChain` — **whose verifier index**: the one tape element that
was derived from nothing, derived from the sha256-pinned Wrap VK by 28 more links of the descriptor
that already carries the other 53.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR, and it authors NO NEW AIR.** `vkChainDesc` is
`MinaPhase1Chain.chainDesc` — *the same object*, `dregg-pasta-fp-chainlink::v1`, 2 048 instructions,
469 columns, eight pin blocks, 256 public inputs (`the_descriptor_is_the_deployed_phase1_link`, by
`rfl`). This file adds 28 WITNESSES to a deployed descriptor. Rust parses it, fills trace cells,
runs the deployed prover and compares slices. House Law #1.

## ⚑⚑ THE HOLE THIS CLOSES, NAMED WITH ITS NUMBER BY THE LANE THAT LEFT IT

`MinaPhase1TapeBinding` §8 residual 1:

> *"THE VERIFIER-INDEX DIGEST IS STILL AN INPUT — 1 tape element, 254 bits, and the number that
> closes it is 28. … It appears in the tree as a bare constant in TWO places and is recomputed from
> nothing… Until then a wrong VK digest produces a complete, self-consistent, entirely wrong
> challenge vector, and nothing downstream can tell: it is the largest trusted object under this
> story."*

It is no longer recomputed from nothing. `the_vk_chain_derives_the_verifier_index_digest` computes
it, and `the_vk_wire_blocks_are_equal` welds the answer to the phase-1 tape's head at full limb
width.

## ⚑ PROVENANCE — GENERATED, NOT TRANSCRIBED

`VK_COMM_XY` and `TXN_VK_COMM_XY` are **written by
`metatheory/fixtures/gen_wrap_vk_comm_xy.py`** off
`bridge/mina-zkapp/fixtures/mina-devnet-wrap-{blockchain,transaction}-vk.json`, whose sha256 is
pinned in `bridge/mina-zkapp/scripts/mina-canonical-circuit-oracle.mjs:189-191` and re-checked by the
generator before it decodes a byte. ⚠ **No human typed these 112 decimals**, and
`gen_wrap_vk_comm_xy.py --check` refuses if the committed literals drift from the fixture. The
harness (`circuit/tests/mina_wrap_vk_digest_chain_proves.rs` §1) closes the loop from the other side:
it decodes the SAME fixture by an INDEPENDENT route — `x` straight from the 32 little-endian bytes,
`y` pinned by `y² = x³ + 5` plus the sign flag, **no square root anywhere** — and diffs it against
the EMITTED WIRE, 56/56 slots, elementwise at full limb width. Two decoders and the emitter in
between; the Lean literals are checked by neither of their own authors.

⚠ **THE SIGN FLAG IS NOT A PARITY BIT, AND THAT IS CHECKED RATHER THAN ASSUMED.** Each commitment is
33 bytes: `x` little-endian, then a flag byte whose bit 7 is arkworks' `SWFlags::PositiveY`, set iff
`y > p − y`. Reading it as "y is odd" or "y is even" yields 28 points that are ALL on the curve and a
sponge run that is entirely self-consistent — and a digest that is wrong. The generator prints all
three; only `greater` reproduces `MinaRealBlockTranscript.VKDIGEST`. An on-curve check could not have
told the three apart, which is this cone's whole lesson arriving one layer lower down.

## THE 28, AND WHY IT IS DERIVED RATHER THAN COUNTED

`VerifierIndex::digest::<EFqSponge>()` (kimchi `verifier_index.rs:399-524`, tag `0.3.0`) opens a
FRESH `EFqSponge`, `absorb_commitment`s `sigma_comm[0..7]`, `coefficients_comm[0..15]`,
`generic_comm`, `psm_comm`, `complete_add_comm`, `mul_comm`, `emul_comm`, `endomul_scalar_comm` —
every optional gate commitment and the whole lookup index are `None` on both devnet Wrap indices, so
they absorb nothing — and returns `digest_fq()`. `absorb_commitment` is `sponge.absorb_g(&chunks)`
and `absorb_g` pushes `x` then `y` as WHOLE base-field elements, so the stream is **56 `Fp` elements,
not one bit packed**, and 56 is EVEN: there is no padding slot here, unlike the phase-1 tape's 37.

`the_twenty_eight_links_are_the_index_digests_own_schedule` is
`MinaPhase1Chain.the_pairs_are_the_absorb_schedule` instantiated at `fpParams` on this stream — the
same theorem, general over every `Params` and every segment, that makes phase 1's 27 a derived
number. `the_vk_chain_is_the_prefix_fold` then says the recursion this file runs IS that fold, so
"28 links" is the rate-2 sponge's own schedule and not a count.

⚑ **AND THE DIGEST IS LANE 0, NOT LANE 1.** `digest_fq` squeezes from ABSORB mode, so it permutes
and reads lane 0 — where `fq_digest` was lane 1 of an already-squeezed state. The last link's
OUTGOING LANE 0 is the answer, PI slots `[3·SK, 4·SK)`.

## ⚠⚠ WHAT THIS DERIVATION IS STRUCTURALLY INCAPABLE OF NOTICING — WRITTEN DOWN FIRST

Two things, and both are theorems in §7 rather than paragraphs.

1. **`the_index_digest_cannot_see_the_circuit_shape`.** kimchi's `digest()` destructures the whole
   `VerifierIndex` and binds `domain`, `max_poly_size`, `zk_rows`, `srs`, `public`,
   `prev_challenges`, `shift`, `w`, `endo`, `linearization` and `powers_of_alpha` to `_`. **The
   digest is a function of the 28 commitments ALONE.** Two verifier indices that agree on every
   commitment and disagree on how many public inputs the circuit takes have the SAME digest, and this
   file exhibits the pair. That is upstream's design, not a defect here — but the phase-1 transcript
   absorbs this digest as its *identity* for the verifier index, and it is not one.
2. **`the_derivation_cannot_see_which_verifier_index_this_is`.** The devnet **transaction** Wrap VK
   is 28 Pallas points too, 28/28 on the curve, sharing NOT ONE commitment with the blockchain VK —
   and the same 28 links over it produce a chain that is internally perfect and derives *its* digest.
   The machinery is verifier-index-agnostic. What selects the blockchain index is the **sha256 pin on
   a JSON file**, which is a fact about a build tree and not an in-circuit one. This is the exact
   shape of `the_on_curve_check_cannot_see_provenance` one layer up: a check that answers *"is this a
   digest of a verifier index"* and cannot answer *"is this THIS block's verifier index"*.

⚑ So what moved is real and bounded: **the trusted object went from one opaque 254-bit constant that
nothing could check to 56 coordinates a byte-pinned fixture determines.** Say that, not more.

## WHAT IS AND IS NOT ESTABLISHED

  * **Kernel-clean and general in the link:** `the_vk_chain_step_is_the_kimchi_permutation` (every
    `j`, no hypotheses — an instance of `MinaWrapVerifierSpongeFp.the_absorb_program_permutes_gen`),
    `the_vk_wire_lane0`/`the_vk_wire_lane1` (`rfl`), `the_vk_emitted_claims_are_continuous`, the
    prefix-fold bridge, and the schedule instance.
  * **Kernel, this index:** the 28-point census, the on-curve leg, the two blind-spot theorems'
    kernel halves, and the forgery's on-curve-and-wrongness.
  * **Compiler-trusted, said out loud:** every 28-permutation evaluation — the digest itself, the
    forgery poles, the transaction index's digest.
  * **NOT established:** that the pinned fixture is the verifier index Mina's own devnet uses. That
    is a sha256 against a byte copy of openmina's `devnet_blockchain_verifier_index.json`, checked by
    `mina-canonical-circuit-oracle.mjs`, and it is a build-tree fact.

Import line for the CI aggregate: `import Dregg2.Circuit.Emit.MinaWrapVkDigestChain`
-/
import Dregg2.Circuit.Emit.MinaPhase1TapeBinding

namespace Dregg2.Circuit.Emit.MinaWrapVkDigestChain

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.PastaFieldSound (SK limbAt pLimb)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt)
open Dregg2.Circuit.Emit.MinaWrapVerifierProgram
open Dregg2.Circuit.Emit.MinaWrapVerifierSponge
open Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp
open Dregg2.Circuit.Emit.PastaPoseidonFq (Params fpParams)
open Dregg2.Circuit.Emit.MinaPhase1Chain (pairsOf linkStepOf)
open Dregg2.Circuit.Emit.MinaRealBlockTranscript (VKDIGEST)

set_option autoImplicit false
set_option maxRecDepth 20000000
set_option maxHeartbeats 4000000

/-! ## §1 — THE 56 COORDINATES OF THE DEVNET BLOCKCHAIN WRAP VERIFIER INDEX.

⚑ **GENERATED.** Every literal below is written by `metatheory/fixtures/gen_wrap_vk_comm_xy.py`
from the sha256-pinned fixture, in `VerifierIndex::digest`'s own absorb order: 7 `sigma_comm`,
15 `coefficients_comm`, then `generic`, `psm`, `complete_add`, `mul`, `emul`, `endomul_scalar`.
`x` then `y`, whole base-field elements. -/

/-- GENERATED — see `metatheory/fixtures/gen_wrap_vk_comm_xy.py`. -/
def VK_COMM_XY : List Nat :=
  [
   10238517694385979400441067096422230638797003193155225134939062071676615297964,
   3900210177105842176653843375981629413475496388856003483451534127124171623991,
   15745569438365094165820543421253218295900016638241048359684559871986848996300,
   22464607937190784244764989161879410897924893574994295722141162970704138921684,
   1348810928739486739550565580977632677189634152439878210885155462708474268139,
   21909548691958096430140910202097691643019658230610581755067301416225068831101,
   7162949178191457163330541908341973291353419054359843509870622177186154831109,
   28251733110730332090087383815976602648219818115081659013706571196678057838606,
   14828479449944575961876792004758925054348372899995888067442819198428246388139,
   25611501809232636111767340003539510947477274670250905801777345176045700782203,
   8743318142348947557626461239892801571835016752674911973903408971652722769361,
   17169127825548115406432078625029683985045882054108087967646003545701384822997,
   14533069567859997931411338798235390554646264745565930216225706045991714547029,
   230076843026232836139391506383317233661567084986689891555547340509935178276,
   17604975070393268522741884040314934259857325626778301999113489011159580765364,
   17038202213383175764498908207865223931558897286427890188578695361555563473773,
   3629213040537781701150823170145380192583936597459527369785224168714974501154,
   8967498922905016531705096735466268931827878423034496453575837306125485943592,
   26629970381965241897282560250933008696433594742695899977030242829782513135375,
   9739183580260344617466979875346260310769325103327953257156394960775266554566,
   27951503287423751919712121095792104915117737379594415816405228985740763378230,
   16859977354613052254445941772213940998400671999100803159807414487565853509402,
   24564626843488319919500904353351783519278685431443895532004759612756541167124,
   6894717885193921115746283271411840268874481546230145946078422154586646993790,
   21097804363354425878220962894775119920206121345704028932119438848871264424680,
   22183198279623402680222102419263275324196163927923119890371040246232456607676,
   28133329390722676823609700606655986836956419495821107970810258390695099502881,
   1959036676278517161890138452385797121793525561906778075243702699983729666862,
   12160866745240813956716089835359244952231316345615235096984889044149071065034,
   9435402212832378946561648668198360482420414240218944966090969465787264524907,
   4553125220630386866536673088952173463994717929684098347875570662002529751583,
   26479401893816489483181665154094527286688400684291728677451425076681205206921,
   15242167493270380075594800822907054421648334928459578079597652483754631538534,
   12112565980258790950711338310816680956717745728863488719502692296298919843326,
   17816717724783781224621217114780070384305374196336428615119130460312030662710,
   8987336457985823771915972080423303259580319582856580168594155238119763833941,
   22773652833227420169167171502886345233490081908372707509170391777508327649539,
   27800782081073374487918820149511719006280279339342059247076731774950404926196,
   13322016142261673328103021151884132126539838823176318065735479485979378830990,
   28108429549031047740384716268717266777323693987249464588150837128016978114117,
   21653356320857381006968735007818291248602525606697163836668798436313155259567,
   14973083266869769883145738252765549430619775182650626026062456519446666029535,
   5953795165810567480458521026869249512810795572323766633824559722220986191161,
   15901911886607693013161673396738069538954749595972174355871589616905356113255,
   24520983069735898256276925645671976288036990947174381745390989718145111659035,
   7886722312494759881281503674899925356215530043385313314588020090486316053004,
   4769154752149556066230820330886643270882173161025745140702742835888634479396,
   13452803353367938068237548133967328903864891688948026343225226820305166787867,
   13805384444512076770002989510975754788187213458051321078716086741317379509579,
   15607277084273474338836773571403635801105736341964995465583685300893782640264,
   28399397168984168516318441257753832010966733359830277905893072343997159553477,
   25449667763879462852100978128524499066487315609880734458875244513989285430921,
   7815551422170048242546256550860518974557789604652241254080089687054669188281,
   890463350541575175773277669201627422969786359695021685876185905984520754873,
   2153859778758829261248299182898345054593593782686804112833600356728172931805,
   713943172506841607399564506540804291592984762176494418658357787378120446532
  ]

/-- GENERATED — see `metatheory/fixtures/gen_wrap_vk_comm_xy.py`. -/
def TXN_VK_COMM_XY : List Nat :=
  [
   20855224843241686736939059870927831219764536853238177719060692421065538520976,
   17505690117660547766153587635691013998921342922048417642117355897833429117481,
   5916476954971449653707976756901174752558074000004368350277992158966224106940,
   8765545075053537434453262180516346785511523459631298513841454867640644928440,
   18274196297610260795793541035484536605576698933150397727785056867356539134957,
   134273913634467036266717512386630952840448631418971055249031322934447152245,
   5445530067959496392667907808322062010487762915120627636448201003811972779186,
   4135408145162681253977214179761782058985675693565584602291387981039699699397,
   23596235234039543469805252710978660721662571349361086731072560599725670439147,
   8880819437402957725414134020581683381967382246096000971832468376984546738604,
   9459062649637162408492799181173698892337638948234251517737917820908072459161,
   6731472955528171744403208855888325085507663514614173689379500083970844865834,
   9150554182664025193326331218468072689749308143309866130226045344145102341530,
   16927200407695796180766453254792510757159441167153750409814873014745337622890,
   11950962706550976234801430276405693809707451213582382769283288414074153180969,
   2443210654696315950248775316515591628719158768210376014850260458025074860303,
   1299971070503703472449606020818555292487010943179969442714905981416222250134,
   8884095662854068958190419968844893366157962840178015727497211769384948869569,
   27338709624067288180242480378572810740582563538807041097318897498295588222503,
   21143727107994400670155580528665044982703148970663095523313646674410153481300,
   1537021921551250044420878864515296795945389600826505578875890712033298182167,
   19367064653260113783715063166962653296782277225591191073629653152360683096812,
   20149159241710001041727193928825458833497319707477675186848977991116728316813,
   13775642556962229614622105587003922115017366324177875119167423433459376167388,
   15506429686420052430464216049642905554579820905877134700705206410691359802593,
   15531165381638263764768120065659879644375378522744115014561290810129511580736,
   9378883205105011492840559387933531064881901820371009618724741253689536234987,
   2398009913301159921215169434269716030898547885507351249391210325065596467183,
   22286138766763071719094803712598518378127551487472026612279781463339801107715,
   28502913837382322870562279528271892194594196638503505162851473976065223305249,
   22405682271980758441084150534251835746548140153997120524930755362681889596067,
   17323525408734395389181817745485366158553777581081288470567848338067071122959,
   8947643529784640944037822293346827734431469518084735359915741258952992606241,
   7103961957182559550639295180883977092797796459232496291767647310985271001624,
   25246681806353186353300537510635527406922184301306024069555636669886568742751,
   26856605783475597375565606144632046787435589770380921728409443683475563111922,
   23297052637954733051579818690360409422286749137660728043153156091809513708283,
   2840000074382436465339148778200296158984080204133901742136944570957363327021,
   23135228817717110049341026769593107795678653024557441764277072948506892441872,
   6211616911918964609938970668918666139293038081085008885910866082931239794958,
   28597175448272789799069896160392766038783043174713436777072413101319630360932,
   20883737762067379868574029069733640392793555448939847323153533135484712042008,
   20282576804963124776533491221935236761066321401621561792684392287736454230637,
   13494506471312727770311767671955382641160425344506625356089795076286151993259,
   8012006179982632094771094896978388519314298487369570388904121826143996199841,
   3355175980408567987079261742816235262282752308633150899122569040576989161674,
   25392611369435573626099062836895906969296551352998630163696785418733979109860,
   16582421493126737884572131434959809010329008345543818913631100029311436531520,
   11867934219476576800380065133252265390525056991395692210653066808375366760798,
   6491035846238903397187295109166185120535938033585656085329476964834321363214,
   21538356831492990201625432077204864042025778418221666496058419749778985732741,
   9109830738638630543532648018443945320696994261474116257813434488519105964584,
   698483576121222685367683300746760411455087911785957230764204269350352294252,
   21843356482196135808765248499248139609753953824348019503122877739751774938189,
   12618037090053490692373075134223284507376627173981076741124985743358139654020,
   8222146484561733716118161112449096775379854182942647676779063741100365854210
  ]

/-! ## §2 — TWENTY-EIGHT POINTS ON PALLAS, AND TWENTY-EIGHT MORE THAT ARE NOT THIS INDEX'S.

Necessary, and named as necessary — §7 is what says how far it reaches. -/

/-- The number of commitments `VerifierIndex::digest` absorbs on a devnet Wrap index. -/
def NVK : Nat := 28

/-- Commitment `i` of the blockchain index, in the projective form the Pasta cone shares. -/
def vkPt (i : Nat) : Pt := (VK_COMM_XY.getD (2 * i) 0, VK_COMM_XY.getD (2 * i + 1) 0, 1)

/-- Commitment `i` of the devnet **transaction** Wrap index — the sibling §7 uses. -/
def txnPt (i : Nat) : Pt := (TXN_VK_COMM_XY.getD (2 * i) 0, TXN_VK_COMM_XY.getD (2 * i + 1) 0, 1)

/-- ⚑ **28 COMMITMENTS, 56 COORDINATES, NO PAD.** 56 is even, so `pairsOf` leaves no padding slot —
the phase-1 tape's 37-element first segment forced one and this stream forces none. -/
theorem the_index_is_twenty_eight_commitments :
    VK_COMM_XY.length = 2 * NVK
    ∧ TXN_VK_COMM_XY.length = 2 * NVK
    ∧ VK_COMM_XY.length % 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **28/28 ON PALLAS.** `y²·z = x³ + 5·z³` over `Fp` — the same `projOnCurveM` the tape's 26
points face. -/
theorem every_vk_commitment_is_on_pallas :
    ((List.range NVK).all (fun i => projOnCurveM pN curveB (vkPt i))) = true := by native_decide

/-- …and none is the point at infinity, so the homogeneous curve equation is not being satisfied by
a degenerate triple. -/
theorem no_vk_commitment_is_the_identity :
    ((List.range NVK).all (fun i => !isInfM pN (vkPt i))) = true := by native_decide

/-- …and the 28 are 28 DIFFERENT points, so a census that matched one point 28 times could not
pass. -/
theorem the_vk_commitments_are_twenty_eight_distinct_points :
    ((List.range NVK).all (fun i =>
      (List.range NVK).all (fun k => decide (i = k) || !projEqM pN (vkPt i) (vkPt k)))) = true := by
  native_decide

/-! ## §3 — THE 28 LINKS ARE THE SPONGE'S OWN SCHEDULE, NOT A COUNT. -/

/-- The absorbed pairs, in `digest()`'s order. -/
def vkLinkXs : List (Nat × Nat) := pairsOf VK_COMM_XY

def vkLinkX (j : Nat) : Nat × Nat := vkLinkXs.getD j (0, 0)

theorem the_vk_chain_is_twenty_eight_links : vkLinkXs.length = NVK := by decide

/-- ⚑ **THE CHAIN STATE.** `vkChainState j` is the sponge state entering link `j`; `vkChainState 0`
is the fresh Kimchi sponge `EFqSponge::new` opens. -/
def vkChainState : Nat → List Nat
  | 0 => [0, 0, 0]
  | (j + 1) => linkStepOf fpParams (vkChainState j) (vkLinkX j)

theorem the_vk_chain_starts_fresh : vkChainState 0 = PastaPoseidonFq.newSponge.st := rfl

/-- ⚑ **THE RECURSION IS A PREFIX FOLD** — the bridge that lets the general schedule theorem below
speak about the object the machine actually runs. General in `n`; no evaluation. -/
theorem the_vk_chain_is_the_prefix_fold (n : Nat) (h : n ≤ NVK) :
    vkChainState n = (vkLinkXs.take n).foldl (linkStepOf fpParams) [0, 0, 0] := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have hk : k < vkLinkXs.length := by
        rw [the_vk_chain_is_twenty_eight_links]; omega
      have hstep : vkChainState (k + 1) = linkStepOf fpParams (vkChainState k) (vkLinkX k) := rfl
      rw [hstep, ih (by omega), List.take_add_one, List.foldl_append,
        List.getElem?_eq_getElem hk]
      simp [vkLinkX, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- ⚑⚑ **`the_twenty_eight_links_are_the_index_digests_own_schedule`** — absorbing the index's 56
coordinates into a FRESH `fp_kimchi` sponge and squeezing lands on exactly the state the 28 links
carry. This is `MinaPhase1Chain.the_pairs_are_the_absorb_schedule` — general over every `Params` and
every segment — instantiated here, so 28 is DERIVED from the rate-2 sponge's own absorb/squeeze
schedule and not counted off a list. -/
theorem the_twenty_eight_links_are_the_index_digests_own_schedule :
    (PastaPoseidonFq.squeeze1 fpParams
        (PastaPoseidonFq.absorbMany fpParams
          ⟨PastaPoseidonFq.newSponge.st, PastaPoseidonFq.Mode.absorbed 0⟩ VK_COMM_XY)).1.st
      = vkChainState NVK := by
  rw [the_vk_chain_is_the_prefix_fold NVK le_rfl,
    List.take_of_length_le (le_of_eq the_vk_chain_is_twenty_eight_links)]
  exact MinaPhase1Chain.the_pairs_are_the_absorb_schedule fpParams (by decide) VK_COMM_XY [0, 0, 0]
    (by decide) rfl (by decide)

/-- ⚑ **AND EVERY COORDINATE IS ABSORBED EXACTLY ONCE, IN ORDER.** Without this the chain could be
28 honest permutations of values nobody checked. -/
theorem the_vk_chain_absorbs_the_commitments_in_order :
    ((List.range NVK).flatMap (fun j => [(vkLinkX j).1, (vkLinkX j).2])) = VK_COMM_XY := by
  native_decide

/-- ⚑⚑ **THE DIGEST — `digest_fq` SQUEEZES FROM ABSORB MODE, SO IT IS LANE 0.** Where `fq_digest`
was lane 1 of an already-squeezed state, this one is lane 0 of the 28th permutation. -/
def vkDigest : Nat := (vkChainState NVK).getD 0 0

/-- ⚑⚑ **`the_vk_chain_derives_the_verifier_index_digest`** — the element the phase-1 transcript
absorbs FIRST, and which the tree carried as a bare constant in two places, is what these 28 links
compute from the pinned index's own commitments. -/
theorem the_vk_chain_derives_the_verifier_index_digest : vkDigest = VKDIGEST := by native_decide

/-! ## §4 — THE MACHINE COMPUTES THE CHAIN STEP, AT EVERY LINK.

The same `fpAbsorbCore` program, the same `allocAt` read, the same kernel-clean generic theorem the
phase-1 chain rests on. -/

def vkChainInitVec (j : Nat) : List Nat :=
  [ (vkChainState j).getD 0 0, (vkChainState j).getD 1 0, (vkChainState j).getD 2 0
  , (vkLinkX j).1, (vkLinkX j).2, 0 ]

def vkChainOutVec (j : Nat) : List Nat := runProgVecAt pN (vkChainInitVec j) fpAbsorbCore

def vkChainOut (j : Nat) : List Nat :=
  [ regsOf (vkChainOutVec j) (allocAt PastaPoseidon.rounds 0)
  , regsOf (vkChainOutVec j) (allocAt PastaPoseidon.rounds 1)
  , regsOf (vkChainOutVec j) (allocAt PastaPoseidon.rounds 2) ]

/-- ⚑⚑ **THE LINK'S MACHINE OUTPUT IS THE NEXT LINK'S INPUT — AT EVERY `j`, WITH NO HYPOTHESES.**
An instance of `MinaWrapVerifierSpongeFp.the_absorb_program_permutes_gen` at `fpParams`. -/
theorem the_vk_chain_step_is_the_kimchi_permutation (j : Nat) :
    vkChainOut j = vkChainState (j + 1) := by
  have hregs : regsOf (vkChainOutVec j)
      = runProgAt pN (regsOf (vkChainInitVec j)) fpAbsorbCore := by
    rw [vkChainOutVec, regsOf_runProgVecAt]
  have h0 : regsOf (vkChainInitVec j) 0 = (vkChainState j).getD 0 0 := rfl
  have h1 : regsOf (vkChainInitVec j) 1 = (vkChainState j).getD 1 0 := rfl
  have h2 : regsOf (vkChainInitVec j) 2 = (vkChainState j).getD 2 0 := rfl
  have h3 : regsOf (vkChainInitVec j) 3 = (vkLinkX j).1 := rfl
  have h4 : regsOf (vkChainInitVec j) 4 = (vkLinkX j).2 := rfl
  have hperm := the_fp_absorb_program_permutes (regsOf (vkChainInitVec j))
  rw [h0, h1, h2, h3, h4] at hperm
  show [ regsOf (vkChainOutVec j) (allocAt PastaPoseidon.rounds 0)
       , regsOf (vkChainOutVec j) (allocAt PastaPoseidon.rounds 1)
       , regsOf (vkChainOutVec j) (allocAt PastaPoseidon.rounds 2) ] = vkChainState (j + 1)
  rw [hregs, hperm]
  show _ = linkStepOf fpParams (vkChainState j) (vkLinkX j)
  rw [MinaPhase1Chain.linkStepOf_fp]

/-! ## §5 — ⚑ THE DESCRIPTOR IS THE DEPLOYED ONE. NO NEW AIR.

`vkChainDesc` is not "the same shape as" `MinaPhase1Chain.chainDesc`; it IS that object. The residual
here is 28 witnesses, not one constraint. -/

def vkChainDesc : EffectVmDescriptor2 := MinaPhase1Chain.chainDesc

/-- ⚑ **`dregg-pasta-fp-chainlink::v1`, UNCHANGED**, at 256 public inputs. -/
theorem the_descriptor_is_the_deployed_phase1_link :
    vkChainDesc = MinaPhase1Chain.chainDesc
    ∧ MinaPhase1Chain.CHAIN_PI_COUNT = 256 := ⟨rfl, rfl⟩

def vkInBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt ((vkChainState j).getD 0 0))
    ++ (List.range SK).map (limbAt ((vkChainState j).getD 1 0))
    ++ (List.range SK).map (limbAt ((vkChainState j).getD 2 0))

/-- The OUTGOING-state block — read from the interpreter's own final register file. -/
def vkOutBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt ((vkChainOut j).getD 0 0))
    ++ (List.range SK).map (limbAt ((vkChainOut j).getD 1 0))
    ++ (List.range SK).map (limbAt ((vkChainOut j).getD 2 0))

def vkAbsorbedBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt (vkLinkX j).1) ++ (List.range SK).map (limbAt (vkLinkX j).2)

def vkChainPIs (j : Nat) : List ℤ := vkInBlock j ++ vkOutBlock j ++ vkAbsorbedBlock j

theorem vkChainPIs_length (j : Nat) : (vkChainPIs j).length = 256 := by
  simp [vkChainPIs, vkInBlock, vkOutBlock, vkAbsorbedBlock, SK]

/-- ⚑⚑ **CONTINUITY IN THE EMITTED CLAIMS** — link `j`'s outgoing PI block IS link `j+1`'s incoming
block, limb for limb, at every `j`. This is the equality a fold's `cb.connect` enforces in-circuit. -/
theorem the_vk_emitted_claims_are_continuous (j : Nat) : vkOutBlock j = vkInBlock (j + 1) := by
  simp only [vkOutBlock, vkInBlock, the_vk_chain_step_is_the_kimchi_permutation]

def vkChainTrace (j : Nat) : List (List ℤ) :=
  runRowsVecAt pN pLimb (vkChainInitVec j) 0 fpAbsorbProg

theorem vkChainTrace_is_the_program_run (j : Nat) :
    vkChainTrace j = runRowsAt pN pLimb (regsOf (vkChainInitVec j)) 0 fpAbsorbProg := by
  rw [vkChainTrace, runRowsVecAt_is_runRowsAt]

/-! ### §5b — the wire, kernel-clean and general in the link.

`in(3) ++ out(3) ++ absorbed(2)` at `SK = 32` eight-bit limbs. All three are `rfl`: `drop`/`take`
walk a spine of known length and never open a limb. -/

theorem the_vk_wire_lane0 (j : Nat) :
    ((vkChainPIs j).drop (6 * SK)).take SK
      = (List.range SK).map (limbAt (vkLinkX j).1) := rfl

theorem the_vk_wire_lane1 (j : Nat) :
    ((vkChainPIs j).drop (7 * SK)).take SK
      = (List.range SK).map (limbAt (vkLinkX j).2) := rfl

/-- ⚑ **AND `[3·SK, 4·SK)` IS THE OUTGOING LANE 0** — the lane `digest_fq` reads. -/
theorem the_vk_wire_outgoing_lane0 (j : Nat) :
    ((vkChainPIs j).drop (3 * SK)).take SK
      = (List.range SK).map (limbAt ((vkChainOut j).getD 0 0)) := rfl

/-- The 32 felts the chain publishes for coordinate `m`: link `m / 2`, lane `m % 2`. -/
def vkWireSlot (m : Nat) : List ℤ :=
  ((vkChainPIs (m / 2)).drop ((6 + m % 2) * SK)).take SK

/-- ⚑⚑ **ALL 56 COORDINATES ARE ON THE WIRE.** The absorbed pair of link `m / 2` carries coordinate
`m`, for all 56 — so the published PI blocks really are the image of the index's commitments. -/
theorem the_absorbed_pairs_are_the_vk_coordinates :
    ((List.range (2 * NVK)).all (fun m =>
      decide ((if m % 2 = 0 then (vkLinkX (m / 2)).1 else (vkLinkX (m / 2)).2)
                = VK_COMM_XY.getD m 0))) = true := by
  native_decide

/-- The wire slice of coordinate `m` IS that coordinate's limbs — §5b's two lanes composed with the
census above, so a slot's 32 published felts are the whole 254-bit element and nothing else. -/
theorem the_vk_wire_slot_is_the_coordinates_limbs (m : Nat) :
    vkWireSlot m
      = (List.range SK).map
          (limbAt (if m % 2 = 0 then (vkLinkX (m / 2)).1 else (vkLinkX (m / 2)).2)) := by
  unfold vkWireSlot
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [h]; simpa using the_vk_wire_lane0 (m / 2)
  · rw [h]; simpa using the_vk_wire_lane1 (m / 2)

/-! ## §6 — ⚑⚑ THE WELD: THE INDEX DIGEST IS THE PHASE-1 TAPE'S HEAD.

This is the point of the leg. Link 27's OUTGOING LANE 0 (PI slots `[3·SK, 4·SK)`) and the phase-1
chain's link 0 ABSORBED[0] (PI slots `[6·SK, 7·SK)`) are the same **32 felts, elementwise, at full
limb width** — a slice comparison with no arithmetic, no digest and therefore **no birthday bound**;
32 × 8 = 256 > 254, so every bit is on the wire and a forger must match all 32 limbs. -/

/-- The link whose outgoing lane 0 is the digest — the last one. -/
def VK_DIGEST_LINK : Nat := 27

/-- Flat slot 0 of the phase-1 tape is the verifier-index digest — link 0's absorbed lane 0. -/
theorem the_phase1_tape_head_is_the_index_digest :
    (MinaPhase1Chain.linkX 0).1 = VKDIGEST := by decide

/-- ⚑ **THE VALUE TIE.** The only compiled step; everything below is kernel, rewritten through it. -/
theorem the_vk_chain_ends_on_the_index_digest :
    (vkChainOut VK_DIGEST_LINK).getD 0 0 = VKDIGEST := by
  rw [the_vk_chain_step_is_the_kimchi_permutation]
  exact the_vk_chain_derives_the_verifier_index_digest

theorem the_index_digest_is_the_phase1_tape_head :
    (vkChainOut VK_DIGEST_LINK).getD 0 0 = (MinaPhase1Chain.linkX 0).1 := by
  rw [the_vk_chain_ends_on_the_index_digest, the_phase1_tape_head_is_the_index_digest]

/-- ⚑⚑ **THE WIRE TIE, ELEMENTWISE AT FULL LIMB WIDTH.** Kernel-clean: `rfl` on both sides,
rewritten through the one compiled value equality. -/
theorem the_vk_wire_blocks_are_equal :
    ((vkChainPIs VK_DIGEST_LINK).drop (3 * SK)).take SK
      = ((MinaPhase1Chain.chainPIs 0).drop (6 * SK)).take SK := by
  rw [the_vk_wire_outgoing_lane0, MinaPhase1TapeBinding.the_wire_lane0 0,
    the_index_digest_is_the_phase1_tape_head]

/-- ⚑ **AND THE TIE IS NOT VACUOUS.** The block is 32 felts, it is not the zero vector, and it is
not the block the SAME link publishes in its other outgoing lane — so this is an equality between
two things that could have differed, not two copies of a constant. -/
theorem the_vk_wire_block_is_not_trivial :
    (((vkChainPIs VK_DIGEST_LINK).drop (3 * SK)).take SK).length = 32
    ∧ ((vkChainPIs VK_DIGEST_LINK).drop (3 * SK)).take SK ≠ List.replicate 32 (0 : ℤ)
    ∧ ((vkChainPIs VK_DIGEST_LINK).drop (3 * SK)).take SK
        ≠ ((vkChainPIs VK_DIGEST_LINK).drop (4 * SK)).take SK := by
  native_decide

/-- ⚑ **A ONE-FELT TIE WOULD BE `2^31`, AND THIS IS NOT ONE.** Stated as arithmetic so the strength
claim is checkable rather than asserted. -/
theorem the_vk_tie_is_the_whole_element :
    SK * PastaFieldSound.SB = 256 ∧ 2 ^ 254 < pN ∧ pN < 2 ^ (SK * PastaFieldSound.SB) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## §7 — ⚠⚠ WHAT THIS DERIVATION CANNOT SEE, AS THEOREMS.

⚠ **READ THIS BEFORE BELIEVING §6.** -/

/-- Every scalar field of a `VerifierIndex` that `digest()` binds to `_`. Carried as a record so the
next theorem is a statement about them rather than a comment about them. -/
structure IndexScalars where
  domainLog2 : Nat
  domainSize : Nat
  maxPolySize : Nat
  zkRows : Nat
  publicLen : Nat
  prevChallenges : Nat
  shift : List Nat
deriving DecidableEq

/-- The devnet Wrap index's scalars — **identical on the blockchain and the transaction index**,
which the harness checks against both fixtures. `shift` is the seven 32-byte little-endian values of
the pinned JSON. -/
def DEVNET_WRAP_SCALARS : IndexScalars :=
  { domainLog2 := 14
  , domainSize := 16384
  , maxPolySize := 32768
  , zkRows := 3
  , publicLen := 40
  , prevChallenges := 2
  , shift :=
      [ 1
      , 328286983623303317637963920346571898945724874896624808297627776768640590563
      , 220790353665890403705559231885806581221301230221265349993193424985261418438
      , 211720422259245489258933986578227917398506328781182391541883955346082631533
      , 211634429328372259348572816867521795029192573698954618296359582461568682420
      , 317476258975906211462498873025720239242336777696786967497139785505242641540
      , 99141114743446054294525453467100398765600279346526770105380817318185104545 ] }

/-- `VerifierIndex::digest`, as a function of what it actually reads. ⚑ The scalars argument is
UNUSED, and that is the modelling claim: kimchi destructures the index and binds `domain`,
`max_poly_size`, `zk_rows`, `srs`, `public`, `prev_challenges`, `shift`, `w`, `endo`,
`linearization` and `powers_of_alpha` to `_` (`verifier_index.rs:405-447`, tag `0.3.0`). -/
def indexDigestOf (_scalars : IndexScalars) (comms : List Nat) : Nat :=
  ((pairsOf comms).foldl (linkStepOf fpParams) [0, 0, 0]).getD 0 0

/-- …and that model IS this chain on this index. -/
theorem the_modelled_digest_is_the_chains :
    indexDigestOf DEVNET_WRAP_SCALARS VK_COMM_XY = VKDIGEST := by
  have h : vkChainState NVK = vkLinkXs.foldl (linkStepOf fpParams) [0, 0, 0] := by
    rw [the_vk_chain_is_the_prefix_fold NVK le_rfl,
      List.take_of_length_le (le_of_eq the_vk_chain_is_twenty_eight_links)]
  show (vkLinkXs.foldl (linkStepOf fpParams) [0, 0, 0]).getD 0 0 = VKDIGEST
  rw [← h]
  exact the_vk_chain_derives_the_verifier_index_digest

/-- ⚑⚑ **`the_index_digest_cannot_see_the_circuit_shape`** — general, and `rfl`, because the scalars
are not in the preimage at all. The digest the phase-1 transcript absorbs as the verifier index's
IDENTITY is a function of its 28 commitments and of nothing else. -/
theorem the_index_digest_cannot_see_the_circuit_shape (s t : IndexScalars) (cs : List Nat) :
    indexDigestOf s cs = indexDigestOf t cs := rfl

/-- ⚑ **AND THE GENERAL FACT IS NOT VACUOUS — HERE IS THE PAIR.** An index taking 41 public inputs
instead of 40 is a DIFFERENT verifier index for a DIFFERENT circuit, and it has the SAME digest. -/
theorem the_index_digest_cannot_see_the_public_input_count :
    DEVNET_WRAP_SCALARS ≠ { DEVNET_WRAP_SCALARS with publicLen := 41 }
    ∧ indexDigestOf DEVNET_WRAP_SCALARS VK_COMM_XY
        = indexDigestOf { DEVNET_WRAP_SCALARS with publicLen := 41 } VK_COMM_XY
    ∧ indexDigestOf DEVNET_WRAP_SCALARS VK_COMM_XY = VKDIGEST :=
  ⟨by decide, rfl, the_modelled_digest_is_the_chains⟩

/-! ### §7b — and it cannot see WHICH verifier index it is digesting.

The devnet **transaction** Wrap index is 28 Pallas points of the same shape, sharing not one
commitment with the blockchain index, and the same 28 links over it are an internally perfect chain
deriving its own digest. Nothing in this file selects between them; the sha256 pin on a JSON file
does, and that is a fact about a build tree. -/

/-- `index.digest::<EFqSponge>()` of the devnet **transaction** Wrap index — derived by these same
28 links from `TXN_VK_COMM_XY`, never transcribed. -/
def TXN_VKDIGEST : Nat :=
  23415626234947000852670752923457805252197068866276289507445996557171837950872

def txnLinkX (j : Nat) : Nat × Nat := (pairsOf TXN_VK_COMM_XY).getD j (0, 0)

def txnChainState : Nat → List Nat
  | 0 => [0, 0, 0]
  | (j + 1) => linkStepOf fpParams (txnChainState j) (txnLinkX j)

/-- ⚑ The sibling index is exactly as good a 28-point Pallas set, and shares nothing with ours. -/
theorem the_transaction_index_is_an_equally_on_curve_twenty_eight :
    ((List.range NVK).all (fun i => projOnCurveM pN curveB (txnPt i))) = true
    ∧ ((List.range NVK).all (fun i => !isInfM pN (txnPt i))) = true
    ∧ ((List.range NVK).all (fun i =>
        (List.range NVK).all (fun k => !projEqM pN (txnPt i) (vkPt k)))) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- ⚑⚑ **`the_derivation_cannot_see_which_verifier_index_this_is`** — the machinery is
index-agnostic. It proves *"this digest is THESE commitments'"*; it cannot prove *"these are THIS
block's verifier index's commitments"*, and the sibling cone paid months for exactly that distance
one layer up (`MinaPhase1TapeBinding.the_on_curve_check_cannot_see_provenance`). -/
theorem the_derivation_cannot_see_which_verifier_index_this_is :
    (txnChainState NVK).getD 0 0 = TXN_VKDIGEST
    ∧ (txnChainState NVK).getD 0 0 ≠ vkDigest := by
  refine ⟨by native_decide, by native_decide⟩

/-! ## §8 — BOTH POLES: AN ON-CURVE-AND-WRONG COMMITMENT.

⚑ **THE FORGERY NEEDS NO SEARCH AND IS NOT A BUMPED LIMB.** It is `sigma_comm[0]` of the devnet
**transaction** Wrap index — a genuine Pallas commitment of a genuine Mina verifier index of the
same shape. Every forgery in this cone is an on-curve-and-wrong REAL point, never an off-curve one,
because `onCurveQ` could never have caught the thing this cone was built to catch. -/

def FORGED_VK_SIGMA0 : Pt := txnPt 0

/-- ⚑⚑ **`the_on_curve_leg_cannot_see_the_substituted_commitment`** — the substitution is on the
Pallas curve, it is NOT this index's `sigma_comm[0]`, and §2's 28-point on-curve leg **still passes
28/28** with it in place. -/
theorem the_on_curve_leg_cannot_see_the_substituted_commitment :
    projOnCurveM pN curveB FORGED_VK_SIGMA0 = true
    ∧ projEqM pN FORGED_VK_SIGMA0 (vkPt 0) = false
    ∧ ((List.range NVK).all
        (fun i => projOnCurveM pN curveB (if i = 0 then FORGED_VK_SIGMA0 else vkPt i))) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND THE FALSIFIER FALSIFIES.** Both coordinates are non-zero and differ from the honest
ones, and the slot the tamper aims at really is `sigma_comm[0].x` — the three checks whose absence
refuted a sibling control that moved a zero into a zero. -/
theorem the_vk_forgery_is_a_real_displacement :
    FORGED_VK_SIGMA0.1 ≠ 0 ∧ FORGED_VK_SIGMA0.2.1 ≠ 0
    ∧ FORGED_VK_SIGMA0.1 ≠ (vkPt 0).1 ∧ FORGED_VK_SIGMA0.2.1 ≠ (vkPt 0).2.1
    ∧ (vkLinkX 0).1 = (vkPt 0).1 ∧ (vkLinkX 0).1 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **…AND IT MOVES ALL 32 PUBLISHED FELTS**, not one. A forgery that moved a single limb would
leave 31 slices agreeing and would say nothing about the width of the tie. -/
theorem the_vk_forgery_moves_every_published_felt :
    ((List.range SK).all (fun i =>
      decide (limbAt (vkPt 0).1 i ≠ limbAt FORGED_VK_SIGMA0.1 i))) = true := by native_decide

/-- ⚑⚑ **AND IT MOVES THE DIGEST** — 28 permutations downstream, so the substitution reaches the
phase-1 tape's head and the 32-felt slice comparison of §6 refuses. ⚑ **BOTH LANES**: link 0 absorbs
`sigma_comm[0]`'s `x` AND `y`, so this replaces a WHOLE POINT with a whole point, which is the only
substitution `the_on_curve_leg_cannot_see_the_substituted_commitment` is actually about. -/
theorem the_forged_vk_commitment_moves_the_index_digest :
    (let lx : Nat → Nat × Nat :=
       fun j => if j = 0 then (FORGED_VK_SIGMA0.1, FORGED_VK_SIGMA0.2.1) else vkLinkX j
     let st : Nat → List Nat := fun n => Nat.rec ([0, 0, 0] : List Nat)
       (fun j ih => linkStepOf fpParams ih (lx j)) n
     (st NVK).getD 0 0) ≠ VKDIGEST := by
  native_decide

/-- ⚑ **AND THE TAMPER TARGET IS THE WHOLE HONEST POINT.** Link 0's two absorbed slots really are
`sigma_comm[0]`'s coordinates and both differ from the substitution — so the control above is not a
value swapped for itself, which is exactly how a sibling falsifier was refuted. -/
theorem the_vk_digest_tamper_target_is_the_first_commitment :
    (vkLinkX 0).1 = (vkPt 0).1 ∧ (vkLinkX 0).2 = (vkPt 0).2.1
    ∧ (vkLinkX 0).1 ≠ FORGED_VK_SIGMA0.1 ∧ (vkLinkX 0).2 ≠ FORGED_VK_SIGMA0.2.1
    ∧ (vkLinkX 0).1 ≠ 0 ∧ (vkLinkX 0).2 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND IT MOVES THE WIRE** — both published slots of commitment 0, where §2's on-curve leg saw
nothing at all. -/
theorem the_forged_vk_commitment_moves_the_wire :
    vkWireSlot 0 ≠ (List.range SK).map (limbAt FORGED_VK_SIGMA0.1)
    ∧ vkWireSlot 1 ≠ (List.range SK).map (limbAt FORGED_VK_SIGMA0.2.1) := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## §9 — RESIDUALS, NAMED.

⚑ **1. THE PINNED FIXTURE IS A BUILD-TREE FACT.** `VK_COMM_XY` is the devnet blockchain Wrap index
because `bridge/mina-zkapp/fixtures/mina-devnet-wrap-blockchain-vk.json` hashes to
`062b7183…cdf626` and `mina-canonical-circuit-oracle.mjs` refuses otherwise, cross-checking against
openmina's `devnet_blockchain_verifier_index.json` when that checkout is present. That is a sha256
against a byte copy — strong, and **not an in-circuit fact**. §7b is that residual stated as a
theorem rather than as this paragraph.

⚑ **2. THE DIGEST DOES NOT BIND THE CIRCUIT SHAPE, AND THAT IS UPSTREAM'S DESIGN.** `domain`,
`max_poly_size`, `zk_rows`, `public`, `prev_challenges`, `shift`, `w` and `endo` are absorbed by
NOTHING (`the_index_digest_cannot_see_the_public_input_count`). Every other consumer of those fields
in this tree — the 40-element public input `MinaWrapPublicCommGate` builds, `ZETA_SRS`'s
`max_poly_size` exponent — carries them separately and none of them is welded to this digest. That
is a real seam and it is one layer above this file.

⚑ **3. NOTHING HERE IS AN IN-AIR CURVE GATE.** §2 is a kernel `decide` over the emitted constants,
not `PastaMsmOnCurve.onCurveGates` instantiated on the index's 28 points — the same residual
`MinaPhase1TapeBinding` §8.4 names for the tape's 26, and the same fix.

⚑ **4. 28 WITNESSES, ONE DESCRIPTOR.** As with both transcript phases, the residual is witnesses,
not algebra: 28 more 2 048-row traces of an already-deployed AIR.
-/

#assert_compiled the_index_is_twenty_eight_commitments
#assert_compiled every_vk_commitment_is_on_pallas
#assert_compiled no_vk_commitment_is_the_identity
#assert_compiled the_vk_commitments_are_twenty_eight_distinct_points
#assert_axioms the_vk_chain_is_twenty_eight_links
#assert_axioms the_vk_chain_starts_fresh
#assert_axioms the_vk_chain_is_the_prefix_fold
#assert_axioms the_twenty_eight_links_are_the_index_digests_own_schedule
#assert_axioms the_vk_chain_step_is_the_kimchi_permutation
#assert_axioms the_descriptor_is_the_deployed_phase1_link
#assert_axioms vkChainPIs_length
#assert_axioms the_vk_emitted_claims_are_continuous
#assert_axioms vkChainTrace_is_the_program_run
#assert_axioms the_vk_wire_lane0
#assert_axioms the_vk_wire_lane1
#assert_axioms the_vk_wire_outgoing_lane0
#assert_axioms the_vk_wire_slot_is_the_coordinates_limbs
#assert_axioms the_phase1_tape_head_is_the_index_digest
#assert_compiled the_vk_tie_is_the_whole_element
#assert_axioms the_index_digest_cannot_see_the_circuit_shape
#assert_compiled the_transaction_index_is_an_equally_on_curve_twenty_eight
#assert_compiled the_on_curve_leg_cannot_see_the_substituted_commitment
#assert_compiled the_vk_forgery_is_a_real_displacement
#assert_compiled the_vk_forgery_moves_every_published_felt
#assert_compiled the_vk_digest_tamper_target_is_the_first_commitment

-- ⚑ COMPILER-TRUSTED, and said out loud: each is up to 28 Kimchi permutations of a 255-bit state,
-- where the `decide` proof-term path overflows.
#assert_compiled the_vk_chain_absorbs_the_commitments_in_order
#assert_compiled the_vk_chain_derives_the_verifier_index_digest
#assert_compiled the_absorbed_pairs_are_the_vk_coordinates
#assert_compiled the_vk_wire_block_is_not_trivial
#assert_compiled the_derivation_cannot_see_which_verifier_index_this_is
#assert_compiled the_forged_vk_commitment_moves_the_index_digest
#assert_compiled the_forged_vk_commitment_moves_the_wire
-- …and the welds, which INHERIT the compiled fact they are rewritten through.
#assert_compiled the_vk_chain_ends_on_the_index_digest
#assert_compiled the_index_digest_is_the_phase1_tape_head
#assert_compiled the_vk_wire_blocks_are_equal
#assert_compiled the_modelled_digest_is_the_chains
#assert_compiled the_index_digest_cannot_see_the_public_input_count

end Dregg2.Circuit.Emit.MinaWrapVkDigestChain
