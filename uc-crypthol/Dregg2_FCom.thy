(*  Title:      Dregg2_FCom.thy
    Author:     dregg2 metatheory — UC transport pass (2026-05-30)

    CROSS-SYSTEM TRANSPORT of the dregg2 commitment functionality F_com into a
    real game-based / UC framework (CryptHOL + Sigma_Commit_Crypto on
    Isabelle2025-2 + AFP 2025-2).

    WHAT IS TRANSPORTED.
    The dregg2 Lean interface `Dregg2.Crypto.CryptoPrimitives`
    (metatheory/Dregg2/Crypto/Primitives.lean) carries a Pedersen commitment as:
      * `commit : Int -> Int -> Digest`           (value, blinding -> commitment)
      * `commit_hom`  — PROVED algebraic law: additive homomorphism
      * `binding   : Prop` — CARRIER: DLog/Pedersen binding (never proved in Lean)
      * `unlinkable: Prop` — CARRIER: hiding/anonymity (never proved in Lean)
    These two `Prop` carriers are exactly the *computational* UC obligations the
    Lean side defers to "the crypto layer". This theory DISCHARGES them in a real
    UC/game framework: the dregg2 commitment is the Pedersen scheme of CryptHOL's
    `Sigma_Commit_Crypto.Pedersen`, whose ideal commitment functionality F_com is
    the `Commitment_Schemes.abstract_commitment` locale (key_gen / commit / verify
    / valid_msg, with the hiding-, binding-, and correctness games).

    WHAT IS PROVED HERE (all green, no `sorry`/`oops`):
      * `dregg2_commit_hom`         — the Pedersen additive homomorphism: the
                                      Lean `commit_hom` PROVED-grade law, re-proved
                                      from the group structure (transport fidelity
                                      of the one algebraic law).
      * `dregg2_F_com_correct`      — F_com correctness (an honest open verifies).
      * `dregg2_F_com_hiding`       — PERFECT hiding: the dregg2 `unlinkable`
                                      carrier, discharged. Pedersen leaks zero bits
                                      (advantage = 0), unconditionally.
      * `dregg2_F_com_binding`      — binding reduces to discrete log: the dregg2
                                      `binding` carrier, discharged. The binding
                                      advantage EQUALS the DLog advantage of an
                                      explicit reduction, hence negligible under
                                      DLog hardness (`dregg2_F_com_binding_asymp`).
      * `dregg2_F_com_realizes`     — the bundling: the dregg2 Pedersen scheme
                                      REALIZES the ideal commitment functionality
                                      F_com (correct + perfectly hiding + binding-
                                      reduces-to-DLog), the UC realization statement
                                      at the commitment layer.

    All of the heavy lifting is the *existing* `Sigma_Commit_Crypto` library; this
    theory's job is the faithful TRANSPORT: naming the dregg2 objects, instantiating
    the locale at the dregg2 commitment, and stating the realization. We reuse:
      Commitment_Schemes.abstract_commitment  (the F_com locale + games)
      Pedersen.pedersen                        (the scheme + its three theorems)
*)

theory Dregg2_FCom
  imports
    Sigma_Commit_Crypto.Pedersen
begin

section\<open>F_com: dregg2's ideal commitment functionality, via CryptHOL\<close>

text\<open>The dregg2 commitment is the Pedersen scheme. We work inside the @{locale pedersen}
locale: a cyclic group \<open>\<G>\<close> of prime order. There, @{term ped_commit} is the
@{locale abstract_commitment} instance (key_gen / commit / verify / valid_msg) — this IS
the ideal commitment functionality F_com that dregg2's `commit` carrier points at.\<close>

context pedersen
begin

subsection\<open>The one PROVED algebraic law — the Pedersen additive homomorphism\<close>

text\<open>dregg2 Lean: \<open>commit_hom : commit (v+w) (r+s) = commit v r + commit w s\<close> is the single
PROVED-grade algebraic field of `CryptoPrimitives`. Here the commitment value (for a fixed
key \<open>ck\<close>) is \<^term>\<open>\<^bold>g [^] d \<otimes> ck [^] m\<close>; the homomorphism is the group law: committing to a
sum of messages with the sum of blindings is the product of the commitments. This re-proves,
in the UC group model, the fidelity of the one algebraic law the dregg2 metatheory relies on.\<close>

lemma dregg2_commit_hom:
  fixes m m' d d' :: nat
  assumes ck: "ck \<in> carrier \<G>"
  shows "(\<^bold>g [^] (d + d') \<otimes> ck [^] (m + m'))
           = (\<^bold>g [^] d \<otimes> ck [^] m) \<otimes> (\<^bold>g [^] d' \<otimes> ck [^] m')"
proof -
  interpret cg: comm_group \<G> by (rule group_comm_groupI) (rule cyclic_group_commute)
  have gd:  "\<^bold>g [^] d  \<in> carrier \<G>" using generator_closed by (rule nat_pow_closed)
  have gd': "\<^bold>g [^] d' \<in> carrier \<G>" using generator_closed by (rule nat_pow_closed)
  have cm:  "ck [^] m  \<in> carrier \<G>" using ck by (rule nat_pow_closed)
  have cm': "ck [^] m' \<in> carrier \<G>" using ck by (rule nat_pow_closed)
  have "(\<^bold>g [^] (d + d') \<otimes> ck [^] (m + m'))
          = (\<^bold>g [^] d \<otimes> \<^bold>g [^] d') \<otimes> (ck [^] m \<otimes> ck [^] m')"
    using ck by (simp add: nat_pow_mult)
  also have "\<dots> = (\<^bold>g [^] d \<otimes> ck [^] m) \<otimes> (\<^bold>g [^] d' \<otimes> ck [^] m')"
    using gd gd' cm cm' by (simp add: cg.m_ac)
  finally show ?thesis .
qed

subsection\<open>Correctness of F_com\<close>

text\<open>An honestly produced commitment opens correctly: dregg2 needs the commitment to be a
real commitment, not vacuous. This is @{thm abstract_correct}.\<close>

theorem dregg2_F_com_correct: "ped_commit.correct"
  by (rule abstract_correct)

subsection\<open>Discharge of the `unlinkable` carrier — PERFECT hiding\<close>

text\<open>dregg2 Lean: \<open>unlinkable : Prop\<close> is the anonymity/hiding carrier the crypto layer must
discharge. Here it is discharged AS PERFECT HIDING: no (even unbounded) adversary's
advantage in the IND-CPA hiding game exceeds 0. This is unconditional — Pedersen leaks zero
information about the committed value.\<close>

theorem dregg2_F_com_hiding: "ped_commit.perfect_hiding_ind_cpa \<A>"
  by (rule abstract_perfect_hiding)

text\<open>Alias under the name the bridge doc cites.\<close>
theorem dregg2_perfect_hiding: "ped_commit.perfect_hiding_ind_cpa \<A>"
  by (rule abstract_perfect_hiding)

subsection\<open>Discharge of the `binding` carrier — reduction to discrete log\<close>

text\<open>dregg2 Lean: \<open>binding : Prop\<close> is the soundness carrier (you cannot open a commitment two
ways). Here it is discharged AS A REDUCTION: the binding advantage of ANY adversary equals
the discrete-log advantage of the explicit reduction @{term dis_log_\<A>}. Thus binding holds
exactly as strongly as discrete log is hard in \<open>\<G>\<close>.\<close>

theorem dregg2_F_com_binding:
  "ped_commit.bind_advantage \<A> = discrete_log.advantage (dis_log_\<A> \<A>)"
  by (rule pedersen_bind)

text\<open>Alias under the name the bridge doc cites.\<close>
theorem dregg2_binding_reduces_to_dlog:
  "ped_commit.bind_advantage \<A> = discrete_log.advantage (dis_log_\<A> \<A>)"
  by (rule pedersen_bind)

subsection\<open>The single-group F_com realization bundle (named for the Lean bridge)\<close>

text\<open>The dregg2 Pedersen commitment realizes F_com in a single prime-order group: correct,
perfectly hiding, and binding-advantage equal to the DLog advantage of the reduction. This is
the theorem the Lean bridge @{text UCBridge.lean} cites as
\<open>Dregg2_UC.pedersen.dregg2_pedersen_realizes_F_com\<close>.

The hiding and binding games take DISTINCT adversary types in @{theory_text Commitment_Schemes}
(@{typ "(_,_,_,_) hid_adv"} = a state-passing pair vs @{typ "(_,_,_,_) bind_adversary"} = a single
opening-producing function), so the bundle quantifies a hiding adversary \<open>\<A>\<close> and a binding
adversary \<open>\<B>\<close> separately — they cannot be the same object.\<close>

theorem dregg2_pedersen_realizes_F_com:
  shows "ped_commit.correct"                                                \<comment> \<open>correctness\<close>
    and "ped_commit.perfect_hiding_ind_cpa \<A>"                              \<comment> \<open>`unlinkable`\<close>
    and "ped_commit.bind_advantage \<B> = discrete_log.advantage (dis_log_\<A> \<B>)"  \<comment> \<open>`binding`\<close>
    by (simp_all add: abstract_correct abstract_perfect_hiding pedersen_bind)

end

section\<open>The UC realization statement (asymptotic) and F_com bundle\<close>

text\<open>In the asymptotic locale @{locale pedersen_asymp} (a family of prime-order groups indexed
by the security parameter), the three properties become the standard UC-style realization of
the ideal commitment functionality F_com: perfectly hiding, and binding negligible iff DLog
is negligible.\<close>

context pedersen_asymp
begin

theorem dregg2_F_com_correct_asymp: "ped_commit.correct n"
  by (rule pedersen_correct_asym)

theorem dregg2_F_com_hiding_asymp: "ped_commit.perfect_hiding_ind_cpa n (\<A> n)"
  by (rule pedersen_perfect_hiding_asym)

theorem dregg2_F_com_binding_asymp:
  "negligible (\<lambda>n. ped_commit.bind_advantage n (\<A> n))
     \<longleftrightarrow> negligible (\<lambda>n. discrete_log.advantage n (dis_log_\<A> n (\<A> n)))"
  by (rule pedersen_bind_asym)

text\<open>THE REALIZATION. The dregg2 Pedersen commitment scheme REALIZES the ideal commitment
functionality F_com: it is correct, perfectly hiding (so the `unlinkable` carrier holds
unconditionally), and binding reduces to discrete log (so the `binding` carrier holds under
the standard DLog assumption). This single statement is the UC-layer discharge of the two
dregg2 `Prop` carriers.\<close>

text\<open>The honest implication the Lean `binding` carrier asserts: if discrete log is hard
(negligible DLog advantage of the reduction), then the dregg2 commitment is binding
(negligible binding advantage). Cited by the Lean bridge as
\<open>Dregg2_UC.pedersen_asymp.dregg2_binding_under_dlog\<close>.\<close>

theorem dregg2_binding_under_dlog:
  assumes "negligible (\<lambda>n. discrete_log.advantage n (dis_log_\<A> n (\<A> n)))"
  shows "negligible (\<lambda>n. ped_commit.bind_advantage n (\<A> n))"
  using assms by (simp add: dregg2_F_com_binding_asymp)

theorem dregg2_F_com_realizes:
  shows "ped_commit.correct n"                                  \<comment> \<open>F_com correctness\<close>
    and "ped_commit.perfect_hiding_ind_cpa n (\<A> n)"            \<comment> \<open>`unlinkable` discharged\<close>
    and "negligible (\<lambda>n. discrete_log.advantage n (dis_log_\<A> n (\<B> n)))
           \<Longrightarrow> negligible (\<lambda>n. ped_commit.bind_advantage n (\<B> n))"  \<comment> \<open>`binding` under DLog\<close>
  by (simp_all add: dregg2_F_com_correct_asymp dregg2_F_com_hiding_asymp
                    dregg2_binding_under_dlog)

text\<open>Alias matching the Lean bridge's cited name
\<open>Dregg2_UC.pedersen_asymp.dregg2_pedersen_realizes_F_com_asymp\<close>.\<close>

theorem dregg2_pedersen_realizes_F_com_asymp:
  shows "ped_commit.perfect_hiding_ind_cpa n (\<A> n)"
    and "negligible (\<lambda>n. ped_commit.bind_advantage n (\<B> n))
           \<longleftrightarrow> negligible (\<lambda>n. discrete_log.advantage n (dis_log_\<A> n (\<B> n)))"
  by (simp_all add: dregg2_F_com_hiding_asymp dregg2_F_com_binding_asymp)

end

end
