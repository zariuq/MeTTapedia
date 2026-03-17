import Mettapedia.Logic.PLNFirstOrder.Soundness
import Mettapedia.Logic.PLNIndefiniteTruth

/-!
# PLN First-Order Quantifier Canary Suite

Regression-style canaries for the finite-domain PLN quantifier layer.

## Literature Alignment (local corpus)

- PLN Book, Ch.11:
  - `ThereExists x F(x) ≡ ¬ ForAll x ¬F(x)` (De Morgan / quantifier duality).
  - Existential generalization and universal specification as core manipulations.
- This module encodes those as theorem-level canaries over current Lean semantics.

We include both positive and negative canaries:
- positive: laws that should always hold in the current semantics;
- negative: formulas that should *not* be assumed in the `isTrue`-filtered setting.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNQuantaleSemantics.PBit
open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.Logic.PLNIndefiniteTruth

section LiteratureCanaries

variable {U : Type*} [Fintype U]

/-- Ch.11 canary: existential quantifier is the De Morgan dual of universal quantifier. -/
theorem canary_ch11_exists_deMorgan
    (S : SatisfyingSet U) (μ : WeightFunction U BinaryEvidence) :
    thereExistsEval S μ = BinaryEvidence.compl (forAllEval (SatisfyingSet.neg S) μ) := by
  simp [thereExistsEval_deMorgan]

/-- Ch.11 quantifier-exchange canary (primary De Morgan form). -/
theorem canary_ch11_quantifier_exchange
    (S : SatisfyingSet U) (μ : WeightFunction U BinaryEvidence) :
    thereExistsEval S μ = BinaryEvidence.compl (forAllEval (SatisfyingSet.neg S) μ) :=
  canary_ch11_exists_deMorgan S μ

/-- Ch.11 canary (extensional view): existential generalization.

`F(c) ≤ ∃x.F(x)` for any witness `c`. -/
theorem canary_ch11_existential_generalization_ext
    (S : SatisfyingSet U) (c : U) :
    S.pred c ≤ thereExistsEvalExt S := by
  unfold thereExistsEvalExt
  exact le_sSup ⟨c, rfl⟩

/-- Ch.11 canary (extensional view): universal specification.

`∀x.F(x) ≤ F(c)` for any instance `c`. -/
theorem canary_ch11_universal_specification_ext
    (S : SatisfyingSet U) (c : U) :
    forAllEvalExt S ≤ S.pred c := by
  unfold forAllEvalExt
  exact sInf_le ⟨c, rfl⟩

/-- Ch.11 rule-family canary bundle (core extensional path).

Packages existential generalization + universal specification + exchange in one theorem. -/
theorem canary_ch11_rule_family_end_to_end_ext
    (S : SatisfyingSet U) (μ : WeightFunction U BinaryEvidence) (c : U) :
    (thereExistsEval S μ = BinaryEvidence.compl (forAllEval (SatisfyingSet.neg S) μ)) ∧
      (S.pred c ≤ thereExistsEvalExt S) ∧
      (forAllEvalExt S ≤ S.pred c) := by
  refine ⟨canary_ch11_quantifier_exchange S μ, ?_, ?_⟩
  · exact canary_ch11_existential_generalization_ext S c
  · exact canary_ch11_universal_specification_ext S c

/-- Nonempty-domain extensional ordering canary: `∀ ≤ ∃`. -/
theorem canary_extensional_forall_le_exists
    [Nonempty U] (S : SatisfyingSet U) :
    forAllEvalExt S ≤ thereExistsEvalExt S :=
  forAllEvalExt_le_thereExistsEvalExt (S := S)

/-- Empty-domain vacuity canary for extensional universal quantifier. -/
theorem canary_empty_domain_forall_ext
    [IsEmpty U] (S : SatisfyingSet U) :
    forAllEvalExt S = ⊤ :=
  forAllEvalExt_eq_top_of_isEmpty (S := S)

/-- Empty-domain vacuity canary for extensional existential quantifier. -/
theorem canary_empty_domain_exists_ext
    [IsEmpty U] (S : SatisfyingSet U) :
    thereExistsEvalExt S = ⊥ :=
  thereExistsEvalExt_eq_bot_of_isEmpty (S := S)

end LiteratureCanaries

section ConcreteFixtures

/-- Concrete Bool fixture with one classical-true and one contradictory witness. -/
def boolFixtureMixed : SatisfyingSet Bool :=
  ⟨fun b => if b then (⟨1, 0⟩ : BinaryEvidence) else (⟨0, 1⟩ : BinaryEvidence)⟩

/-- Concrete Fin 2 fixture with a constant evidence value. -/
def fin2FixtureConst : SatisfyingSet (Fin 2) :=
  ⟨fun _ => (⟨2, 0⟩ : BinaryEvidence)⟩

/-- Bool fixture canary: extensional universal quantifier evaluates to `⟨0,0⟩`. -/
theorem canary_fixture_bool_mixed_forall_ext :
    forAllEvalExt boolFixtureMixed = (⟨0, 0⟩ : BinaryEvidence) := by
  have hset :
      ({ e : BinaryEvidence | ∃ u : Bool, e = boolFixtureMixed.pred u } : Set BinaryEvidence) =
        ({ (⟨1, 0⟩ : BinaryEvidence), (⟨0, 1⟩ : BinaryEvidence) } : Set BinaryEvidence) := by
    ext e
    constructor
    · intro h
      rcases h with ⟨u, rfl⟩
      cases u <;> simp [boolFixtureMixed]
    · intro h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · refine ⟨true, ?_⟩
        simpa [boolFixtureMixed] using h
      · refine ⟨false, ?_⟩
        simpa [boolFixtureMixed] using h
  unfold forAllEvalExt
  rw [hset, sInf_pair]
  show BinaryEvidence.inf (⟨1, 0⟩ : BinaryEvidence) (⟨0, 1⟩ : BinaryEvidence) = (⟨0, 0⟩ : BinaryEvidence)
  unfold BinaryEvidence.inf
  apply BinaryEvidence.ext'
  · simp
  · simp

/-- Bool fixture canary: extensional existential quantifier evaluates to `⟨1,1⟩`. -/
theorem canary_fixture_bool_mixed_exists_ext :
    thereExistsEvalExt boolFixtureMixed = (⟨1, 1⟩ : BinaryEvidence) := by
  have hset :
      ({ e : BinaryEvidence | ∃ u : Bool, e = boolFixtureMixed.pred u } : Set BinaryEvidence) =
        ({ (⟨1, 0⟩ : BinaryEvidence), (⟨0, 1⟩ : BinaryEvidence) } : Set BinaryEvidence) := by
    ext e
    constructor
    · intro h
      rcases h with ⟨u, rfl⟩
      cases u <;> simp [boolFixtureMixed]
    · intro h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · refine ⟨true, ?_⟩
        simpa [boolFixtureMixed] using h
      · refine ⟨false, ?_⟩
        simpa [boolFixtureMixed] using h
  unfold thereExistsEvalExt
  rw [hset, sSup_pair]
  show BinaryEvidence.sup (⟨1, 0⟩ : BinaryEvidence) (⟨0, 1⟩ : BinaryEvidence) = (⟨1, 1⟩ : BinaryEvidence)
  unfold BinaryEvidence.sup
  apply BinaryEvidence.ext'
  · simp
  · simp

/-- Fin-2 constant fixture canary: extensional ∀ and ∃ both evaluate to the constant. -/
theorem canary_fixture_fin2_const_ext :
    forAllEvalExt fin2FixtureConst = (⟨2, 0⟩ : BinaryEvidence) ∧
      thereExistsEvalExt fin2FixtureConst = (⟨2, 0⟩ : BinaryEvidence) := by
  have hset :
      ({ e : BinaryEvidence | ∃ u : Fin 2, e = fin2FixtureConst.pred u } : Set BinaryEvidence) =
        ({ (⟨2, 0⟩ : BinaryEvidence) } : Set BinaryEvidence) := by
    ext e
    constructor
    · intro h
      rcases h with ⟨u, rfl⟩
      simp [fin2FixtureConst]
    · intro h
      simp only [Set.mem_singleton_iff] at h
      refine ⟨0, ?_⟩
      simpa [fin2FixtureConst] using h
  constructor
  · unfold forAllEvalExt
    rw [hset, sInf_singleton]
  · unfold thereExistsEvalExt
    rw [hset, sSup_singleton]

/-- Ch.11 regression canary: extensional `∀` and `∃` are not equivalent on mixed evidence. -/
theorem canary_ch11_non_equivalence_extensional_bool_mixed :
    forAllEvalExt boolFixtureMixed ≠ thereExistsEvalExt boolFixtureMixed := by
  intro hEq
  have h0 : (⟨0, 0⟩ : BinaryEvidence) = (⟨1, 1⟩ : BinaryEvidence) := by
    rw [← canary_fixture_bool_mixed_forall_ext, ← canary_fixture_bool_mixed_exists_ext]
    exact hEq
  have hpos : (0 : ENNReal) = 1 := by
    simpa using congrArg BinaryEvidence.pos h0
  exact zero_ne_one hpos

/-- Ch.11 regression canary in the ITV layer (Walley semantics):
quantifier non-equivalence persists after BinaryEvidence→ITV mapping. -/
theorem canary_ch11_non_equivalence_itv_walley_bool_mixed
    (s : ℝ) (hs : 0 < s) :
    forAllEvalExt boolFixtureMixed ≠ thereExistsEvalExt boolFixtureMixed ∧
      (ITV.fromWalleyIDMPredictive (forAllEvalExt boolFixtureMixed) s hs).credibility <
        (ITV.fromWalleyIDMPredictive (thereExistsEvalExt boolFixtureMixed) s hs).credibility := by
  constructor
  · exact canary_ch11_non_equivalence_extensional_bool_mixed
  · rw [canary_fixture_bool_mixed_forall_ext, canary_fixture_bool_mixed_exists_ext]
    have hs2 : 0 < (2 : ℝ) + s := by linarith
    have hpos : 0 < (2 : ℝ) / ((2 : ℝ) + s) := by
      exact div_pos (by norm_num) hs2
    have hleft :
        (ITV.fromWalleyIDMPredictive (⟨0, 0⟩ : BinaryEvidence) s hs).credibility = 0 := by
      simp [ITV.fromWalleyIDMPredictive_credibility]
    have hright :
        (ITV.fromWalleyIDMPredictive (⟨1, 1⟩ : BinaryEvidence) s hs).credibility =
          (2 : ℝ) / ((2 : ℝ) + s) := by
      simp [ITV.fromWalleyIDMPredictive_credibility]
      norm_num
    rw [hleft, hright]
    exact hpos

end ConcreteFixtures

section NegativeCanaries

/-- Negative canary: `isTrue` is not meet-preserving in BinaryEvidence.

This blocks naive classical-distributive rewrites in the `isTrue`-filtered quantifier semantics. -/
theorem canary_not_isTrue_meet_preserving :
    ¬ (∀ e₁ e₂ : BinaryEvidence,
      isTrue (e₁ ⊓ e₂) → (isTrue e₁ ∧ isTrue e₂)) := by
  intro h
  rcases isTrue_meet_not_implies_both with ⟨e₁, e₂, hmeet, hnot⟩
  exact hnot (h e₁ e₂ hmeet)

/-- Negative canary with explicit witness pair used in Soundness.lean. -/
theorem canary_isTrue_meet_counterexample_witness :
    isTrue ((⟨1, 0⟩ : BinaryEvidence) ⊓ (⟨1, 1⟩ : BinaryEvidence)) ∧
      ¬ (isTrue (⟨1, 0⟩ : BinaryEvidence) ∧ isTrue (⟨1, 1⟩ : BinaryEvidence)) := by
  have h_meet : ((⟨1, 0⟩ : BinaryEvidence) ⊓ (⟨1, 1⟩ : BinaryEvidence)) = (⟨1, 0⟩ : BinaryEvidence) := by
    show BinaryEvidence.inf (⟨1, 0⟩ : BinaryEvidence) (⟨1, 1⟩ : BinaryEvidence) = (⟨1, 0⟩ : BinaryEvidence)
    unfold BinaryEvidence.inf
    apply BinaryEvidence.ext'
    · simp
    · simp
  constructor
  · rw [h_meet]
    exact ⟨zero_lt_one, rfl⟩
  · intro h
    exact one_ne_zero h.2.2

end NegativeCanaries

end Mettapedia.Logic.PLNFirstOrder
