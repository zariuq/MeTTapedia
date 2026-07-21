import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EquivalenceLadder

/-!
# First-mismatch depth as a censored survival observation

Partial sequence agreement is represented by the first failed observation in
a bounded evaluator run.  If no failure is visible before the declared limit,
the observation is right-censored at that limit.  Reaching the censoring limit
means only that every observed term matched; it is not extensional program
equality.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping

/-- First failure before `limit`, or `limit` when the observation is censored. -/
noncomputable def firstMismatchDepth (limit : ℕ) (agrees : ℕ → Prop) : ℕ := by
  classical
  exact if h : ∃ i, i < limit ∧ ¬ agrees i then Nat.find h else limit

theorem firstMismatchDepth_le (limit : ℕ) (agrees : ℕ → Prop) :
    firstMismatchDepth limit agrees ≤ limit := by
  classical
  unfold firstMismatchDepth
  split_ifs with h
  · exact Nat.le_of_lt (Nat.find_spec h).1
  · exact le_rfl

theorem matches_before_firstMismatchDepth
    (limit : ℕ) (agrees : ℕ → Prop) {i : ℕ}
    (hi : i < firstMismatchDepth limit agrees) : agrees i := by
  classical
  unfold firstMismatchDepth at hi
  split_ifs at hi with h
  · by_contra hnot
    have hwitness : i < limit ∧ ¬ agrees i :=
      ⟨lt_trans hi (Nat.find_spec h).1, hnot⟩
    have hminimal := Nat.find_min' h hwitness
    exact (Nat.not_lt_of_ge hminimal) hi
  · by_contra hnot
    exact h ⟨i, hi, hnot⟩

theorem mismatch_at_firstMismatchDepth
    (limit : ℕ) (agrees : ℕ → Prop)
    (hdepth : firstMismatchDepth limit agrees < limit) :
    ¬ agrees (firstMismatchDepth limit agrees) := by
  classical
  unfold firstMismatchDepth at hdepth ⊢
  split_ifs at hdepth ⊢ with h
  · exact (Nat.find_spec h).2
  · omega

theorem firstMismatchDepth_eq_limit_iff
    (limit : ℕ) (agrees : ℕ → Prop) :
    firstMismatchDepth limit agrees = limit ↔
      ∀ i, i < limit → agrees i := by
  constructor
  · intro hdepth i hi
    apply matches_before_firstMismatchDepth limit agrees
    simpa [hdepth] using hi
  · intro hall
    exact le_antisymm (firstMismatchDepth_le limit agrees)
      (Nat.le_of_not_gt fun hlt ↦
        (mismatch_at_firstMismatchDepth limit agrees hlt)
          (hall _ hlt))

theorem firstMismatchDepth_eq_of_boundary
    (limit depth : ℕ) (agrees : ℕ → Prop)
    (hdepth : depth < limit)
    (hbefore : ∀ i, i < depth → agrees i)
    (hfail : ¬ agrees depth) :
    firstMismatchDepth limit agrees = depth := by
  apply le_antisymm
  · by_contra hnot
    have hlt : depth < firstMismatchDepth limit agrees :=
      Nat.lt_of_not_ge hnot
    exact hfail (matches_before_firstMismatchDepth limit agrees hlt)
  · by_contra hnot
    have hlt : firstMismatchDepth limit agrees < depth :=
      Nat.lt_of_not_ge hnot
    have hlimit : firstMismatchDepth limit agrees < limit := lt_trans hlt hdepth
    exact (mismatch_at_firstMismatchDepth limit agrees hlimit)
      (hbefore _ hlt)

theorem firstMismatchDepth_mono_limit
    {short long : ℕ} (agrees : ℕ → Prop) (hlimits : short ≤ long) :
    firstMismatchDepth short agrees ≤ firstMismatchDepth long agrees := by
  by_contra horder
  have hreverse : firstMismatchDepth long agrees <
      firstMismatchDepth short agrees := Nat.lt_of_not_ge horder
  have hlongLimit : firstMismatchDepth long agrees < long :=
    lt_of_lt_of_le
      (lt_of_lt_of_le hreverse (firstMismatchDepth_le short agrees)) hlimits
  exact (mismatch_at_firstMismatchDepth long agrees hlongLimit)
    (matches_before_firstMismatchDepth short agrees hreverse)

/-! ## Instantiation against the actual Gauthier E1 evaluator -/

namespace Gauthier

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT
open Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity

/-- The target term at index `i` matches when the evaluator emits that term.
Indices beyond the finite target impose no observation. -/
def matchesTargetAt (fuel : ℕ) (program : Prog) (target : List Int) (i : ℕ) : Prop :=
  ∀ value, listGet? target i = some value →
    EmitsAt orgE1Signature fuel program (Int.ofNat i) value

/-- Censored first-mismatch depth for a real E1 evaluation against a target. -/
noncomputable def firstMismatchDepth
    (fuel : ℕ) (program : Prog) (target : List Int) : ℕ :=
  SemanticShaping.firstMismatchDepth target.length
    (matchesTargetAt fuel program target)

private theorem listGet?_some_lt {values : List Int} {i : ℕ} {value : Int}
    (h : listGet? values i = some value) : i < values.length := by
  induction values generalizing i with
  | nil => simp [listGet?] at h
  | cons head tail ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [listGet?] at h
          simpa using ih h

theorem firstMismatchDepth_le_targetLength
    (fuel : ℕ) (program : Prog) (target : List Int) :
    firstMismatchDepth fuel program target ≤ target.length :=
  SemanticShaping.firstMismatchDepth_le _ _

/-- Surviving the complete finite target is exactly the evaluator's public
prefix predicate.  It remains a bounded observation, not extensionality. -/
theorem firstMismatchDepth_eq_length_iff_emitsPrefix
    (fuel : ℕ) (program : Prog) (target : List Int) :
    firstMismatchDepth fuel program target = target.length ↔
      EmitsPrefix orgE1Signature fuel program target := by
  rw [firstMismatchDepth, SemanticShaping.firstMismatchDepth_eq_limit_iff]
  constructor
  · intro hall i value hget
    exact hall i (listGet?_some_lt hget) value hget
  · intro hp i hi value hget
    exact hp i value hget

theorem probeId_survives_observed_term :
    firstMismatchDepth 20 probeId [0] = 1 := by
  apply (firstMismatchDepth_eq_length_iff_emitsPrefix
    20 probeId [0]).2
  exact probeId_emits_one_prefix

theorem probeZeroAfterZero_firstMismatch_is_one :
    firstMismatchDepth 20 probeZeroAfterZero [0, 1] = 1 := by
  apply SemanticShaping.firstMismatchDepth_eq_of_boundary 2 1
    (matchesTargetAt 20 probeZeroAfterZero [0, 1])
  · omega
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    intro value hget
    simp [listGet?] at hget
    subst value
    rw [emitsAt_iff]
    exact ⟨Store.zero, by
      simp [probeZeroAfterZero, Org.cond, Org.X, Org.z, eval,
        orgE1Signature, entryAt, listGet?, entry, seed]⟩
  · intro hmatch
    have hemits := hmatch 1 (by simp [listGet?])
    rw [emitsAt_iff] at hemits
    simp [probeZeroAfterZero, Org.cond, Org.X, Org.z, eval,
      orgE1Signature, entryAt, listGet?, entry, seed] at hemits

end Gauthier

#print axioms firstMismatchDepth_eq_limit_iff
#print axioms firstMismatchDepth_mono_limit
#print axioms Gauthier.firstMismatchDepth_eq_length_iff_emitsPrefix
#print axioms Gauthier.probeId_survives_observed_term
#print axioms Gauthier.probeZeroAfterZero_firstMismatch_is_one

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping
