import Mettapedia.Computability.PNP.FiniteERM
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Basic

/-!
# P vs NP background theory: finite consistency bounds

This file extends the finite ERM layer with a fully combinatorial counting bound.
Rather than introducing measure theory immediately, we count the number of length-`m`
input samples on which a wrong predictor can still look perfectly consistent with
the target labels.

The resulting theorem is the finite-domain uniform-sampling skeleton behind a
future finite-class generalization bound:

* a wrong predictor fits at most exponentially few samples,
* a finite encoded family therefore has only exponentially few deceptive samples,
* if the target function is realized by the family, then ERM recovers the target
  on every non-deceptive sample.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u v

/-- A length-`m` input sample, viewed as a function on `Fin m`. -/
abbrev PointSample (Input : Type u) (m : ℕ) := Fin m → Input

section SampleConsistency

variable {Input : Type u} {Output : Type v}

/-- A predictor agrees with the target on a point sample if every sampled input is
labeled the same way. -/
def AgreesWithTarget (target predict : Input → Output) {m : ℕ}
    (sample : PointSample Input m) : Prop :=
  ∀ i, predict (sample i) = target (sample i)

/-- The subtype of points where `predict` and `target` agree. -/
abbrev AgreementPoints (target predict : Input → Output) :=
  { x : Input // predict x = target x }

/-- The subtype of length-`m` point samples on which `predict` agrees with `target`. -/
abbrev ConsistentSamples (target predict : Input → Output) (m : ℕ) :=
  { sample : PointSample Input m // AgreesWithTarget target predict sample }

noncomputable instance agreementPointsFintype
    [Fintype Input] [DecidableEq Output]
    (target predict : Input → Output) :
    Fintype (AgreementPoints target predict) :=
  Fintype.ofFinite _

noncomputable instance consistentSamplesFintype
    [Fintype Input] [DecidableEq Output]
    (target predict : Input → Output) (m : ℕ) :
    Fintype (ConsistentSamples target predict m) :=
  Fintype.ofFinite _

noncomputable def consistentSamplesEquivAgreementFunctions
    (target predict : Input → Output) (m : ℕ) :
    ConsistentSamples target predict m ≃ (Fin m → AgreementPoints target predict) :=
  Equiv.subtypePiEquivPi
    (β := fun _ : Fin m => Input)
    (p := fun _ x => predict x = target x)

theorem card_consistentSamples_eq
    [Fintype Input] [DecidableEq Output]
    (target predict : Input → Output) (m : ℕ) :
    Fintype.card (ConsistentSamples target predict m) =
      Fintype.card (AgreementPoints target predict) ^ m := by
  classical
  calc
    Fintype.card (ConsistentSamples target predict m)
      = Fintype.card (Fin m → AgreementPoints target predict) := by
          exact Fintype.card_congr (consistentSamplesEquivAgreementFunctions target predict m)
    _ = Fintype.card (AgreementPoints target predict) ^ m := by
      simp

theorem card_consistentSamples_le_of_exists_disagreement
    [Fintype Input] [DecidableEq Output]
    (target predict : Input → Output) {m : ℕ}
    (hneq : ∃ x, predict x ≠ target x) :
    Fintype.card (ConsistentSamples target predict m) ≤
      (Fintype.card Input - 1) ^ m := by
  classical
  rcases hneq with ⟨x, hx⟩
  have hlt : Fintype.card (AgreementPoints target predict) < Fintype.card Input := by
    simpa [AgreementPoints] using
      (Fintype.card_subtype_lt (α := Input) (p := fun y => predict y = target y) hx)
  have hle : Fintype.card (AgreementPoints target predict) ≤ Fintype.card Input - 1 :=
    Nat.le_sub_one_of_lt hlt
  calc
    Fintype.card (ConsistentSamples target predict m)
      = Fintype.card (AgreementPoints target predict) ^ m :=
        card_consistentSamples_eq target predict m
    _ ≤ (Fintype.card Input - 1) ^ m := Nat.pow_le_pow_left hle m

/-- Label a point sample using the target function, producing the finite ERM sample
format from `FiniteERM.lean`. -/
def labeledByTarget (target : Input → Output) {m : ℕ}
    (sample : PointSample Input m) : Sample Input Output :=
  List.ofFn fun i => (sample i, target (sample i))

theorem fitsSample_labeledByTarget_iff
    [DecidableEq Output]
    (target predict : Input → Output) {m : ℕ} (sample : PointSample Input m) :
    FitsSample (labeledByTarget target sample) predict ↔
      AgreesWithTarget target predict sample := by
  constructor
  · intro h i
    exact h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h ex hex
    rcases List.mem_ofFn.mp hex with ⟨i, rfl⟩
    exact h i

end SampleConsistency

namespace EncodedFamily

section FiniteBound

variable {Input : Type u} {Output : Type v}
variable [Fintype Input] [DecidableEq Output]
variable (H : EncodedFamily Input Output)

/-- The bad codes are those whose decoded predictor is not the target function. -/
abbrev BadCodes (target : Input → Output) := { c : H.Code // H.decode c ≠ target }

/-- A point sample is deceptive for `target` if some bad code agrees with all
target labels on that sample. -/
def IsDeceptiveSample (target : Input → Output) {m : ℕ}
    (sample : PointSample Input m) : Prop :=
  ∃ c : H.Code, H.decode c ≠ target ∧ AgreesWithTarget target (H.decode c) sample

/-- The subtype of deceptive point samples. -/
abbrev DeceptiveSamples (target : Input → Output) (m : ℕ) :=
  { sample : PointSample Input m // H.IsDeceptiveSample target sample }

/-- Witnessed deceptive samples keep both the bad code and the consistent sample. -/
abbrev DeceptiveWitnesses (target : Input → Output) (m : ℕ) :=
  Sigma fun c : H.BadCodes target => ConsistentSamples target (H.decode c.1) m

noncomputable instance badCodesFintype (target : Input → Output) :
    Fintype (H.BadCodes target) :=
  Fintype.ofFinite _

noncomputable instance deceptiveSamplesFintype (target : Input → Output) (m : ℕ) :
    Fintype (H.DeceptiveSamples target m) :=
  Fintype.ofFinite _

noncomputable def deceptiveWitnessToSample
    (target : Input → Output) {m : ℕ} :
    H.DeceptiveWitnesses target m → H.DeceptiveSamples target m
  | ⟨c, sample⟩ => ⟨sample.1, ⟨c.1, c.2, sample.2⟩⟩

omit [Fintype Input] [DecidableEq Output] in
theorem deceptiveWitnessToSample_surjective
    (target : Input → Output) {m : ℕ} :
    Function.Surjective (H.deceptiveWitnessToSample target (m := m)) := by
  intro sample
  rcases sample.2 with ⟨c, hc, hs⟩
  exact ⟨⟨⟨c, hc⟩, ⟨sample.1, hs⟩⟩, Subtype.ext rfl⟩

theorem card_deceptiveWitnesses_le
    (target : Input → Output) (m : ℕ) :
    Fintype.card (H.DeceptiveWitnesses target m) ≤
      Fintype.card (H.BadCodes target) * (Fintype.card Input - 1) ^ m := by
  classical
  calc
    Fintype.card (H.DeceptiveWitnesses target m)
      = ∑ c : H.BadCodes target,
          Fintype.card (ConsistentSamples target (H.decode c.1) m) := by
            change
              Fintype.card (Sigma fun c : H.BadCodes target =>
                ConsistentSamples target (H.decode c.1) m) =
                ∑ c : H.BadCodes target,
                  Fintype.card (ConsistentSamples target (H.decode c.1) m)
            exact
              (Fintype.card_sigma :
                Fintype.card (Sigma fun c : H.BadCodes target =>
                  ConsistentSamples target (H.decode c.1) m) =
                  ∑ c : H.BadCodes target,
                    Fintype.card (ConsistentSamples target (H.decode c.1) m))
    _ ≤ ∑ c : H.BadCodes target, (Fintype.card Input - 1) ^ m := by
      refine Finset.sum_le_sum ?_
      intro c _
      have hneq : ∃ x, H.decode c.1 x ≠ target x := by
        by_contra h
        push_neg at h
        exact c.2 (funext h)
      exact card_consistentSamples_le_of_exists_disagreement target (H.decode c.1) hneq
    _ = Fintype.card (H.BadCodes target) * (Fintype.card Input - 1) ^ m := by
      simp

theorem card_deceptiveSamples_le
    (target : Input → Output) (m : ℕ) :
    Fintype.card (H.DeceptiveSamples target m) ≤
      Fintype.card H.Code * (Fintype.card Input - 1) ^ m := by
  have hsurj := H.deceptiveWitnessToSample_surjective target (m := m)
  have hwitness :
      Fintype.card (H.DeceptiveSamples target m) ≤
        Fintype.card (H.DeceptiveWitnesses target m) :=
    Fintype.card_le_of_surjective _ hsurj
  have hbad :
      Fintype.card (H.BadCodes target) ≤ Fintype.card H.Code :=
    Fintype.card_subtype_le (fun c : H.Code => H.decode c ≠ target)
  exact le_trans hwitness <|
    le_trans (H.card_deceptiveWitnesses_le target m) <|
      Nat.mul_le_mul_right ((Fintype.card Input - 1) ^ m) hbad

theorem empiricalRiskPredictor_eq_target_of_not_deceptive
    [Nonempty H.Code]
    (target : Input → Output) {m : ℕ} (sample : PointSample Input m)
    (htarget : ∃ c : H.Code, H.decode c = target)
    (hnot : ¬ H.IsDeceptiveSample target sample) :
    H.empiricalRiskPredictor (labeledByTarget target sample) = target := by
  have hfitTarget : ∃ c : H.Code, FitsSample (labeledByTarget target sample) (H.decode c) := by
    rcases htarget with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [hc] using
      (fitsSample_labeledByTarget_iff target target sample).2 (fun _ => rfl)
  have hfitERM :
      FitsSample (labeledByTarget target sample)
        (H.empiricalRiskPredictor (labeledByTarget target sample)) :=
    H.empiricalRiskPredictor_fitsSample_of_exists_code_fits
      (sample := labeledByTarget target sample) hfitTarget
  have hagreeERM :
      AgreesWithTarget target (H.empiricalRiskPredictor (labeledByTarget target sample)) sample :=
    (fitsSample_labeledByTarget_iff target
      (H.empiricalRiskPredictor (labeledByTarget target sample)) sample).1 hfitERM
  by_contra hneq
  exact hnot ⟨H.empiricalRiskMinimizer (labeledByTarget target sample), hneq, hagreeERM⟩

end FiniteBound

end EncodedFamily

end Mettapedia.Computability.PNP
