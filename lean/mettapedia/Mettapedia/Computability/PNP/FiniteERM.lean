import Mettapedia.Computability.PNP.HypothesisClass
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.List.Count

/-!
# P vs NP background theory: finite-class empirical risk minimization

This file continues the optimistic grassroots route after `HypothesisClass.lean`.
Once a switched predictor family is shown to come from a small finite code space,
the next honest theorem is not yet a full statistical generalization bound.  It
is the finite combinatorial kernel behind empirical risk minimization (ERM):

* empirical error on a finite labeled sample,
* existence of an error-minimizing code in any nonempty finite encoded family,
* transfer of exact sample consistency through the ERM selector.

This is the clean learning-theoretic step that becomes available as soon as the
switched family is compressed into a finite hypothesis class.
-/

namespace Mettapedia.Computability.PNP

universe u v w

/-- One labeled example. -/
abbrev LabeledExample (Input : Type u) (Output : Type v) := Input × Output

/-- A finite training sample. -/
abbrev Sample (Input : Type u) (Output : Type v) := List (LabeledExample Input Output)

section Sample

variable {Input : Type u} {Output : Type v} [DecidableEq Output]

/-- Boolean predicate recording whether a predictor misclassifies one labeled example. -/
def misclassified (predict : Input → Output) (ex : LabeledExample Input Output) : Bool :=
  decide (predict ex.1 ≠ ex.2)

/-- Empirical classification error on a finite labeled sample. -/
def empiricalError (sample : Sample Input Output) (predict : Input → Output) : ℕ :=
  sample.countP (misclassified predict)

/-- Exact sample consistency: every labeled example is classified correctly. -/
def FitsSample (sample : Sample Input Output) (predict : Input → Output) : Prop :=
  ∀ ex ∈ sample, predict ex.1 = ex.2

@[simp] theorem empiricalError_nil (predict : Input → Output) :
    empiricalError ([] : Sample Input Output) predict = 0 := by
  simp [empiricalError]

@[simp] theorem empiricalError_cons (ex : LabeledExample Input Output)
    (sample : Sample Input Output) (predict : Input → Output) :
    empiricalError (ex :: sample) predict =
      empiricalError sample predict + if predict ex.1 ≠ ex.2 then 1 else 0 := by
  by_cases h : predict ex.1 = ex.2
  · simp [empiricalError, misclassified, h]
  · simp [empiricalError, misclassified, h]

theorem empiricalError_le_length (sample : Sample Input Output) (predict : Input → Output) :
    empiricalError sample predict ≤ sample.length := by
  simpa [empiricalError] using List.countP_le_length (p := misclassified predict) (l := sample)

@[simp] theorem empiricalError_append (sample₁ sample₂ : Sample Input Output)
    (predict : Input → Output) :
    empiricalError (sample₁ ++ sample₂) predict =
      empiricalError sample₁ predict + empiricalError sample₂ predict := by
  simp [empiricalError]

theorem fitsSample_iff_empiricalError_eq_zero (sample : Sample Input Output)
    (predict : Input → Output) :
    FitsSample sample predict ↔ empiricalError sample predict = 0 := by
  induction sample with
  | nil =>
      simp [FitsSample, empiricalError]
  | cons ex sample ih =>
      by_cases h : predict ex.1 = ex.2
      · simp [FitsSample, empiricalError, misclassified, h]
      · simp [FitsSample, empiricalError, misclassified, h]

end Sample

namespace EncodedFamily

section ERM

variable {Input : Type u} {Output : Type v}
variable [DecidableEq Output]
variable (H : EncodedFamily Input Output)

/-- Empirical error of one code in an encoded family. -/
def codeEmpiricalError [Nonempty H.Code] (sample : Sample Input Output) (c : H.Code) : ℕ :=
  empiricalError sample (H.decode c)

/-- Any nonempty finite encoded family contains a code minimizing empirical error. -/
theorem exists_empiricalRiskMinimizer [Nonempty H.Code] (sample : Sample Input Output) :
    ∃ c_star : H.Code, ∀ c, H.codeEmpiricalError sample c_star ≤ H.codeEmpiricalError sample c := by
  simpa [codeEmpiricalError] using
    (Finite.exists_min (α := H.Code) (β := ℕ)
      (f := fun c => empiricalError sample (H.decode c)))

/-- Choose one empirical-risk-minimizing code. -/
noncomputable def empiricalRiskMinimizer [Nonempty H.Code] (sample : Sample Input Output) :
    H.Code :=
  Classical.choose (H.exists_empiricalRiskMinimizer sample)

/-- The classifier realized by the chosen ERM code. -/
noncomputable def empiricalRiskPredictor [Nonempty H.Code] (sample : Sample Input Output) :
    Input → Output :=
  H.decode (H.empiricalRiskMinimizer sample)

theorem empiricalRiskMinimizer_spec [Nonempty H.Code] (sample : Sample Input Output) :
    ∀ c, H.codeEmpiricalError sample (H.empiricalRiskMinimizer sample) ≤
      H.codeEmpiricalError sample c :=
  Classical.choose_spec (H.exists_empiricalRiskMinimizer sample)

theorem empiricalRiskPredictor_mem_realized [Nonempty H.Code] (sample : Sample Input Output) :
    H.empiricalRiskPredictor sample ∈ realized H :=
  ⟨H.empiricalRiskMinimizer sample, rfl⟩

theorem empiricalRiskPredictor_le [Nonempty H.Code] (sample : Sample Input Output) (c : H.Code) :
    empiricalError sample (H.empiricalRiskPredictor sample) ≤ empiricalError sample (H.decode c) := by
  simpa [empiricalRiskPredictor, codeEmpiricalError] using
    H.empiricalRiskMinimizer_spec sample c

/-- If some code in the family fits the sample exactly, the chosen ERM predictor
also fits the sample exactly. -/
theorem empiricalRiskPredictor_zero_of_exists_zero [Nonempty H.Code]
    (sample : Sample Input Output)
    (hzero : ∃ c : H.Code, empiricalError sample (H.decode c) = 0) :
    empiricalError sample (H.empiricalRiskPredictor sample) = 0 := by
  rcases hzero with ⟨c, hc⟩
  have hmin : empiricalError sample (H.empiricalRiskPredictor sample) ≤
      empiricalError sample (H.decode c) :=
    H.empiricalRiskPredictor_le sample c
  have : empiricalError sample (H.empiricalRiskPredictor sample) ≤ 0 := by
    simpa [hc] using hmin
  exact Nat.eq_zero_of_le_zero this

theorem empiricalRiskPredictor_fitsSample_of_exists_code_fits [Nonempty H.Code]
    (sample : Sample Input Output)
    (hfit : ∃ c : H.Code, FitsSample sample (H.decode c)) :
    FitsSample sample (H.empiricalRiskPredictor sample) := by
  apply (fitsSample_iff_empiricalError_eq_zero sample (H.empiricalRiskPredictor sample)).2
  apply H.empiricalRiskPredictor_zero_of_exists_zero sample
  rcases hfit with ⟨c, hc⟩
  exact ⟨c, (fitsSample_iff_empiricalError_eq_zero sample (H.decode c)).1 hc⟩

/-- Realized-set form of ERM existence: the realized hypothesis class contains
an empirical-error minimizer. -/
theorem exists_realized_empiricalRiskMinimizer [Nonempty H.Code]
    (sample : Sample Input Output) :
    ∃ predict ∈ realized H,
      ∀ g ∈ realized H, empiricalError sample predict ≤ empiricalError sample g := by
  refine ⟨H.empiricalRiskPredictor sample, H.empiricalRiskPredictor_mem_realized sample, ?_⟩
  intro g hg
  rcases hg with ⟨c, rfl⟩
  exact H.empiricalRiskPredictor_le sample c

end ERM

end EncodedFamily

end Mettapedia.Computability.PNP
