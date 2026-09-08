import Mettapedia.Cybernetics.DistinctionCalculus.ProofSystem

/-!
# Finite input admission and proof-carrying metric completion

Both the seed matrix and a proposed completion are finite rational data.
Admission checks the observer laws. Completion checking checks coherence,
extension of the seed, and one path certificate for each proposed distance.
The last condition proves minimality, not merely feasibility: an accepted
candidate is the least metric similarity extending the seed.

The producer is deliberately unspecified. This module verifies proposed
completions; it does not yet prove termination or completeness of a shortest
path generator. A different producer can use the same checking interface.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u

variable {V : Type u}

def ValidSimilarity (matrix : V → V → ℚ) : Prop :=
  (∀ x y, 0 ≤ matrix x y) ∧ (∀ x y, matrix x y ≤ 1) ∧
  (∀ x, matrix x x = 1) ∧ (∀ x y, matrix x y = matrix y x)

instance [Fintype V] (matrix : V → V → ℚ) : Decidable (ValidSimilarity matrix) := by
  unfold ValidSimilarity
  infer_instance

def admit [Fintype V] (matrix : V → V → ℚ) : Option (Tolerance V) :=
  if h : ValidSimilarity matrix then
    some ⟨matrix, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else none

theorem admit_iff [Fintype V] (matrix : V → V → ℚ) :
    (∃ observer, admit matrix = some observer) ↔ ValidSimilarity matrix := by
  unfold admit
  split_ifs with h <;> simp [h]

theorem admit_similarity [Fintype V] {matrix : V → V → ℚ} {observer : Tolerance V}
    (accepted : admit matrix = some observer) : observer.similarity = matrix := by
  unfold admit at accepted
  split_ifs at accepted with valid
  · cases Option.some.inj accepted
    rfl

@[simp] theorem admit_tolerance [Fintype V] (a : Tolerance V) :
    admit a.similarity = some a := by
  have valid : ValidSimilarity a.similarity :=
    ⟨a.nonnegative, a.bounded, a.reflexive, a.symmetric⟩
  simp only [admit, dif_pos valid]

instance [Fintype V] (a : Tolerance V) : Decidable a.Metric := by
  unfold Tolerance.Metric
  infer_instance

instance [Fintype V] (a b : Tolerance V) : Decidable (a.Extends b) := by
  unfold Tolerance.Extends
  infer_instance

/-- A universal property independent of the checking algorithm. -/
def LeastMetricExtension (base candidate : Tolerance V) : Prop :=
  base.Extends candidate ∧ candidate.Metric ∧
    ∀ other : Tolerance V, base.Extends other → other.Metric → candidate.Extends other

/-- The semantic model class is never empty. This upper bound is not claimed
to be the least completion; graded controls explicitly refute that shortcut. -/
theorem exists_metric_extension (base : Tolerance V) :
    ∃ model : Tolerance V, base.Extends model ∧ model.Metric := by
  refine ⟨Tolerance.ofReport (fun _ : V => false), ?_, Tolerance.ofReport_metric _⟩
  intro x y
  simpa [Tolerance.ofReport] using base.bounded x y

/-- Finite, total validation of a proposed completion and its path witnesses. -/
def completionCheck [Fintype V] [DecidableEq V] (base candidate : Tolerance V)
    (paths : V → V → Certificate V) : Bool :=
  decide (base.Extends candidate ∧ candidate.Metric ∧
    ∀ x y, check base ⟨x, y, candidate.distance x y⟩ (paths x y) = true)

theorem completionCheck_sound [Fintype V] [DecidableEq V]
    {base candidate : Tolerance V} {paths : V → V → Certificate V}
    (accepted : completionCheck base candidate paths = true) :
    LeastMetricExtension base candidate := by
  obtain ⟨extendsSeed, metric, checked⟩ := of_decide_eq_true accepted
  refine ⟨extendsSeed, metric, ?_⟩
  intro other hExt otherMetric x y
  have bound := check_sound (checked x y) other otherMetric hExt
  dsimp [Tolerance.distance] at bound
  linarith

theorem leastMetricExtension_unique {base first second : Tolerance V}
    (left : LeastMetricExtension base first) (right : LeastMetricExtension base second) :
    first.similarity = second.similarity := by
  funext x y
  exact le_antisymm (left.2.2 second right.1 right.2.1 x y)
    (right.2.2 first left.1 left.2.1 x y)

/-- A coherent seed is its own least completion. -/
theorem metric_leastMetricExtension (base : Tolerance V) (metric : base.Metric) :
    LeastMetricExtension base base :=
  ⟨fun _ _ => le_rfl, metric, fun _ hExt _ => hExt⟩

/-- Accepted completion cannot change a seed that was already coherent. -/
theorem completionCheck_fixed [Fintype V] [DecidableEq V]
    {base candidate : Tolerance V} {paths : V → V → Certificate V}
    (metric : base.Metric) (accepted : completionCheck base candidate paths = true) :
    candidate.similarity = base.similarity :=
  leastMetricExtension_unique (completionCheck_sound accepted)
    (metric_leastMetricExtension base metric)

/-- The raw interface admits matrices before checking the proposed completion. -/
def checkRawCompletion [Fintype V] [DecidableEq V]
    (seed candidate : V → V → ℚ) (paths : V → V → Certificate V) : Bool :=
  match admit seed, admit candidate with
  | some base, some model => completionCheck base model paths
  | _, _ => false

theorem checkRawCompletion_sound [Fintype V] [DecidableEq V]
    {seed candidate : V → V → ℚ} {paths : V → V → Certificate V}
    (accepted : checkRawCompletion seed candidate paths = true) :
    ∃ base model : Tolerance V, base.similarity = seed ∧ model.similarity = candidate ∧
      LeastMetricExtension base model := by
  cases hBase : admit seed with
  | none => simp [checkRawCompletion, hBase] at accepted
  | some base =>
      cases hModel : admit candidate with
      | none => simp [checkRawCompletion, hBase, hModel] at accepted
      | some model =>
          exact ⟨base, model, admit_similarity hBase, admit_similarity hModel,
            completionCheck_sound (by simpa [checkRawCompletion, hBase, hModel] using accepted)⟩

end Mettapedia.Cybernetics.DistinctionCalculus
