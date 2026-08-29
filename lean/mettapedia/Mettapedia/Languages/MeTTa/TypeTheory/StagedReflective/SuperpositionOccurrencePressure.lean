import Mettapedia.Cybernetics.MultiscaleGoal
import Mettapedia.Languages.MeTTa.TypeTheory.StagedReflective.Presentation

/-!
# Occurrence pressure on staged-reflective superposition typing

The staged-reflective candidate currently gives a binary superposition the
same type as each branch.  This module records the exact consequence without
prescribing a replacement syntax.

The single term `u0` and the duplicated term `superpose u0 u0` are distinct
raw programs, and both are derivably typed as `u1`.  Therefore a policy which
observes only their current result type cannot represent the goal "this term
contains the duplicated occurrence".  An occurrence-count observation can.

This is a pressure theorem, not a declaration that the surface type must be
`Bag A`.  A bag type, a multiplicity effect, or an external proof-relevant
occurrence fibre could all satisfy the demonstrated requirement.  What is
ruled out is relying on the current branch type alone wherever multiplicity
is semantically observable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StagedReflective.SuperpositionOccurrencePressure

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal

/-- The smallest comparison separating one occurrence from a duplicated
superposition. -/
inductive BranchShape where
  | single
  | duplicated
  deriving DecidableEq

/-- Concrete terms in the live staged-reflective raw syntax. -/
def term : BranchShape -> StagedReflectiveTm 0 0
  | .single => .u0
  | .duplicated => .superpose .u0 .u0

/-- The current typing rule assigns both terms the same result type. -/
def inferredType (_ : BranchShape) : StagedReflectiveTm 0 0 := .u1

/-- Both observations are accepted by the actual authored typing judgment. -/
theorem inferredType_sound : forall shape,
    NativeModalTyping.HasType NativeModalTyping.syntacticConversion .nil
      (term shape) (inferredType shape) := by
  intro shape
  cases shape with
  | single =>
      exact NativeModalTyping.HasType.u0_type .nil
  | duplicated =>
      exact NativeModalTyping.HasType.superpose_intro
        (NativeModalTyping.HasType.u0_type .nil)
        (NativeModalTyping.HasType.u0_type .nil)

/-- Typability does not identify the raw programs. -/
theorem single_ne_duplicated : Not (term .single = term .duplicated) := by
  simp [term]

/-- The complete current witness: distinct raw programs, one inferred type,
and derivations for both. -/
theorem current_rule_forgets_duplication :
    Nonempty (NativeModalTyping.HasType
      NativeModalTyping.syntacticConversion .nil (term .single) .u1) /\
    Nonempty (NativeModalTyping.HasType
      NativeModalTyping.syntacticConversion .nil (term .duplicated) .u1) /\
    Not (term .single = term .duplicated) := by
  exact ⟨⟨inferredType_sound .single⟩,
    ⟨inferredType_sound .duplicated⟩, single_ne_duplicated⟩

/-- The type-only observer exposes exactly the readout justified above. -/
def typeObserver : Observer BranchShape (StagedReflectiveTm 0 0) where
  observe := inferredType

/-- The occurrence-sensitive goal selected for the pressure test. -/
def duplicationProblem : ProblemSpace BranchShape where
  preferredRegion := {shape | shape = .duplicated}

/-- The current result type cannot express the duplicated-occurrence goal. -/
theorem duplication_not_visible_to_current_type :
    Not (duplicationProblem.GoalVisibleAt typeObserver) := by
  intro visible
  have invariant :=
    (duplicationProblem.goalVisibleAt_iff_invariantOnFibres typeObserver).mp visible
  have contradiction := invariant .single .duplicated rfl
  simp [duplicationProblem] at contradiction

/-- One possible richer observation retains branch occurrence count.  It is
used only to prove satisfiability of the requirement, not to select the final
type-theory presentation. -/
def occurrenceCount : BranchShape -> Nat
  | .single => 1
  | .duplicated => 2

def occurrenceObserver : Observer BranchShape Nat where
  observe := occurrenceCount

/-- An occurrence-aware layer can represent the same goal exactly. -/
theorem duplication_visible_to_occurrence_count :
    duplicationProblem.GoalVisibleAt occurrenceObserver := by
  refine ⟨{count | count = 2}, ?_⟩
  intro shape
  cases shape <;> simp [duplicationProblem, occurrenceObserver, occurrenceCount]

/-- Consequently the type-only observation is strictly coarser on this
fragment than the occurrence-aware observation. -/
theorem occurrence_distinguishes_where_type_does_not :
    typeObserver.observe .single = typeObserver.observe .duplicated /\
      occurrenceObserver.Distinguishes .single .duplicated := by
  constructor
  · rfl
  · simp [Observer.Distinguishes, occurrenceObserver, occurrenceCount]

end Mettapedia.Languages.MeTTa.StagedReflective.SuperpositionOccurrencePressure

#print axioms Mettapedia.Languages.MeTTa.StagedReflective.SuperpositionOccurrencePressure.inferredType_sound
#print axioms Mettapedia.Languages.MeTTa.StagedReflective.SuperpositionOccurrencePressure.current_rule_forgets_duplication
#print axioms Mettapedia.Languages.MeTTa.StagedReflective.SuperpositionOccurrencePressure.duplication_not_visible_to_current_type
#print axioms Mettapedia.Languages.MeTTa.StagedReflective.SuperpositionOccurrencePressure.duplication_visible_to_occurrence_count
