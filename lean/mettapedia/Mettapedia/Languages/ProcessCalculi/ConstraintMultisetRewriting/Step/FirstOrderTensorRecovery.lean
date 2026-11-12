import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderNativeRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence

/-!
# Recovery of the existing first-order tensor by actual native runs

The established separated-schedule theorem constructs an execution in the
shared Step interface, with the complete original firing word and a transport
isomorphism of endpoints. Raw identities keep their larger empty domain;
requiring consistent execution recovers exactly the old definedness theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns

open AnnotatedRuns (Firing firstOrder firstOrderTransport Executable follow space BlindTo jointStore Separated)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

structure TensorExecution (left right : Configuration T O) (first second : List (Firing T S O)) where
  execution : (firstOrder A label).toStep.Run (AnnotatedRuns.tensor left right)
  word : sites A label execution = first ++ second
  resultIso : (firstOrderTransport A label).Iso execution.last
    (AnnotatedRuns.tensor (follow label left first) (follow label right second))

def tensor_of_separated (left right : Configuration T O) (first second : List (Firing T S O))
    (separated : Separated A label left first right second) : TensorExecution A label left right first second := by
  have whole := AnnotatedRuns.tensor_executable A label left first right second separated
  let execution := ofExecutable A label (AnnotatedRuns.tensor left right) (first ++ second) whole.1
  have word := sites_ofExecutable A label (AnnotatedRuns.tensor left right) (first ++ second) whole.1
  refine ⟨execution, word, ⟨?_⟩⟩
  rw [last_eq_follow, word]
  exact whole.2

theorem raw_tensor_defined_iff {left right : Configuration T O} {first second : List (Firing T S O)}
    (one : Executable A label left first) (two : Executable A label right second)
    (apart : Disjoint (space left first) (space right second))
    (leftBlind : ∀ f ∈ first, BlindTo A label (space right second) f)
    (rightBlind : ∀ f ∈ second, BlindTo A label (space left first) f) :
    (∃ run : (firstOrder A label).toStep.Run (AnnotatedRuns.tensor left right),
      sites A label run = first ++ second) ↔
        (first = [] ∧ second = []) ∨ A.Consistent (jointStore label left first right second) := by
  rw [exists_run_iff, List.append_eq_nil_iff,
    AnnotatedRuns.tensor_defined_iff A label one two apart leftBlind rightBlind]

theorem consistent_tensor_defined_iff {left right : Configuration T O} {first second : List (Firing T S O)}
    (one : Executable A label left first) (two : Executable A label right second)
    (apart : Disjoint (space left first) (space right second))
    (leftBlind : ∀ f ∈ first, BlindTo A label (space right second) f)
    (rightBlind : ∀ f ∈ second, BlindTo A label (space left first) f) :
    (∃ run : (firstOrder A label).toStep.Run (AnnotatedRuns.tensor left right),
      sites A label run = first ++ second ∧ A.Consistent (AnnotatedRuns.tensor left right).equations) ↔
        A.Consistent (jointStore label left first right second) := by
  rw [consistent_run_iff, AnnotatedRuns.tensor_defined_iff A label one two apart leftBlind rightBlind]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns
