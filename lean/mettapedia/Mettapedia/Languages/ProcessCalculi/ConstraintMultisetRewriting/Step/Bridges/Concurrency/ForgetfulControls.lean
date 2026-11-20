import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Frames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls
import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-!
# What the weak-terminal assignment forgets

The existing assignment to `Frames.firstOrderFrame` is a solution witness,
not a faithful representation of names. Two distinct names of one sort have
the same image. An equality not entailed by empty knowledge consequently
becomes entailed after this assignment. A proper injective frame extension
provides the positive comparison and retains all observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ForgetfulControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

abbrev base : Signature := ContextualFrame.Controls.signature

def small : Frames.Frame base := ⟨Bool, fun _ => ([], ())⟩

def nameTerm (name : Bool) : Term (signature base small.arity) [] () :=
  generator small.arity name

def nameObservation (name : Bool) : Observation base small.arity :=
  observe (nameTerm name)

theorem source_names_distinct : nameObservation false ≠ nameObservation true := by
  intro same
  have terms := observe_injective same
  have names := congrArg (support (S := base) (source := small.arity)) terms
  change [false] = [true] at names
  cases names

theorem weak_terminal_collapses_names :
    instantiateObservation (Frames.toFirstOrder small) (nameObservation false) =
      instantiateObservation (Frames.toFirstOrder small) (nameObservation true) := by
  rfl

theorem weak_terminal_not_injective :
    ¬ Function.Injective (instantiateObservation (Frames.toFirstOrder small)) := by
  intro faithful
  exact source_names_distinct (faithful weak_terminal_collapses_names)

theorem source_equality_not_entailed :
    ¬ (Frames.contextual base).Entails (a := small) [] (fun _ candidate =>
      instantiateObservation candidate (nameObservation false) =
        instantiateObservation candidate (nameObservation true)) := by
  intro entailed
  have atIdentity := entailed small (generator small.arity)
    ((Frames.contextual base).models_nil (generator small.arity))
  have same : nameObservation false = nameObservation true := by
    simpa only [instantiateObservation_identity] using atIdentity
  exact source_names_distinct same

theorem image_equality_entailed :
    (Frames.contextual base).Entails (a := Frames.firstOrderFrame base) [] (fun _ candidate =>
      instantiateObservation candidate
          (instantiateObservation (Frames.toFirstOrder small) (nameObservation false)) =
        instantiateObservation candidate
          (instantiateObservation (Frames.toFirstOrder small) (nameObservation true))) := by
  intro _ candidate _
  exact congrArg (instantiateObservation candidate) weak_terminal_collapses_names

theorem source_equation_solvable :
    (Frames.contextual base).Solvable (a := small)
      [(nameObservation false, nameObservation true)] := by
  refine ⟨Frames.firstOrderFrame base, Frames.toFirstOrder small, ?_⟩
  intro equation present
  have only : equation = (nameObservation false, nameObservation true) :=
    List.mem_singleton.mp present
  subst equation
  exact weak_terminal_collapses_names

/-! ## A proper frame extension retains the names -/

def larger : Frames.Frame base := ⟨Option Bool, fun _ => ([], ())⟩

def includeNames : Assignment small.arity larger.arity :=
  fun name => generator larger.arity (some name)

def recoverNames : Assignment larger.arity small.arity
  | none => generator small.arity false
  | some name => generator small.arity name

theorem inclusion_retracts : Assignment.compose recoverNames includeNames = generator small.arity := by
  funext name
  exact instantiate_generator recoverNames (some name)

theorem inclusion_retains_observations :
    Function.Injective (instantiateObservation includeNames) := by
  intro first second same
  have recovered := congrArg (instantiateObservation recoverNames) same
  rw [instantiateObservation_comp, instantiateObservation_comp, inclusion_retracts,
    instantiateObservation_identity, instantiateObservation_identity] at recovered
  exact recovered

theorem inclusion_keeps_names_distinct :
    instantiateObservation includeNames (nameObservation false) ≠
      instantiateObservation includeNames (nameObservation true) := by
  intro same
  exact source_names_distinct (inclusion_retains_observations same)

theorem extension_has_an_extra_name : ∀ name : Bool, (some name : Option Bool) ≠ none := by
  intro name same
  cases same

theorem inclusion_equality_not_entailed :
    ¬ (Frames.contextual base).Entails (a := larger) [] (fun _ candidate =>
      instantiateObservation candidate (instantiateObservation includeNames (nameObservation false)) =
        instantiateObservation candidate (instantiateObservation includeNames (nameObservation true))) := by
  intro entailed
  have atIdentity := entailed larger (generator larger.arity)
    ((Frames.contextual base).models_nil (generator larger.arity))
  have same : instantiateObservation includeNames (nameObservation false) =
      instantiateObservation includeNames (nameObservation true) := by
    simpa only [instantiateObservation_identity] using atIdentity
  exact inclusion_keeps_names_distinct same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ForgetfulControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ForgetfulControls.weak_terminal_not_injective
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ForgetfulControls.source_equality_not_entailed
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ForgetfulControls.inclusion_retains_observations
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ForgetfulControls.inclusion_equality_not_entailed
