import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextPlacement

/-!
# Context-enabled guards, scope separation and a fresh-output refusal

A prepared candidate asks that an existing variable equal seven. An explicitly
shared context supplies this fact and enables the candidate. An isolated copy
supplies the fact about a different variable and does not enable it. Reusing
an occupied output identity is refused even with the shared guard satisfied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacementControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers.Consumer (tiny constant empty)

def oneFrame : Frames.Frame tiny := ⟨Unit, fun _ => ([], ())⟩
def twoFrame : Frames.Frame tiny := ⟨Bool, fun _ => ([], ())⟩

def metavariable : Term (signature tiny oneFrame.arity) [] () := generator oneFrame.arity ()
def equation : Equation (Observation tiny oneFrame.arity) :=
  (observe metavariable, observe (constant (Γ := []) 7))

def left : State tiny Nat := ⟨oneFrame, [], ∅⟩
def right : State tiny Nat := ⟨oneFrame, [equation], ∅⟩
def candidate : Firing left := ⟨1, ([], ()), constant 9, [equation]⟩

def shared : ContextPlacement left right :=
  ⟨oneFrame, generator oneFrame.arity, generator oneFrame.arity⟩

def isolated : ContextPlacement left right :=
  ⟨twoFrame, (fun _ => generator twoFrame.arity false), (fun _ => generator twoFrame.arity true)⟩

def solvesOne : Assignment oneFrame.arity empty.arity := fun _ => constant 7
def separates : Assignment twoFrame.arity empty.arity := fun (side : Bool) =>
  match side with
  | false => constant 8
  | true => constant 7

theorem right_solvable : (Frames.contextual tiny).Solvable right.knowledge := by
  refine ⟨empty, solvesOne, ?_⟩
  intro entry member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem candidate_prepared : helperStep.Prepares candidate :=
  ⟨List.nodup_singleton _, (enabled_iff candidate).mpr (by decide),
    information_solvable candidate ⟨oneFrame, generator oneFrame.arity, Frames.models_nil _⟩⟩

theorem candidate_locally_refused : ¬helperStep.Admits candidate := by
  intro allowed
  have asked := ((admits_iff candidate).mp allowed).2.2
  have solved := asked oneFrame ((Frames.contextual tiny).id oneFrame) (Frames.models_nil _)
  have impossible := solved equation (List.mem_singleton_self _)
  change (Frames.contextual tiny).E
    ((Frames.contextual tiny).act ((Frames.contextual tiny).id oneFrame) equation.1)
    ((Frames.contextual tiny).act ((Frames.contextual tiny).id oneFrame) equation.2) at impossible
  rw [Frames.act_id, Frames.act_id] at impossible
  change observe metavariable = observe (constant (declaration := oneFrame.arity) (Γ := []) 7) at impossible
  cases observe_injective impossible

theorem shared_knowledge : shared.state.knowledge = right.knowledge := by
  change (Frames.contextual tiny).applyStore ((Frames.contextual tiny).id oneFrame) [] ++
    (Frames.contextual tiny).applyStore ((Frames.contextual tiny).id oneFrame) [equation] = [equation]
  rw [Frames.applyStore_id, Frames.applyStore_id, List.nil_append]

theorem shared_solvable : (Frames.contextual tiny).Solvable shared.state.knowledge :=
  shared_knowledge.symm ▸ right_solvable

theorem context_enables_candidate : helperStep.Admits (s := shared.state) (candidate.move shared.leftMap) := by
  apply (shared.left_admission_iff candidate).mpr
  refine ⟨shared_solvable, by decide, by decide, ?_⟩
  intro target mapping solved
  change (Frames.contextual tiny).Models mapping
    ((Frames.contextual tiny).applyStore ((Frames.contextual tiny).id oneFrame) [equation])
  have solved' : (Frames.contextual tiny).Models (a := oneFrame) (b := target) mapping [equation] :=
    Eq.mp (congrArg
      (fun store : EquationStore (Observation tiny oneFrame.arity) =>
        (Frames.contextual tiny).Models (a := oneFrame) (b := target) mapping store)
      shared_knowledge) solved
  exact Eq.mpr (congrArg
    (fun store : EquationStore (Observation tiny oneFrame.arity) =>
      (Frames.contextual tiny).Models (a := oneFrame) (b := target) mapping store)
    (Frames.applyStore_id (X := Frames.contextual tiny) [equation])) solved'

theorem isolated_model : (Frames.contextual tiny).Models separates isolated.state.knowledge := by
  intro entry member
  change entry ∈ [(instantiateObservation isolated.rightMap equation.1,
    instantiateObservation isolated.rightMap equation.2)] at member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem isolated_solvable : (Frames.contextual tiny).Solvable isolated.state.knowledge :=
  ⟨empty, separates, isolated_model⟩

theorem isolated_copy_does_not_enable :
    ¬helperStep.Admits (s := isolated.state) (candidate.move isolated.leftMap) := by
  intro allowed
  have asked := ((isolated.left_admission_iff candidate).mp allowed).2.2.2
  have guard := asked empty separates isolated_model
  have impossible := guard _ (List.mem_singleton_self _)
  change observe (constant (declaration := empty.arity) (Γ := []) 8) =
    observe (constant (Γ := []) 7) at impossible
  cases observe_injective impossible

def occupiedRight : State tiny Nat := { right with present := {1} }
def occupied : ContextPlacement left occupiedRight :=
  ⟨oneFrame, generator oneFrame.arity, generator oneFrame.arity⟩

theorem occupied_output_refused :
    ¬helperStep.Admits (s := occupied.state) (candidate.move occupied.leftMap) := by
  intro allowed
  have fresh := ((occupied.left_admission_iff candidate).mp allowed).2.2.1
  exact fresh (Finset.mem_singleton_self _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacementControls
