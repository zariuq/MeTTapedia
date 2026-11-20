import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ResidualModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.FamilyInformationControls

/-!
# A real residual retains two visible unresolved values

A native maker runs while physical rows 7 and 8 retain two distinct captured
unknowns. The given model keeps those unknowns as distinct target names. The
fresh extension lift preserves their difference; the existing weak-terminal
amalgam identifies their images. The same actual execution also transports a
whole remaining family's given solution data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ResidualModelsControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidualExample (tiny bit)
open FamilyInformationControls (locals shared)

abbrev active := ContextualActivatedStep.target locals shared

def state : NativeState tiny Nat ([] : Ctx tiny) () :=
  { FamilyInformationControls.state with state :=
    { FamilyInformationControls.state.state with
      present := {7,8}
      rows := fun occurrence => ContextualConditionalRows.ofStored locals shared
        (.shared (generator shared (occurrence == 7))) } }

def maker (port : Nat) : LiveFiring state where
  rule := ⟨[],[],[],[],[bit _ false]⟩
  selection := ⟨[],[],[port]⟩
  outputs _ := bit active false
  patterns := []
  fuel := 0

theorem maker_information (port : Nat) : (maker port).toNative.information = [] := rfl

theorem maker_realized (port : Nat) (fresh : port ∉ ({7,8} : Finset Nat)) : (maker port).toNative.Realized := by
  apply (native_admits_iff (S := tiny) (maker port).toNative).mpr
  refine ⟨⟨List.nodup_nil,List.nodup_singleton port,rfl,rfl,rfl⟩,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,fun _ inside => by simp [Selection.commit] at inside⟩
    · show ([] : List Nat).toFinset ⊆ ({7,8} : Finset Nat)
      simp
    · show ([] : List Nat).toFinset ⊆ ({7,8} : Finset Nat)
      simp
    · show Disjoint ([] : List Nat).toFinset ([] : List Nat).toFinset
      simp
    · show Disjoint [port].toFinset ({7,8} : Finset Nat)
      simpa using fresh
  · exact ⟨state.infoFrame,generator _,fun _ inside => absurd inside List.not_mem_nil⟩
  · intro _ _ _
    exact ⟨fun _ inside => absurd inside List.not_mem_nil,fun _ inside => absurd inside List.not_mem_nil⟩

noncomputable def execution : ContextualConditionalExecution.Firing state.locals state.state :=
  LiveFiring.execution (maker_realized 0 (by decide))

def target : Frames.Frame tiny := ⟨Bool,shared⟩

def candidate : Assignment active target.arity
  | .inl _ => generator target.arity false
  | .inr name => generator target.arity name

noncomputable def joint : NativeResidual.Joint state (maker 1).toNative.information
    (NativeResidual.problemOf state execution.selection execution.rule) target where
  left := candidate
  right := candidate
  left_models := fun _ inside => absurd inside List.not_mem_nil
  right_models := by
    have actual := NativeIterated.problemOf_execution (maker_realized 0 (by decide))
    change ContextualResidual.Models candidate
      (NativeResidual.problemOf state (LiveFiring.execution (maker_realized 0 (by decide))).selection
        (LiveFiring.execution (maker_realized 0 (by decide))).rule)
    rw [actual]
    exact fun _ inside => absurd inside List.not_mem_nil
  agree := rfl

theorem unmade : ∀ occurrence ∈ (maker 1).selection.taken ++ (maker 1).selection.read,
    occurrence ∉ execution.selection.made := fun _ inside => absurd inside List.not_mem_nil

theorem actual_residual_model : ContextualResidual.Models (ResidualModels.amalgam execution joint)
    ((maker 1).residualAt execution).toNative.information := ResidualModels.models_amalgam execution (maker 1) unmade joint

def value (name : Bool) : Term (signature tiny active) ([] : Ctx tiny) () := generator active (.inr name)

theorem given_values_differ : instantiate candidate (value true) ≠ instantiate candidate (value false) := by
  rw [show instantiate candidate (value true) = generator target.arity true from instantiate_generator candidate (.inr true)]
  rw [show instantiate candidate (value false) = generator target.arity false from instantiate_generator candidate (.inr false)]
  intro same
  cases same

theorem faithful_residual_values_differ :
    instantiate (ResidualModels.amalgam execution joint) (instantiate (NativeResidual.carry execution) (value true)) ≠
      instantiate (ResidualModels.amalgam execution joint) (instantiate (NativeResidual.carry execution) (value false)) := by
  intro same
  exact given_values_differ ((ResidualModels.read_left_equal_iff execution joint (value true) (value false)).mp same)

theorem weak_amalgam_values_agree :
    instantiate (NativeResidual.amalgam execution joint) (instantiate (NativeResidual.carry execution) (value true)) =
      instantiate (NativeResidual.amalgam execution joint) (instantiate (NativeResidual.carry execution) (value false)) := by
  have read (name : Bool) :
      instantiate (NativeResidual.amalgam execution joint) (instantiate (NativeResidual.carry execution) (value name)) =
        instantiate (Frames.toFirstOrder target) (instantiate candidate (value name)) :=
    (instantiate_comp (NativeResidual.carry execution) (NativeResidual.amalgam execution joint) (value name)).trans
      ((congrArg (fun assignment => instantiate assignment (value name)) (NativeResidual.amalgam_left execution joint)).trans
        (Assignment.instantiate_compose (Frames.toFirstOrder target) candidate (value name)))
  rw [read true,read false]
  rfl

def sourceData : FamilyInformation.SolutionData state [maker 1] target where
  shared name := generator target.arity name
  member _ := candidate
  agrees _ := by
    funext name
    exact instantiate_generator candidate (.inr name)
  models index := by
    fin_cases index
    exact fun _ inside => absurd inside List.not_mem_nil

noncomputable def afterData : FamilyInformation.SolutionData (rawTarget execution)
    ([maker 1].map (fun firing => firing.residualAt execution)) (ResidualModels.extended execution target) :=
  ResidualModels.residualData execution sourceData candidate joint.right_models
    (sourceData.agrees ⟨0,by decide⟩) (fun firing inside => by
      obtain rfl := List.mem_singleton.mp inside
      exact unmade)

theorem actual_remaining_family_model : ContextualResidual.Models (afterData.member ⟨0,by decide⟩)
    (FamilyInformation.memberInformation (([maker 1].map (fun firing => firing.residualAt execution))[0])) :=
  afterData.models ⟨0,by decide⟩

theorem observed_rows_are_present : 7 ∈ state.state.present ∧ 8 ∈ state.state.present := by simp [state]

theorem observed_source_values :
    (state.state.rows 7).value = .shared (generator shared true) ∧
      (state.state.rows 8).value = .shared (generator shared false) := ⟨rfl,rfl⟩

theorem observed_rows_remain_present :
    7 ∈ (rawTarget execution).state.present ∧ 8 ∈ (rawTarget execution).state.present := by
  change 7 ∈ MeTTaCalculus.OccurrenceCommits.fire state.state.present (execution.selection.commit (T := Unit)) ∧
    8 ∈ MeTTaCalculus.OccurrenceCommits.fire state.state.present (execution.selection.commit (T := Unit))
  have selected : execution.selection = (maker 0).selection := (LiveFiring.execution_data (maker_realized 0 (by decide))).2.1
  rw [selected]
  simp [state,maker,Selection.commit,MeTTaCalculus.OccurrenceCommits.fire]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ResidualModelsControls
