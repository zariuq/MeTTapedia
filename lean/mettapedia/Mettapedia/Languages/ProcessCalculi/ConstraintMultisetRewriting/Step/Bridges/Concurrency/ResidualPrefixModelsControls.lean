import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ResidualPrefixModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ResidualModelsControls

/-!
# Actual prefix readback and a newly produced input obstruction

An actual native prefix carries the same given capture and private readings
to a remaining member, with a checked model of the endpoint knowledge.
The two original visible unknowns remain distinct. A remaining read of the
prefix's newly made port instead violates Unmade: a prefix witness alone is
not a licence for the simultaneous source-information interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ResidualPrefixModelsControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidualExample (tiny bit)
open NativeIterated
open NativeRoundExecution (Witness)
open ResidualPrefixModels

abbrev actualNative := native (S := tiny) (O := Nat) (Γ := []) (sort := ())

def family : List (LiveFiring ResidualModelsControls.state) := [ResidualModelsControls.maker 0,ResidualModelsControls.maker 1]

def data : FamilyInformation.SolutionData ResidualModelsControls.state family ResidualModelsControls.target where
  shared name := generator ResidualModelsControls.target.arity name
  member _ := ResidualModelsControls.candidate
  agrees _ := by
    funext name
    exact instantiate_generator ResidualModelsControls.candidate (.inr name)
  models index := by
    fin_cases index <;> exact fun _ inside => absurd inside List.not_mem_nil

theorem clear : FamilyClear ResidualModelsControls.state family where
  admitted firing inside := by
    simp only [family,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl <;> exact ResidualModelsControls.maker_realized _ (by decide)
  pairwise := by
    refine List.pairwise_cons.mpr ⟨?_,List.pairwise_singleton _ _⟩
    intro firing inside
    obtain rfl := List.mem_singleton.mp inside
    apply NativePacketRounds.clears_of_resources
    · simp [NativePacketRounds.ResourcesApart,ResidualModelsControls.maker]
    · exact ⟨ResidualModelsControls.target,⟨InformationNaturality.jointAt data ⟨0,by decide⟩ ⟨1,by decide⟩⟩⟩
    all_goals rfl
  jointly := (FamilyInformation.jointly_iff_solvable _ _).mpr
    ⟨ResidualModelsControls.target,FamilyInformation.assemble data,FamilyInformation.assemble_models data⟩

theorem first_realized : (ResidualModelsControls.maker 0).toNative.Realized := ResidualModelsControls.maker_realized 0 (by decide)

noncomputable def afterState := actualNative.result (ResidualModelsControls.maker 0).toNative first_realized

noncomputable def witness : Witness ResidualModelsControls.state [ResidualModelsControls.maker 0] afterState :=
  .cons (ResidualModelsControls.maker 0) [] first_realized (.nil afterState)

noncomputable def post := lift_of_clear witness (remaining := [ResidualModelsControls.maker 1]) data (by simp) clear

theorem actual_endpoint_model : ContextualResidual.Models post.data.shared afterState.state.equations := post.known

theorem actual_capture_readback :
    Assignment.compose post.data.shared (lastTransport witness.toRun_last witness.toRun.toLast) =
      Assignment.compose post.extension.assignment data.shared :=
  lift_actual_captures witness data (NativePacketRounds.data_models_knowledge data (by simp [family])) (unmade_of_clear clear)

def remainingIndex : Fin (residuals witness [ResidualModelsControls.maker 1]).length := ⟨0,by simp [residuals_length]⟩

theorem actual_private_readback : Assignment.compose (post.data.member remainingIndex) (carried witness) =
    Assignment.compose post.extension.assignment (data.member (remainingPick witness [ResidualModelsControls.maker 1] remainingIndex)) :=
  post.members remainingIndex

theorem prefix_values_remain_distinct :
    instantiate (post.data.member remainingIndex) (instantiate (carried witness) (ResidualModelsControls.value true)) ≠
      instantiate (post.data.member remainingIndex) (instantiate (carried witness) (ResidualModelsControls.value false)) := by
  have reading (name : Bool) :
      instantiate (post.data.member remainingIndex) (instantiate (carried witness) (ResidualModelsControls.value name)) =
        instantiate post.extension.assignment (instantiate ResidualModelsControls.candidate (ResidualModelsControls.value name)) :=
    (instantiate_comp (carried witness) (post.data.member remainingIndex) (ResidualModelsControls.value name)).trans
      ((congrArg (fun assignment => instantiate assignment (ResidualModelsControls.value name)) actual_private_readback).trans
        (Assignment.instantiate_compose post.extension.assignment ResidualModelsControls.candidate (ResidualModelsControls.value name)))
  intro equal
  have original := post.extension.instantiate_injective ((reading true).symm.trans (equal.trans (reading false)))
  exact ResidualModelsControls.given_values_differ original

theorem actual_output_reading (occurrence : Nat) :
    instantiate (post.data.member remainingIndex) ((residuals witness [ResidualModelsControls.maker 1])[remainingIndex].outputs occurrence) =
      instantiate post.extension.assignment
        (instantiate ResidualModelsControls.candidate ((ResidualModelsControls.maker 1).outputs occurrence)) :=
  lift_output_reading witness data (NativePacketRounds.data_models_knowledge data (by simp [family]))
    (unmade_of_clear clear) remainingIndex occurrence

def newlyRead : LiveFiring ResidualModelsControls.state where
  rule := ⟨[],[bit _ true],[],[],[]⟩
  selection := ⟨[],[0],[]⟩
  outputs _ := bit ResidualModelsControls.active false
  patterns := []
  fuel := 0

theorem newlyRead_information : newlyRead.toNative.information =
    [(observe (bit ResidualModelsControls.active true),observe (generator ResidualModelsControls.active (.inr false)))] := rfl

def beforeCandidate : Assignment ResidualModelsControls.active ResidualModelsControls.target.arity
  | .inl _ => bit ResidualModelsControls.target.arity true
  | .inr name => if name then generator ResidualModelsControls.target.arity true else bit ResidualModelsControls.target.arity true

theorem source_information_can_hold :
    ContextualResidual.Models beforeCandidate newlyRead.toNative.information := by
  rw [newlyRead_information]
  intro equation inside
  obtain rfl := List.mem_singleton.mp inside
  rfl

def badData : FamilyInformation.SolutionData ResidualModelsControls.state
    [ResidualModelsControls.maker 0,newlyRead] ResidualModelsControls.target where
  shared := Assignment.compose beforeCandidate
    (ContextualSelectionViews.capturedTarget ResidualModelsControls.state.locals ResidualModelsControls.state.state.declarations)
  member _ := beforeCandidate
  agrees _ := rfl
  models index := by
    fin_cases index
    · exact fun _ inside => absurd inside List.not_mem_nil
    · exact source_information_can_hold

theorem bad_initial_knowledge_model : ContextualResidual.Models badData.shared ResidualModelsControls.state.state.equations :=
  fun _ inside => absurd inside List.not_mem_nil

noncomputable abbrev laterActive := ContextualActivatedStep.target afterState.locals afterState.state.declarations

theorem newlyRead_residual_information : (residualAfter first_realized newlyRead).toNative.information =
    [(observe (bit laterActive true),observe (bit laterActive false))] := rfl

theorem newlyRead_residual_unsolvable :
    ¬ (Frames.contextual tiny).Solvable (a := afterState.infoFrame) (residualAfter first_realized newlyRead).toNative.information := by
  rintro ⟨future,candidate,model⟩
  rw [newlyRead_residual_information] at model
  have clash := observe_injective (model _ List.mem_cons_self)
  change bit future.arity true = bit future.arity false at clash
  cases clash

theorem no_after_data (target : Frames.Frame tiny) :
    ¬ Nonempty (FamilyInformation.SolutionData afterState [residualAfter first_realized newlyRead] target) := by
  rintro ⟨data⟩
  exact newlyRead_residual_unsolvable ⟨target,data.member ⟨0,by decide⟩,data.models ⟨0,by decide⟩⟩

theorem newlyRead_not_initially_admitted : ¬ newlyRead.toNative.Realized := by
  intro accepted
  have kept := ((native_admits_iff (S := tiny) newlyRead.toNative).mp accepted).2.1.kept_subset
    (show 0 ∈ newlyRead.selection.commit.kept by simp [newlyRead,Selection.commit])
  simp [ResidualModelsControls.state] at kept

theorem prefix_witness_does_not_supply_unmade : ¬ Unmade [ResidualModelsControls.maker 0,newlyRead] := by
  intro unmade
  exact unmade newlyRead (by simp) (ResidualModelsControls.maker 0) (by simp) 0
    (by simp [newlyRead]) (by simp [ResidualModelsControls.maker])

theorem actual_prefix_event_count : witness.toRun.word.length = 1 := witness.event_count

namespace Generated

def firing : LiveFiring ResidualModelsControls.state where
  rule := ⟨[],[],[],[],[FamilyInformationControls.privateTerm]⟩
  selection := ⟨[],[],[1]⟩
  outputs _ := ContextualFreshening.termAt FamilyInformationControls.locals FamilyInformationControls.shared (FamilyInformationControls.scope 1)
    FamilyInformationControls.privateTerm
  patterns := []
  fuel := 0

theorem realized : firing.toNative.Realized := by
  apply (native_admits_iff (S := tiny) firing.toNative).mpr
  refine ⟨⟨List.nodup_nil,List.nodup_singleton 1,rfl,rfl,rfl⟩,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,fun _ inside => by simp [Selection.commit] at inside⟩
    · show ([] : List Nat).toFinset ⊆ ({7,8} : Finset Nat)
      simp
    · show ([] : List Nat).toFinset ⊆ ({7,8} : Finset Nat)
      simp
    · show Disjoint ([] : List Nat).toFinset ([] : List Nat).toFinset
      simp
    · show Disjoint ([1] : List Nat).toFinset ({7,8} : Finset Nat)
      simp
  · exact ⟨ResidualModelsControls.state.infoFrame,generator _,fun _ inside => absurd inside List.not_mem_nil⟩
  · intro _ _ _
    exact ⟨fun _ inside => absurd inside List.not_mem_nil,fun _ inside => absurd inside List.not_mem_nil⟩

def valuation (value : Bool) : Assignment ResidualModelsControls.active ResidualModelsControls.target.arity
  | .inl _ => bit ResidualModelsControls.target.arity value
  | .inr name => generator ResidualModelsControls.target.arity name

def sourceData : FamilyInformation.SolutionData ResidualModelsControls.state [ResidualModelsControls.maker 0,firing]
    ResidualModelsControls.target where
  shared name := generator ResidualModelsControls.target.arity name
  member index := valuation (index.val == 1)
  agrees index := by
    funext name
    exact instantiate_generator (valuation (index.val == 1)) (.inr name)
  models index := by
    fin_cases index <;> exact fun _ inside => absurd inside List.not_mem_nil

theorem clear : FamilyClear ResidualModelsControls.state [ResidualModelsControls.maker 0,firing] where
  admitted member inside := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl
    · exact first_realized
    · exact realized
  pairwise := by
    refine List.pairwise_cons.mpr ⟨?_,List.pairwise_singleton _ _⟩
    intro member inside
    obtain rfl := List.mem_singleton.mp inside
    apply NativePacketRounds.clears_of_resources
    · simp [NativePacketRounds.ResourcesApart,ResidualModelsControls.maker,firing]
    · exact ⟨ResidualModelsControls.target,⟨InformationNaturality.jointAt sourceData ⟨0,by decide⟩ ⟨1,by decide⟩⟩⟩
    all_goals rfl
  jointly := (FamilyInformation.jointly_iff_solvable _ _).mpr
    ⟨ResidualModelsControls.target,FamilyInformation.assemble sourceData,FamilyInformation.assemble_models sourceData⟩

noncomputable def after := lift_of_clear witness (remaining := [firing]) sourceData (by simp) clear

def index : Fin (residuals witness [firing]).length := ⟨0,by simp [residuals_length]⟩

theorem generated_output_is_the_given_true :
    instantiate (after.data.member index) ((residuals witness [firing])[index].outputs 1) =
      bit after.extension.declarations true := by
  have reading := lift_output_reading witness sourceData (NativePacketRounds.data_models_knowledge sourceData (by simp))
    (unmade_of_clear clear) index 1
  have selected : remainingPick witness [firing] index = ⟨1,by decide⟩ := by
    apply Fin.ext
    rfl
  rw [selected] at reading
  change instantiate (after.data.member index) ((residuals witness [firing])[index].outputs 1) =
    instantiate after.extension.assignment (instantiate (valuation true) (firing.outputs 1)) at reading
  have original : instantiate (valuation true) (firing.outputs 1) = bit ResidualModelsControls.target.arity true := by rfl
  exact reading.trans (congrArg (instantiate after.extension.assignment) original)

theorem source_private_valuations_are_different :
    sourceData.member ⟨0,by decide⟩ (.inl ⟨FamilyInformationControls.scope 1,()⟩) = bit ResidualModelsControls.target.arity false ∧
      sourceData.member ⟨1,by decide⟩ (.inl ⟨FamilyInformationControls.scope 1,()⟩) = bit ResidualModelsControls.target.arity true := ⟨rfl,rfl⟩

end Generated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ResidualPrefixModelsControls
