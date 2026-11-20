import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.InformationNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.FamilyInformationControls

/-!
# Symbolic target transport and positional cuts of actual native solutions

The existing duplicate generative members keep distinct private values while
their shared capture remains symbolic in a further target frame. Reversing
their positional cut reverses those values. A diagonal reindexing instead
loses the second value. Actual target instantiation may also identify distinct
target terms, so forward model transport supplies no equation-reflection licence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.InformationNaturalityControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open NativeResidualExample (tiny bit)
open FamilyInformation InformationNaturality
open FamilyInformationControls (state target scope generative duplicateSolutions)

def original : Solutions state [generative,generative] target :=
  ⟨assemble duplicateSolutions, FamilyInformationControls.duplicate_information_solved⟩

def later : Frames.Frame tiny := ⟨Bool, fun _ => ([], ())⟩
def post : Assignment target.arity later.arity := fun _ => generator later.arity true
def transported : Solutions state [generative,generative] later := postSolution post original
def transportedData : SolutionData state [generative,generative] later := postData post duplicateSolutions

theorem original_data : solutionEquiv state [generative,generative] target original = duplicateSolutions :=
  (solutionEquiv state [generative,generative] target).apply_symm_apply duplicateSolutions

theorem transported_data : solutionEquiv state [generative,generative] later transported = transportedData := by
  change solutionEquiv state [generative,generative] later (postSolution post original) = _
  rw [solutionEquiv_natural, original_data]
  rfl

theorem transported_models : ContextualResidual.Models transported.val (information state [generative,generative]) :=
  transported.property

theorem private_values_preserved :
    transported.val (.inl (⟨0,by decide⟩,ScopedVar.at (scope 3) ())) = bit later.arity false ∧
      transported.val (.inl (⟨1,by decide⟩,ScopedVar.at (scope 3) ())) = bit later.arity true := ⟨rfl,rfl⟩

theorem shared_stays_symbolic :
    transported.val (.inr true) = generator later.arity true ∧
      transported.val (.inr false) = generator later.arity true :=
  ⟨instantiate_generator post (),instantiate_generator post ()⟩

def reversed : Cut [generative,generative] [generative,generative] :=
  pairCut ⟨1,by decide⟩ ⟨0,by decide⟩ (by decide)

theorem reversed_cut_values :
    assemble (reversed.data transportedData) (.inl (⟨0,by decide⟩,ScopedVar.at (scope 3) ())) = bit later.arity true ∧
      assemble (reversed.data transportedData) (.inl (⟨1,by decide⟩,ScopedVar.at (scope 3) ())) = bit later.arity false :=
  ⟨rfl,rfl⟩

theorem reversed_cut_post_square :
    reversed.solution (postSolution post original) = postSolution post (reversed.solution original) :=
  reversed.solution_post post original

def firstOwn : Cut [generative,generative] [generative] := ownCut ⟨0,by decide⟩
def secondOwn : Cut [generative,generative] [generative] := ownCut ⟨1,by decide⟩

theorem own_cuts_keep_their_positions :
    assemble (firstOwn.data transportedData) (.inl (⟨0,by decide⟩,ScopedVar.at (scope 3) ())) = bit later.arity false ∧
      assemble (secondOwn.data transportedData) (.inl (⟨0,by decide⟩,ScopedVar.at (scope 3) ())) = bit later.arity true :=
  ⟨rfl,rfl⟩

def nativeJoint : NativeResidual.Joint state (memberInformation generative) (memberInformation generative) later :=
  jointAt transportedData ⟨0,by decide⟩ ⟨1,by decide⟩

theorem actual_native_joint_models :
    ContextualResidual.Models nativeJoint.left (memberInformation generative) ∧
      ContextualResidual.Models nativeJoint.right (memberInformation generative) :=
  ⟨nativeJoint.left_models,nativeJoint.right_models⟩

theorem native_joint_post_square :
    jointAt transportedData ⟨0,by decide⟩ ⟨1,by decide⟩ =
      postJoint post (jointAt duplicateSolutions ⟨0,by decide⟩ ⟨1,by decide⟩) :=
  jointAt_postData post duplicateSolutions _ _

def diagonal : Fin 2 → Fin 2 := fun _ => 0

theorem diagonal_reads (index : Fin 2) :
    ([generative,generative] : List (LiveFiring state))[index] =
      ([generative,generative] : List (LiveFiring state))[diagonal index] := by
  fin_cases index <;> rfl

theorem diagonal_not_injective : ¬ Function.Injective diagonal := by
  intro injective
  have same : (0 : Fin 2) = 1 := injective (by rfl)
  exact (by decide : (0 : Fin 2) ≠ 1) same

def diagonalData : SolutionData state [generative,generative] later :=
  restrictData (members := [generative,generative]) (subfamily := [generative,generative])
    diagonal diagonal_reads transportedData

theorem diagonal_loses_second_value :
    assemble diagonalData (.inl (⟨1,by decide⟩,ScopedVar.at (scope 3) ())) = bit later.arity false ∧
      transported.val (.inl (⟨1,by decide⟩,ScopedVar.at (scope 3) ())) = bit later.arity true :=
  ⟨rfl,private_values_preserved.2⟩

theorem diagonal_changes_assignment : assemble diagonalData ≠ transported.val := by
  intro same
  have value := congrFun same (.inl (⟨1,by decide⟩,ScopedVar.at (scope 3) ()))
  have clash : bit later.arity false = bit later.arity true :=
    diagonal_loses_second_value.1.symm.trans (value.trans diagonal_loses_second_value.2)
  unfold bit at clash
  cases clash

theorem diagonal_cannot_be_a_faithful_cut :
    ¬ ∃ cut : Cut [generative,generative] [generative,generative], cut.pick = diagonal := by
  rintro ⟨cut, same⟩
  exact diagonal_not_injective (same ▸ cut.injective)

def collapse : Assignment later.arity target.arity := fun _ => generator target.arity ()

theorem post_may_identify_distinct_terms :
    (generator later.arity true : Term (signature tiny later.arity) [] ()) ≠ generator later.arity false ∧
      instantiate collapse (generator later.arity true : Term (signature tiny later.arity) [] ()) =
        instantiate collapse (generator later.arity false) := by
  refine ⟨?_, ?_⟩
  · intro same
    cases same
  · exact (instantiate_generator collapse true).trans (instantiate_generator collapse false).symm

theorem solved_information_does_not_supply_compatibility :
    ContextualResidual.Models transported.val (information state [generative,generative]) ∧
      ¬ NativeIterated.Clears generative generative :=
  ⟨transported_models,FamilyInformationControls.duplicate_not_clear⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.InformationNaturalityControls
