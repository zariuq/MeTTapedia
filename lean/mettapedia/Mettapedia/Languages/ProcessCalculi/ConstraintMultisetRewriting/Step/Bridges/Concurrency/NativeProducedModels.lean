import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.PacketResultModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativeWitnessCuts

/-!
# Given returned readings recover the original producer model

The actual witness and supplied target model are retained. No model target
is chosen or collapsed. A producer at any original position is recovered
through the actual residual sequence, including repeated firing values at
different positions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativeProducedModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual NativeIterated
open NativeRoundExecution (Witness)
open FamilyInformation (SolutionData)
open ResidualPrefixModels (changes castData castData_shared unmade_of_clear)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem produced_model {initial last : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    (witness : Witness initial members last) (clear : FamilyClear initial members)
    {target : Frames.Frame S} (candidate : Assignment last.state.declarations target.arity)
    (known : ContextualResidual.Models candidate last.state.equations)
    (pattern : Term (signature S target.arity) Γ sort) (occurrence : O)
    (matched : ContextualConditionalRows.Matches last.locals last.state.declarations candidate
      pattern (last.state.rows occurrence)) (index : Fin members.length)
    (made : occurrence ∈ members[index].selection.made) :
    ∃ data : SolutionData initial members target,
      ContextualResidual.Models data.shared initial.state.equations ∧
      data.shared = Assignment.compose candidate (changes witness) ∧
      pattern = instantiate (data.member index) (members[index].outputs occurrence) := by
  induction witness generalizing target with
  | nil initial => exact index.elim0
  | @cons initial first rest accepted last tail ih =>
      have clearTail := familyClear_residual clear accepted
      have untouched : ∀ firing ∈ rest,
          ∀ port ∈ firing.selection.taken ++ firing.selection.read, port ∉ first.selection.made := by
        intro firing inside port selected
        exact (unmade_of_clear clear) firing (List.mem_cons_of_mem first inside)
          first List.mem_cons_self port selected
      have captures (post : SolutionData (native.result first.toNative accepted)
          (rest.map (residualAfter accepted)) target)
          (postKnown : ContextualResidual.Models post.shared (native.result first.toNative accepted).state.equations)
          (postSame : post.shared = Assignment.compose candidate (changes tail)) :
          (PacketResultModels.stepData accepted rest post postKnown untouched).shared =
            Assignment.compose candidate (changes (.cons first rest accepted tail)) := by
        rw [PacketResultModels.stepData_captures,postSame]
        exact (Assignment.compose_associative _ _ _).symm
      revert made
      refine Fin.cases (fun made => ?_) (fun position made => ?_) index
      · have headMade : occurrence ∈ first.selection.made := made
        let recovered := PacketResultModels.recoverFinal tail candidate known (unmade_of_clear clearTail)
        let post := castData (List.append_nil (rest.map (residualAfter accepted))) recovered.data
        have postKnown : ContextualResidual.Models post.shared
            (native.result first.toNative accepted).state.equations := by
          change ContextualResidual.Models (castData _ recovered.data).shared _
          rw [castData_shared]
          exact recovered.known
        have postSame : post.shared = Assignment.compose candidate (changes tail) := by
          change (castData _ recovered.data).shared = _
          rw [castData_shared,recovered.captures,PacketResultModels.finalPost_shared]
        let before := PacketResultModels.stepData accepted rest post postKnown untouched
        have tailNotMade : ∀ firing ∈ rest.map (residualAfter accepted), occurrence ∉ firing.selection.made := by
          intro firing inside also
          obtain ⟨original,member,rfl⟩ := List.mem_map.mp inside
          exact Finset.disjoint_left.mp ((List.pairwise_cons.mp clear.pairwise).1 original member).1.ports
            (List.mem_toFinset.mpr headMade) (List.mem_toFinset.mpr also)
        have retained := (PacketResultModels.witness_matches_retained tail candidate occurrence tailNotMade pattern).mp matched
        have actualMade : occurrence ∈ (LiveFiring.execution accepted).selection.made := by
          rwa [(LiveFiring.execution_data accepted).2.1]
        have live : (LiveFiring.execution accepted).reusable occurrence = false := by
          rw [(LiveFiring.execution_data accepted).2.2.2]
        have output := (PacketResultModels.state_matches_made (LiveFiring.execution accepted)
          (Assignment.compose candidate (changes tail)) actualMade live pattern).mp retained
        rw [(LiveFiring.execution_data accepted).2.2.1] at output
        refine ⟨before,PacketResultModels.stepData_known accepted rest post postKnown untouched,
          captures post postKnown postSame,?_⟩
        change pattern = instantiate (Assignment.compose post.shared
          (ContextualComputedFreshFrame.includeSource (LiveFiring.execution accepted).update)) (first.outputs occurrence)
        rw [postSame]
        exact output
      · let nextIndex := PacketResultModels.residualIndex accepted rest position
        have nextMade : occurrence ∈ (rest.map (residualAfter accepted))[nextIndex].selection.made := by
          change occurrence ∈ (rest.map (residualAfter accepted))[position.val].selection.made
          rw [List.getElem_map]
          exact made
        obtain ⟨post,postKnown,postSame,output⟩ := ih clearTail candidate known pattern matched nextIndex nextMade
        let before := PacketResultModels.stepData accepted rest post postKnown untouched
        refine ⟨before,PacketResultModels.stepData_known accepted rest post postKnown untouched,
          captures post postKnown postSame,?_⟩
        change pattern = instantiate (before.member position.succ) (rest[position].outputs occurrence)
        rw [PacketResultModels.stepData_remaining]
        change pattern = instantiate (post.member nextIndex)
          (((rest.map (residualAfter accepted))[position.val]).outputs occurrence) at output
        rw [List.getElem_map] at output
        exact output.trans (Assignment.instantiate_compose _ _ _).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativeProducedModels
