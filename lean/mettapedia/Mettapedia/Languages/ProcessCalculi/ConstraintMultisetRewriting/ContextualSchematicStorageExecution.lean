import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorageControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommonEventExecution

/-!
# Stored-rule answers in an actual two-firing inventory path

The generic pair construction supplies actual completed worklist returns
and changing declaration frames. Both output equations are transported to
the final inventory. Neither a returned solver update nor a path is a
premise of the construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage.Execution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualScopeSupport ContextualWorldScopeLedger ContextualExecution ContextualSchedulePromotion
open Controls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def scopes (_ : Nat) : Finset Nat := ∅
def inventory : Inventory locals captures (O := Nat) [] () := ⟨before,rows,[],[]⟩
def initial : Endpoint locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := scopes
  occupied := occupied
  inventory := inventory
  covered := (coveredWorld_iff locals captures scopes occupied inventory).mpr (by decide +kernel)

def joint := ContextualPairFrames.jointProblem locals captures occupied second (query captures 2) rows
  first (query captures 1) before
def firstView : Assignment active later := (ContextualPairFrames.first locals captures).assignment
def secondView : Assignment active later := (ContextualPairFrames.second locals captures).assignment
def firstAnswer : Closed later := instantiate firstView (firstOutput 99)
def secondAnswer : Closed later := instantiate secondView (firstOutput 100)
def firstArgument : Closed later := instantiate firstView (localVariable 2 0)
def secondArgument : Closed later := instantiate secondView (localVariable 2 0)

theorem joint_equations :
    joint =
      [(equation (f (number 1)) firstAnswer, equation (f firstArgument) (b firstArgument (number 2))),
       (equation (f (number 2)) secondAnswer, equation (f secondArgument) (b secondArgument (number 2)))] := by
  with_unfolding_all rfl

def jointSolution {Next : Type} (target : Next → MetaArity base) (caller : Assignment captures target) :
    Assignment later target
  | .inl ⟨scope,name⟩ => if scope = 1 ∧ name = 1 then b (number 1) (number 2) else number 1
  | .inr (.inl ⟨scope,name⟩) => if scope = 1 ∧ name = 1 then b (number 2) (number 2) else number 2
  | .inr (.inr name) => caller name

theorem joint_accepts_every_caller_assignment {Next : Type} (target : Next → MetaArity base)
    (caller : Assignment captures target) : ContextualFrameUnifier.Models (jointSolution target caller) joint := by
  rw [joint_equations]
  intro e member
  rcases List.mem_cons.mp member with same | member
  · subst e
    with_unfolding_all rfl
  · have same := List.mem_singleton.mp member
    subst e
    with_unfolding_all rfl

theorem joint_answers {Next : Type} {target : Next → MetaArity base} (candidate : Assignment later target)
    (solved : ContextualFrameUnifier.Models candidate joint) :
    instantiate candidate firstAnswer = b (number 1) (number 2) ∧
    instantiate candidate secondAnswer = b (number 2) (number 2) := by
  rw [joint_equations] at solved
  exact ⟨read_answer candidate firstArgument firstAnswer 1 (solved _ List.mem_cons_self),
    read_answer candidate secondArgument secondAnswer 2
      (solved (equation (f (number 2)) secondAnswer,
        equation (f secondArgument) (b secondArgument (number 2))) (by simp))⟩

theorem query_covered (n : Nat) :
    RuleCovered (privateScopes scopes) occupied (query captures n) := by
  apply (ruleRoots_covered_iff _ _ _).mp
  change (∅ : Finset Nat) ⊆ occupied
  exact Finset.empty_subset _

theorem first_admission : ContextualGuardedStep.Valid
    locals captures occupied first (query captures 1) rows before firstOutput := by
  refine ⟨⟨first_valid.take_distinct,first_valid.output_distinct,first_valid.take_length,
    first_valid.read_length,first_valid.outputs,first_valid.occurrences,?_⟩,
    ContextualFrameUnifier.solvable_of_model (first_read_accepts_every_caller_assignment active
      (ContextualSelectionViews.capturedTarget locals captures))⟩
  intro check member
  cases member

theorem first_pattern : ContextualPatternFragment.ProblemPattern
    (ContextualResidual.observeProblem firstProblem) :=
  (ContextualPatternFragment.checkProblem_iff _).mp (by decide +kernel)

theorem joint_pattern : ContextualPatternFragment.ProblemPattern
    (ContextualResidual.observeProblem joint) :=
  (ContextualPatternFragment.checkProblem_iff _).mp (by decide +kernel)

theorem second_formation : ContextualInteractionFactors.Formation
    locals captures occupied second (query captures 2) rows firstOutput := ⟨rfl,rfl,rfl⟩

theorem second_resources : ContextualInteractionFactors.Resources second
    (fire before.present (first.commit (T := Unit))) := by
  apply (ContextualInteractionFactors.resources_iff firstOutput _ _).mpr
  decide +kernel

theorem selected_schema_unchanged : ∀ o ∈ second.taken ++ second.read, o ∉ first.made := by
  decide +kernel

theorem first_answer_entailed : ContextualGuardSemantics.Ask locals joint
    (ContextualPairFrames.rowsAfterBoth locals captures rows first second firstOutput firstOutput)
    (fire (fire before.present (first.commit (T := Unit))) (second.commit (T := Unit)))
    (.equal firstAnswer (b (number 1) (number 2))) := by
  intro Next target candidate solved
  exact (joint_answers candidate solved).1

theorem second_answer_entailed : ContextualGuardSemantics.Ask locals joint
    (ContextualPairFrames.rowsAfterBoth locals captures rows first second firstOutput firstOutput)
    (fire (fire before.present (first.commit (T := Unit))) (second.commit (T := Unit)))
    (.equal secondAnswer (b (number 2) (number 2))) := by
  intro Next target candidate solved
  exact (joint_answers candidate solved).2

/-- Retaining an ordinary stored atom through an actual solver return does
not specialize its private template. This holds for arbitrary binding syntax. -/
theorem firing_retains_stored_atom {S : Signature} {Local O : Type}
    [DecidableEq Local] [DecidableEq O] [DecidableEq S.Srt] [∀ s, DecidableEq (S.Op s)]
    (privateDecl : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}
    {before after : Endpoint privateDecl O Γ sort} (firing : Firing privateDecl before after)
    (atom : Term (signature S privateDecl) Γ sort) (o : O)
    (stored : before.inventory.rows o = ContextualStoredRows.store privateDecl before.declarations atom)
    (notMade : o ∉ firing.selection.made) :
    after.inventory.rows o = ContextualStoredRows.store privateDecl after.declarations atom := by
  cases firing with
  | mk rule covered selection outputs fuel update admitted computed empty destination =>
      subst after
      change ((ContextualActivatedStep.resultRows privateDecl before.declarations selection outputs before.inventory.rows) o).map
          privateDecl (ContextualComputedFreshFrame.includeSource update) = _
      simp only [ContextualActivatedStep.resultRows,if_neg notMade,stored,ContextualStoredRows.map_store]
      rfl

/-- Actual family-changing firings retain both expected answers. The map
only relocates the common event variables into the computed final frame. -/
theorem actual_two_reader_path :
    ∃ after : Endpoint locals Nat [] (), ∃ path : Quiver.Path initial after,
      ∃ view : Assignment later after.declarations,
        ContextualExecution.selections path = [first,second] ∧
        after.inventory.configuration.present = {7,8,99,100} ∧
        after.inventory.rows 7 = ContextualStoredRows.store locals after.declarations storedRule ∧
        ContextualGuardSemantics.Ask locals after.inventory.configuration.equations after.inventory.rows
          after.inventory.configuration.present (.equal (instantiate view firstAnswer) (b (number 1) (number 2))) ∧
        ContextualGuardSemantics.Ask locals after.inventory.configuration.equations after.inventory.rows
          after.inventory.configuration.present (.equal (instantiate view secondAnswer) (b (number 2) (number 2))) := by
  have jointModel := joint_accepts_every_caller_assignment later
    (ContextualPairFrames.caller locals captures)
  obtain ⟨one,two,relocation,_,oneSelected,_,_,twoSelected,_,_,oneChecked,twoChecked,⟨path,picked⟩,transport⟩ :=
    ContextualPairFrames.realize_ordered_pair locals initial first second (query captures 1) (query captures 2)
      firstOutput firstOutput (query_covered 1) (query_covered 2) first_admission first_pattern
      second_formation second_resources selected_schema_unchanged
      (ContextualFrameUnifier.solvable_of_model jointModel)
      (by intro check member; cases member) joint_pattern
  let view := Assignment.compose (ContextualComputedFreshFrame.includeSource two.update)
    (ContextualPairFrames.secondActive locals captures one.update.declaration relocation).assignment
  have oneStored := firing_retains_stored_atom locals (one.firing oneChecked) storedRule 7
    (by change rows 7 = ContextualStoredRows.store locals captures storedRule; simp [rows])
    (by change 7 ∉ one.selection.made; rw [oneSelected]; decide +kernel)
  have twoStored := firing_retains_stored_atom locals (two.firing twoChecked) storedRule 7 oneStored
    (by change 7 ∉ two.selection.made; rw [twoSelected]; decide +kernel)
  refine ⟨two.target,path,view,picked,?_,twoStored,?_,?_⟩
  · rw [(two.firing twoChecked).physical_result]
    change fire one.target.inventory.configuration.present (two.selection.commit (T := Unit)) = _
    rw [twoSelected,(one.firing oneChecked).physical_result]
    change fire (fire initial.inventory.configuration.present (one.selection.commit (T := Unit)))
      (second.commit (T := Unit)) = _
    rw [oneSelected]
    change fire (fire before.present (first.commit (T := Unit))) (second.commit (T := Unit)) = _
    decide +kernel
  · exact (transport (.equal firstAnswer (b (number 1) (number 2)))).mpr first_answer_entailed
  · exact (transport (.equal secondAnswer (b (number 2) (number 2)))).mpr second_answer_entailed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage.Execution
