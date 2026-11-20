import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Controls.HostedEventsAudit

/-!
# Whole-query duplicate, failure and shared-scope controls

Closed duplicate equations produce two finished answers in the target frontier.
A source failure has a target retirement step. A source call can advance the
global scope while a previously finished branch remains in the partial answer
bag. These are instances of the complete configuration correspondence, not
selected-branch comparisons.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting.Answers.Bags (D N P1 P2 q sp supply W0 W1 X Y final2 oneT oneC fT matched1 live_ff)
open Classical

theorem plain_one : PlainProgram P1 := by
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  trivial

theorem duplicate_source_has_two_live_branches :
    (final2.branches.filter (fun branch => Solvable branch.store)).card = 2 := by
  have allLive : ∀ branch ∈ final2.branches, Solvable branch.store := by
    intro branch member
    have same : branch = Y := by simpa [final2] using member
    subst branch
    exact live_ff
  rw [Multiset.filter_eq_self.mpr allLive]
  simp [final2]

theorem duplicate_query_runs_to_two_answers :
    ∃ frontier : FrontierConfig.TargetState,
      (FrontierConfig.target (D := D) P2 N q).MultiStep ⟨{[]}, 0⟩ frontier ∧
      FrontierConfig.Represents (D := D) P2 N q final2 frontier ∧
      frontier.leaves.card = 2 ∧
      Frontier.answers (FinishedClass (D := D) N P2 q) (classAnswer (D := D) N P2 q) frontier = {{oneC}, {oneC}} := by
  obtain ⟨frontier, reached, paired⟩ := FrontierConfig.runs_forward (D := D) P2 N q supply
    Controls.HostedEventsAudit.plain_program
    (FrontierConfig.initial (D := D) P2 N q sp (by trivial) Hosting.Answers.Bags.q_unopened)
    Hosting.Answers.Bags.p2_runs
  refine ⟨frontier, reached, paired, ?_, ?_⟩
  · exact (Multiset.card_eq_card_of_rel paired.leaves).symm.trans duplicate_source_has_two_live_branches
  · exact (FrontierConfig.answers_eq (D := D) P2 N q paired).symm.trans Hosting.Answers.Bags.p2_answers

def failQuery : Comp mkeys [] () MTy := .fail

theorem fail_unopened : ∀ term ∈ failQuery.data, ∀ name ∈ support term, name.scopes = [] := by
  intro term member
  cases member

theorem fail_source_step :
    SourceLanguage.Step D P1 supply (Config.initial sp failQuery) ⟨W0, 0⟩ :=
  Step.single live_nil (.fail W0 [] [] [])

theorem failure_has_controller_step :
    ∃ frontier : FrontierConfig.TargetState,
      (FrontierConfig.target (D := D) P1 N failQuery).Step ⟨{[]}, 0⟩ frontier ∧
      FrontierConfig.Represents (D := D) P1 N failQuery ⟨W0, 0⟩ frontier ∧
      frontier.leaves = 0 := by
  obtain ⟨frontier, moved, paired⟩ := FrontierConfig.forward (D := D) P1 N failQuery supply plain_one
    (FrontierConfig.initial (D := D) P1 N failQuery sp (by trivial) fail_unopened) fail_source_step
  refine ⟨frontier, moved, paired, ?_⟩
  apply Multiset.rel_zero_left.mp
  exact paired.leaves

/-- The failed initial history is retired, rather than silently disappearing from the
controller's bookkeeping. No native child is manufactured for the failed branch. -/
theorem failure_retires_empty_history :
    (FrontierConfig.target (D := D) P1 N failQuery).Step ⟨{[]}, 0⟩ ⟨0, {[]}⟩ := by
  let : (word : List RuleName) → Fintype ((HostedEvents.targetSystem (D := D) N P1 failQuery).Choice word) :=
    fun word => FrontierNames.targetChoices (D := D) P1 N failQuery word
  have paired : HostedEvents.Related (D := D) N P1 failQuery (W0, initialBranch failQuery) [] :=
    HostedEvents.initial (D := D) (N := N) (P := P1) (q := failQuery) sp (by trivial) fail_unopened
  have sourceEmpty : Fintype.card ((HostedEvents.sourceSystem (D := D) P1).Choice (W0, initialBranch failQuery)) = 0 :=
    Fintype.card_eq_zero_iff.mpr Controls.HostedEventsAudit.failure_has_no_named_child
  have counts := Fintype.card_congr ((HostedEvents.bisimulation plain_one).choices paired)
  have empty : Fintype.card ((HostedEvents.targetSystem (D := D) N P1 failQuery).Choice []) = 0 :=
    counts.symm.trans sourceEmpty
  have childrenEmpty : Frontier.children (HostedEvents.targetSystem (D := D) N P1 failQuery) [] = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [Frontier.children, Multiset.card_map]
    change Fintype.card ((HostedEvents.targetSystem (D := D) N P1 failQuery).Choice []) = 0
    exact empty
  have unfinished : ¬ FinishedClass (D := D) N P1 failQuery [] := by
    intro finished
    exact not_finished_of_fail rfl ((HostedEvents.finished_iff paired).mpr finished)
  have moved := Frontier.Unfold.expand (system := HostedEvents.targetSystem (D := D) N P1 failQuery)
    (finished := FinishedClass (D := D) N P1 failQuery) [] 0 0 unfinished
  change Frontier.Unfold (HostedEvents.targetSystem (D := D) N P1 failQuery)
    (FinishedClass (D := D) N P1 failQuery) ⟨{[]}, 0⟩ ⟨0, {[]}⟩
  simpa only [childrenEmpty, zero_add, Frontier.retire, if_pos empty, Multiset.cons_zero] using moved

def mixedQuery : Comp mkeys [] () MTy := .choice (.ret oneT) (.apply fT)
def leftPending : Branch mkeys [] () MTy := ⟨[], .eval (.ret oneT), [], []⟩
def leftDone : Branch mkeys [] () MTy := ⟨[], .value oneT, [], []⟩
def rightPending : Branch mkeys [] () MTy := initialBranch q
def afterFork : Config mkeys [] () MTy := ⟨W0, {leftPending, rightPending}⟩
def afterLeft : Config mkeys [] () MTy := ⟨W0, {leftDone, rightPending}⟩
def afterScope : Config mkeys [] () MTy := ⟨W1, {leftDone, X}⟩

theorem mixed_unopened : ∀ term ∈ mixedQuery.data, ∀ name ∈ support term, name.scopes = [] := by
  intro term member name inside
  simp only [mixedQuery, Comp.data, List.mem_append, List.mem_singleton] at member
  rcases member with rfl | rfl <;> simp [oneT, fT, tuple, tupleArgs, sym, support, supportArgs] at inside

theorem mixed_runs : Runs D P1 supply (Config.initial sp mixedQuery) afterScope := by
  have fork : SourceLanguage.Step D P1 supply (Config.initial sp mixedQuery) afterFork :=
    Step.single live_nil (.choice W0 [] (.ret oneT) (.apply fT) [] [])
  have finishLeft : SourceLanguage.Step D P1 supply afterFork afterLeft :=
    Step.of_eq (b := leftPending) (rest := {rightPending}) rfl rfl live_nil (.ret W0 [] oneT [] [])
  have callRight : SourceLanguage.Step D P1 supply afterLeft afterScope := by
    apply Step.of_eq (D := D) (P := P1) (supply := supply) (b := rightPending) (rest := {leftDone})
      (by exact Multiset.cons_swap _ _ _) (by exact Multiset.cons_swap _ _ _)
      live_nil (.apply W0 [] fT [] [] matched1)
  exact (Relation.ReflTransGen.single fork).tail finishLeft |>.tail callRight

theorem scope_advanced_with_finished_neighbor :
    afterLeft.world.scope = 0 ∧ afterScope.world.scope = 1 ∧
      leftDone ∈ afterScope.branches ∧ leftDone.Finished (D := D) := by
  refine ⟨rfl, rfl, ?_, rfl, oneT, rfl⟩
  simp [afterScope]

theorem prefix_keeps_finished_answer : afterScope.answers (D := D) = {leftDone.answer (D := D)} := by
  have notFinished : ¬ X.Finished (D := D) := by
    rintro ⟨_, value, same⟩
    cases same
  have pending : (⟨W1, {X}⟩ : Config mkeys [] () MTy).answers (D := D) = 0 := by
    simp only [Config.answers, Multiset.filter_singleton]
    rw [if_neg (fun both => notFinished both.1)]
    rfl
  change (⟨W1, leftDone ::ₘ {X}⟩ : Config mkeys [] () MTy).answers (D := D) = _
  rw [answers_cons_finished (D := D) ⟨rfl, oneT, rfl⟩ live_nil, pending]
  rfl

theorem shared_scope_prefix_is_realized :
    ∃ frontier : FrontierConfig.TargetState,
      (FrontierConfig.target (D := D) P1 N mixedQuery).MultiStep ⟨{[]}, 0⟩ frontier ∧
      FrontierConfig.Represents (D := D) P1 N mixedQuery afterScope frontier ∧
      Frontier.answers (FinishedClass (D := D) N P1 mixedQuery) (classAnswer (D := D) N P1 mixedQuery) frontier =
        {leftDone.answer (D := D)} := by
  obtain ⟨frontier, reached, paired⟩ := FrontierConfig.runs_forward (D := D) P1 N mixedQuery supply plain_one
    (FrontierConfig.initial (D := D) P1 N mixedQuery sp (by trivial) mixed_unopened) mixed_runs
  exact ⟨frontier, reached, paired, (FrontierConfig.answers_eq (D := D) P1 N mixedQuery paired).symm.trans
    prefix_keeps_finished_answer⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierControls.duplicate_query_runs_to_two_answers
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierControls.failure_has_controller_step
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierControls.failure_retires_empty_history
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierControls.shared_scope_prefix_is_realized
