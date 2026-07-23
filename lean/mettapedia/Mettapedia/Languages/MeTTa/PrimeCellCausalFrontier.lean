import Mettapedia.Languages.MeTTa.PrimeCellCausalSemantics
import Mathlib.Data.Finset.Card

/-!
# Prime cell-causal candidate frontier

The global machine owns producer outcomes.  This module adds the separate
per-rule candidate automata that consume those outcomes.  Candidate steps may
accept, refute, report a stable fault, or remain incomplete, but their type has
no operation that can create a producer outcome.

An exact residual certificate is deliberately non-vacuous: the eligible
frontier must be nonempty, and every eligible rule occurrence must carry an
explicit refutation receipt.  Pending, successful, faulted, and interrupted
candidates are not refutations.
-/

namespace Mettapedia.Languages.MeTTa.PrimeCellCausalFrontier

open PrimeCellCausalSemantics

inductive CandidateStatus (Event Answer Fault : Type*) where
  | pending
  | accepted (answer : Answer) (receipt : Finset Event)
  | refuted (receipt : Finset Event)
  | stableFault (fault : Fault) (receipt : Finset Event)
  | incomplete (receipt : Finset Event)
deriving DecidableEq

structure CandidateFrontier
    (Rule Event Answer Fault : Type*) where
  eligible : Finset Rule
  status : Rule → CandidateStatus Event Answer Fault

variable
  {Rule Source Producer ExpectedType Occurrence Outcome Event Publication
    Answer Fault : Type*}
  [DecidableEq Rule] [DecidableEq Source] [DecidableEq Producer]
  [DecidableEq ExpectedType] [DecidableEq Occurrence] [DecidableEq Outcome]
  [DecidableEq Event] [DecidableEq Publication] [DecidableEq Answer]
  [DecidableEq Fault]

local notation "CoreStateT" =>
  State Rule Source Producer ExpectedType Occurrence Outcome Event
    Publication Answer

def CandidateFrontier.setStatus
    (frontier : CandidateFrontier Rule Event Answer Fault)
    (rule : Rule) (status : CandidateStatus Event Answer Fault) :
    CandidateFrontier Rule Event Answer Fault :=
  { frontier with status := Function.update frontier.status rule status }

omit [DecidableEq Event] [DecidableEq Answer] [DecidableEq Fault] in
@[simp]
theorem CandidateFrontier.status_setStatus_same
    (frontier : CandidateFrontier Rule Event Answer Fault)
    (rule : Rule) (status : CandidateStatus Event Answer Fault) :
    (frontier.setStatus rule status).status rule = status := by
  simp [CandidateFrontier.setStatus]

omit [DecidableEq Event] [DecidableEq Answer] [DecidableEq Fault] in
@[simp]
theorem CandidateFrontier.status_setStatus_of_ne
    (frontier : CandidateFrontier Rule Event Answer Fault)
    {changed other : Rule} (different : other ≠ changed)
    (status : CandidateStatus Event Answer Fault) :
    (frontier.setStatus changed status).status other = frontier.status other := by
  simp [CandidateFrontier.setStatus, different]

omit [DecidableEq Event] [DecidableEq Answer] [DecidableEq Fault] in
theorem CandidateFrontier.setStatus_comm
    (frontier : CandidateFrontier Rule Event Answer Fault)
    {left right : Rule} (distinct : left ≠ right)
    (leftStatus rightStatus : CandidateStatus Event Answer Fault) :
    (frontier.setStatus left leftStatus).setStatus right rightStatus =
      (frontier.setStatus right rightStatus).setStatus left leftStatus := by
  cases frontier with
  | mk eligible status =>
    have updated :
        Function.update (Function.update status left leftStatus)
            right rightStatus =
          Function.update (Function.update status right rightStatus)
            left leftStatus := by
      funext rule
      by_cases rule = left
      · subst rule
        simp [Function.update, distinct]
      · by_cases rule = right
        · subst rule
          simp [Function.update, distinct.symm]
        · simp [Function.update, *]
    exact congrArg
      (fun nextStatus =>
        ({ eligible := eligible, status := nextStatus } :
          CandidateFrontier Rule Event Answer Fault)) updated

inductive CandidateStep
    (global : CoreStateT) :
    CandidateFrontier Rule Event Answer Fault →
      CandidateFrontier Rule Event Answer Fault → Prop where
  | accept (frontier) (rule) (answer) (receipt)
      (eligible : rule ∈ frontier.eligible)
      (pending : frontier.status rule = .pending)
      (exact : receipt = rootsFor global rule) :
      CandidateStep global frontier
        (frontier.setStatus rule (.accepted answer receipt))
  | refute (frontier) (rule) (receipt)
      (eligible : rule ∈ frontier.eligible)
      (pending : frontier.status rule = .pending)
      (exact : receipt = rootsFor global rule) :
      CandidateStep global frontier
        (frontier.setStatus rule (.refuted receipt))
  | fault (frontier) (rule) (fault) (receipt)
      (eligible : rule ∈ frontier.eligible)
      (pending : frontier.status rule = .pending)
      (exact : receipt = rootsFor global rule) :
      CandidateStep global frontier
        (frontier.setStatus rule (.stableFault fault receipt))
  | interrupt (frontier) (rule) (receipt)
      (eligible : rule ∈ frontier.eligible)
      (pending : frontier.status rule = .pending)
      (exact : receipt = rootsFor global rule) :
      CandidateStep global frontier
        (frontier.setStatus rule (.incomplete receipt))
  | resume (frontier) (rule)
      (eligible : rule ∈ frontier.eligible)
      (incomplete : ∃ receipt, frontier.status rule = .incomplete receipt) :
      CandidateStep global frontier
        (frontier.setStatus rule .pending)

omit [DecidableEq Source] [DecidableEq Producer] [DecidableEq ExpectedType]
    [DecidableEq Occurrence] [DecidableEq Outcome] [DecidableEq Publication]
    [DecidableEq Answer] [DecidableEq Fault] in
theorem accept_refute_independent_diamond
    (global : CoreStateT)
    (frontier : CandidateFrontier Rule Event Answer Fault)
    {acceptedRule refutedRule : Rule}
    (distinct : acceptedRule ≠ refutedRule)
    (answer : Answer) (acceptedReceipt refutedReceipt : Finset Event)
    (acceptedEligible : acceptedRule ∈ frontier.eligible)
    (refutedEligible : refutedRule ∈ frontier.eligible)
    (acceptedPending : frontier.status acceptedRule = .pending)
    (refutedPending : frontier.status refutedRule = .pending)
    (acceptedExact : acceptedReceipt = rootsFor global acceptedRule)
    (refutedExact : refutedReceipt = rootsFor global refutedRule) :
    let acceptedFirst :=
      frontier.setStatus acceptedRule (.accepted answer acceptedReceipt)
    let refutedFirst :=
      frontier.setStatus refutedRule (.refuted refutedReceipt)
    ∃ final,
      CandidateStep global frontier acceptedFirst ∧
      CandidateStep global acceptedFirst final ∧
      CandidateStep global frontier refutedFirst ∧
      CandidateStep global refutedFirst final := by
  let acceptedFirst :=
    frontier.setStatus acceptedRule (.accepted answer acceptedReceipt)
  let refutedFirst :=
    frontier.setStatus refutedRule (.refuted refutedReceipt)
  let final := acceptedFirst.setStatus refutedRule (.refuted refutedReceipt)
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · exact CandidateStep.accept frontier acceptedRule answer acceptedReceipt
      acceptedEligible acceptedPending acceptedExact
  · apply CandidateStep.refute acceptedFirst refutedRule refutedReceipt
    · exact refutedEligible
    · rw [show acceptedFirst.status refutedRule =
          frontier.status refutedRule by
        exact frontier.status_setStatus_of_ne distinct.symm
          (.accepted answer acceptedReceipt)]
      exact refutedPending
    · exact refutedExact
  · exact CandidateStep.refute frontier refutedRule refutedReceipt
      refutedEligible refutedPending refutedExact
  · rw [show final =
        refutedFirst.setStatus acceptedRule
          (.accepted answer acceptedReceipt) by
      exact frontier.setStatus_comm distinct
        (.accepted answer acceptedReceipt) (.refuted refutedReceipt)]
    apply CandidateStep.accept refutedFirst acceptedRule answer acceptedReceipt
    · exact acceptedEligible
    · rw [show refutedFirst.status acceptedRule =
          frontier.status acceptedRule by
        exact frontier.status_setStatus_of_ne distinct
          (.refuted refutedReceipt)]
      exact acceptedPending
    · exact acceptedExact

def ExactResidual
    (frontier : CandidateFrontier Rule Event Answer Fault) : Prop :=
  frontier.eligible.Nonempty ∧
    ∀ rule ∈ frontier.eligible,
      ∃ receipt, frontier.status rule = .refuted receipt

omit [DecidableEq Rule] [DecidableEq Event] [DecidableEq Answer]
    [DecidableEq Fault] in
theorem ExactResidual.eligible_nonempty
    {frontier : CandidateFrontier Rule Event Answer Fault}
    (residual : ExactResidual frontier) :
    frontier.eligible.Nonempty :=
  residual.1

omit [DecidableEq Rule] [DecidableEq Event] [DecidableEq Answer]
    [DecidableEq Fault] in
theorem ExactResidual.refutes
    {frontier : CandidateFrontier Rule Event Answer Fault}
    (residual : ExactResidual frontier)
    {rule : Rule} (eligible : rule ∈ frontier.eligible) :
    ∃ receipt, frontier.status rule = .refuted receipt :=
  residual.2 rule eligible

omit [DecidableEq Rule] [DecidableEq Event] [DecidableEq Answer]
    [DecidableEq Fault] in
theorem not_exactResidual_of_status_ne_refuted
    {frontier : CandidateFrontier Rule Event Answer Fault}
    {rule : Rule} (eligible : rule ∈ frontier.eligible)
    (notRefuted : ∀ receipt, frontier.status rule ≠ .refuted receipt) :
    ¬ ExactResidual frontier := by
  intro residual
  rcases residual.refutes eligible with ⟨receipt, refuted⟩
  exact notRefuted receipt refuted

omit [DecidableEq Rule] [DecidableEq Event] [DecidableEq Answer]
    [DecidableEq Fault] in
theorem pending_blocks_exactResidual
    {frontier : CandidateFrontier Rule Event Answer Fault}
    {rule : Rule} (eligible : rule ∈ frontier.eligible)
    (pending : frontier.status rule = .pending) :
    ¬ ExactResidual frontier := by
  apply not_exactResidual_of_status_ne_refuted eligible
  intro receipt refuted
  rw [pending] at refuted
  cases refuted

omit [DecidableEq Rule] [DecidableEq Event] [DecidableEq Answer]
    [DecidableEq Fault] in
theorem incomplete_blocks_exactResidual
    {frontier : CandidateFrontier Rule Event Answer Fault}
    {rule : Rule} (eligible : rule ∈ frontier.eligible)
    {receipt : Finset Event}
    (incomplete : frontier.status rule = .incomplete receipt) :
    ¬ ExactResidual frontier := by
  apply not_exactResidual_of_status_ne_refuted eligible
  intro other refuted
  rw [incomplete] at refuted
  cases refuted

omit [DecidableEq Rule] [DecidableEq Event] [DecidableEq Answer]
    [DecidableEq Fault] in
theorem accepted_blocks_exactResidual
    {frontier : CandidateFrontier Rule Event Answer Fault}
    {rule : Rule} (eligible : rule ∈ frontier.eligible)
    {answer : Answer} {receipt : Finset Event}
    (accepted : frontier.status rule = .accepted answer receipt) :
    ¬ ExactResidual frontier := by
  apply not_exactResidual_of_status_ne_refuted eligible
  intro other refuted
  rw [accepted] at refuted
  cases refuted

omit [DecidableEq Rule] [DecidableEq Event] [DecidableEq Answer]
    [DecidableEq Fault] in
theorem stableFault_blocks_exactResidual
    {frontier : CandidateFrontier Rule Event Answer Fault}
    {rule : Rule} (eligible : rule ∈ frontier.eligible)
    {fault : Fault} {receipt : Finset Event}
    (faulted : frontier.status rule = .stableFault fault receipt) :
    ¬ ExactResidual frontier := by
  apply not_exactResidual_of_status_ne_refuted eligible
  intro other refuted
  rw [faulted] at refuted
  cases refuted

def frontierFromDeclarations
    (rules : List Rule)
    (status : Rule → CandidateStatus Event Answer Fault) :
    CandidateFrontier Rule Event Answer Fault :=
  { eligible := rules.toFinset, status := status }

omit [DecidableEq Event] [DecidableEq Answer] [DecidableEq Fault] in
theorem frontierFromDeclarations_perm
    {left right : List Rule} (permutation : left.Perm right)
    (status : Rule → CandidateStatus Event Answer Fault) :
    frontierFromDeclarations left status = frontierFromDeclarations right status := by
  simp [frontierFromDeclarations,
    List.toFinset_eq_of_perm left right permutation]

omit [DecidableEq Event] [DecidableEq Answer] [DecidableEq Fault] in
theorem distinct_rule_occurrences_are_retained
    {left right : Rule} (distinct : left ≠ right)
    (status : Rule → CandidateStatus Event Answer Fault) :
    (frontierFromDeclarations [left, right] status).eligible.card = 2 := by
  simp [frontierFromDeclarations, distinct]

structure ApplicationState where
  core : CoreStateT
  frontier : CandidateFrontier Rule Event Answer Fault

inductive ApplicationStep
    (model : Model Producer Occurrence Outcome Event) :
    ApplicationState → ApplicationState → Prop where
  | core {before after : CoreStateT}
      (frontier : CandidateFrontier Rule Event Answer Fault)
      (step : Step model before after) :
      ApplicationStep model
        { core := before, frontier := frontier }
        { core := after, frontier := frontier }
  | candidate (core : CoreStateT)
      {before after : CandidateFrontier Rule Event Answer Fault}
      (step : CandidateStep core before after) :
      ApplicationStep model
        { core := core, frontier := before }
        { core := core, frontier := after }

omit [DecidableEq Fault] in
theorem candidate_step_preserves_core
    {model : Model Producer Occurrence Outcome Event}
    {core : CoreStateT}
    {before after : CandidateFrontier Rule Event Answer Fault}
    (step : CandidateStep core before after) :
    ApplicationStep model
      { core := core, frontier := before }
      { core := core, frontier := after } :=
  ApplicationStep.candidate core step

omit [DecidableEq Fault] in
theorem core_step_preserves_frontier
    {model : Model Producer Occurrence Outcome Event}
    {before after : CoreStateT}
    (frontier : CandidateFrontier Rule Event Answer Fault)
    (step : Step model before after) :
    ApplicationStep model
      { core := before, frontier := frontier }
      { core := after, frontier := frontier } :=
  ApplicationStep.core frontier step

end Mettapedia.Languages.MeTTa.PrimeCellCausalFrontier
