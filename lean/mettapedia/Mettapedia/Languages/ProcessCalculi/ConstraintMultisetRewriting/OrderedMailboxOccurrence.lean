import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedMailboxComputation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences

/-!
# Ordered mailbox receives as prepared occurrence firings

One occurrence contains the complete ordered queue. A pure first-match scan
prepares an ordinary rule that takes this occurrence and makes a residual
queue and a delivered result. The exact queue occurrence is revalidated by
the atomic firing; a prepared result cannot commit after it has been taken.

The cell values in this interface are closed data. Accordingly its equation
profile is rigid equality, with no logic variables or binding effects. The
computation-to-rule adapter is explicit: ordinary multiset rewriting does
not evaluate an arbitrary selector by itself. The selector's language-level
implementation, progress while no message matches, and native publication
refinement are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedMailboxOccurrence

open Mettapedia.Languages.Erlang
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open OrderedMailboxComputation

variable {α β : Type*}

/-- Order is retained inside one queue cell; equal messages are distinct list
positions. Delivered values are separate output occurrences. -/
inductive Cell (α β : Type*) where
  | queue (messages : List α)
  | delivered (result : β)
  deriving DecidableEq

/-- The closed-data profile has no substitution choices. This is the explicit
ground boundary of this adapter, not a model of open-message unification. -/
def closedAction : SubstitutionAction (Cell α β) Unit where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := fun _ cell => cell
  identity := ⟨⟩
  compose := fun _ _ => ⟨⟩
  apply_identity := fun _ => rfl
  apply_compose := fun _ _ _ => rfl
  preserves := fun _ {_ _} equation => equation

abbrev Occurrence (α β : Type*) := IndexedOccurrences.Occurrence (Cell α β)

def label : Occurrence α β → Cell α β := IndexedOccurrences.label

def receiveRule (messages : List α) (result : β) (remaining : List α) :
    RuleInstance (Cell α β) where
  take := [.queue messages]
  read := []
  tell := []
  checks := []
  produce := [.queue remaining, .delivered result]

/-- Preparation performs the verified pure scan. Failure produces no rule;
success makes the computed residual queue and value explicit rule outputs. -/
def prepare (select : α → Option β) : Cell α β → Option (RuleInstance (Cell α β))
  | .queue messages =>
      (compute select messages).map fun pair => receiveRule messages pair.1 pair.2
  | .delivered _ => none

theorem prepare_some {select : α → Option β} {cell : Cell α β}
    {rule : RuleInstance (Cell α β)} (prepared : prepare select cell = some rule) :
    ∃ messages result remaining, cell = .queue messages ∧
      compute select messages = some (result, remaining) ∧
      rule = receiveRule messages result remaining := by
  cases cell with
  | delivered result => simp [prepare] at prepared
  | queue messages =>
      cases computed : compute select messages with
      | none => simp [prepare, computed] at prepared
      | some pair =>
          obtain ⟨result, remaining⟩ := pair
          refine ⟨messages, result, remaining, rfl, computed, ?_⟩
          simpa [prepare, computed] using prepared.symm

section Occurrences

variable [DecidableEq α] [DecidableEq β]

/-- An actual selected firing with its output observation. No source receive
relation is a field: the source result is recovered from preparation, output
agreement, and the separately verified scanner. -/
def Fires (select : α → Option β) (before : Configuration (Cell α β) (Occurrence α β))
    (queue : Occurrence α β) (result : β) (remaining : List α)
    (after : Configuration (Cell α β) (Occurrence α β)) : Prop :=
  ∃ (rule : RuleInstance (Cell α β)) (selection : Selection (Occurrence α β)),
    prepare select (label queue) = some rule ∧
    selection.taken = [queue] ∧
    selection.Valid closedAction label rule before ∧
    selection.made.map label = [.queue remaining, .delivered result] ∧
    after = selection.result label rule before

theorem Fires.ordinary_step {select : α → Option β}
    {before after : Configuration (Cell α β) (Occurrence α β)}
    {queue : Occurrence α β} {result : β} {remaining : List α}
    (firing : Fires select before queue result remaining after) :
    ∃ rule, prepare select (label queue) = some rule ∧
      Step closedAction label rule before after := by
  obtain ⟨rule, selection, prepared, _, valid, _, endpoint⟩ := firing
  exact ⟨rule, prepared, selection, valid, endpoint⟩

theorem Fires.no_invention {select : α → Option β}
    {before after : Configuration (Cell α β) (Occurrence α β)}
    {queue : Occurrence α β} {result : β} {remaining : List α}
    (firing : Fires select before queue result remaining after) :
    ∃ messages, label queue = .queue messages ∧
      Mailbox.selectFirst select messages = some (result, remaining) := by
  obtain ⟨rule, selection, prepared, _, valid, observed, _⟩ := firing
  obtain ⟨messages, selected, rest, input, computed, rfl⟩ := prepare_some prepared
  have outputs : ([Cell.queue rest, Cell.delivered selected] : List (Cell α β)) =
      [.queue remaining, .delivered result] := valid.outputs.symm.trans observed
  have restEq : rest = remaining := Cell.queue.inj (List.cons.inj outputs).1
  have resultEq : selected = result :=
    Cell.delivered.inj (List.cons.inj (List.cons.inj outputs).2).1
  subst rest selected
  exact ⟨messages, input, (compute_eq_selectFirst select messages).symm.trans computed⟩

theorem Fires.queue_present {select : α → Option β}
    {before after : Configuration (Cell α β) (Occurrence α β)}
    {queue : Occurrence α β} {result : β} {remaining : List α}
    (firing : Fires select before queue result remaining after) :
    queue ∈ before.present := by
  obtain ⟨_, selection, _, taken, valid, _, _⟩ := firing
  apply valid.occurrences.taken_subset
  simp [Selection.commit, taken]

theorem Fires.queue_consumed {select : α → Option β}
    {before after : Configuration (Cell α β) (Occurrence α β)}
    {queue : Occurrence α β} {result : β} {remaining : List α}
    (firing : Fires select before queue result remaining after) :
    queue ∉ after.present := by
  obtain ⟨_, selection, _, taken, valid, _, rfl⟩ := firing
  exact valid.consumed_removed (by simp [taken])

/-- The actual frame is unchanged. Exactly two distinct fresh occurrences
are made, and the old queue occurrence is removed. -/
theorem Fires.exact_result {select : α → Option β}
    {before after : Configuration (Cell α β) (Occurrence α β)}
    {queue : Occurrence α β} {result : β} {remaining : List α}
    (firing : Fires select before queue result remaining after) :
    ∃ queueOut resultOut : Occurrence α β,
      label queueOut = .queue remaining ∧ label resultOut = .delivered result ∧
      queueOut ≠ resultOut ∧ queueOut ∉ before.present ∧ resultOut ∉ before.present ∧
      after.present = before.present.erase queue ∪ {queueOut, resultOut} := by
  obtain ⟨_, selection, _, taken, valid, observed, rfl⟩ := firing
  obtain ⟨queueOut, later, madeEq, atQueue, laterObserved⟩ := List.map_eq_cons_iff.mp observed
  obtain ⟨resultOut, laterEq, atResult⟩ := List.map_eq_singleton_iff.mp laterObserved
  subst later
  have distinct : queueOut ≠ resultOut := by simpa [madeEq] using valid.output_distinct
  have fresh : ∀ occurrence ∈ selection.made, occurrence ∉ before.present := by
    intro occurrence made old
    exact Finset.disjoint_left.mp valid.occurrences.fresh
      (by simpa [Selection.commit] using made) old
  refine ⟨queueOut, resultOut, atQueue, atResult, distinct,
    fresh _ (by simp [madeEq]), fresh _ (by simp [madeEq]), ?_⟩
  simp [Selection.result, Selection.commit, fire, taken, madeEq,
    Finset.sdiff_singleton_eq_erase]

/-- The selected physical queue is the only queue-state cell. Other cells
may hold an arbitrary frame of previously delivered results. -/
def QueueState (world : Finset (Occurrence α β)) (queue : Occurrence α β)
    (messages : List α) : Prop :=
  queue ∈ world ∧ label queue = .queue messages ∧
    ∀ occurrence ∈ world, ∀ other, label occurrence = .queue other → occurrence = queue

theorem Fires.preserves_unique_queue {select : α → Option β}
    {before after : Configuration (Cell α β) (Occurrence α β)}
    {queue : Occurrence α β} {result : β} {messages remaining : List α}
    (state : QueueState before.present queue messages)
    (firing : Fires select before queue result remaining after) :
    ∃ queueOut, QueueState after.present queueOut remaining := by
  obtain ⟨queueOut, resultOut, atQueue, atResult, _, _, _, endpoint⟩ := firing.exact_result
  refine ⟨queueOut, ?_, atQueue, ?_⟩
  · rw [endpoint]
    simp
  · intro occurrence present other asQueue
    rw [endpoint] at present
    rcases Finset.mem_union.mp present with old | made
    · have oldParts := Finset.mem_erase.mp old
      exact False.elim (oldParts.1 (state.2.2 occurrence oldParts.2 other asQueue))
    · have alternatives : occurrence = queueOut ∨ occurrence = resultOut := by simpa using made
      rcases alternatives with equal | rfl
      · exact equal
      · rw [atResult] at asQueue
        cases asQueue

/-- A saved preparation is invalidated by consuming its exact input
occurrence, even when an equal queue value is later republished elsewhere. -/
theorem no_stale_firing {select : α → Option β}
    {before after : Configuration (Cell α β) (Occurrence α β)}
    {queue : Occurrence α β} {result : β} {remaining : List α}
    (absent : queue ∉ before.present) :
    ¬ Fires select before queue result remaining after :=
  fun firing => absent firing.queue_present

theorem source_has_firing (select : α → Option β)
    (before : Configuration (Cell α β) (Occurrence α β))
    (queue : Occurrence α β) (messages : List α) (result : β) (remaining : List α)
    (present : queue ∈ before.present) (input : label queue = .queue messages)
    (background : closedAction.Consistent before.equations)
    (source : Mailbox.selectFirst select messages = some (result, remaining)) :
    ∃ after, Fires select before queue result remaining after := by
  obtain ⟨queueOut, queueFresh, queueLabel⟩ :=
    IndexedOccurrences.supply before.present (Cell.queue remaining : Cell α β)
  obtain ⟨resultOut, resultFresh, resultLabel⟩ :=
    IndexedOccurrences.supply (insert queueOut before.present) (Cell.delivered result)
  have resultFreshOld : resultOut ∉ before.present :=
    fun member => resultFresh (Finset.mem_insert_of_mem member)
  have distinct : queueOut ≠ resultOut := by
    intro equal
    apply resultFresh
    simp [← equal]
  let selection : Selection (Occurrence α β) := ⟨[queue], [], [queueOut, resultOut]⟩
  let rule := receiveRule messages result remaining
  have valid : selection.Valid closedAction label rule before := by
    refine ⟨by simp [selection], by simp [selection, distinct], rfl, rfl, ?_, ?_, ?_, ?_⟩
    · exact congrArg₂ (fun one two : Cell α β => [one, two]) queueLabel resultLabel
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [Selection.commit, selection] using present
      · simp [Selection.commit, selection]
      · simp [Selection.commit, selection]
      · apply Finset.disjoint_left.mpr
        intro occurrence made old
        have alternatives : occurrence = queueOut ∨ occurrence = resultOut := by
          simpa [Selection.commit, selection] using made
        rcases alternatives with rfl | rfl
        · exact queueFresh old
        · exact resultFreshOld old
      · intro query member
        cases member
    · obtain ⟨assignment, models⟩ := background
      refine ⟨assignment, ?_⟩
      have extra : closedAction.Models assignment [(Cell.queue messages, label queue)] := by
        simp [SubstitutionAction.Models, SubstitutionAction.Solves, closedAction, input]
      simpa [Selection.problem, Selection.equations, selection, rule, receiveRule] using
        (closedAction.models_append assignment _ _).mpr ⟨models, extra⟩
    · intro check member
      cases member
  refine ⟨selection.result label rule before, rule, selection, ?_, rfl, valid, ?_, rfl⟩
  · simp [prepare, input, compute_eq_selectFirst, source, rule]
  · exact valid.outputs

/-- Exact source correspondence for the explicit ordered-state representation,
with an arbitrary consistent untouched frame. Fresh outputs are constructed. -/
theorem source_iff_firing (select : α → Option β)
    (before : Configuration (Cell α β) (Occurrence α β))
    (queue : Occurrence α β) (messages : List α) (result : β) (remaining : List α)
    (present : queue ∈ before.present) (input : label queue = .queue messages)
    (background : closedAction.Consistent before.equations) :
    Mailbox.selectFirst select messages = some (result, remaining) ↔
      ∃ after, Fires select before queue result remaining after := by
  constructor
  · exact source_has_firing select before queue messages result remaining present input background
  · rintro ⟨after, firing⟩
    obtain ⟨other, atQueue, source⟩ := firing.no_invention
    have equal : other = messages := Cell.queue.inj (atQueue.symm.trans input)
    simpa [equal] using source

/-- Actual firings compose on the fresh residual queue. The next operation
uses the resulting physical configuration and its consistent equation store. -/
theorem Fires.continue {select : α → Option β}
    {before middle : Configuration (Cell α β) (Occurrence α β)}
    {queue : Occurrence α β} {result : β} {remaining : List α}
    (first : Fires select before queue result remaining middle)
    (nextSelect : α → Option β) (nextResult : β) (nextRemaining : List α)
    (nextSource : Mailbox.selectFirst nextSelect remaining = some (nextResult, nextRemaining)) :
    ∃ nextQueue after, label nextQueue = .queue remaining ∧
      Fires nextSelect middle nextQueue nextResult nextRemaining after := by
  obtain ⟨nextQueue, delivered, atQueue, _, _, _, _, endpoint⟩ := first.exact_result
  obtain ⟨_, _, ordinary⟩ := first.ordinary_step
  have present : nextQueue ∈ middle.present := by rw [endpoint]; simp
  obtain ⟨after, firing⟩ := source_has_firing nextSelect middle nextQueue remaining
    nextResult nextRemaining present atQueue ordinary.consistent nextSource
  exact ⟨nextQueue, after, atQueue, firing⟩

theorem no_match_no_firing (select : α → Option β)
    (before after : Configuration (Cell α β) (Occurrence α β))
    (queue : Occurrence α β) (messages : List α) (result : β) (remaining : List α)
    (input : label queue = .queue messages)
    (noneMatches : ∀ message ∈ messages, select message = none) :
    ¬ Fires select before queue result remaining after := by
  intro firing
  obtain ⟨other, atQueue, source⟩ := firing.no_invention
  have equal : other = messages := Cell.queue.inj (atQueue.symm.trans input)
  subst other
  have none := (Mailbox.selectFirst_none_iff select messages).mpr noneMatches
  rw [none] at source
  cases source

/-- Under the declared representation invariants, refusal is exactly source
no-match. Resource absence or an inconsistent background are not misreported
as a source no-match. -/
theorem source_none_iff_no_firing (select : α → Option β)
    (before : Configuration (Cell α β) (Occurrence α β))
    (queue : Occurrence α β) (messages : List α)
    (present : queue ∈ before.present) (input : label queue = .queue messages)
    (background : closedAction.Consistent before.equations) :
    Mailbox.selectFirst select messages = none ↔
      ∀ result remaining after, ¬ Fires select before queue result remaining after := by
  constructor
  · intro noMatch result remaining after
    exact no_match_no_firing select before after queue messages result remaining input
      ((Mailbox.selectFirst_none_iff select messages).mp noMatch)
  · intro noFiring
    cases source : Mailbox.selectFirst select messages with
    | none => rfl
    | some pair =>
        obtain ⟨result, remaining⟩ := pair
        obtain ⟨after, firing⟩ := source_has_firing select before queue messages result
          remaining present input background source
        exact False.elim (noFiring result remaining after firing)

/-- Fresh occurrence choices may differ, but the selected value and residual
ordered queue are determined by the source computation. -/
theorem Fires.same_visible_result {select : α → Option β}
    {before afterOne afterTwo : Configuration (Cell α β) (Occurrence α β)}
    {queue : Occurrence α β} {resultOne resultTwo : β} {restOne restTwo : List α}
    (first : Fires select before queue resultOne restOne afterOne)
    (second : Fires select before queue resultTwo restTwo afterTwo) :
    resultOne = resultTwo ∧ restOne = restTwo := by
  obtain ⟨messages, atQueue, source⟩ := first.no_invention
  obtain ⟨otherMessages, atOther, otherSource⟩ := second.no_invention
  have sameInput : otherMessages = messages := Cell.queue.inj (atOther.symm.trans atQueue)
  subst otherMessages
  exact Prod.mk.inj (Option.some.inj (source.symm.trans otherSource))

end Occurrences

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedMailboxOccurrence
