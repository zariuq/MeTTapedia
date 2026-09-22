import Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

/-!
# Handled ground-binding conflicts

A rejected proposal need not discard the context in which it was made.
This module connects an explicitly handled update to the existing ground
refinement semantics: acceptance commits a real refinement; rejection leaves
the original store unchanged. A handler can then continue using that store,
without establishing the rejected assignment.

`tryBind` uses the existing conflict-observing step once. The ordinary
`refineStep` and `refineRun` remain unchanged, and a conflicting conjunction
still has no solution. This is an optional control-flow interpretation, not
mandatory diagnostics, history retention, or a non-ground unification theory.
The laws constrain dispatch and store updates, not arbitrary claims returned
by a user-supplied handler.
-/

namespace Mettapedia.TypeTheory.ContextualBindingConflict

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

variable {N V : Type*}

/-- An update result keeps rejection distinct from successful refinement. -/
inductive UpdateResult (N V : Type*) where
  | accepted (store : Store N V)
  | rejected (store : Store N V) (name : N) (old proposed : V)

/-- The context available after handling the update. -/
def UpdateResult.store : UpdateResult N V → Store N V
  | .accepted s => s
  | .rejected s _ _ _ => s

/-- Only the accepted branch is a solution of the proposed refinement. -/
def UpdateResult.acceptedStore : UpdateResult N V → Option (Store N V)
  | .accepted s => some s
  | .rejected _ _ _ _ => none

/-- Dispatch to distinct success and rejection continuations. -/
def UpdateResult.handle {α : Type*} (result : UpdateResult N V)
    (onAccepted : Store N V → α)
    (onRejected : Store N V → N → V → V → α) : α :=
  match result with
  | .accepted s => onAccepted s
  | .rejected s n old proposed => onRejected s n old proposed

variable [DecidableEq N] [DecidableEq V]

/-- Try one ground proposal, preserving the input store on rejection.
The existing observer performs the refinement decision once. -/
def tryBind (s : Store N V) (proposal : N × V) : UpdateResult N V :=
  match observeStep s proposal with
  | .ok t => .accepted t
  | .conflict n old proposed => .rejected s n old proposed

/-- Acceptance is exactly acceptance by the original refinement step. -/
theorem tryBind_accepted_iff {s t : Store N V} {proposal : N × V} :
    tryBind s proposal = .accepted t ↔ refineStep s proposal = some t := by
  rw [← observeStep_ok_iff]
  unfold tryBind
  cases observeStep s proposal <;> simp

/-- Rejection records an actual conflicting lookup and preserves its context. -/
theorem tryBind_rejected_iff {s t : Store N V} {proposal : N × V}
    {n : N} {old proposed : V} :
    tryBind s proposal = .rejected t n old proposed ↔
      t = s ∧ n = proposal.1 ∧ s proposal.1 = some old ∧
        proposed = proposal.2 ∧ old ≠ proposed := by
  unfold tryBind
  cases h : observeStep s proposal with
  | ok u =>
      have success := observeStep_ok_iff.mp h
      constructor
      · intro impossible; cases impossible
      · rintro ⟨same, rfl, lookup, rfl, different⟩
        subst t
        have failure : refineStep s proposal = none := by
          simp [refineStep, lookup, different]
        rw [failure] at success
        cases success
  | conflict name previous next =>
      obtain ⟨_, nameEq, lookup, nextEq, different⟩ :=
        observeStep_conflict_iff.mp h
      constructor
      · intro equality
        cases equality
        exact ⟨rfl, nameEq, lookup, nextEq, different⟩
      · rintro ⟨rfl, rfl, lookup', rfl, _⟩
        have previousEq : previous = old := Option.some.inj (lookup.symm.trans lookup')
        cases nameEq
        cases nextEq
        cases previousEq
        rfl

/-- Erasing the handling branch recovers the ordinary refinement answer,
not the store retained for recovery. -/
theorem tryBind_acceptedStore_eq (s : Store N V) (proposal : N × V) :
    (tryBind s proposal).acceptedStore = refineStep s proposal := by
  cases h : tryBind s proposal with
  | accepted t =>
      rw [tryBind_accepted_iff.mp h]
      rfl
  | rejected t n old proposed =>
      obtain ⟨_, _, lookup, nextEq, different⟩ := tryBind_rejected_iff.mp h
      simp [UpdateResult.acceptedStore, refineStep, lookup, ← nextEq, different]

/-- Both acceptance and handled rejection preserve every old binding. -/
theorem tryBind_preserves_store (s : Store N V) (proposal : N × V) :
    Store.LE s (tryBind s proposal).store := by
  cases h : tryBind s proposal with
  | accepted t => exact refineStep_mono (tryBind_accepted_iff.mp h)
  | rejected t n old proposed =>
      obtain ⟨rfl, _⟩ := tryBind_rejected_iff.mp h
      exact Store.LE.refl _

/-- The successful branch establishes the proposed binding. -/
theorem accepted_establishes_proposal {s t : Store N V} {proposal : N × V}
    (accepted : tryBind s proposal = .accepted t) :
    t proposal.1 = some proposal.2 :=
  refineStep_binds (tryBind_accepted_iff.mp accepted)

/-- A handled rejection still does not establish the rejected binding. -/
theorem rejected_does_not_establish_proposal {s t : Store N V}
    {proposal : N × V} {n : N} {old proposed : V}
    (rejected : tryBind s proposal = .rejected t n old proposed) :
    t proposal.1 ≠ some proposal.2 := by
  obtain ⟨rfl, _, lookup, rfl, different⟩ := tryBind_rejected_iff.mp rejected
  rw [lookup]
  exact fun equality => different (Option.some.inj equality)

/-- Conflict is more than failure of this implementation: no information-
preserving extension of the old store can satisfy the proposed assignment. -/
theorem rejected_has_no_compatible_extension {s t : Store N V}
    {proposal : N × V} {n : N} {old proposed : V}
    (rejected : tryBind s proposal = .rejected t n old proposed) :
    ¬ ∃ u : Store N V, Store.LE s u ∧ u proposal.1 = some proposal.2 := by
  obtain ⟨_, _, lookup, rfl, different⟩ := tryBind_rejected_iff.mp rejected
  rintro ⟨u, monotone, proposedLookup⟩
  exact different (Option.some.inj ((monotone _ _ lookup).symm.trans proposedLookup))

/-- An ordinary success continuation runs only after real refinement. -/
def bindThen {α : Type*} (s : Store N V) (proposal : N × V)
    (next : Store N V → Option α) : Option α :=
  (refineStep s proposal).bind next

/-- Calling a rejection handler does not make the ordinary success path run. -/
theorem rejected_bindThen_eq_none {α : Type*} {s t : Store N V}
    {proposal : N × V} {n : N} {old proposed : V}
    (rejected : tryBind s proposal = .rejected t n old proposed)
    (next : Store N V → Option α) :
    bindThen s proposal next = none := by
  have failure : refineStep s proposal = none := by
    rw [← tryBind_acceptedStore_eq, rejected]
    rfl
  simp [bindThen, failure]

/-- A handled conflict passes the original context to the rejection branch. -/
theorem rejected_handle_eq {α : Type*} {s t : Store N V}
    {proposal : N × V} {n : N} {old proposed : V}
    (rejected : tryBind s proposal = .rejected t n old proposed)
    (onAccepted : Store N V → α)
    (onRejected : Store N V → N → V → V → α) :
    (tryBind s proposal).handle onAccepted onRejected =
      onRejected s n old proposed := by
  have original := (tryBind_rejected_iff.mp rejected).1
  rw [rejected, original]
  rfl

/-- Continue with ordinary refinements after explicitly handling an update.
The caller retains the update result separately if its status is needed. -/
def continueAfterTry (result : UpdateResult N V) (steps : Steps N V) :
    Option (Store N V) :=
  refineRun result.store steps

/-- Later successful work preserves bindings from before the handled update,
including when the update itself was rejected. -/
theorem continuation_preserves_old_bindings {s t : Store N V}
    {proposal : N × V} {steps : Steps N V}
    (continued : continueAfterTry (tryBind s proposal) steps = some t) :
    Store.LE s t :=
  (tryBind_preserves_store s proposal).trans (refineRun_mono continued)

/-- Recovery followed by successful refinement cannot turn the conflicting
proposal into a true binding. -/
theorem continuation_does_not_establish_rejected {s t u : Store N V}
    {proposal : N × V} {steps : Steps N V} {n : N} {old proposed : V}
    (rejected : tryBind s proposal = .rejected t n old proposed)
    (continued : continueAfterTry (tryBind s proposal) steps = some u) :
    u proposal.1 ≠ some proposal.2 := by
  intro proposedLookup
  exact rejected_has_no_compatible_extension rejected
    ⟨u, continuation_preserves_old_bindings continued, proposedLookup⟩

/-! ## Ground controls -/

/-- A context already containing `x = a`. -/
def exampleStore : Store String String :=
  fun n => if n = "x" then some "a" else none

/-- A genuinely new name is committed without changing the old name. -/
theorem fresh_proposal_succeeds :
    (tryBind exampleStore ("y", "b")).acceptedStore.map
      (fun s => (s "x", s "y")) = some (some "a", some "b") := by
  rfl

/-- Repeating the existing assignment is accepted, not reported as a conflict. -/
theorem agreeing_proposal_succeeds :
    tryBind exampleStore ("x", "a") = .accepted exampleStore := by
  rfl

/-- A conflicting proposal reports rejection with the original store. -/
theorem conflicting_proposal_rejected :
    tryBind exampleStore ("x", "b") =
      .rejected exampleStore "x" "a" "b" := by
  rfl

/-- A handler returns the retained value; that is not success of `x = b`.
The ordinary conflicting conjunction and its success path remain empty. -/
theorem conjunction_fails_while_handler_continues :
    solveConj ([("x", "a"), ("x", "b")] : Steps String String) = none ∧
    bindThen exampleStore ("x", "b") (fun s => s "x") = none ∧
    (tryBind exampleStore ("x", "b")).handle
      (fun s => s "x") (fun s _ _ _ => s "x") = some "a" ∧
    (tryBind exampleStore ("x", "b")).acceptedStore = none := by
  exact ⟨shadow_breaks_conj.1, rfl, rfl, rfl⟩

/-- Recovery may do useful new work while the old assignment stays intact. -/
theorem recovery_can_bind_another_name :
    (continueAfterTry (tryBind exampleStore ("x", "b")) [("y", "c")]).map
      (fun s => (s "x", s "y")) = some (some "a", some "c") := by
  rfl

/-- Retrying the incompatible assignment as an ordinary continuation fails. -/
theorem recovery_cannot_smuggle_rejected_binding :
    continueAfterTry (tryBind exampleStore ("x", "b")) [("x", "b")] = none := by
  rfl

end Mettapedia.TypeTheory.ContextualBindingConflict
