import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchPreparation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedGuardedCandidateBatch

/-!
# Checked source match entry with current-world capture

The worker performs handle preparation and a complete live capture. A later
admission refusal retains the reached invocation, including its new handle
equation. Its proof is assembled from source steps, not from running the
reference machine. Captured controls retain their exact body-head shape.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)

variable {Context : Type}

def entrance (body destination : Atom) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) : ScopedCursor Context :=
  ClosedOnceQueryFrame.placed state.allocator state.world state.scope state.parents
    {caller with goals := .evaluate body destination :: caller.goals} context origins pending

structure Selection (body destination : Atom) (older : List Goal) where
  choices : List (Nat × Control)
  shape : ∀ entry ∈ choices, entry.2.goals = .evaluate body destination :: older

inductive Result (Context : Type) (body destination : Atom) (older : List Goal) where
  | reference (saved : ScopedCursor Context)
  | captured (selected : Selection body destination older)

def Result.observation {body destination : Atom} {older : List Goal}
    (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) :
    Result Context body destination older →
      List CollectedAnswer × Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary
  | .reference saved => ([], .exhausted saved)
  | .captured selected => ([], .exhausted (state.cursor (ScopedQuerySource.work context origins selected.choices ++ pending)))

structure Receipt (program : SpaceSemantics.Program) (handle : NamedSpaces.Handle) (pattern body destination : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) where
  budget : Nat
  result : Result Context body destination caller.goals
  exact : (ScopedQuerySource.machine .relational program).run budget
    (entrance (ScopedMatchPreparation.source handle pattern body) destination caller state context origins pending) =
      result.observation state context origins pending

/-- Pure admission may refuse at the entrance. Once preparation is consumed,
all later refusals retain that reached source cursor. -/
def execute (program : SpaceSemantics.Program) (handle : NamedSpaces.Handle) (pattern body destination : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) :
    Receipt program handle pattern body destination caller state context origins pending :=
  match resolved : resolve caller.bindings with
  | none => ⟨0, .reference (entrance (ScopedMatchPreparation.source handle pattern body) destination caller state context origins pending), rfl⟩
  | some principal =>
    let ready := ScopedMatchPreparation.ready caller destination handle pattern body
    let location := ScopedMatchPreparation.location caller destination handle pattern body
    let saved := ClosedOnceQueryFrame.placed state.allocator state.world state.scope state.parents ready context origins pending
    have prepared := ScopedMatchPreparation.preparation program state.allocator state.world state.scope state.parents
      caller context origins pending destination handle pattern body ⟨principal, resolve_sound resolved⟩
    let defer : Receipt program handle pattern body destination caller state context origins pending :=
      ⟨3, .reference saved, prepared⟩
    match readyResolved : resolve ready.bindings with
    | none => False.elim (by
      obtain ⟨environment, success⟩ := resolve_complete
        (ScopedMatchPreparation.ready_consistent caller destination handle pattern body ⟨principal, resolve_sound resolved⟩)
      change resolve ready.bindings = some environment at success
      rw [readyResolved] at success
      cases success)
    | some environment =>
      match snapshot : state.world.state.read handle with
      | none => defer
      | some rows =>
        if complete : ClosedQueryAdmission.rowsReady (read environment pattern) rows = true then
          if unfused : ScopedQuerySource.fused (read environment pattern) body = false then
            match captured : ScopedQuerySource.capture ready (read environment pattern) body destination caller.goals 0 rows with
            | none => defer
            | some selected =>
              have source := ScopedQuerySource.capture_has_source _ _ _ _ _ _ _ _ captured
              let selection : Selection body destination caller.goals :=
                ⟨selected, fun entry member => (source.frames entry member).2.2.1⟩
              {budget := 4, result := .captured selection, exact := by
                have step := ScopedQuerySource.captured_step .relational program state.allocator state.world
                  {state.scope with frontier := (ready, context, origins) :: pending} state.parents ready context origins pending
                  (.var location) pattern body destination caller.goals environment rows selected rfl rfl readyResolved unfused
                  (by
                    have reading := ScopedMatchPreparation.ready_location caller destination handle pattern body environment readyResolved
                    change read environment (.var location) = Effects.handleValue handle at reading
                    rw [reading, Effects.readHandle_handleValue]
                    exact snapshot) complete source
                have one := (ScopedQuerySource.machine .relational program).run_succ_silent (fuel := 0) step
                have joined := (ScopedQuerySource.machine .relational program).established_and_pending 3 1 _ _ [] prepared
                change (ScopedQuerySource.machine .relational program).run _ _ =
                  ([] ++ ((ScopedQuerySource.machine .relational program).run 1 saved).1,
                    ((ScopedQuerySource.machine .relational program).run 1 saved).2) at joined
                change (ScopedQuerySource.machine .relational program).run 1 saved =
                  ([], .exhausted (state.cursor (ScopedQuerySource.work context origins selected ++ pending))) at one
                rw [one] at joined
                change (ScopedQuerySource.machine .relational program).run 4
                  (entrance (ScopedMatchPreparation.source handle pattern body) destination caller state context origins pending) =
                  ([], .exhausted (state.cursor (ScopedQuerySource.work context origins selected ++ pending)))
                simpa only [List.nil_append, entrance, ScopedMatchPreparation.entry, Nat.reduceAdd] using joined }
          else defer
        else defer

theorem execute_exact (program : SpaceSemantics.Program) (handle : NamedSpaces.Handle) (pattern body destination : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) :
    (ScopedQuerySource.machine .relational program).run
      (execute program handle pattern body destination caller state context origins pending).budget
      (entrance (ScopedMatchPreparation.source handle pattern body) destination caller state context origins pending) =
      (execute program handle pattern body destination caller state context origins pending).result.observation state context origins pending :=
  (execute program handle pattern body destination caller state context origins pending).exact

/-- Independently established reads and complete matching force the actual
entry worker to return that captured list, rather than a handoff. -/
theorem captured_of_checks (program : SpaceSemantics.Program) (handle : NamedSpaces.Handle) (pattern body destination : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (principal environment : Environment) (rows : List Atom) (selected : List (Nat × Control))
    (resolved : resolve caller.bindings = some principal)
    (prepared : resolve (ScopedMatchPreparation.ready caller destination handle pattern body).bindings = some environment)
    (snapshot : state.world.state.read handle = some rows)
    (complete : ClosedQueryAdmission.rowsReady (read environment pattern) rows = true)
    (unfused : ScopedQuerySource.fused (read environment pattern) body = false)
    (captured : ScopedQuerySource.capture (ScopedMatchPreparation.ready caller destination handle pattern body)
      (read environment pattern) body destination caller.goals 0 rows = some selected) :
    (execute program handle pattern body destination caller state context origins pending).budget = 4 ∧
      ∃ actual, (execute program handle pattern body destination caller state context origins pending).result = .captured actual ∧
        actual.choices = selected := by
  unfold execute
  split
  next absent => simp [resolved] at absent
  next actualPrincipal found =>
    have same := Option.some.inj (found.symm.trans resolved)
    subst actualPrincipal
    dsimp only
    split
    next absent => simp [prepared] at absent
    next actualEnvironment found =>
      have same := Option.some.inj (found.symm.trans prepared)
      subst actualEnvironment
      split
      next absent => simp [snapshot] at absent
      next actualRows found =>
        have same := Option.some.inj (found.symm.trans snapshot)
        subst actualRows
        split
        next ready =>
          split
          next absent => simp [captured] at absent
          next actual found =>
            have same := Option.some.inj (found.symm.trans captured)
            subst actual
            exact ⟨rfl, _, rfl, rfl⟩
        next rejected => exact (rejected complete).elim

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchEntry
