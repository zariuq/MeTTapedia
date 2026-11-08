import Mettapedia.Logic.ASP.Watches
import Mettapedia.Logic.ASP.SourcePointers
import Mettapedia.Logic.ASP.SolverControls

/-!
# Controls for executable propagation

Values are computed by the kernel (`decide`); the `#eval` lines show the executable
operations running.

## Watched literals

* The implications `0 → 1 → 2 → 3` as nogoods `{T 0, F 1}, {T 1, F 2}, {T 2, F 3}`:
  after the decision `T 0`, propagation by watches reaches the fixpoint
  `T 3, T 2, T 1, T 0`; every literal unit propagation derives from `T 0` is on it
  (`implications_closure`).
* Adding `{T 3, T 0}`: propagation pushes `F 3` from it, then `F 2`, and reports
  the falsified nogood `{T 1, F 2}`.
* The completion nogoods of `p :- not p. p :- q.` after the decision `T p`: the
  watches push `T q` by the support nogood `{T p, T p, F q}` of `p` and reach a
  fixpoint; the trail it reaches is reached by solver steps
  (`liarQ_watched_solver`). The support nogood `{T q}` of `q`, which the fixpoint
  violates, is no watched nogood, nor is the nogood `{F p, F p}` of the rule
  `p :- not p`, whose two literals are one: they are left to the scan of short
  nogoods.
* A negative control: a nogood with one literal has no two watches and is not in
  the watched database; it is handled as a unit at level 0. So are both nogoods of
  `p :- not p.`, the empty nogood of its rule and the unit support nogood `{T p}`
  (`liar_nothing_watched`).

## Source pointers

* `p :- q. q :- p. r :- not p.`: with nothing assigned, the check marks `{p, q}`
  and sources `r`; the reason for `F p` is the loop nogood `{T p}`, and pushing it
  is a solver step.
* `p :- q. q :- p. p :- not r. r :- not p.`: with nothing assigned nothing is
  marked; once `not r` is false, that is once `T r` is assigned, `{p, q}` is marked,
  both from scratch and from the earlier sources, of which `r` is kept.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.PropagationControls

open CheckerControls CheckerControls.Atom SolverControls Program Relation

/-! ## Watched literals -/

/-- `0 → 1 → 2 → 3` as nogoods. -/
def implications : List (Nogood ℕ) :=
  [⟨[tAtom 0, fAtom 1], .learned 0⟩, ⟨[tAtom 1, fAtom 2], .learned 1⟩, ⟨[tAtom 2, fAtom 3], .learned 2⟩]

/-- The watched state after the decision `T 0`. -/
def start : WState ℕ := (WState.init implications []).decide (tAtom 0)

/-- The literals of a fixpoint. -/
def fixpointLits {α : Type} : Outcome α → Option (List (Lit α))
  | .fixpoint st => some st.lits
  | _ => none

/-- The conflict nogood and the trail of a conflict. -/
def conflictOf {α : Type} : Outcome α → Option (List (Lit α) × List (Lit α))
  | .conflict δ st => some (δ.lits, st.lits)
  | _ => none

theorem implications_watchable : watchable implications = implications := by decide

theorem start_inv : WInv (watchable implications) start :=
  (WInv.init implications (t := []) List.nodup_nil fun _ _ => ⟨List.not_mem_nil, List.not_mem_nil⟩).decide rfl
    (by simp [onTrail, State.Assigned, WState.init])

theorem implications_propagate :
    fixpointLits (propagateWatched 10 start) = some [tAtom 3, tAtom 2, tAtom 1, tAtom 0] := by
  decide

/-- **Propagation by watches computes the closure** for the implications. -/
theorem implications_closure :
    ∃ st, propagateWatched 10 start = .fixpoint st ∧ st.lits = [tAtom 3, tAtom 2, tAtom 1, tAtom 0] ∧
      ∀ t', ReflTransGen (UPStep (watchable implications)) start.trail t' →
        ∀ l ∈ t'.map Entry.lit, l ∈ st.trail.map Entry.lit := by
  have computed := implications_propagate
  cases h : propagateWatched 10 start with
  | fixpoint st =>
    rw [h] at computed
    exact ⟨st, rfl, Option.some.inj computed, (propagateWatched_closure start_inv h).2⟩
  | conflict δ st =>
    rw [h] at computed
    cases computed
  | outOfFuel st =>
    rw [h] at computed
    cases computed

/-- With `{T 3, T 0}` added, propagation reports the falsified nogood `{T 1, F 2}`. -/
theorem implications_conflict :
    conflictOf (propagateWatched 10 ((WState.init (implications ++ [⟨[tAtom 3, tAtom 0], .learned 3⟩]) []).decide
      (tAtom 0))) = some ([tAtom 1, fAtom 2], [fAtom 2, fAtom 3, tAtom 1, tAtom 0]) := by
  decide

/-- A one-literal nogood has no two watches. -/
theorem unit_not_watched : watchable [(⟨[tAtom 0], .learned 0⟩ : Nogood ℕ)] = [] := by decide

theorem liar_nothing_watched : watchable liar.completionNogoods = [] := by decide

theorem liarQ_watchable : (∀ δ ∈ watchable liarQ.completionNogoods, δ ∈ liarQ.completionNogoods) ∧
    liarQ.supportNogood q ∉ watchable liarQ.completionNogoods ∧
    headNogood ⟨p, [], [p]⟩ ∉ watchable liarQ.completionNogoods := by
  decide

/-- The watched state of `p :- not p. p :- q.` after the decision `T p`. -/
def liarQStart : WState Atom := (WState.init liarQ.completionNogoods []).decide (tAtom p)

theorem liarQ_watched_fixpoint :
    fixpointLits (propagateWatched 10 liarQStart) = some [tAtom q, tAtom p] := by
  decide

theorem liarQStart_inv : WInv (watchable liarQ.completionNogoods) liarQStart :=
  (WInv.init liarQ.completionNogoods (t := []) List.nodup_nil fun _ _ => ⟨List.not_mem_nil, List.not_mem_nil⟩).decide
    rfl (by simp [onTrail, State.Assigned, WState.init])

/-- **The trail the watches reach is reached by solver steps.** -/
theorem liarQ_watched_solver :
    ∃ st, propagateWatched 10 liarQStart = .fixpoint st ∧
      ReflTransGen liarQ.Step (.running ⟨liarQStart.trail, [], 0⟩) (.running ⟨st.trail, [], 0⟩) := by
  have spec := propagateWatched_spec 10 liarQStart liarQStart_inv
  have computed := liarQ_watched_fixpoint
  cases h : propagateWatched 10 liarQStart with
  | fixpoint st =>
    rw [h] at spec
    exact ⟨st, rfl, liarQ.upSteps_solver (fun δ hδ => Or.inl (liarQ_watchable.1 δ hδ))
      (fun δ hδ => liarQ.completionNogoods_vars (liarQ_watchable.1 δ hδ)) spec.2.2⟩
  | conflict δ st =>
    rw [h] at computed
    cases computed
  | outOfFuel st =>
    rw [h] at computed
    cases computed

#eval fixpointLits (propagateWatched 10 start)
#eval conflictOf (propagateWatched 10 ((WState.init (implications ++ [⟨[tAtom 3, tAtom 0], .learned 3⟩]) []).decide
  (tAtom 0)))
#eval fixpointLits (propagateWatched 10 liarQStart)

/-! ## Source pointers -/

theorem unsupportedLoop_check :
    unsupportedLoop.marked [] [] = [q, p] ∧ (unsupportedLoop.sources [] []).map Prod.fst = [r] := by
  decide

theorem unsupportedLoop_reason :
    (unsupportedLoop.loopNogood (unsupportedLoop.marked [] []).toFinset p).lits = [tAtom p] := by
  decide

/-- Pushing `F p` with the loop nogood of the marked set is a solver step. -/
theorem unsupportedLoop_step :
    unsupportedLoop.Step (.running (State.initial : State Atom))
      (.running ((State.initial : State Atom).push ⟨fAtom p, levelOf (State.initial : State Atom).trail,
        some (unsupportedLoop.loopNogood (unsupportedLoop.marked (State.initial : State Atom).lits []).toFinset p)⟩)) :=
  unsupportedLoop.unfoundedCheck_step (s := State.initial) [] (by decide) (by decide)
    (by simp [State.Assigned, State.initial])

theorem supportedLoop_nothing_marked : supportedLoop.marked [] [] = [] := by decide

theorem supportedLoop_marked_after :
    supportedLoop.marked [tAtom r] [] = [q, p] ∧
      supportedLoop.marked [tAtom r] (supportedLoop.sources [] []) = [q, p] ∧
      (supportedLoop.sources [tAtom r] (supportedLoop.sources [] [])).map Prod.fst = [r] := by
  decide

#eval (unsupportedLoop.marked [] [], (unsupportedLoop.sources [] []).map Prod.fst)
#eval (supportedLoop.marked [tAtom r] (supportedLoop.sources [] []),
  (supportedLoop.sources [tAtom r] (supportedLoop.sources [] [])).map Prod.fst)

end Mettapedia.Logic.ASP.PropagationControls
