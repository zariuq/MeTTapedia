import Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverRun

/-!
# Resource accounting on the packed reference run

This calculation follows the existing packed transition. It
records peak term and scratch sizes and the append-only agenda
and trail extents. A small physical workspace is not evidence
of an inconsistent system of equations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverResources

open Mettapedia.Logic.LP
open NativeSolverRun (Fits)
open NativeSolverStep (Outcome Room agendaDemand trailDemand mapDemand)
open PackedWorklist (Worklist Words)

structure Budget where
  nodes : ℕ
  edges : ℕ
  map : ℕ
  agenda : ℕ
  trail : ℕ
  deriving Repr, DecidableEq

structure Budget.Within (use limit : Budget) : Prop where
  nodes : use.nodes ≤ limit.nodes
  edges : use.edges ≤ limit.edges
  map : use.map ≤ limit.map
  agenda : use.agenda ≤ limit.agenda
  trail : use.trail ≤ limit.trail

def Budget.peak (first later : Budget) : Budget :=
  ⟨max first.nodes later.nodes, max first.edges later.edges, max first.map later.map,
    max first.agenda later.agenda, max first.trail later.trail⟩

theorem Budget.Within.trans {first middle last : Budget} (left : first.Within middle) (right : middle.Within last) :
    first.Within last :=
  ⟨left.nodes.trans right.nodes, left.edges.trans right.edges, left.map.trans right.map,
    left.agenda.trans right.agenda, left.trail.trans right.trail⟩

theorem Budget.le_peak_left (first later : Budget) : first.Within (first.peak later) :=
  ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _⟩

theorem Budget.le_peak_right (first later : Budget) : later.Within (first.peak later) :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

def occupied (a t : ℕ) (state : Outcome) : Budget :=
  ⟨PackedWorklist.nodeCount state, PackedWorklist.edgeCount state, 0, a, t⟩

def stepUse (terms : PackedTerms.Arena) (a t : ℕ) (action : PackedUnifierAction.Encoded) : Budget :=
  ⟨terms.nodes.size, terms.children.size, mapDemand terms action, a, t⟩

def planned : ℕ → ℕ → ℕ → Outcome → Option Budget
  | _, a, t, .solved terms history => some (occupied a t (.solved terms history))
  | _, a, t, .inconsistent why => some (occupied a t (.inconsistent why))
  | 0, _, _, .working _ => none
  | fuel + 1, a, t, .working work =>
    match work.pending with
    | [] => some (occupied a t (.working work))
    | (left, right) :: pending => do
      let action ← PackedUnifierAction.inspect work.arena left right
      let next ← PackedWorklist.advance work
      let future ← planned fuel (a + agendaDemand pending action) (t + trailDemand action) next
      some ((stepUse work.arena a t action).peak future)

theorem occupied_at_start (fuel a t : ℕ) (state : Outcome) (budget : Budget)
    (plan : planned fuel a t state = some budget) : (occupied a t state).Within budget := by
  have reflexive (x : Budget) : x.Within x := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  cases state with
  | solved terms history => cases fuel <;> exact (Option.some.inj plan) ▸ reflexive _
  | inconsistent why => cases fuel <;> exact (Option.some.inj plan) ▸ reflexive _
  | working work =>
    rcases work with ⟨terms, todo, history⟩
    cases fuel with
    | zero => cases plan
    | succ fuel =>
      cases todo with
      | nil => exact (Option.some.inj plan) ▸ reflexive _
      | cons next pending =>
        rcases next with ⟨left, right⟩
        obtain ⟨action, _, remaining⟩ := Option.bind_eq_some_iff.mp plan
        obtain ⟨after, _, more⟩ := Option.bind_eq_some_iff.mp remaining
        obtain ⟨future, _, returned⟩ := Option.bind_eq_some_iff.mp more
        obtain rfl := Option.some.inj returned
        have now : (occupied a t (.working ⟨terms, (left, right) :: pending, history⟩)).Within (stepUse terms a t action) :=
          ⟨Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.le_refl _, Nat.le_refl _⟩
        exact now.trans (Budget.le_peak_left _ _)

/-- Every completed reference run has a resource plan.
This is independent of the availability of a particular
physical layout, which is checked separately. -/
theorem exists_plan (fuel a t : ℕ) (state result : Outcome)
    (ran : PackedWorklist.run fuel state = some result) (finished : PackedWorklist.terminal result = true) :
    ∃ need, planned fuel a t state = some need := by
  induction fuel generalizing a t state result with
  | zero =>
    obtain rfl := Option.some.inj ran
    cases state with
    | working work => cases finished
    | solved terms history => exact ⟨_, rfl⟩
    | inconsistent why => exact ⟨_, rfl⟩
  | succ fuel ih =>
    cases state with
    | solved terms history => exact ⟨_, rfl⟩
    | inconsistent why => exact ⟨_, rfl⟩
    | working work =>
      rcases work with ⟨terms, pending, bindings⟩
      cases pending with
      | nil => exact ⟨_, rfl⟩
      | cons first more =>
        rcases first with ⟨left, right⟩
        obtain ⟨next, stepped, later⟩ := Option.bind_eq_some_iff.mp ran
        have source : PackedWorklist.advance ⟨terms, (left, right) :: more, bindings⟩ = some next := stepped
        have examined := source
        change (PackedUnifierAction.inspect terms left right).bind _ = some next at examined
        obtain ⟨action, chosen, _⟩ := Option.bind_eq_some_iff.mp examined
        obtain ⟨rest, remaining⟩ := ih (a + agendaDemand more action) (t + trailDemand action) next result later finished
        refine ⟨(stepUse terms a t action).peak rest, ?_⟩
        simp only [planned, chosen, source, bind, Option.bind_some, remaining]

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- Logical decoding and the computable resource plan give
the hypotheses of native execution. They name no native
states, instruction fetches, or assumed simulation laws. -/
theorem fitted (symbols : UnifierHeaders.Symbols σ) (fuel a t : ℕ) (state : Outcome)
    (typed : Derivation.FiniteUnifier.Configuration σ)
    (decoded : PackedWorklist.read symbols state = some typed)
    (wordBudget : PackedWorklist.Reserve fuel (PackedWorklist.nodeCount state) (PackedWorklist.edgeCount state))
    (used limit : Budget) (plan : planned fuel a t state = some used) (room : used.Within limit) :
    Fits symbols limit.nodes limit.edges limit.map limit.agenda limit.trail fuel a t state := by
  induction fuel generalizing a t state typed used with
  | zero =>
    cases state with
    | working work => cases plan
    | solved terms history => exact .terminal rfl
    | inconsistent why => exact .terminal rfl
  | succ fuel ih =>
    cases state with
    | solved terms history => exact .terminal rfl
    | inconsistent why => exact .terminal rfl
    | working work =>
      rcases work with ⟨terms, pending, history⟩
      cases pending with
      | nil => exact .empty
      | cons front pending =>
        rcases front with ⟨left, right⟩
        obtain ⟨action, examined, rest⟩ := Option.bind_eq_some_iff.mp plan
        obtain ⟨next, advanced, afterwards⟩ := Option.bind_eq_some_iff.mp rest
        obtain ⟨later, visit, shape⟩ := Option.bind_eq_some_iff.mp afterwards
        obtain rfl := Option.some.inj shape
        have afterSpace := (Budget.le_peak_right (stepUse terms a t action) later).trans room
        have nextFit := (occupied_at_start fuel (a + agendaDemand pending action) (t + trailDemand action) next later visit).trans afterSpace
        have now := (Budget.le_peak_left (stepUse terms a t action) later).trans room
        obtain ⟨abstractEqs, decodedEqs, carried⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨abstractTrail, decodedTrail, mode⟩ := Option.bind_eq_some_iff.mp carried
        obtain rfl := Option.some.inj mode
        have firstRead := decodedEqs
        rw [PackedWorklist.readEquations, List.mapM_cons] at firstRead
        obtain ⟨first, represented, _⟩ := Option.bind_eq_some_iff.mp firstRead
        obtain ⟨lTerm, decodedLeft, foundRight⟩ := Option.bind_eq_some_iff.mp represented
        obtain ⟨rTerm, decodedRight, _⟩ := Option.map_eq_some_iff.mp foundRight
        have expanded : PackedWorklist.Reserve fuel (terms.nodes.size + terms.nodes.size)
            (terms.children.size + terms.nodes.size * terms.children.size) := wordBudget
        obtain ⟨computed, exactStep, afterRead, nodes, edges⟩ :=
          PackedWorklist.advance_checked symbols ⟨terms, (left, right) :: pending, history⟩ ⟨abstractEqs, abstractTrail⟩
            decodedEqs decodedTrail (PackedWorklist.reserve_current fuel _ _ expanded)
        obtain rfl := Option.some.inj (exactStep.symm.trans advanced)
        have following := ih _ _ _ _ afterRead (PackedWorklist.reserve_mono fuel nodes edges expanded) later visit afterSpace
        exact .step decodedLeft decodedRight examined exactStep
          ⟨nextFit.nodes, nextFit.edges, now.map, nextFit.agenda, nextFit.trail⟩ following

namespace Examples

private def atoms : PackedTerms.Arena := ⟨#[⟨⟨1, 1⟩, 0, 0⟩], #[]⟩

theorem exhausted_search_has_no_completed_resource_plan :
    planned 0 1 0 (.working ⟨atoms, [(0, 0)], []⟩) = none := rfl

theorem discarding_twice_does_not_allocate :
    planned 3 2 0 (.working ⟨atoms, [(0, 0), (0, 0)], []⟩) = some ⟨1, 0, 0, 2, 0⟩ := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSolverResources
