import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Continuations

/-!
# Costed dispatch of the continuation machine

The control machine uses pointer reads and links for its agenda and
calls the scheduler, solver and reduction service. Those calls have
separate tariffs. An attempt that cannot step is still billed, even
when its trace of source moves is empty.

The cost theorem is uniform when every admitted algebra supplies the
same per-service rate. The result prices control and service calls
under that contract. It does not identify an unbounded symbolic term
operation with one word instruction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.DispatchCost

open Mettapedia.OSLF.Binding
open Evaluation (Evaluator Reply)
open Machine (State Transition Scheduler)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {Storage : Type} {D : Discipline S Γ star}

structure Prices (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty Storage : Type) where
  selection : State κ Γ star Ty Storage → Nat
  live : ExecutionWorld Storage → Branch κ Γ star Ty → Nat
  reduction : ExecutionWorld Storage → Branch κ Γ star Ty → Nat

variable (machine : Evaluator κ D Storage) (strategy : Strategy κ Γ star D.Ty)
  (schedule : Scheduler machine strategy) (prices : Prices κ Γ star D.Ty Storage)

private def service (state : State κ Γ star D.Ty Storage) (branch : Branch κ Γ star D.Ty) :
    Option ((ExecutionWorld Storage × Charge (Data κ Γ star)) × List (Branch κ Γ star D.Ty)) × Nat :=
  if machine.solver.satisfiable branch.store then
    ((Evaluation.reduce machine state.world branch).map fun reply =>
      ((reply.world', charge strategy (state.source machine.spaces) branch reply.branches), reply.branches),
      prices.live state.world branch + prices.reduction state.world branch)
  else (none, prices.live state.world branch)

def step (state : State κ Γ star D.Ty Storage) :
    Option (Transition κ Γ star D.Ty Storage) × Nat :=
  match schedule state with
  | none => (none, prices.selection state + 1)
  | some picked =>
    let reply := OrderedAgenda.meteredSplice (service machine strategy prices state) state.agenda picked.val
    (reply.1.map fun ((world, work), agenda) => ⟨⟨world, agenda⟩, work⟩, prices.selection state + 1 + reply.2)

theorem step_exact (state : State κ Γ star D.Ty Storage) :
    (step machine strategy schedule prices state).1 = Machine.advance machine strategy schedule state := by
  cases pick : schedule state with
  | none => simp [step, Machine.advance, pick]
  | some picked =>
    simp only [step, Machine.advance, pick, OrderedAgenda.meteredSplice_exact, Option.map_map, Option.bind_some]
    by_cases live : machine.solver.satisfiable (state.agenda.get picked.val).store = true
    · simp only [service, Machine.advanceAt, live, if_true, Option.map_map]
      cases Evaluation.reduce machine state.world (state.agenda.get picked.val) <;> rfl
    · simp only [service, Machine.advanceAt, if_neg live, Option.map_none]

/-- A policy prices the work of searching up its own frontier, including
when its last scan finds no permitted position. -/
def selectionQuota (unavailable : State κ Γ star D.Ty Storage → Nat)
    (state : State κ Γ star D.Ty Storage) : Nat :=
  1 + match schedule state with
  | none => unavailable state
  | some picked => strategy.selectionVisits (state.source machine.spaces) (state.agenda.get picked.val)

private def spaceQuota (state : State κ Γ star D.Ty Storage) (branch : Branch κ Γ star D.Ty) : Nat :=
  ((spaceRequest branch).map (strategy.spaceSteps (state.world.source machine.spaces))).getD 0

private def delivery (state : State κ Γ star D.Ty Storage) (branch : Branch κ Γ star D.Ty) : Nat :=
  ((Evaluation.reduce machine state.world branch).map (fun reply => reply.branches.length)).getD 0

/-- Slots are selected by position. If an implementation follows a
linked agenda to that position, the charge includes the traversed
prefix. The other hypotheses concern individual primitive calls. -/
structure Adequate (unavailable : State κ Γ star D.Ty Storage → Nat) (rate : Nat) : Prop where
  traversal : ∀ state picked, schedule state = some picked →
    picked.val.val ≤ strategy.selectionVisits (state.source machine.spaces) (state.agenda.get picked.val)
  selection : ∀ state, prices.selection state ≤ rate * selectionQuota machine strategy schedule unavailable state
  live : ∀ (state : State κ Γ star D.Ty Storage) (branch : Branch κ Γ star D.Ty),
    prices.live state.world branch ≤ rate * (1 + strategy.solverSteps (state.world.source machine.spaces) branch)
  reduction : ∀ (state : State κ Γ star D.Ty Storage) (branch : Branch κ Γ star D.Ty),
    prices.reduction state.world branch ≤
    rate * (1 + strategy.solverSteps (state.world.source machine.spaces) branch +
      spaceQuota machine strategy state branch + delivery machine state branch)

/-- A successful attempt gets its source charge. A selected failure gets
the same request charge with zero deliveries. An unsuccessful selection
gets its scan charge. -/
def debit (unavailable : State κ Γ star D.Ty Storage → Nat) (state : State κ Γ star D.Ty Storage) : Nat :=
  match Machine.advance machine strategy schedule state with
  | some moved => moved.work.units
  | none =>
    match schedule state with
    | none => selectionQuota machine strategy schedule unavailable state
    | some picked => (charge strategy (state.source machine.spaces) (state.agenda.get picked.val) 0).units

theorem debit_at_stop (unavailable : State κ Γ star D.Ty Storage → Nat)
    (state : State κ Γ star D.Ty Storage) (stopped : schedule state = none) :
    debit machine strategy schedule unavailable state = 1 + unavailable state := by
  simp [debit, Machine.advance, stopped, selectionQuota]

private theorem add_payment (rate budget first second third control : Nat)
    (a : first ≤ rate * budget) (b : second ≤ rate * budget) (c : third ≤ rate * budget)
    (d : control ≤ 3 * budget) :
    first + second + third + control ≤ (3 * rate + 3) * budget := by
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

theorem step_bound {unavailable : State κ Γ star D.Ty Storage → Nat} {rate : Nat}
    (adequate : Adequate machine strategy schedule prices unavailable rate)
    (state : State κ Γ star D.Ty Storage) :
    (step machine strategy schedule prices state).2 ≤
      (3 * rate + 3) * debit machine strategy schedule unavailable state := by
  cases pick : schedule state with
  | none =>
    have selection := adequate.selection state
    rw [debit_at_stop machine strategy schedule unavailable state pick]
    simp only [step, pick]
    simp only [selectionQuota, pick] at selection
    have paid := add_payment rate (1 + unavailable state) (prices.selection state) 0 0 1
      selection (Nat.zero_le _) (Nat.zero_le _) (by omega)
    simpa only [Nat.add_zero] using paid
  | some picked =>
    let branch := state.agenda.get picked.val
    let selection := strategy.selectionVisits (state.source machine.spaces) branch
    let solver := strategy.solverSteps (state.world.source machine.spaces) branch
    let space := spaceQuota machine strategy state branch
    let position := picked.val.val
    have traversed : position ≤ selection := adequate.traversal state picked pick
    have selectPaid : prices.selection state ≤ rate * (1 + selection) := by
      simpa only [selectionQuota, pick] using adequate.selection state
    have solvePaid : prices.live state.world branch ≤ rate * (1 + solver) := adequate.live state branch
    have reducePaid := adequate.reduction state branch
    by_cases live : machine.solver.satisfiable (state.agenda.get picked.val).store = true
    · cases reduced : Evaluation.reduce machine state.world (state.agenda.get picked.val) with
      | none =>
        change prices.reduction state.world branch ≤ rate * (1 + solver + space + delivery machine state branch)
          at reducePaid
        dsimp only [branch] at reducePaid
        simp only [delivery, reduced, Option.map_none, Option.getD_none, Nat.add_zero] at reducePaid
        have paid := add_payment rate (1 + solver + (1 + selection) + space)
          (prices.selection state) (prices.live state.world branch) (prices.reduction state.world branch)
          (2 * position + 2)
          (selectPaid.trans (Nat.mul_le_mul_left _ (by omega)))
          (solvePaid.trans (Nat.mul_le_mul_left _ (by omega)))
          (reducePaid.trans (Nat.mul_le_mul_left _ (by omega))) (by omega)
        simp only [step, pick, OrderedAgenda.meteredSplice_exact, service, live, if_true, reduced,
          Option.map_none, OrderedAgenda.emittedWork]
        simp only [debit, Machine.advance, pick, Machine.advanceAt, Option.bind_some, live, if_true, reduced,
          Option.map_none, charge, Charge.units, Multiset.card_zero, Nat.not_lt_zero, if_false, Nat.add_zero]
        change _ ≤ (3 * rate + 3) * (1 + solver + (1 + selection) + space)
        dsimp only [position, branch] at paid
        omega
      | some reply =>
        let size := reply.branches.length
        let budget := (charge strategy (state.source machine.spaces) branch reply.branches).units
        have budgetForm : budget =
            1 + solver + (1 + selection) + size + (if 1 < size then 1 else 0) + space := by
          simp only [budget, charge, Charge.units, Multiset.coe_card]
          rfl
        change prices.reduction state.world branch ≤ rate * (1 + solver + space + delivery machine state branch)
          at reducePaid
        dsimp only [branch] at reducePaid
        simp only [delivery, reduced, Option.map_some, Option.getD_some] at reducePaid
        have paid := add_payment rate budget (prices.selection state) (prices.live state.world branch)
          (prices.reduction state.world branch) (2 * position + 2 * size + 3)
          (selectPaid.trans (Nat.mul_le_mul_left _ (by rw [budgetForm]; omega)))
          (solvePaid.trans (Nat.mul_le_mul_left _ (by rw [budgetForm]; omega)))
          (reducePaid.trans (Nat.mul_le_mul_left _ (by rw [budgetForm]; dsimp only [size]; omega)))
          (by rw [budgetForm]; omega)
        simp only [step, pick, OrderedAgenda.meteredSplice_exact, service, live, if_true, reduced,
          Option.map_some, OrderedAgenda.emittedWork]
        simp only [debit, Machine.advance, pick, Machine.advanceAt, Option.bind_some, live, if_true,
          reduced, Option.map_some]
        change _ ≤ (3 * rate + 3) * budget
        dsimp only [position, size, branch] at paid
        omega
    · have paid := add_payment rate (1 + solver + (1 + selection) + space)
        (prices.selection state) (prices.live state.world branch) 0 (2 * position + 2)
        (selectPaid.trans (Nat.mul_le_mul_left _ (by omega)))
        (solvePaid.trans (Nat.mul_le_mul_left _ (by omega)))
        (Nat.zero_le _) (by omega)
      simp only [step, pick, OrderedAgenda.meteredSplice_exact, service, if_neg live, OrderedAgenda.emittedWork]
      simp only [debit, Machine.advance, pick, Machine.advanceAt, Option.bind_some, if_neg live,
        charge, Charge.units, Multiset.card_zero, Nat.not_lt_zero, Nat.add_zero]
      change _ ≤ (3 * rate + 3) * (1 + solver + (1 + selection) + space)
      dsimp only [position, branch] at paid
      omega

structure Execution (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty Storage : Type) where
  state : State κ Γ star Ty Storage
  moves : List (Charge (Data κ Γ star))
  elapsed : Nat
  stopped : Bool

def run : Nat → State κ Γ star D.Ty Storage → Execution κ Γ star D.Ty Storage
  | 0, state => ⟨state, [], 0, false⟩
  | fuel + 1, state =>
    let attempt := step machine strategy schedule prices state
    match attempt.1 with
    | none => ⟨state, [], attempt.2, true⟩
    | some moved =>
      let following := run fuel moved.next
      ⟨following.state, moved.work :: following.moves, attempt.2 + following.elapsed, following.stopped⟩

theorem run_exact (fuel : Nat) (state : State κ Γ star D.Ty Storage) :
    let result := run machine strategy schedule prices fuel state
    (result.state, result.moves) = Machine.run machine strategy schedule fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [run, Machine.run, step_exact]
    cases Machine.advance machine strategy schedule state with
    | none => rfl
    | some moved =>
      have later := ih moved.next
      simp only
      rw [← later]

def totalDebit (unavailable : State κ Γ star D.Ty Storage → Nat)
    (result : Execution κ Γ star D.Ty Storage) : Nat :=
  units result.moves + if result.stopped then debit machine strategy schedule unavailable result.state else 0

/-- The same multiplier accounts for all runs through any service that
meets the local rate. Any startup term is independent of the input. -/
theorem run_bound {unavailable : State κ Γ star D.Ty Storage → Nat} {rate : Nat}
    (adequate : Adequate machine strategy schedule prices unavailable rate)
    (startup fuel : Nat) (state : State κ Γ star D.Ty Storage) :
    let result := run machine strategy schedule prices fuel state
    result.elapsed + startup ≤ (3 * rate + 3) * totalDebit machine strategy schedule unavailable result + startup := by
  induction fuel generalizing state with
  | zero => simp [run, totalDebit, units]
  | succ fuel ih =>
    have lead := step_bound machine strategy schedule prices adequate state
    have phase := step_exact machine strategy schedule prices state
    simp only [run, phase]
    cases did : Machine.advance machine strategy schedule state with
    | none => simpa [totalDebit, units] using Nat.add_le_add_right lead startup
    | some moved =>
      have paidStep : (step machine strategy schedule prices state).2 ≤ (3 * rate + 3) * moved.work.units := by
        simpa only [debit, did] using lead
      have combined := Nat.add_le_add paidStep (ih moved.next)
      simpa only [totalDebit, units, List.map_cons, List.sum_cons, Nat.mul_add, Nat.add_assoc] using combined

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.DispatchCost
