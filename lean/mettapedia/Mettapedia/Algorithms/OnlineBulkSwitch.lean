import Mathlib.Tactic

/-!
# Online switching under a fixed bulk cost

The controller sees accumulated selective work and whether the consumer has
stopped. It does not know the eventual selective horizon. It rents one unit at
a time until that work reaches the fixed bulk price, then purchases completion
of the retained residual. The recursion models the unknown horizon supplied
by the workload, not an input available to the controller.

The competitive theorem requires that the bulk price remains valid after
selective progress. A separate executed control shows why a price that changes
with the retained state invalidates that theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.OnlineBulkSwitch

inductive Decision where
  | selective
  | bulk
  deriving Repr, DecidableEq

def choose (price spent : Nat) : Decision :=
  if spent < price then .selective else .bulk

structure Receipt where
  selective : Nat
  bulk : Nat
  deriving Repr, DecidableEq

def Receipt.total (receipt : Receipt) : Nat := receipt.selective + receipt.bulk

/-- The realized horizon terminates the interaction. Only `price` and prior
work are passed to `choose`; unfinished work is purchased exactly once. -/
def execute (price : Nat) : Nat → Nat → Receipt
  | 0, _ => ⟨0, 0⟩
  | horizon + 1, spent => match choose price spent with
    | .selective =>
        let remaining := execute price horizon (spent + 1)
        ⟨remaining.selective + 1, remaining.bulk⟩
    | .bulk => ⟨0, price⟩

theorem execute_exact (price horizon spent : Nat) (within : spent ≤ price) :
    execute price horizon spent =
      if horizon + spent ≤ price then ⟨horizon, 0⟩
      else ⟨price - spent, price⟩ := by
  induction horizon generalizing spent with
  | zero => simp [execute, within]
  | succ horizon ih =>
      by_cases before : spent < price
      · have nextWithin : spent + 1 ≤ price := by omega
        simp only [execute, choose, if_pos before]
        rw [ih (spent + 1) nextWithin]
        by_cases completes : horizon + (spent + 1) ≤ price
        · simp only [if_pos completes]
          rw [if_pos (by omega : horizon + 1 + spent ≤ price)]
        · simp only [if_neg completes]
          rw [if_neg (by omega : ¬ horizon + 1 + spent ≤ price)]
          congr 1
          omega
      · have atPrice : spent = price := by omega
        subst spent
        simp [execute, choose]

def offline (price horizon : Nat) : Nat := min horizon price

/-- The bound follows from the actual controller execution. Completion before
the switching threshold pays only its selective work. -/
theorem competitive (price horizon : Nat) :
    (execute price horizon 0).total ≤ 2 * offline price horizon := by
  rw [execute_exact price horizon 0 (Nat.zero_le _)]
  by_cases completes : horizon ≤ price
  · simp only [Nat.add_zero, if_pos completes, Receipt.total, Nat.add_zero,
      offline, Nat.min_eq_left completes]
    omega
  · have cheaper : price ≤ horizon := by omega
    simp [completes, Receipt.total, offline, Nat.min_eq_right cheaper]
    omega

/-- A residual-dependent purchase meter uses the same controller but can
charge a different amount at the eventual switch. -/
def executeVariable (price : Nat) (purchase : Nat → Nat) : Nat → Nat → Receipt
  | 0, _ => ⟨0, 0⟩
  | horizon + 1, spent => match choose price spent with
    | .selective =>
        let remaining := executeVariable price purchase horizon (spent + 1)
        ⟨remaining.selective + 1, remaining.bulk⟩
    | .bulk => ⟨0, purchase spent⟩

namespace Controls

example : execute 5 3 0 = ⟨3, 0⟩ := by decide
example : execute 5 20 0 = ⟨5, 5⟩ := by decide
example : execute 5 5 0 = ⟨5, 0⟩ := by decide

/-- At the initial boundary bulk costs five; after selective work it costs
one hundred. Reusing the initial price as a permanent bound is unsound. -/
def changingPurchase (spent : Nat) : Nat := if spent = 0 then 5 else 100

example : (executeVariable 5 changingPurchase 20 0).total = 105 := by decide
example : 2 * min 20 (changingPurchase 0) = 10 := by decide
example : ¬ (executeVariable 5 changingPurchase 20 0).total ≤
    2 * min 20 (changingPurchase 0) := by decide

end Controls

end Mettapedia.Algorithms.OnlineBulkSwitch
