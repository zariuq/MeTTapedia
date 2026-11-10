import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

/-!
# Executable conjunctive guard checking over binary observation covers

The flat procedure enumerates complete binary alternatives and checks their
conjunctions. The factored procedure checks each local observation twice.
Equality is proved for every guard table. Enumeration itself remains available
and unchanged; only the universal guard certificate avoids materialization.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace AdmissionFactoredBoolean
abbrev Guard := Bool × Bool

def holds (guard : Guard) (value : Bool) : Bool := if value then guard.2 else guard.1

def assignments : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (assignments n).flatMap fun rest => [false :: rest, true :: rest]

def evaluate : List Guard → List Bool → Bool
  | [], [] => true
  | guard :: guards, value :: values => holds guard value && evaluate guards values
  | _, _ => false

def flat (guards : List Guard) : Bool := (assignments guards.length).all (evaluate guards)
def factored (guards : List Guard) : Bool := guards.all (fun guard => guard.1 && guard.2)

theorem assignments_nonempty (n : Nat) : assignments n ≠ [] := by
  induction n with
  | zero => simp [assignments]
  | succ n ih =>
    intro empty
    have present : false :: (assignments n).head ih ∈ assignments (n+1) := by
      exact List.mem_flatMap.mpr ⟨_, List.head_mem ih, List.mem_cons_self⟩
    rw [empty] at present
    cases present

theorem assignments_length (n : Nat) : (assignments n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [assignments, List.length_flatMap, ih, Nat.pow_succ, Nat.mul_comm]

theorem all_conjunction {α : Type} (values : List α) (first second : α → Bool) :
    values.all (fun x => first x && second x) = (values.all first && values.all second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, Bool.and_eq_true, forall_and]

theorem all_constant {α : Type} (values : List α) (nonempty : values ≠ []) (value : Bool) :
    values.all (fun _ => value) = value := by
  cases values with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest => cases value <;> simp

theorem flat_eq_factored (guards : List Guard) : flat guards = factored guards := by
  induction guards with
  | nil => rfl
  | cons guard guards ih =>
    unfold flat
    simp only [List.length_cons, assignments, List.all_flatMap, List.all_cons, List.all_nil,
      Bool.and_true, evaluate, holds, Bool.false_eq_true, if_false, if_true]
    have reorder (value : Bool) : ((guard.1 && value) && (guard.2 && value)) = ((guard.1 && guard.2) && value) := by
      cases guard with
      | mk first second => cases first <;> cases second <;> cases value <;> rfl
    simp only [reorder]
    rw [all_conjunction, all_constant _ (assignments_nonempty _)]
    change ((guard.1 && guard.2) && flat guards) = ((guard.1 && guard.2) && factored guards)
    rw [ih]

/-- A reachable failed local guard is a genuine counterexample to the
universal check; no Cartesian-product completion is required. -/
theorem factored_true_iff (guards : List Guard) :
    factored guards = true ↔ ∀ guard ∈ guards, guard.1 = true ∧ guard.2 = true := by
  simp [factored]

/-- Semantic work counts when every local guard passes. -/
def flatGuardCalls (n : Nat) : Nat := n * 2^n
def factoredGuardCalls (n : Nat) : Nat := 2*n

theorem all_tables_up_to_eight :
    (List.range 9).all (fun n => (assignments (2*n)).all (fun bits =>
      let table := (List.range n).map (fun i => (bits.getD (2*i) false, bits.getD (2*i+1) false))
      flat table == factored table)) = true := by
  apply List.all_eq_true.mpr
  intro n _
  apply List.all_eq_true.mpr
  intro bits _
  simp only [flat_eq_factored, beq_self_eq_true]
end AdmissionFactoredBoolean
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
