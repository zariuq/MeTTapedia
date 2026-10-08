import Mettapedia.OSLF.Syntax.ParallelScopeDecision
import Mettapedia.Algebra.NameSupportedDecomposition

/-!
# Complete quotient decisions, repeated occurrences and support boundaries

Two scopes accept positive output multiplicities on channels zero and two.
Channel one belongs to neither scope, so a universe-covering partition is
not required. The actual equation quotient retains two left and three right
occurrences and accepts either ordering of their authored parallel syntax.
An extra output on the unadmitted channel, an empty inventory and erasure of
a repeated occurrence all fail their independent specification.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ParallelFragment.ScopeControls

open Mettapedia.Algebra.SupportSeparatedDecomposition

def leftScope (term : Term psig [] PSrt.proc) : Prop :=
  (countOut 1 term = 0 ∧ countOut 2 term = 0) ∧ 0 < countOut 0 term

def rightScope (term : Term psig [] PSrt.proc) : Prop :=
  (countOut 0 term = 0 ∧ countOut 1 term = 0) ∧ 0 < countOut 2 term

instance leftScope_decidable : DecidablePred leftScope := fun _ => by
  unfold leftScope
  infer_instance

instance rightScope_decidable : DecidablePred rightScope := fun _ => by
  unfold rightScope
  infer_instance

def classify (name : Fin 3) : Bool := decide (name = 0)

theorem leftInvariant : ScopeInvariant leftScope := by
  intro first second equation
  simp only [leftScope, countOut_invariant 0 equation,
    countOut_invariant 1 equation, countOut_invariant 2 equation]

theorem rightInvariant : ScopeInvariant rightScope := by
  intro first second equation
  simp only [rightScope, countOut_invariant 0 equation,
    countOut_invariant 1 equation, countOut_invariant 2 equation]

theorem leftSupported : LeftSupported classify (inventoryScope leftScope) := by
  rintro inventory ⟨term, admitted, rfl⟩ name member
  have positive : 0 < countOut name term := (freeNames_iff_count term name).mp member
  rw [classify, decide_eq_true_eq]
  fin_cases name
  · rfl
  · change 0 < countOut 1 term at positive
    rw [admitted.1.1] at positive
    omega
  · change 0 < countOut 2 term at positive
    rw [admitted.1.2] at positive
    omega

theorem rightSupported : RightSupported classify (inventoryScope rightScope) := by
  rintro inventory ⟨term, admitted, rfl⟩ name member selected
  have same : name = 0 := of_decide_eq_true selected
  subst name
  have positive : 0 < countOut 0 term := (freeNames_iff_count term 0).mp member
  rw [admitted.1.1] at positive
  omega

theorem whole_scopes_grade_zero : ScopeGradeZero leftScope rightScope :=
  (scopeGradeZero_iff_inventory leftScope rightScope).mpr
    (classified_gradeZero leftSupported rightSupported)

theorem extensions_disjoint (term : Term psig [] PSrt.proc) :
    ¬ (leftScope term ∧ rightScope term) := by
  rintro ⟨first, second⟩
  have positive := first.2
  rw [second.1.1] at positive
  omega

theorem unused_channel_admitted_by_neither :
    ¬ leftScope (u 1) ∧ ¬ rightScope (u 1) := by
  decide

def ordered : Term psig [] PSrt.proc := parT (pow 0 2) (pow 2 3)
def reversed : Term psig [] PSrt.proc := parT (pow 2 3) (pow 0 2)

theorem repeated_left_admitted : leftScope (pow 0 2) := by decide
theorem repeated_right_admitted : rightScope (pow 2 3) := by decide

theorem ordered_member :
    CompositeScopeQ leftScope rightScope leftInvariant rightInvariant (classOf ordered) :=
  ⟨classOf (pow 0 2), classOf (pow 2 3),
    repeated_left_admitted, repeated_right_admitted, rfl⟩

theorem accepts_actual_quotient :
    decideCompositeQ classify leftScope rightScope (classOf ordered) = true :=
  (decideCompositeQ_iff leftInvariant rightInvariant leftSupported rightSupported _).mpr
    ordered_member

theorem authored_reordering_same_class : classOf ordered = classOf reversed :=
  Quotient.sound (parComm (pow 0 2) (pow 2 3))

theorem accepts_reordered_quotient :
    decideCompositeQ classify leftScope rightScope (classOf reversed) = true := by
  rw [← authored_reordering_same_class]
  exact accepts_actual_quotient

theorem complete_occurrences_and_queries :
    partitionInventory classify (inventoryQ (classOf ordered)) =
      CountedParts.mk ({0, 0} : Multiset (Fin 3)) {2, 2, 2} 5 := by
  apply CountedParts.ext <;> decide

theorem duplicate_erasure_changes_class : classOf (pow 0 2) ≠ classOf (u 0) := by
  intro same
  have counted := congrArg (fun value => (inventoryQ value).count 0) same
  change (nameInventory (pow 0 2)).count 0 = (nameInventory (u 0)).count 0 at counted
  rw [nameInventory_count, nameInventory_count] at counted
  simp [countOut_pow, u, countOut, countOutArgs, headCount] at counted

theorem rejects_unadmitted_channel :
    decideCompositeQ classify leftScope rightScope (classOf (parT ordered (u 1))) = false := by
  decide

theorem rejects_empty_inventory :
    decideCompositeQ classify leftScope rightScope (classOf nulT) = false := by
  decide

theorem every_other_split_recovers_complete_halves
    {first second : ParallelClass}
    (admittedFirst : scopeQ leftScope leftInvariant first)
    (admittedSecond : scopeQ rightScope rightInvariant second)
    (whole : parallelQ first second = classOf ordered) :
    first = classOf (pow 0 2) ∧ second = classOf (pow 2 3) :=
  quotient_halves_unique leftInvariant rightInvariant whole_scopes_grade_zero
    admittedFirst admittedSecond repeated_left_admitted repeated_right_admitted whole

end Mettapedia.OSLF.Binding.ParallelFragment.ScopeControls
