import Mettapedia.GSLT.Logic.EnumerationMetric

/-!
# Reordering tests changes numerical distance

The same Boolean test is first in one enumeration and second in another.
Both enumerations cover exactly the same tests and have the same zero kernel,
but their distances on the two states are one and one half.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.EnumerationMetricControls

def reading (test state : Bool) : Prop := if test then state = true else True
def first (index : Nat) : Bool := index == 0
def second (index : Nat) : Bool := index == 1

theorem first_covers : Function.Surjective first := by
  intro test
  cases test
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

theorem second_covers : Function.Surjective second := by
  intro test
  cases test
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem first_distance :
    (enumeratedTests (fun index => reading (first index))).distance false true = 1 := by
  have distance := enumerated_distance_first (fun index => reading (first index)) false true 0
    (by simp [reading, first]) (by intro index earlier; omega)
  simpa using distance

theorem second_distance :
    (enumeratedTests (fun index => reading (second index))).distance false true = 1 / 2 := by
  have distance := enumerated_distance_first (fun index => reading (second index)) false true 1
    (by simp [reading, second]) (by
      intro index earlier
      have zero : index = 0 := by omega
      subst index
      simp [reading, second])
  simpa using distance

theorem same_zero_kernel (left right : Bool) :
    ((enumeratedTests (fun index => reading (first index))).distance left right = 0) ↔
      (enumeratedTests (fun index => reading (second index))).distance left right = 0 :=
  (enumerated_zero_iff reading first first_covers left right).trans
    (enumerated_zero_iff reading second second_covers left right).symm

theorem numerical_distance_changes :
    (enumeratedTests (fun index => reading (first index))).distance false true ≠
      (enumeratedTests (fun index => reading (second index))).distance false true := by
  rw [first_distance, second_distance]
  norm_num

end Mettapedia.GSLT.Logic.EnumerationMetricControls
