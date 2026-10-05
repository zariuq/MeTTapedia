import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.String.Lemmas

/-!
# Fresh strings for finite supports

The chosen string is longer than every forbidden string. This supplies an
effective fresh name without ordering or searching the forbidden names.
-/

namespace Mettapedia.FreshString

/-- A string longer than every member of a finite support. -/
def fresh (avoid : Finset String) : String :=
  String.replicate (avoid.sup String.length + 1) '_'

@[simp] theorem length_fresh (avoid : Finset String) :
    (fresh avoid).length = avoid.sup String.length + 1 := by
  simp only [fresh, String.length_replicate]

/-- The length bound proves freshness constructively. -/
theorem fresh_not_mem (avoid : Finset String) : fresh avoid ∉ avoid := by
  intro member
  have bound := Finset.le_sup (f := String.length) member
  rw [length_fresh] at bound
  omega

end Mettapedia.FreshString
