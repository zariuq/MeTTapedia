import Mettapedia.Languages.OCaml.Primitives

/-! Equations for the existing source byte-string comparison. No target
encoding or implementation participates in these source laws.
-/

set_option autoImplicit false

open private Mettapedia.Languages.OCaml.compareBytes Mettapedia.Languages.OCaml.compareNat
  from Mettapedia.Languages.OCaml.Primitives

namespace Mettapedia.Languages.OCaml

theorem bytes_nil_nil : compareValue (.literal (.string [])) (.literal (.string [])) = .ok (.ok .eq) := rfl

theorem bytes_nil_cons (head : UInt8) (tail : List UInt8) :
    compareValue (.literal (.string [])) (.literal (.string (head :: tail))) = .ok (.ok .lt) := rfl

theorem bytes_cons_nil (head : UInt8) (tail : List UInt8) :
    compareValue (.literal (.string (head :: tail))) (.literal (.string [])) = .ok (.ok .gt) := rfl

theorem bytes_cons_cons (head other : UInt8) (tail rest : List UInt8) :
    compareValue (.literal (.string (head :: tail))) (.literal (.string (other :: rest))) =
      match (if head.toNat < other.toNat then Ordering.lt else if head.toNat = other.toNat then .eq else .gt) with
      | .eq => compareValue (.literal (.string tail)) (.literal (.string rest))
      | order => .ok (.ok order) := by
  rw [compareValue, Mettapedia.Languages.OCaml.compareBytes, Mettapedia.Languages.OCaml.compareNat]
  rw [compareValue]
  generalize (if head.toNat < other.toNat then Ordering.lt else if head.toNat = other.toNat then .eq else .gt) = order
  cases order <;> rfl

#print axioms bytes_cons_cons

end Mettapedia.Languages.OCaml
