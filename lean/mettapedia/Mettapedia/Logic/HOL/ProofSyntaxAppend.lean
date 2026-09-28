import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Occurrence transports for appended assumption contexts

`ProofSyntaxStructural` supplies `OccurrenceMap.prepend`, `.lift` and `.map`,
which cover consing a hypothesis and renaming the whole context. The two
transports still missing are the ones an appended context needs:

```
Δ₁  ↪  Δ₁ ++ Δ₂        (keep the index)
Δ₂  ↪  Δ₁ ++ Δ₂        (shift by the length of Δ₁)
```

Both are written as structural recursions on the list, so the `get_eq`
obligations discharge by `rfl` at each step: `[] ++ bs` and `(a :: as) ++ bs`
reduce definitionally, so the appended `get` is literally the original one.
That is what keeps them axiom-free, and it is why this is a recursion rather
than a `Fin.castAdd` composed with a cast through `List.length_append` — the
latter compiles, but discharging its side conditions by `simp` drags
`Classical.choice` in, which is a silly price for an index shift.

These are what `ProofSyntax.mono` needs in order to replace the membership-based
weakening of `ProvenanceSemiringReadout.DerivationTree`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ProofSyntax.OccurrenceMap

universe u

variable {α : Type u}

/-! ## Keeping an index when the context grows on the right -/

/-- The position of `as.get i` inside `as ++ bs`: unchanged. -/
def leftIndex : (as bs : List α) → Fin as.length → Fin (as ++ bs).length
  | [], _, i => absurd i.isLt (Nat.not_lt_zero i.val)
  | _ :: as, bs, i =>
      Fin.cases ⟨0, Nat.succ_pos _⟩ (fun j => (leftIndex as bs j).succ) i

theorem get_leftIndex : ∀ (as bs : List α) (i : Fin as.length),
    (as ++ bs).get (leftIndex as bs i) = as.get i
  | [], _, i => absurd i.isLt (Nat.not_lt_zero i.val)
  | _ :: as, bs, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact get_leftIndex as bs j

/-- **A proof over `Δ₁` is a proof over `Δ₁ ++ Δ₂`.** -/
def appendRight (as bs : List α) : OccurrenceMap as (as ++ bs) where
  index := leftIndex as bs
  get_eq := get_leftIndex as bs

/-! ## Shifting an index when the context grows on the left -/

/-- The position of `bs.get i` inside `as ++ bs`: shifted past `as`. -/
def rightIndex : (as bs : List α) → Fin bs.length → Fin (as ++ bs).length
  | [], _, i => i
  | _ :: as, bs, i => (rightIndex as bs i).succ

theorem get_rightIndex : ∀ (as bs : List α) (i : Fin bs.length),
    (as ++ bs).get (rightIndex as bs i) = bs.get i
  | [], _, _ => rfl
  | _ :: as, bs, i => get_rightIndex as bs i

/-- **A proof over `Δ₂` is a proof over `Δ₁ ++ Δ₂`.** -/
def appendLeft (as bs : List α) : OccurrenceMap bs (as ++ bs) where
  index := rightIndex as bs
  get_eq := get_rightIndex as bs

/-! ## Controls -/

namespace AppendControls

/-- Appending nothing on the right keeps every index where it was. -/
theorem leftIndex_nil (as : List α) (i : Fin as.length) :
    ((as ++ ([] : List α)).get (leftIndex as [] i)) = as.get i :=
  get_leftIndex as [] i

/-- Appending nothing on the left is the identity on indices. -/
theorem rightIndex_nil (bs : List α) (i : Fin bs.length) :
    rightIndex [] bs i = i := rfl

/-- The two transports genuinely differ: into `[0] ++ [1]` the left transport
lands on position `0` and the right transport on position `1`. -/
theorem left_ne_right :
    (leftIndex [0] [1] ⟨0, Nat.succ_pos 0⟩ : Fin (([0] : List Nat) ++ [1]).length)
      ≠ rightIndex [0] [1] ⟨0, Nat.succ_pos 0⟩ := by
  decide

end AppendControls

end Mettapedia.Logic.HOL.ProofSyntax.OccurrenceMap

#print axioms Mettapedia.Logic.HOL.ProofSyntax.OccurrenceMap.appendRight
#print axioms Mettapedia.Logic.HOL.ProofSyntax.OccurrenceMap.appendLeft
#print axioms Mettapedia.Logic.HOL.ProofSyntax.OccurrenceMap.get_leftIndex
#print axioms Mettapedia.Logic.HOL.ProofSyntax.OccurrenceMap.get_rightIndex
