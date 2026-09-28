import Mettapedia.SetTheory.Surreal.Associativity
import Mettapedia.SetTheory.Surreal.IntegerEmbedding
import Mathlib.Tactic.FastInstance

/-!
# The ordered additive group

The laws are all proved, so this assembles them into the structures Mathlib
recognises: `AddCommGroup` and `IsOrderedCancelAddMonoid` over the existing
`LinearOrder`. From here the whole ordered-group API applies to `Surreal`
unchanged — `sub_pos`, `add_lt_add_iff_left`, `neg_lt_neg_iff`, `abs`, and the
rest arrive without further work.

## Why the primed names below this file exist

`add_comm'`, `add_assoc'`, `zero_add'`, `add_zero'`, `neg_neg'`, `neg_zero'`
are the bootstrap layer. They are stated about the bare function `add` and the
bare `Neg` instance, because they are what *builds* the group — they cannot be
stated with `+` and `-` before the instance exists, and they cannot be named
`add_comm`/`neg_neg` without shadowing the root-level names they are being used
to establish. Once this file is imported, the Mathlib spelling is the one to
use; the primed names remain only as the foundation they sit on.

`x + y` and `add x y` are the same term, not merely equal ones, and likewise
`x - y` and `sub x y`; `add_eq` and `sub_eq` below hold by `rfl`, so nothing
downstream has to choose between the two notations.

## Deliberately absent

No `One`, no `Mul`, no `natCast` and no `intCast`. Each of those asserts a
relationship between the integers and this addition — `ofNat (n+1) = ofNat n + 1`
is a theorem, not a definition — and they belong with the dyadic interpretation
where that theorem is proved. Declaring them here with unproved coherence would
be an instance whose laws are assumed rather than established.

Multiplication is a separate construction, so only an ordered additive group
is supplied here. No ordered-ring or field instance is supplied by this file;
that is a boundary of this development, not an obstruction to surreal fields.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

/-! ## The group -/

/-- The bare operations, declared before the structure so that `nsmulRec` and
`zsmulRec` — which the group's default scalar actions are built from — have an
`Add` to be defined against. -/
noncomputable instance instAdd : Add Surreal := ⟨add⟩

noncomputable instance instSub : Sub Surreal := ⟨sub⟩

/-- Reuse the bootstrap operation instances in the group's inherited fields.
This also makes the two paths to each operation agree at the transparency used
by rewriting, without unfolding the operation's mathematical construction. -/
noncomputable instance instAddCommGroup : AddCommGroup Surreal := fast_instance%
  { add := add
    add_assoc := add_assoc'
    zero := 0
    zero_add := zero_add'
    add_zero := add_zero'
    neg := fun x => -x
    sub := fun x y => Surreal.sub x y
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := neg_add_self
    add_comm := add_comm' }

/-- The bare function and the notation are the same term. The simp direction is
towards the notation, since that is what the library API is stated in. -/
@[simp] theorem add_eq (x y : Surreal) : add x y = x + y := rfl

@[simp] theorem sub_eq (x y : Surreal) : sub x y = x - y := rfl

/-! ## Compatibility with the order

`Surreal` already carries a `LinearOrder`; this records that addition respects
it, in the cancellative form, which is what makes the strict-monotonicity API
available as well as the weak one. -/

instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Surreal where
  add_le_add_left _ _ h c := add_le_add_right h c
  add_le_add_right _ _ h c := add_le_add_left h c
  le_of_add_le_add_left _ _ _ h := add_le_add_left_iff.mp h
  le_of_add_le_add_right _ _ _ h := add_le_add_right_iff.mp h

/-! ## The bootstrap laws, restated in the library's spelling

These are `rfl`-level restatements rather than new content. They exist so that
the surreal-specific lemmas proved before the instance can be cited in either
notation without an `add_eq` rewrite at every use. -/

theorem neg_add_eq (x y : Surreal) : -(x + y) = -x + -y := neg_add' x y

theorem sub_pos' {x y : Surreal} : 0 < x - y ↔ y < x := sub_pos_iff

theorem sub_neg' {x y : Surreal} : x - y < 0 ↔ x < y := sub_neg_iff

/-! ## Controls -/

namespace AddGroupControls

/-- **The structure is not degenerate**: the group has more than one element,
so the laws are not holding vacuously. -/
theorem nontrivial : (0 : Surreal) ≠ ofNat 1 := ne_of_lt (ofNat_pos Nat.one_pos)

/-- **The Mathlib API really does apply.**  `sub_pos` is a library lemma about
any ordered additive group; it now holds of surreals, and agrees with the
bespoke version proved before the instance existed. -/
theorem library_sub_pos (x y : Surreal) : 0 < x - y ↔ y < x := sub_pos

/-- Strict monotonicity, in the library's spelling, at numbers that differ. -/
theorem library_add_lt_add_left :
    (0 : Surreal) + mk (dyadicPre 1) < ofNat 1 + mk (dyadicPre 1) :=
  add_lt_add_right (ofNat_pos Nat.one_pos) _

/-- Cancellation, in the library's spelling. -/
theorem library_cancel (x y : Surreal) : x + y - y = x := add_sub_cancel_right x y

/-- A bootstrap operation and an inherited group operation can occur in the
same expression and still match the ordinary library rewrite. -/
theorem bootstrap_neg_neg (x : Surreal) :
    @Neg.neg Surreal instNeg (-x) = x := by
  rw [_root_.neg_neg]

/-- Subtraction rewrites to the original sign-flipping operation, without a
separate unfolding or conversion lemma for the instance path. -/
theorem sub_eq_add_bootstrap_neg (x y : Surreal) :
    x - y = x + @Neg.neg Surreal instNeg y := by
  rw [_root_.sub_eq_add_neg]

/-- Integer scaling uses the additive-group API directly. -/
theorem library_zsmul_add (m : ℤ) (x y : Surreal) :
    m • (x + y) = m • x + m • y := by
  rw [zsmul_add]

/-- **Negative control**: the order is not trivialised by the group structure —
a strict inequality is still refused in the wrong direction. -/
theorem not_one_add_half_lt_half :
    ¬ (ofNat 1 + mk (dyadicPre 1) < (0 : Surreal) + mk (dyadicPre 1)) :=
  not_lt.mpr (le_of_lt (add_lt_add_right (ofNat_pos Nat.one_pos) _))

/-- **Negative control**: `sub` is genuinely a difference, not a constant — it
is zero exactly when the arguments agree. -/
theorem sub_ne_zero_of_ne : mk (dyadicPre 1) - (0 : Surreal) ≠ 0 := fun h =>
  absurd (sub_eq_zero_iff.mp h) (ne_of_gt (dyadic_pos 1))

end AddGroupControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.instAddCommGroup
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.instIsOrderedCancelAddMonoid
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.AddGroupControls.library_sub_pos
