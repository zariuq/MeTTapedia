import Mettapedia.SetTheory.Surreal.CutConstruction
import Mettapedia.SetTheory.Surreal.Negation
import Mettapedia.SetTheory.Surreal.BoundedBirthday

/-!
# Addition by cut recursion

Conway's rule is

```
x + y = { xᴸ + y , x + yᴸ | xᴿ + y , x + yᴿ }
```

and on this carrier it is a recursion through the constructed cut. Two things
have to be arranged for that to be a definition at all.

**A measure.** The recursive calls are `(xᴸ, y)` and `(x, yᴸ)`. The first drops
the left birthday; the second keeps it and drops the right. So the
lexicographic pair `(birthday x, birthday y)` strictly decreases on every call,
and ordinal well-foundedness does the rest.

**A total cut.** `cut` is only defined for families that are separated and have
bounded birthdays, and at the point of definition neither is yet known of the
sum's own options. `cutTotal` is therefore the cut where those hypotheses hold
and `0` where they do not. The junk branch is not a gap: `cutTotal_eq_cut`
says it is never taken when the hypotheses hold, and the theorems below say
they do hold in the cases they cover. Nothing here assumes an obligation it has
not discharged.

What this file establishes:

* `add` — the recursion, accepted with the lexicographic measure.
* `add_comm'` — commutativity. It needs nothing about separation, because it is
  an equality between the *arguments* of the two cuts.
* `add_zero'` and `zero_add'` — the unit law. These do need the cut to be the
  real one, and they get it from `cut_self`: with `0`'s option families empty,
  the sum's options collapse to `x`'s own, and the cut of a number's canonical
  options is that number.

Order compatibility, the birthday bound, associativity and inverses are not
here. They need the simultaneous induction that proves separation of the sum's
options along with the order law, and that is stated as outstanding rather than
implied.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open scoped Classical

/-! ## A total cut -/

/-- The cut where it is defined, and `0` elsewhere.  The second branch exists
only so that the recursion below is a definition; `cutTotal_eq_cut` shows it is
not taken under the hypotheses, and every use here supplies them. -/
noncomputable def cutTotal (L R : Set Surreal) : Surreal :=
  if h : Separated L R ∧ BddAbove (birthday '' (L ∪ R)) then cut L R h.1 h.2 else 0

theorem cutTotal_eq_cut {L R : Set Surreal} (hsep : Separated L R)
    (hbound : BddAbove (birthday '' (L ∪ R))) :
    cutTotal L R = cut L R hsep hbound := by
  rw [cutTotal, dif_pos ⟨hsep, hbound⟩]

/-- **A number is the total cut of its own canonical options.** -/
theorem cutTotal_self (x : Surreal) :
    cutTotal (leftOptions x) (rightOptions x) = x := by
  rw [cutTotal_eq_cut (canonical_separated x) (canonical_bounded x), cut_self]

/-! ## The recursion -/

/-- **Conway's sum.**  Every option of the sum replaces one summand by one of
its own options. -/
noncomputable def add (x y : Surreal) : Surreal :=
  cutTotal
    ((Set.range fun l : leftOptions x => add l.1 y) ∪
      (Set.range fun l : leftOptions y => add x l.1))
    ((Set.range fun r : rightOptions x => add r.1 y) ∪
      (Set.range fun r : rightOptions y => add x r.1))
termination_by (birthday x, birthday y)
decreasing_by
  · exact Prod.Lex.left _ _ l.2.2
  · exact Prod.Lex.right _ l.2.2
  · exact Prod.Lex.left _ _ r.2.2
  · exact Prod.Lex.right _ r.2.2

/-! ## The sum's own option families

Naming the two families lets the boundedness obligation be discharged once,
for every sum, rather than re-argued at each recursive call. -/

/-- The left options of `x + y`. -/
noncomputable def leftSum (x y : Surreal) : Set Surreal :=
  (Set.range fun l : leftOptions x => add l.1 y) ∪
    (Set.range fun l : leftOptions y => add x l.1)

/-- The right options of `x + y`. -/
noncomputable def rightSum (x y : Surreal) : Set Surreal :=
  (Set.range fun r : rightOptions x => add r.1 y) ∪
    (Set.range fun r : rightOptions y => add x r.1)

theorem add_eq_cutTotal (x y : Surreal) :
    add x y = cutTotal (leftSum x y) (rightSum x y) := by
  rw [add]; rfl

instance small_leftSum (x y : Surreal) : Small.{0} (leftSum x y) := by
  rw [leftSum]
  exact small_union _ _

instance small_rightSum (x y : Surreal) : Small.{0} (rightSum x y) := by
  rw [rightSum]
  exact small_union _ _

/-- **The boundedness obligation, discharged for every sum.**  Both families
are small, because each is the image of a small family of options. -/
theorem bddAbove_sum_options (x y : Surreal) :
    BddAbove (birthday '' (leftSum x y ∪ rightSum x y)) :=
  bddAbove_birthday_union _ _

/-- **So only separation is left.**  Wherever the sum's options are separated,
the recursion really is Conway's cut and not the junk branch. -/
theorem add_eq_cut (x y : Surreal) (hsep : Separated (leftSum x y) (rightSum x y)) :
    add x y = cut (leftSum x y) (rightSum x y) hsep (bddAbove_sum_options x y) := by
  rw [add_eq_cutTotal, cutTotal_eq_cut hsep (bddAbove_sum_options x y)]

/-- And then it is the simplest number strictly between them. -/
theorem isCut_add (x y : Surreal) (hsep : Separated (leftSum x y) (rightSum x y)) :
    IsCut (leftSum x y) (rightSum x y) (add x y) := by
  rw [add_eq_cut x y hsep]
  exact isCut_cut _ _ hsep (bddAbove_sum_options x y)

/-- The option families as images, which is the form the negation law needs. -/
theorem leftSum_eq_image (x y : Surreal) :
    leftSum x y = ((fun l => add l y) '' leftOptions x) ∪
      ((fun l => add x l) '' leftOptions y) := by
  rw [leftSum, Set.image_eq_range, Set.image_eq_range]

theorem rightSum_eq_image (x y : Surreal) :
    rightSum x y = ((fun r => add r y) '' rightOptions x) ∪
      ((fun r => add x r) '' rightOptions y) := by
  rw [rightSum, Set.image_eq_range, Set.image_eq_range]

/-! ## Negation distributes over the sum

Negation swaps the two families of every cut (`neg_cutTotal`), and it swaps a
number's own options (`leftOptions_neg`).  Putting those together, `-(x + y)`
and `(-x) + (-y)` are cuts of the same two families, so they are equal.  No
separation is needed: the junk branch is symmetric under the swap too. -/

theorem isCut_neg {L R : Set Surreal} {x : Surreal} (h : IsCut L R x) :
    IsCut ((fun z => -z) '' R) ((fun z => -z) '' L) (-x) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro p ⟨r, hr, rfl⟩
    exact neg_lt_neg_iff.mpr (h.right r hr)
  · rintro q ⟨l, hl, rfl⟩
    exact neg_lt_neg_iff.mpr (h.left l hl)
  · intro y hy
    have hy' : Between L R (-y) := by
      constructor
      · intro l hl
        exact lt_neg_iff.mpr (hy.2 (-l) ⟨l, hl, rfl⟩)
      · intro r hr
        exact neg_lt_iff.mpr (hy.1 (-r) ⟨r, hr, rfl⟩)
    have hb := h.simplest (-y) hy'
    rw [birthday_neg] at hb
    rwa [birthday_neg]

theorem separated_neg_iff {L R : Set Surreal} :
    Separated ((fun z => -z) '' R) ((fun z => -z) '' L) ↔ Separated L R := by
  constructor
  · intro h l hl r hr
    exact neg_lt_neg_iff.mp (h (-r) ⟨r, hr, rfl⟩ (-l) ⟨l, hl, rfl⟩)
  · rintro h p ⟨r, hr, rfl⟩ q ⟨l, hl, rfl⟩
    exact neg_lt_neg_iff.mpr (h l hl r hr)

theorem birthday_image_neg (L R : Set Surreal) :
    birthday '' (((fun z => -z) '' R) ∪ ((fun z => -z) '' L)) = birthday '' (L ∪ R) := by
  ext β
  simp only [Set.mem_image, Set.mem_union]
  constructor
  · rintro ⟨w, (⟨r, hr, rfl⟩ | ⟨l, hl, rfl⟩), rfl⟩
    · exact ⟨r, Or.inr hr, (birthday_neg r).symm⟩
    · exact ⟨l, Or.inl hl, (birthday_neg l).symm⟩
  · rintro ⟨w, (hw | hw), rfl⟩
    · exact ⟨-w, Or.inr ⟨w, hw, rfl⟩, birthday_neg w⟩
    · exact ⟨-w, Or.inl ⟨w, hw, rfl⟩, birthday_neg w⟩

/-- **Negation commutes with the cut**, swapping the families. -/
theorem neg_cutTotal (L R : Set Surreal) :
    -(cutTotal L R) = cutTotal ((fun z => -z) '' R) ((fun z => -z) '' L) := by
  by_cases hsep : Separated L R
  · by_cases hb : BddAbove (birthday '' (L ∪ R))
    · have hsep' : Separated ((fun z => -z) '' R) ((fun z => -z) '' L) :=
        separated_neg_iff.mpr hsep
      have hb' : BddAbove (birthday '' (((fun z => -z) '' R) ∪ ((fun z => -z) '' L))) := by
        rw [birthday_image_neg]; exact hb
      rw [cutTotal_eq_cut hsep hb, cutTotal_eq_cut hsep' hb']
      exact IsCut.unique (isCut_neg (isCut_cut L R hsep hb)) (isCut_cut _ _ hsep' hb')
    · have hb' : ¬ BddAbove (birthday '' (((fun z => -z) '' R) ∪ ((fun z => -z) '' L))) := by
        rw [birthday_image_neg]; exact hb
      rw [cutTotal, cutTotal, dif_neg (fun h => hb h.2), dif_neg (fun h => hb' h.2), neg_zero']
  · have hsep' : ¬ Separated ((fun z => -z) '' R) ((fun z => -z) '' L) :=
      fun h => hsep (separated_neg_iff.mp h)
    rw [cutTotal, cutTotal, dif_neg (fun h => hsep h.1), dif_neg (fun h => hsep' h.1), neg_zero']

/-- **Negation distributes over the sum.**  Both sides are cuts of the same two
families, so they are equal — with no appeal to separation or monotonicity. -/
theorem neg_add (x y : Surreal) : -(add x y) = add (-x) (-y) := by
  rw [add_eq_cutTotal x y, neg_cutTotal, add_eq_cutTotal (-x) (-y)]
  have hA : (fun z => -z) '' rightSum x y = leftSum (-x) (-y) := by
    rw [rightSum_eq_image, leftSum_eq_image, leftOptions_neg, leftOptions_neg,
      Set.image_union, Set.image_image, Set.image_image, Set.image_image,
      Set.image_image]
    refine congrArg₂ (· ∪ ·) ?_ ?_
    · exact Set.image_congr fun r hr => neg_add r y
    · exact Set.image_congr fun r hr => neg_add x r
  have hB : (fun z => -z) '' leftSum x y = rightSum (-x) (-y) := by
    rw [leftSum_eq_image, rightSum_eq_image, rightOptions_neg, rightOptions_neg,
      Set.image_union, Set.image_image, Set.image_image, Set.image_image,
      Set.image_image]
    refine congrArg₂ (· ∪ ·) ?_ ?_
    · exact Set.image_congr fun l hl => neg_add l y
    · exact Set.image_congr fun l hl => neg_add x l
  rw [hA, hB]
termination_by (birthday x, birthday y)
decreasing_by
  · exact Prod.Lex.left _ _ hr.2
  · exact Prod.Lex.right _ hr.2
  · exact Prod.Lex.left _ _ hl.2
  · exact Prod.Lex.right _ hl.2

/-! ## Commutativity

This one costs nothing beyond the recursion, because swapping the summands
permutes the two halves of each option family and leaves the cut's arguments
equal as sets. -/

theorem add_comm' (x y : Surreal) : add x y = add y x := by
  rw [add, add]
  have hL₁ : (Set.range fun l : leftOptions x => add l.1 y)
      = (Set.range fun l : leftOptions x => add y l.1) :=
    congrArg Set.range (funext fun l => add_comm' l.1 y)
  have hL₂ : (Set.range fun l : leftOptions y => add x l.1)
      = (Set.range fun l : leftOptions y => add l.1 x) :=
    congrArg Set.range (funext fun l => add_comm' x l.1)
  have hR₁ : (Set.range fun r : rightOptions x => add r.1 y)
      = (Set.range fun r : rightOptions x => add y r.1) :=
    congrArg Set.range (funext fun r => add_comm' r.1 y)
  have hR₂ : (Set.range fun r : rightOptions y => add x r.1)
      = (Set.range fun r : rightOptions y => add r.1 x) :=
    congrArg Set.range (funext fun r => add_comm' x r.1)
  rw [hL₁, hL₂, hR₁, hR₂, Set.union_comm, Set.union_comm
    (Set.range fun r : rightOptions x => add y r.1)]
termination_by (birthday x, birthday y)
decreasing_by
  · exact Prod.Lex.left _ _ l.2.2
  · exact Prod.Lex.right _ l.2.2
  · exact Prod.Lex.left _ _ r.2.2
  · exact Prod.Lex.right _ r.2.2

/-! ## The unit

`0` has no options at all, so half of each family in `x + 0` is empty and the
other half collapses, by induction, to `x`'s own options.  The cut of a
number's canonical options is that number. -/

theorem add_zero' (x : Surreal) : add x 0 = x := by
  rw [add]
  have hLempty : (Set.range fun l : leftOptions (0 : Surreal) => add x l.1) = ∅ := by
    rw [Set.range_eq_empty_iff]
    rw [CutControls.zero_leftOptions_empty]
    infer_instance
  have hRempty : (Set.range fun r : rightOptions (0 : Surreal) => add x r.1) = ∅ := by
    rw [Set.range_eq_empty_iff]
    rw [CutControls.zero_rightOptions_empty]
    infer_instance
  have hL : (Set.range fun l : leftOptions x => add l.1 0) = leftOptions x := by
    rw [congrArg Set.range (funext fun l : leftOptions x => add_zero' l.1)]
    exact Subtype.range_coe
  have hR : (Set.range fun r : rightOptions x => add r.1 0) = rightOptions x := by
    rw [congrArg Set.range (funext fun r : rightOptions x => add_zero' r.1)]
    exact Subtype.range_coe
  rw [hLempty, hRempty, hL, hR, Set.union_empty, Set.union_empty, cutTotal_self]
termination_by (birthday x, birthday 0)
decreasing_by
  · exact Prod.Lex.left _ _ l.2.2
  · exact Prod.Lex.left _ _ r.2.2

theorem zero_add' (x : Surreal) : add 0 x = x := by
  rw [add_comm', add_zero']

/-! ## Controls -/

namespace AdditionControls

/-- The unit law is not vacuous: it applies at a number with options on both
sides. -/
theorem half_add_zero : add (mk (dyadicPre 1)) 0 = mk (dyadicPre 1) :=
  add_zero' _

/-- And commutativity is exercised where the two summands genuinely differ. -/
theorem comm_at_zero_half : add 0 (mk (dyadicPre 1)) = add (mk (dyadicPre 1)) 0 :=
  add_comm' _ _

/-- The junk branch of `cutTotal` is reachable in principle — overlapping
options are not separated — which is why the theorems above supply the
hypotheses rather than assuming them. -/
theorem overlapping_not_separated : ¬ Separated ({0} : Set Surreal) {0} := by
  intro h
  exact absurd (h 0 rfl 0 rfl) (lt_irrefl _)

end AdditionControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.add_comm'
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.add_zero'
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.zero_add'
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.cutTotal_self
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.neg_add
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.neg_cutTotal
