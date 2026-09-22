import Mettapedia.GSLT.Topos.PresheafPredicateHeyting
import Mettapedia.GSLT.Topos.PresheafPredicateTotalProducts
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Exponentials of the total presheaf predicate category

The total category of the presheaf predicate projection has finite products;
this file gives it exponentials, so it is cartesian closed over a cartesian
closed base.

The exponential of two objects lies over the base's function object, and
carries the predicate "on every restriction, arguments satisfying the source
predicate are sent to results satisfying the target predicate".  Written with
the fibre operations that predicate is

  `∀_snd ( source∘fst  ⇨  target∘evaluation )`

and `expPredicate` is exactly that expression.

The load-bearing result is `le_expPredicate_preimage_iff`, a **biconditional**:
a curried base map satisfies the exponential predicate exactly when its
uncurrying carries the product predicate to the target.  From it the currying
and uncurrying of total morphisms, the two round trips, the defining hom-set
bijection and evaluation all follow, with uniqueness free because a total
morphism is determined by its base map (`hom_ext`).

Its proof needs three inputs, each established at its own layer:

* `forallAlong_snd_preimage` — Beck–Chevalley along a pairing square, proved
  below by computing both sides on sections;
* `preimage_himp` — reindexing preserves Heyting implication;
* `preimage_le_iff_le_forallAlong` — the quantifier's adjunction.

## Scope

This gives the total category exponentials for the *cartesian* monoidal
structure on the base, which is the one its finite products use.  The base's
closedness is the ambient `MonoidalClosed` instance on presheaves, whose
internal hom is the function object and whose adjunction is against the same
tensor the projections live on.

Exponentials are constructed here; preservation of a closed structure by the
projection is recorded only as the object-level identity `expTotal_base`.

## References

- Williams & Stay, "Native Type Theory" (ACT 2021), §3.
- Jacobs, "Categorical Logic and Type Theory" (1999), Ch. 1 and Ch. 9.
- Mac Lane–Moerdijk, "Sheaves in Geometry and Logic" (1994), Ch. I.6.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

variable {C : Type u} [Category.{u} C]

/-! ## Beck–Chevalley along a pairing square -/

/-- Reindexing a predicate quantified over one factor, along a map of the
other factor, is the quantification of the reindexed predicate. -/
theorem forallAlong_snd_preimage (a c E : Cᵒᵖ ⥤ Type u) (h : c ⟶ E)
    (Ψ : Subfunctor (a ⊗ E)) :
    (forallAlong (snd a E) Ψ).preimage h =
      forallAlong (snd a c) (Ψ.preimage (a ◁ h)) := by
  ext U x
  constructor
  · intro held V i q over
    show (a ◁ h).app V q ∈ Ψ.obj V
    refine held V i ((a ◁ h).app V q) ?_
    show h.app V (q : a.obj V × c.obj V).2 = E.map i (h.app U x)
    have step : (q : a.obj V × c.obj V).2 = c.map i x := over
    rw [step]
    exact NatTrans.naturality_apply h i x
  · intro held V i p over
    have second : (p : a.obj V × E.obj V).2 = E.map i (h.app U x) := over
    have pieces := held V i
      (((p : a.obj V × E.obj V).1, c.map i x) : (a ⊗ c).obj V) rfl
    show p ∈ Ψ.obj V
    have rewritten :
        ((p : a.obj V × E.obj V).1, h.app V (c.map i x)) ∈ Ψ.obj V := pieces
    rw [NatTrans.naturality_apply h i x, ← second] at rewritten
    exact rewritten

/-! ## The exponential -/

/-- The base's function object. -/
abbrev expBase (a b : PresheafPredicateTotal C) : Cᵒᵖ ⥤ Type u :=
  (ihom a.base).obj b.base

/-- Evaluation out of the cartesian product of bases. -/
abbrev expEval (a b : PresheafPredicateTotal C) :
    a.base ⊗ expBase a b ⟶ b.base :=
  (ihom.ev a.base).app b.base

/-- The exponential predicate: on every restriction, arguments satisfying the
source predicate are sent to results satisfying the target predicate. -/
noncomputable def expPredicate (a b : PresheafPredicateTotal C) :
    Subfunctor (expBase a b) :=
  forallAlong (snd a.base (expBase a b))
    ((objectPredicate a).preimage (fst a.base (expBase a b)) ⇨
      (objectPredicate b).preimage (expEval a b))

/-- The exponential object of the total category. -/
noncomputable abbrev expTotal (a b : PresheafPredicateTotal C) :
    PresheafPredicateTotal C :=
  totalOfPredicate (expBase a b) (expPredicate a b)

/-- The projection sends the exponential to the base's function object. -/
theorem expTotal_base (a b : PresheafPredicateTotal C) :
    (expTotal a b).base = (ihom a.base).obj b.base := rfl

/-- **Transposition.** A curried base map satisfies the exponential predicate
exactly when its uncurrying carries the product predicate to the target.  This
is an equivalence, not a one-sided bound. -/
theorem le_expPredicate_preimage_iff (a b c : PresheafPredicateTotal C)
    (h : c.base ⟶ expBase a b) :
    objectPredicate c ≤ (expPredicate a b).preimage h ↔
      (objectPredicate a).preimage (fst a.base c.base) ⊓
          (objectPredicate c).preimage (snd a.base c.base) ≤
        (objectPredicate b).preimage ((a.base ◁ h) ≫ expEval a b) := by
  rw [expPredicate, forallAlong_snd_preimage, preimage_himp,
    ← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp,
    (by simp : (a.base ◁ h) ≫ fst a.base (expBase a b) = fst a.base c.base),
    ← preimage_le_iff_le_forallAlong, le_himp_iff, inf_comm]

/-! ## Currying total morphisms -/

noncomputable def expCurry {a b c : PresheafPredicateTotal C}
    (f : prodTotal a c ⟶ b) : c ⟶ expTotal a b :=
  homOfEntailment (MonoidalClosed.curry f.base) (by
    show objectPredicate c ≤
      (expPredicate a b).preimage (MonoidalClosed.curry f.base)
    rw [le_expPredicate_preimage_iff, ← MonoidalClosed.uncurry_eq,
      MonoidalClosed.uncurry_curry]
    exact hom_entailment f)

noncomputable def expUncurry {a b c : PresheafPredicateTotal C}
    (h : c ⟶ expTotal a b) : prodTotal a c ⟶ b :=
  homOfEntailment (MonoidalClosed.uncurry h.base) (by
    show (objectPredicate a).preimage (fst a.base c.base) ⊓
        (objectPredicate c).preimage (snd a.base c.base) ≤
      (objectPredicate b).preimage (MonoidalClosed.uncurry h.base)
    rw [MonoidalClosed.uncurry_eq, ← le_expPredicate_preimage_iff]
    exact hom_entailment h)

@[simp] theorem expCurry_base {a b c : PresheafPredicateTotal C}
    (f : prodTotal a c ⟶ b) :
    (expCurry f).base = MonoidalClosed.curry f.base := rfl

@[simp] theorem expUncurry_base {a b c : PresheafPredicateTotal C}
    (h : c ⟶ expTotal a b) :
    (expUncurry h).base = MonoidalClosed.uncurry h.base := rfl

/-- Beta: uncurrying a curried morphism returns it. -/
theorem expUncurry_expCurry {a b c : PresheafPredicateTotal C}
    (f : prodTotal a c ⟶ b) : expUncurry (expCurry f) = f :=
  hom_ext _ _ (by
    show MonoidalClosed.uncurry (MonoidalClosed.curry f.base) = f.base
    exact MonoidalClosed.uncurry_curry f.base)

/-- Eta: currying an uncurried morphism returns it. -/
theorem expCurry_expUncurry {a b c : PresheafPredicateTotal C}
    (h : c ⟶ expTotal a b) : expCurry (expUncurry h) = h :=
  hom_ext _ _ (by
    show MonoidalClosed.curry (MonoidalClosed.uncurry h.base) = h.base
    exact MonoidalClosed.curry_uncurry h.base)

/-- The exponential's defining bijection, as total morphisms. -/
noncomputable def expHomEquiv (a b c : PresheafPredicateTotal C) :
    (prodTotal a c ⟶ b) ≃ (c ⟶ expTotal a b) where
  toFun := expCurry
  invFun := expUncurry
  left_inv := expUncurry_expCurry
  right_inv := expCurry_expUncurry

/-- Evaluation as a total morphism. -/
noncomputable def expEvalHom (a b : PresheafPredicateTotal C) :
    prodTotal a (expTotal a b) ⟶ b :=
  expUncurry (𝟙 (expTotal a b))

/-! ## Functoriality of the product, and naturality of transposition -/

/-- The product's action on total morphisms. -/
def prodTotalMap {a a' c c' : PresheafPredicateTotal C}
    (u : a ⟶ a') (v : c ⟶ c') : prodTotal a c ⟶ prodTotal a' c' :=
  prodTotalLift (prodTotalFst a c ≫ u) (prodTotalSnd a c ≫ v)

theorem prodTotalMap_base {a a' c c' : PresheafPredicateTotal C}
    (u : a ⟶ a') (v : c ⟶ c') :
    (prodTotalMap u v).base =
      lift (fst a.base c.base ≫ u.base) (snd a.base c.base ≫ v.base) := rfl

/-- Transposition is natural in the context argument. -/
theorem expCurry_naturality {a b c c' : PresheafPredicateTotal C}
    (g : c' ⟶ c) (f : prodTotal a c ⟶ b) :
    expCurry (prodTotalMap (𝟙 a) g ≫ f) = g ≫ expCurry f :=
  hom_ext _ _ (by
    have whiskered : (prodTotalMap (𝟙 a) g).base = a.base ◁ g.base := by
      show lift (fst a.base c'.base ≫ 𝟙 a.base)
          (snd a.base c'.base ≫ g.base) = a.base ◁ g.base
      rw [Category.comp_id]
      ext <;> simp
    show MonoidalClosed.curry ((prodTotalMap (𝟙 a) g).base ≫ f.base) =
      g.base ≫ MonoidalClosed.curry f.base
    rw [whiskered, MonoidalClosed.curry_natural_left])

/-! ## Stagewise reading on generalized elements -/

/-- The exponential predicate, read on generalized elements: a function
satisfies it exactly when, at every restriction, every argument satisfying the
source predicate is evaluated into the target predicate.

The defining expression has two nested restriction quantifiers, one from the
quantifier and one from the implication.  They collapse to the single one
below, which is the form a consumer can discharge. -/
theorem mem_expPredicate (a b : PresheafPredicateTotal C) (U : Cᵒᵖ)
    (f : (expBase a b).obj U) :
    f ∈ (expPredicate a b).obj U ↔
      ∀ (V : Cᵒᵖ) (i : U ⟶ V) (arg : a.base.obj V),
        arg ∈ (objectPredicate a).obj V →
          (expEval a b).app V ((arg, (expBase a b).map i f)) ∈
            (objectPredicate b).obj V := by
  rw [expPredicate, ← himpPointwise_eq_himp]
  constructor
  · intro held V i arg inSource
    have step := held V i ((arg, (expBase a b).map i f)) rfl
    have applied := step V (𝟙 V) (by
      show a.base.map (𝟙 V) arg ∈ (objectPredicate a).obj V
      rw [Functor.map_id_apply]
      exact inSource)
    have reduced :
        ((a.base ⊗ expBase a b).map (𝟙 V)
          ((arg, (expBase a b).map i f) : (a.base ⊗ expBase a b).obj V)
            : a.base.obj V × (expBase a b).obj V)
          = (arg, (expBase a b).map i f) := by
      show (a.base.map (𝟙 V) arg, (expBase a b).map (𝟙 V)
        ((expBase a b).map i f)) = _
      rw [Functor.map_id_apply, Functor.map_id_apply]
    show _ ∈ (objectPredicate b).obj V
    rw [← reduced]
    exact applied
  · intro held V i p over W j inSource
    have second : (p : a.base.obj V × (expBase a b).obj V).2 =
        (expBase a b).map i f := over
    have restricted := held W (i ≫ j)
      (a.base.map j (p : a.base.obj V × (expBase a b).obj V).1) inSource
    show (expEval a b).app W
      (a.base.map j (p : a.base.obj V × (expBase a b).obj V).1,
        (expBase a b).map j (p : a.base.obj V × (expBase a b).obj V).2) ∈
      (objectPredicate b).obj W
    rw [second, ← Functor.map_comp_apply]
    exact restricted

/-! ## Controls -/

/-- The exponential predicate is a real obstruction: between a top-predicate
source and a bottom-predicate target over a presheaf with a section, no total
morphism lands in the exponential at all. -/
theorem no_hom_into_expTotal {P : Cᵒᵖ ⥤ Type u} {U : Cᵒᵖ} (point : P.obj U) :
    ¬ Nonempty (totalOfPredicate P ⊤ ⟶
      expTotal (totalOfPredicate P ⊤) (totalOfPredicate P ⊥)) := by
  rintro ⟨h⟩
  have entails := hom_entailment (expUncurry h)
  exact entails U (⟨trivial, trivial⟩ :
    ((point, point) : (P ⊗ P).obj U) ∈
      ((objectPredicate (totalOfPredicate P ⊤)).preimage (fst P P) ⊓
        (objectPredicate (totalOfPredicate P ⊤)).preimage (snd P P)).obj U)

end Mettapedia.GSLT.Topos

#print axioms Mettapedia.GSLT.Topos.forallAlong_snd_preimage
#print axioms Mettapedia.GSLT.Topos.le_expPredicate_preimage_iff
#print axioms Mettapedia.GSLT.Topos.expUncurry_expCurry
#print axioms Mettapedia.GSLT.Topos.expCurry_expUncurry
#print axioms Mettapedia.GSLT.Topos.expCurry_naturality
#print axioms Mettapedia.GSLT.Topos.mem_expPredicate
#print axioms Mettapedia.GSLT.Topos.no_hom_into_expTotal
