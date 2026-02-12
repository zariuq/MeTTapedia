import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mettapedia.GSLT.Topos.PredicateFibration
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# OSLF Category-Theoretic Bridge

Lifts the Set-level OSLF construction to categorical infrastructure
using Mathlib's `CategoryTheory` library.

## Main Results

1. **Monotonicity**: `langDiamond` and `langBox` are monotone (as
   left/right adjoints of a Galois connection).

2. **Modal adjunction**: The Galois connection `langDiamond ⊣ langBox`
   lifts to a categorical `Adjunction` between monotone functors on the
   predicate preorder category (via `GaloisConnection.adjunction`).

3. **Sort category**: For any `RewriteSystem`, the sorts form a discrete
   category `Discrete R.Sorts`.

4. **Predicate fibration**: Each sort `s` is assigned the fiber
   `R.Term s → Prop`, forming a `SubobjectFibration` over the sort category.

## The Categorical Picture

The reduction relation R gives a span:
```
        E (reduction graph)
       / \
  src /   \ tgt
     /     \
    v       v
   Proc    Proc
```

Modal operators arise from change-of-base along this span:
  diamond(phi) = exists_src . tgt*,  box(phi) = forall_tgt . src*

The Galois connection diamond -| box follows from composing adjunctions.
In a preorder category, this IS a categorical adjunction (Mathlib's
`GaloisConnection.adjunction`).

## References

- Meredith & Stay, "Operational Semantics in Logical Form" sections 4, 6
- Williams & Stay, "Native Type Theory" (ACT 2021) section 3
-/

namespace Mettapedia.OSLF.Framework.CategoryBridge

open CategoryTheory
open Opposite
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.TypeSynthesis

universe u v

/-! ## Set-Level Results (from DerivedModalities.lean) -/

/-- The generic Galois connection for any reduction span. -/
example (span : ReductionSpan X) :
    GaloisConnection (derivedDiamond span) (derivedBox span) :=
  derived_galois span

/-- The rho-calculus Galois connection as a corollary. -/
example : GaloisConnection
    Mettapedia.OSLF.RhoCalculus.Reduction.possiblyProp
    Mettapedia.OSLF.RhoCalculus.Reduction.relyProp :=
  rho_galois_from_span

/-! ## Monotonicity of Modal Operators

A `GaloisConnection l u` implies `Monotone l` and `Monotone u`.
This is the first step toward viewing the modal operators as functors.
-/

/-- `langDiamond` is monotone: if φ ≤ ψ then ◇φ ≤ ◇ψ. -/
theorem langDiamond_monotone (lang : LanguageDef) :
    Monotone (langDiamond lang) :=
  (langGalois lang).monotone_l

/-- `langBox` is monotone: if φ ≤ ψ then □φ ≤ □ψ. -/
theorem langBox_monotone (lang : LanguageDef) :
    Monotone (langBox lang) :=
  (langGalois lang).monotone_u

/-- `possiblyProp` is monotone. -/
theorem possiblyProp_monotone :
    Monotone Mettapedia.OSLF.RhoCalculus.Reduction.possiblyProp :=
  rho_galois_from_span.monotone_l

/-- `relyProp` is monotone. -/
theorem relyProp_monotone :
    Monotone Mettapedia.OSLF.RhoCalculus.Reduction.relyProp :=
  rho_galois_from_span.monotone_u

/-! ## Categorical Lift: Galois Connection → Adjunction

A `GaloisConnection` between preorders lifts to a categorical `Adjunction`
between the associated preorder categories. Mathlib provides this via:
- `Monotone.functor`: monotone map → functor on preorder category
- `GaloisConnection.adjunction`: Galois connection → adjunction
- `Adjunction.gc`: adjunction → Galois connection (inverse direction)

The predicate type `(Pattern → Prop)` has a `CompleteLattice` structure
(hence `Preorder`), which gives it a thin category via
`Preorder.smallCategory`. However, `Pattern → Prop` also inherits a
`CategoryTheory.Pi` instance, creating an instance diamond.

To avoid this ambiguity, we use a dedicated type wrapper `PredLattice`
for the predicate preorder category.
-/

/-- The predicate lattice over Pattern, viewed as a preorder.

    Using `def` (not `abbrev`) prevents instance diamonds between
    `Preorder.smallCategory` and `CategoryTheory.Pi` on `Pattern → Prop`. -/
def PredLattice : Type := Pattern → Prop

noncomputable instance : CompleteLattice PredLattice := Pi.instCompleteLattice

/-- Wrap a predicate as a `PredLattice` element. -/
def PredLattice.mk (φ : Pattern → Prop) : PredLattice := φ

/-- Unwrap a `PredLattice` element to a predicate. -/
def PredLattice.get (φ : PredLattice) : Pattern → Prop := φ

/-- Lift `langDiamond` to operate on `PredLattice`. -/
def langDiamondL (lang : LanguageDef) : PredLattice → PredLattice :=
  fun φ => langDiamond lang φ.get

/-- Lift `langBox` to operate on `PredLattice`. -/
def langBoxL (lang : LanguageDef) : PredLattice → PredLattice :=
  fun φ => langBox lang φ.get

/-- The lifted langDiamond is monotone. -/
theorem langDiamondL_monotone (lang : LanguageDef) :
    Monotone (langDiamondL lang) := by
  intro φ ψ h
  exact (langGalois lang).monotone_l h

/-- The lifted langBox is monotone. -/
theorem langBoxL_monotone (lang : LanguageDef) :
    Monotone (langBoxL lang) := by
  intro φ ψ h
  exact (langGalois lang).monotone_u h

/-- The Galois connection lifts to `PredLattice`. -/
theorem langGaloisL (lang : LanguageDef) :
    GaloisConnection (langDiamondL lang) (langBoxL lang) := by
  intro φ ψ
  exact langGalois lang φ.get ψ.get

/-- The modal adjunction ◇ ⊣ □ for any `LanguageDef`, as a categorical
    `Adjunction` between endofunctors on the predicate preorder category.

    This lifts the order-theoretic Galois connection to category theory. -/
noncomputable def langModalAdjunction (lang : LanguageDef) :
    (langGaloisL lang).monotone_l.functor ⊣
    (langGaloisL lang).monotone_u.functor :=
  (langGaloisL lang).adjunction

/-- The rho-calculus modal adjunction: instantiate the generic one for `rhoCalc`. -/
noncomputable def rhoModalAdjunction :=
  langModalAdjunction rhoCalc

/-! ## Sort Category and Predicate Fibration

For any `RewriteSystem R`, we build:
1. A sort-category interface (defaulting to a discrete category on `R.Sorts`)
2. A `SubobjectFibration` assigning `(R.Term s → Prop)` to each sort `s`
-/

/-- Interface for selecting the base category used by OSLF sort fibers.

    This is the first concrete lift away from a hard-coded discrete base:
    we can now plug a λ-theory category interface by providing an equivalence
    between rewrite-system sorts and objects in that category. -/
structure SortCategoryInterface (R : RewriteSystem) where
  Obj : Type u
  instCategory : CategoryTheory.Category.{v} Obj
  sortObj : R.Sorts → Obj
  sortOf : Obj → R.Sorts
  sortObj_sortOf : ∀ X : Obj, sortObj (sortOf X) = X
  sortOf_sortObj : ∀ s : R.Sorts, sortOf (sortObj s) = s

attribute [instance] SortCategoryInterface.instCategory

/-- Default sort-category interface: discrete category on sorts. -/
def defaultSortCategoryInterface (R : RewriteSystem) : SortCategoryInterface R where
  Obj := CategoryTheory.Discrete R.Sorts
  instCategory := inferInstance
  sortObj := CategoryTheory.Discrete.mk
  sortOf := fun X => X.as
  sortObj_sortOf := by
    intro X
    cases X
    rfl
  sortOf_sortObj := by
    intro s
    rfl

/-- λ-theory adapter for sort categories.

    Given an equivalence between rewrite-system sorts and objects of a
    λ-theory category, this packages that category as an OSLF sort base. -/
def lambdaTheorySortInterface (R : RewriteSystem)
    (T : Mettapedia.GSLT.Core.LambdaTheoryWithEquality)
    (sortEquiv : R.Sorts ≃ T.Obj) : SortCategoryInterface R where
  Obj := T.Obj
  instCategory := T.instCategory
  sortObj := sortEquiv
  sortOf := sortEquiv.symm
  sortObj_sortOf := sortEquiv.apply_symm_apply
  sortOf_sortObj := sortEquiv.symm_apply_apply

/-- A concrete rewrite system with `Sorts = Type`.

    This is used as a concrete instantiation target for the
    `lambdaTheorySortInterface` plumbing while the full presheaf lift is
    still in progress. -/
def typeSortsRewriteSystem : RewriteSystem where
  Sorts := Type
  procSort := Pattern
  Term := fun X => X
  Reduces := fun _ _ => False

/-- A concrete OSLF type system over `typeSortsRewriteSystem`. -/
noncomputable def typeSortsOSLF : OSLFTypeSystem typeSortsRewriteSystem where
  Pred := fun X => X → Prop
  frame := fun _ => Pi.instFrame
  satisfies := fun t φ => φ t
  diamond := fun _ _ => False
  diamond_spec := by
    intro φ p
    constructor
    · intro h
      exact False.elim h
    · rintro ⟨q, hred, _⟩
      exact False.elim hred
  box := fun _ _ => True
  box_spec := by
    intro φ p
    constructor
    · intro _ q hred
      exact False.elim hred
    · intro _
      trivial
  galois := by
    intro φ ψ
    constructor
    · intro _ p hpPhi
      trivial
    · intro _ p hpDiamond
      exact False.elim hpDiamond

/-- A concrete λ-theory on `Type`, matching `Sorts = Type` by `Equiv.refl`. -/
noncomputable def typeSortsLambdaTheory : Mettapedia.GSLT.Core.LambdaTheoryWithEquality where
  Obj := Type
  instCategory := inferInstance
  instCartesianMonoidal := inferInstance
  instMonoidalClosed := inferInstance
  instHasFiniteLimits := inferInstance
  fibration := {
    Sub := fun X => X → Prop
    frame := fun _ => Pi.instFrame
  }

/-- Concrete λ-theory-backed sort interface for `typeSortsRewriteSystem`. -/
noncomputable def typeSortsLambdaInterface :
    SortCategoryInterface typeSortsRewriteSystem :=
  lambdaTheorySortInterface typeSortsRewriteSystem typeSortsLambdaTheory (Equiv.refl Type)

/-- The default sort category used by existing OSLF constructions. -/
abbrev SortCategory (R : RewriteSystem) : Type u := (defaultSortCategoryInterface R).Obj

/-- Presheaf packaging of a sort-indexed family over the discrete sort base.

For `SortCategory R = Discrete R.Sorts`, this is the canonical "old-style"
per-sort data as a presheaf object.

Reference:
- Mac Lane–Moerdijk (1994), Ch. I.1: presheaves on a discrete base are exactly
  indexed families. -/
def sortFamilyPresheaf (R : RewriteSystem) (T : R.Sorts → Type v) :
    CategoryTheory.Functor (Opposite (CategoryTheory.Discrete R.Sorts)) (Type v) where
  obj X := T X.unop.as
  map {X Y} f := by
    intro x
    exact cast (by
      simpa using congrArg T (CategoryTheory.Discrete.eq_of_hom f.unop).symm) x
  map_id := by
    intro X
    ext x
    simp
  map_comp := by
    intro X Y Z f g
    ext x
    cases X using Opposite.rec
    cases Y using Opposite.rec
    cases Z using Opposite.rec
    cases f
    cases g
    simp

private lemma pred_cast_iff {S : Type u} (T : S → Type v)
    (p : ∀ s : S, T s → Prop) {s t : S} (h : t = s) (x : T s) :
    p s x ↔ p t (cast (congrArg T h.symm) x) := by
  cases h
  simp

/-- On the discrete sort base, subfunctors of a sort-family presheaf are
exactly pointwise predicates.

This is the explicit "where-applicable" bridge from the presheaf backend to
the prior sort-wise approximation.

Reference:
- Jacobs (1999), Ch. 1: predicates as subobjects/fibers; specialized here to
  discrete-indexed families. -/
noncomputable def sortFamilySubfunctorEquivPred
    (R : RewriteSystem) (T : R.Sorts → Type v) :
    CategoryTheory.Subfunctor (sortFamilyPresheaf R T) ≃
      (∀ s : R.Sorts, T s → Prop) where
  toFun G s x := x ∈ G.obj (Opposite.op (CategoryTheory.Discrete.mk s))
  invFun p := by
    refine
      { obj := fun X => { x : (sortFamilyPresheaf R T).obj X | p X.unop.as x }
        map := ?_ }
    intro X Y f x hx
    change p Y.unop.as ((sortFamilyPresheaf R T).map f x)
    have hp : p X.unop.as x ↔ p Y.unop.as ((sortFamilyPresheaf R T).map f x) := by
      let hs : Y.unop.as = X.unop.as := CategoryTheory.Discrete.eq_of_hom f.unop
      have hcast : (sortFamilyPresheaf R T).map f x = cast (congrArg T hs.symm) x := by
        simp [sortFamilyPresheaf]
      have hp' : p X.unop.as x ↔ p Y.unop.as (cast (congrArg T hs.symm) x) := by
        exact pred_cast_iff (T := T) (p := p) hs x
      simpa [hcast] using hp'
    exact hp.mp hx
  left_inv G := by
    ext X x
    rfl
  right_inv p := by
    funext s
    funext x
    rfl

/-- Specialization of `sortFamilySubfunctorEquivPred` to term families. -/
noncomputable def sortTermSubfunctorEquivPred (R : RewriteSystem) :
    CategoryTheory.Subfunctor
      (sortFamilyPresheaf R (fun s => R.Term s)) ≃
      (∀ s : R.Sorts, R.Term s → Prop) :=
  sortFamilySubfunctorEquivPred (R := R) (T := fun s => R.Term s)

/-- The predicate fibration for a rewrite system.

    Each sort `s` is assigned the fiber `R.Term s → Prop` (predicates on
    terms at sort `s`), which is a `Frame` (complete Heyting algebra).

    This is the default-discrete approximation to the full subobject
    fibration `Sub : Set^{T^op} → Set` from Native Type Theory. -/
noncomputable def predFibrationUsing (R : RewriteSystem)
    (I : SortCategoryInterface R) :
    Mettapedia.GSLT.Core.SubobjectFibration I.Obj := by
  let _ : CategoryTheory.Category I.Obj := I.instCategory
  refine
    { Sub := fun X => R.Term (I.sortOf X) → Prop
      frame := ?_ }
  intro _
  exact Pi.instFrame

/-- Backward-compatible default predicate fibration over `SortCategory R`. -/
noncomputable def predFibration (R : RewriteSystem) :
    Mettapedia.GSLT.Core.SubobjectFibration (SortCategory R) :=
  predFibrationUsing R (defaultSortCategoryInterface R)

/-- Construct a `SubobjectFibration` over the sort category from an
    `OSLFTypeSystem`, using the predicate types `sys.Pred s` as fibers. -/
def oslf_fibrationUsing (R : RewriteSystem) (sys : OSLFTypeSystem R)
    (I : SortCategoryInterface R) :
    Mettapedia.GSLT.Core.SubobjectFibration I.Obj := by
  let _ : CategoryTheory.Category I.Obj := I.instCategory
  refine
    { Sub := fun X => sys.Pred (I.sortOf X)
      frame := ?_ }
  intro X
  exact sys.frame (I.sortOf X)

/-- Backward-compatible default OSLF fibration over `SortCategory R`. -/
def oslf_fibration (R : RewriteSystem) (sys : OSLFTypeSystem R) :
    Mettapedia.GSLT.Core.SubobjectFibration (SortCategory R) :=
  oslf_fibrationUsing R sys (defaultSortCategoryInterface R)

/-! ## Presheaf-Topos Fibration Path (Ω/Subobject-Backed) -/

/-! ### Bridge Provenance

- `predFibrationPresheafUsing` / `predFibrationPresheafPrimary`:
  wired to `Topos.presheafPredicateFib`, i.e. Ω/subobject-backed presheaf
  fibers (Mac Lane–Moerdijk Ch. I.3; fibrational view via Jacobs Ch. 1).
- `sortFamilyPresheaf` + `sortFamilySubfunctorEquivPred`:
  explicit specialization of presheaf/subfunctor predicates to discrete sort
  bases (presheaves on discrete categories as indexed families). -/

/-- Selectable backend for presheaf-topos predicate fibrations.

    `omegaSubobject` is the source-faithful backend: predicates are
    represented by `Subfunctor`/`Subobject` fibers via Ω in presheaves. -/
inductive PresheafToposBackend where
  | omegaSubobject

/-- Build a presheaf-topos predicate fibration from the selected backend.

    This is wired to the Ω/subobject-backed construction in
    `GSLT/Topos/PredicateFibration.lean`. -/
noncomputable def predFibrationPresheafUsing
    (C : Type u) (instC : CategoryTheory.Category C)
    (backend : PresheafToposBackend := .omegaSubobject) :
    Mettapedia.GSLT.Core.SubobjectFibration
      (CategoryTheory.Functor (Opposite C) (Type v)) := by
  let _ : CategoryTheory.Category C := instC
  cases backend with
  | omegaSubobject =>
      exact (Mettapedia.GSLT.Topos.presheafPredicateFib (C := C)).toSubobjectFibration

/-- Primary presheaf-topos base path: Ω/subobject-backed fibers. -/
noncomputable abbrev predFibrationPresheafPrimary
    (C : Type u) (instC : CategoryTheory.Category C) :
    Mettapedia.GSLT.Core.SubobjectFibration
      (CategoryTheory.Functor (Opposite C) (Type v)) :=
  predFibrationPresheafUsing (C := C) instC .omegaSubobject

/-- The predicate fibration for the rho-calculus. -/
noncomputable def rhoPredFibration :
    Mettapedia.GSLT.Core.SubobjectFibration
      (SortCategory (langRewriteSystem rhoCalc "Proc")) :=
  predFibration (langRewriteSystem rhoCalc "Proc")

/-- Non-default concrete use-site: predicate fibration over λ-theory-backed
    sort interface (instead of default `SortCategory`). -/
noncomputable def typeSortsPredFibrationViaLambdaInterface :
    Mettapedia.GSLT.Core.SubobjectFibration
      typeSortsLambdaInterface.Obj :=
  predFibrationUsing typeSortsRewriteSystem typeSortsLambdaInterface

/-- Non-default concrete use-site for OSLF-generated fibers over the
    λ-theory-backed sort interface. -/
noncomputable def typeSortsOSLFFibrationViaLambdaInterface :
    Mettapedia.GSLT.Core.SubobjectFibration
      typeSortsLambdaInterface.Obj :=
  oslf_fibrationUsing typeSortsRewriteSystem
    typeSortsOSLF
    typeSortsLambdaInterface

-- Verify the key constructions type-check
#check @langModalAdjunction
#check @rhoModalAdjunction
#check @SortCategoryInterface
#check @defaultSortCategoryInterface
#check @lambdaTheorySortInterface
#check @typeSortsRewriteSystem
#check @typeSortsOSLF
#check @typeSortsLambdaTheory
#check @typeSortsLambdaInterface
#check @predFibration
#check @predFibrationUsing
#check @oslf_fibration
#check @oslf_fibrationUsing
#check @sortFamilyPresheaf
#check @sortFamilySubfunctorEquivPred
#check @sortTermSubfunctorEquivPred
#check @PresheafToposBackend
#check @predFibrationPresheafUsing
#check @predFibrationPresheafPrimary
#check @typeSortsPredFibrationViaLambdaInterface
#check @typeSortsOSLFFibrationViaLambdaInterface

/-! ## Summary

**0 sorries. 0 axioms.**

### Proven Results

1. **Monotonicity**: `langDiamond_monotone`, `langBox_monotone`,
   `possiblyProp_monotone`, `relyProp_monotone`
2. **Modal adjunction**: `langModalAdjunction` (for any `LanguageDef`),
   `rhoModalAdjunction` (for rho-calculus)
3. **Sort category interface**: `SortCategoryInterface R` with default
   `defaultSortCategoryInterface R = Discrete R.Sorts`
4. **Predicate fibration**: `predFibration` and `oslf_fibration` construct
   `SubobjectFibration` instances over the sort category (plus generic
   `predFibrationUsing`/`oslf_fibrationUsing` over any interface)
5. **Concrete λ-theory interface use-site**:
   `typeSortsPredFibrationViaLambdaInterface` and
   `typeSortsOSLFFibrationViaLambdaInterface`
6. **Presheaf-topos path**:
   `predFibrationPresheafUsing` (selectable backend) and
   `predFibrationPresheafPrimary` (Ω/subobject primary path)

### Connection to GSLT

The `SubobjectFibration` structure bridges to `GSLT/Core/`:
- `LambdaTheoryCategory.lean`: Defines `SubobjectFibration` with
  CartesianMonoidalCategory, MonoidalClosed, HasFiniteLimits
- `ChangeOfBase.lean`: The adjoint triple `∃_f ⊣ f* ⊣ ∀_f` at the
  categorical level

### What Remains (Full Topos Lift)

To go from discrete-category fibers to the full topos-theoretic picture:
1. Instantiate `lambdaTheorySortInterface` with a concrete λ-theory category
   equivalence coming from a real language model (currently interface-only)
2. Express the reduction relation as a subobject in the presheaf topos
3. Show `ChangeOfBase.stepForward` restricts to `derivedDiamond` on fibers
4. Prove the Beck-Chevalley condition for substitution commutativity
-/

end Mettapedia.OSLF.Framework.CategoryBridge
