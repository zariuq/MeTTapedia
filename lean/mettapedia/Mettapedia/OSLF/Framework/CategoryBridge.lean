import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mettapedia.GSLT.Topos.PredicateFibration
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Yoneda
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
open Mettapedia.OSLF.Framework.ConstructorCategory

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

/-- Legacy sort-category predicate fibration over `SortCategory R`.

    This preserves the earlier sort-wise approximation as a compatibility
    wrapper. The primary/default backend is `predFibration` (presheaf-topos). -/
noncomputable def predFibrationSortApprox (R : RewriteSystem) :
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

/-- Legacy sort-category OSLF fibration over `SortCategory R`.

    Compatibility wrapper for the prior sort-wise path. -/
def oslf_fibrationSortApprox (R : RewriteSystem) (sys : OSLFTypeSystem R) :
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

/-- Canonical presheaf base for sort-indexed OSLF/GSLT lifting. -/
abbrev SortPresheafCategory (R : RewriteSystem) : Type (max u (v + 1)) :=
  CategoryTheory.Functor (Opposite (CategoryTheory.Discrete R.Sorts)) (Type v)

/-- Default predicate fibration for OSLF bridge consumers.

    This is now the primary Ω/subobject-backed presheaf path over the discrete
    sort base (presheafized). -/
noncomputable def predFibration (R : RewriteSystem) :
    Mettapedia.GSLT.Core.SubobjectFibration (SortPresheafCategory R) :=
  predFibrationPresheafPrimary (C := CategoryTheory.Discrete R.Sorts) inferInstance

/-- Default OSLF fibration for bridge consumers.

    The consumer-facing default is the same Ω/subobject-backed presheaf base.
    For compatibility with the former API shape, `sys` is retained.
    Use `oslf_fibrationSortApprox` if you explicitly need sort-wise fibers. -/
noncomputable def oslf_fibration (R : RewriteSystem) (_sys : OSLFTypeSystem R) :
    Mettapedia.GSLT.Core.SubobjectFibration (SortPresheafCategory R) :=
  predFibration R

/-- The default predicate fibration for the rho-calculus. -/
noncomputable def rhoPredFibration :
    Mettapedia.GSLT.Core.SubobjectFibration
      (SortPresheafCategory (langRewriteSystem rhoCalc "Proc")) :=
  predFibration (langRewriteSystem rhoCalc "Proc")

/-- Legacy sort-wise rho predicate fibration (compatibility wrapper). -/
noncomputable def rhoPredFibrationSortApprox :
    Mettapedia.GSLT.Core.SubobjectFibration
      (SortCategory (langRewriteSystem rhoCalc "Proc")) :=
  predFibrationSortApprox (langRewriteSystem rhoCalc "Proc")

/-- Generic discrete-base agreement: the presheaf-primary default fiber on the
term-family presheaf coincides with the legacy sort-wise approximation.

This is the canonical bridge theorem for migrating from the old sort-category
default to the Ω/subobject presheaf default without semantic drift. -/
noncomputable def predFibration_presheafSortApprox_agreement (R : RewriteSystem) :
    (predFibration R).Sub
      (sortFamilyPresheaf R (fun s => R.Term s))
      ≃
    (∀ s : R.Sorts,
      (predFibrationSortApprox R).Sub (CategoryTheory.Discrete.mk s)) := by
  simpa [predFibration, predFibrationPresheafPrimary, predFibrationPresheafUsing,
    predFibrationSortApprox, predFibrationUsing, defaultSortCategoryInterface,
    SortPresheafCategory] using
    (sortTermSubfunctorEquivPred (R := R))

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

/-- Pointwise fiber family induced by `oslf_fibrationUsing` on the concrete
`typeSorts` λ-theory-backed interface. -/
abbrev typeSortsOSLFFiberFamily : Type → Type :=
  fun s => (typeSortsOSLFFibrationViaLambdaInterface.Sub
    (typeSortsLambdaInterface.sortObj s))

/-- Concrete agreement theorem: on the `typeSorts` instance, the
`oslf_fibrationUsing` fibers align with the presheaf-primary backend
fiber over the corresponding sort-family presheaf.

This witnesses one explicit instance where OSLF fibers and presheaf-topos
subobject fibers coincide (via subfunctor↔predicate equivalence). -/
noncomputable def typeSortsOSLFFibrationUsing_presheafAgreement :
    (predFibrationPresheafPrimary
      (C := CategoryTheory.Discrete Type)
      (instC := inferInstance)).Sub
      (sortFamilyPresheaf typeSortsRewriteSystem
        (fun s => typeSortsRewriteSystem.Term s))
      ≃
    (∀ s : Type, typeSortsOSLFFiberFamily s) := by
  simpa [predFibrationPresheafPrimary, predFibrationPresheafUsing,
    typeSortsOSLFFiberFamily, typeSortsOSLFFibrationViaLambdaInterface,
    oslf_fibrationUsing, typeSortsLambdaInterface, lambdaTheorySortInterface,
    typeSortsRewriteSystem] using
    (sortTermSubfunctorEquivPred (R := typeSortsRewriteSystem))

/-- Pointwise fiber family induced by `oslf_fibrationUsing` on a language wrapper
(`Sorts = String`). -/
abbrev langOSLFFiberFamily (lang : LanguageDef) (procSort : String := "Proc") : String → Type :=
  fun s => ((oslf_fibrationUsing
    (langRewriteSystem lang procSort)
    (langOSLF lang procSort)
    (defaultSortCategoryInterface (langRewriteSystem lang procSort))).Sub
      (CategoryTheory.Discrete.mk s))

/-! ## Generic Language-Wrapper Agreement (SortPresheaf ↔ OSLF Fibers) -/

/-- Generic agreement theorem on language wrappers (`Sorts = String`):
`oslf_fibrationUsing` fibers coincide with the presheaf-primary backend fiber
over the sort-family presheaf of `langRewriteSystem lang procSort`. -/
noncomputable def langOSLFFibrationUsing_presheafAgreement
    (lang : LanguageDef) (procSort : String := "Proc") :
    (predFibrationPresheafPrimary
      (C := CategoryTheory.Discrete String)
      (instC := inferInstance)).Sub
      (sortFamilyPresheaf (langRewriteSystem lang procSort)
        (fun s => (langRewriteSystem lang procSort).Term s))
      ≃
    (∀ s : String, langOSLFFiberFamily lang procSort s) := by
  simpa [predFibrationPresheafPrimary, predFibrationPresheafUsing,
    langOSLFFiberFamily, oslf_fibrationUsing, defaultSortCategoryInterface,
    langRewriteSystem, langRewriteSystemUsing, langOSLF] using
    (sortTermSubfunctorEquivPred (R := (langRewriteSystem lang procSort)))

/-- Pointwise fiber family induced by `oslf_fibrationUsing` on the concrete
`rhoCalc` language wrapper (`Sorts = String`). -/
abbrev rhoLangOSLFFiberFamily : String → Type :=
  langOSLFFiberFamily rhoCalc "Proc"

/-- Concrete agreement theorem on a real language instance (`rhoCalc`):
`oslf_fibrationUsing` fibers coincide with the presheaf-primary backend fiber
over the sort-family presheaf of `langRewriteSystem rhoCalc`.

This is the non-toy companion to `typeSortsOSLFFibrationUsing_presheafAgreement`,
showing the same bridge on the actual executable language wrapper used by OSLF.
-/
noncomputable def rhoLangOSLFFibrationUsing_presheafAgreement :
    (predFibrationPresheafPrimary
      (C := CategoryTheory.Discrete String)
      (instC := inferInstance)).Sub
      (sortFamilyPresheaf (langRewriteSystem rhoCalc "Proc")
        (fun s => (langRewriteSystem rhoCalc "Proc").Term s))
      ≃
    (∀ s : String, rhoLangOSLFFiberFamily s) := by
  simpa [rhoLangOSLFFiberFamily] using
    (langOSLFFibrationUsing_presheafAgreement (lang := rhoCalc) (procSort := "Proc"))

/-! ## Real Language λ-Theory Presheaf Lift (Canonical)

This section is the first non-toy "full topos" language lift:
- base category = `ConstructorObj lang` (actual sort-crossing category),
- ambient λ-theory objects = presheaves on that base,
- fibers = Ω/subobject-backed presheaf predicate fibers.

So this is a concrete language-dependent λ-theory instantiation, not the
`Sorts = Type` plumbing demo.
-/

/-- Presheaf object type over the constructor category of a language. -/
abbrev languagePresheafObj (lang : LanguageDef) : Type 1 :=
  CategoryTheory.Functor (Opposite (ConstructorObj lang)) Type

/-- Canonical λ-theory for a concrete language:
`Obj = Psh(ConstructorObj lang)` with Ω/subobject-backed predicate fibers. -/
noncomputable def languagePresheafLambdaTheory (lang : LanguageDef) :
    Mettapedia.GSLT.Core.LambdaTheoryWithEquality where
  Obj := languagePresheafObj lang
  instCategory := inferInstance
  instCartesianMonoidal := inferInstance
  instMonoidalClosed := inferInstance
  instHasFiniteLimits := inferInstance
  fibration :=
    (Mettapedia.GSLT.Topos.presheafPredicateFib (C := ConstructorObj lang)).toSubobjectFibration

/-- Canonical sort embedding into the presheaf λ-theory via Yoneda representables. -/
noncomputable def languageSortRepresentableObj (lang : LanguageDef)
    (s : LangSort lang) : (languagePresheafLambdaTheory lang).Obj :=
  (CategoryTheory.yoneda.obj (ConstructorObj.mk s))

/-- Fiber at a concrete language sort in the canonical presheaf λ-theory. -/
noncomputable def languageSortFiber (lang : LanguageDef) (s : LangSort lang) : Type :=
  (languagePresheafLambdaTheory lang).Sub (languageSortRepresentableObj lang s)

/-- Characteristic-map view of a sort fiber:
`Sub(y(s)) ≃ (y(s) ⟶ Ω)` in the presheaf topos. -/
noncomputable def languageSortFiber_characteristicEquiv
    (lang : LanguageDef) (s : LangSort lang) :
    ((languageSortRepresentableObj lang s) ⟶
      Mettapedia.GSLT.Topos.omegaFunctor (C := ConstructorObj lang))
      ≃ languageSortFiber lang s := by
  simpa [languageSortFiber, languagePresheafLambdaTheory, languageSortRepresentableObj] using
    (Mettapedia.GSLT.Topos.natTransEquivSubfunctor
      (C := ConstructorObj lang)
      (P := (CategoryTheory.yoneda.obj (ConstructorObj.mk s))))

/-- Side condition ensuring a `Pattern → Prop` predicate is stable under
precomposition along constructor-category arrows into a fixed representable
target sort.

This is exactly the closure condition needed to package the predicate as a
subfunctor of `y(s)` (hence an element of `languageSortFiber lang s`). -/
def languageSortPredNaturality
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop) : Prop :=
  ∀ {a b : LangSort lang}
    (g : SortPath lang a b) (h : SortPath lang b s),
      φ (pathSem lang h seed) →
      φ (pathSem lang (g.comp h) seed)

/-- `commSubst`-image predicate over `Pattern`.

This matches the direct-image shape used by COMM:
`r ↦ ∃ u, commSubst u q = r ∧ φ u`. -/
def commDiPred (q : Pattern) (φ : Pattern → Prop) : Pattern → Prop :=
  fun r => ∃ u, Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = r ∧ φ u

/-- Structural witness-lifting condition for COMM direct-image predicates.

Given a representable target witness `pathSem h seed`, any COMM witness for it
can be lifted along precomposition by `g` to a witness for
`pathSem (g.comp h) seed`, preserving `φ`.

This names the exact transport obligation needed for naturality of `commDiPred`.
-/
def commDiWitnessLifting
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop) : Prop :=
  ∀ {a b : LangSort lang}
    (g : SortPath lang a b) (h : SortPath lang b s)
    {u : Pattern},
      Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = pathSem lang h seed →
      φ u →
      ∃ u',
        Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u' q =
          pathSem lang (g.comp h) seed ∧
        φ u'

/-- `pathSem` commutes with COMM substitution on the substituted body:
wrapping a COMM-substituted term along constructor paths equals
COMM-substituting after wrapping the body along the same path. -/
theorem pathSem_commSubst
    (lang : LanguageDef) {a b : LangSort lang}
    (g : SortPath lang a b) (u q : Pattern) :
    pathSem lang g (Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q) =
      Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem lang g u) q := by
  induction g with
  | nil =>
      rfl
  | cons g arr ih =>
      refine (congrArg (fun t => arrowSem lang arr t) ih).trans ?_
      calc
        arrowSem lang arr (Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem lang g u) q)
            =
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst
            (arrowSem lang arr (pathSem lang g u)) q := by
              simp [arrowSem, Mettapedia.OSLF.MeTTaIL.Substitution.commSubst,
                Mettapedia.OSLF.MeTTaIL.Substitution.openBVar]
        _ =
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst
            (pathSem lang (SortPath.cons g arr) u) q := by
              simp [pathSem, Function.comp]

/-- Closure of a predicate under all constructor-path semantic actions.

`PathSemClosedPred lang φ` is the least predicate containing `φ` and closed
under `pathSem` along any sort-path. This provides a canonical assumption-free
carrier for representable-fiber transport obligations. -/
inductive PathSemClosedPred
    (lang : LanguageDef) (φ : Pattern → Prop) : Pattern → Prop where
  | base {u : Pattern} : φ u → PathSemClosedPred lang φ u
  | step {a b : LangSort lang} (g : SortPath lang a b) {u : Pattern} :
      PathSemClosedPred lang φ u →
        PathSemClosedPred lang φ (pathSem lang g u)

/-- `PathSemClosedPred` is closed under all `pathSem` actions by construction. -/
theorem pathSemClosedPred_closed
    (lang : LanguageDef) (φ : Pattern → Prop)
    {a b : LangSort lang} (g : SortPath lang a b) {u : Pattern}
    (hu : PathSemClosedPred lang φ u) :
    PathSemClosedPred lang φ (pathSem lang g u) :=
  PathSemClosedPred.step g hu

/-- Naturality transport for COMM direct-image predicates.

The assumption is the named structural condition `commDiWitnessLifting`
capturing exactly the required witness transport along precomposition.
-/
theorem languageSortPredNaturality_commDi
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLift : commDiWitnessLifting lang s seed q φ) :
    languageSortPredNaturality lang s seed (commDiPred q φ) := by
  intro a b g h hh
  rcases hh with ⟨u, huEq, huφ⟩
  rcases hLift g h huEq huφ with ⟨u', hu'Eq, hu'φ⟩
  exact ⟨u', hu'Eq, hu'φ⟩

/-- Builder for `commDiWitnessLifting` from an explicit witness transformer.

If a transformation `lift` preserves `φ` and transports COMM witnesses to the
composed path target, then the structural lifting condition holds. -/
theorem commDiWitnessLifting_of_lift
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (lift :
      ∀ {a b : LangSort lang},
        SortPath lang a b → Pattern → Pattern)
    (hLiftEq :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s)
        {u : Pattern},
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = pathSem lang h seed →
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (lift g u) q =
            pathSem lang (g.comp h) seed)
    (hLiftPred :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) {u : Pattern},
          φ u → φ (lift g u)) :
    commDiWitnessLifting lang s seed q φ := by
  intro a b g h u huEq huφ
  refine ⟨lift g u, hLiftEq g h huEq, hLiftPred g huφ⟩

/-- Specialized constructor for COMM witness lifting when using `pathSem` as
the witness transformer.

This packages the common case where a caller provides:
1. explicit COMM witness transport along `pathSem` for the chosen seed, and
2. closure of `φ` under `pathSem`.
-/
theorem commDiWitnessLifting_of_pathSemLift
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLiftEq :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s)
        {u : Pattern},
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = pathSem lang h seed →
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem lang g u) q =
            pathSem lang (g.comp h) seed)
    (hClosed :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) {u : Pattern},
          φ u → φ (pathSem lang g u)) :
    commDiWitnessLifting lang s seed q φ := by
  refine commDiWitnessLifting_of_lift lang s seed q φ
    (lift := fun {a b} g u => pathSem lang g u) ?_ ?_
  · intro a b g h u huEq
    exact hLiftEq g h huEq
  · intro a b g u hu
    exact hClosed g hu

/-- COMM witness lifting for canonical path-semantics closure of a predicate:
only the witness-transport equation is required (`hLiftEq`); closure is
discharged automatically by `PathSemClosedPred`. -/
theorem commDiWitnessLifting_of_pathSemClosed
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLiftEq :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s)
        {u : Pattern},
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = pathSem lang h seed →
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem lang g u) q =
            pathSem lang (g.comp h) seed) :
    commDiWitnessLifting lang s seed q (PathSemClosedPred lang φ) := by
  refine commDiWitnessLifting_of_pathSemLift lang s seed q (PathSemClosedPred lang φ) hLiftEq ?_
  intro a b g u hu
  exact pathSemClosedPred_closed lang φ g hu

/-- Naturality transport for COMM direct-image predicates over the canonical
path-semantics closure of a predicate.

As with `commDiWitnessLifting_of_pathSemClosed`, this reduces assumptions to the
single witness-transport equation (`hLiftEq`). -/
theorem languageSortPredNaturality_commDi_pathSemClosed
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hLiftEq :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s)
        {u : Pattern},
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = pathSem lang h seed →
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem lang g u) q =
            pathSem lang (g.comp h) seed) :
    languageSortPredNaturality lang s seed
      (commDiPred q (PathSemClosedPred lang φ)) := by
  exact languageSortPredNaturality_commDi lang s seed q (PathSemClosedPred lang φ)
    (commDiWitnessLifting_of_pathSemClosed lang s seed q φ hLiftEq)

/-- Canonical package for path-based COMM witness transport obligations.

This packages the witness-transport equation once, so downstream BC/graph
corollaries can consume a named artifact instead of restating raw formulas. -/
structure CommDiPathSemLiftPkg
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) : Prop where
  liftEq :
    ∀ {a b : LangSort lang}
      (g : SortPath lang a b) (h : SortPath lang b s)
      {u : Pattern},
        Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = pathSem lang h seed →
        Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem lang g u) q =
          pathSem lang (g.comp h) seed

/-- Manual package route: if a concrete `liftEq` law is available, we can
instantiate `CommDiPathSemLiftPkg` directly. -/
theorem commDiPathSemLiftPkg_of_liftEq
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern)
    (hLiftEq :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s)
        {u : Pattern},
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q = pathSem lang h seed →
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem lang g u) q =
            pathSem lang (g.comp h) seed) :
    CommDiPathSemLiftPkg lang s seed q := by
  exact ⟨hLiftEq⟩

/-- Automatic package route from two structural laws:
1. path/substitution commutation (`pathSem_commSubst`), and
2. path-order law for the chosen seed (`pathSem g (pathSem h seed) = pathSem (g.comp h) seed`).

When (2) is unavailable for a language/sort, callers should use
`commDiPathSemLiftPkg_of_liftEq` with an explicit `liftEq` theorem. -/
theorem commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed) :
    CommDiPathSemLiftPkg lang s seed q := by
  refine ⟨?_⟩
  intro a b g h u huEq
  calc
    Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem lang g u) q
        = pathSem lang g (Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q) := by
            simpa using (pathSem_commSubst lang g u q).symm
    _ = pathSem lang g (pathSem lang h seed) := by simp [huEq]
    _ = pathSem lang (g.comp h) seed := hPathOrder g h

/-- Package form of `commDiWitnessLifting_of_pathSemClosed`. -/
theorem commDiWitnessLifting_of_pathSemLiftPkg
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hPkg : CommDiPathSemLiftPkg lang s seed q) :
    commDiWitnessLifting lang s seed q (PathSemClosedPred lang φ) := by
  exact commDiWitnessLifting_of_pathSemClosed lang s seed q φ hPkg.liftEq

/-- Package form of `languageSortPredNaturality_commDi_pathSemClosed`. -/
theorem languageSortPredNaturality_commDi_pathSemClosed_of_pkg
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hPkg : CommDiPathSemLiftPkg lang s seed q) :
    languageSortPredNaturality lang s seed
      (commDiPred q (PathSemClosedPred lang φ)) := by
  exact languageSortPredNaturality_commDi_pathSemClosed lang s seed q φ hPkg.liftEq

/-- Map a `Pattern → Prop` predicate into the representable sort fiber
`languageSortFiber lang s`, provided the naturality side condition
`languageSortPredNaturality`.

The construction is the subfunctor of `y(s)` selecting exactly those arrows
whose semantic action on `seed` satisfies `φ`. -/
noncomputable def languageSortFiber_ofPatternPred
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ) :
    languageSortFiber lang s := by
  refine
    { obj := fun X =>
        { h : (languageSortRepresentableObj lang s).obj X |
            φ (pathSem lang h seed) }
      map := ?_ }
  intro X Y f h hh
  change φ (pathSem lang (((languageSortRepresentableObj lang s).map f) h) seed)
  simpa [languageSortRepresentableObj, CategoryTheory.yoneda] using
    (hNat f.unop h hh)

/-- Naturality-by-construction: membership in
`languageSortFiber_ofPatternPred ...` is preserved by representable reindexing
maps. -/
theorem languageSortFiber_ofPatternPred_map_mem
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {X Y : Opposite (ConstructorObj lang)}
    (f : X ⟶ Y) (h : (languageSortRepresentableObj lang s).obj X)
    (hh : h ∈ (languageSortFiber_ofPatternPred lang s seed φ hNat).obj X) :
    ((languageSortRepresentableObj lang s).map f h) ∈
      (languageSortFiber_ofPatternPred lang s seed φ hNat).obj Y := by
  exact (languageSortFiber_ofPatternPred lang s seed φ hNat).map f hh

/-- Subobject form of `languageSortFiber_ofPatternPred`, for use with
subobject-level theorems (e.g. Beck–Chevalley). -/
noncomputable def languageSortFiber_ofPatternPred_subobject
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ) :
    CategoryTheory.Subobject (languageSortRepresentableObj lang s) :=
  (CategoryTheory.Subfunctor.orderIsoSubobject
    (F := languageSortRepresentableObj lang s)).toEquiv
      (languageSortFiber_ofPatternPred lang s seed φ hNat)

/-- Canonical conversion: representable fiber element to subobject form. -/
noncomputable def languageSortFiber_toSubobject
    (lang : LanguageDef) (s : LangSort lang)
    (F : languageSortFiber lang s) :
    CategoryTheory.Subobject (languageSortRepresentableObj lang s) :=
  (CategoryTheory.Subfunctor.orderIsoSubobject
    (F := languageSortRepresentableObj lang s)).toEquiv F

/-- Round-trip on the fiber side after `languageSortFiber_toSubobject`. -/
theorem languageSortFiber_toSubobject_roundtrip
    (lang : LanguageDef) (s : LangSort lang)
    (F : languageSortFiber lang s) :
    (CategoryTheory.Subfunctor.orderIsoSubobject
      (F := languageSortRepresentableObj lang s)).invFun
      (languageSortFiber_toSubobject lang s F) = F := by
  simpa [languageSortFiber_toSubobject] using
    (CategoryTheory.Subfunctor.orderIsoSubobject
      (F := languageSortRepresentableObj lang s)).toEquiv.left_inv F

/-- Characteristic map associated to `languageSortFiber_ofPatternPred` via the
representable-fiber equivalence `Sub(y(s)) ≃ (y(s) ⟶ Ω)`. -/
noncomputable def languageSortFiber_ofPatternPred_characteristicMap
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ) :
    ((languageSortRepresentableObj lang s) ⟶
      Mettapedia.GSLT.Topos.omegaFunctor (C := ConstructorObj lang)) :=
  (languageSortFiber_characteristicEquiv (lang := lang) (s := s)).symm
    (languageSortFiber_ofPatternPred lang s seed φ hNat)

/-- The characteristic map round-trip for `languageSortFiber_ofPatternPred`. -/
theorem languageSortFiber_ofPatternPred_characteristicMap_spec
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ) :
    (languageSortFiber_characteristicEquiv (lang := lang) (s := s))
    (languageSortFiber_ofPatternPred_characteristicMap
          lang s seed φ hNat)
      =
    languageSortFiber_ofPatternPred lang s seed φ hNat := by
  simp [languageSortFiber_ofPatternPred_characteristicMap]

/-- Membership in the representable sort fiber induced from a predicate is
definitionally equivalent to evaluating that predicate at the semantically
reached term. -/
theorem languageSortFiber_ofPatternPred_mem_iff
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {X : Opposite (ConstructorObj lang)}
    (h : (languageSortRepresentableObj lang s).obj X) :
    h ∈ (languageSortFiber_ofPatternPred lang s seed φ hNat).obj X
      ↔
    φ (pathSem lang h seed) := by
  rfl

/-- OSLF `satisfies` form of `languageSortFiber_ofPatternPred_mem_iff`. -/
theorem languageSortFiber_ofPatternPred_mem_iff_satisfies
    (lang : LanguageDef) (procSort : String := "Proc")
    (s : LangSort lang)
    (seed : Pattern)
    (φ : (langOSLF lang procSort).Pred s.val)
    (hNat : languageSortPredNaturality lang s seed φ)
    {X : Opposite (ConstructorObj lang)}
    (h : (languageSortRepresentableObj lang s).obj X) :
    h ∈ (languageSortFiber_ofPatternPred lang s seed φ hNat).obj X
      ↔
    (langOSLF lang procSort).satisfies (S := s.val) (pathSem lang h seed) φ := by
  rfl

/-- Executable-semantics compatibility for the concrete `rhoCalc` process sort:
membership in the representable fiber induced from `langOSLF` process predicates
is exactly `satisfies` at the semantically reached process state. -/
theorem rhoProc_langOSLF_predicate_to_fiber_mem_iff
    (seed : Pattern)
    (φ : (langOSLF rhoCalc "Proc").Pred "Proc")
    (hNat : languageSortPredNaturality rhoCalc rhoProc seed φ)
    {X : Opposite (ConstructorObj rhoCalc)}
    (h : (languageSortRepresentableObj rhoCalc rhoProc).obj X) :
  h ∈ (languageSortFiber_ofPatternPred rhoCalc rhoProc seed φ hNat).obj X
      ↔
    (langOSLF rhoCalc "Proc").satisfies (pathSem rhoCalc h seed) φ := by
  simpa using
    (languageSortFiber_ofPatternPred_mem_iff_satisfies
      (lang := rhoCalc) (procSort := "Proc")
      (s := rhoProc) (seed := seed) (φ := φ) (hNat := hNat) (h := h))

/-- Interface-selected OSLF Proc-predicate type for rhoCalc. -/
abbrev rhoProcOSLFUsingPred : Type :=
  (oslf_fibrationUsing
      (langRewriteSystem rhoCalc "Proc")
      (langOSLF rhoCalc "Proc")
      (defaultSortCategoryInterface (langRewriteSystem rhoCalc "Proc"))).Sub
    (CategoryTheory.Discrete.mk "Proc")

/-- Direct bridge from interface-selected Proc predicates to the canonical
language-presheaf representable Proc fiber.

This is the concrete agreement map used by the interface-selected OSLF path
to enter the full representable/subobject semantics. -/
noncomputable def rhoProcOSLFUsingPred_to_languageSortFiber
    (seed : Pattern)
    (φ : rhoProcOSLFUsingPred)
    (hNat : languageSortPredNaturality rhoCalc rhoProc seed φ) :
    languageSortFiber rhoCalc rhoProc :=
  languageSortFiber_ofPatternPred rhoCalc rhoProc seed φ hNat

/-- Concrete rho-Proc package for path-based COMM lifting side conditions.

This packages the two structural obligations used by
`commDiWitnessLifting_of_pathSemLift` for the concrete predicate family
`rhoProcOSLFUsingPred`. -/
def rho_proc_pathSemLift_pkg
    (seed q : Pattern) (φ : rhoProcOSLFUsingPred) : Prop :=
  (∀ {a b : LangSort rhoCalc}
      (g : SortPath rhoCalc a b) (h : SortPath rhoCalc b rhoProc)
      {u : Pattern},
        Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
            pathSem rhoCalc h seed →
        Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (pathSem rhoCalc g u) q =
            pathSem rhoCalc (g.comp h) seed)
  ∧
  (∀ {a b : LangSort rhoCalc}
      (g : SortPath rhoCalc a b) {u : Pattern},
        φ u → φ (pathSem rhoCalc g u))

/-- Convert a concrete rho-Proc path-lift package into the structural COMM
witness lifting condition. -/
theorem rho_proc_commDiWitnessLifting_of_pkg
    (seed q : Pattern) (φ : rhoProcOSLFUsingPred)
    (hPkg : rho_proc_pathSemLift_pkg seed q φ) :
    commDiWitnessLifting rhoCalc rhoProc seed q φ := by
  exact commDiWitnessLifting_of_pathSemLift rhoCalc rhoProc seed q φ hPkg.1 hPkg.2

/-- Membership/specification for the interface-selected Proc-predicate bridge. -/
theorem rhoProcOSLFUsingPred_to_languageSortFiber_mem_iff
    (seed : Pattern)
    (φ : rhoProcOSLFUsingPred)
    (hNat : languageSortPredNaturality rhoCalc rhoProc seed φ)
    {X : Opposite (ConstructorObj rhoCalc)}
    (h : (languageSortRepresentableObj rhoCalc rhoProc).obj X) :
    h ∈ (rhoProcOSLFUsingPred_to_languageSortFiber seed φ hNat).obj X
      ↔
    (langOSLF rhoCalc "Proc").satisfies (S := "Proc") (pathSem rhoCalc h seed) φ := by
  simpa [rhoProcOSLFUsingPred_to_languageSortFiber] using
    (rhoProc_langOSLF_predicate_to_fiber_mem_iff seed φ hNat h)

/-- Sort-indexed predicate fibration induced from the canonical language
presheaf λ-theory by evaluating fibers on Yoneda-representable sorts. -/
noncomputable def languageSortPredicateFibration (lang : LanguageDef) :
    Mettapedia.GSLT.Core.SubobjectFibration (CategoryTheory.Discrete (LangSort lang)) where
  Sub := fun s => languageSortFiber lang s.as
  frame := by
    intro s
    dsimp [languageSortFiber, languagePresheafLambdaTheory]
    infer_instance

/-- Concrete rho process sort object in the canonical presheaf λ-theory lift. -/
noncomputable def rhoProcRepresentableObj :
    (languagePresheafLambdaTheory rhoCalc).Obj :=
  languageSortRepresentableObj rhoCalc rhoProc

/-- Concrete rho process sort fiber in the canonical presheaf λ-theory lift. -/
noncomputable def rhoProcSortFiber : Type :=
  languageSortFiber rhoCalc rhoProc

/-- Concrete rho process sort characteristic-map equivalence
`Sub(y(Proc)) ≃ (y(Proc) ⟶ Ω)`. -/
noncomputable def rhoProcSortFiber_characteristicEquiv :
    (rhoProcRepresentableObj ⟶
      Mettapedia.GSLT.Topos.omegaFunctor (C := ConstructorObj rhoCalc))
      ≃ rhoProcSortFiber := by
  simpa [rhoProcRepresentableObj, rhoProcSortFiber] using
    (languageSortFiber_characteristicEquiv (lang := rhoCalc) (s := rhoProc))

/-- Sort-indexed rho fibration induced from the canonical presheaf λ-theory. -/
noncomputable def rhoSortPredicateFibration :
    Mettapedia.GSLT.Core.SubobjectFibration (CategoryTheory.Discrete (LangSort rhoCalc)) :=
  languageSortPredicateFibration rhoCalc

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
#check @predFibrationSortApprox
#check @predFibrationUsing
#check @oslf_fibrationSortApprox
#check @oslf_fibrationUsing
#check @SortPresheafCategory
#check @predFibration
#check @oslf_fibration
#check @predFibration_presheafSortApprox_agreement
#check @sortFamilyPresheaf
#check @sortFamilySubfunctorEquivPred
#check @sortTermSubfunctorEquivPred
#check @PresheafToposBackend
#check @predFibrationPresheafUsing
#check @predFibrationPresheafPrimary
#check @typeSortsPredFibrationViaLambdaInterface
#check @typeSortsOSLFFibrationViaLambdaInterface
#check @typeSortsOSLFFiberFamily
#check @typeSortsOSLFFibrationUsing_presheafAgreement
#check @langOSLFFiberFamily
#check @langOSLFFibrationUsing_presheafAgreement
#check @rhoLangOSLFFiberFamily
#check @rhoLangOSLFFibrationUsing_presheafAgreement
#check @languagePresheafObj
#check @languagePresheafLambdaTheory
#check @languageSortRepresentableObj
#check @languageSortFiber
#check @languageSortPredNaturality
#check @commDiPred
#check @pathSem_commSubst
#check @languageSortPredNaturality_commDi
#check @CommDiPathSemLiftPkg
#check @commDiPathSemLiftPkg_of_liftEq
#check @commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
#check @commDiWitnessLifting_of_pathSemLiftPkg
#check @languageSortPredNaturality_commDi_pathSemClosed_of_pkg
#check @rho_proc_pathSemLift_pkg
#check @rho_proc_commDiWitnessLifting_of_pkg
#check @languageSortFiber_ofPatternPred
#check @languageSortFiber_ofPatternPred_map_mem
#check @languageSortFiber_ofPatternPred_subobject
#check @languageSortFiber_toSubobject
#check @languageSortFiber_toSubobject_roundtrip
#check @languageSortFiber_ofPatternPred_characteristicMap
#check @languageSortFiber_ofPatternPred_characteristicMap_spec
#check @languageSortFiber_ofPatternPred_mem_iff
#check @languageSortFiber_ofPatternPred_mem_iff_satisfies
#check @rhoProc_langOSLF_predicate_to_fiber_mem_iff
#check @rhoProcOSLFUsingPred
#check @rhoProcOSLFUsingPred_to_languageSortFiber
#check @languageSortFiber_characteristicEquiv
#check @languageSortPredicateFibration
#check @rhoProcRepresentableObj
#check @rhoProcSortFiber
#check @rhoProcSortFiber_characteristicEquiv
#check @rhoSortPredicateFibration

/-! ## Summary

**0 sorries. 0 axioms.**

### Proven Results

1. **Monotonicity**: `langDiamond_monotone`, `langBox_monotone`,
   `possiblyProp_monotone`, `relyProp_monotone`
2. **Modal adjunction**: `langModalAdjunction` (for any `LanguageDef`),
   `rhoModalAdjunction` (for rho-calculus)
3. **Sort category interface**: `SortCategoryInterface R` with default
   `defaultSortCategoryInterface R = Discrete R.Sorts`
4. **Sort-wise compatibility wrappers**:
   `predFibrationSortApprox` / `oslf_fibrationSortApprox` preserve the earlier
   sort-category approximation, with generic
   `predFibrationUsing`/`oslf_fibrationUsing` over any interface
5. **Concrete λ-theory interface use-site**:
   `typeSortsPredFibrationViaLambdaInterface` and
   `typeSortsOSLFFibrationViaLambdaInterface`
6. **Presheaf-topos default path**:
   `predFibration` / `oslf_fibration` now target
   `SortPresheafCategory` via `predFibrationPresheafPrimary`
   (Ω/subobject primary path), with selectable backend
   `predFibrationPresheafUsing`
7. **Concrete language-wrapper agreement (`rhoCalc`)**:
   `rhoLangOSLFFibrationUsing_presheafAgreement` gives an explicit
   non-toy instance where `oslf_fibrationUsing` aligns with the
   presheaf-primary backend over `langRewriteSystem rhoCalc`
8. **Generic + concrete language-wrapper agreements**:
   `langOSLFFibrationUsing_presheafAgreement` (generic over `LanguageDef`)
   and `rhoLangOSLFFibrationUsing_presheafAgreement` (concrete `rhoCalc`)
9. **Predicate→representable-fiber bridge**:
   `languageSortFiber_ofPatternPred` maps `Pattern → Prop` into
   `languageSortFiber lang s` under explicit precomposition naturality
   (`languageSortPredNaturality`)
10. **Concrete full language λ-theory lift**:
   `languagePresheafLambdaTheory` instantiates a real language-dependent
   λ-theory over `Psh(ConstructorObj lang)` (with Ω/subobject fibers), with
   representable sort objects `languageSortRepresentableObj` and
   characteristic-map equivalence `languageSortFiber_characteristicEquiv`

### Connection to GSLT

The `SubobjectFibration` structure bridges to `GSLT/Core/`:
- `LambdaTheoryCategory.lean`: Defines `SubobjectFibration` with
  CartesianMonoidalCategory, MonoidalClosed, HasFiniteLimits
- `ChangeOfBase.lean`: The adjoint triple `∃_f ⊣ f* ⊣ ∀_f` at the
  categorical level

### What Remains (Full Topos Lift)

With concrete language λ-theory lift now in place:
1. Connect sort-embedded representable fibers to executable OSLF synthesis
   (`langOSLF`) via an explicit compatibility theorem.
2. Use `ToposReduction` to make reduction edges primary as internal relations
   over language-presheaf objects (not only transport lemmas).
3. Integrate substitution/rewrite Beck-Chevalley directly over
   `languagePresheafLambdaTheory` representables.
-/

end Mettapedia.OSLF.Framework.CategoryBridge
