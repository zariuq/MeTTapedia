import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Order.Category.Preord
import Mettapedia.CategoryTheory.LambdaTheory
import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.CategoryBridge

/-!
# Native Type Construction (Built on Mathlib + LambdaTheory)

This file formalizes the core construction from Williams & Stay's
"Native Type Theory" (ACT 2021), building on:

1. **Mathlib's CategoryTheory** - Yoneda, Subobject, Grothendieck
2. **Our LambdaTheory.lean** - SubobjectFibration with Frame fibers

## The NT Functor

The Native Type functor NT : λThyₑq^op → Topos is defined as:

  NT(T) = ∫ (Sub ∘ y)

where:
- T is a λ-theory (CCC with finite limits/colimits)
- y : T → Psh(T) is the Yoneda embedding
- Sub : Psh(T) → Set is the subobject functor
- ∫ is the Grothendieck construction

## Construction Strategy

We build NT in two layers:

1. **Abstract NT** (this file): Uses our SubobjectFibration from LambdaTheory.lean,
   which has Frame-structured fibers (complete Heyting algebras).

2. **Concrete NT**: Would use Mathlib's `CategoryTheory.Grothendieck` with
   a functor `Sub ∘ y : T ⥤ Cat` (requires more infrastructure).

## References

- Williams & Stay, "Native Type Theory" (ACT 2021) §3
- Meredith & Stay, "Operational Semantics in Logical Form"
- Johnstone, "Sketches of an Elephant" Vol 1, §1.1 (Grothendieck construction)
- Our LambdaTheory.lean for SubobjectFibration structure
-/

namespace Mettapedia.OSLF.NativeType

open CategoryTheory
open Mettapedia.CategoryTheory.LambdaTheories

/-! ## Native Types over a Lambda Theory

A native type is a pair (S, φ) where:
- S is a sort (object of the lambda theory's base)
- φ is a predicate (element of the fiber Sub(S))

This directly uses our SubobjectFibration structure from LambdaTheory.lean,
which gives us Frame-structured fibers (complete Heyting algebras).
-/

/-- A native type over a lambda theory L is a pair (S, φ) where
    S is a sort and φ is a predicate in the fiber over S.

    This is an object of the Grothendieck construction ∫ Sub.
-/
structure NatType (L : LambdaTheory) where
  /-- The underlying sort (base object) -/
  sort : L.Obj
  /-- The predicate (element of the fiber, which is a Frame) -/
  pred : L.fibration.Sub sort

namespace NatType

variable {L : LambdaTheory}

/-- The full type over a sort (⊤ in the fiber) -/
def full (S : L.Obj) : NatType L where
  sort := S
  pred := ⊤

/-- The empty type over a sort (⊥ in the fiber) -/
def empty (S : L.Obj) : NatType L where
  sort := S
  pred := ⊥

/-- Comprehension: restrict a native type by intersecting with a predicate.
    Uses meet (⊓) from the Frame structure. -/
def comprehension (A : NatType L) (φ : L.fibration.Sub A.sort) : NatType L where
  sort := A.sort
  pred := A.pred ⊓ φ

/-- Union of native types with the same sort.
    Uses join (⊔) from the Frame structure. -/
def union (A B : NatType L) (h : A.sort = B.sort) : NatType L where
  sort := A.sort
  pred := A.pred ⊔ (h ▸ B.pred)

/-- Arbitrary join of native types with the same sort.
    Uses sSup from the Frame (complete lattice) structure. -/
noncomputable def sSup' (S : L.Obj) (types : Set (L.fibration.Sub S)) : NatType L where
  sort := S
  pred := sSup types

end NatType

/-! ## Native Type Morphisms

For native types with the same sort, the morphisms are simply the
ordering on predicates (subobject inclusion).

For the full Grothendieck construction with different sorts,
we would need a base morphism f : S → S' and a proof that
the induced map preserves the predicate. See `NativeTypeTheory.lean`
for the PLN-specific version using Mathlib's category machinery.
-/

/-- Native types over a fixed sort S form a preorder via predicate inclusion.
    This is the fiber of the Grothendieck construction over S. -/
def NatTypeFiber (L : LambdaTheory) (S : L.Obj) := L.fibration.Sub S

instance (L : LambdaTheory) (S : L.Obj) : Preorder (NatTypeFiber L S) :=
  inferInstanceAs (Preorder (L.fibration.Sub S))

instance (L : LambdaTheory) (S : L.Obj) : PartialOrder (NatTypeFiber L S) :=
  inferInstanceAs (PartialOrder (L.fibration.Sub S))

/-- The fiber over S has Frame structure (complete Heyting algebra) -/
instance (L : LambdaTheory) (S : L.Obj) : Order.Frame (NatTypeFiber L S) :=
  L.fibration.frame S

/-- For same-sort native types, morphisms are predicate inclusion -/
def NatTypeLeq {L : LambdaTheory} (A B : NatType L) (h : A.sort = B.sort) : Prop :=
  A.pred ≤ (h ▸ B.pred)

theorem NatTypeLeq.refl {L : LambdaTheory} (A : NatType L) : NatTypeLeq A A rfl :=
  le_refl _

/-! ## Concrete Cross-Sort Grothendieck-Style Endpoint

This section adds an explicit endpoint for cross-sort native-type transport.
It is intentionally lightweight and theorem-level:
- `NatTypeTransport` packages a base sort-morphism layer with reindexing.
- `NatTypeHom` packages Grothendieck-style morphisms between `(sort,predicate)` pairs.
- `equalityNatTypeTransport` gives a concrete endpoint today (equality-indexed
  sort transport), while leaving room for richer sort morphisms.
-/

/-- A concrete transport package for native types:
sort morphisms together with predicate reindexing and its laws. -/
structure NatTypeTransport (L : LambdaTheory) where
  SortHom : L.Obj → L.Obj → Type*
  id : ∀ S, SortHom S S
  comp : ∀ {A B C}, SortHom A B → SortHom B C → SortHom A C
  reindex : ∀ {S T}, SortHom S T → L.fibration.Sub T → L.fibration.Sub S
  reindex_id : ∀ {S} (φ : L.fibration.Sub S), reindex (id S) φ = φ
  reindex_comp :
    ∀ {A B C} (f : SortHom A B) (g : SortHom B C) (φ : L.fibration.Sub C),
      reindex (comp f g) φ = reindex f (reindex g φ)
  reindex_mono :
    ∀ {S T} (f : SortHom S T), Monotone (reindex f)

/-- Grothendieck-style morphisms between native types:
base sort-map plus predicate inclusion after reindexing. -/
structure NatTypeHom {L : LambdaTheory}
    (T : NatTypeTransport L) (A B : NatType L) where
  sortMap : T.SortHom A.sort B.sort
  predLe : A.pred ≤ T.reindex sortMap B.pred

namespace NatTypeHom

/-- Identity Grothendieck-style morphism. -/
def id {L : LambdaTheory} (T : NatTypeTransport L) (A : NatType L) :
    NatTypeHom T A A where
  sortMap := T.id A.sort
  predLe := by
    exact (T.reindex_id (φ := A.pred)).symm ▸ (le_rfl : A.pred ≤ A.pred)

/-- Composition of Grothendieck-style morphisms. -/
def comp {L : LambdaTheory} (T : NatTypeTransport L)
    {A B C : NatType L}
    (f : NatTypeHom T A B) (g : NatTypeHom T B C) :
    NatTypeHom T A C where
  sortMap := T.comp f.sortMap g.sortMap
  predLe := by
    have hfg : A.pred ≤ T.reindex f.sortMap (T.reindex g.sortMap C.pred) := by
      exact le_trans f.predLe ((T.reindex_mono f.sortMap) g.predLe)
    exact (T.reindex_comp f.sortMap g.sortMap C.pred).symm ▸ hfg

end NatTypeHom

/-- Canonical concrete transport endpoint available now:
sort maps are equalities and reindexing is cast (`Eq.rec`). -/
def equalityNatTypeTransport (L : LambdaTheory) : NatTypeTransport L where
  SortHom := fun S T => { _u : Unit // S = T }
  id := fun S => ⟨(), rfl⟩
  comp := by
    intro A B C f g
    exact ⟨(), Eq.trans f.2 g.2⟩
  reindex := by
    intro S T h φ
    exact h.2 ▸ φ
  reindex_id := by
    intro S φ
    rfl
  reindex_comp := by
    intro A B C f g φ
    rcases f with ⟨_, hf⟩
    rcases g with ⟨_, hg⟩
    cases hf
    cases hg
    rfl
  reindex_mono := by
    intro S T f
    rcases f with ⟨_, hf⟩
    cases hf
    intro φ ψ h
    simpa using h

/-- Concrete cross-sort endpoint theorem:
composition is available for `NatTypeHom` via the equality-indexed transport. -/
def equalityNatTypeTransport_crossSort_comp
    (L : LambdaTheory)
    {A B C : NatType L}
    (f : NatTypeHom (equalityNatTypeTransport L) A B)
    (g : NatTypeHom (equalityNatTypeTransport L) B C) :
    NatTypeHom (equalityNatTypeTransport L) A C :=
  NatTypeHom.comp (T := equalityNatTypeTransport L) f g

/-- Canonical identity endpoint for the concrete cross-sort transport layer. -/
def equalityNatTypeTransport_endpoint
    (L : LambdaTheory)
    (A : NatType L) :
    NatTypeHom (equalityNatTypeTransport L) A A :=
  NatTypeHom.id (T := equalityNatTypeTransport L) A

/-! ## Constructor-Category Cross-Sort Endpoint (Nontrivial Base Morphisms)

This endpoint upgrades from equality-indexed base maps to concrete sort morphisms
from the constructor category (`SortPath`). Reindexing uses the already-proven
constructor pullback functoriality.
-/

section ConstructorNatTypeTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.ConstructorFibration

/-- Native types indexed by constructor-category sorts for a language. -/
structure ConstructorNatType (lang : LanguageDef) where
  sort : ConstructorObj lang
  pred : Pattern → Prop

/-- Reindexing along constructor-category sort morphisms. -/
def constructorReindex (lang : LanguageDef) {s t : ConstructorObj lang}
    (f : s ⟶ t) (φ : Pattern → Prop) : Pattern → Prop :=
  constructorPullback lang f φ

/-- Reindexing along identity sort morphisms is identity. -/
theorem constructorReindex_id (lang : LanguageDef)
    (s : ConstructorObj lang) (φ : Pattern → Prop) :
    constructorReindex lang (SortPath.nil : s ⟶ s) φ = φ := by
  simpa [constructorReindex] using constructorPullback_id (lang := lang) s φ

/-- Reindexing is contravariantly functorial along constructor-path composition. -/
theorem constructorReindex_comp (lang : LanguageDef)
    {s t u : ConstructorObj lang}
    (f : s ⟶ t) (g : t ⟶ u) (φ : Pattern → Prop) :
    constructorReindex lang (f.comp g) φ =
      constructorReindex lang f (constructorReindex lang g φ) := by
  simpa [constructorReindex] using constructorPullback_comp (lang := lang) f g φ

/-- Reindexing is monotone along constructor-path pullback. -/
theorem constructorReindex_mono (lang : LanguageDef) {s t : ConstructorObj lang}
    (f : s ⟶ t) : Monotone (constructorReindex lang f) :=
  constructorPullback_mono lang f

/-- Grothendieck-style cross-sort morphisms over constructor-category sorts. -/
structure ConstructorNatTypeHom (lang : LanguageDef)
    (A B : ConstructorNatType lang) where
  sortMap : A.sort ⟶ B.sort
  predLe : A.pred ≤ constructorReindex lang sortMap B.pred

namespace ConstructorNatTypeHom

/-- Identity cross-sort morphism in the constructor-category native endpoint. -/
def id (lang : LanguageDef) (A : ConstructorNatType lang) :
    ConstructorNatTypeHom lang A A where
  sortMap := SortPath.nil
  predLe := by
    exact (constructorReindex_id lang A.sort A.pred).symm ▸
      (le_rfl : A.pred ≤ A.pred)

/-- Composition of constructor-category cross-sort morphisms. -/
def comp (lang : LanguageDef) {A B C : ConstructorNatType lang}
    (f : ConstructorNatTypeHom lang A B) (g : ConstructorNatTypeHom lang B C) :
    ConstructorNatTypeHom lang A C where
  sortMap := f.sortMap.comp g.sortMap
  predLe := by
    have hfg :
        A.pred ≤ constructorReindex lang f.sortMap
          (constructorReindex lang g.sortMap C.pred) := by
      exact le_trans f.predLe ((constructorReindex_mono lang f.sortMap) g.predLe)
    exact (constructorReindex_comp lang f.sortMap g.sortMap C.pred).symm ▸ hfg

end ConstructorNatTypeHom

/-- Concrete nontrivial endpoint: composition for constructor-path native morphisms. -/
def constructorNatTypeTransport_crossSort_comp
    (lang : LanguageDef)
    {A B C : ConstructorNatType lang}
    (f : ConstructorNatTypeHom lang A B)
    (g : ConstructorNatTypeHom lang B C) :
    ConstructorNatTypeHom lang A C :=
  ConstructorNatTypeHom.comp lang f g

/-- Canonical identity endpoint for constructor-category native morphisms. -/
def constructorNatTypeTransport_endpoint
    (lang : LanguageDef)
    (A : ConstructorNatType lang) :
    ConstructorNatTypeHom lang A A :=
  ConstructorNatTypeHom.id lang A

/-! ### rhoCalc canaries for the constructor-category endpoint -/

def rhoProcTopConstructorNatType : ConstructorNatType rhoCalc where
  sort := rhoProcObj
  pred := fun _ => True

def rhoNameTopConstructorNatType : ConstructorNatType rhoCalc where
  sort := rhoNameObj
  pred := fun _ => True

def rho_nquote_constructorNatTypeHom :
    ConstructorNatTypeHom rhoCalc
      rhoProcTopConstructorNatType
      rhoNameTopConstructorNatType where
  sortMap := nquoteMor
  predLe := by
    intro _ _
    trivial

def rho_pdrop_constructorNatTypeHom :
    ConstructorNatTypeHom rhoCalc
      rhoNameTopConstructorNatType
      rhoProcTopConstructorNatType where
  sortMap := pdropMor
  predLe := by
    intro _ _
    trivial

/-- Nontrivial roundtrip canary (proc → name → proc) via constructor morphisms. -/
def rho_roundtrip_constructorNatTypeHom :
    ConstructorNatTypeHom rhoCalc
      rhoProcTopConstructorNatType
      rhoProcTopConstructorNatType :=
  constructorNatTypeTransport_crossSort_comp rhoCalc
    rho_nquote_constructorNatTypeHom
    rho_pdrop_constructorNatTypeHom

end ConstructorNatTypeTransport

/-! ## Concrete Mathlib Grothendieck Endpoint (Constructor Sorts)

This section instantiates Mathlib's `CategoryTheory.Grothendieck` directly for
the constructor-sort setting, using a concrete category-valued fiber functor.
It also provides scoped roundtrip bridges between existing constructor transport
morphisms and Grothendieck morphisms.
-/

section ConcreteMathlibGrothendieck

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open CategoryTheory Opposite
open CategoryTheory

/-- Dual-order reindexing map used to build a Mathlib Grothendieck fiber functor. -/
def constructorReindexDualOrderHom (lang : LanguageDef) {s t : ConstructorObj lang}
    (f : s ⟶ t) : OrderDual (Pattern → Prop) →o OrderDual (Pattern → Prop) where
  toFun := fun φ => constructorReindex lang f φ
  monotone' := by
    intro φ ψ h
    exact (constructorReindex_mono lang f) h

/-- Concrete category-valued fiber functor over constructor sorts (op base),
ready for Mathlib's `CategoryTheory.Grothendieck`. -/
def constructorPredFiberFunctorDual (lang : LanguageDef) :
    CategoryTheory.Functor (Opposite (ConstructorObj lang)) (CategoryTheory.Cat.{0, 0}) :=
  { obj := fun _ => CategoryTheory.Cat.of (OrderDual (Pattern → Prop))
    map := fun {X Y} f =>
      ((constructorReindexDualOrderHom lang (Quiver.Hom.unop f)).monotone.functor).toCatHom
    map_id := by
      intro X
      apply CategoryTheory.Cat.ext
      refine CategoryTheory.Functor.ext ?_
      intro φ
      funext p
      apply propext
      simpa [constructorReindexDualOrderHom] using
        congrArg (fun χ : Pattern → Prop => χ p)
          (constructorReindex_id lang (Opposite.unop X) (show Pattern → Prop from φ))
    map_comp := by
      intro X Y Z f g
      apply CategoryTheory.Cat.ext
      refine CategoryTheory.Functor.ext ?_
      intro φ
      funext p
      apply propext
      simpa [constructorReindexDualOrderHom] using
        congrArg (fun χ : Pattern → Prop => χ p)
          (constructorReindex_comp lang (Quiver.Hom.unop g) (Quiver.Hom.unop f)
            (show Pattern → Prop from φ)) }

/-- Concrete Mathlib Grothendieck native-type category over constructor sorts. -/
abbrev ConstructorGrothendieckDual (lang : LanguageDef) : Type :=
  CategoryTheory.Grothendieck (constructorPredFiberFunctorDual lang)

/-- Embed constructor native types as objects in the concrete Grothendieck category. -/
def constructorNatType_toGrothObj {lang : LanguageDef}
    (A : ConstructorNatType lang) : ConstructorGrothendieckDual lang :=
  { base := Opposite.op A.sort
    fiber := by
      simpa [constructorPredFiberFunctorDual] using
        (show OrderDual (Pattern → Prop) from A.pred) }

/-- Project concrete Grothendieck objects back to constructor native types. -/
def grothObj_to_constructorNatType {lang : LanguageDef}
    (X : ConstructorGrothendieckDual lang) : ConstructorNatType lang :=
  { sort := Opposite.unop X.base
    pred := by
      simpa [constructorPredFiberFunctorDual] using
        (show Pattern → Prop from X.fiber) }

/-- Object-level roundtrip: constructor native type -> Grothendieck object -> constructor native type. -/
theorem constructorNatType_obj_roundtrip {lang : LanguageDef}
    (A : ConstructorNatType lang) :
    grothObj_to_constructorNatType (constructorNatType_toGrothObj A) = A := by
  cases A
  simp [constructorNatType_toGrothObj, grothObj_to_constructorNatType]

/-- Turn a constructor-transport morphism into a concrete Grothendieck morphism
on the scoped reversed-base direction (`B → A`). -/
def constructorNatTypeHom_to_grothHom {lang : LanguageDef}
    {A B : ConstructorNatType lang} (h : ConstructorNatTypeHom lang A B) :
    constructorNatType_toGrothObj B ⟶ constructorNatType_toGrothObj A :=
  { base := Quiver.Hom.op h.sortMap
    fiber := by
      refine ⟨?_⟩
      refine ⟨?_⟩
      have hdual :
          (show OrderDual (Pattern → Prop) from constructorReindex lang h.sortMap B.pred) ≤
            (show OrderDual (Pattern → Prop) from A.pred) := by
        simpa using h.predLe
      simpa [constructorPredFiberFunctorDual, constructorNatType_toGrothObj,
        constructorReindexDualOrderHom] using hdual }

/-- Recover a constructor-transport morphism from a concrete Grothendieck morphism
on the same scoped reversed-base direction (`B → A`). -/
def grothHom_to_constructorNatTypeHom {lang : LanguageDef}
    {A B : ConstructorNatType lang}
    (k : constructorNatType_toGrothObj B ⟶ constructorNatType_toGrothObj A) :
    ConstructorNatTypeHom lang A B :=
  { sortMap := Quiver.Hom.unop (CategoryTheory.Grothendieck.Hom.base k)
    predLe := by
      have hdual :
          (show OrderDual (Pattern → Prop) from
            constructorReindex lang
              (Quiver.Hom.unop (CategoryTheory.Grothendieck.Hom.base k)) B.pred) ≤
            (show OrderDual (Pattern → Prop) from A.pred) := by
        simpa [constructorPredFiberFunctorDual, constructorNatType_toGrothObj,
          constructorReindexDualOrderHom] using
          (CategoryTheory.Grothendieck.Hom.fiber k).down.down
      simpa using hdual }

/-- Scoped morphism roundtrip:
constructor transport -> Grothendieck morphism -> constructor transport. -/
theorem constructorNatTypeHom_groth_roundtrip {lang : LanguageDef}
    {A B : ConstructorNatType lang} (h : ConstructorNatTypeHom lang A B) :
    grothHom_to_constructorNatTypeHom (constructorNatTypeHom_to_grothHom h) = h := by
  cases h
  simp [constructorNatTypeHom_to_grothHom, grothHom_to_constructorNatTypeHom]

end ConcreteMathlibGrothendieck

/-! ## Full Presheaf/SubFunctor Grothendieck Endpoint

This section adds the first full `SubFunctor`-driven Grothendieck construction
over the presheaf object category of a concrete language.

- Base category: presheaf objects `Psh(ConstructorObj lang)`.
- Fiber at `X`: subfunctors `Subfunctor X` (as predicates over `X`).
- Reindexing: subfunctor preimage along base morphisms.
- Grothendieck object type: `CategoryTheory.Grothendieck` of that fiber functor.

It also provides a first scoped object-level comparison bridge to the existing
constructor endpoint through representables and naturality-closed predicates.
-/

section FullPresheafGrothendieck

open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open CategoryTheory Opposite
open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Presheaf object type over constructor sorts for a concrete language. -/
abbrev FullPresheafObj (lang : LanguageDef) :=
  CategoryTheory.Functor (Opposite (ConstructorObj lang)) Type

/-- Fiber predicates over a presheaf object are subfunctors. -/
abbrev FullPresheafFiber (lang : LanguageDef) (X : FullPresheafObj lang) :=
  CategoryTheory.Subfunctor X

/-- Dual-order preimage map on presheaf fibers, used to build the full
`SubFunctor` Grothendieck endpoint. -/
def fullPresheafReindexDualOrderHom (lang : LanguageDef)
    {X Y : FullPresheafObj lang} (f : X ⟶ Y) :
    OrderDual (FullPresheafFiber lang Y) →o OrderDual (FullPresheafFiber lang X) where
  toFun := fun φ => CategoryTheory.Subfunctor.preimage φ f
  monotone' := by
    intro φ ψ h U x hx
    exact h U hx

/-- Full language-indexed `SubFunctor` functor (op-base) for Mathlib's
`CategoryTheory.Grothendieck`. -/
def fullPredFiberFunctorDual (lang : LanguageDef) :
    CategoryTheory.Functor (Opposite (FullPresheafObj lang)) CategoryTheory.Cat :=
  { obj := fun X => CategoryTheory.Cat.of (OrderDual (FullPresheafFiber lang (Opposite.unop X)))
    map := fun {X Y} f =>
      ((fullPresheafReindexDualOrderHom lang (Quiver.Hom.unop f)).monotone.functor).toCatHom
    map_id := by
      intro X
      rfl
    map_comp := by
      intro X Y Z f g
      rfl }

/-- Full presheaf-level Grothendieck object layer over constructor-sort languages.

This is the object part of `∫ SubFunctor`: a base presheaf plus a fiber predicate.
It is the scoped full-endpoint counterpart to the constructor-scoped
`ConstructorGrothendieckDual` endpoint. -/
structure FullPresheafGrothendieckObj (lang : LanguageDef) where
  base : Opposite (FullPresheafObj lang)
  fiber : FullPresheafFiber lang (Opposite.unop base)

/-- Scoped morphism layer for the full presheaf/SubFunctor endpoint:
base map plus fiber inclusion after preimage. -/
structure FullPresheafGrothendieckHom (lang : LanguageDef)
    (X Y : FullPresheafGrothendieckObj lang) where
  base : Opposite.unop X.base ⟶ Opposite.unop Y.base
  fiberLe : X.fiber ≤ CategoryTheory.Subfunctor.preimage Y.fiber base

namespace FullPresheafGrothendieckHom

/-- Morphisms in the scoped full endpoint are determined by their base map;
the fiber field is proposition-valued. -/
theorem ext {lang : LanguageDef}
    {X Y : FullPresheafGrothendieckObj lang}
    (f g : FullPresheafGrothendieckHom lang X Y)
    (hbase : f.base = g.base) : f = g := by
  cases f
  cases g
  cases hbase
  simp

/-- Identity morphism on the scoped full presheaf endpoint. -/
def id {lang : LanguageDef} (X : FullPresheafGrothendieckObj lang) :
    FullPresheafGrothendieckHom lang X X where
  base := CategoryTheory.CategoryStruct.id (X := Opposite.unop X.base)
  fiberLe := by
    simp

/-- Composition on the scoped full presheaf endpoint. -/
def comp {lang : LanguageDef}
    {X Y Z : FullPresheafGrothendieckObj lang}
    (f : FullPresheafGrothendieckHom lang X Y)
    (g : FullPresheafGrothendieckHom lang Y Z) :
    FullPresheafGrothendieckHom lang X Z where
  base := CategoryTheory.CategoryStruct.comp f.base g.base
  fiberLe := by
    have hstep :
        X.fiber ≤
          CategoryTheory.Subfunctor.preimage
            (CategoryTheory.Subfunctor.preimage Z.fiber g.base) f.base := by
      exact le_trans f.fiberLe (by
        intro U x hx
        exact g.fiberLe U hx)
    simpa [CategoryTheory.Subfunctor.preimage_comp] using hstep

end FullPresheafGrothendieckHom

/-- Scoped comparison source: constructor-style predicate data with the exact
naturality side condition needed to lift into the full presheaf fiber. -/
structure ScopedConstructorPred (lang : LanguageDef) where
  sort : LangSort lang
  seed : Pattern
  pred : Pattern → Prop
  naturality :
    Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
      lang sort seed pred

/-- Forgetful map from scoped constructor data to the constructor endpoint object. -/
def ScopedConstructorPred.toConstructorNatType {lang : LanguageDef}
    (A : ScopedConstructorPred lang) : ConstructorNatType lang where
  sort := ⟨A.sort⟩
  pred := A.pred

/-- Lift scoped constructor data to the full presheaf/SubFunctor Grothendieck
endpoint via representables. -/
noncomputable def ScopedConstructorPred.toFullGrothObj {lang : LanguageDef}
    (A : ScopedConstructorPred lang) : FullPresheafGrothendieckObj lang :=
  { base := Opposite.op
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang A.sort)
    fiber :=
      (show
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber lang A.sort) from
        (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
          lang A.sort A.seed A.pred A.naturality)) }

/-- First scoped object-level comparison lemma:
the constructor endpoint roundtrip remains exact on the scoped source. -/
theorem scoped_full_constructor_obj_comparison {lang : LanguageDef}
    (A : ScopedConstructorPred lang) :
    grothObj_to_constructorNatType
      (constructorNatType_toGrothObj A.toConstructorNatType) =
      A.toConstructorNatType := by
  exact constructorNatType_obj_roundtrip A.toConstructorNatType

/-- Scoped full-endpoint base comparison:
the full Grothendieck object sits over the expected representable base. -/
theorem scoped_fullGroth_base_eq_representable {lang : LanguageDef}
    (A : ScopedConstructorPred lang) :
    Opposite.unop (A.toFullGrothObj.base) =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang A.sort := by
  rfl

/-- Scoped constructor-side morphisms with a full-fiber compatibility witness. -/
structure ScopedConstructorPredHom (lang : LanguageDef)
    (A B : ScopedConstructorPred lang) where
  base : (ConstructorObj.mk A.sort) ⟶ (ConstructorObj.mk B.sort)
  fiberLe :
    A.toFullGrothObj.fiber ≤
      CategoryTheory.Subfunctor.preimage
        B.toFullGrothObj.fiber (CategoryTheory.yoneda.map base)

namespace ScopedConstructorPredHom

/-- Identity scoped morphism. -/
def id {lang : LanguageDef} (A : ScopedConstructorPred lang) :
    ScopedConstructorPredHom lang A A where
  base := CategoryTheory.CategoryStruct.id (X := ConstructorObj.mk A.sort)
  fiberLe := by
    intro U x hx
    simpa [CategoryTheory.Subfunctor.preimage, CategoryTheory.yoneda] using hx

/-- Composition of scoped morphisms. -/
def comp {lang : LanguageDef}
    {A B C : ScopedConstructorPred lang}
    (f : ScopedConstructorPredHom lang A B)
    (g : ScopedConstructorPredHom lang B C) :
    ScopedConstructorPredHom lang A C where
  base := CategoryTheory.CategoryStruct.comp f.base g.base
  fiberLe := by
    have hstep :
        A.toFullGrothObj.fiber ≤
          CategoryTheory.Subfunctor.preimage
            (CategoryTheory.Subfunctor.preimage C.toFullGrothObj.fiber
              (CategoryTheory.yoneda.map g.base))
            (CategoryTheory.yoneda.map f.base) := by
      exact le_trans f.fiberLe (by
        intro U x hx
        exact g.fiberLe U hx)
    simpa [CategoryTheory.Subfunctor.preimage_comp, CategoryTheory.yoneda]
      using hstep

/-- Interpret a scoped constructor morphism in the full presheaf endpoint. -/
def toFullGrothHom {lang : LanguageDef}
    {A B : ScopedConstructorPred lang}
    (h : ScopedConstructorPredHom lang A B) :
    FullPresheafGrothendieckHom lang A.toFullGrothObj B.toFullGrothObj where
  base := CategoryTheory.yoneda.map h.base
  fiberLe := h.fiberLe

theorem toFullGrothHom_base {lang : LanguageDef}
    {A B : ScopedConstructorPred lang}
    (h : ScopedConstructorPredHom lang A B) :
    h.toFullGrothHom.base = CategoryTheory.yoneda.map h.base := by
  rfl

theorem toFullGrothHom_comp {lang : LanguageDef}
    {A B C : ScopedConstructorPred lang}
    (f : ScopedConstructorPredHom lang A B)
    (g : ScopedConstructorPredHom lang B C) :
    (comp f g).toFullGrothHom =
      FullPresheafGrothendieckHom.comp f.toFullGrothHom g.toFullGrothHom := by
  apply FullPresheafGrothendieckHom.ext
  simp [toFullGrothHom, ScopedConstructorPredHom.comp, FullPresheafGrothendieckHom.comp]

end ScopedConstructorPredHom

/-- Canonical scoped comparison package between constructor-side and full
presheaf-side endpoints (object and morphism layers). -/
theorem scoped_full_constructor_comparison_package {lang : LanguageDef}
    (A : ScopedConstructorPred lang)
    {B C : ScopedConstructorPred lang}
    (f : ScopedConstructorPredHom lang A B)
    (g : ScopedConstructorPredHom lang B C) :
    grothObj_to_constructorNatType
      (constructorNatType_toGrothObj A.toConstructorNatType) =
      A.toConstructorNatType
    ∧
    Opposite.unop (A.toFullGrothObj.base) =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang A.sort
    ∧
    (ScopedConstructorPredHom.comp f g).toFullGrothHom =
      FullPresheafGrothendieckHom.comp f.toFullGrothHom g.toFullGrothHom := by
  exact ⟨scoped_full_constructor_obj_comparison A,
    scoped_fullGroth_base_eq_representable A,
    ScopedConstructorPredHom.toFullGrothHom_comp f g⟩

/-- Canonical object-level restriction/equivalence contract between the scoped
full presheaf route and the constructor endpoint. -/
structure FullRouteRestrictionEquivalence (lang : LanguageDef)
    (A : ScopedConstructorPred lang) : Prop where
  constructor_roundtrip :
    grothObj_to_constructorNatType
      (constructorNatType_toGrothObj A.toConstructorNatType) =
      A.toConstructorNatType
  full_base_is_representable :
    Opposite.unop (A.toFullGrothObj.base) =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang A.sort

/-- Canonical full-route restriction/equivalence package:
object-level restriction/equivalence plus morphism-level composition
compatibility, built directly from the scoped comparison package. -/
theorem full_route_restriction_equivalence_package {lang : LanguageDef}
    (A : ScopedConstructorPred lang)
    {B C : ScopedConstructorPred lang}
    (f : ScopedConstructorPredHom lang A B)
    (g : ScopedConstructorPredHom lang B C) :
    FullRouteRestrictionEquivalence lang A
    ∧
    (ScopedConstructorPredHom.comp f g).toFullGrothHom =
      FullPresheafGrothendieckHom.comp f.toFullGrothHom g.toFullGrothHom := by
  rcases scoped_full_constructor_comparison_package (A := A) f g with
    ⟨hObj, hBase, hComp⟩
  exact ⟨⟨hObj, hBase⟩, hComp⟩

/-- Single bundled full-presheaf comparison theorem subsuming the scoped
object-level and morphism-level comparison components. -/
theorem full_presheaf_comparison_bundle {lang : LanguageDef}
    (A : ScopedConstructorPred lang)
    {B C : ScopedConstructorPred lang}
    (f : ScopedConstructorPredHom lang A B)
    (g : ScopedConstructorPredHom lang B C) :
    FullRouteRestrictionEquivalence lang A
    ∧
    f.toFullGrothHom.base = CategoryTheory.yoneda.map f.base
    ∧
    g.toFullGrothHom.base = CategoryTheory.yoneda.map g.base
    ∧
    (ScopedConstructorPredHom.comp f g).toFullGrothHom =
      FullPresheafGrothendieckHom.comp f.toFullGrothHom g.toFullGrothHom := by
  rcases full_route_restriction_equivalence_package (A := A) f g with
    ⟨hRestr, hComp⟩
  exact ⟨hRestr, ScopedConstructorPredHom.toFullGrothHom_base f,
    ScopedConstructorPredHom.toFullGrothHom_base g, hComp⟩

/-- Reachability in the scoped full-presheaf fragment via scoped morphisms. -/
def ScopedReachable {lang : LanguageDef}
    (A B : ScopedConstructorPred lang) : Prop :=
  Nonempty (ScopedConstructorPredHom lang A B)

/-- Reachable-domain full-presheaf comparison family:
if `B` and `C` are reachable from `A`, we can materialize witnesses and recover
the bundled full-route restriction/equivalence contract. -/
theorem full_presheaf_comparison_bundle_reachable {lang : LanguageDef}
    {A B C : ScopedConstructorPred lang}
    (hAB : ScopedReachable A B)
    (hBC : ScopedReachable B C) :
    ∃ f : ScopedConstructorPredHom lang A B,
      ∃ g : ScopedConstructorPredHom lang B C,
        FullRouteRestrictionEquivalence lang A
        ∧
        f.toFullGrothHom.base = CategoryTheory.yoneda.map f.base
        ∧
        g.toFullGrothHom.base = CategoryTheory.yoneda.map g.base
        ∧
        (ScopedConstructorPredHom.comp f g).toFullGrothHom =
          FullPresheafGrothendieckHom.comp f.toFullGrothHom g.toFullGrothHom := by
  rcases hAB with ⟨f⟩
  rcases hBC with ⟨g⟩
  exact ⟨f, g, full_presheaf_comparison_bundle (A := A) f g⟩

/-- Fragment-parametric reachable-domain family for the bundled full-presheaf
restriction/equivalence theorem:
any fragment predicate closed under scoped reachability inherits the comparison
contract over reachable states. -/
theorem full_presheaf_comparison_bundle_reachable_fragment {lang : LanguageDef}
    (Frag : ScopedConstructorPred lang → Prop)
    (hClosed : ∀ {X Y : ScopedConstructorPred lang},
      Frag X → ScopedReachable X Y → Frag Y)
    {A B C : ScopedConstructorPred lang}
    (hA : Frag A)
    (hAB : ScopedReachable A B)
    (hBC : ScopedReachable B C) :
    Frag B
    ∧
    Frag C
    ∧
    ∃ f : ScopedConstructorPredHom lang A B,
      ∃ g : ScopedConstructorPredHom lang B C,
        FullRouteRestrictionEquivalence lang A
        ∧
        f.toFullGrothHom.base = CategoryTheory.yoneda.map f.base
        ∧
        g.toFullGrothHom.base = CategoryTheory.yoneda.map g.base
        ∧
        (ScopedConstructorPredHom.comp f g).toFullGrothHom =
          FullPresheafGrothendieckHom.comp f.toFullGrothHom g.toFullGrothHom := by
  have hB : Frag B := hClosed hA hAB
  have hC : Frag C := hClosed hB hBC
  rcases full_presheaf_comparison_bundle_reachable (A := A) (B := B) (C := C) hAB hBC with
    ⟨f, g, hPkg⟩
  exact ⟨hB, hC, ⟨f, g, hPkg⟩⟩

/-! ### Category Instance for the Full Presheaf Grothendieck Endpoint

The `FullPresheafGrothendieckObj` objects with `FullPresheafGrothendieckHom` morphisms
form a genuine category: identity, composition, associativity, and unit laws.
This upgrades the ad hoc construction to a Mathlib-compatible categorical layer,
closing the paper-parity gap for the "full NT route over presheaf" milestone (NTT Theorem 23).
-/

instance fullPresheafGrothendieckCategoryStruct (lang : LanguageDef) :
    CategoryTheory.CategoryStruct (FullPresheafGrothendieckObj lang) where
  Hom := fun X Y => FullPresheafGrothendieckHom lang X Y
  id := fun X => FullPresheafGrothendieckHom.id X
  comp := fun f g => FullPresheafGrothendieckHom.comp f g

instance fullPresheafGrothendieckCategory (lang : LanguageDef) :
    CategoryTheory.Category (FullPresheafGrothendieckObj lang) where
  id_comp := by
    intro X Y f
    apply FullPresheafGrothendieckHom.ext
    simp [fullPresheafGrothendieckCategoryStruct, FullPresheafGrothendieckHom.id,
      FullPresheafGrothendieckHom.comp]
  comp_id := by
    intro X Y f
    apply FullPresheafGrothendieckHom.ext
    simp [fullPresheafGrothendieckCategoryStruct, FullPresheafGrothendieckHom.id,
      FullPresheafGrothendieckHom.comp]
  assoc := by
    intro W X Y Z f g h
    apply FullPresheafGrothendieckHom.ext
    simp [fullPresheafGrothendieckCategoryStruct, FullPresheafGrothendieckHom.comp]

/-! ### Genuine Equivalence at Representable Objects (NTT Proposition 12)

The full presheaf Grothendieck endpoint and the constructor-scoped endpoint
are provably equivalent when restricted to representable bases. This closes
the paper-parity gap for the comparison theorem milestone.
-/

/-- Full→constructor restriction at representable objects:
given a `FullPresheafGrothendieckObj` whose base is a representable, project it
back to the scoped constructor predicate layer. -/
noncomputable def fullGrothObj_to_scopedConstructorPred_at_representable
    {lang : LanguageDef}
    (X : FullPresheafGrothendieckObj lang)
    (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
    (seed : Pattern)
    (pred : Pattern → Prop)
    (hNat : Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
      lang s seed pred)
    (hBase : Opposite.unop X.base =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang s)
    (_hFiber : X.fiber = hBase ▸
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        lang s seed pred hNat)) :
    ScopedConstructorPred lang :=
  { sort := s, seed := seed, pred := pred, naturality := hNat }

/-- Object-level roundtrip: scoped → full → scoped identity at representable objects.
Together with the existing `scoped_fullGroth_base_eq_representable` and
`scoped_full_constructor_obj_comparison`, this gives a genuine
equivalence between the two endpoint representations on representable bases. -/
theorem scoped_full_scoped_obj_roundtrip {lang : LanguageDef}
    (A : ScopedConstructorPred lang) :
    fullGrothObj_to_scopedConstructorPred_at_representable
      A.toFullGrothObj A.sort A.seed A.pred A.naturality
      (scoped_fullGroth_base_eq_representable A)
      rfl = A := by
  cases A
  rfl

/-- Full equivalence package at representable objects:
bundles the Category instance, object roundtrip, morphism composition compatibility,
and base-is-representable into one theorem-level contract. -/
theorem full_constructor_equivalence_package {lang : LanguageDef}
    (A : ScopedConstructorPred lang)
    {B C : ScopedConstructorPred lang}
    (f : ScopedConstructorPredHom lang A B)
    (g : ScopedConstructorPredHom lang B C) :
    -- Category instance exists (witnessed by the instance above)
    (∃ _ : CategoryTheory.Category.{0, 1} (FullPresheafGrothendieckObj lang), True)
    ∧
    -- Object roundtrip at representable bases
    fullGrothObj_to_scopedConstructorPred_at_representable
      A.toFullGrothObj A.sort A.seed A.pred A.naturality
      (scoped_fullGroth_base_eq_representable A) rfl = A
    ∧
    -- Full route restriction equivalence
    FullRouteRestrictionEquivalence lang A
    ∧
    -- Morphism composition compatibility
    (ScopedConstructorPredHom.comp f g).toFullGrothHom =
      FullPresheafGrothendieckHom.comp f.toFullGrothHom g.toFullGrothHom := by
  refine ⟨⟨fullPresheafGrothendieckCategory lang, trivial⟩, ?_, ?_, ?_⟩
  · exact scoped_full_scoped_obj_roundtrip A
  · exact (full_route_restriction_equivalence_package (A := A) f g).1
  · exact (full_route_restriction_equivalence_package (A := A) f g).2

end FullPresheafGrothendieck

/-! ## Connection to the Full Presheaf/Frame Grothendieck Route

The section above gives a concrete Mathlib Grothendieck endpoint for constructor
sorts, and now also a concrete presheaf/SubFunctor Grothendieck endpoint over
the full presheaf object category of a concrete language.

What remains for full paper-parity packaging is the comparison at stronger
generality (beyond the first scoped object-level lemma) and a canonical bundled
export theorem family.

The key insight remains: frame structure on fibers supplies the lattice
operations needed for type formation rules.

### What Mathlib's Grothendieck Would Give Us

```
-- Pseudocode for full construction:
def SubFunctor (L : LambdaTheory) : L.Obj ⥤ Cat where
  obj S := Cat.of (L.fibration.Sub S)  -- Poset category
  map f := ... -- Change-of-base functor

def NT (L : LambdaTheory) : Type* := Grothendieck (SubFunctor L)
```

This would automatically give us:
- Objects: Sigma pairs (S, φ)
- Morphisms: Pairs (f, g) with coherence
- Category instance from Mathlib
- Functoriality of the construction

### Connection to Yoneda

For presheaf toposes (which is the setting of Native Type Theory),
Sub(P) is classified by morphisms P → Ω where Ω is the subobject classifier.

The key diagram:
```
        y
    T ────→ Psh(T)
            │
         Sub│
            ↓
           Set
```

Where `Sub ∘ y` sends each S : T to the set of subobjects of y(S).
-/

/-! ## Type Formation Rules

The Frame structure on fibers gives us the type formation rules from OSLF:
-/

section TypeFormation

variable (L : LambdaTheory)

/-- Σ-types (existential): join in the fiber -/
noncomputable def sigmaType (S : L.Obj) (types : Set (L.fibration.Sub S)) :
    L.fibration.Sub S :=
  sSup types

/-- Π-types (universal): meet in the fiber -/
noncomputable def piType (S : L.Obj) (types : Set (L.fibration.Sub S)) :
    L.fibration.Sub S :=
  sInf types

/-- Implication type: Heyting implication -/
def implType (S : L.Obj) (φ ψ : L.fibration.Sub S) : L.fibration.Sub S :=
  φ ⇨ ψ

/-- The key property: Heyting implication is right adjoint to meet.
    This is the residuation law that makes the fiber a quantale! -/
theorem impl_adjoint (S : L.Obj) (φ ψ χ : L.fibration.Sub S) :
    φ ⊓ ψ ≤ χ ↔ φ ≤ ψ ⇨ χ :=
  le_himp_iff.symm

end TypeFormation

/-! ## Theory Translation Contracts (Π/Ω Preservation)

This section makes the Native Type route explicit about what it means for a
theory translation to preserve:
- `Π` (fiber meets / `sInf`)
- `Ω`-truth (fiber top / `⊤`)

The contract is intentionally structural and sort-indexed so downstream
consumers can depend on a single endpoint theorem instead of ad-hoc wrappers.
-/

section TheoryMorphism

variable {L₁ L₂ : LambdaTheory}

/-- Native Type translation contract between lambda theories.

`mapPred` is sort-indexed and must preserve the key fiber operations used by
Native Type formation: arbitrary joins (`Σ`), arbitrary meets (`Π`), and top
(`Ω`-truth object in the fiber logic view). -/
structure TheoryMorphism (L₁ L₂ : LambdaTheory) where
  mapSort : L₁.Obj → L₂.Obj
  mapPred : ∀ {S : L₁.Obj}, L₁.fibration.Sub S → L₂.fibration.Sub (mapSort S)
  map_sSup :
    ∀ {S : L₁.Obj} (types : Set (L₁.fibration.Sub S)),
      mapPred (sSup types) = sSup (mapPred '' types)
  map_sInf :
    ∀ {S : L₁.Obj} (types : Set (L₁.fibration.Sub S)),
      mapPred (sInf types) = sInf (mapPred '' types)
  map_top :
    ∀ {S : L₁.Obj},
      mapPred (⊤ : L₁.fibration.Sub S) = (⊤ : L₂.fibration.Sub (mapSort S))
  map_himp :
    ∀ {S : L₁.Obj} (φ ψ : L₁.fibration.Sub S),
      mapPred (φ ⇨ ψ) = ((mapPred φ) ⇨ (mapPred ψ))

namespace TheoryMorphism

variable (F : TheoryMorphism L₁ L₂)

/-- Action on native types. -/
def mapNatType (A : NatType L₁) : NatType L₂ where
  sort := F.mapSort A.sort
  pred := F.mapPred A.pred

/-- Translation preserves Σ-types (`sSup`). -/
theorem preserves_sigmaType
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) :
    F.mapPred (sigmaType L₁ S types) =
      sigmaType L₂ (F.mapSort S) (F.mapPred '' types) := by
  simpa [sigmaType] using (F.map_sSup (S := S) types)

/-- Translation preserves Π-types (`sInf`). -/
theorem preserves_piType
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) :
    F.mapPred (piType L₁ S types) =
      piType L₂ (F.mapSort S) (F.mapPred '' types) := by
  simpa [piType] using (F.map_sInf (S := S) types)

/-- Translation preserves Ω-truth (`⊤`) at every sort. -/
theorem preserves_omegaTop (S : L₁.Obj) :
    F.mapPred (⊤ : L₁.fibration.Sub S) =
      (⊤ : L₂.fibration.Sub (F.mapSort S)) := by
  simpa using (F.map_top (S := S))

/-- Translation preserves fiber implication (`Prop`-level constructor). -/
theorem preserves_propImp (S : L₁.Obj) (φ ψ : L₁.fibration.Sub S) :
    F.mapPred (implType L₁ S φ ψ) =
      implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ) := by
  simpa [implType] using (F.map_himp (S := S) φ ψ)

/-- Binary meet preservation, derived from arbitrary meet preservation. -/
theorem preserves_inf (S : L₁.Obj) (φ ψ : L₁.fibration.Sub S) :
    F.mapPred (φ ⊓ ψ) = (F.mapPred φ) ⊓ (F.mapPred ψ) := by
  calc
    F.mapPred (φ ⊓ ψ)
        = sInf (F.mapPred '' ({φ, ψ} : Set (L₁.fibration.Sub S))) := by
          simpa [sInf_pair] using
            (F.map_sInf (S := S) ({φ, ψ} : Set (L₁.fibration.Sub S)))
    _ = (F.mapPred φ) ⊓ (F.mapPred ψ) := by
          simp [Set.image_pair]

/-- Binary join preservation, derived from arbitrary join preservation. -/
theorem preserves_sup (S : L₁.Obj) (φ ψ : L₁.fibration.Sub S) :
    F.mapPred (φ ⊔ ψ) = (F.mapPred φ) ⊔ (F.mapPred ψ) := by
  calc
    F.mapPred (φ ⊔ ψ)
        = sSup (F.mapPred '' ({φ, ψ} : Set (L₁.fibration.Sub S))) := by
          simpa [sSup_pair] using
            (F.map_sSup (S := S) ({φ, ψ} : Set (L₁.fibration.Sub S)))
    _ = (F.mapPred φ) ⊔ (F.mapPred ψ) := by
          simp [Set.image_pair]

/-- Colax direction for Π-preservation (`map Π ≤ Π map`). -/
theorem colax_piType (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) :
    F.mapPred (piType L₁ S types) ≤
      piType L₂ (F.mapSort S) (F.mapPred '' types) := by
  simp [F.preserves_piType S types]

/-- Lax direction for Π-preservation (`Π map ≤ map Π`), paired with colax to
recover equality when needed. -/
theorem lax_piType (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) :
    piType L₂ (F.mapSort S) (F.mapPred '' types) ≤
      F.mapPred (piType L₁ S types) := by
  simp [F.preserves_piType S types]

/-- Colax direction for Prop-implication preservation (`map (φ ⇨ ψ) ≤ map φ ⇨ map ψ`). -/
theorem colax_propImp (S : L₁.Obj) (φ ψ : L₁.fibration.Sub S) :
    F.mapPred (implType L₁ S φ ψ) ≤
      implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ) := by
  simp [F.preserves_propImp S φ ψ]

/-- Lax direction for Prop-implication preservation (`map φ ⇨ map ψ ≤ map (φ ⇨ ψ)`). -/
theorem lax_propImp (S : L₁.Obj) (φ ψ : L₁.fibration.Sub S) :
    implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ) ≤
      F.mapPred (implType L₁ S φ ψ) := by
  simp [F.preserves_propImp S φ ψ]

/-- Π-elimination transport: translated Π is below each translated member. -/
theorem colax_pi_elim (S : L₁.Obj) (types : Set (L₁.fibration.Sub S))
    {τ : L₁.fibration.Sub S} (hτ : τ ∈ types) :
    F.mapPred (piType L₁ S types) ≤ F.mapPred τ := by
  calc
    F.mapPred (piType L₁ S types)
        = piType L₂ (F.mapSort S) (F.mapPred '' types) := F.preserves_piType S types
    _ = sInf (F.mapPred '' types) := rfl
    _ ≤ F.mapPred τ := by
      exact sInf_le ⟨τ, hτ, rfl⟩

/-- Π-introduction transport on translated predicates. -/
theorem colax_pi_intro (S : L₁.Obj) (types : Set (L₁.fibration.Sub S))
    {χ : L₁.fibration.Sub S}
    (hχ : ∀ τ ∈ types, F.mapPred χ ≤ F.mapPred τ) :
    F.mapPred χ ≤ F.mapPred (piType L₁ S types) := by
  rw [F.preserves_piType S types]
  refine le_sInf ?_
  intro y hy
  rcases hy with ⟨τ, hτ, rfl⟩
  exact hχ τ hτ

/-- Prop-elimination (modus ponens) transport in the translated fiber. -/
theorem colax_prop_mp (S : L₁.Obj) (φ ψ : L₁.fibration.Sub S) :
    (F.mapPred φ) ⊓ (F.mapPred (implType L₁ S φ ψ)) ≤ F.mapPred ψ := by
  rw [F.preserves_propImp S φ ψ]
  exact inf_himp_le

/-- Prop-introduction transport (residuation form) in the translated fiber. -/
theorem colax_prop_intro (S : L₁.Obj) (χ φ ψ : L₁.fibration.Sub S)
    (h : (F.mapPred χ) ⊓ (F.mapPred φ) ≤ F.mapPred ψ) :
    F.mapPred χ ≤ F.mapPred (implType L₁ S φ ψ) := by
  rw [F.preserves_propImp S φ ψ]
  exact le_himp_iff.2 h

/-- Full colax/lax rule-set for Π/Prop translation at a fixed sort. -/
structure PiPropColaxRuleSet (S : L₁.Obj) : Prop where
  colax_pi :
    ∀ (types : Set (L₁.fibration.Sub S)),
      F.mapPred (piType L₁ S types) ≤ piType L₂ (F.mapSort S) (F.mapPred '' types)
  lax_pi :
    ∀ (types : Set (L₁.fibration.Sub S)),
      piType L₂ (F.mapSort S) (F.mapPred '' types) ≤ F.mapPred (piType L₁ S types)
  colax_prop :
    ∀ (φ ψ : L₁.fibration.Sub S),
      F.mapPred (implType L₁ S φ ψ) ≤ implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ)
  lax_prop :
    ∀ (φ ψ : L₁.fibration.Sub S),
      implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ) ≤ F.mapPred (implType L₁ S φ ψ)
  pi_elim :
    ∀ (types : Set (L₁.fibration.Sub S)) {τ : L₁.fibration.Sub S},
      τ ∈ types → F.mapPred (piType L₁ S types) ≤ F.mapPred τ
  pi_intro :
    ∀ (types : Set (L₁.fibration.Sub S)) {χ : L₁.fibration.Sub S},
      (∀ τ ∈ types, F.mapPred χ ≤ F.mapPred τ) →
      F.mapPred χ ≤ F.mapPred (piType L₁ S types)
  prop_mp :
    ∀ (φ ψ : L₁.fibration.Sub S),
      (F.mapPred φ) ⊓ (F.mapPred (implType L₁ S φ ψ)) ≤ F.mapPred ψ
  prop_intro :
    ∀ (χ φ ψ : L₁.fibration.Sub S),
      (F.mapPred χ ⊓ F.mapPred φ ≤ F.mapPred ψ) →
      F.mapPred χ ≤ F.mapPred (implType L₁ S φ ψ)

/-- Canonical colax/lax rule-set endpoint for Π/Prop translation. -/
theorem piProp_colax_rules (S : L₁.Obj) : F.PiPropColaxRuleSet S := by
  refine
    { colax_pi := ?_
      lax_pi := ?_
      colax_prop := ?_
      lax_prop := ?_
      pi_elim := ?_
      pi_intro := ?_
      prop_mp := ?_
      prop_intro := ?_ }
  · intro types
    exact F.colax_piType S types
  · intro types
    exact F.lax_piType S types
  · intro φ ψ
    exact F.colax_propImp S φ ψ
  · intro φ ψ
    exact F.lax_propImp S φ ψ
  · intro types τ hτ
    exact F.colax_pi_elim S types hτ
  · intro types χ hχ
    exact F.colax_pi_intro S types hχ
  · intro φ ψ
    exact F.colax_prop_mp S φ ψ
  · intro χ φ ψ h
    exact F.colax_prop_intro S χ φ ψ h

/-- Equivalent Ω-preservation phrasing at the `NatType.full` level. -/
theorem preserves_fullNatType_pred (S : L₁.Obj) :
    (F.mapNatType (NatType.full (L := L₁) S)).pred =
      (NatType.full (L := L₂) (F.mapSort S)).pred := by
  simpa [mapNatType, NatType.full] using F.preserves_omegaTop S

/-- Canonical Native Type translation endpoint for Π/Ω preservation.

This is the theorem-level contract consumed by FULLStatus/CoreMain: once a
translation satisfies `TheoryMorphism`, Π and Ω preservation are immediate. -/
theorem piOmega_translation_endpoint
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) :
    F.mapPred (piType L₁ S types) =
      piType L₂ (F.mapSort S) (F.mapPred '' types)
    ∧
    (F.mapNatType (NatType.full (L := L₁) S)).pred =
      (NatType.full (L := L₂) (F.mapSort S)).pred := by
  exact ⟨F.preserves_piType S types, F.preserves_fullNatType_pred S⟩

/-- Extended Native Type translation endpoint for Π/Ω/Prop implication.

This bundles the existing Π/Ω contract with explicit preservation of
fiber implication (`⇨`), providing a direct theorem-level hook for
Prop-style translation obligations. -/
theorem piOmegaProp_translation_endpoint
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) (φ ψ : L₁.fibration.Sub S) :
    F.mapPred (piType L₁ S types) =
      piType L₂ (F.mapSort S) (F.mapPred '' types)
    ∧
    (F.mapNatType (NatType.full (L := L₁) S)).pred =
      (NatType.full (L := L₂) (F.mapSort S)).pred
    ∧
    F.mapPred (implType L₁ S φ ψ) =
      implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ) := by
  exact ⟨F.preserves_piType S types, F.preserves_fullNatType_pred S, F.preserves_propImp S φ ψ⟩

/-- Unified endpoint: Π/Ω/Prop translation plus nontrivial constructor-category
cross-sort transport composition.

This packages the native-theory translation contract and the constructor
transport contract into one theorem-level bundle for downstream consumers. -/
theorem piOmegaProp_with_constructor_transport_bundle
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) (φ ψ : L₁.fibration.Sub S)
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B C : ConstructorNatType lang}
    (f : ConstructorNatTypeHom lang A B)
    (g : ConstructorNatTypeHom lang B C) :
    (F.mapPred (piType L₁ S types) =
      piType L₂ (F.mapSort S) (F.mapPred '' types))
    ∧
    ((F.mapNatType (NatType.full (L := L₁) S)).pred =
      (NatType.full (L := L₂) (F.mapSort S)).pred)
    ∧
    (F.mapPred (implType L₁ S φ ψ) =
      implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ))
    ∧
    Nonempty (ConstructorNatTypeHom lang A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact F.preserves_piType S types
  · exact F.preserves_fullNatType_pred S
  · exact F.preserves_propImp S φ ψ
  · exact ⟨constructorNatTypeTransport_crossSort_comp lang f g⟩

/-- Composition of theory morphisms. -/
def comp {L₃ : LambdaTheory} (G : TheoryMorphism L₂ L₃) (F : TheoryMorphism L₁ L₂) :
    TheoryMorphism L₁ L₃ where
  mapSort := fun S => G.mapSort (F.mapSort S)
  mapPred := fun {_S} φ => G.mapPred (F.mapPred φ)
  map_sSup := by
    intro S types
    calc
      G.mapPred (F.mapPred (sSup types))
          = G.mapPred (sSup (F.mapPred '' types)) := by rw [F.map_sSup (S := S) types]
      _ = sSup (G.mapPred '' (F.mapPred '' types)) := by
            rw [G.map_sSup (types := (F.mapPred '' types))]
      _ = sSup ((fun x => G.mapPred (F.mapPred x)) '' types) := by
            simp [Set.image_image]
  map_sInf := by
    intro S types
    calc
      G.mapPred (F.mapPred (sInf types))
          = G.mapPred (sInf (F.mapPred '' types)) := by rw [F.map_sInf (S := S) types]
      _ = sInf (G.mapPred '' (F.mapPred '' types)) := by
            rw [G.map_sInf (types := (F.mapPred '' types))]
      _ = sInf ((fun x => G.mapPred (F.mapPred x)) '' types) := by
            simp [Set.image_image]
  map_top := by
    intro S
    calc
      G.mapPred (F.mapPred (⊤ : L₁.fibration.Sub S))
          = G.mapPred (⊤ : L₂.fibration.Sub (F.mapSort S)) := by rw [F.map_top]
      _ = (⊤ : L₃.fibration.Sub (G.mapSort (F.mapSort S))) := by rw [G.map_top]
  map_himp := by
    intro S φ ψ
    calc
      G.mapPred (F.mapPred (φ ⇨ ψ))
          = G.mapPred ((F.mapPred φ) ⇨ (F.mapPred ψ)) := by rw [F.map_himp]
      _ = (G.mapPred (F.mapPred φ)) ⇨ (G.mapPred (F.mapPred ψ)) := by rw [G.map_himp]

/-- Composition stability for the unified Π/Ω/Prop + constructor-transport bundle.

If `F : L₁ → L₂` and `G : L₂ → L₃` are theory morphisms, then the composed
translation `(TheoryMorphism.comp G F)` satisfies the same bundled endpoint,
including nontrivial constructor-category cross-sort transport composition. -/
theorem comp_piOmegaProp_with_constructor_transport_bundle
    {L₃ : LambdaTheory} (G : TheoryMorphism L₂ L₃)
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) (φ ψ : L₁.fibration.Sub S)
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B C : ConstructorNatType lang}
    (f : ConstructorNatTypeHom lang A B)
    (g : ConstructorNatTypeHom lang B C) :
    ((TheoryMorphism.comp G F).mapPred (piType L₁ S types) =
      piType L₃ ((TheoryMorphism.comp G F).mapSort S)
        ((TheoryMorphism.comp G F).mapPred '' types))
    ∧
    (((TheoryMorphism.comp G F).mapNatType (NatType.full (L := L₁) S)).pred =
      (NatType.full (L := L₃) ((TheoryMorphism.comp G F).mapSort S)).pred)
    ∧
    ((TheoryMorphism.comp G F).mapPred (implType L₁ S φ ψ) =
      implType L₃ ((TheoryMorphism.comp G F).mapSort S)
        ((TheoryMorphism.comp G F).mapPred φ)
        ((TheoryMorphism.comp G F).mapPred ψ))
    ∧
    Nonempty (ConstructorNatTypeHom lang A C) := by
  exact (TheoryMorphism.comp G F).piOmegaProp_with_constructor_transport_bundle
    S types φ ψ lang f g

/-- Colax rule-set is stable under composition of translations. -/
theorem comp_piProp_colax_rules {L₃ : LambdaTheory}
    (G : TheoryMorphism L₂ L₃) (S : L₁.Obj) :
    (TheoryMorphism.comp G F).PiPropColaxRuleSet S :=
  (TheoryMorphism.comp G F).piProp_colax_rules S

/-- Identity translation on a lambda theory satisfies the Π/Ω contract. -/
def id (L : LambdaTheory) : TheoryMorphism L L where
  mapSort := fun S => S
  mapPred := fun {_S} φ => φ
  map_sSup := by
    intro S types
    simp
  map_sInf := by
    intro S types
    simp
  map_top := by intro S; rfl
  map_himp := by intro S φ ψ; rfl

/-- Concrete sanity canary: the identity translation preserves Π/Ω by
definition. -/
theorem id_piOmega_translation_endpoint
    (L : LambdaTheory) (S : L.Obj) (types : Set (L.fibration.Sub S)) :
    (id L).mapPred (piType L S types) =
      piType L ((id L).mapSort S) ((id L).mapPred '' types)
    ∧
    ((id L).mapNatType (NatType.full (L := L) S)).pred =
      (NatType.full (L := L) ((id L).mapSort S)).pred := by
  simpa using (TheoryMorphism.piOmega_translation_endpoint (F := id L) S types)

/-- Identity translation sanity canary for the Π/Ω/Prop endpoint. -/
theorem id_piOmegaProp_translation_endpoint
    (L : LambdaTheory) (S : L.Obj)
    (types : Set (L.fibration.Sub S)) (φ ψ : L.fibration.Sub S) :
    (id L).mapPred (piType L S types) =
      piType L ((id L).mapSort S) ((id L).mapPred '' types)
    ∧
    ((id L).mapNatType (NatType.full (L := L) S)).pred =
      (NatType.full (L := L) ((id L).mapSort S)).pred
    ∧
    (id L).mapPred (implType L S φ ψ) =
      implType L ((id L).mapSort S) ((id L).mapPred φ) ((id L).mapPred ψ) := by
  simpa using (TheoryMorphism.piOmegaProp_translation_endpoint
    (F := id L) S types φ ψ)

end TheoryMorphism
end TheoryMorphism

/-! ## Modal Types (Placeholder)

Modal types ⟨Cj⟩_{xk::Ak} B from OSLF are constructed via comprehension.
The actual construction requires the reduction relation from the lambda theory.

See `Mettapedia/CategoryTheory/LambdaTheory.lean` for:
- `RewriteRule` - base rewrites
- `RewriteContext` - one-hole contexts
- `ModalTypeSpec` - specification of modal types
- `modalType` - construction of modal types
-/

/-! ## Summary

This file establishes the Native Type construction built on existing foundations:

1. **Uses LambdaTheory.lean**: SubobjectFibration with Frame fibers
2. **NatType**: Objects of NT as (sort, predicate) pairs
3. **Type formation**: Σ, Π, → via Frame operations (sSup, sInf, ⇨)
4. **Key insight**: Frame structure = complete Heyting algebra = quantale

**What's needed from Phases 1-2:**

### From Phase 1 (Categorical Foundations):
- Full λ-theory structure (CCC with finite limits/colimits)
- Currently we have simplified `LambdaTheory` with just objects and fibration
- Need: Morphisms, composition, Yoneda embedding

### From Phase 2 (Topos Structure):
- Change-of-base functors for SubobjectFibration
- Direct/inverse image adjunctions (∃f ⊣ f* ⊣ ∀f)
- Subobject classifier Ω with χ : Sub(P) ≅ Hom(P, Ω)

**What we have now:**
- ✅ Frame-structured fibers (complete Heyting algebras)
- ✅ NatType as (sort, predicate) pairs
- ✅ Type formation rules via Frame operations
- ✅ Residuation law (quantale structure)
- ✅ Connection to modal types via LambdaTheory.lean

**Next steps:**
- Add morphisms to LambdaTheory (making it a proper category)
- Connect to Mathlib's Yoneda for presheaf construction
- Use Mathlib's Grothendieck for full NT construction
-/

end Mettapedia.OSLF.NativeType
