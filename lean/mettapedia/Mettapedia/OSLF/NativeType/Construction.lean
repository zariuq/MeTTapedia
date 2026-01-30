import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Subobject.Basic
import Mettapedia.CategoryTheory.LambdaTheory

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

/-! ## Connection to Mathlib's Grothendieck Construction

To use Mathlib's `CategoryTheory.Grothendieck` directly, we would need:

1. A functor `SubFunctor : L.Obj ⥤ Cat` where `SubFunctor.obj S = L.fibration.Sub S`
2. This requires making each fiber into a category (poset category from Frame)
3. Then `Grothendieck SubFunctor` gives us the full construction

For now, our simplified construction suffices for connecting to OSLF semantics.
The key insight is that the Frame structure on fibers gives us all the
lattice operations needed for type formation rules.

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
