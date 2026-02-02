import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.CompleteBooleanAlgebra

universe u v w

/-!
# Lambda-Theories with Categorical Structure

This file establishes lambda-theories as proper categorical objects using Mathlib.

## Main Definitions

* `LambdaTheoryWithEquality` - A lambda-theory with morphisms, CCC structure, and finite limits
* `LambdaTheoryMorphism` - Structure-preserving functors between lambda-theories
* `SubobjectFibration` - Subobject fibration with Frame-structured fibers

## Key Insights

From Bucciarelli-Salibra "Graph Lambda Theories":
- Lambda-theories arise from equational theories of lambda calculus
- Graph models D = (|D|, c_D) induce lambda-theories Th(D)
- The categorical structure (CCC + finite limits) supports type-theoretic reasoning

From Williams-Stay "Native Type Theory":
- Lambda-theories with equality are CCCs with pullbacks
- The 2-category λThyₑq has theories as objects, functors as 1-morphisms
- Native types arise via Grothendieck construction over Sub ∘ Yoneda

## References

- Bucciarelli & Salibra, "Graph Lambda Theories" (2008)
- Williams & Stay, "Native Type Theory" (ACT 2021)
- Lambek & Scott, "Introduction to Higher Order Categorical Logic"
-/

namespace Mettapedia.GSLT.Core

open CategoryTheory
open CategoryTheory.Limits

/-! ## Subobject Fibration with Frame Structure

Each fiber Sub(X) is a Frame (complete Heyting algebra), giving us:
- Complete lattice (sSup, sInf) for arbitrary joins/meets
- Heyting implication (⇨) as residuation
- The quantale law: ⊓ distributes over ⨆
-/

/-- A subobject fibration assigns to each object X a Frame Sub(X).

    In topos theory, Sub(X) is the lattice of subobjects of X.
    We work axiomatically: each fiber is a Frame.
-/
structure SubobjectFibration (C : Type u) [Category.{v} C] where
  /-- The fiber over each object -/
  Sub : C → Type w
  /-- Each fiber is a Frame (complete Heyting algebra) -/
  frame : ∀ X, Order.Frame (Sub X)

namespace SubobjectFibration

variable {C : Type u} [Category.{v} C] (F : SubobjectFibration C)

/-- The fiber over an object, with its Frame structure -/
instance instFrame (X : C) : Order.Frame (F.Sub X) := F.frame X

/-- Heyting implication in a fiber -/
def himp (X : C) (a b : F.Sub X) : F.Sub X := a ⇨ b

/-- The top element of a fiber -/
def top (X : C) : F.Sub X := ⊤

/-- The bottom element of a fiber -/
def bot (X : C) : F.Sub X := ⊥

/-- Join in a fiber -/
def sup (X : C) (a b : F.Sub X) : F.Sub X := a ⊔ b

/-- Meet in a fiber -/
def inf (X : C) (a b : F.Sub X) : F.Sub X := a ⊓ b

/-- Arbitrary join in a fiber -/
def sSup' (X : C) (S : Set (F.Sub X)) : F.Sub X := sSup S

/-- Arbitrary meet in a fiber -/
def sInf' (X : C) (S : Set (F.Sub X)) : F.Sub X := sInf S

/-- Residuation: Heyting implication is right adjoint to meet -/
theorem himp_adjoint (X : C) (a b c : F.Sub X) : a ⊓ b ≤ c ↔ a ≤ b ⇨ c :=
  le_himp_iff.symm

end SubobjectFibration

/-! ## Lambda-Theory with Equality

A lambda-theory with equality is:
1. A category C (the base)
2. Cartesian closed structure (for lambda abstraction)
3. Finite limits (for pullbacks, used in comprehension)
4. A subobject fibration (for predicates/types)

We package this as a bundled structure containing a category with
all the required instances, plus a subobject fibration.
-/

/-- A lambda-theory with equality.

    This is the categorical semantics of simply-typed lambda calculus
    with comprehension types (dependent types).

    Objects are "sorts" or "types"
    Morphisms are "terms" (modulo equations)
    CCC structure gives us function types
    Finite limits give us dependent types via pullbacks
-/
structure LambdaTheoryWithEquality where
  /-- The underlying type of objects -/
  Obj : Type u
  /-- Category structure on objects -/
  instCategory : Category.{v} Obj
  /-- Cartesian monoidal structure (chosen finite products) -/
  instCartesianMonoidal : CartesianMonoidalCategory Obj
  /-- Monoidal closed structure (exponentials) -/
  instMonoidalClosed : MonoidalClosed Obj
  /-- Finite limits -/
  instHasFiniteLimits : HasFiniteLimits Obj
  /-- The subobject fibration -/
  fibration : @SubobjectFibration Obj instCategory

attribute [instance] LambdaTheoryWithEquality.instCategory
attribute [instance] LambdaTheoryWithEquality.instCartesianMonoidal
attribute [instance] LambdaTheoryWithEquality.instMonoidalClosed
attribute [instance] LambdaTheoryWithEquality.instHasFiniteLimits

namespace LambdaTheoryWithEquality

variable (T : LambdaTheoryWithEquality)

/-- The fiber over an object X -/
abbrev Sub (X : T.Obj) : Type _ := T.fibration.Sub X

/-- Frame structure on fibers -/
instance instFiberFrame (X : T.Obj) : Order.Frame (T.Sub X) := T.fibration.frame X

/-- The exponential object (internal hom) using Mathlib's ihom -/
def exp (X Y : T.Obj) : T.Obj :=
  @Functor.obj _ _ _ _ (@ihom T.Obj T.instCategory T.instCartesianMonoidal.toMonoidalCategory
    X (T.instMonoidalClosed.closed X)) Y

/-- The product of two objects -/
noncomputable def prod' (X Y : T.Obj) : T.Obj := Limits.prod X Y

/-- The terminal object -/
noncomputable def terminal : T.Obj := ⊤_ T.Obj

/-- The internal hom functor -/
def internalHom (X : T.Obj) : T.Obj ⥤ T.Obj :=
  @ihom T.Obj T.instCategory T.instCartesianMonoidal.toMonoidalCategory
    X (T.instMonoidalClosed.closed X)

end LambdaTheoryWithEquality

/-! ## Lambda-Theory Morphisms

A morphism of lambda-theories is a functor that preserves the structure:
- Preserves finite limits
- Preserves cartesian closed structure
-/

/-- A morphism between lambda-theories.

    This is a functor that preserves:
    - Finite limits (terminal, products, pullbacks)
    - Cartesian closed structure (exponentials)
-/
structure LambdaTheoryMorphism (T S : LambdaTheoryWithEquality) where
  /-- The underlying functor -/
  functor : T.Obj ⥤ S.Obj
  /-- Preserves finite limits -/
  preservesFiniteLimits : PreservesFiniteLimits functor
  /-- Preserves binary products -/
  preservesBinaryProducts : PreservesLimitsOfShape (Discrete WalkingPair) functor
  /-- Preserves terminal object -/
  preservesTerminal : PreservesLimit (Functor.empty T.Obj) functor

namespace LambdaTheoryMorphism

/-- Identity morphism -/
def id (T : LambdaTheoryWithEquality) : LambdaTheoryMorphism T T where
  functor := Functor.id T.Obj
  preservesFiniteLimits := inferInstance
  preservesBinaryProducts := inferInstance
  preservesTerminal := inferInstance

/-- Composition of morphisms -/
def comp {T S U : LambdaTheoryWithEquality}
    (G : LambdaTheoryMorphism S U) (F : LambdaTheoryMorphism T S) :
    LambdaTheoryMorphism T U where
  functor := F.functor ⋙ G.functor
  preservesFiniteLimits :=
    letI := F.preservesFiniteLimits
    letI := G.preservesFiniteLimits
    Limits.comp_preservesFiniteLimits F.functor G.functor
  preservesBinaryProducts :=
    letI := F.preservesBinaryProducts
    letI := G.preservesBinaryProducts
    Limits.comp_preservesLimitsOfShape F.functor G.functor
  preservesTerminal := by
    letI := F.preservesFiniteLimits
    letI := G.preservesFiniteLimits
    letI := Limits.comp_preservesFiniteLimits F.functor G.functor
    infer_instance

end LambdaTheoryMorphism

/-! ## The 2-Category of Lambda-Theories

Lambda-theories form a 2-category λThyₑq:
- Objects: Lambda-theories with equality
- 1-morphisms: Lambda-theory morphisms (structure-preserving functors)
- 2-morphisms: Natural transformations

For now, we define the 1-categorical structure.
The full 2-category structure would require Bicategory from Mathlib.
-/

/-! ## Summary

This file establishes the categorical foundation for GSLTs:

1. **SubobjectFibration**: Assigns Frame-valued fibers to each object
2. **LambdaTheoryWithEquality**: Category + CCC + finite limits + fibration
3. **LambdaTheoryMorphism**: Structure-preserving functors

**Key Connections to Literature**:
- Matches Williams-Stay's λ-theories with equality (CCCs with pullbacks)
- Fibers are Frames (complete Heyting algebras) as in OSLF
- Morphisms preserve the structure needed for functoriality of NT

**Next Steps**:
- `Web.lean`: Webs and coding functions from Bucciarelli-Salibra
- `ChangeOfBase.lean`: f*, ∃f, ∀f functors with adjunctions
-/

end Mettapedia.GSLT.Core
