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
# Bundled categorical theory interfaces

This file packages supplied categorical structures using Mathlib. It does not
construct them from an equational lambda theory or an authored `LanguageDef`.

## Main Definitions

* `LambdaTheoryWithEquality` - A lambda-theory with morphisms, CCC structure, and finite limits
* `LambdaTheoryMorphism` - Functors equipped with finite-limit preservation
* `SubobjectFibration` - Object-indexed Frame data, without reindexing or a
  proved identification with categorical subobjects

The current morphism record does not include exponential preservation or an
action on its Frame data. The Frame record alone is not a categorical fibration.
Full native-type-theory generation therefore requires further constructions;
it does not follow from these bundles.

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

/-- Object-indexed Frame data. Categorical subobjects motivate this interface,
but it currently supplies no reindexing, cartesian lifts, or identification
with actual subobjects. It is not by itself a categorical fibration.
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

/-- A category equipped with cartesian closed structure, finite limits, and
object-indexed Frame data. All structures are supplied, not derived here.
Dependent comprehension and dependent products are not consequences of this
record alone; they require their own construction and coherence laws.
-/
structure LambdaTheoryWithEquality.{u', v', w'} where
  /-- The underlying type of objects -/
  Obj : Type u'
  /-- Category structure on objects -/
  instCategory : Category.{v'} Obj
  /-- Cartesian monoidal structure (chosen finite products) -/
  instCartesianMonoidal : CartesianMonoidalCategory Obj
  /-- Monoidal closed structure (exponentials) -/
  instMonoidalClosed : MonoidalClosed Obj
  /-- Finite limits -/
  instHasFiniteLimits : HasFiniteLimits Obj
  /-- The subobject fibration -/
  fibration : @SubobjectFibration.{u', v', w'} Obj instCategory

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

The current morphism interface records finite-limit preservation.
Preservation of exponentials and action on the Frame data are not included.
-/

/-- A finite-limit-preserving functor between the bundled categories.
The additional binary-product and terminal fields specialize that property.
This record does not certify exponential preservation or a map of Frame data.
-/
structure LambdaTheoryMorphism (T S : LambdaTheoryWithEquality) where
  /-- The underlying functor -/
  functor : T.Obj ⥤ S.Obj
  /-- Preserves finite limits -/
  preservesFiniteLimits : PreservesFiniteLimits functor
  /-- Preserves binary products -/
  preservesBinaryProducts : PreservesLimitsOfShape (Discrete WalkingPair) functor
  /-- Preserves terminal object -/
  preservesTerminal : PreservesLimit (Functor.empty.{0} T.Obj) functor

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
    let := F.preservesFiniteLimits
    let := G.preservesFiniteLimits
    let := Limits.comp_preservesFiniteLimits F.functor G.functor
    infer_instance

end LambdaTheoryMorphism

/-! ## The 2-Category of Lambda-Theories

The source's intended 2-category λThyₑq has:
- Objects: Lambda-theories with equality
- 1-morphisms: Lambda-theory morphisms (structure-preserving functors)
- 2-morphisms: Natural transformations

This file supplies identity and composition operations on the current
finite-limit-preserving records. It does not supply a category instance or
the full bicategory, nor identify these records with all source morphisms.
-/

/-! ## Summary

This file supplies bundled inputs for categorical constructions:

1. **SubobjectFibration**: Assigns a Frame to each object, without reindexing
2. **LambdaTheoryWithEquality**: Category + CCC + finite limits + Frame data
3. **LambdaTheoryMorphism**: Finite-limit-preserving functor records

**Key Connections to Literature**:
- The supplied CCC and finite-limit structures are motivated by Williams–Stay
- The Frame fields supply complete Heyting-algebra operations
- Functoriality of native-type-theory generation still requires its own
  structure-preservation and coherence theorems

**Next Steps**:
- `Web.lean`: Webs and coding functions from Bucciarelli-Salibra
- `ChangeOfBase.lean`: f*, ∃f, ∀f functors with adjunctions
-/

end Mettapedia.GSLT.Core
