import Mathlib.Order.Heyting.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.Data.Set.Lattice

/-!
# Lambda Theories and Fibered Categories

This file formalizes the categorical foundations for the Stay-Wells-Meredith
framework for generating type systems from operational semantics.

## Main Definitions

* `SubobjectFibration` - A fibration where each fiber is a Heyting algebra
* `LambdaTheory` - A category with finite limits, subobject fibration, and reduction relation
* `RewriteRule` - A base rewrite in a lambda theory
* `RewriteContext` - A one-hole context from a rewrite

## Key Insight

The fibers of a subobject fibration are Heyting algebras, which are complete lattices!
This provides the missing structure for quantales: we get sSup/sInf for free.

## References

* Stay & Wells, "Generating Hypercubes of Type Systems" (hypercube.pdf)
* Meredith & Stay, "Operational Semantics in Logical Form" (oslf.pdf)
* Lawvere, "Metric spaces, generalized logic, and closed categories" (1973)
-/


namespace Mettapedia.CategoryTheory.LambdaTheories

open CategoryTheory

/-! ## Subobject Fibrations

A subobject fibration assigns to each object X a Heyting algebra Sub(X) of "subobjects".
In the topos-theoretic setting, these are actual subobjects classified by Ω.
For our purposes, we work axiomatically: we require each fiber to be a Heyting algebra.
-/

/-- A subobject fibration over a type of objects.

    Each object X has an associated Frame Sub(X) of "types at X".
    A Frame (complete Heyting algebra) gives us:
    - Complete lattice (sSup, sInf) for arbitrary joins/meets
    - Heyting implication (⇨) which will be residuation
    - Top (⊤) and bottom (⊥) elements
    - The crucial property: ⊓ distributes over ⨆ (the quantale law!)
-/
structure SubobjectFibration (Obj : Type*) where
  /-- The fiber over each object -/
  Sub : Obj → Type*
  /-- Each fiber is a Frame (complete Heyting algebra) -/
  frame : ∀ X, Order.Frame (Sub X)

namespace SubobjectFibration

variable {Obj : Type*} (F : SubobjectFibration Obj)

/-- The fiber over an object, with its Frame structure -/
instance (X : Obj) : Order.Frame (F.Sub X) := F.frame X

/-- Heyting implication in a fiber (this will be residuation!) -/
def himp (X : Obj) (a b : F.Sub X) : F.Sub X := a ⇨ b

/-- The top element of a fiber -/
def top (X : Obj) : F.Sub X := ⊤

/-- The bottom element of a fiber -/
def bot (X : Obj) : F.Sub X := ⊥

/-- Join in a fiber -/
def sup (X : Obj) (a b : F.Sub X) : F.Sub X := a ⊔ b

/-- Meet in a fiber -/
def inf (X : Obj) (a b : F.Sub X) : F.Sub X := a ⊓ b

/-- Arbitrary join in a fiber -/
def sSup' (X : Obj) (S : Set (F.Sub X)) : F.Sub X := sSup S

/-- Arbitrary meet in a fiber -/
def sInf' (X : Obj) (S : Set (F.Sub X)) : F.Sub X := sInf S

end SubobjectFibration

/-! ## Lambda Theories

A lambda theory is a subobject fibration with:
1. A distinguished object Pr of "processes" (or propositions, or terms)
2. A reduction relation ⇝ as a subobject of Pr × Pr

This is a simplified version of the full definition from hypercube.pdf.
-/

/-- A lambda theory (simplified).

    In the full version, we would have:
    - A category T with finite limits
    - A fibration π : Sub(T) → T
    - Cartesian closure

    For now, we work with a simpler version where Obj is just a type,
    and we focus on the fiber structure.
-/
structure LambdaTheory where
  /-- The type of objects (carriers) -/
  Obj : Type*
  /-- The subobject fibration -/
  fibration : SubobjectFibration Obj
  /-- Distinguished object of processes/propositions -/
  Pr : Obj
  /-- Product of objects (simplified - in full version this comes from limits) -/
  prod : Obj → Obj → Obj
  /-- The reduction relation as a subobject of Pr × Pr -/
  reduce : fibration.Sub (prod Pr Pr)

namespace LambdaTheory

variable (L : LambdaTheory)

/-- Shorthand for the fiber over an object -/
abbrev Sub (X : L.Obj) : Type* := L.fibration.Sub X

/-- The fiber over Pr - this is where truth values / types live -/
abbrev SubPr : Type* := L.Sub L.Pr

/-- The Frame structure on SubPr -/
instance : Order.Frame L.SubPr := L.fibration.frame L.Pr

/-! ### Key Lemma: Heyting Implication is Residuation

In a Heyting algebra, we have: a ⊓ b ≤ c ↔ a ≤ b ⇨ c

This is exactly the residuation property we need for quantales!
The meet (⊓) will correspond to our tensor product.
-/

/-- Heyting implication is right adjoint to meet -/
theorem himp_adjoint (a b c : L.SubPr) : a ⊓ b ≤ c ↔ a ≤ b ⇨ c :=
  le_himp_iff.symm

/-- This is the residuation property for quantales! -/
theorem residuation (a b c : L.SubPr) : a ⊓ b ≤ c ↔ a ≤ b ⇨ c :=
  himp_adjoint L a b c

end LambdaTheory

/-! ## Rewrite Rules and Contexts

A rewrite rule is a base reduction: Γ ⊢ L ⇝ R
A rewrite context is a one-hole context Cj with Cj[tj] = L
-/

/-- A rewrite rule in a lambda theory.

    Represents: x₁:X₁, ..., xₙ:Xₙ ⊢ L(x⃗) ⇝ R(x⃗)

    For simplicity, we represent L and R as elements of SubPr
    (the types of the left and right hand sides).
-/
structure RewriteRule (L : LambdaTheory) where
  /-- The context variables and their carriers -/
  ctx : List L.Obj
  /-- Type of the left-hand side (redex) -/
  lhsType : L.SubPr
  /-- Type of the right-hand side (reduct) -/
  rhsType : L.SubPr

/-! ## Modal Composition

The composition of modal types gives the tensor product for the quantale.

If we have:
- ⟨C₁⟩_{x::A} B  (modal type for "A implies B")
- ⟨C₂⟩_{y::B} C  (modal type for "B implies C")

Their composition gives a modal type for "A implies C".
This is the PLN deduction rule!
-/

/-- Compose two modal types.

    This is the quantale tensor product in disguise!
-/
noncomputable def modalCompose (L : LambdaTheory)
    (m1 m2 : L.SubPr) : L.SubPr :=
  -- The composition uses meet (⊓) from the Heyting algebra
  -- In the full development, this would involve composing the
  -- underlying rely-possibly specifications
  m1 ⊓ m2

namespace LambdaTheory

variable (L : LambdaTheory)

/-- Modal composition distributes over arbitrary joins.

    This is THE quantale law!
-/
theorem modalCompose_sSup (a : L.SubPr) (S : Set L.SubPr) :
    modalCompose L a (sSup S) = sSup (modalCompose L a '' S) := by
  unfold modalCompose
  -- In a Frame, meet distributes over arbitrary joins
  -- inf_sSup_eq : a ⊓ sSup S = ⨆ b ∈ S, a ⊓ b
  -- sSup_image : sSup (f '' S) = ⨆ a ∈ S, f a
  rw [inf_sSup_eq, sSup_image]

/-- Modal composition distributes over joins (binary version) -/
theorem modalCompose_sup (a b c : L.SubPr) :
    modalCompose L a (b ⊔ c) = modalCompose L a b ⊔ modalCompose L a c := by
  unfold modalCompose
  -- Frame gives us DistribLattice structure
  rw [inf_sup_left]

/-! ## The Quantale Instance

Now we can show that SubPr forms a quantale!
-/

/-- The fiber SubPr of a lambda theory forms a quantale.

    - Complete lattice: from Frame
    - Monoid: modalCompose with ⊤ as unit
    - Quantale law: modalCompose_sSup
-/
noncomputable instance instMonoidSubPr : Monoid L.SubPr where
  mul := modalCompose L
  one := ⊤
  mul_assoc a b c := inf_assoc a b c
  one_mul a := top_inf_eq a
  mul_one a := inf_top_eq a

/-- The quantale multiplication is just modalCompose -/
theorem mul_eq_modalCompose (a b : L.SubPr) :
    a * b = modalCompose L a b := rfl

/-- The quantale law holds -/
theorem quantale_law (a : L.SubPr) (S : Set L.SubPr) :
    a * sSup S = sSup ((a * ·) '' S) :=
  modalCompose_sSup L a S

end LambdaTheory

end Mettapedia.CategoryTheory.LambdaTheories
