import Mathlib.ModelTheory.Ultraproducts
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mettapedia.UniversalAlgebra.EquationSystem
import Mettapedia.UniversalAlgebra.Mathlib.FirstOrder

/-!
# Ultrapowers preserve equational truth

This file isolates a standard model-theoretic boundary for universal algebra.
An ultrapower may contain genuinely new, non-diagonal elements, but it satisfies
exactly the same universally quantified equations as its base algebra.

The result is deliberately stated for arbitrary finitary one-sorted signatures.
It is therefore about equational logic, not about any particular arithmetic,
bootstrap calculus, or proposed foundational language.  Stronger first-order
transfer is Łoś's theorem; the direct proof here exposes the smaller amount of
model theory needed by the equational fragment.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open Filter FirstOrder

universe u v w

variable {S : Signature.{u}}

namespace Model

/-- The carrier of the ultrapower of `Carrier` along `ultrafilter`. -/
abbrev UltrapowerCarrier (Carrier : Type v) {Index : Type w}
    (ultrafilter : Ultrafilter Index) : Type (max v w) :=
  (ultrafilter : Filter Index).Product (fun _ : Index => Carrier)

/-- The universal-algebra model on an ultrapower, obtained from Mathlib's
pointwise ultraproduct structure on the associated algebraic first-order
language. -/
noncomputable def ultrapower {Carrier : Type v} {Index : Type w}
    (model : Model S Carrier) (ultrafilter : Ultrafilter Index) :
    Model S (UltrapowerCarrier Carrier ultrafilter) := by
  letI : (index : Index) → S.toFirstOrderLanguage.Structure Carrier :=
    fun _ => model.toFirstOrderStructure
  exact Model.ofFirstOrderStructure inferInstance

/-- A base element viewed as a constant element of an ultrapower. -/
def diagonal {Carrier : Type v} {Index : Type w}
    (ultrafilter : Ultrafilter Index) (value : Carrier) :
    UltrapowerCarrier Carrier ultrafilter :=
  (fun _ : Index => value : Index → Carrier)

/-- Operations in the induced ultrapower model act pointwise on chosen
representatives. -/
theorem ultrapower_interpret {Carrier : Type v} {Index : Type w}
    (model : Model S Carrier) (ultrafilter : Ultrafilter Index)
    (operation : S.Operation)
    (arguments : Fin (S.arity operation) → Index → Carrier) :
    (model.ultrapower ultrafilter).interpret operation
        (fun position =>
          (arguments position : UltrapowerCarrier Carrier ultrafilter)) =
      (fun index =>
        model.interpret operation (fun position => arguments position index) :
          Index → Carrier) := by
  letI : (index : Index) → S.toFirstOrderLanguage.Structure Carrier :=
    fun _ => model.toFirstOrderStructure
  exact @FirstOrder.Language.Ultraproduct.funMap_cast
    Index (fun _ : Index => Carrier) ultrafilter S.toFirstOrderLanguage
    (fun _ : Index => model.toFirstOrderStructure) (S.arity operation)
    (⟨operation, rfl⟩ : S.toFirstOrderLanguage.Functions (S.arity operation))
    arguments

end Model

namespace Term

variable {Carrier : Type v} {Index : Type w}

/-- Evaluation in an ultrapower is pointwise evaluation of representatives.
This is the term-level fragment of Łoś transfer. -/
theorem evaluate_ultrapower (model : Model S Carrier)
    (ultrafilter : Ultrafilter Index) (valuation : Nat → Index → Carrier) :
    ∀ term : Term S,
      term.evaluate (model.ultrapower ultrafilter)
          (fun variableIndex =>
            (valuation variableIndex :
              Model.UltrapowerCarrier Carrier ultrafilter)) =
        (fun index =>
          term.evaluate model (fun variableIndex => valuation variableIndex index) :
            Index → Carrier) := by
  intro term
  induction term with
  | var variableIndex => rfl
  | op operation arguments ih =>
      simp only [Term.evaluate]
      rw [show
        (fun position =>
            (arguments position).evaluate (model.ultrapower ultrafilter)
              (fun variableIndex =>
                (valuation variableIndex :
                  Model.UltrapowerCarrier Carrier ultrafilter))) =
          (fun position =>
            ((fun index =>
                (arguments position).evaluate model
                  (fun variableIndex => valuation variableIndex index) :
                Index → Carrier) :
              Model.UltrapowerCarrier Carrier ultrafilter)) from funext ih]
      exact Model.ultrapower_interpret model ultrafilter operation
        (fun position index =>
          (arguments position).evaluate model
            (fun variableIndex => valuation variableIndex index))

end Term

namespace Equation

variable {Carrier : Type v} {Index : Type w}

/-- A universally quantified equation holds in a model exactly when it holds in
any constant ultrapower of that model.  The reverse implication uses only a
diagonal valuation; the forward implication chooses representatives for an
arbitrary ultrapower valuation. -/
theorem holds_ultrapower_iff (model : Model S Carrier)
    (ultrafilter : Ultrafilter Index) (equation : Equation S) :
    equation.Holds (model.ultrapower ultrafilter) ↔ equation.Holds model := by
  classical
  constructor
  · intro equationHolds valuation
    have diagonalHolds := equationHolds (fun variableIndex =>
      Model.diagonal ultrafilter (valuation variableIndex))
    change
      equation.1.evaluate (model.ultrapower ultrafilter)
          (fun variableIndex =>
            ((fun _ : Index => valuation variableIndex) :
              Model.UltrapowerCarrier Carrier ultrafilter)) =
        equation.2.evaluate (model.ultrapower ultrafilter)
          (fun variableIndex =>
            ((fun _ : Index => valuation variableIndex) :
              Model.UltrapowerCarrier Carrier ultrafilter))
      at diagonalHolds
    rw [Term.evaluate_ultrapower model ultrafilter
          (fun variableIndex _ => valuation variableIndex) equation.1,
      Term.evaluate_ultrapower model ultrafilter
          (fun variableIndex _ => valuation variableIndex) equation.2]
      at diagonalHolds
    have eventuallyEqual :
        Filter.EventuallyEq (ultrafilter : Filter Index)
          (fun _ : Index => equation.1.evaluate model valuation)
          (fun _ : Index => equation.2.evaluate model valuation) :=
      Quotient.eq''.mp diagonalHolds
    exact (Filter.nonempty_of_mem
      (Filter.eventually_iff.mp eventuallyEqual)).choose_spec
  · intro equationHolds valuation
    let representatives : Nat → Index → Carrier :=
      fun variableIndex => Quotient.out (valuation variableIndex)
    have valuation_eq :
        (fun variableIndex =>
          (representatives variableIndex :
            Model.UltrapowerCarrier Carrier ultrafilter)) = valuation := by
      funext variableIndex
      exact Quotient.out_eq (valuation variableIndex)
    rw [← valuation_eq,
      Term.evaluate_ultrapower model ultrafilter representatives equation.1,
      Term.evaluate_ultrapower model ultrafilter representatives equation.2]
    apply Quotient.eq''.mpr
    exact Filter.Eventually.of_forall fun index =>
      equationHolds (fun variableIndex => representatives variableIndex index)

end Equation

namespace Model

variable {Carrier : Type v} {Index : Type w}

/-- Satisfaction of a finite occurrence-bearing equation system is invariant
under constant ultrapowers. -/
theorem satisfies_ultrapower_iff (model : Model S Carrier)
    (ultrafilter : Ultrafilter Index) (system : EquationSystem S) :
    (model.ultrapower ultrafilter).Satisfies system ↔ model.Satisfies system := by
  simp only [Model.Satisfies]
  constructor
  · intro ultrapowerSatisfies equation equationMem
    exact (Equation.holds_ultrapower_iff model ultrafilter equation).mp
      (ultrapowerSatisfies equation equationMem)
  · intro modelSatisfies equation equationMem
    exact (Equation.holds_ultrapower_iff model ultrafilter equation).mpr
      (modelSatisfies equation equationMem)

end Model

namespace UltrapowerBoundary

/-- The class of the identity sequence in the natural-number ultrapower along
the cofinite-extending ultrafilter. -/
noncomputable def growingElement :
    Model.UltrapowerCarrier Nat (Filter.hyperfilter Nat) :=
  (fun index : Nat => index : Nat → Nat)

/-- The identity sequence is not equivalent to any constant sequence.  Thus
equational invariance does not say that the diagonal map exhausts an
ultrapower. -/
theorem growingElement_ne_diagonal (value : Nat) :
    growingElement ≠ Model.diagonal (Filter.hyperfilter Nat) value := by
  intro equalClasses
  change
    ((fun index : Nat => index : Nat → Nat) :
        Model.UltrapowerCarrier Nat (Filter.hyperfilter Nat)) =
      ((fun _ : Nat => value : Nat → Nat) :
        Model.UltrapowerCarrier Nat (Filter.hyperfilter Nat))
    at equalClasses
  have eventuallyConstant :
      Filter.EventuallyEq (Filter.hyperfilter Nat : Filter Nat)
        (fun index : Nat => index) (fun _ : Nat => value) :=
    Quotient.eq''.mp equalClasses
  have singletonMem : {index : Nat | index = value} ∈ Filter.hyperfilter Nat :=
    Filter.eventually_iff.mp eventuallyConstant
  have singletonFinite : Set.Finite {index : Nat | index = value} := by
    simpa only [Set.setOf_eq_eq_singleton] using Set.finite_singleton value
  exact singletonFinite.notMem_hyperfilter singletonMem

/-- Negative canary: the diagonal embedding into this ultrapower is not
surjective. -/
theorem diagonal_not_surjective :
    ¬ Function.Surjective
      (Model.diagonal (Filter.hyperfilter Nat) :
        Nat → Model.UltrapowerCarrier Nat (Filter.hyperfilter Nat)) := by
  intro diagonalSurjective
  obtain ⟨value, valueMaps⟩ := diagonalSurjective growingElement
  exact growingElement_ne_diagonal value valueMaps.symm

end UltrapowerBoundary

end Mettapedia.UniversalAlgebra
