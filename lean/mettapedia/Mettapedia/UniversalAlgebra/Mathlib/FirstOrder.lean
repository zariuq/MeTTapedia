import Mathlib.ModelTheory.Semantics
import Mettapedia.UniversalAlgebra.Model

/-!
# Exact bridge to Mathlib's first-order algebraic languages

A single-sorted universal-algebra signature is exactly an algebraic
`FirstOrder.Language`: an operation of arity `n` becomes a function symbol of
arity `n`, and there are no relation symbols.  The term and model translations
below preserve syntax and evaluation in both directions.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

universe u v

open FirstOrder

/-- The algebraic first-order language determined by a signature. -/
def Signature.toFirstOrderLanguage (S : Signature.{u}) : FirstOrder.Language.{u, 0} where
  Functions n := { operation : S.Operation // S.arity operation = n }
  Relations _ := Empty

instance (S : Signature.{u}) : S.toFirstOrderLanguage.IsAlgebraic :=
  fun _ => by
    change IsEmpty Empty
    infer_instance

namespace Term

variable {S : Signature.{u}}

/-- Translate a universal-algebra term to the corresponding Mathlib term. -/
def toFirstOrder : Term S → S.toFirstOrderLanguage.Term Nat
  | .var index => .var index
  | .op operation arguments =>
      .func ⟨operation, rfl⟩ (fun i => (arguments i).toFirstOrder)

/-- Translate a Mathlib term in the associated algebraic language back. -/
def ofFirstOrder : S.toFirstOrderLanguage.Term Nat → Term S
  | .var index => .var index
  | @FirstOrder.Language.Term.func _ _ _arity operation arguments =>
      .op operation.1 (fun i =>
        ofFirstOrder (arguments (Fin.cast operation.2 i)))

@[simp] theorem ofFirstOrder_toFirstOrder (term : Term S) :
    ofFirstOrder term.toFirstOrder = term := by
  induction term with
  | var index => rfl
  | op operation arguments ih =>
      simp only [toFirstOrder, ofFirstOrder]
      congr 1
      funext i
      exact ih i

@[simp] theorem toFirstOrder_ofFirstOrder
    (term : S.toFirstOrderLanguage.Term Nat) :
    (ofFirstOrder term).toFirstOrder = term := by
  induction term with
  | var index => rfl
  | @func arity operation arguments ih =>
      rcases operation with ⟨operation, rfl⟩
      simp only [ofFirstOrder, toFirstOrder]
      congr 1
      funext i
      exact ih i

/-- Universal-algebra terms and Mathlib terms are equivalent, not merely
embedded. -/
def firstOrderEquiv (S : Signature.{u}) :
    Term S ≃ S.toFirstOrderLanguage.Term Nat where
  toFun := toFirstOrder
  invFun := ofFirstOrder
  left_inv := ofFirstOrder_toFirstOrder
  right_inv := toFirstOrder_ofFirstOrder

@[simp] theorem toFirstOrder_subst (term : Term S)
    (substitution : Nat → Term S) :
    (term.subst substitution).toFirstOrder =
      term.toFirstOrder.subst (fun index => (substitution index).toFirstOrder) := by
  induction term with
  | var index => rfl
  | op operation arguments ih =>
      simp only [Term.subst, toFirstOrder, FirstOrder.Language.Term.subst]
      congr 1
      funext i
      exact ih i

end Term

namespace Model

variable {S : Signature.{u}} {Carrier : Type v}

/-- Interpret the associated Mathlib language using a universal-algebra
model. -/
@[reducible] def toFirstOrderStructure (model : Model S Carrier) :
    S.toFirstOrderLanguage.Structure Carrier where
  funMap operation arguments :=
    model.interpret operation.1 (fun i => arguments (Fin.cast operation.2 i))
  RelMap relation := Empty.elim relation

/-- Read a Mathlib structure for the associated algebraic language as a
universal-algebra model. -/
def ofFirstOrderStructure
    (foStructure : S.toFirstOrderLanguage.Structure Carrier) : Model S Carrier where
  interpret operation arguments :=
    @FirstOrder.Language.Structure.funMap
      S.toFirstOrderLanguage Carrier foStructure (S.arity operation)
      ⟨operation, rfl⟩ arguments

@[simp] theorem ofFirstOrderStructure_toFirstOrderStructure
    (model : Model S Carrier) :
    ofFirstOrderStructure model.toFirstOrderStructure = model := by
  cases model
  rfl

@[simp] theorem toFirstOrderStructure_ofFirstOrderStructure
    (foStructure : S.toFirstOrderLanguage.Structure Carrier) :
    (ofFirstOrderStructure foStructure).toFirstOrderStructure = foStructure := by
  ext arity operation arguments
  · change @FirstOrder.Language.Structure.funMap
        S.toFirstOrderLanguage Carrier foStructure (S.arity operation.1)
        ⟨operation.1, rfl⟩ (fun i => arguments (Fin.cast operation.2 i)) =
      @FirstOrder.Language.Structure.funMap
        S.toFirstOrderLanguage Carrier foStructure arity operation arguments
    rcases operation with ⟨operation, rfl⟩
    rfl
  · exact Empty.elim operation

/-- Models of a signature are exactly Mathlib structures for its associated
algebraic language. -/
def firstOrderStructureEquiv (S : Signature.{u}) (Carrier : Type v) :
    Model S Carrier ≃ S.toFirstOrderLanguage.Structure Carrier where
  toFun := toFirstOrderStructure
  invFun := ofFirstOrderStructure
  left_inv := ofFirstOrderStructure_toFirstOrderStructure
  right_inv := toFirstOrderStructure_ofFirstOrderStructure

theorem realize_toFirstOrder (model : Model S Carrier)
    (valuation : Nat → Carrier) (term : Term S) :
    letI : S.toFirstOrderLanguage.Structure Carrier := model.toFirstOrderStructure
    term.toFirstOrder.realize valuation = term.evaluate model valuation := by
  letI : S.toFirstOrderLanguage.Structure Carrier := model.toFirstOrderStructure
  induction term with
  | var index => rfl
  | op operation arguments ih =>
      simp only [Term.toFirstOrder, FirstOrder.Language.Term.realize,
        Term.evaluate]
      apply congrArg (model.interpret operation)
      funext i
      exact ih i

end Model

end Mettapedia.UniversalAlgebra
