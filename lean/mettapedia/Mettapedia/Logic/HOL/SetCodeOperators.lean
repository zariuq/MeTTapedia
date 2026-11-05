import Mettapedia.Logic.HOL.ClosedOperationProofs
import Mettapedia.Logic.HOL.SetTraceProductProofs
import Mettapedia.Logic.HOL.SetPairProjectionProofs

/-!
# Closed operators for the material-set code interface

All eight derived operations have actual bodies over the set signature and
the explicit selector. Their substitution laws instantiate the generic
closure construction and its retained beta receipts.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.SetCodeOperators
open SetComprehensionProofs SetPairingProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (mapping)
universe v

inductive Operator : Ty Unit → Type where
  | product : Operator (object ⇒ mapping ⇒ object)
  | sum : Operator (object ⇒ mapping ⇒ object)
  | abstraction : Operator (object ⇒ mapping ⇒ object)
  | application : Operator (object ⇒ object ⇒ object)
  | pair : Operator (object ⇒ object ⇒ object)
  | first : Operator (object ⇒ object)
  | second : Operator (object ⇒ object)
  | truth : Operator (.prop ⇒ object)

variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))

def binary {left right : Ty Unit} : Operator (left ⇒ right ⇒ object) → BinaryOperation Const left right object
  | .product => ⟨SetTraceProductProofs.product core epsilon,SetTraceProductProofs.subst_product core epsilon⟩
  | .sum => ⟨SetDependentSumProofs.sum core epsilon,SetDependentSumProofs.subst_sum core epsilon⟩
  | .abstraction => ⟨SetTraceProofs.abstraction core epsilon,SetDependentSumProofs.subst_sum core epsilon⟩
  | .application => ⟨SetTraceProofs.application core epsilon,SetTraceProofs.subst_application core epsilon⟩
  | .pair => ⟨ordered core epsilon,subst_ordered core epsilon⟩

def unary {input : Ty Unit} : Operator (input ⇒ object) → UnaryOperation Const input object
  | .first => ⟨SetPairProjectionProofs.first core epsilon,SetPairProjectionProofs.subst_first core epsilon⟩
  | .second => ⟨SetPairProjectionProofs.second core epsilon,SetPairProjectionProofs.subst_second core epsilon⟩
  | .truth => {
      term := truthCode core
      subst := by
        intro Γ Ξ theta proposition
        simp only [truthCode,separate,power,HOL.subst,HOL.subst_weaken] }

def body {type : Ty Unit} : Operator type → ClosedTerm Const type
  | .product => (binary core epsilon .product).body
  | .sum => (binary core epsilon .sum).body
  | .abstraction => (binary core epsilon .abstraction).body
  | .application => (binary core epsilon .application).body
  | .pair => (binary core epsilon .pair).body
  | .first => (unary core epsilon .first).body
  | .second => (unary core epsilon .second).body
  | .truth => (unary core epsilon .truth).body

theorem body_binary {left right : Ty Unit} (operator : Operator (left ⇒ right ⇒ object)) :
    body core epsilon operator = (binary core epsilon operator).body := by cases operator <;> rfl

theorem body_unary {input : Ty Unit} (operator : Operator (input ⇒ object)) :
    body core epsilon operator = (unary core epsilon operator).body := by cases operator <;> rfl

variable {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}

def binaryBeta {left right : Ty Unit} (operator : Operator (left ⇒ right ⇒ object))
    (first : Term Const Γ left) (second : Term Const Γ right) :
    ProofSyntax Const Δ (.eq (.app (.app (weakenCtx Γ (body core epsilon operator)) first) second)
      ((binary core epsilon operator).term first second)) :=
  ProofSyntax.castIndices rfl (by rw [body_binary]) ((binary core epsilon operator).beta first second)

def unaryBeta {input : Ty Unit} (operator : Operator (input ⇒ object)) (value : Term Const Γ input) :
    ProofSyntax Const Δ (.eq (.app (weakenCtx Γ (body core epsilon operator)) value)
      ((unary core epsilon operator).term value)) :=
  ProofSyntax.castIndices rfl (by rw [body_unary]) ((unary core epsilon operator).beta value)

theorem binaryBeta_free {left right : Ty Unit} (operator : Operator (left ⇒ right ⇒ object))
    (first : Term Const Γ left) (second : Term Const Γ right) :
    (binaryBeta (Δ := Δ) core epsilon operator first second).FunctionExtensionalityFree := by
  simpa only [binaryBeta,ProofSyntax.functionExtensionalityFree_castIndices] using
    (binary core epsilon operator).beta_free (Δ := Δ) first second

theorem unaryBeta_free {input : Ty Unit} (operator : Operator (input ⇒ object)) (value : Term Const Γ input) :
    (unaryBeta (Δ := Δ) core epsilon operator value).FunctionExtensionalityFree := by
  simpa only [unaryBeta,ProofSyntax.functionExtensionalityFree_castIndices] using
    (unary core epsilon operator).beta_free (Δ := Δ) value

end Mettapedia.Logic.HOL.SetCodeOperators
