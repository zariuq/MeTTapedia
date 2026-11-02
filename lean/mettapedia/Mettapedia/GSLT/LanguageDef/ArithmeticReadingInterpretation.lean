import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTermControls
import Mettapedia.Logic.HOL.TermInterpretationLaws

/-!
# Coherent arithmetic source readings under closed-term interpretation

Variable images are the primitive context contract. Zero, successor and
addition are supplied by actual closed target terms; the complete expression
comparison is derived structurally, under arbitrary caller substitutions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.ArithmeticReadingInterpretation
open Mettapedia.Logic
open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open IndexedInductiveNatVec IndexedInductiveHOLTerms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} (arithmetic : Arithmetic Const)
abbrev SourceBase := IndexedInductiveHOLTerms.Controls.SortCode
abbrev SourceConst := IndexedInductiveHOLTerms.Controls.Symbol
abbrev sourceArithmetic := IndexedInductiveHOLTerms.Controls.arithmetic

def types : SourceBase → Ty Base
  | .number => arithmetic.number
  | .element => arithmetic.element

def constants : {type : Ty SourceBase} → SourceConst type → ClosedTerm Const (Ty.substitute (types arithmetic) type)
  | _, .zero => arithmetic.zero
  | _, .successor => arithmetic.successor
  | _, .addition => arithmetic.addition

def interpretation : TermInterpretation SourceBase SourceConst Base Const :=
  ⟨types arithmetic, constants arithmetic⟩

@[simp] theorem zero_image : (interpretation arithmetic).term sourceArithmetic.zero = arithmetic.zero := rfl
@[simp] theorem successor_image : (interpretation arithmetic).term sourceArithmetic.successor = arithmetic.successor := rfl
@[simp] theorem addition_image : (interpretation arithmetic).term sourceArithmetic.addition = arithmetic.addition := rfl

variable {Γ : Ctx SourceBase}

theorem term_agrees {context : List Vectors.DataSort}
    (sourceTheta : Subst SourceConst (context.map sourceArithmetic.sort ++ []) Γ)
    (targetTheta : Subst Const (context.map arithmetic.sort ++ []) (Γ.map (Ty.substitute (types arithmetic))))
    (compatibleVariables : ∀ reference : Vectors.LengthVariable context,
      (interpretation arithmetic).term (sourceTheta (sourceArithmetic.reference reference)) =
        targetTheta (arithmetic.reference reference))
    (expression : Vectors.IndexExpr context) :
    (interpretation arithmetic).term (HOL.subst sourceTheta (sourceArithmetic.term expression)) =
      HOL.subst targetTheta (arithmetic.term expression) := by
  induction expression with
  | zero =>
      simp only [Arithmetic.term, HOL.subst_weakenCtx, TermInterpretation.term_weakenCtx]
      rfl
  | «variable» reference =>
      simpa only [Arithmetic.term, HOL.subst] using compatibleVariables reference
  | successor expression previous =>
      simp only [Arithmetic.term, HOL.subst, HOL.subst_weakenCtx, TermInterpretation.term_app]
      rw [previous]
      simp only [TermInterpretation.term_weakenCtx]
      rfl
  | addition first second firstHyp secondHyp =>
      simp only [Arithmetic.term, HOL.subst, HOL.subst_weakenCtx, TermInterpretation.term_app]
      rw [firstHyp,secondHyp]
      simp only [TermInterpretation.term_weakenCtx]
      rfl

#print axioms term_agrees
end Mettapedia.GSLT.LanguageDef.ArithmeticReadingInterpretation
