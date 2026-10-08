import Mettapedia.CategoryTheory.RelativeClosedSyntaxRawOperations
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationReadout

/-!
# Complete native readings of raw closed operations

The local object and body readings compute the complete arrow produced by
currying or function application. The comparison includes both function
arguments and the ambient stage, before passing to the generated quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory GeneratedCategory

universe u v a w z

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasFiniteLimits D]
variable (assignment : Assignment C symbols D)

omit [MonoidalClosed D] [HasFiniteLimits D] in
private theorem exchange_cancel (first second : D) :
    exchange first second ≫ exchange second first = 𝟙 (first ⊗ second) := by
  apply hom_ext <;> simp [exchange]

theorem raw_curry_read {argument context result : Object signature} {A Z X : D}
    (body : RawHom (product argument context) result) (actual : A ⊗ Z ⟶ X)
    (argumentRead : assignment.evaluateObject argument.code = some A)
    (contextRead : assignment.evaluateObject context.code = some Z)
    (resultRead : assignment.evaluateObject result.code = some X)
    (bodyRead : assignment.evaluateArrow body.code = some ⟨A ⊗ Z, X, actual⟩) :
    assignment.evaluateArrow (RawHom.curry body).code =
      some ⟨Z, A ⟶[D] X, MonoidalClosed.curry actual⟩ := by
  have swapped := assignment.evaluate_pair _ _
    (assignment.evaluate_second contextRead argumentRead)
    (assignment.evaluate_first contextRead argumentRead)
  have complete := assignment.evaluate_abstraction _ contextRead argumentRead resultRead
    (assignment.evaluate_compose _ _ swapped bodyRead)
  have same : abstraction (exchange Z A ≫ actual) = MonoidalClosed.curry actual := by
    unfold abstraction
    rw [← Category.assoc, exchange_cancel, Category.id_comp]
  exact complete.trans (congrArg (fun arrow => some (⟨Z, A ⟶[D] X, arrow⟩ : ArrowValue D)) same)

def RawHom.applyFunction {context argument result : Object signature}
    (function : RawHom context (exponentialObject argument result))
    (value : RawHom context argument) : RawHom context result :=
  RawHom.compose (RawHom.pair function value)
    ⟨.evaluation argument.code result.code,
      ⟨.evaluation argument.formed.some result.formed.some⟩⟩

theorem raw_apply_read {context argument result : Object signature} {Z A X : D}
    (function : RawHom context (exponentialObject argument result))
    (value : RawHom context argument) (actualFunction : Z ⟶ (A ⟶[D] X))
    (actualValue : Z ⟶ A)
    (argumentRead : assignment.evaluateObject argument.code = some A)
    (resultRead : assignment.evaluateObject result.code = some X)
    (functionRead : assignment.evaluateArrow function.code = some ⟨Z, A ⟶[D] X, actualFunction⟩)
    (valueRead : assignment.evaluateArrow value.code = some ⟨Z, A, actualValue⟩) :
    assignment.evaluateArrow (RawHom.applyFunction function value).code =
      some ⟨Z, X, lift actualValue actualFunction ≫ (ihom.ev A).app X⟩ := by
  have complete := assignment.evaluate_compose _ _
    (assignment.evaluate_pair _ _ functionRead valueRead)
    (assignment.evaluate_evaluation argumentRead resultRead)
  have same : lift actualFunction actualValue ≫ evaluation A X =
      lift actualValue actualFunction ≫ (ihom.ev A).app X := by
    unfold evaluation exchange
    rw [← Category.assoc, comp_lift, lift_snd, lift_fst]
  exact complete.trans (congrArg (fun arrow => some (⟨Z, X, arrow⟩ : ArrowValue D)) same)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
