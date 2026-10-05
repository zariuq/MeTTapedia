import Mettapedia.Languages.Chaitin.GSLT.Configurations

/-!
# Compositional execution through explicit Lisp continuations

Every finite derivation of the shared pure natural semantics gives a path
through the configuration rules, in any caller continuation. This comparison
retains argument order, dynamic scope, and clean re-evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT

open PureEvaluation

def Evaluated (environment : Environment) (expression value : SExpr) : Prop :=
  ∀ continuation, CorePath (.eval expression environment continuation) (.returned value continuation)

def Applied (environment : Environment) (function : SExpr) (arguments : List SExpr)
    (value : SExpr) : Prop :=
  ∀ continuation, CorePath (.apply function arguments environment continuation) (.returned value continuation)

def ArgumentsEvaluated (environment : Environment) (expressions values : List SExpr) : Prop :=
  ∀ (function : SExpr) (reversed : List SExpr) continuation,
    CorePath (argumentsConfiguration function reversed expressions environment continuation)
      (.apply function (reversed.reverse ++ values) environment continuation)

private theorem atom_evaluated {environment expression}
    (atomic : expression.atom = true) : Evaluated environment expression (lookup environment expression) :=
  fun _ => .single (.atom atomic)

private theorem quote_evaluated {environment head operands}
    (function : Evaluated environment head (.symbol "'")) :
    Evaluated environment (.list (head :: operands)) (operands.headD SExpr.nil) :=
  fun continuation => (Relation.ReflTransGen.single CoreStep.call).trans
    ((function (.function operands environment continuation)).trans (.single .quote))

private theorem conditional_evaluated {environment head operands condition value}
    (function : Evaluated environment head (.symbol "if"))
    (test : Evaluated environment (operands.headD SExpr.nil) condition)
    (branch : Evaluated environment
      (if condition.truth then operands.tail.headD SExpr.nil else operands.tail.tail.headD SExpr.nil) value) :
    Evaluated environment (.list (head :: operands)) value :=
  fun continuation => (Relation.ReflTransGen.single CoreStep.call).trans
    ((function (.function operands environment continuation)).trans
      ((Relation.ReflTransGen.single CoreStep.conditional).trans
        ((test (.conditional (operands.tail.headD SExpr.nil)
          (operands.tail.tail.headD SExpr.nil) environment continuation)).trans
          ((Relation.ReflTransGen.single CoreStep.branch).trans (branch continuation)))))

private theorem application_evaluated {environment head operands function values value}
    (functionRun : Evaluated environment head function)
    (notQuote : function ≠ .symbol "'") (notIf : function ≠ .symbol "if")
    (arguments : ArgumentsEvaluated environment operands values)
    (body : Applied environment function values value) :
    Evaluated environment (.list (head :: operands)) value := by
  intro continuation
  exact (Relation.ReflTransGen.single CoreStep.call).trans
    ((functionRun (.function operands environment continuation)).trans
      ((Relation.ReflTransGen.single (CoreStep.function notQuote notIf)).trans
        ((arguments function [] continuation).trans (body continuation))))

private theorem nil_evaluated (environment : Environment) : ArgumentsEvaluated environment [] [] := by
  intro function reversed continuation
  simp only [argumentsConfiguration, List.append_nil]
  exact .refl

private theorem cons_evaluated {environment expression expressions value values}
    (head : Evaluated environment expression value)
    (tail : ArgumentsEvaluated environment expressions values) :
    ArgumentsEvaluated environment (expression :: expressions) (value :: values) := by
  intro function reversed continuation
  simpa only [CorePath, argumentsConfiguration, List.reverse_cons, List.append_assoc,
    List.singleton_append] using
    (head (.argument function reversed expressions environment continuation)).trans
      ((Relation.ReflTransGen.single CoreStep.argument).trans
        (tail function (value :: reversed) continuation))

theorem pureEval_corePath {environment expression value}
    (derivation : PureEval environment expression value) : Evaluated environment expression value := by
  induction derivation using PureEval.rec
      (motive_2 := fun environment expressions values _ => ArgumentsEvaluated environment expressions values)
      (motive_3 := fun environment function arguments value _ => Applied environment function arguments value) with
  | atom environment expression atomic => exact atom_evaluated atomic
  | quote function ih => exact quote_evaluated ih
  | conditional function test branch ihFunction ihTest ihBranch =>
      exact conditional_evaluated ihFunction ihTest ihBranch
  | application functionRun notQuote notIf arguments body ihFunction ihArguments ihBody =>
      exact application_evaluated ihFunction notQuote notIf ihArguments ihBody
  | nil environment => exact nil_evaluated environment
  | cons head tail ihHead ihTail => exact cons_evaluated ihHead ihTail
  | primitive returned => exact fun _ => .single (.primitive returned)
  | eval body ih => exact fun continuation =>
      (Relation.ReflTransGen.single CoreStep.eval).trans (ih continuation)
  | lambda dispatch body ih => exact fun continuation =>
      (Relation.ReflTransGen.single (CoreStep.lambda dispatch)).trans (ih continuation)

end Mettapedia.Languages.Chaitin.GSLT
