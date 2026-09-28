import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
import Mettapedia.OSLF.Framework.PathTypeSynthesis

/-!
# Operational evaluation of many-sorted construction algebras

The reference machine reduces one operation only after its children are
values, with contextual steps for ordered arguments. It uses the existing
construction-tree carrier. The direct fold avoids constructing intermediate
machine states. Its correspondence with the reference machine is proved for
every finite tree, then expressed using the canonical OSLF path native type.

This supplies a semantic interface for admitted evaluators. It is not a
correspondence theorem for a C implementation or a particular language's
choice of interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySortedEvaluation

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.PathTypeSynthesis

variable (algebra :
  ManySortedConstructionAlgebra.{0, 0, 0, 0})

/-- Machine leaves are already computed values. Operations and their ordered
sorts are unchanged; this is an evaluation state, not another syntax. -/
abbrev valueAlgebra : ManySortedConstructionAlgebra where
  Kind := algebra.Kind
  Object := algebra.Object
  Source := algebra.Object
  Operation := algebra.Operation
  interpretSource := id
  interpretOperation := algebra.interpretOperation

abbrev State (kind : algebra.Kind) := ConstructionTree (valueAlgebra algebra) kind
abbrev Arguments (kinds : List algebra.Kind) :=
  ConstructionArguments (valueAlgebra algebra) kinds

mutual
  /-- Enter the evaluator by observing only source leaves. All operations,
  their ordering and child contexts remain in the computation. -/
  def enterState : {kind : algebra.Kind} → ConstructionTree algebra kind → State algebra kind
    | _, .source source => .source (algebra.interpretSource source)
    | _, .apply operation arguments => .apply operation (enterArguments arguments)

  def enterArguments : {kinds : List algebra.Kind} →
      ConstructionArguments algebra kinds → Arguments algebra kinds
    | _, .nil => .nil
    | _, .cons head tail => .cons (enterState head) (enterArguments tail)
end

mutual
  theorem enterState_evaluates {kind : algebra.Kind}
      (route : ConstructionTree algebra kind) :
      (valueAlgebra algebra).evaluate (enterState algebra route) = algebra.evaluate route := by
    match route with
    | .source source => rfl
    | .apply operation arguments =>
        change algebra.interpretOperation operation
          ((valueAlgebra algebra).evaluateArguments (enterArguments algebra arguments)) = _
        rw [enterArguments_evaluate arguments]
        rfl
    termination_by structural route

  theorem enterArguments_evaluate {kinds : List algebra.Kind}
      (arguments : ConstructionArguments algebra kinds) :
      (valueAlgebra algebra).evaluateArguments (enterArguments algebra arguments) =
        algebra.evaluateArguments arguments := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        change FamilyList.cons
          ((valueAlgebra algebra).evaluate (enterState algebra head))
          ((valueAlgebra algebra).evaluateArguments (enterArguments algebra tail)) = _
        rw [enterState_evaluates head, enterArguments_evaluate tail]
        rfl
    termination_by structural arguments
end

/-- Embed computed children without invoking any operation. -/
def readyArguments : {kinds : List algebra.Kind} →
    FamilyList algebra.Object kinds → Arguments algebra kinds
  | [], .nil => .nil
  | _ :: _, .cons head tail => .cons (.source head) (readyArguments tail)

@[simp] theorem evaluate_readyArguments {kinds : List algebra.Kind}
    (values : FamilyList algebra.Object kinds) :
    (valueAlgebra algebra).evaluateArguments (readyArguments algebra values) = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change FamilyList.cons head
        ((valueAlgebra algebra).evaluateArguments (readyArguments algebra tail)) = _
      rw [ih]

mutual
  /-- Reference steps: evaluate one ready operation, or one child context. -/
  inductive Step : {kind : algebra.Kind} → State algebra kind → State algebra kind → Prop
    | compute {inputs : List algebra.Kind} {output : algebra.Kind}
        (operation : algebra.Operation inputs output)
        (values : FamilyList algebra.Object inputs) :
        Step (.apply operation (readyArguments algebra values))
          (.source (algebra.interpretOperation operation values))
    | child {inputs : List algebra.Kind} {output : algebra.Kind}
        (operation : algebra.Operation inputs output)
        {before after : Arguments algebra inputs}
        (step : ArgumentsStep before after) :
        Step (.apply operation before) (.apply operation after)

  inductive ArgumentsStep : {kinds : List algebra.Kind} →
      Arguments algebra kinds → Arguments algebra kinds → Prop
    | head {kind : algebra.Kind} {kinds : List algebra.Kind}
        {before after : State algebra kind} (step : Step before after)
        (tail : Arguments algebra kinds) :
        ArgumentsStep (.cons before tail) (.cons after tail)
    | tail {kind : algebra.Kind} {kinds : List algebra.Kind}
        (head : algebra.Object kind) {before after : Arguments algebra kinds}
        (step : ArgumentsStep before after) :
        ArgumentsStep (.cons (.source head) before) (.cons (.source head) after)
end

mutual
  theorem step_preserves {kind : algebra.Kind} {before after : State algebra kind}
      (step : Step algebra before after) :
      (valueAlgebra algebra).evaluate before = (valueAlgebra algebra).evaluate after := by
    match step with
    | .compute operation values =>
        simp only [ManySortedConstructionAlgebra.evaluate_apply,
          evaluate_readyArguments, ManySortedConstructionAlgebra.evaluate_source]
        rfl
    | .child operation childStep =>
        simp only [ManySortedConstructionAlgebra.evaluate_apply,
          argumentsStep_preserves childStep]
    termination_by structural step

  theorem argumentsStep_preserves {kinds : List algebra.Kind}
      {before after : Arguments algebra kinds}
      (step : ArgumentsStep algebra before after) :
      (valueAlgebra algebra).evaluateArguments before =
        (valueAlgebra algebra).evaluateArguments after := by
    match step with
    | .head childStep tail =>
        simp only [ManySortedConstructionAlgebra.evaluateArguments_cons,
          step_preserves childStep]
    | .tail head tailStep =>
        simp only [ManySortedConstructionAlgebra.evaluateArguments_cons,
          argumentsStep_preserves tailStep]
    termination_by structural step
end

abbrev Steps {kind : algebra.Kind} := Relation.ReflTransGen (@Step algebra kind)
abbrev ArgumentsSteps {kinds : List algebra.Kind} :=
  Relation.ReflTransGen (@ArgumentsStep algebra kinds)

theorem steps_preserve {kind : algebra.Kind} {before after : State algebra kind}
    (steps : Steps algebra before after) :
    (valueAlgebra algebra).evaluate before = (valueAlgebra algebra).evaluate after := by
  induction steps with
  | refl => rfl
  | tail _ step ih => exact ih.trans (step_preserves algebra step)

theorem steps_child {inputs : List algebra.Kind} {output : algebra.Kind}
    (operation : algebra.Operation inputs output) {before after : Arguments algebra inputs}
    (steps : ArgumentsSteps algebra before after) :
    Steps algebra (.apply operation before) (.apply operation after) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.child operation step)

theorem steps_head {kind : algebra.Kind} {kinds : List algebra.Kind}
    {before after : State algebra kind} (tail : Arguments algebra kinds)
    (steps : Steps algebra before after) :
    ArgumentsSteps algebra (.cons before tail) (.cons after tail) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.head step tail)

theorem steps_tail {kind : algebra.Kind} {kinds : List algebra.Kind}
    (head : algebra.Object kind) {before after : Arguments algebra kinds}
    (steps : ArgumentsSteps algebra before after) :
    ArgumentsSteps algebra (.cons (.source head) before) (.cons (.source head) after) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.tail head step)

mutual
  /-- The bottom-up reference machine reaches the direct fold's result. -/
  theorem normalize {kind : algebra.Kind} (state : State algebra kind) :
      Steps algebra state (.source ((valueAlgebra algebra).evaluate state)) := by
    match state with
    | .source value => exact .refl
    | .apply operation arguments =>
        exact .tail (steps_child algebra operation (normalizeArguments arguments))
          (Step.compute (algebra := algebra) operation _)
    termination_by structural state

  theorem normalizeArguments {kinds : List algebra.Kind}
      (arguments : Arguments algebra kinds) :
      ArgumentsSteps algebra arguments
        (readyArguments algebra ((valueAlgebra algebra).evaluateArguments arguments)) := by
    match arguments with
    | .nil => exact .refl
    | .cons head tail =>
        exact (steps_head algebra tail (normalize head)).trans
          (steps_tail algebra _ (normalizeArguments tail))
    termination_by structural arguments
end

/-- Evaluation semantics used by OSLF, with the result sort retained in the
term carrier. There are real contextual steps, not an inert output theory. -/
def evaluationGSLT (kind : algebra.Kind) : GSLT :=
  equalityGSLT (State algebra kind) (Step algebra)

theorem path_to_steps {kind : algebra.Kind} {before after : State algebra kind}
    (path : (evaluationGSLT algebra kind).RewritePath before after) :
    Steps algebra before after := by
  match path with
  | .nil _ => exact .refl
  | .cons step rest => exact .head step (path_to_steps rest)
  termination_by structural path

theorem steps_iff_path {kind : algebra.Kind} (before after : State algebra kind) :
    Steps algebra before after ↔
      Nonempty ((evaluationGSLT algebra kind).RewritePath before after) := by
  constructor
  · intro steps
    induction steps using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨.nil _⟩
    | head step _ ih =>
        obtain ⟨path⟩ := ih
        exact ⟨.cons step path⟩
  · rintro ⟨path⟩
    exact path_to_steps algebra path

/-- Native type generated by OSLF at finite-path granularity. Its meaning is
reachability of the given value, independently of the direct fold definition. -/
def resultNativeType {kind : algebra.Kind} (value : algebra.Object kind) :
    PathNativeType (evaluationGSLT algebra kind) :=
  exactTargetNativeType (pathGSLT (evaluationGSLT algebra kind)) (.source value)

/-- A generated result type is inhabited exactly for the result computed by
the fold. Soundness uses step preservation; completeness uses normalization. -/
theorem satisfies_result_iff {kind : algebra.Kind} (state : State algebra kind)
    (value : algebra.Object kind) :
    (pathOSLF (evaluationGSLT algebra kind)).satisfies state
      (resultNativeType algebra value).pred ↔
        (valueAlgebra algebra).evaluate state = value := by
  refine (satisfies_exactTargetNativeType_iff_step
    (pathGSLT (evaluationGSLT algebra kind)) state (.source value)).trans ?_
  refine (nonempty_semanticPath_iff_rewritePath_of_equiv_iff_eq
    (evaluationGSLT algebra kind) (fun _ _ => Iff.rfl) state (.source value)).trans ?_
  refine (steps_iff_path algebra state (.source value)).symm.trans ?_
  constructor
  · intro steps
    exact steps_preserve algebra steps
  · intro evaluated
    rw [← evaluated]
    exact normalize algebra state

/-- Any prepared evaluator must supply native-type evidence for its output.
This is a semantic admission interface, not a check of example outputs. -/
structure AdmittedEvaluator where
  run : {kind : algebra.Kind} → State algebra kind → algebra.Object kind
  admitted : ∀ {kind : algebra.Kind} (state : State algebra kind),
    (pathOSLF (evaluationGSLT algebra kind)).satisfies state
      (resultNativeType algebra (run state)).pred

/-- Source-containing routes have the same operational result criterion;
source observation is explicit in `enterState`, not a missing tree case. -/
theorem entered_result_iff {kind : algebra.Kind}
    (route : ConstructionTree algebra kind) (value : algebra.Object kind) :
    (pathOSLF (evaluationGSLT algebra kind)).satisfies (enterState algebra route)
      (resultNativeType algebra value).pred ↔ algebra.evaluate route = value := by
  rw [satisfies_result_iff, enterState_evaluates]

/-- The direct fold is admitted by the operational normalization theorem. -/
def directEvaluator : AdmittedEvaluator algebra where
  run := (valueAlgebra algebra).evaluate
  admitted state := (satisfies_result_iff algebra state _).mpr rfl

/-- Native-type evidence licenses the evaluator's result at the reference
machine boundary. A different operation interpretation cannot borrow it. -/
theorem admittedEvaluator_sound (evaluator : AdmittedEvaluator algebra)
    {kind : algebra.Kind} (state : State algebra kind) :
    Steps algebra state (.source (evaluator.run state)) := by
  have correct := (satisfies_result_iff algebra state _).mp (evaluator.admitted state)
  rw [← correct]
  exact normalize algebra state

theorem admittedEvaluator_unique (first second : AdmittedEvaluator algebra)
    {kind : algebra.Kind} (state : State algebra kind) :
    first.run state = second.run state :=
  ((satisfies_result_iff algebra state _).mp (first.admitted state)).symm.trans
    ((satisfies_result_iff algebra state _).mp (second.admitted state))

#print axioms normalize
#print axioms satisfies_result_iff
#print axioms admittedEvaluator_sound
#print axioms admittedEvaluator_unique

end Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySortedEvaluation
