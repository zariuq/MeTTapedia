import Mettapedia.OSLF.Syntax.SecondOrderOperationalModal
import Mettapedia.OSLF.Syntax.Chapter7AlgebraicOperationalInstances
import Mettapedia.OSLF.Syntax.IntrinsicLambdaFourRulePresentation
import Mettapedia.OSLF.Syntax.RhoPayloadPresentation

/-!
# Authored Chapter 7 languages in the equation-class operational model

The same context-indexed operational construction accepts the actual JSON,
monoid, four-rule lambda and reflective rho declarations. The positive
controls below transport established lambda and rho firing trees into the
equation-class model. The negative controls for the empty-rule languages
remain valid at every contextual stage.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private abbrev jsonEquations :
    List (EqAxiom JsonTermRung.sig ([] : List (MetaArity JsonTermRung.sig))) := []
private abbrev jsonRules :
    List (Rule JsonTermRung.sig ([] : List (MetaArity JsonTermRung.sig))) := []
private abbrev monoidRules :
    List (Rule MonoidEquationRung.sig MonoidEquationRung.metas) := []

/-- The authored JSON operations are data constructors and carry no
operational rewrite rule. -/
noncomputable def jsonOperationalContexts :=
  authoredQuotientOperationalPresheaf JsonTermRung.sig jsonEquations jsonRules

/-- Authored monoid equations identify programs without creating firings. -/
noncomputable def monoidOperationalContexts :=
  authoredQuotientOperationalPresheaf MonoidEquationRung.sig
    MonoidEquationRung.monoidE monoidRules

/-- The one shared lambda presentation contains beta and all three
congruence rules, with the abstraction premise under its own binder. -/
noncomputable def lambdaOperationalContexts :=
  authoredQuotientOperationalPresheaf LambdaContextualRung.sig
    ([] : List (EqAxiom LambdaContextualRung.sig
      IntrinsicLambdaFourRulePresentation.metas))
    IntrinsicLambdaFourRulePresentation.rules

/-- Communication and parallel congruence in the strict reflective core. -/
noncomputable def rhoStrictOperationalContexts :=
  authoredQuotientOperationalPresheaf RhoPayloadPresentation.sig
    RhoPayloadPresentation.equations RhoPayloadPresentation.strictRules

/-- The book profile adds an explicit drop execution rule. -/
noncomputable def rhoBookOperationalContexts :=
  authoredQuotientOperationalPresheaf RhoPayloadPresentation.sig
    RhoPayloadPresentation.equations RhoPayloadPresentation.bookRules

/-- No firing can be manufactured at any contextual stage of the authored
JSON language. -/
theorem json_no_firing (X : Object JsonTermRung.sig)
    (judgment : Judgment
      (authoredEquationModelAt JsonTermRung.sig jsonEquations X).algebra) :
    ¬ Reduces jsonRules judgment :=
  no_rules_no_reduction _ judgment

/-- Monoid equations do not turn into operational rewrite rules at any
contextual stage. -/
theorem monoid_no_firing (X : Object MonoidEquationRung.sig)
    (judgment : Judgment
      (authoredEquationModelAt MonoidEquationRung.sig
        MonoidEquationRung.monoidE X).algebra) :
    ¬ Reduces monoidRules judgment :=
  no_rules_no_reduction _ judgment

/-- The authored JSON presentation has an empty endpoint image: data
constructors alone cannot create an operational firing. -/
theorem json_no_reduction_image (X : Object JsonTermRung.sig)
    (sort : JsonTermRung.sig.Srt)
    (source target : (authoredStates JsonTermRung.sig
      jsonEquations jsonRules sort).obj
        (Opposite.op
          ((authoredEquationPresentation JsonTermRung.sig
            jsonEquations).quotientFunctor.obj X))) :
    (source, target) ∉
      (authoredReduction JsonTermRung.sig jsonEquations jsonRules sort).obj
        (Opposite.op
          ((authoredEquationPresentation JsonTermRung.sig
            jsonEquations).quotientFunctor.obj X)) := by
  intro observed
  exact json_no_firing X _
    ((authoredReduction_iff_reduces JsonTermRung.sig
      jsonEquations jsonRules sort
      (Opposite.op
        ((authoredEquationPresentation JsonTermRung.sig
          jsonEquations).quotientFunctor.obj X)) source target).1 observed)

/-- Monoid equations quotient program states but still add no rewrite
occurrence; their endpoint image is empty at every context. -/
theorem monoid_no_reduction_image (X : Object MonoidEquationRung.sig)
    (sort : MonoidEquationRung.sig.Srt)
    (source target : (authoredStates MonoidEquationRung.sig
      MonoidEquationRung.monoidE monoidRules sort).obj
        (Opposite.op
          ((authoredEquationPresentation MonoidEquationRung.sig
            MonoidEquationRung.monoidE).quotientFunctor.obj X))) :
    (source, target) ∉
      (authoredReduction MonoidEquationRung.sig
        MonoidEquationRung.monoidE monoidRules sort).obj
        (Opposite.op
          ((authoredEquationPresentation MonoidEquationRung.sig
            MonoidEquationRung.monoidE).quotientFunctor.obj X)) := by
  intro observed
  exact monoid_no_firing X _
    ((authoredReduction_iff_reduces MonoidEquationRung.sig
      MonoidEquationRung.monoidE monoidRules sort
      (Opposite.op
        ((authoredEquationPresentation MonoidEquationRung.sig
          MonoidEquationRung.monoidE).quotientFunctor.obj X))
      source target).1 observed)

/-- Every step of the actual four-rule contextual lambda relation yields a
retained firing tree in the equation-class model at every authored context. -/
theorem lambda_step_has_event (X : Object LambdaContextualRung.sig)
    {Γ : Ctx LambdaContextualRung.sig}
    {source target : Term LambdaContextualRung.sig Γ .term}
    (step : LambdaContextualRung.Step Γ source target) :
    Reduces IntrinsicLambdaFourRulePresentation.rules
      (mapJudgment
        (FreeBindingClone.interpretHom
          (authoredEquationModelAt LambdaContextualRung.sig
            ([] : List (EqAxiom LambdaContextualRung.sig
              IntrinsicLambdaFourRulePresentation.metas)) X).algebra)
        (⟨Γ, .term, source, target⟩ :
          Judgment (BindingCloneAlgebra.terms LambdaContextualRung.sig))) :=
  reduces_map IntrinsicLambdaFourRulePresentation.rules
    (FreeBindingClone.interpretHom
      (authoredEquationModelAt LambdaContextualRung.sig
        ([] : List (EqAxiom LambdaContextualRung.sig
          IntrinsicLambdaFourRulePresentation.metas)) X).algebra)
    (IntrinsicLambdaFourRulePresentation.sourceStep_to_reduces step)

/-- An actual strict-core communication survives in every equation-class
context. The conclusion still records the received payload substitution. -/
theorem rho_strict_comm_has_event (X : Object RhoPayloadPresentation.sig)
    {Γ : Ctx RhoPayloadPresentation.sig}
    (channel : Term RhoPayloadPresentation.sig Γ .nm)
    (payload : Term RhoPayloadPresentation.sig Γ .pr)
    (continuation : Term RhoPayloadPresentation.sig (.pr :: Γ) .pr) :
    Reduces RhoPayloadPresentation.strictRules
      (mapJudgment
        (FreeBindingClone.interpretHom
          (authoredEquationModelAt RhoPayloadPresentation.sig
            RhoPayloadPresentation.equations X).algebra)
        (⟨Γ, .pr,
          RhoPayloadPresentation.parT
            (RhoPayloadPresentation.outT channel payload)
            (RhoPayloadPresentation.inpT channel continuation),
          inst continuation payload⟩ :
          Judgment (BindingCloneAlgebra.terms RhoPayloadPresentation.sig))) :=
  reduces_map RhoPayloadPresentation.strictRules
    (FreeBindingClone.interpretHom
      (authoredEquationModelAt RhoPayloadPresentation.sig
        RhoPayloadPresentation.equations X).algebra)
    (RhoPayloadPresentation.comm_reduces [] channel payload continuation)

/-- The additional book-profile drop constructor also survives quotienting;
it is not silently inserted into the strict profile. -/
theorem rho_book_drop_has_event (X : Object RhoPayloadPresentation.sig)
    {Γ : Ctx RhoPayloadPresentation.sig}
    (code : Term RhoPayloadPresentation.sig Γ .pr) :
    Reduces RhoPayloadPresentation.bookRules
      (mapJudgment
        (FreeBindingClone.interpretHom
          (authoredEquationModelAt RhoPayloadPresentation.sig
            RhoPayloadPresentation.equations X).algebra)
        (⟨Γ, .pr,
          RhoPayloadPresentation.drpT (RhoPayloadPresentation.quoT code), code⟩ :
          Judgment (BindingCloneAlgebra.terms RhoPayloadPresentation.sig))) :=
  reduces_map RhoPayloadPresentation.bookRules
    (FreeBindingClone.interpretHom
      (authoredEquationModelAt RhoPayloadPresentation.sig
        RhoPayloadPresentation.equations X).algebra)
    (RhoPayloadPresentation.drop_reduces code)

/-- Every closed lambda step, including the actual binder-local LamCong
case, belongs to the image of the retained event graph after contextual
equations are imposed. -/
theorem lambda_closed_step_in_reduction (X : Object LambdaContextualRung.sig)
    {source target : Term LambdaContextualRung.sig [] .term}
    (step : LambdaContextualRung.Step [] source target) :
    let E : List (EqAxiom LambdaContextualRung.sig
      IntrinsicLambdaFourRulePresentation.metas) := []
    let A := (authoredEquationModelAt LambdaContextualRung.sig E X).algebra
    let interpret := FreeBindingClone.interpretHom A
    (interpret.raw.map source, interpret.raw.map target) ∈
      (authoredReduction LambdaContextualRung.sig E
        IntrinsicLambdaFourRulePresentation.rules .term).obj
        (Opposite.op
          ((authoredEquationPresentation LambdaContextualRung.sig E).quotientFunctor.obj X)) := by
  exact (authoredReduction_iff_reduces
    LambdaContextualRung.sig
    ([] : List (EqAxiom LambdaContextualRung.sig
      IntrinsicLambdaFourRulePresentation.metas))
    IntrinsicLambdaFourRulePresentation.rules .term
    (Opposite.op ((authoredEquationPresentation LambdaContextualRung.sig
      ([] : List (EqAxiom LambdaContextualRung.sig
        IntrinsicLambdaFourRulePresentation.metas))).quotientFunctor.obj X))
    _ _).2 (lambda_step_has_event X step)

/-- A genuine reflective communication belongs to the endpoint image of
the strict authored rho graph, with its payload substitution retained in
the event tree. -/
theorem rho_strict_comm_in_reduction (X : Object RhoPayloadPresentation.sig)
    (channel : Term RhoPayloadPresentation.sig [] .nm)
    (payload : Term RhoPayloadPresentation.sig [] .pr)
    (continuation : Term RhoPayloadPresentation.sig [.pr] .pr) :
    let A := (authoredEquationModelAt RhoPayloadPresentation.sig
      RhoPayloadPresentation.equations X).algebra
    let interpret := FreeBindingClone.interpretHom A
    (interpret.raw.map
        (RhoPayloadPresentation.parT
          (RhoPayloadPresentation.outT channel payload)
          (RhoPayloadPresentation.inpT channel continuation)),
      interpret.raw.map (inst continuation payload)) ∈
      (authoredReduction RhoPayloadPresentation.sig
        RhoPayloadPresentation.equations
        RhoPayloadPresentation.strictRules .pr).obj
        (Opposite.op
          ((authoredEquationPresentation RhoPayloadPresentation.sig
            RhoPayloadPresentation.equations).quotientFunctor.obj X)) := by
  exact (authoredReduction_iff_reduces
    RhoPayloadPresentation.sig RhoPayloadPresentation.equations
    RhoPayloadPresentation.strictRules .pr
    (Opposite.op ((authoredEquationPresentation RhoPayloadPresentation.sig
      RhoPayloadPresentation.equations).quotientFunctor.obj X))
    _ _).2 (rho_strict_comm_has_event X channel payload continuation)

/-- For this LamCong instance the executor emits the stated ordered history,
and the corresponding intrinsic beta-under-lambda step belongs to the
equation-class endpoint image. This does not assert a general map from
executor histories to retained semantic firing trees. -/
theorem lambda_lamCong_runtime_in_reduction
    (X : Object LambdaContextualRung.sig)
    (inner : Term LambdaContextualRung.sig [.term, .term] .term)
    (argument : Term LambdaContextualRung.sig [.term] .term) :
    ((Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.RuleHistory.fire 1
        [.step 0 0 (.fire 0 [])],
      Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
        (LambdaContextualRung.lamT
          (inst inner argument))) ∈
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
        2 0
        (Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
          (LambdaContextualRung.lamT
            (LambdaContextualRung.appT
              (LambdaContextualRung.lamT inner) argument)))) ∧
    (let E : List (EqAxiom LambdaContextualRung.sig
        IntrinsicLambdaFourRulePresentation.metas) := []
     let A := (authoredEquationModelAt LambdaContextualRung.sig E X).algebra
     let interpret := FreeBindingClone.interpretHom A
     (interpret.raw.map
        (LambdaContextualRung.lamT
          (LambdaContextualRung.appT
            (LambdaContextualRung.lamT inner) argument)),
      interpret.raw.map
        (LambdaContextualRung.lamT (inst inner argument))) ∈
       (authoredReduction LambdaContextualRung.sig E
         IntrinsicLambdaFourRulePresentation.rules .term).obj
         (Opposite.op
           ((authoredEquationPresentation LambdaContextualRung.sig E).quotientFunctor.obj X))) := by
  have both :=
    IntrinsicLambdaFourRulePresentation.authoredLamCong_matches_intrinsic
      inner argument
  constructor
  · exact both.1
  · exact (authoredReduction_iff_reduces
      LambdaContextualRung.sig
      ([] : List (EqAxiom LambdaContextualRung.sig
        IntrinsicLambdaFourRulePresentation.metas))
      IntrinsicLambdaFourRulePresentation.rules .term
      (Opposite.op ((authoredEquationPresentation LambdaContextualRung.sig
        ([] : List (EqAxiom LambdaContextualRung.sig
          IntrinsicLambdaFourRulePresentation.metas))).quotientFunctor.obj X))
      _ _).2
        (reduces_map IntrinsicLambdaFourRulePresentation.rules
          (FreeBindingClone.interpretHom
            (authoredEquationModelAt LambdaContextualRung.sig
              ([] : List (EqAxiom LambdaContextualRung.sig
                IntrinsicLambdaFourRulePresentation.metas)) X).algebra)
          both.2)

/-- The real scoped LamCong execution yields the generated may-observation
at every authored equation context.  The target predicate selects its
specific contracted body; the firing tree remains available separately. -/
theorem lambda_lamCong_runtime_may
    (X : Object LambdaContextualRung.sig)
    (inner : Term LambdaContextualRung.sig [.term, .term] .term)
    (argument : Term LambdaContextualRung.sig [.term] .term) :
    let E : List (EqAxiom LambdaContextualRung.sig
      IntrinsicLambdaFourRulePresentation.metas) := []
    let A := (authoredEquationModelAt LambdaContextualRung.sig E X).algebra
    let interpret := FreeBindingClone.interpretHom A
    let context := Opposite.op
      ((authoredEquationPresentation LambdaContextualRung.sig E).quotientFunctor.obj X)
    gsltDiamond
      (authoredTheoryAt LambdaContextualRung.sig E
        IntrinsicLambdaFourRulePresentation.rules .term context)
      (fun candidate =>
        candidate = interpret.raw.map
          (LambdaContextualRung.lamT (inst inner argument)))
      (interpret.raw.map
        (LambdaContextualRung.lamT
          (LambdaContextualRung.appT
            (LambdaContextualRung.lamT inner) argument))) := by
  have image := (lambda_lamCong_runtime_in_reduction X inner argument).2
  exact (gsltDiamond_singleton_iff_step
    (authoredTheoryAt LambdaContextualRung.sig
      ([] : List (EqAxiom LambdaContextualRung.sig
        IntrinsicLambdaFourRulePresentation.metas))
      IntrinsicLambdaFourRulePresentation.rules .term
      (Opposite.op
        ((authoredEquationPresentation LambdaContextualRung.sig
          ([] : List (EqAxiom LambdaContextualRung.sig
            IntrinsicLambdaFourRulePresentation.metas))).quotientFunctor.obj X)))
    _ _).2 image

/-- No JSON state has the generated may-observation at any equation context
or target predicate: constructors are not operational rules. -/
theorem json_no_may
    (X : Object JsonTermRung.sig) (sort : JsonTermRung.sig.Srt)
    (predicate : (authoredStates JsonTermRung.sig
      jsonEquations jsonRules sort).obj
        (Opposite.op
          ((authoredEquationPresentation JsonTermRung.sig
            jsonEquations).quotientFunctor.obj X)) → Prop)
    (source : (authoredStates JsonTermRung.sig
      jsonEquations jsonRules sort).obj
        (Opposite.op
          ((authoredEquationPresentation JsonTermRung.sig
            jsonEquations).quotientFunctor.obj X))) :
    ¬ gsltDiamond
      (authoredTheoryAt JsonTermRung.sig
        jsonEquations jsonRules sort
        (Opposite.op
          ((authoredEquationPresentation JsonTermRung.sig
            jsonEquations).quotientFunctor.obj X)))
      predicate source := by
  intro may
  obtain ⟨target, firing, _⟩ :=
    (authoredDiamond_iff_reduces JsonTermRung.sig
      jsonEquations jsonRules sort _ predicate source).1 may
  exact json_no_firing X _ firing

/-- A strict-core reflective communication has the generated may-observation
at its actual substituted continuation. The book-only Drop rule is not used. -/
theorem rho_strict_comm_may
    (X : Object RhoPayloadPresentation.sig)
    (channel : Term RhoPayloadPresentation.sig [] .nm)
    (payload : Term RhoPayloadPresentation.sig [] .pr)
    (continuation : Term RhoPayloadPresentation.sig [.pr] .pr) :
    let E := RhoPayloadPresentation.equations
    let A := (authoredEquationModelAt RhoPayloadPresentation.sig E X).algebra
    let interpret := FreeBindingClone.interpretHom A
    let context := Opposite.op
      ((authoredEquationPresentation RhoPayloadPresentation.sig E).quotientFunctor.obj X)
    gsltDiamond
      (authoredTheoryAt RhoPayloadPresentation.sig E
        RhoPayloadPresentation.strictRules .pr context)
      (fun candidate => candidate = interpret.raw.map (inst continuation payload))
      (interpret.raw.map
        (RhoPayloadPresentation.parT
          (RhoPayloadPresentation.outT channel payload)
          (RhoPayloadPresentation.inpT channel continuation))) := by
  exact (gsltDiamond_singleton_iff_step
    (authoredTheoryAt RhoPayloadPresentation.sig
      RhoPayloadPresentation.equations
      RhoPayloadPresentation.strictRules .pr
      (Opposite.op
        ((authoredEquationPresentation RhoPayloadPresentation.sig
          RhoPayloadPresentation.equations).quotientFunctor.obj X)))
    _ _).2
      (rho_strict_comm_in_reduction X channel payload continuation)

/-- Monoid equations alone create no may-step, regardless of the chosen
target predicate. -/
theorem monoid_no_may
    (X : Object MonoidEquationRung.sig) (sort : MonoidEquationRung.sig.Srt)
    (predicate : (authoredStates MonoidEquationRung.sig
      MonoidEquationRung.monoidE monoidRules sort).obj
        (Opposite.op
          ((authoredEquationPresentation MonoidEquationRung.sig
            MonoidEquationRung.monoidE).quotientFunctor.obj X)) → Prop)
    (source : (authoredStates MonoidEquationRung.sig
      MonoidEquationRung.monoidE monoidRules sort).obj
        (Opposite.op
          ((authoredEquationPresentation MonoidEquationRung.sig
            MonoidEquationRung.monoidE).quotientFunctor.obj X))) :
    ¬ gsltDiamond
      (authoredTheoryAt MonoidEquationRung.sig
        MonoidEquationRung.monoidE monoidRules sort
        (Opposite.op
          ((authoredEquationPresentation MonoidEquationRung.sig
            MonoidEquationRung.monoidE).quotientFunctor.obj X)))
      predicate source := by
  intro may
  obtain ⟨target, firing, _⟩ :=
    (authoredDiamond_iff_reduces MonoidEquationRung.sig
      MonoidEquationRung.monoidE monoidRules sort _ predicate source).1 may
  exact monoid_no_firing X _ firing

end Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.lambda_step_has_event
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.rho_strict_comm_has_event
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.rho_book_drop_has_event
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.lambda_closed_step_in_reduction
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.rho_strict_comm_in_reduction
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.json_no_reduction_image
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.monoid_no_reduction_image
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.lambda_lamCong_runtime_in_reduction
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.lambda_lamCong_runtime_may
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.json_no_may
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.rho_strict_comm_may
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.Chapter7Clients.monoid_no_may
