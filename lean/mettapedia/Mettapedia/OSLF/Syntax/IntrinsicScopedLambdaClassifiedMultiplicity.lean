import Mettapedia.OSLF.Syntax.IntrinsicScopedLambdaClassifiedInstance
import Mettapedia.OSLF.Syntax.LambdaDerivationGraph
import Mettapedia.OSLF.Syntax.FreePresheafEventImage

/-!
# Distinct actual classified Lambda histories with equal endpoints

The original Omega beta firing is the child of both application congruence
constructors. Their different authored rule addresses survive the complete
shared-to-local adapter, the canonical equation quotient, and the actual
categorical event objects. Doubling that operational graph adds retained
events while preserving its endpoint image.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLambdaClassifiedMultiplicity

open _root_.CategoryTheory
open LambdaContextualRung (sig Srt appT)
open LambdaDerivationGraph (duplicateBody omegaFunction omega)
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open IntrinsicScopedLambdaClassifiedInstance (rules eqs model)
open IntrinsicScopedAuthoredClassifiedInstance (algebra treeModel)
open IntrinsicScopedSharedLocalTreeComparison (toLocalTree)
open IntrinsicScopedLocalPolynomial (LocalRule Tree mapTree)
open IntrinsicScopedOperationalPresheafEvents (eventAtEquiv)
open IntrinsicScopedOperationalPresheafEventPowers (sourcePower_body targetPower_body)
open FreePresheafEventExtension (Graph Hom graphSum graphInl)
open FreePresheafEventImage (endpointMap endpointImage endpointImage_graphSum)

universe u

private def localRoot {S : Signature} (R : List (LocalRule S))
    {A : BindingCloneAlgebra.Algebra.{u} S} {j : Judgment A} (tree : Tree R A j) : Nat :=
  (Mettapedia.TypeTheory.IndexedPolynomial.Fix.out
    (IntrinsicScopedLocalPolynomial.rules R A) tree).1.1.index.val

private def sharedRoot {S : Signature} {M : List (MetaArity S)}
    (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    {A : BindingCloneAlgebra.Algebra.{u} S} {j : Judgment A}
    (tree : IntrinsicScopedConditionalSubstitution.Tree R A j) : Nat :=
  (Mettapedia.TypeTheory.IndexedPolynomial.Fix.out
    (IntrinsicScopedConditionalPolynomial.rules R A) tree).1.1.index.val

private theorem localRoot_map {S : Signature} (R : List (LocalRule S))
    {A B : BindingCloneAlgebra.Algebra.{u} S} (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (tree : Tree R A j) :
    localRoot R (mapTree R h j tree) = localRoot R tree := by
  let P := IntrinsicScopedLocalPolynomial.rules R A
  have compared : localRoot R (mapTree R h j
      (Mettapedia.TypeTheory.IndexedPolynomial.Fix.rollExtension P
        (Mettapedia.TypeTheory.IndexedPolynomial.Fix.out P tree))) =
      localRoot R (Mettapedia.TypeTheory.IndexedPolynomial.Fix.rollExtension P
        (Mettapedia.TypeTheory.IndexedPolynomial.Fix.out P tree)) := by
    generalize Mettapedia.TypeTheory.IndexedPolynomial.Fix.out P tree = layer
    rcases layer with ⟨shape, children⟩
    rfl
  simpa only [Mettapedia.TypeTheory.IndexedPolynomial.Fix.rollExtension_out] using compared

private theorem localRoot_adapter {S : Signature} {M : List (MetaArity S)}
    (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    {A : BindingCloneAlgebra.Algebra.{u} S} {j : Judgment A}
    (tree : IntrinsicScopedConditionalSubstitution.Tree R A j) :
    localRoot (IntrinsicScopedSharedLocalPolynomialComparison.localRules R)
      (toLocalTree R A j tree) = sharedRoot R tree := by
  let P := IntrinsicScopedConditionalPolynomial.rules R A
  have compared : localRoot (IntrinsicScopedSharedLocalPolynomialComparison.localRules R)
      (toLocalTree R A j (Mettapedia.TypeTheory.IndexedPolynomial.Fix.rollExtension P
        (Mettapedia.TypeTheory.IndexedPolynomial.Fix.out P tree))) =
      sharedRoot R (Mettapedia.TypeTheory.IndexedPolynomial.Fix.rollExtension P
        (Mettapedia.TypeTheory.IndexedPolynomial.Fix.out P tree)) := by
    generalize Mettapedia.TypeTheory.IndexedPolynomial.Fix.out P tree = layer
    rcases layer with ⟨shape, children⟩
    rfl
  simpa only [Mettapedia.TypeTheory.IndexedPolynomial.Fix.rollExtension_out] using compared

abbrev rawAlgebra := BindingCloneAlgebra.terms sig
abbrev quotientAlgebra := algebra eqs
abbrev evidenceModel := treeModel rules quotientAlgebra
abbrev projection := BindingEquationQuotientModel.projection eqs

def omegaJudgment : Judgment rawAlgebra := ⟨[], Srt.term, omega, omega⟩
def doubleOmega : Term sig [] Srt.term := appT omega omega
def doubleJudgment : Judgment rawAlgebra := ⟨[], Srt.term, doubleOmega, doubleOmega⟩

private def betaValuation :=
  IntrinsicLambdaFourRulePresentation.valuationOf [] duplicateBody duplicateBody
    omegaFunction omegaFunction omegaFunction

private def appValuation :=
  IntrinsicLambdaFourRulePresentation.valuationOf [] duplicateBody duplicateBody omega omega omega

private def betaOccurrence :=
  IntrinsicLambdaFourRulePresentation.betaOccurrence [] betaValuation
private def leftOccurrence :=
  IntrinsicLambdaFourRulePresentation.appCongLOccurrence [] appValuation
private def rightOccurrence :=
  IntrinsicLambdaFourRulePresentation.appCongROccurrence [] appValuation

private theorem beta_conclusion :
    IntrinsicScopedConditionalPolynomial.conclusionJudgment
      IntrinsicLambdaFourRulePresentation.rules rawAlgebra betaOccurrence = omegaJudgment :=
  IntrinsicLambdaFourRulePresentation.betaConclusion [] betaValuation

private theorem left_conclusion :
    IntrinsicScopedConditionalPolynomial.conclusionJudgment
      IntrinsicLambdaFourRulePresentation.rules rawAlgebra leftOccurrence = doubleJudgment :=
  IntrinsicLambdaFourRulePresentation.appCongLConclusion [] appValuation

private theorem right_conclusion :
    IntrinsicScopedConditionalPolynomial.conclusionJudgment
      IntrinsicLambdaFourRulePresentation.rules rawAlgebra rightOccurrence = doubleJudgment :=
  IntrinsicLambdaFourRulePresentation.appCongRConclusion [] appValuation

private theorem left_child
    (position : Fin (IntrinsicLambdaFourRulePresentation.rules.get leftOccurrence.index).premises.length) :
    IntrinsicScopedConditionalPolynomial.childJudgment
      IntrinsicLambdaFourRulePresentation.rules rawAlgebra leftOccurrence position = omegaJudgment := by
  have atZero : position = ⟨0, by decide⟩ := by
    apply Fin.ext
    change position.val = 0
    have bounded : position.val < 1 := position.isLt
    omega
  subst position
  exact IntrinsicLambdaFourRulePresentation.appCongLChild [] appValuation

private theorem right_child
    (position : Fin (IntrinsicLambdaFourRulePresentation.rules.get rightOccurrence.index).premises.length) :
    IntrinsicScopedConditionalPolynomial.childJudgment
      IntrinsicLambdaFourRulePresentation.rules rawAlgebra rightOccurrence position = omegaJudgment := by
  have atZero : position = ⟨0, by decide⟩ := by
    apply Fin.ext
    change position.val = 0
    have bounded : position.val < 1 := position.isLt
    omega
  subst position
  exact IntrinsicLambdaFourRulePresentation.appCongRChild [] appValuation

/-- A genuine original beta constructor, with its complete authored valuation. -/
def betaTree : IntrinsicScopedConditionalSubstitution.Tree
    IntrinsicLambdaFourRulePresentation.rules rawAlgebra omegaJudgment :=
  .roll ⟨betaOccurrence, beta_conclusion⟩ (fun position => position.elim0)

/-- The original left application occurrence retains its beta child. -/
def rawLeftTree : IntrinsicScopedConditionalSubstitution.Tree
    IntrinsicLambdaFourRulePresentation.rules rawAlgebra doubleJudgment :=
  .roll ⟨leftOccurrence, left_conclusion⟩
    (fun position => by
      change IntrinsicScopedConditionalSubstitution.Tree
        IntrinsicLambdaFourRulePresentation.rules rawAlgebra
        (IntrinsicScopedConditionalPolynomial.childJudgment
          IntrinsicLambdaFourRulePresentation.rules rawAlgebra leftOccurrence position)
      exact (left_child position).symm ▸ betaTree)

/-- The original right application occurrence retains the same beta child. -/
def rawRightTree : IntrinsicScopedConditionalSubstitution.Tree
    IntrinsicLambdaFourRulePresentation.rules rawAlgebra doubleJudgment :=
  .roll ⟨rightOccurrence, right_conclusion⟩
    (fun position => by
      change IntrinsicScopedConditionalSubstitution.Tree
        IntrinsicLambdaFourRulePresentation.rules rawAlgebra
        (IntrinsicScopedConditionalPolynomial.childJudgment
          IntrinsicLambdaFourRulePresentation.rules rawAlgebra rightOccurrence position)
      exact (right_child position).symm ▸ betaTree)

/-- The complete adapter and real quotient map act on the whole left history. -/
def leftTree : Tree rules quotientAlgebra (mapJudgment projection doubleJudgment) :=
  mapTree rules projection doubleJudgment
    (toLocalTree IntrinsicLambdaFourRulePresentation.rules rawAlgebra doubleJudgment rawLeftTree)

/-- The complete adapter and real quotient map act on the whole right history. -/
def rightTree : Tree rules quotientAlgebra (mapJudgment projection doubleJudgment) :=
  mapTree rules projection doubleJudgment
    (toLocalTree IntrinsicLambdaFourRulePresentation.rules rawAlgebra doubleJudgment rawRightTree)

/-- AppCongL keeps its actual declaration address in the canonical quotient. -/
theorem leftTree_root : localRoot rules leftTree = 1 :=
  (localRoot_map rules projection _).trans
    ((localRoot_adapter IntrinsicLambdaFourRulePresentation.rules _).trans rfl)

/-- AppCongR keeps its different declaration address in the same quotient. -/
theorem rightTree_root : localRoot rules rightTree = 2 :=
  (localRoot_map rules projection _).trans
    ((localRoot_adapter IntrinsicLambdaFourRulePresentation.rules _).trans rfl)

theorem trees_distinct : leftTree ≠ rightTree := by
  intro same
  have addresses := congrArg (localRoot rules) same
  rw [leftTree_root, rightTree_root] at addresses
  omega

abbrev closedStage := IntrinsicScopedAuthoredClassifiedReduction.stage eqs []
abbrev EventSection := (model.objects.event [] Srt.term).obj closedStage

/-- The real retained left history in the classified model's event object. -/
def leftEvent : EventSection :=
  (eventAtEquiv evidenceModel.toAction [] Srt.term closedStage).symm
    ⟨(projection.raw.map doubleOmega, projection.raw.map doubleOmega), leftTree⟩

/-- The real retained right history in the same categorical event object. -/
def rightEvent : EventSection :=
  (eventAtEquiv evidenceModel.toAction [] Srt.term closedStage).symm
    ⟨(projection.raw.map doubleOmega, projection.raw.map doubleOmega), rightTree⟩

private def eventRoot (event : EventSection) : Nat :=
  localRoot rules (eventAtEquiv evidenceModel.toAction [] Srt.term closedStage event).2

theorem leftEvent_root : eventRoot leftEvent = 1 := leftTree_root
theorem rightEvent_root : eventRoot rightEvent = 2 := rightTree_root

/-- Actual categorical events are distinct despite having the same endpoints. -/
theorem events_distinct : leftEvent ≠ rightEvent := by
  intro same
  have addresses := congrArg eventRoot same
  rw [leftEvent_root, rightEvent_root] at addresses
  omega

theorem left_source_body :
    MultiBinderPresheaf.scopedBodyEquiv quotientAlgebra closedStage.unop [] Srt.term
      ((model.objects.source [] Srt.term).app closedStage leftEvent) =
        projection.raw.map doubleOmega :=
  (sourcePower_body evidenceModel.toAction [] Srt.term closedStage leftEvent).trans rfl

theorem right_source_body :
    MultiBinderPresheaf.scopedBodyEquiv quotientAlgebra closedStage.unop [] Srt.term
      ((model.objects.source [] Srt.term).app closedStage rightEvent) =
        projection.raw.map doubleOmega :=
  (sourcePower_body evidenceModel.toAction [] Srt.term closedStage rightEvent).trans rfl

theorem left_target_body :
    MultiBinderPresheaf.scopedBodyEquiv quotientAlgebra closedStage.unop [] Srt.term
      ((model.objects.target [] Srt.term).app closedStage leftEvent) =
        projection.raw.map doubleOmega :=
  (targetPower_body evidenceModel.toAction [] Srt.term closedStage leftEvent).trans rfl

theorem right_target_body :
    MultiBinderPresheaf.scopedBodyEquiv quotientAlgebra closedStage.unop [] Srt.term
      ((model.objects.target [] Srt.term).app closedStage rightEvent) =
        projection.raw.map doubleOmega :=
  (targetPower_body evidenceModel.toAction [] Srt.term closedStage rightEvent).trans rfl

/-- The actual classified event graph has the model's chosen function-valued endpoints. -/
def graph : Graph (model.programModel.power [] Srt.term) where
  edge := model.objects.event [] Srt.term
  source := model.objects.source [] Srt.term
  target := model.objects.target [] Srt.term

theorem events_same_endpoints :
    (endpointMap graph).app closedStage leftEvent =
      (endpointMap graph).app closedStage rightEvent := by
  apply Prod.ext
  · exact (MultiBinderPresheaf.scopedBodyEquiv quotientAlgebra closedStage.unop [] Srt.term).injective
      (left_source_body.trans right_source_body.symm)
  · exact (MultiBinderPresheaf.scopedBodyEquiv quotientAlgebra closedStage.unop [] Srt.term).injective
      (left_target_body.trans right_target_body.symm)

theorem endpoint_map_not_injective :
    ¬ Function.Injective ((endpointMap graph).app closedStage) := by
  intro injective
  exact events_distinct (injective events_same_endpoints)

/-- Both copies consist of actual classified-model event sections. -/
def doubledGraph := graphSum graph graph
def firstCopy : Hom graph doubledGraph := graphInl graph graph

/-- The second copy adds retained histories without adding endpoint pairs. -/
theorem doubled_image_eq : endpointImage doubledGraph = endpointImage graph := by
  exact (endpointImage_graphSum graph graph).trans (sup_idem _)

/-- A concrete actual Lambda event in the second copy has no first-copy preimage. -/
theorem firstCopy_not_event_surjective :
    ¬ Function.Surjective (firstCopy.edgeMap.app closedStage) := by
  intro surjective
  obtain ⟨event, impossible⟩ := surjective (Sum.inr leftEvent)
  cases impossible

theorem image_equality_without_event_surjectivity :
    endpointImage doubledGraph = endpointImage graph ∧
      ¬ Function.Surjective (firstCopy.edgeMap.app closedStage) :=
  ⟨doubled_image_eq, firstCopy_not_event_surjective⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedLambdaClassifiedMultiplicity
