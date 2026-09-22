import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProducts

/-!
# A dependent shared-quotient product workload

These controls invoke the actual shared Pi/Sigma meaning and admitted-beta
clauses on the same `data common`. The family is native identity at its
Data argument, its body is native reflexivity, and application receives a
real mixed HOL-list/wire projection. The resulting proof is then the second
component of a dependent pair whose two projections use those same clauses.

This is a connected constructor workload, not a full shared model or a
claim that arbitrary failed proof submissions make their propositions false.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProductExamples

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive FormationSensitiveContextual SharedJudgmentFragment
open SharedJudgmentQuotientInterpretation SharedJudgmentQuotientComprehension
open SharedJudgmentTypeInterpretation SharedJudgmentQuotientProducts
open QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

noncomputable section

abbrev source : SharedJudgmentInterpretation.Context common 0 := .nil

def family := canonicalFamily source Common.wireType ComparisonControls.variableIdentity

theorem family_admitted : FamilyAdmitted common source.raw Common.wireType.code
    ComparisonControls.variableIdentity.code := by
  exact ⟨.sort Tower.zero, .sort Tower.zero, .sort (.max Tower.zero Tower.zero),
    Common.wireType.judgment, .sort _, ComparisonControls.variableIdentity.judgment,
    .sort _, .sorts _ _⟩

theorem family_meaning : FamilyMeaning (data common) family :=
  canonical_family_meaning source Common.wireType ComparisonControls.variableIdentity

def body : QuotientCwf.Tm
    (QuotientCwf.ext ((data common).ctx source) family.semanticDomain) family.semanticCodomain :=
  QuotientProducts.Controls.reflexivityBody

theorem body_meaning :
    (data common).term family.context ComparisonControls.variableReflexivity.code
      ComparisonControls.variableIdentity.code
      (QuotientCwf.tySub family.semanticCodomain family.comparison.forward)
      (QuotientCwf.tmSub body family.comparison.forward) := by
  apply meaning_of_code_conversion (assembly := common) (source := family.context)
    ComparisonControls.variableReflexivity.judgment family_meaning.2.2
  have represented := chosenTerm_represents body
    (ComparisonControls.variableReflexivity.reindex QuotientProducts.Controls.wireBinder.hom) rfl
  change Conv _ _ (subst ids ComparisonControls.variableReflexivity.code) _ at represented
  rw [subst_ids] at represented
  exact .trans _ _ _
    (QuotientProductTermRepresentation.chosenTerm_through_presentation Common.wireType body)
    represented

def argument (wire : NativeWireData.Wire) :
    QuotientCwf.Tm ((data common).ctx source) family.semanticDomain :=
  QuotientCwf.Controls.projected wire

theorem argument_meaning (wire : NativeWireData.Wire) :
    (data common).term source (Common.projected wire).code Common.wireType.code
      family.semanticDomain (argument wire) :=
  QuotientInterpretation.term_meaning _ (Common.projected wire)

def function : QuotientCwf.Tm ((data common).ctx source)
    (QuotientProducts.pi family.semanticDomain family.semanticCodomain) :=
  QuotientProducts.lam body

def lambdaCode : Tower.Tm 0 := .lam ComparisonControls.variableReflexivity.code

theorem pi_type_meaning :
    (data common).ty source (.pi Common.wireType.code ComparisonControls.variableIdentity.code)
      (QuotientProducts.pi family.semanticDomain family.semanticCodomain) :=
  pi_formation_meaning 0 source _ _ family family_admitted family_meaning

theorem lambda_admitted : Judgment common.rules source.raw lambdaCode
    (.pi Common.wireType.code ComparisonControls.variableIdentity.code) :=
  (QuotientProducts.nativeLambda ComparisonControls.variableReflexivity).judgment

theorem lambda_meaning :
    (data common).term source lambdaCode
      (.pi Common.wireType.code ComparisonControls.variableIdentity.code)
      (QuotientProducts.pi family.semanticDomain family.semanticCodomain) function :=
  pi_introduction_meaning 0 source _ _ _ family body family_admitted family_meaning
    ComparisonControls.variableReflexivity.judgment body_meaning

def resultType (wire : NativeWireData.Wire) : Tower.Tm 0 :=
  inst0 (Common.projected wire).code ComparisonControls.variableIdentity.code

theorem result_type_retains_actual_endpoint (wire : NativeWireData.Wire) :
    resultType wire = .id NativeWireData.dataType (Common.projected wire).code
      (Common.projected wire).code := rfl

def applicationCode (wire : NativeWireData.Wire) : Tower.Tm 0 :=
  .app lambdaCode (Common.projected wire).code

def application (wire : NativeWireData.Wire) :
    QuotientCwf.Tm ((data common).ctx source)
      (QuotientCwf.tySub family.semanticCodomain
        (selfExtend (QuotientCwf.cwf common.rules) (argument wire))) :=
  QuotientProducts.app function (argument wire)

theorem application_admitted (wire : NativeWireData.Wire) :
    Judgment common.rules source.raw (applicationCode wire) (resultType wire) :=
  ⟨source.formed, .appElim lambda_admitted.typing (Common.projected wire).typed⟩

theorem application_meaning (wire : NativeWireData.Wire) :
    (data common).ty source (resultType wire)
        (QuotientCwf.tySub family.semanticCodomain
          (selfExtend (QuotientCwf.cwf common.rules) (argument wire))) ∧
      (data common).term source (applicationCode wire) (resultType wire)
        (QuotientCwf.tySub family.semanticCodomain
          (selfExtend (QuotientCwf.cwf common.rules) (argument wire))) (application wire) :=
  pi_elimination_meaning 0 source _ _ _ _ family function (argument wire)
    family_admitted family_meaning lambda_admitted (Common.projected wire).judgment
    lambda_meaning (argument_meaning wire)

theorem application_beta (wire : NativeWireData.Wire) :
    application wire = QuotientCwf.tmSub body
      (selfExtend (QuotientCwf.cwf common.rules) (argument wire)) :=
  pi_beta 0 source _ _ _ _ family body (argument wire) family_admitted family_meaning
    ComparisonControls.variableReflexivity.judgment (Common.projected wire).judgment
    body_meaning (argument_meaning wire)

theorem sigma_type_meaning :
    (data common).ty source (.sigma Common.wireType.code ComparisonControls.variableIdentity.code)
      (QuotientProducts.sigma family.semanticDomain family.semanticCodomain) :=
  sigma_formation_meaning 0 source _ _ family family_admitted family_meaning

def pairCode (wire : NativeWireData.Wire) : Tower.Tm 0 :=
  .pair (Common.projected wire).code (applicationCode wire)

def dependentPair (wire : NativeWireData.Wire) :
    QuotientCwf.Tm ((data common).ctx source)
      (QuotientProducts.sigma family.semanticDomain family.semanticCodomain) :=
  QuotientProducts.pair (argument wire) (application wire)

theorem pair_admitted (wire : NativeWireData.Wire) :
    Judgment common.rules source.raw (pairCode wire)
      (.sigma Common.wireType.code ComparisonControls.variableIdentity.code) :=
  ⟨source.formed, .pairIntro
    (QuotientProducts.nativeSigma Common.wireType ComparisonControls.variableIdentity).formed
    (QuotientProducts.nativeSigma Common.wireType ComparisonControls.variableIdentity).universeWitness
    (Common.projected wire).typed (application_admitted wire).typing⟩

theorem pair_meaning (wire : NativeWireData.Wire) :
    (data common).term source (pairCode wire)
      (.sigma Common.wireType.code ComparisonControls.variableIdentity.code)
      (QuotientProducts.sigma family.semanticDomain family.semanticCodomain) (dependentPair wire) :=
  sigma_introduction_meaning 0 source _ _ _ _ family (argument wire) (application wire)
    family_admitted family_meaning (Common.projected wire).judgment (application_admitted wire)
    (argument_meaning wire) (application_meaning wire).2

theorem projections_meaning (wire : NativeWireData.Wire) :
    (data common).term source (.fst (pairCode wire)) Common.wireType.code
        family.semanticDomain (QuotientProducts.fst (dependentPair wire)) ∧
      (data common).ty source (inst0 (.fst (pairCode wire)) ComparisonControls.variableIdentity.code)
        (QuotientCwf.tySub family.semanticCodomain
          (selfExtend (QuotientCwf.cwf common.rules) (QuotientProducts.fst (dependentPair wire)))) ∧
      (data common).term source (.snd (pairCode wire))
        (inst0 (.fst (pairCode wire)) ComparisonControls.variableIdentity.code)
        (QuotientCwf.tySub family.semanticCodomain
          (selfExtend (QuotientCwf.cwf common.rules) (QuotientProducts.fst (dependentPair wire))))
        (QuotientProducts.snd (dependentPair wire)) :=
  sigma_elimination_meaning 0 source _ _ _ family (dependentPair wire)
    family_admitted family_meaning (pair_admitted wire) (pair_meaning wire)

theorem pair_beta (wire : NativeWireData.Wire) :
    QuotientProducts.fst (dependentPair wire) = argument wire ∧
      HEq (QuotientProducts.snd (dependentPair wire)) (application wire) :=
  sigma_beta 0 source _ _ _ _ family (argument wire) (application wire)
    family_admitted family_meaning (Common.projected wire).judgment (application_admitted wire)
    (argument_meaning wire) (application_meaning wire).2

/-- The shared admitted-beta clause supplies the application equation;
the existing native body computation then identifies its exact proof value. -/
theorem application_returns_reflexivity (wire : NativeWireData.Wire) :
    (application wire).val = QTerm.mk (QuotientProducts.Controls.expectedReflexivity wire) := by
  exact (congrArg Subtype.val (application_beta wire)).trans
    ((congrArg (fun value : QuotientCwf.Tm ((data common).ctx source) family.semanticDomain =>
        (QuotientCwf.tmSub body (selfExtend (QuotientCwf.cwf common.rules) value)).val)
      (QuotientCwf.Controls.projected_is_result wire)).trans
        (QuotientProducts.Controls.body_instantiation wire))

/-- The exact result class is attached to the original submitted application
and its projection-dependent annotation, via the shared elimination clause. -/
theorem application_exact_meaning (wire : NativeWireData.Wire) :
    (data common).term source (applicationCode wire) (resultType wire)
      (QType.mk (QuotientProducts.Controls.expectedType wire))
      (TermFibre.mk (QuotientProducts.Controls.expectedReflexivity wire)) := by
  obtain ⟨annotation, code, actual, actualCode, _, value⟩ := (application_meaning wire).2
  have actualValue := value.trans (application_returns_reflexivity wire)
  exact ⟨annotation, code, actual, actualCode, congrArg QTerm.type actualValue, actualValue⟩

theorem pair_first_returns_wire (wire : NativeWireData.Wire) :
    QuotientProducts.fst (dependentPair wire) = QuotientCwf.Controls.result wire :=
  (pair_beta wire).1.trans (QuotientCwf.Controls.projected_is_result wire)

theorem pair_second_returns_reflexivity (wire : NativeWireData.Wire) :
    (QuotientProducts.snd (dependentPair wire)).val =
      QTerm.mk (QuotientProducts.Controls.expectedReflexivity wire) := by
  have sameType := congrArg (fun value : QuotientCwf.Tm ((data common).ctx source) family.semanticDomain =>
    QuotientCwf.tySub family.semanticCodomain (selfExtend (QuotientCwf.cwf common.rules) value))
      (pair_beta wire).1
  exact (heq_value sameType (pair_beta wire).2).trans (application_returns_reflexivity wire)

/-- Changing the input changes the dependent pair's first observable value. -/
theorem changed_seven_to_eight_rejected : dependentPair (.natural 7) ≠ dependentPair (.natural 8) := by
  intro same
  exact QuotientCwf.Controls.seven_is_not_eight
    ((pair_first_returns_wire (.natural 7)).symm.trans
      ((congrArg QuotientProducts.fst same).trans (pair_first_returns_wire (.natural 8))))

private theorem identity_right_development {n : Nat} {carrier left right target : Tower.Tm n}
    (steps : NativeRelatorConversionParallel.ParStar (.id carrier left right) target) :
    ∃ carrier' left' right', target = .id carrier' left' right' ∧
      NativeRelatorConversionParallel.ParStar right right' := by
  induction steps with
  | refl => exact ⟨_, _, _, rfl, .refl⟩
  | tail _ finalStep ih =>
      obtain ⟨_, _, _, rfl, rightSteps⟩ := ih
      cases finalStep with
      | id _ _ last => exact ⟨_, _, _, rfl, rightSteps.tail last⟩

/-- Right-endpoint conversion is recovered from the actual common-reduct
theorem. Existing opaque natural-constant rigidity then rejects 7 versus 8. -/
theorem changed_endpoint_not_convertible :
    ¬ Conv common.rules.headEq
      (.id NativeWireData.dataType (NativeWireData.encode (n := 0) (.natural 7))
        (NativeWireData.encode (.natural 7)))
      (.id NativeWireData.dataType (NativeWireData.encode (.natural 7))
        (NativeWireData.encode (.natural 8))) common.rules.computation := by
  intro converted
  obtain ⟨commonTerm, before, after⟩ := NativeRelatorConversionParallel.conversion_join
    ((OpaqueRelatorExtension.conversion_iff HOLNativeRelatorCompatibility.opacity).mp converted)
  obtain ⟨_, _, first, firstShape, firstSteps⟩ := identity_right_development before
  obtain ⟨_, _, second, secondShape, secondSteps⟩ := identity_right_development after
  have endpoints : first = second := (Tm.id.inj (firstShape.symm.trans secondShape)).2.2
  subst second
  have rightConversion : NativeRelatorConversionCompletion.AuthoredConv
      (NativeWireData.encode (n := 0) (.natural 7)) (NativeWireData.encode (.natural 8)) :=
    .trans _ _ _ firstSteps.sound secondSteps.sound.symm
  have impossible := (QuotientControls.natural_conversion_iff (n := 0) 7 8).mp
    ((OpaqueRelatorExtension.conversion_iff HOLNativeRelatorCompatibility.opacity).mpr rightConversion)
  cases impossible

/-- The altered target is itself formed; its rejection below is not an
unavailable-type or malformed-context control. -/
def changedTarget : TypeOver Common.context where
  code := .id NativeWireData.dataType (NativeWireData.encode (.natural 7))
    (NativeWireData.encode (.natural 8))
  level := .sort Tower.zero
  universeWitness := .sort _
  formed := .idForm Common.wireType.formed Common.wireType.universeWitness
    (Common.result (.natural 7)).typed (Common.result (.natural 8)).typed

theorem changed_target_not_same_class :
    QType.mk changedTarget ≠ QType.mk (QuotientProducts.Controls.expectedType (.natural 7)) := by
  intro same
  have converted := ((QType.mk_eq_iff _ _).mp same).symm
  rw [QuotientProducts.Controls.expected_type_code] at converted
  exact changed_endpoint_not_convertible converted

theorem changed_target_type_not_meaning :
    ¬ (data common).ty source changedTarget.code
      (QType.mk (QuotientProducts.Controls.expectedType (.natural 7))) := by
  intro wrongMeaning
  exact changed_target_not_same_class
    (type_meaning_unique (assembly := common) (source := source)
      (QuotientInterpretation.type_meaning _ changedTarget) wrongMeaning)

/-- The exact retained application/proof value cannot be attached to the
altered native target. This does not assert falsity from a rejected proof. -/
theorem changed_proof_target_rejected :
    ¬ (data common).term source (applicationCode (.natural 7)) changedTarget.code
      (QType.mk (QuotientProducts.Controls.expectedType (.natural 7)))
      (TermFibre.mk (QuotientProducts.Controls.expectedReflexivity (.natural 7))) := by
  rintro ⟨annotation, annotationCode, _, _, represented, _⟩
  exact changed_target_type_not_meaning ⟨annotation, annotationCode, represented⟩

end

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProductExamples
