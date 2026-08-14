import Mettapedia.GSLT.LanguageDef.CostElaboratedSection
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction

/-!
# Rho Cost² does not factor through compact erasure

The proof-relevant Cost² counterexample is restated at the generic elaborated
carrier boundary.  It shows that no normalizer on compact syntax can reproduce
the normalized result of every valid second-layer elaboration.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open LanguageDefContinuedInteraction

/-! ## The first rho Cost layer on retained syntax -/

/-- Rho's selected-colour generator theorem makes every fully witnessed
structural Cost transport erase to an authored equation path in the single
generated Cost language. -/
theorem rhoCostStructuralTransportSound :
    rhoCIGSLT.CostStructuralTransportSound rhoCIGSLT.costStaticPlanLift :=
  rhoCIGSLT.costStructuralTransportSound_of_mappedGeneratorFiberAction
    rhoCIGSLT.costStaticPlanLift
    CostCanonicalLaws.rho_costStaticMappedGeneratorFiberAction

/-- The first rho Cost layer has an exact canonical section on retained
proof-relevant syntax.  Declaration identity, colour, collection choice, and
finite boundary evidence remain in the carrier; erasure targets the generated
Cost `IGSLT` and introduces no second equation authority. -/
def rhoCostSemanticElaboratedOpenTheory : ReflectiveElaboratedOpenTheory :=
  rhoCIGSLT.costSemanticElaboratedOpenTheory
    CostCanonicalLaws.rho_costTypedUnaryNormalizationLaws

/-! ## Normalizer-parameterized second-layer negatives -/

/-- Any lawful first-layer normalizer retaining rho's empty-parallel
representative fails to factor every second-layer elaboration through compact
erasure. -/
theorem rhoCostOneFor_not_normalizationFactorsThroughCompactErasure
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ¬ configuration.source.CostNormalizationFactorsThroughCompactErasure := by
  rw [CIGSLT.not_costNormalizationFactorsThroughCompactErasure_iff]
  exact
    CostIterationObstruction.rhoCostOneFor_not_compactCostNormalizationCoherent
      configuration representative

/-- The corresponding compact-erasure map cannot be faithful. -/
theorem rhoCostOneFor_not_costCompactErasureFaithful
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ¬ configuration.source.CostCompactErasureFaithful := by
  intro faithful
  exact
    CostIterationObstruction.rhoCostOneFor_not_compactCostNormalizationCoherent
      configuration representative
      (configuration.source.compactNormalizationCoherent_of_erasureFaithful
        faithful)

/-- Equivalently, some second-layer decoration fibre is nontrivial. -/
theorem rhoCostOneFor_not_all_elaborationFibersSubsingleton
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ¬ configuration.source.CostElaborationFibersSubsingleton := by
  rw [← configuration.source.costCompactErasureFaithful_iff_fibersSubsingleton]
  exact rhoCostOneFor_not_costCompactErasureFaithful configuration
    representative

/-- Even a completed proof-relevant second-layer normalizer cannot commute
with one compactification on every elaboration of this source. -/
theorem rhoCostOneFor_no_normalizationCommutingCompactification
    (configuration : CostIterationObstruction.RhoCostOneConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration)
    (semanticLaws : CostElaboratedNormalizationLaws configuration.source) :
    ¬ CostReferenceElaboratedCompactification semanticLaws.sectionData := by
  intro compactification
  exact
    CostIterationObstruction.rhoCostOneFor_not_compactCostNormalizationCoherent
      configuration representative
      ((CostReferenceElaboratedCompactification.iff_compactCostNormalizationCoherent
        semanticLaws).mp compactification)

/-- Rho's second Cost normalization cannot be defined solely from erased
compact syntax while agreeing with every proof-relevant elaboration. -/
theorem rhoReferenceCostOne_not_normalizationFactorsThroughCompactErasure
    (laws : CIGSLT.CostReferenceOneObjectLaws rhoCIGSLT) :
    ¬ (CostIterationObstruction.rhoReferenceCostOne laws
      ).CostNormalizationFactorsThroughCompactErasure := by
  rw [CIGSLT.not_costNormalizationFactorsThroughCompactErasure_iff]
  exact CostIterationObstruction.rhoReferenceCostOne_not_compactCostNormalizationCoherent
    laws

/-- At rho's second Cost layer the projection from proof-relevant
elaborations to compact syntax is not faithful. -/
theorem rhoReferenceCostOne_not_costCompactErasureFaithful
    (laws : CIGSLT.CostReferenceOneObjectLaws rhoCIGSLT) :
    ¬ (CostIterationObstruction.rhoReferenceCostOne laws
      ).CostCompactErasureFaithful := by
  intro faithful
  exact CostIterationObstruction.rhoReferenceCostOne_not_compactCostNormalizationCoherent
    laws
      ((CostIterationObstruction.rhoReferenceCostOne laws
        ).compactNormalizationCoherent_of_erasureFaithful faithful)

/-- Equivalently, rho Cost² has a genuinely nontrivial decoration fiber over
some checked compact term. -/
theorem rhoReferenceCostOne_not_all_elaborationFibersSubsingleton
    (laws : CIGSLT.CostReferenceOneObjectLaws rhoCIGSLT) :
    ¬ (CostIterationObstruction.rhoReferenceCostOne laws
      ).CostElaborationFibersSubsingleton := by
  rw [← (CostIterationObstruction.rhoReferenceCostOne laws
    ).costCompactErasureFaithful_iff_fibersSubsingleton]
  exact rhoReferenceCostOne_not_costCompactErasureFaithful laws

/-- Even if the second-layer proof-relevant normalizer laws are discharged,
its semantic normalization cannot commute with the compact reference normalizer on
every elaboration.  The obstruction is representation-theoretic, not a
missing proof field in Cost₁. -/
theorem rhoReferenceCostOne_no_normalizationCommutingCompactification
    (laws : CIGSLT.CostReferenceOneObjectLaws rhoCIGSLT)
    (semanticLaws : CostElaboratedNormalizationLaws
      (CostIterationObstruction.rhoReferenceCostOne laws)) :
    ¬ CostReferenceElaboratedCompactification semanticLaws.sectionData := by
  intro compactification
  exact CostIterationObstruction.rhoReferenceCostOne_not_compactCostNormalizationCoherent
    laws
      ((CostReferenceElaboratedCompactification.iff_compactCostNormalizationCoherent
        semanticLaws).mp compactification)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
