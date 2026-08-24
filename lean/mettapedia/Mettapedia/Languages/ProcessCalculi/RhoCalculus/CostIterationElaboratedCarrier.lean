import Mettapedia.GSLT.LanguageDef.CostElaboratedSection
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction

/-!
# Rho cost-layer iteration does not factor through compact erasure

The proof-relevant cost-layer iteration counterexample is restated at the generic elaborated
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
theorem rhoCostLayerFor_not_normalizationFactorsThroughCompactErasure
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ¬ configuration.source.CostNormalizationFactorsThroughCompactErasure := by
  rw [CIGSLT.not_costNormalizationFactorsThroughCompactErasure_iff]
  exact
    CostIterationObstruction.rhoCostLayerFor_not_compactCostNormalizationCoherent
      configuration representative

/-- The corresponding compact-erasure map cannot be faithful. -/
theorem rhoCostLayerFor_not_costCompactErasureFaithful
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ¬ configuration.source.CostCompactErasureFaithful := by
  intro faithful
  exact
    CostIterationObstruction.rhoCostLayerFor_not_compactCostNormalizationCoherent
      configuration representative
      (configuration.source.compactNormalizationCoherent_of_erasureFaithful
        faithful)

/-- Equivalently, some second-layer decoration fibre is nontrivial. -/
theorem rhoCostLayerFor_not_all_elaborationFibersSubsingleton
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ¬ configuration.source.CostElaborationFibersSubsingleton := by
  rw [← configuration.source.costCompactErasureFaithful_iff_fibersSubsingleton]
  exact rhoCostLayerFor_not_costCompactErasureFaithful configuration
    representative

/-- Even a completed proof-relevant second-layer normalizer cannot commute
with one compactification on every elaboration of this source. -/
theorem rhoCostLayerFor_no_normalizationCommutingCompactification
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration)
    (semanticLaws : Cost.ElaboratedSection.Laws configuration.source) :
    ¬ Cost.SemanticSection.ReferenceErasureSemiconj
      semanticLaws.toElaboratedSection := by
  intro compactification
  exact
    CostIterationObstruction.rhoCostLayerFor_not_compactCostNormalizationCoherent
      configuration representative
      ((Cost.SemanticSection.ReferenceErasureSemiconj.iff_compactCostNormalizationCoherent
        semanticLaws).mp compactification)

/-- Rho's second Cost normalization cannot be defined solely from erased
compact syntax while agreeing with every proof-relevant elaboration. -/
theorem rhoReferenceCostLayer_not_normalizationFactorsThroughCompactErasure
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) :
    ¬ (CostIterationObstruction.rhoReferenceCostLayer laws
      ).CostNormalizationFactorsThroughCompactErasure := by
  rw [CIGSLT.not_costNormalizationFactorsThroughCompactErasure_iff]
  exact CostIterationObstruction.rhoReferenceCostLayer_not_compactCostNormalizationCoherent
    laws

/-- At rho's second Cost layer the projection from proof-relevant
elaborations to compact syntax is not faithful. -/
theorem rhoReferenceCostLayer_not_costCompactErasureFaithful
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) :
    ¬ (CostIterationObstruction.rhoReferenceCostLayer laws
      ).CostCompactErasureFaithful := by
  intro faithful
  exact CostIterationObstruction.rhoReferenceCostLayer_not_compactCostNormalizationCoherent
    laws
      ((CostIterationObstruction.rhoReferenceCostLayer laws
        ).compactNormalizationCoherent_of_erasureFaithful faithful)

/-- Equivalently, rho cost-layer iteration has a genuinely nontrivial decoration fiber over
some checked compact term. -/
theorem rhoReferenceCostLayer_not_all_elaborationFibersSubsingleton
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) :
    ¬ (CostIterationObstruction.rhoReferenceCostLayer laws
      ).CostElaborationFibersSubsingleton := by
  rw [← (CostIterationObstruction.rhoReferenceCostLayer laws
    ).costCompactErasureFaithful_iff_fibersSubsingleton]
  exact rhoReferenceCostLayer_not_costCompactErasureFaithful laws

/-- Even if the second-layer proof-relevant normalizer laws are discharged,
its semantic normalization cannot commute with the compact reference normalizer on
every elaboration.  The obstruction is representation-theoretic, not a
missing proof field in cost layer. -/
theorem rhoReferenceCostLayer_no_normalizationCommutingCompactification
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT)
    (semanticLaws : Cost.ElaboratedSection.Laws
      (CostIterationObstruction.rhoReferenceCostLayer laws)) :
    ¬ Cost.SemanticSection.ReferenceErasureSemiconj
      semanticLaws.toElaboratedSection := by
  intro compactification
  exact CostIterationObstruction.rhoReferenceCostLayer_not_compactCostNormalizationCoherent
    laws
      ((Cost.SemanticSection.ReferenceErasureSemiconj.iff_compactCostNormalizationCoherent
        semanticLaws).mp compactification)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
