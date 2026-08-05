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
def rhoCostSemanticElaboratedOpenTheory : ElaboratedOpenTheory :=
  rhoCIGSLT.costSemanticElaboratedOpenTheory
    CostCanonicalLaws.rho_costTypedUnaryNormalizationLaws

/-- Rho's second Cost normalization cannot be defined solely from erased
compact syntax while agreeing with every proof-relevant elaboration. -/
theorem rhoCostOne_not_normalizationFactorsThroughCompactErasure
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    ¬ (CostIterationObstruction.rhoCostOne laws
      ).CostNormalizationFactorsThroughCompactErasure := by
  rw [CIGSLT.not_costNormalizationFactorsThroughCompactErasure_iff]
  exact CostIterationObstruction.rhoCostOne_not_compactCostNormalizationCoherent
    laws

/-- At rho's second Cost layer the projection from proof-relevant
elaborations to compact syntax is not faithful. -/
theorem rhoCostOne_not_costCompactErasureFaithful
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    ¬ (CostIterationObstruction.rhoCostOne laws
      ).CostCompactErasureFaithful := by
  intro faithful
  exact CostIterationObstruction.rhoCostOne_not_compactCostNormalizationCoherent
    laws
      ((CostIterationObstruction.rhoCostOne laws
        ).compactNormalizationCoherent_of_erasureFaithful faithful)

/-- Equivalently, rho Cost² has a genuinely nontrivial decoration fiber over
some checked compact term. -/
theorem rhoCostOne_not_all_elaborationFibersSubsingleton
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    ¬ (CostIterationObstruction.rhoCostOne laws
      ).CostElaborationFibersSubsingleton := by
  rw [← (CostIterationObstruction.rhoCostOne laws
    ).costCompactErasureFaithful_iff_fibersSubsingleton]
  exact rhoCostOne_not_costCompactErasureFaithful laws

/-- Even if the second-layer proof-relevant normalizer laws are discharged,
its semantic normalization cannot commute with one compact raw normalizer on
every elaboration.  The obstruction is representation-theoretic, not a
missing proof field in Cost₁. -/
theorem rhoCostOne_no_normalizationCommutingCompactification
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (semanticLaws : CostElaboratedNormalizationLaws
      (CostIterationObstruction.rhoCostOne laws)) :
    ¬ CostElaboratedCompactification semanticLaws.sectionData := by
  intro compactification
  exact CostIterationObstruction.rhoCostOne_not_compactCostNormalizationCoherent
    laws
      ((CostElaboratedCompactification.iff_compactCostNormalizationCoherent
        semanticLaws).mp compactification)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
