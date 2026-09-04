import Mettapedia.PLN.Bridges.GSLT.ProbabilityAssumptionDischarge
import Mettapedia.TypeTheory.CertificateGSLTDisplayedAnytimeEvidence

/-!
# Displayed finite evidence for probabilistic GSLT side conditions

The finite d-separation checker is an accelerator for one explicitly
supported Bayesian-network profile.  Acceptance and a checked derivation of
the encoded side condition travel together as proof-relevant staged evidence.
An open GSLT proof plan may close only after that pair is present.

This module does not turn source non-reuse into stochastic independence and
does not make the finite checker the meaning of independence.  Exactness of
the graph algorithm and exactness of the selected judgment encoding are
separate premises retained by the construction.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.GSLT.ProbabilityDisplayedDischarge

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Logic.DisplayedAnytimeEvidence
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.PLN.Bridges.GSLT.ProbabilityAssumptionDischarge
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.TypeTheory.CertificateGSLTDisplayedAnytimeEvidence

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {bn : BayesianNetwork V} [DecidableRel bn.graph.edges]
variable {definition : ValidatedCalculusLanguageDef}

/-- One finite-stage witness retains both executable graph acceptance and the
checked GSLT derivation supplied by the exact encoding. -/
structure CheckedRuleSideWitness
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn) where
  accepted :
    FiniteSideCondition.checkRuleInstance ruleInstance = true
  derivation : Derivation definition
    (encoding.toJudgmentEncodingAdequacy.encode
      (CompiledPlan.compile bn ruleInstance).sideCond)

/-- The finite graph authority as proof-relevant staged evidence.  Its fibre
is constant after discovery because both the Boolean receipt and checked
derivation remain valid at later observation stages. -/
def checkedRuleSideEvidence
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn) :
    StagedJudgmentEvidence encoding
      (CompiledPlan.compile bn ruleInstance).sideCond where
  EvidenceAt := fun _ => CheckedRuleSideWitness encoding ruleInstance
  persist _ witness := witness
  derive witness := witness.derivation

/-- Under the proved finite-graph hypotheses and the declared endpoint
profile, the staged side-condition authority is positively complete. -/
theorem checkedRuleSideEvidence_eventuallyComplete
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn)
    (acyclic : bn.graph.IsAcyclic)
    (irreflexive : ∀ vertex, ¬ bn.graph.edges vertex vertex)
    (supported :
      (FiniteSideCondition.ofRuleInstance ruleInstance).Supported) :
    (checkedRuleSideEvidence encoding ruleInstance).toEvidence.EventuallyComplete := by
  intro sideCondition
  have accepted :
      FiniteSideCondition.checkRuleInstance ruleInstance = true :=
    (FiniteSideCondition.checkRuleInstance_eq_true_iff
      ruleInstance acyclic irreflexive).2 ⟨sideCondition, supported⟩
  obtain ⟨derivation⟩ := encoding.derivation_complete
    (CompiledPlan.compile bn ruleInstance).sideCond sideCondition
  exact ⟨0, ⟨⟨accepted, derivation⟩⟩⟩

/-- The one compiled d-separation condition as an ordered GSLT context.
Keeping the singleton list explicit preserves the occurrence discipline used
by larger proof plans. -/
def checkedRuleContextEvidence
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn) :
    StagedContextEvidence encoding
      [(CompiledPlan.compile bn ruleInstance).sideCond] :=
  StagedContextEvidence.cons
    (checkedRuleSideEvidence encoding ruleInstance)
    StagedContextEvidence.nil

/-- The supported finite graph profile eventually supplies the complete
singleton evidence environment required by a compiled rule plan. -/
theorem checkedRuleContextEvidence_eventuallyComplete
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn)
    (acyclic : bn.graph.IsAcyclic)
    (irreflexive : ∀ vertex, ¬ bn.graph.edges vertex vertex)
    (supported :
      (FiniteSideCondition.ofRuleInstance ruleInstance).Supported) :
    (checkedRuleContextEvidence encoding ruleInstance).toEvidence.EventuallyComplete := by
  apply StagedContextEvidence.cons_eventuallyComplete
  · exact checkedRuleSideEvidence_eventuallyComplete
      encoding ruleInstance acyclic irreflexive supported
  · exact StagedContextEvidence.nil_eventuallyComplete

/-- A compiled probabilistic proof plan becomes a proof-relevant monotone
stream of closed derivations.  Until its side-condition evidence exists, its
thin observer does not accept. -/
def compiledPlanEvidence
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn) {goal : Pattern}
    (plan : OpenDerivation definition
      [encoding.toJudgmentEncodingAdequacy.encode
        (CompiledPlan.compile bn ruleInstance).sideCond] goal) :
    MonotoneEvidence (Nonempty (Derivation definition goal)) :=
  (checkedRuleContextEvidence encoding ruleInstance).dischargeEvidence plan

/-- If the semantic side condition holds in the supported finite profile,
the graph checker and exact judgment authority eventually expose a stage at
which this particular plan closes. -/
theorem compiledPlanEvidence_eventually_accepts
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn) {goal : Pattern}
    (plan : OpenDerivation definition
      [encoding.toJudgmentEncodingAdequacy.encode
        (CompiledPlan.compile bn ruleInstance).sideCond] goal)
    (acyclic : bn.graph.IsAcyclic)
    (irreflexive : ∀ vertex, ¬ bn.graph.edges vertex vertex)
    (supported :
      (FiniteSideCondition.ofRuleInstance ruleInstance).Supported)
    (sideCondition :
      (CompiledPlan.compile bn ruleInstance).sideCond.holds (bn := bn)) :
    ∃ stage,
      (compiledPlanEvidence encoding ruleInstance plan).toCertificate.acceptsAt
        stage := by
  apply StagedContextEvidence.dischargeEvidence_eventually_accepts_of_allMeaning
    (checkedRuleContextEvidence encoding ruleInstance) plan
    (checkedRuleContextEvidence_eventuallyComplete encoding ruleInstance
      acyclic irreflexive supported)
  intro condition member
  simp only [List.mem_singleton] at member
  exact member ▸ sideCondition

/-! ## Audited theorem crowns -/

#print axioms checkedRuleSideEvidence_eventuallyComplete
#print axioms checkedRuleContextEvidence_eventuallyComplete
#print axioms compiledPlanEvidence_eventually_accepts
#print axioms ProbabilityAssumptionDischarge.sourceNonreuse_cannot_discharge_eventIndependence

end Mettapedia.PLN.Bridges.GSLT.ProbabilityDisplayedDischarge
