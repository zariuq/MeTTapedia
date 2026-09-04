import Mettapedia.PLN.Bridges.GSLT.ProbabilityDisplayedDischarge
import Mettapedia.PLN.WorldModel.DisplayedConsequence

/-!
# Checked probability assumptions licensing world-model rules

A finite d-separation algorithm may accelerate discovery of one world-model
rule's side condition, but it does not define the rule or the underlying
probabilistic semantics.  This module composes the already proved boundaries:

* executable finite graph acceptance plus a checked CertificateGSLT
  derivation forms proof-relevant staged evidence;
* an explicit semantic adapter shows that the compiled d-separation
  condition is sufficient for the selected WM rule's side condition;
* the WM rule's own soundness theorem transports that witness to a query
  consequence or sort-indexed rewrite.

The resulting evidence fibre still contains the graph receipt and the
checked derivation.  Its thin observer says only that the rule is presently
licensed.  Source non-reuse remains a distinct provenance property and is
not accepted as a stochastic-independence certificate.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.GSLT.ProbabilityWorldModelDischarge

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Logic.DisplayedAnytimeEvidence
open Mettapedia.PLN.Bridges.GSLT.ProbabilityAssumptionDischarge
open Mettapedia.PLN.Bridges.GSLT.ProbabilityDisplayedDischarge
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.DisplayedConsequence
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.TypeTheory.CertificateGSLTDisplayedAnytimeEvidence

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {bn : BayesianNetwork V} [DecidableRel bn.graph.edges]
variable {definition : ValidatedCalculusLanguageDef}

/-! ## Untyped WM consequence rules -/

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- A compiled d-separation condition licenses a selected WM consequence
only through an explicit semantic implication to that rule's own side
condition. -/
def checkedConsequenceEvidence
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn)
    (rule : WMConsequenceRule State Query)
    (discharges :
      (CompiledPlan.compile bn ruleInstance).sideCond.holds (bn := bn) →
        rule.side) :
    MonotoneEvidence
      (WMStrengthLE (State := State) (Query := Query)
        rule.premise rule.conclusion) :=
  consequenceEvidence rule
    ((checkedRuleSideEvidence encoding ruleInstance).toEvidence.map discharges)

/-- The licensed consequence retains the complete graph-check and GSLT
evidence value at every stage. -/
@[simp] theorem checkedConsequenceEvidence_EvidenceAt
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn)
    (rule : WMConsequenceRule State Query)
    (discharges :
      (CompiledPlan.compile bn ruleInstance).sideCond.holds (bn := bn) →
        rule.side)
    (stage : Nat) :
    (checkedConsequenceEvidence encoding ruleInstance rule discharges).EvidenceAt
        stage =
      CheckedRuleSideWitness encoding ruleInstance :=
  rfl

/-- Under the supported finite graph profile, a true d-separation condition
eventually yields an actual license for the selected WM consequence. -/
theorem checkedConsequenceEvidence_eventually_accepts
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn)
    (rule : WMConsequenceRule State Query)
    (discharges :
      (CompiledPlan.compile bn ruleInstance).sideCond.holds (bn := bn) →
        rule.side)
    (acyclic : bn.graph.IsAcyclic)
    (irreflexive : ∀ vertex, ¬ bn.graph.edges vertex vertex)
    (supported :
      (FiniteSideCondition.ofRuleInstance ruleInstance).Supported)
    (sideCondition :
      (CompiledPlan.compile bn ruleInstance).sideCond.holds (bn := bn)) :
    ∃ stage,
      (checkedConsequenceEvidence encoding ruleInstance rule discharges).toCertificate.acceptsAt
        stage := by
  exact (checkedRuleSideEvidence_eventuallyComplete encoding ruleInstance
    acyclic irreflexive supported) sideCondition

/-! ## Sort-indexed higher-order WM rewrites -/

namespace HigherOrder

variable {HOState Srt : Type*} {HOQuery : Srt → Type*}
variable [EvidenceType HOState] [WorldModelSigma HOState Srt HOQuery]

/-- A finite probability-side checker may license a sort-indexed
higher-order WM rewrite without erasing it to first-order syntax. -/
def checkedRewriteEvidenceAt
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn)
    (rule : WorldModelSigma.WMRewriteRuleSigma HOState Srt HOQuery)
    (discharges :
      (CompiledPlan.compile bn ruleInstance).sideCond.holds (bn := bn) →
        rule.side)
    (world : HOState) :
    MonotoneEvidence
      (rule.derive world = WorldModelSigma.evidence world rule.conclusion) :=
  Mettapedia.PLN.WorldModel.DisplayedConsequence.HigherOrder.rewriteEvidenceAt rule
    ((checkedRuleSideEvidence encoding ruleInstance).toEvidence.map discharges)
    world

/-- The higher-order rewrite retains the same checked side-condition fibre. -/
@[simp] theorem checkedRewriteEvidenceAt_EvidenceAt
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn)
    (rule : WorldModelSigma.WMRewriteRuleSigma HOState Srt HOQuery)
    (discharges :
      (CompiledPlan.compile bn ruleInstance).sideCond.holds (bn := bn) →
        rule.side)
    (world : HOState) (stage : Nat) :
    (checkedRewriteEvidenceAt encoding ruleInstance rule discharges world).EvidenceAt
        stage =
      CheckedRuleSideWitness encoding ruleInstance :=
  rfl

end HigherOrder

/-! ## Audited theorem crowns -/

#print axioms checkedConsequenceEvidence_eventually_accepts
#print axioms HigherOrder.checkedRewriteEvidenceAt_EvidenceAt
#print axioms ProbabilityAssumptionDischarge.sourceNonreuse_cannot_discharge_eventIndependence

end Mettapedia.PLN.Bridges.GSLT.ProbabilityWorldModelDischarge
