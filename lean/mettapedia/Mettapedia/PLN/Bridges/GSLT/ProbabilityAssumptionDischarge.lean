import Mettapedia.Evidence.SourceScopeProbabilityBoundary
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenDischarge
import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
import Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

/-!
# Probability side conditions as dischargeable GSLT obligations

Compiled probabilistic rules may be useful proof plans before their
independence conditions have been established.  They must not become closed
proofs merely because their source ledgers are disjoint or because a search
procedure assigned them a high score.

This module connects three existing boundaries:

* a Bayesian-network compilation exposes a `DSeparationCond`;
* an exact CertificateGSLT judgment encoding supplies checked evidence for
  precisely those conditions that hold;
* open-derivation discharge closes the surrounding proof plan only after that
  evidence is supplied at every ordered occurrence.

The adapter is deliberately conditional on an exact d-separation encoding.
It does not pretend that such a native checker has already been selected.
The negative control reuses the correlated-packet model to show why
source-disjoint provenance cannot implement this semantic authority.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.GSLT.ProbabilityAssumptionDischarge

open MeasureTheory ProbabilityTheory
open Mettapedia.Evidence
open Mettapedia.Evidence.SourceScopeProbabilityBoundary
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
open Mettapedia.ProbabilityTheory.BayesianNetworks

namespace FiniteSideCondition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Forget the finite presentation while preserving the three endpoint sets
as the set-valued condition used by the PLN/BN compilation theory. -/
def toDSeparationCond
    (condition : FiniteDSeparation.Condition V) : DSeparationCond V where
  X := condition.X
  Y := condition.Y
  Z := condition.Z

omit [Fintype V] in
/-- The finite and set-valued presentations state the same d-separation
judgment. -/
theorem meaning_iff_holds (bn : BayesianNetwork V)
    (condition : FiniteDSeparation.Condition V) :
    condition.Meaning bn.graph ↔
      (toDSeparationCond condition).holds (bn := bn) := by
  constructor
  · rintro ⟨compatible, separated⟩
    refine ⟨?_, separated⟩
    intro vertex overlap
    change vertex ∈ condition.Z
    apply compatible
    exact Finset.mem_inter.mpr ⟨overlap.1, overlap.2⟩
  · rintro ⟨compatible, separated⟩
    refine ⟨?_, separated⟩
    intro vertex overlap
    rcases Finset.mem_inter.mp overlap with ⟨vertexInX, vertexInY⟩
    exact compatible ⟨vertexInX, vertexInY⟩

/-- Retain the finite data underlying a compiled rule instance. -/
def ofRuleInstance {bn : BayesianNetwork V}
    (ruleInstance : RuleInstance bn) : FiniteDSeparation.Condition V :=
  match ruleInstance.kind with
  | .deduction =>
      ⟨{ruleInstance.A}, {ruleInstance.C}, {ruleInstance.B}⟩
  | .induction =>
      ⟨{ruleInstance.A}, {ruleInstance.C}, {ruleInstance.B}⟩
  | .abduction => ⟨{ruleInstance.A}, {ruleInstance.C}, ∅⟩

omit [Fintype V] [DecidableEq V] in
/-- Finite retention commutes exactly with the existing PLN/BN compiler. -/
theorem toDSeparationCond_ofRuleInstance {bn : BayesianNetwork V}
    (ruleInstance : RuleInstance bn) :
    toDSeparationCond (ofRuleInstance ruleInstance) =
      (CompiledPlan.compile bn ruleInstance).sideCond := by
  cases ruleInstance with
  | mk kind A B C valA valB valC =>
      cases kind <;>
        simp [toDSeparationCond, ofRuleInstance, CompiledPlan.compile,
          CompiledPlan.deductionSide, CompiledPlan.inductionSide,
          CompiledPlan.abductionSide]

/-- Execute the proved finite d-separation authority for one compiled rule
instance. -/
def checkRuleInstance {bn : BayesianNetwork V}
    [DecidableRel bn.graph.edges]
    (ruleInstance : RuleInstance bn) : Bool :=
  FiniteDSeparation.check bn.graph (ofRuleInstance ruleInstance)

/-- The executable result is exactly the existing compiled side condition,
within the explicitly supported finite endpoint profile. -/
theorem checkRuleInstance_eq_true_iff {bn : BayesianNetwork V}
    [DecidableRel bn.graph.edges] (ruleInstance : RuleInstance bn)
    (acyclic : bn.graph.IsAcyclic)
    (irreflexive : ∀ vertex, ¬ bn.graph.edges vertex vertex) :
    checkRuleInstance ruleInstance = true ↔
      (CompiledPlan.compile bn ruleInstance).sideCond.holds (bn := bn) ∧
        (ofRuleInstance ruleInstance).Supported := by
  rw [checkRuleInstance,
    FiniteDSeparation.check_eq_true_iff bn.graph
      (ofRuleInstance ruleInstance)
      acyclic irreflexive]
  constructor
  · rintro ⟨meaning, supported⟩
    refine ⟨?_, supported⟩
    rw [← toDSeparationCond_ofRuleInstance ruleInstance]
    exact (meaning_iff_holds bn (ofRuleInstance ruleInstance)).1 meaning
  · rintro ⟨holds, supported⟩
    refine ⟨?_, supported⟩
    apply (meaning_iff_holds bn (ofRuleInstance ruleInstance)).2
    rw [toDSeparationCond_ofRuleInstance ruleInstance]
    exact holds

end FiniteSideCondition

/-- An exact CertificateGSLT presentation of the d-separation judgments for
one Bayesian network.  Soundness prevents false structural certificates;
completeness makes every true condition available for plan discharge. -/
abbrev DSeparationExactEncoding {V : Type*}
    (bn : BayesianNetwork V)
    (definition : ValidatedCalculusLanguageDef) :=
  ExactJudgmentEncoding (DSeparationCond V)
    (fun condition => condition.holds (bn := bn)) definition

/-- The exact encoded context of the one side condition emitted by a
compiled PLN/BN plan. -/
def compiledSideConditionContext {V : Type*} {bn : BayesianNetwork V}
    {definition : ValidatedCalculusLanguageDef}
    (encoding : DSeparationExactEncoding bn definition)
    (plan : CompiledPlan bn) : List Pattern :=
  [encoding.toJudgmentEncodingAdequacy.encode plan.sideCond]

/-- A compiled plan with a proved d-separation condition closes its open
CertificateGSLT proof.  The proof of `holds` is converted to checked evidence
through the exact encoding; it is not inserted as an unchecked premise. -/
theorem closeCompiledPlan {V : Type*} {bn : BayesianNetwork V}
    {definition : ValidatedCalculusLanguageDef}
    (encoding : DSeparationExactEncoding bn definition)
    (compiled : CompiledPlan bn) {goal : Pattern}
    (plan : OpenDerivation definition
      (compiledSideConditionContext encoding compiled) goal)
    (sideCondition : compiled.sideCond.holds (bn := bn)) :
    Nonempty (Derivation definition goal) := by
  apply encoding.discharge_of_all [compiled.sideCond] plan
  intro condition member
  simp only [List.mem_singleton] at member
  exact member ▸ sideCondition

/-- For a finite compiled rule instance, acceptance by the exact graph
authority supplies the semantic premise needed to close the corresponding
open CertificateGSLT plan. -/
theorem closeCheckedRuleInstance {V : Type*} [Fintype V] [DecidableEq V]
    {bn : BayesianNetwork V} [DecidableRel bn.graph.edges]
    (acyclic : bn.graph.IsAcyclic)
    (irreflexive : ∀ vertex, ¬ bn.graph.edges vertex vertex)
    {definition : ValidatedCalculusLanguageDef}
    (encoding : DSeparationExactEncoding bn definition)
    (ruleInstance : RuleInstance bn) {goal : Pattern}
    (plan : OpenDerivation definition
      (compiledSideConditionContext encoding
        (CompiledPlan.compile bn ruleInstance)) goal)
    (accepted :
      FiniteSideCondition.checkRuleInstance ruleInstance = true) :
    Nonempty (Derivation definition goal) := by
  apply closeCompiledPlan encoding (CompiledPlan.compile bn ruleInstance) plan
  exact (FiniteSideCondition.checkRuleInstance_eq_true_iff
    ruleInstance acyclic irreflexive).1 accepted |>.1

/-! ## A concrete positive structural control -/

namespace ChainControl

open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

instance : DecidableRel chainBN.graph.edges := by
  intro source target
  dsimp [chainBN, chainGraph]
  infer_instance

/-- Finite presentation of the chain deduction side condition. -/
def finiteDeductionSide : FiniteDSeparation.Condition Three :=
  ⟨{Three.A}, {Three.C}, {Three.B}⟩

/-- The same endpoints without conditioning provide a negative control. -/
def finiteUnblockedSide : FiniteDSeparation.Condition Three :=
  ⟨{Three.A}, {Three.C}, ∅⟩

/-- The finite graph authority accepts the structurally blocked chain. -/
theorem finiteDeductionSide_check :
    FiniteDSeparation.check chainBN.graph finiteDeductionSide = true := by
  decide

/-- Removing the conditioning vertex changes the result. -/
theorem finiteUnblockedSide_check :
    FiniteDSeparation.check chainBN.graph finiteUnblockedSide = false := by
  decide

/-- Forgetting finite storage recovers the existing set-valued PLN
condition exactly. -/
theorem finiteDeductionSide_erases :
    FiniteSideCondition.toDSeparationCond finiteDeductionSide =
      CompiledPlan.deductionSide Three.A Three.B Three.C := by
  simp [FiniteSideCondition.toDSeparationCond, finiteDeductionSide,
    CompiledPlan.deductionSide]

/-- The canonical chain `A → B → C` satisfies the deduction plan's actual
structural side condition. -/
theorem deductionSide_holds :
    (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN) := by
  refine ⟨?_, chain_dsepFull_A_C_given_B⟩
  intro vertex overlap
  simp [CompiledPlan.deductionSide] at overlap

/-- Consequently any exact GSLT encoding of chain d-separation can close a
plan conditional on this side condition.  The theorem remains polymorphic in
the calculus: no particular runtime representation is privileged. -/
theorem deductionPlan_closes
    {definition : ValidatedCalculusLanguageDef}
    (encoding : DSeparationExactEncoding chainBN definition)
    {goal : Pattern}
    (plan : OpenDerivation definition
      [encoding.toJudgmentEncodingAdequacy.encode
        (CompiledPlan.deductionSide Three.A Three.B Three.C)] goal) :
    Nonempty (Derivation definition goal) := by
  apply encoding.discharge_of_all
    [CompiledPlan.deductionSide Three.A Three.B Three.C] plan
  intro condition member
  simp only [List.mem_singleton] at member
  exact member ▸ deductionSide_holds

end ChainControl

/-! ## Provenance is not a probability discharger -/

/-- Negative control: a generic rule replacing semantic event independence
with source non-reuse is refuted by the correlated-packet model. -/
theorem sourceNonreuse_cannot_discharge_eventIndependence :
    ¬ (SourceScoped.Independent correlatedLeft correlatedRight →
      _root_.ProbabilityTheory.IndepSet correlatedLeft.event
        correlatedRight.event fairWorldMeasure) := by
  intro purportedBridge
  exact correlated_packets_not_stochasticallyIndependent
    (purportedBridge correlated_packets_sourceIndependent)

end Mettapedia.PLN.Bridges.GSLT.ProbabilityAssumptionDischarge
