import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.PracticalEthicsKernel
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.UpperShard

set_option autoImplicit false

/-!
# Meta-Ethics Kernel

This module adds the top-down side of the ethics stack:

- a descriptive base,
- a grounded normative base,
- bridge principles from descriptive sentences to ethical claims,
- admissible paradigm views,
- and a thin rendering seam into the practical-ethics scaffold.

The aim is not to formalize all of meta-ethics.  The aim is to provide one
small, typed kernel in which specific ethical theories and their practical
resolvers can later be situated.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Ethics
open Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology

universe u v

/-- Top-down descriptive sentences.

This starts deliberately small: the descriptive side is a plain world-indexed
formula.  If we later need richer structured descriptive theories, this alias is
the seam where they should be introduced. -/
abbrev DescriptiveSentence (World : Type u) :=
  Formula World

/-- A structured ethical claim together with the proof obligation showing that
its declared ground is genuinely witnessed. -/
structure GroundedStructuredClaim (World : Type u) (Agent : Type u) where
  claim : StructuredEthicalClaim World Agent
  grounded : claim.ground.Witnessed₀

/-- One top-down bridge principle: if the descriptive premises obtain, the
conclusion claim is licensed.  Soundness of the bridge requires that the
conclusion ground be witnessed. -/
structure BridgePrinciple (World : Type u) (Agent : Type u) where
  premises : DescriptiveSentence World
  conclusion : StructuredEthicalClaim World Agent

/-- A bridge principle is proof-carrying when its conclusion ground is
genuinely witnessed. -/
def BridgePrinciple.ProofCarrying
    {World : Type u} {Agent : Type u}
    (bp : BridgePrinciple World Agent) : Prop :=
  bp.conclusion.ground.Witnessed₀

theorem BridgePrinciple.proofCarrying_of_grounded
    {World : Type u} {Agent : Type u}
    (bp : BridgePrinciple World Agent)
    (h : bp.conclusion.ground.Witnessed₀) :
    bp.ProofCarrying :=
  h

/-- A normative base is the small set of primitive or accepted claims from
which a theory is allowed to reason.  Every core claim must be grounded. -/
structure NormativeBase (World : Type u) (Agent : Type u) where
  core : Set (StructuredEthicalClaim World Agent)
  grounded :
    ∀ ⦃claim : StructuredEthicalClaim World Agent⦄,
      claim ∈ core → claim.ground.Witnessed₀

theorem NormativeBase.mem_grounded
    {World : Type u} {Agent : Type u}
    (base : NormativeBase World Agent)
    {claim : StructuredEthicalClaim World Agent}
    (h : claim ∈ base.core) :
    claim.ground.Witnessed₀ :=
  base.grounded h

/-- Chalmers-style scrutability base for ethics:

- descriptive assumptions,
- a grounded normative core,
- and grounded bridge principles connecting the two.
-/
structure ScrutabilityBase (World : Type u) (Agent : Type u) where
  descriptiveAssumptions : Set (DescriptiveSentence World)
  normativeBase : NormativeBase World Agent
  bridgePrinciples : Set (BridgePrinciple World Agent)
  bridges_grounded :
    ∀ ⦃bp : BridgePrinciple World Agent⦄,
      bp ∈ bridgePrinciples → bp.ProofCarrying

theorem ScrutabilityBase.bridgeConclusion_grounded
    {World : Type u} {Agent : Type u}
    (base : ScrutabilityBase World Agent)
    {bp : BridgePrinciple World Agent}
    (h : bp ∈ base.bridgePrinciples) :
    bp.conclusion.ground.Witnessed₀ :=
  base.bridges_grounded h

/-- Minimal top-down conflict discipline.

This is intentionally abstract: the meta-ethical layer specifies which options
are admissible at a choice point, while lower practical layers may implement a
concrete resolver. -/
structure ConflictDiscipline (World : Type u) where
  admissible : ChoicePoint World → Formula World → Prop

/-- Computable companion to a conflict discipline at the practical-action seam.

The semantic discipline still speaks about formulas in a choice point.  The
computable companion is allowed to decide admissibility directly on actions, as
long as it agrees with the formula-level semantics induced by the practical
problem's `actionFormula`. -/
structure ComputableConflictDiscipline
    {World : Type u} {Agent : Type u} {Action : Type u}
    (problem : PracticalEthicalProblem World Agent Action) where
  toConflictDiscipline : ConflictDiscipline World
  admissibleAction : Action → Bool
  admissibleAction_spec :
    ∀ a : Action,
      admissibleAction a = true ↔
        toConflictDiscipline.admissible
          problem.conflict.choicePoint (problem.actionFormula a)

theorem ComputableConflictDiscipline.action_admissible_iff
    {World : Type u} {Agent : Type u} {Action : Type u}
    {problem : PracticalEthicalProblem World Agent Action}
    (discipline : ComputableConflictDiscipline problem)
    (a : Action) :
    discipline.admissibleAction a = true ↔
      discipline.toConflictDiscipline.admissible
        problem.conflict.choicePoint (problem.actionFormula a) :=
  discipline.admissibleAction_spec a

/-- A top-down ethical theory:

- a scrutability base,
- one primary paradigm,
- a set of admissible paradigm views,
- and a conflict discipline.

The paradigm set is intentionally pluralistic: the theory may have one primary
presentation while admitting faithful views in other paradigms. -/
structure MetaEthicalTheory (World : Type u) (Agent : Type u)
    extends ScrutabilityBase World Agent where
  primaryParadigm : EthicalParadigm
  admissibleParadigms : Set EthicalParadigm
  primary_mem_admissible : primaryParadigm ∈ admissibleParadigms
  conflictDiscipline : ConflictDiscipline World

theorem MetaEthicalTheory.primaryParadigm_admissible
    {World : Type u} {Agent : Type u}
    (theory : MetaEthicalTheory World Agent) :
    theory.primaryParadigm ∈ theory.admissibleParadigms :=
  theory.primary_mem_admissible

/-- Rendering of practical actions into the structured ethical-claim layer.

This is the key seam between the top-down theory side and the practical
resolver side. -/
structure ActionRendering
    (World : Type u) (Agent : Type u) (Action : Type u) where
  toClaim : Action → StructuredEthicalClaim World Agent

/-- Turn an action rendering into the practical bridge expected by the
practical-ethics kernel. -/
def ActionRendering.toPracticalBridge
    {World : Type u} {Agent : Type u} {Action : Type u} {Atom : Type v}
    (rendering : ActionRendering World Agent Action)
    (encoder : StructuredEthicsQueryEncoder World Agent Atom) :
    PracticalEthicsBridge World Agent Action Atom where
  toClaim := rendering.toClaim
  encoder := encoder

@[simp] theorem ActionRendering.toPracticalBridge_actionQuery
    {World : Type u} {Agent : Type u} {Action : Type u} {Atom : Type v}
    (rendering : ActionRendering World Agent Action)
    (encoder : StructuredEthicsQueryEncoder World Agent Atom)
    (a : Action) :
    (rendering.toPracticalBridge encoder).actionQuery a =
      (rendering.toClaim a).toQuery encoder := by
  rfl

/-- Lift the kernel's deontic/value equivalence through the practical
action-rendering seam when the practical bridge uses the staged legacy-lowering
encoder and the labeler preserves the deontic/value translation. -/
theorem ActionRendering.toPracticalBridge_actionQuery_deontic_toAxiological_ofLegacy_eq_of_aligned
    {World : Type u} {Agent : Type u} {Action : Type u} {Label : Type v}
    {Atom : Type*}
    (rendering : ActionRendering World Agent Action)
    (labeler : StructuredClaimLabeler World Agent Label)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (hEncAlign : enc.DeonticValueAligned)
    (hLabelAlign : labeler.DeonticValueAligned)
    (a : Action)
    (subject : Agent) (ground : EthicalGround Agent) (role : EthicalRole)
    (tag : DeonticAttribute) (φ : Formula World)
    (hClaim :
      rendering.toClaim a =
        ({ subject := subject
           content := .propositional φ
           presentation := .deontic tag
           ground := ground
           role := role } : StructuredEthicalClaim World Agent)) :
    (rendering.toPracticalBridge (StructuredEthicsQueryEncoder.ofLegacy labeler enc)).actionQuery a =
      ({ subject := subject
         content := .propositional φ
         presentation := .axiological (deonticToMoralValue tag)
         ground := ground
         role := role } : StructuredEthicalClaim World Agent).toQuery
        (StructuredEthicsQueryEncoder.ofLegacy labeler enc) := by
  rw [ActionRendering.toPracticalBridge_actionQuery, hClaim]
  simpa [ActionRendering.toPracticalBridge_actionQuery] using
    StructuredEthicalClaim.propositional_deontic_toAxiological_toQuery_ofLegacy_eq_of_aligned
      labeler enc hEncAlign hLabelAlign subject ground role tag φ

/-- Package a top-down theory together with its action rendering, ready to be
consumed by a practical resolver. -/
structure TheoryGuidedPracticalInterface
    (World : Type u) (Agent : Type u) (Action : Type u) where
  theory : MetaEthicalTheory World Agent
  rendering : ActionRendering World Agent Action

def TheoryGuidedPracticalInterface.toPracticalBridge
    {World : Type u} {Agent : Type u} {Action : Type u} {Atom : Type v}
    (iface : TheoryGuidedPracticalInterface World Agent Action)
    (encoder : StructuredEthicsQueryEncoder World Agent Atom) :
    PracticalEthicsBridge World Agent Action Atom :=
  iface.rendering.toPracticalBridge encoder

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
