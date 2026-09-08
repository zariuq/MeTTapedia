import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.GSLT.Dynamics.ProofRelevantRelationProtocol
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLTBridge

/-!
# Rho reduction as a dependent protocol

The closed rho GSLT uses an modulo-equations proposition-valued step
relation.  The underlying rho reduction is Type-valued and can retain a
specific reduction receipt.  This module exposes that distinction by giving
the established closed rho system a complete proof-relevant interaction
presentation and its canonical response-indexed protocol polynomial.

The protocol endpoint relation and the established GSLT step relation agree
exactly.  Their equation structures do not: the protocol uses literal state
equality, while the established GSLT identifies structurally congruent closed
processes through canonical representatives.  Thus operational exactness does
not imply static-equation equivalence.

The closed communication and inert dropped-quotation examples are inherited
from the existing rho development.  No second process syntax or reduction
relation is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionProtocolComparison

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.ProofRelevantRelationProtocol
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-! ## Exact occurrences over the established modulo-equations carrier -/

/-- One modulo-equations rho step together with a concrete Type-valued raw
reduction receipt for its selected middle edge. -/
structure RewriteOccurrence (source target : RhoProcess) where
  redex : RhoProcess
  contractum : RhoProcess
  sourceEquation : rhoProcessEquations.r source redex
  derivedStep : rhoRewriteSystem.Reduces redex contractum
  rawReceipt : Reduces redex.1 contractum.1
  targetEquation : rhoProcessEquations.r contractum target

namespace RewriteOccurrence

/-- Forget occurrence data to the established rho GSLT step. -/
def toStep {source target : RhoProcess}
    (occurrence : RewriteOccurrence source target) :
    rhoLanguageDefGSLT.Step source target :=
  ⟨occurrence.redex, occurrence.contractum,
    occurrence.sourceEquation, occurrence.derivedStep,
    occurrence.targetEquation⟩

/-- Every established GSLT step has at least one concrete raw receipt.  The
result is propositionally truncated; consumers needing receipt identity use
`RewriteOccurrence` itself. -/
theorem complete {source target : RhoProcess}
    (step : rhoLanguageDefGSLT.Step source target) :
    Nonempty (RewriteOccurrence source target) := by
  obtain ⟨redex, contractum, sourceEquation, derivedStep,
    targetEquation⟩ := step
  obtain ⟨rawReceipt⟩ := rhoRewriteSystem_reduces_sound derivedStep
  exact ⟨⟨redex, contractum, sourceEquation, derivedStep, rawReceipt,
    targetEquation⟩⟩

end RewriteOccurrence

/-- Complete occurrence-retaining interaction semantics for the established
rho GSLT. -/
def occurrenceInteraction : InteractionPresentation rhoLanguageDefGSLT where
  Site := Unit
  Event := fun _ source target => RewriteOccurrence source target
  sound := RewriteOccurrence.toStep

theorem occurrenceInteraction_complete : occurrenceInteraction.Complete := by
  intro source target step
  obtain ⟨occurrence⟩ := RewriteOccurrence.complete step
  exact ⟨⟨(), occurrence⟩⟩

/-- Enabled events of the direct rho interaction presentation are exactly
target-indexed rewrite occurrences. -/
def occurrenceEventEquiv (source : RhoProcess) :
    occurrenceInteraction.Enabled source ≃
      Outgoing RewriteOccurrence source where
  toFun event := ⟨event.target, event.evidence⟩
  invFun outgoing :=
    { site := ()
      target := outgoing.1
      evidence := outgoing.2 }
  left_inv := by
    rintro ⟨site, target, occurrence⟩
    cases site
    rfl
  right_inv := by
    rintro ⟨target, occurrence⟩
    rfl

/-! ## Canonical indexed-polynomial protocol -/

/-- The canonical dependent protocol of exact rho rewrite occurrences. -/
abbrev rhoProtocol := protocol RewriteOccurrence

/-- Its endpoint-only GSLT uses literal equality as its static equation. -/
abbrev rhoProtocolSystem := lts rhoProtocol

/-- The generic protocol interaction and the direct rho interaction retain
exactly the same enabled occurrences. -/
def protocolOccurrenceEquiv (source : RhoProcess) :
    (interaction rhoProtocol).Enabled source ≃
      occurrenceInteraction.Enabled source :=
  (eventEquiv RewriteOccurrence source).trans
    (occurrenceEventEquiv source).symm

/-- The protocol endpoint relation and the established modulo-equations rho
GSLT step relation agree for every pair of closed processes. -/
theorem protocol_step_iff_languageDef_step
    {source target : RhoProcess} :
    rhoProtocolSystem.Step source target <->
      rhoLanguageDefGSLT.Step source target := by
  constructor
  · intro protocolStep
    obtain ⟨occurrence⟩ :=
      (lts_step_iff RewriteOccurrence).1 protocolStep
    exact occurrence.toStep
  · intro languageStep
    exact (lts_step_iff RewriteOccurrence).2
      (RewriteOccurrence.complete languageStep)

/-- Literal protocol equations map soundly into the richer established rho
equations, and exact endpoint steps map by the preceding theorem. -/
def protocolToLanguageDef :
    OperationalTranslation rhoProtocolSystem rhoLanguageDefGSLT where
  mapTerm := id
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := fun step => protocol_step_iff_languageDef_step.1 step

/-! ## Existing rho controls through the protocol face -/

/-- The known closed COMM step supplies one concrete occurrence. -/
noncomputable def closedCommOccurrence :
    RewriteOccurrence closedCommSource closedCommTarget where
  redex := closedCommSource
  contractum := closedCommTarget
  sourceEquation := rfl
  derivedStep := closedCommSource_reduces_closedCommTarget
  rawReceipt := Classical.choice
    (rhoRewriteSystem_reduces_sound closedCommSource_reduces_closedCommTarget)
  targetEquation := rfl

noncomputable def closedCommOutgoing :
    Outgoing RewriteOccurrence closedCommSource :=
  ⟨closedCommTarget, closedCommOccurrence⟩

noncomputable def closedCommEvent :
    (interaction rhoProtocol).Enabled closedCommSource :=
  eventOfOutgoing RewriteOccurrence closedCommOutgoing

/-- A complete unit-valued handler exists at the closed communication source
and is indexed by every exact outgoing occurrence. -/
noncomputable def closedCommRound :
    OneRound rhoProtocol (fun _ => PUnit) closedCommSource :=
  roundOf RewriteOccurrence closedCommOutgoing (fun _ => PUnit.unit)

theorem closedComm_protocol_control :
    closedCommEvent.target = closedCommTarget /\
      rhoProtocolSystem.Step closedCommSource closedCommTarget /\
      Nonempty (OneRound rhoProtocol (fun _ => PUnit) closedCommSource) :=
  ⟨rfl, closedCommEvent.step, ⟨closedCommRound⟩⟩

/-- The existing inert free Drop has no enabled protocol event. -/
theorem closedFreeDrop_has_no_protocol_event :
    ¬ Nonempty ((interaction rhoProtocol).Enabled closedFreeDrop) := by
  rintro ⟨event⟩
  let outgoing := eventEquiv RewriteOccurrence closedFreeDrop event
  exact closedFreeDrop_irreducible_in_gslt outgoing.1
    outgoing.2.toStep

/-- The two existing closed process representatives are syntactically
different even though the established rho equations identify them. -/
theorem closedCommTarget_ne_closedNil : closedCommTarget ≠ closedNil := by
  intro equalTerms
  have equalPatterns := congrArg Subtype.val equalTerms
  simp [closedCommTarget, closedNil] at equalPatterns

/-- Exact step correspondence does not collapse the static-equation choice.
The established GSLT equates a singleton parallel process with its component;
the literal-equation protocol GSLT does not. -/
theorem operational_exactness_does_not_imply_equation_reflection :
    (forall source target,
      rhoProtocolSystem.Step source target <->
        rhoLanguageDefGSLT.Step source target) /\
      rhoLanguageDefGSLT.Equiv closedCommTarget closedNil /\
      ¬ rhoProtocolSystem.Equiv closedCommTarget closedNil := by
  refine ⟨fun _ _ => protocol_step_iff_languageDef_step,
    closedParallelSingleton_equivalent_nil, ?_⟩
  exact closedCommTarget_ne_closedNil

/-! ## Axiom audit -/

#print axioms RewriteOccurrence.toStep
#print axioms RewriteOccurrence.complete
#print axioms occurrenceInteraction_complete
#print axioms occurrenceEventEquiv
#print axioms protocolOccurrenceEquiv
#print axioms protocol_step_iff_languageDef_step
#print axioms protocolToLanguageDef
#print axioms closedComm_protocol_control
#print axioms closedFreeDrop_has_no_protocol_event
#print axioms operational_exactness_does_not_imply_equation_reflection

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionProtocolComparison
