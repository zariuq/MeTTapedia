import Mettapedia.GSLT.Dynamics.EquationSaturatedProtocol
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol

/-!
# The rho calculus as an equation-saturated dependent protocol

The generic equation-saturation construction is instantiated on the existing
closed rho carrier, canonical process equations, and declaration-derived raw
rewrite relation.  The resulting saturated GSLT and the established rho GSLT
agree on equations and endpoint steps in both directions.  Their canonical
literal-equality protocol retains exactly the same rewrite occurrences as the
existing rho occurrence protocol.

The typed strict-COMM subprotocol maps into this quotient-aware protocol while
retaining its independent native typing evidence.  Static equations, dynamic
receipts, and typing therefore meet through explicit maps rather than one
combined judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.EquationSaturatedProtocolBridge

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.ProofRelevantRelationProtocol
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionProtocolComparison
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol

/-! ## Exact middle receipts and saturated occurrences -/

/-- The declaration-derived middle rewrite together with its established raw
rho reduction witness.  Keeping both fields prevents a generated rewrite and
an unrelated semantic receipt from being paired later. -/
structure MiddleReceipt (redex contractum : RhoProcess) where
  derived : rhoRewriteSystem.Reduces redex contractum
  raw : Reduces redex.1 contractum.1

/-- Generic equation-saturated occurrences specialized to rho. -/
abbrev SaturatedOccurrence (source target : RhoProcess) :=
  Mettapedia.GSLT.Dynamics.EquationSaturatedProtocol.Occurrence
    rhoProcessEquations MiddleReceipt source target

/-- The hand-written rho occurrence and the generic equation-saturated
occurrence carry exactly the same data. -/
def occurrenceEquiv (source target : RhoProcess) :
    RewriteOccurrence source target ≃ SaturatedOccurrence source target where
  toFun occurrence :=
    { redex := occurrence.redex
      contractum := occurrence.contractum
      sourceEquation := occurrence.sourceEquation
      receipt := ⟨occurrence.derivedStep, occurrence.rawReceipt⟩
      targetEquation := occurrence.targetEquation }
  invFun occurrence :=
    { redex := occurrence.redex
      contractum := occurrence.contractum
      sourceEquation := occurrence.sourceEquation
      derivedStep := occurrence.receipt.derived
      rawReceipt := occurrence.receipt.raw
      targetEquation := occurrence.targetEquation }
  left_inv := by
    intro occurrence
    cases occurrence
    rfl
  right_inv := by
    intro occurrence
    cases occurrence
    rfl

/-- Target-indexed outgoing occurrences are preserved exactly. -/
def outgoingEquiv (source : RhoProcess) :
    Outgoing SaturatedOccurrence source ≃
      Outgoing RewriteOccurrence source where
  toFun outgoing :=
    ⟨outgoing.1, (occurrenceEquiv source outgoing.1).symm outgoing.2⟩
  invFun outgoing :=
    ⟨outgoing.1, occurrenceEquiv source outgoing.1 outgoing.2⟩
  left_inv := by
    rintro ⟨target, occurrence⟩
    cases occurrence
    rfl
  right_inv := by
    rintro ⟨target, occurrence⟩
    cases occurrence
    rfl

/-! ## Exact comparison of the two rho GSLTs -/

/-- The generic equation-saturated system for rho. -/
abbrev saturatedRhoSystem : GSLT :=
  Mettapedia.GSLT.Dynamics.EquationSaturatedProtocol.saturatedSystem
    rhoProcessEquations MiddleReceipt

/-- The generic literal-equality dependent protocol for rho saturation. -/
abbrev saturatedRhoProtocol :=
  Mettapedia.GSLT.Dynamics.EquationSaturatedProtocol.protocol
    rhoProcessEquations MiddleReceipt

/-- Its literal-equality endpoint GSLT. -/
abbrev saturatedRhoProtocolSystem : GSLT :=
  Mettapedia.GSLT.Dynamics.EquationSaturatedProtocol.protocolSystem
    rhoProcessEquations MiddleReceipt

/-- Generic equation saturation and the established rho GSLT have exactly the
same endpoint steps. -/
theorem saturated_step_iff_languageDef_step
    {source target : RhoProcess} :
    saturatedRhoSystem.Step source target <->
      rhoLanguageDefGSLT.Step source target := by
  constructor
  · rintro ⟨occurrence⟩
    exact ⟨occurrence.redex, occurrence.contractum,
      occurrence.sourceEquation, occurrence.receipt.derived,
      occurrence.targetEquation⟩
  · intro step
    obtain ⟨occurrence⟩ := RewriteOccurrence.complete step
    exact ⟨occurrenceEquiv source target occurrence⟩

/-- Identity-on-terms operational translation from generic saturation to the
established rho GSLT. -/
def saturatedToLanguageDef :
    OperationalTranslation saturatedRhoSystem rhoLanguageDefGSLT where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapStep := saturated_step_iff_languageDef_step.mp

/-- The reverse identity-on-terms operational translation.  Together with the
previous map this records two-sided operational agreement without identifying
their proof objects definitionally. -/
def languageDefToSaturated :
    OperationalTranslation rhoLanguageDefGSLT saturatedRhoSystem where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapStep := saturated_step_iff_languageDef_step.mpr

/-- The literal protocol also agrees exactly with the established rho endpoint
relation, by composition through generic equation saturation. -/
theorem protocol_step_iff_languageDef_step
    {source target : RhoProcess} :
    saturatedRhoProtocolSystem.Step source target <->
      rhoLanguageDefGSLT.Step source target := by
  exact
    (Mettapedia.GSLT.Dynamics.EquationSaturatedProtocol.protocol_step_iff_saturated_step
      rhoProcessEquations MiddleReceipt).trans
        saturated_step_iff_languageDef_step

/-- The generic saturated protocol and the existing rho protocol retain
exactly the same enabled occurrence fibre at every source. -/
def protocolEventEquiv (source : RhoProcess) :
    (Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.interaction
        saturatedRhoProtocol).Enabled source
      ≃ (Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.interaction
        rhoProtocol).Enabled source :=
  (eventEquiv SaturatedOccurrence source).trans
    ((outgoingEquiv source).trans (eventEquiv RewriteOccurrence source).symm)

/-! ## The typed fragment enters the quotient-aware protocol -/

/-- Forget a typed strict-COMM receipt only as far as the generic saturated
rho occurrence. -/
noncomputable def typedToSaturated {source target : RhoProcess} :
    StrictCoreCommOccurrence source target ->
      SaturatedOccurrence source target :=
  fun occurrence => occurrenceEquiv source target occurrence.toRewriteOccurrence

/-- Every typed strict-COMM step enters the quotient-aware protocol and the
established rho GSLT, while its typing theorem remains available separately. -/
theorem typed_step_enters_saturated_protocol
    {source target : RhoProcess}
    (step : typedCommSystem.Step source target) :
    saturatedRhoProtocolSystem.Step source target /\
      rhoLanguageDefGSLT.Step source target /\
      HasType TypingContext.empty source.1 processTruth /\
      HasTypeUpToSubjectEquiv TypingContext.empty target.1 processTruth := by
  obtain ⟨occurrence⟩ :=
    (lts_step_iff StrictCoreCommOccurrence).1 step
  have saturatedOccurrence := typedToSaturated occurrence
  refine ⟨(lts_step_iff SaturatedOccurrence).2 ⟨saturatedOccurrence⟩,
    occurrence.toRewriteOccurrence.toStep, ?_⟩
  exact occurrence.preservesNativeTyping

/-! ## Controls -/

/-- The existing closed COMM occurrence survives the generic saturation
equivalence exactly. -/
noncomputable def closedCommSaturatedOccurrence :
    SaturatedOccurrence closedCommSource closedCommTarget :=
  occurrenceEquiv closedCommSource closedCommTarget closedCommOccurrence

theorem closedComm_enters_generic_saturation :
    saturatedRhoProtocolSystem.Step closedCommSource closedCommTarget /\
      saturatedRhoSystem.Step closedCommSource closedCommTarget /\
      rhoLanguageDefGSLT.Step closedCommSource closedCommTarget := by
  refine ⟨(lts_step_iff SaturatedOccurrence).2
    ⟨closedCommSaturatedOccurrence⟩,
    ⟨closedCommSaturatedOccurrence⟩,
    closedCommOccurrence.toStep⟩

/-- The quotient-aware comparison preserves the known static-equation
boundary: all three endpoint systems agree operationally, but the literal
protocol does not reflect rho's singleton-parallel equation. -/
theorem rho_protocol_quotient_boundary :
    (forall source target,
      saturatedRhoProtocolSystem.Step source target <->
        rhoLanguageDefGSLT.Step source target) /\
      saturatedRhoSystem.Equiv closedCommTarget closedNil /\
      rhoLanguageDefGSLT.Equiv closedCommTarget closedNil /\
      Not (saturatedRhoProtocolSystem.Equiv closedCommTarget closedNil) := by
  refine ⟨fun _ _ => protocol_step_iff_languageDef_step,
    closedParallelSingleton_equivalent_nil,
    closedParallelSingleton_equivalent_nil, ?_⟩
  exact closedCommTarget_ne_closedNil

/-! ## Axiom audit -/

#print axioms occurrenceEquiv
#print axioms outgoingEquiv
#print axioms saturated_step_iff_languageDef_step
#print axioms saturatedToLanguageDef
#print axioms languageDefToSaturated
#print axioms protocol_step_iff_languageDef_step
#print axioms protocolEventEquiv
#print axioms typed_step_enters_saturated_protocol
#print axioms closedComm_enters_generic_saturation
#print axioms rho_protocol_quotient_boundary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.EquationSaturatedProtocolBridge
