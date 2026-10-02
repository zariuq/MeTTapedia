import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitPolicyControls

/-!
# Nonempty generated paths and quotation-scope controls

Both witnesses use a bound-name receiver, a nonempty signed payload and a
nonempty quoted channel. Their paths are constructed by the existing enabled
one-firing constructor, preserving the exact candidate and event identifier.
Whole execution instantiates the selected authored R1 readout; split execution
retains both physical cells and both checked signature surfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathControls

open ActivationGenerated ActivationGenerated.SerializationAdmission ActivationLocatedControls
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def wholeSource : Pattern := receiverSource channelSource boundBodySource payloadSource unitSource emptySource

def wholeTerm : CostTerm LiteralAuthority :=
  decodedReceiverSource channel (.drop (.bvar 0)) payload {unitSource} .empty

theorem whole_image : ConfigImage channel wholeSource wholeTerm :=
  located_receiver_config_image channel_image
    (CodeImage.drop (NameImage.bvar (index := 0) (by decide +kernel)))
    payload_image unitTyped unit_accepted StackImage.empty

theorem split_image : ConfigImage channel
    (splitReceiverSource channelSource boundBodySource payloadSource unitSource productSource
      ActivationSplitControls.recvTailSource ActivationSplitControls.sendTailSource)
    ActivationSplitControls.source :=
  split_receiver_config_image channel_image
    (CodeImage.drop (NameImage.bvar (index := 0) (by decide +kernel))) payload_image
    unitTyped unit_accepted ActivationSplitControls.productTyped ActivationSplitControls.product_accepted
    ActivationSplitControls.recv_tail_image ActivationSplitControls.send_tail_image

/-- A genuine funded whole path instantiates the class-wide selected-contact
comparison and the independently licensed pure-base path. -/
theorem whole_nonempty_path {signatureName : SignatureNameEncoding String}
    (signatureClosed : signatureName.MapsToClosedRhoNames) :
    ∃ step, ∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm wholeTerm)) 1
        (applyTracedStep (initialTraceComponents (literalEncodeTerm wholeTerm)) step 0),
      path.depth = 1 ∧ path.firingEntries = [(0, initialTraceComponents (literalEncodeTerm wholeTerm), step)] ∧
      (∃ contactSource contactTarget frameSource sourceTerm targetTerm,
        Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
          (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
          rhoCIGSLT.costWholeLanguage contactSource contactTarget ∧
        ConfigImage channel (.collection .hashBag [contactSource, frameSource] none) sourceTerm ∧
        ConfigImage channel (.collection .hashBag [contactTarget, frameSource] none) targetTerm ∧
        ((literalEncodeTerm sourceTerm).normalizeConfig : Multiset RawCostTerm) =
          ((initialTraceComponents (literalEncodeTerm wholeTerm)).map RawTraceComponent.term : Multiset RawCostTerm) ∧
        rawConfigStructuralDenote ((applyTracedStep (initialTraceComponents (literalEncodeTerm wholeTerm)) step 0).map
          RawTraceComponent.term) = rawConfigStructuralDenote (literalEncodeTerm targetTerm).normalizeConfig) ∧
      ∃ finalSafe : (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm wholeTerm)) step 0).map
          RawTraceComponent.term)).BinderSafe,
        ∃ purePath : Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT.rhoLanguageDefGSLT.RewritePath
          ((decodeRawConfig ((initialTraceComponents (literalEncodeTerm wholeTerm)).map RawTraceComponent.term))
            |>.eraseCanonicalProcess signatureClosed whole_image.initial_decoded_binderSafe)
          ((decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm wholeTerm)) step 0).map
            RawTraceComponent.term)) |>.eraseCanonicalProcess signatureClosed finalSafe), purePath.length = 1 := by
  obtain ⟨step, enabled, _located, spent, _oldPath⟩ := actual_closed_location_entry
  have wellFormed := whole_image.literal_wellFormed channel_image.literal_wellFormed
  let path := UnitPolicyControls.fireOnce (literalEncodeTerm wholeTerm) wellFormed step enabled
  have entries : path.firingEntries = [(0, initialTraceComponents (literalEncodeTerm wholeTerm), step)] := rfl
  have cells : step.selectedPurses.length = 1 := by
    rw [whole_image.canonical_candidate_cells_eq_atoms channel_image enabled, spent, Multiset.card_singleton]
  obtain ⟨_finalSource, _decoded, _fuel, finalSafe, purePath, _parsed, _exactReadback, length, comparisons⟩ :=
    whole_image.finite_path_operational_adequacy channel_image path signatureClosed
  have member : (0, initialTraceComponents (literalEncodeTerm wholeTerm), step) ∈ path.firingEntries := by
    rw [entries]
    exact List.mem_singleton_self _
  obtain ⟨_canonical, _images, _enabled, _sound, wholeOrSplit⟩ := comparisons _ member
  rcases wholeOrSplit with ⟨cover, same, _coordinates, realization⟩ | ⟨cover, same, selected, _fields⟩
  · exact ⟨step, path, rfl, entries, realization, finalSafe, purePath, length⟩
  · have sameCells : cover.selected.length = 1 := by
      change cover.runtimeStep.selectedPurses.length = 1
      rw [same]
      exact cells
    omega

/-- Both split signing surfaces remain accepted entire Patterns, and both
selected cells belong to the actual nonempty occurrence path. -/
theorem split_nonempty_path {signatureName : SignatureNameEncoding String}
    (signatureClosed : signatureName.MapsToClosedRhoNames) :
    ∃ step, ∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)) 1
        (applyTracedStep (initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)) step 0),
      path.depth = 1 ∧ path.firingEntries = [(0, initialTraceComponents (literalEncodeTerm ActivationSplitControls.source), step)] ∧
      (∃ cover : RawSplitOccurrenceCover
        ((initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)).map RawTraceComponent.term),
        cover.runtimeStep = step ∧ cover.selected.length = 2 ∧
        SignatureAdmitted cover.receiver.sig ∧ SignatureAdmitted cover.sender.sig) ∧
      ∃ finalSafe : (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)) step 0).map
          RawTraceComponent.term)).BinderSafe,
        ∃ purePath : Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT.rhoLanguageDefGSLT.RewritePath
          ((decodeRawConfig ((initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)).map RawTraceComponent.term))
            |>.eraseCanonicalProcess signatureClosed split_image.initial_decoded_binderSafe)
          ((decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)) step 0).map
            RawTraceComponent.term)) |>.eraseCanonicalProcess signatureClosed finalSafe), purePath.length = 1 := by
  obtain ⟨step, enabled, _spent, cells, _oldPath, _balance⟩ :=
    ActivationSplitControls.actual_two_generated_purse_execution
  have wellFormed := split_image.literal_wellFormed channel_image.literal_wellFormed
  let path := UnitPolicyControls.fireOnce (literalEncodeTerm ActivationSplitControls.source) wellFormed step enabled
  have entries : path.firingEntries = [(0, initialTraceComponents (literalEncodeTerm ActivationSplitControls.source), step)] := rfl
  obtain ⟨_finalSource, _decoded, _fuel, finalSafe, purePath, _parsed, _exactReadback, length, comparisons⟩ :=
    split_image.finite_path_operational_adequacy channel_image path signatureClosed
  have member : (0, initialTraceComponents (literalEncodeTerm ActivationSplitControls.source), step) ∈ path.firingEntries := by
    rw [entries]
    exact List.mem_singleton_self _
  obtain ⟨_canonical, images, _enabled, _sound, wholeOrSplit⟩ := comparisons _ member
  rcases wholeOrSplit with ⟨cover, same, coordinates, _realization⟩ | ⟨cover, same, selected, _fields⟩
  · obtain ⟨_signatureSource, _signature, purse, _tailSource, _tail,
      _checked, _spent, _location, _participants, singleton, _purseLocation, _head, _tailImage, _tailSame⟩ := coordinates
    change cover.runtimeStep = step at same
    have sameCells : step.selectedPurses.length = 1 := by rw [← same, singleton]; rfl
    omega
  · exact ⟨step, path, rfl, entries, ⟨cover, same, selected, cover.admitted_signatures images⟩,
      finalSafe, purePath, length⟩

/-- An ambient receiver binder never opens a literal quotation. -/
theorem quote_scope_resets (depth : Nat) :
    ¬NameAdmitted depth (.quote (.drop (.bvar 0))) := by
  intro image
  cases image with
  | quote code =>
      cases code with
      | drop name =>
          cases name with
          | bvar bound => omega

theorem receiver_open_quote_rejected :
    ¬CodeAdmitted 1 (.drop (.quote (.drop (.bvar 0)))) := by
  intro image
  cases image with
  | drop name => exact quote_scope_resets 1 name

def fundedOpenQuote (authority : String) : RawCostTerm :=
  .par (.signed (.par
    (.recv (.quote .nil) (.drop (.quote (.drop (.bvar 0)))))
    (.send (.quote .nil) (.signed (.send (.quote .nil) .nil) [authority]))) [authority])
    (.purse (.quote .nil) [[authority]])

/-- A real located funding head does not license capture inside quotation. -/
theorem funded_open_quote_runtime_rejected (authority : String) :
    runtimeCostCandidates (fundedOpenQuote authority) = none := by
  simp [runtimeCostCandidates, fundedOpenQuote, RawCostTerm.supported,
    RawCostTerm.runtimeBinderSafe, RawCostTerm.runtimeBinderSafeAt,
    RawCostProc.runtimeBinderSafeAt, RawCostName.runtimeBinderSafeAt]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathControls
