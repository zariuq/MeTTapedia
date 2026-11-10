import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionDefinitionData
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSemanticDefinitions
import Mettapedia.Languages.HOLLight.DefinitionReplayExtension

/-! # A received extension for general preparation and admission

The semantic-effect history is retained as a prefix. New exported records
are admitted by the same registered definition gate, and its chronological
model construction interprets the complete history on unchanged carriers.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionDefinitions

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight

theorem extension_available :
    (SourceProfile.referenceDefinitions? HOLSemanticDefinitions.received HOLAdmissionDefinitionData.records).isSome = true := by
  decide +kernel

def received : ExportCodec.State :=
  (SourceProfile.referenceDefinitions? HOLSemanticDefinitions.received HOLAdmissionDefinitionData.records).get extension_available

theorem received_exact :
    SourceProfile.referenceDefinitions? HOLSemanticDefinitions.received HOLAdmissionDefinitionData.records = some received :=
  (Option.some_get extension_available).symm

theorem complete_history : SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis
    (HOLSemanticDefinitionData.records ++ HOLAdmissionDefinitionData.records) = some received :=
  DefinitionReplayExtension.reference_append_accepted HOLSemanticDefinitions.received_exact received_exact

theorem earlier_cache (fact : Theorem) (known : fact ∈ HOLSemanticDefinitions.received.received.registered.cache) :
    fact ∈ received.received.registered.cache :=
  DefinitionReplayExtension.cache_inclusion received_exact fact known

theorem definition_inventory : HOLSemanticDefinitionData.records.length + HOLAdmissionDefinitionData.records.length = 24 := rfl

universe w

theorem defining_equations_have_constructed_model
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ∃ finalModel : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      finalModel.Carrier = model.Carrier ∧
      (model.FullDomains → finalModel.FullDomains) ∧
      ∀ fact ∈ received.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ finalModel.models formula :=
  DefinitionReplayModels.reference_definitions_models SourceProfile.primitiveBasis
    (HOLSemanticDefinitionData.records ++ HOLAdmissionDefinitionData.records) received complete_history rfl model

theorem earlier_equations (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (equations : ∀ fact ∈ received.received.registered.cache, ∀ substitution : TypeSubst,
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally []
          ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula) :
    ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally []
          ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula :=
  fun fact known substitution => equations fact (earlier_cache fact known) substitution

#print axioms extension_available
#print axioms earlier_cache
#print axioms defining_equations_have_constructed_model

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionDefinitions
