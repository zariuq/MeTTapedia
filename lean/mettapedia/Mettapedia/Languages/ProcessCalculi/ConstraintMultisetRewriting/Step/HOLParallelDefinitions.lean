import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLParallelDefinitionData
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSemanticDefinitions

/-!
# The independently exported parallel definitions in the registered receiver

The original definition history is retained as a checked cache prefix. The
two new definitions are admitted conservatively, and the existing history
model construction interprets all twenty-one defining equations together.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelDefinitions

open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic

def records : List Lean.Json := HOLSemanticDefinitionData.records ++ HOLParallelDefinitionData.records

theorem reference_available :
    (SourceProfile.referenceDefinitions? HOLSemanticDefinitions.received
      HOLParallelDefinitionData.records).isSome = true := by decide +kernel

def received : ExportCodec.State :=
  (SourceProfile.referenceDefinitions? HOLSemanticDefinitions.received HOLParallelDefinitionData.records).get
    reference_available

theorem extension_exact : SourceProfile.referenceDefinitions? HOLSemanticDefinitions.received
    HOLParallelDefinitionData.records = some received := (Option.some_get reference_available).symm

private theorem definitions_append (before : ExportCodec.State) (first second : List Lean.Json) :
    SourceProfile.referenceDefinitions? before (first ++ second) =
      (SourceProfile.referenceDefinitions? before first).bind
        (fun middle => SourceProfile.referenceDefinitions? middle second) := by
  induction first generalizing before with
  | nil => rfl
  | cons input rest ih =>
      simp only [List.cons_append, SourceProfile.referenceDefinitions?]
      split
      · rfl
      · cases next : ExportCodec.receive? emptyAxiomPolicy before input with
        | none => rfl
        | some middle => simpa [next] using ih middle

theorem received_exact : SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis records = some received :=
  by rw [records, definitions_append, HOLSemanticDefinitions.received_exact, Option.bind_some, extension_exact]

theorem definition_inventory : records.length = 21 := rfl

private theorem definitions_cache_append (before after : ExportCodec.State) (inputs : List Lean.Json)
    (accepted : SourceProfile.referenceDefinitions? before inputs = some after) :
    ∃ suffix, after.received.registered.cache.toList = before.received.registered.cache.toList ++ suffix := by
  induction inputs generalizing before with
  | nil =>
      have same := Option.some.inj accepted
      subst after
      exact ⟨[], (List.append_nil _).symm⟩
  | cons input rest ih =>
      unfold SourceProfile.referenceDefinitions? at accepted
      split at accepted
      · contradiction
      · cases next : ExportCodec.receive? emptyAxiomPolicy before input with
        | none => simp [next] at accepted
        | some middle =>
            have remaining : SourceProfile.referenceDefinitions? middle rest = some after := by
              simpa [next] using accepted
            obtain ⟨event, replayed⟩ := ExportCodec.receive?_checked emptyAxiomPolicy next
            have checked := (ExportReplay.apply_checked emptyAxiomPolicy replayed).1
            obtain ⟨output, _checked, _context, cache, _receipts⟩ :=
              ProofExecution.Registered.apply_result emptyAxiomPolicy checked
            obtain ⟨suffix, later⟩ := ih middle remaining
            refine ⟨output.theorems ++ suffix, ?_⟩
            rw [later, cache, Array.toList_append, List.toList_toArray, List.append_assoc]

theorem original_cache_prefix :
    received.received.registered.cache.toList.take HOLSemanticDefinitions.received.received.registered.cache.size =
      HOLSemanticDefinitions.received.received.registered.cache.toList := by
  obtain ⟨suffix, same⟩ := definitions_cache_append _ _ _ extension_exact
  rw [same]
  simp

theorem original_cache_included {fact : Theorem}
    (member : fact ∈ HOLSemanticDefinitions.received.received.registered.cache) :
    fact ∈ received.received.registered.cache := by
  apply Array.mem_toList_iff.mp
  obtain ⟨suffix, same⟩ := definitions_cache_append _ _ _ extension_exact
  rw [same]
  exact List.mem_append_left _ (Array.mem_toList_iff.mpr member)

universe w

theorem defining_equations_have_constructed_model
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ∃ finalModel : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      finalModel.Carrier = model.Carrier ∧
      (model.FullDomains → finalModel.FullDomains) ∧
      ∀ fact ∈ received.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula :=
  DefinitionReplayModels.reference_definitions_models SourceProfile.primitiveBasis records received received_exact rfl model

theorem repeated_parallel_definitions_refused :
    SourceProfile.referenceDefinitions? received HOLParallelDefinitionData.records = none := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelDefinitions
