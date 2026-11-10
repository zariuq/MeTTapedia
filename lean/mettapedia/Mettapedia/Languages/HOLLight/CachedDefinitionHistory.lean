import Mettapedia.Languages.HOLLight.RegisteredReplayModels
import Mettapedia.Languages.HOLLight.DefinitionReplayModels

/-!
# A received constant history inside a mixed source model

Exact cached theorem inclusion lets an already checked constant-only history
be interpreted in a later model which also contains type definitions and proof
steps. The old contexts are retained. Every source type instance is covered;
the argument does not construct a separate model for the old declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CachedDefinitionHistory

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution DefinitionHistoryModels DefinitionReplayModels RegisteredReplayModels
open DefinitionHistorySchemas DefinitionSchemaSubstitution ModelInterpretation TypeFamilySemantics
open DefinitionAdapters DefinitionModelFamily SignatureFormation

universe w

theorem history_models {initial final referenceInitial referenceFinal : TheoryContext}
    {policy : AxiomPolicy} {cache : Array Theorem}
    (frame : Frame.{w} initial policy final cache) (primitives : Primitives initial)
    (history : ConstantHistory referenceInitial referenceFinal)
    (referencePrimitives : Primitives referenceInitial)
    (included : ∀ result ∈ history.records, result.output.definitionTheorem ∈ cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {result : DefinitionAdapters.ContextConstantDefinitionResult} (member : result ∈ history.records)
    (substitution : TypeSubst) :
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB result.output.definitionTheorem.sequent.concl.term)
        .prop formula ∧ (frame.model other assignment).models formula := by
  obtain ⟨before, instances, name, source, accepted⟩ := history.record_admitted member
  have translated := (ConstantHistory.record_translated history member).applyDB
    (TypeCorrectTermSubstitution.ofTypes substitution)
  rw [targetMap_eq_typeMap (ConstantHistory.record_ordinary history referencePrimitives member)] at translated
  exact ⟨_, translated, frame.cached_constant_schema_instance primitives accepted
    (included result member) other assignment substitution⟩

theorem reference_models {initial final : TheoryContext} {policy : AxiomPolicy} {cache : Array Theorem}
    (frame : Frame.{w} initial policy final cache) (primitives : Primitives initial)
    (before : ExportCodec.State) (inputs : List Lean.Json) (after : ExportCodec.State)
    (referencePrimitives : Primitives before.received.registered.context)
    (accepted : SourceProfile.referenceDefinitions? before inputs = some after)
    (empty : before.received.registered.cache = #[])
    (included : ∀ fact ∈ after.received.registered.cache, fact ∈ cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∀ fact ∈ after.received.registered.cache, ∀ substitution : TypeSubst,
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally [] ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term)
          .prop formula ∧ (frame.model other assignment).models formula := by
  obtain ⟨events, constants, replayed⟩ := reference_definitions_events before inputs after accepted
  have commands := replay_registered_commands before.received events after.received replayed
  obtain ⟨history, recorded⟩ := replay_constant_history before.received.registered
    (events.map ExportReplay.Event.command) after.received.registered
    (by intro command member; obtain ⟨event, present, rfl⟩ := List.mem_map.mp member; exact constants event present)
    commands
  have allRecords (result) (member : result ∈ history.records) : result.output.definitionTheorem ∈ cache := by
    apply included
    have present : result.output.definitionTheorem ∈ after.received.registered.cache.toList := by
      rw [recorded]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨result, member, rfl⟩)
    simpa using present
  intro fact member substitution
  have present : fact ∈ after.received.registered.cache.toList := by simpa using member
  rw [recorded, empty] at present
  simp only [List.nil_append, List.mem_map] at present
  obtain ⟨result, recordedMember, rfl⟩ := present
  exact history_models frame primitives history referencePrimitives allRecords other assignment recordedMember substitution

private def select? (cache : Array Theorem) : (indices : List Nat) →
    Option {facts : List Theorem // ∀ fact ∈ facts, fact ∈ cache}
  | [] => some ⟨[], by simp⟩
  | index :: rest => do
      if present : index < cache.size then
        let selected ← select? cache rest
        return ⟨cache[index] :: selected.val, by
          intro fact member
          rcases List.mem_cons.mp member with rfl | later
          · exact Array.getElem_mem present
          · exact selected.property fact later⟩
      else none

structure Inclusion (earlier later : Array Theorem) : Type where
  known : ∀ fact ∈ earlier, fact ∈ later

/-- A short address table is checked by full theorem identity, not names. -/
def inclusion? (earlier later : Array Theorem) (indices : List Nat) : Option (Inclusion earlier later) := do
  let selected ← select? later indices
  if same : theoremListStructuralSame earlier.toList selected.val = true then
    return ⟨by
      intro fact member
      apply selected.property
      rw [← (theoremListStructuralSame_eq_true_iff _ _).mp same]
      simpa using member⟩
  else none

end Mettapedia.Languages.HOLLight.CachedDefinitionHistory
