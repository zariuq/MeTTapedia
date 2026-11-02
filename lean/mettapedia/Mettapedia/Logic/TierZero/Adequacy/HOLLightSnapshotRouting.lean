import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotActivation

/-!
# Earned routing for the actual data-resident source catalog

Installed routing is preserved through real finite snapshot growth. The
catalog's source projection constructs the original Entry interface from
that invariant; it does not recheck declaration histories or assume source
rule soundness. Its activation is exactly the original local activation,
wrapped with the private snapshot read and its public request envelope.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotRouting

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotInstallation
open HOLLightSnapshotActivation

def Routes (snapshot : Snapshot) : Prop :=
  ∀ source entry command, lookup snapshot source = some (entry, command) →
    ∃ beforeContext afterContext, context snapshot entry.1 = some beforeContext ∧
      context snapshot entry.2.1 = some afterContext ∧
      HOLLightContextActivation.targetContext beforeContext command = some afterContext

theorem initial_routed {root : TheoryContext} (table : DeclarationTable.Table root) : Routes (initial table) := by
  intro source entry command found
  rw [initial_source_absent table source] at found
  cases found

theorem lookup_outside_new_slot (snapshot : Snapshot) (before : Nat) (data : Mettapedia.OSLF.Binding.WireCodec.Data)
    (command : Command) (output : Output) (table : DeclarationTable.Table output.context) (parents : List Theorem)
    (source : Nat) (different : source ≠ snapshot.entries.size) :
    lookup (updated snapshot before data command output table parents).snapshot source = lookup snapshot source := by
  simp [lookup, updated, Array.getElem?_push, different]

theorem routes_updated (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (prior : Routes snapshot) (before : Nat) (data : Mettapedia.OSLF.Binding.WireCodec.Data)
    (command : Command) (output : Output) (table : DeclarationTable.Table output.context) (parents : List Theorem)
    (cache : Array Theorem) {beforeContext : TheoryContext}
    (known : context snapshot before = some beforeContext)
    (checked : command.check policy beforeContext cache = some output)
    (decoded : HOLLightFiniteCommandData.decode data = some command) :
    Routes (updated snapshot before data command output table parents).snapshot := by
  intro source entry actualCommand found
  by_cases same : source = snapshot.entries.size
  · subst source
    have installed := installed_lookup snapshot before data command output table parents decoded
    have equal := Prod.mk.inj (Option.some.inj (found.symm.trans installed))
    obtain ⟨entrySame, commandSame⟩ := equal
    subst entry
    subst actualCommand
    exact ⟨beforeContext, output.context,
      old_context_retained snapshot before data command output table parents before known,
      target_context_exact policy snapshot before data command output table parents cache known checked,
      HOLLightContextActivation.checked_target_context policy beforeContext cache command checked⟩
  · rw [lookup_outside_new_slot snapshot before data command output table parents source same] at found
    obtain ⟨oldBefore, oldAfter, beforeKnown, afterKnown, routed⟩ := prior source entry actualCommand found
    exact ⟨oldBefore, oldAfter,
      old_context_retained snapshot before data command output table parents entry.1 beforeKnown,
      old_context_retained snapshot before data command output table parents entry.2.1 afterKnown, routed⟩

def sourceEntry (snapshot : Snapshot) (routed : Routes snapshot) (fallback : TheoryContext)
    (source : Nat) (loaded : RawEntry × Command) (found : lookup snapshot source = some loaded) :
    HOLLightContextActivation.Entry (interpret snapshot fallback) where
  before := loaded.1.1
  after := loaded.1.2.1
  command := loaded.2
  routed := by
    obtain ⟨beforeContext, afterContext, beforeKnown, afterKnown, actual⟩ := routed source loaded.1 loaded.2 found
    simpa only [interpret, beforeKnown, afterKnown, Option.getD_some] using actual

def entries (snapshot : Snapshot) (routed : Routes snapshot) (fallback : TheoryContext) (source : Nat) :
    Option (HOLLightContextActivation.Entry (interpret snapshot fallback)) :=
  match found : lookup snapshot source with
  | none => none
  | some loaded =>
      if (snapshot.store.lookup (.inl loaded.1.1)).isSome then some (sourceEntry snapshot routed fallback source loaded found) else none

theorem entries_none (snapshot : Snapshot) (routed : Routes snapshot) (fallback : TheoryContext) (source : Nat)
    (missing : lookup snapshot source = none) : entries snapshot routed fallback source = none := by
  unfold entries
  split
  · rfl
  · rename_i loaded found
    rw [missing] at found
    cases found

theorem entries_some (snapshot : Snapshot) (routed : Routes snapshot) (fallback : TheoryContext) (source : Nat)
    (loaded : RawEntry × Command) (known : lookup snapshot source = some loaded) :
    entries snapshot routed fallback source =
      if (snapshot.store.lookup (.inl loaded.1.1)).isSome then some (sourceEntry snapshot routed fallback source loaded known) else none := by
  unfold entries
  split
  · rename_i missing
    rw [known] at missing
    cases missing
  · rename_i actual found
    have same : actual = loaded := Option.some.inj (found.symm.trans known)
    subst actual
    rfl

def lift (value : InferenceSchemaKernel.Value) : Value := (.inl value.1, value.2)

def wrap (snapshot : Snapshot) (source : Nat) (cache : Array Theorem) (raw : RuleInstance InferenceSchemaKernel.Value) : RuleInstance Value :=
  { raw.map lift with take := [(requests, runRequest source cache)]
                      read := (snapshots, snapshotPayload snapshot) :: raw.read.map lift }

theorem activation_exact_original (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (routed : Routes snapshot) (fallback : TheoryContext) (source : Nat) (cache : Array Theorem) :
    runActivate policy snapshot source cache =
      (HOLLightContextActivation.activate policy (interpret snapshot fallback) (entries snapshot routed fallback) source cache).map
        (wrap snapshot source cache) := by
  cases sourceKnown : lookup snapshot source with
  | none =>
      have missingEntries := entries_none snapshot routed fallback source sourceKnown
      simp [runActivate, HOLLightContextActivation.activate, missingEntries, sourceKnown]
  | some loaded =>
      obtain ⟨entry, command⟩ := loaded
      obtain ⟨beforeContext, afterContext, beforeKnown, afterKnown, route⟩ := routed source entry command sourceKnown
      have entryKnown := entries_some snapshot routed fallback source (entry, command) sourceKnown
      cases licensed : snapshot.store.lookup (.inl entry.1) with
      | none => simp [runActivate, HOLLightContextActivation.activate, entryKnown, sourceKnown, beforeKnown, licensed]
      | some identity =>
          cases checked : command.check policy beforeContext cache with
          | none =>
              simp [runActivate, HOLLightContextActivation.activate, entryKnown, sourceKnown,
                sourceEntry, interpret, beforeKnown, licensed, checked]
          | some output =>
              cases selected : Mettapedia.Logic.DerivationGraph.lookupPremises cache command.parents with
              | none =>
                  simp [runActivate, HOLLightContextActivation.activate, entryKnown, sourceKnown,
                    sourceEntry, interpret, beforeKnown, licensed, selected]
              | some parents =>
                  simp [runActivate, HOLLightContextActivation.activate, entryKnown, sourceKnown,
                    sourceEntry, interpret, beforeKnown, licensed, checked, selected,
                    wrap, runFromResult, RuleInstance.map, HOLLightContextActivation.fromResult, lift, List.map_map, judgments]

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotRouting
