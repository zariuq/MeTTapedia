import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotSemantics
import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotRouting

/-!
# Rooted canonical-registry meaning survives the actual snapshot replacement

The existing LicensedStore predicate is retained. Its immutable context IDs
must additionally refer to actual decoded table entries, so an out-of-range
fallback cannot later become a different licensed context. Actual selected
source premises earn the new context/path licenses; public cache entries do
not acquire authority merely by being present in the request data.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotRegistrySemantics

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightCanonicalLicenses (Key Store)
open HOLLightCanonicalContextRegistry (LicensedStore Eligible intern_preserves_licenses)
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotInstallation HOLLightSnapshotActivation
open HOLLightContextLicensing

def Addressed (snapshot : Snapshot) : Key → Prop
  | .inl identifier => ∃ sourceContext, context snapshot identifier = some sourceContext
  | .inr (before, after) => ∃ beforeContext afterContext,
      context snapshot before = some beforeContext ∧ context snapshot after = some afterContext

structure RegistryValid (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (fallback : TheoryContext) (snapshot : Snapshot) : Prop where
  licensed : LicensedStore initial policy (interpret snapshot fallback) snapshot.store
  addressed : ∀ index key, (index, key) ∈ snapshot.store.rows → Addressed snapshot key

theorem initialized_valid (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (fallback : TheoryContext) (table : DeclarationTable.Table root) : RegistryValid root policy fallback (initial table) := by
  refine ⟨?_, ?_⟩
  · apply HOLLightCanonicalContextRegistry.initialized_licensed root policy (interpret (initial table) fallback) 0
    simp only [interpret, initial_context, Option.getD_some]
  · intro index key member
    have rows : (initial table).store.rows = {(0, Sum.inl 0)} := rfl
    rw [rows] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Finset.mem_singleton.mp member)
    exact ⟨root, initial_context table⟩

theorem licensed_context (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (fallback : TheoryContext) (snapshot : Snapshot) (valid : RegistryValid root policy fallback snapshot)
    (identifier : Nat) (sourceContext : TheoryContext) (known : context snapshot identifier = some sourceContext)
    (available : (snapshot.store.lookup (.inl identifier)).isSome = true) : Licensed root policy sourceContext := by
  cases found : snapshot.store.lookup (.inl identifier) with
  | none => simp [found] at available
  | some index =>
      have actual := valid.licensed index (.inl identifier) ((snapshot.store.represented index _).mpr found)
      simpa only [Eligible, interpret, known, Option.getD_some] using actual

private theorem intern_addressed (snapshot : Snapshot) (store : Store)
    (prior : ∀ index key, (index, key) ∈ store.rows → Addressed snapshot key)
    (key : Key) (addressed : Addressed snapshot key) :
    ∀ index other, (index, other) ∈ (store.intern key).1.rows → Addressed snapshot other := by
  intro index other member
  cases known : store.lookup key with
  | some existing =>
      rw [(store.repeated_lookup_creates_no_row key existing known).1] at member
      exact prior index other member
  | none =>
      rw [(store.actual_fresh_row key known).1] at member
      rcases Finset.mem_insert.mp member with fresh | previous
      · have same : other = key := congrArg Prod.snd fresh
        exact same ▸ addressed
      · exact prior index other previous

theorem updated_registry_valid (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (fallback : TheoryContext) (snapshot : Snapshot) (valid : RegistryValid root policy fallback snapshot)
    (before : Nat) (data : Data) (command : Command) (output : Output)
    (table : DeclarationTable.Table output.context) (parents : List Theorem) (cache : Array Theorem)
    (sourceContext : TheoryContext) (known : context snapshot before = some sourceContext)
    (available : (snapshot.store.lookup (.inl before)).isSome = true)
    (checked : command.check policy sourceContext cache = some output)
    (selected : ∀ index ∈ command.parents, ∀ fact, cache[index]? = some fact → TheoryDerives policy sourceContext fact) :
    RegistryValid root policy fallback (updated snapshot before data command output table parents).snapshot := by
  let next := (updated snapshot before data command output table parents).snapshot
  let after := (updated snapshot before data command output table parents).after
  have beforeKnown : context next before = some sourceContext :=
    old_context_retained snapshot before data command output table parents before known
  have afterKnown : context next after = some output.context :=
    target_context_exact policy snapshot before data command output table parents cache known checked
  have source := checked_command_licenses_output root policy
    (licensed_context root policy fallback snapshot valid before sourceContext known available) command cache checked selected
  have transferred : LicensedStore root policy (interpret next fallback) snapshot.store := by
    intro index key member
    have earlier := valid.licensed index key member
    cases key with
    | inl identifier =>
        obtain ⟨actualContext, contextKnown⟩ := valid.addressed index (.inl identifier) member
        have retained : context next identifier = some actualContext :=
          old_context_retained snapshot before data command output table parents identifier contextKnown
        simpa only [Eligible, interpret, contextKnown, retained, Option.getD_some] using earlier
    | inr pair =>
        obtain ⟨fromContext, toContext, fromKnown, toKnown⟩ := valid.addressed index (.inr pair) member
        have fromRetained : context next pair.1 = some fromContext :=
          old_context_retained snapshot before data command output table parents pair.1 fromKnown
        have toRetained : context next pair.2 = some toContext :=
          old_context_retained snapshot before data command output table parents pair.2 toKnown
        simpa only [Eligible, interpret, fromKnown, toKnown, fromRetained, toRetained, Option.getD_some] using earlier
  have oldAddressed : ∀ index key, (index, key) ∈ snapshot.store.rows → Addressed next key := by
    intro index key member
    cases key with
    | inl identifier =>
        obtain ⟨actualContext, contextKnown⟩ := valid.addressed index (.inl identifier) member
        exact ⟨actualContext, old_context_retained snapshot before data command output table parents identifier contextKnown⟩
    | inr pair =>
        obtain ⟨fromContext, toContext, fromKnown, toKnown⟩ := valid.addressed index (.inr pair) member
        exact ⟨fromContext, toContext,
          old_context_retained snapshot before data command output table parents pair.1 fromKnown,
          old_context_retained snapshot before data command output table parents pair.2 toKnown⟩
  have newLicense : Eligible root policy (interpret next fallback) (.inl after) := by
    simpa only [Eligible, interpret, afterKnown, Option.getD_some] using source.1
  have newPath : Eligible root policy (interpret next fallback) (.inr (before, after)) := by
    simpa only [Eligible, interpret, beforeKnown, afterKnown, Option.getD_some] using source.2.1
  refine ⟨?_, ?_⟩
  · change LicensedStore root policy (interpret next fallback) (recordIds snapshot.store before after)
    unfold recordIds
    split
    · exact transferred
    · exact intern_preserves_licenses root policy (interpret next fallback)
        (snapshot.store.intern (.inl after)).1
        (intern_preserves_licenses root policy (interpret next fallback) snapshot.store transferred (.inl after) newLicense)
        (.inr (before, after)) newPath
  · change ∀ index key, (index, key) ∈ (recordIds snapshot.store before after).rows → Addressed next key
    unfold recordIds
    split
    · exact oldAddressed
    · exact intern_addressed next (snapshot.store.intern (.inl after)).1
        (intern_addressed next snapshot.store oldAddressed (.inl after) ⟨output.context, afterKnown⟩)
        (.inr (before, after)) ⟨sourceContext, output.context, beforeKnown, afterKnown⟩

theorem prepared_registry_valid (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (fallback : TheoryContext) (snapshot : Snapshot) (valid : RegistryValid root policy fallback snapshot)
    (before : Nat) (data : Data) (cache : Array Theorem) {prepared : Prepared}
    (computed : prepare policy snapshot before data cache = some prepared)
    (selected : ∀ sourceContext, context snapshot before = some sourceContext → ∀ index ∈ prepared.command.parents,
      ∀ fact, cache[index]? = some fact → TheoryDerives policy sourceContext fact) :
    RegistryValid root policy fallback prepared.snapshot := by
  obtain ⟨contextData, formed, command, output, table, parents, contextKnown, available, _, checked, _, rfl⟩ :=
    prepare_origin policy snapshot before data cache computed
  have known : context snapshot before = some (HOLLightFiniteContextData.toContext contextData formed) := by
    simp only [context, contextKnown, Bind.bind, Option.bind]
    unfold HOLLightFiniteContextData.decode
    rw [dif_pos ((HOLLightFiniteContextData.valid_iff _).mpr formed)]
  exact updated_registry_valid root policy fallback snapshot valid before data command output table parents cache _ known available checked
    (selected _ known)

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotRegistrySemantics
