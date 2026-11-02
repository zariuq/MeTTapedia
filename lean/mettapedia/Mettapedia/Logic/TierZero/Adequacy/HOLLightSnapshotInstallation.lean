import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotAdmission
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextLicensing

/-!
# Computed snapshot installation retains real source lookup and exact contexts

The new catalog entry is operationally selected by the actual lookup, while
all earlier source entries and immutable contexts remain available. Its
original Entry routing follows the one checked source command. Rooted source
validity still requires exactly its selected protected premises.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotInstallation

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.HOLLight.MeTTa
open HOLLightSnapshotData HOLLightSnapshotAdmission
open HOLLightContextLicensing

theorem installed_lookup (snapshot : Snapshot) (before : Nat) (data : Data) (command : Command)
    (output : Output) (table : DeclarationTable.Table output.context) (parents : List Theorem)
    (decoded : HOLLightFiniteCommandData.decode data = some command) :
    lookup (updated snapshot before data command output table parents).snapshot snapshot.entries.size =
      some ((before, (updated snapshot before data command output table parents).after, data), command) := by
  simp [lookup, updated, decoded]

theorem old_lookup_retained (snapshot : Snapshot) (before : Nat) (data : Data) (command : Command)
    (output : Output) (table : DeclarationTable.Table output.context) (parents : List Theorem)
    (source : Nat) {entry : RawEntry} {oldCommand : Command}
    (known : lookup snapshot source = some (entry, oldCommand)) :
    lookup (updated snapshot before data command output table parents).snapshot source = some (entry, oldCommand) := by
  obtain ⟨catalogKnown, entryKnown, decoded⟩ := lookup_origin snapshot source known
  have bounded : source < snapshot.entries.size := (Array.getElem?_eq_some_iff.mp entryKnown).1
  have member : source ∈ snapshot.catalog ++ [snapshot.entries.size] := List.mem_append_left _ catalogKnown
  change (if source ∈ snapshot.catalog ++ [snapshot.entries.size] then do
    let raw ← (snapshot.entries.push (before, (updated snapshot before data command output table parents).after, data))[source]?
    let checked ← HOLLightFiniteCommandData.decode raw.2.2
    pure (raw, checked)
    else none) = some (entry, oldCommand)
  rw [if_pos member, Array.getElem?_push, if_neg (Nat.ne_of_lt bounded), entryKnown]
  simp [decoded]

theorem old_context_data_retained (snapshot : Snapshot) (before : Nat) (data : Data) (command : Command)
    (output : Output) (table : DeclarationTable.Table output.context) (parents : List Theorem)
    (identifier : Nat) {contextData : HOLLightFiniteContextData.ContextData}
    (known : snapshot.contexts[identifier]? = some contextData) :
    (updated snapshot before data command output table parents).snapshot.contexts[identifier]? = some contextData := by
  have bounded : identifier < snapshot.contexts.size := (Array.getElem?_eq_some_iff.mp known).1
  by_cases changes : HOLLightContextTable.changesContext command = true
  · simp only [updated, changes, if_true]
    rw [Array.getElem?_push, if_neg (Nat.ne_of_lt bounded)]
    exact known
  · have unchanged : HOLLightContextTable.changesContext command = false := Bool.eq_false_iff.mpr changes
    simpa only [updated, unchanged, Bool.false_eq_true, if_false] using known

theorem old_context_retained (snapshot : Snapshot) (before : Nat) (data : Data) (command : Command)
    (output : Output) (table : DeclarationTable.Table output.context) (parents : List Theorem)
    (identifier : Nat) {oldContext : TheoryContext} (known : context snapshot identifier = some oldContext) :
    context (updated snapshot before data command output table parents).snapshot identifier = some oldContext := by
  cases contextKnown : snapshot.contexts[identifier]? with
  | none => simp [context, contextKnown] at known
  | some contextData =>
      have retained := old_context_data_retained snapshot before data command output table parents identifier contextKnown
      simpa only [context, retained, Bind.bind, Option.bind] using (by simpa [context, contextKnown] using known)

theorem target_context_exact (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (before : Nat) (data : Data) (command : Command)
    (output : Output) (table : DeclarationTable.Table output.context) (parents : List Theorem)
    (cache : Array Theorem) {beforeContext : TheoryContext}
    (known : context snapshot before = some beforeContext)
    (checked : command.check policy beforeContext cache = some output) :
    context (updated snapshot before data command output table parents).snapshot
      (updated snapshot before data command output table parents).after = some output.context := by
  cases command with
  | proof node certificates =>
      have same : beforeContext = output.context :=
        Option.some.inj (HOLLightContextActivation.checked_target_context policy _ _ _ checked)
      change context snapshot before = some output.context
      exact known.trans (congrArg some same)
  | constant origin name body certificates =>
      change (do
        let stored ← (snapshot.contexts.push (HOLLightFiniteContextSource.ofTable table))[snapshot.contexts.size]?
        HOLLightFiniteContextData.decode stored) = some output.context
      rw [Array.getElem?_push_size]
      exact HOLLightFiniteContextSource.decode_ofTable table
  | typeDefinition origin request index certificates =>
      change (do
        let stored ← (snapshot.contexts.push (HOLLightFiniteContextSource.ofTable table))[snapshot.contexts.size]?
        HOLLightFiniteContextData.decode stored) = some output.context
      rw [Array.getElem?_push_size]
      exact HOLLightFiniteContextSource.decode_ofTable table

theorem routed_entry_constructed (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (before : Nat) (data : Data) (command : Command)
    (output : Output) (table : DeclarationTable.Table output.context) (parents : List Theorem)
    (cache : Array Theorem) {beforeContext : TheoryContext}
    (known : context snapshot before = some beforeContext)
    (checked : command.check policy beforeContext cache = some output) (fallback : TheoryContext) :
    ∃ entry : HOLLightContextActivation.Entry (interpret (updated snapshot before data command output table parents).snapshot fallback),
      entry.before = before ∧ entry.after = (updated snapshot before data command output table parents).after ∧ entry.command = command := by
  have retained := old_context_retained snapshot before data command output table parents before known
  have afterKnown := target_context_exact policy snapshot before data command output table parents cache known checked
  refine ⟨⟨before, (updated snapshot before data command output table parents).after, command, ?_⟩, rfl, rfl, rfl⟩
  simp only [interpret, retained, afterKnown, Option.getD_some]
  exact HOLLightContextActivation.checked_target_context policy beforeContext cache command checked

theorem prepared_source_is_rooted (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (before : Nat) (data : Data) (cache : Array Theorem) {prepared : Prepared}
    (computed : prepare policy snapshot before data cache = some prepared)
    (licensed : ∀ sourceContext, context snapshot before = some sourceContext → Licensed initial policy sourceContext)
    (selected : ∀ sourceContext, context snapshot before = some sourceContext → ∀ index ∈ prepared.command.parents,
      ∀ fact, cache[index]? = some fact → TheoryDerives policy sourceContext fact) :
    Licensed initial policy prepared.output.context ∧
      (∀ fact ∈ prepared.output.theorems, TheoryDerives policy prepared.output.context fact) ∧
      context prepared.snapshot prepared.after = some prepared.output.context := by
  obtain ⟨contextData, formed, command, output, table, parents, contextKnown, _, _, checked, _, rfl⟩ :=
    prepare_origin policy snapshot before data cache computed
  have beforeKnown : context snapshot before = some (HOLLightFiniteContextData.toContext contextData formed) := by
    simp only [context, contextKnown, Bind.bind, Option.bind]
    unfold HOLLightFiniteContextData.decode
    rw [dif_pos ((HOLLightFiniteContextData.valid_iff _).mpr formed)]
  have source := checked_command_licenses_output initial policy (licensed _ beforeKnown) command cache checked
    (selected _ beforeKnown)
  exact ⟨source.1, source.2.2, target_context_exact policy snapshot before data command output table parents cache beforeKnown checked⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotInstallation
