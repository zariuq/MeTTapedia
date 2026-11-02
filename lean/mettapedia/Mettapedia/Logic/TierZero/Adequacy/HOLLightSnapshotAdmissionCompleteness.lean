import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublication

/-!
# Every original admitted finite command has an actual snapshot installation

The selected context and canonical availability are actual data lookups.
Every accepted original command supplies its finite certificate observation
and actual ordered parent values, then computes the coupled activation. The
statement includes all primitive and declaration constructors, without source
history replay or an arbitrary-function serialization assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotAdmissionCompleteness

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Logic
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotActivation
open HOLLightFiniteCommandWitnesses

theorem checked_parents_exist (policy : AxiomPolicy) [DecidablePred policy] (sourceContext : TheoryContext)
    (cache : Array Theorem) (command : Command) {output : Output}
    (checked : command.check policy sourceContext cache = some output) :
    ∃ parents, DerivationGraph.lookupPremises cache command.parents = some parents := by
  cases command with
  | proof node certificates =>
      cases replayed : node.replay (ruleWitness policy) cache with
      | none => simp [Command.check, replayed] at checked
      | some result =>
          obtain ⟨parents, found, _, _⟩ := (node.replay_eq_some_iff (ruleWitness policy) cache result).mp replayed
          exact ⟨parents, found⟩
  | constant origin name body certificates => exact ⟨[], rfl⟩
  | typeDefinition origin request index certificates =>
      cases found : cache[index]? with
      | none => simp [Command.check, found] at checked
      | some fact =>
          exact ⟨[fact], by simp [Command.parents, DerivationGraph.lookupPremises, found]⟩

theorem decoded_context_exists (contextData : HOLLightFiniteContextData.ContextData) (sourceContext : TheoryContext)
    (decoded : HOLLightFiniteContextData.decode contextData = some sourceContext) :
    ∃ formed : HOLLightFiniteContextData.WellFormed contextData,
      HOLLightFiniteContextData.toContext contextData formed = sourceContext := by
  unfold HOLLightFiniteContextData.decode at decoded
  split at decoded
  · rename_i checked
    exact ⟨(HOLLightFiniteContextData.valid_iff _).mp checked, Option.some.inj decoded⟩
  · cases decoded

theorem recordIds_after_available (store : HOLLightCanonicalLicenses.Store) (before after : Nat)
    (available : (store.lookup (.inl before)).isSome = true) :
    ((recordIds store before after).lookup (.inl after)).isSome = true := by
  unfold recordIds
  split
  · rename_i same
    exact same ▸ available
  · have allocated := store.after_lookup (.inl after)
    have retained := (store.intern (.inl after)).1.retained_lookup (.inr (before, after)) (.inl after) _ allocated
    rw [retained]
    rfl

theorem prepared_after_available (policy : AxiomPolicy) [DecidablePred policy] (snapshot : Snapshot)
    (before : Nat) (data : Data) (cache : Array Theorem) {prepared : Prepared}
    (computed : prepare policy snapshot before data cache = some prepared) :
    (prepared.snapshot.store.lookup (.inl prepared.after)).isSome = true := by
  obtain ⟨_, _, command, output, table, parents, _, available, _, _, _, rfl⟩ :=
    prepare_origin policy snapshot before data cache computed
  exact recordIds_after_available snapshot.store before _ available

theorem every_checked_command_installs (policy : AxiomPolicy) [DecidablePred policy] (snapshot : Snapshot)
    (before : Nat) (sourceContext : TheoryContext) (known : context snapshot before = some sourceContext)
    (available : (snapshot.store.lookup (.inl before)).isSome = true)
    (cache : Array Theorem) (command : Command) (output : Output)
    (checked : command.check policy sourceContext cache = some output) :
    ∃ prepared : Prepared,
      prepare policy snapshot before (HOLLightFiniteCommandData.encode command (sampleCommand command output)) cache = some prepared ∧
      prepared.output = output ∧ prepared.command.origin = command.origin ∧ prepared.command.parents = command.parents := by
  let finiteCommand := withWitnesses command (HOLLightFiniteWitnesses.witnesses (sampleCommand command output))
  have finiteChecked : finiteCommand.check policy sourceContext cache = some output :=
    accepted_finite_observation policy sourceContext cache command checked
  obtain ⟨parents, selected⟩ := checked_parents_exist policy sourceContext cache finiteCommand finiteChecked
  cases contextKnown : snapshot.contexts[before]? with
  | none => simp [context, contextKnown] at known
  | some contextData =>
      have decoded : HOLLightFiniteContextData.decode contextData = some sourceContext := by simpa [context, contextKnown] using known
      obtain ⟨formed, sameContext⟩ := decoded_context_exists contextData sourceContext decoded
      have actualChecked : finiteCommand.check policy (HOLLightFiniteContextData.toContext contextData formed) cache = some output :=
        (congrArg (fun sourceContext => finiteCommand.check policy sourceContext cache) sameContext).trans finiteChecked
      cases licensed : snapshot.store.lookup (.inl before) with
      | none => simp [licensed] at available
      | some identity =>
          let table := HOLLightFiniteAdmissionTables.outputTable policy (HOLLightFiniteContextData.toTable contextData formed)
            cache finiteCommand output actualChecked
          let prepared := updated snapshot before (HOLLightFiniteCommandData.encode command (sampleCommand command output)) finiteCommand output table parents
          refine ⟨prepared, prepare_of_checked policy snapshot before _ cache contextData formed finiteCommand output parents identity
            contextKnown licensed (HOLLightFiniteCommandData.decode_encode command _) actualChecked selected, rfl, ?_, ?_⟩
          · exact origin_preserved command _
          · exact parents_preserved command _

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotAdmissionCompleteness
