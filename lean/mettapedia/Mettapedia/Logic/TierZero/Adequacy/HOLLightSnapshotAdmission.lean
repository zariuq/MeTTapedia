import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotData
import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteAdmissionTables
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextTable

/-!
# One original local admission computes every successor snapshot projection

A selected finite context, canonical availability lookup and decoded original
command drive admission. Its computed output constructs the successor finite
context table, real source entry/catalog and canonical metadata together.
The old source history is not replayed. Logical source authority still comes
from the actual selected protected premise occurrences of the physical step.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotAdmission

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Logic
open HOLLightSnapshotData
open HOLLightCanonicalLicenses (Store)

def recordIds (store : Store) (before after : Nat) : Store :=
  if after = before then store else
    (((store.intern (.inl after)).1).intern (.inr (before, after))).1

theorem recordIds_original (store : Store) {contexts : Nat → TheoryContext} (entry : HOLLightContextActivation.Entry contexts) :
    recordIds store entry.before entry.after = HOLLightCanonicalContextRegistry.record store entry := rfl

structure Prepared where
  snapshot : Snapshot
  source : Nat
  before : Nat
  after : Nat
  command : Command
  output : Output
  parents : List Theorem

def updated (snapshot : Snapshot) (before : Nat) (data : Data) (command : Command)
    (output : Output) (table : DeclarationTable.Table output.context) (parents : List Theorem) : Prepared :=
  let after := if HOLLightContextTable.changesContext command then snapshot.contexts.size else before
  let contexts := if HOLLightContextTable.changesContext command then
    snapshot.contexts.push (HOLLightFiniteContextSource.ofTable table) else snapshot.contexts
  ⟨⟨contexts, recordIds snapshot.store before after,
      snapshot.entries.push (before, after, data), snapshot.catalog ++ [snapshot.entries.size]⟩,
    snapshot.entries.size, before, after, command, output, parents⟩

def prepare (policy : AxiomPolicy) [DecidablePred policy] (snapshot : Snapshot) (before : Nat)
    (data : Data) (cache : Array Theorem) : Option Prepared := do
  let contextData ← snapshot.contexts[before]?
  if formed : HOLLightFiniteContextData.valid contextData = true then
    let table := HOLLightFiniteContextData.toTable contextData ((HOLLightFiniteContextData.valid_iff _).mp formed)
    let _ ← snapshot.store.lookup (.inl before)
    let command ← HOLLightFiniteCommandData.decode data
    let admitted ← HOLLightFiniteAdmissionTables.admitWithTable policy table cache command
    let parents ← DerivationGraph.lookupPremises cache command.parents
    pure (updated snapshot before data command admitted.1 admitted.2 parents)
  else none

theorem prepare_of_checked (policy : AxiomPolicy) [DecidablePred policy]
    (snapshot : Snapshot) (before : Nat) (data : Data) (cache : Array Theorem)
    (contextData : HOLLightFiniteContextData.ContextData) (formed : HOLLightFiniteContextData.WellFormed contextData)
    (command : Command) (output : Output) (parents : List Theorem) (identity : Nat)
    (contextKnown : snapshot.contexts[before]? = some contextData)
    (licensed : snapshot.store.lookup (.inl before) = some identity)
    (decoded : HOLLightFiniteCommandData.decode data = some command)
    (checked : command.check policy (HOLLightFiniteContextData.toContext contextData formed) cache = some output)
    (selected : DerivationGraph.lookupPremises cache command.parents = some parents) :
    prepare policy snapshot before data cache = some (updated snapshot before data command output
      (HOLLightFiniteAdmissionTables.outputTable policy (HOLLightFiniteContextData.toTable contextData formed)
        cache command output checked) parents) := by
  have admittedExact : HOLLightFiniteAdmissionTables.admitWithTable policy
      (HOLLightFiniteContextData.toTable contextData formed) cache command = some ⟨output,
        HOLLightFiniteAdmissionTables.outputTable policy (HOLLightFiniteContextData.toTable contextData formed)
          cache command output checked⟩ := by
    unfold HOLLightFiniteAdmissionTables.admitWithTable
    split
    · rename_i refused
      rw [checked] at refused
      cases refused
    · rename_i result checkedAgain
      have same : result = output := Option.some.inj (checkedAgain.symm.trans checked)
      subst result
      rfl
  simp only [prepare, contextKnown, Bind.bind, Option.bind]
  rw [dif_pos ((HOLLightFiniteContextData.valid_iff _).mpr formed)]
  simp only [licensed, decoded, admittedExact, selected]
  rfl

theorem prepare_origin (policy : AxiomPolicy) [DecidablePred policy] (snapshot : Snapshot) (before : Nat)
    (data : Data) (cache : Array Theorem) {prepared : Prepared}
    (computed : prepare policy snapshot before data cache = some prepared) :
    ∃ (contextData : HOLLightFiniteContextData.ContextData)
      (formed : HOLLightFiniteContextData.WellFormed contextData) (command : Command) (output : Output)
      (table : DeclarationTable.Table output.context) (parents : List Theorem),
      snapshot.contexts[before]? = some contextData ∧
      (snapshot.store.lookup (.inl before)).isSome = true ∧
      HOLLightFiniteCommandData.decode data = some command ∧
      command.check policy (HOLLightFiniteContextData.toContext contextData formed) cache = some output ∧
      DerivationGraph.lookupPremises cache command.parents = some parents ∧
      prepared = updated snapshot before data command output table parents := by
  cases contextKnown : snapshot.contexts[before]? with
  | none => simp [prepare, contextKnown] at computed
  | some contextData =>
      simp only [prepare, contextKnown, Bind.bind, Option.bind] at computed
      split at computed
      · rename_i formed
        cases licensed : snapshot.store.lookup (.inl before) with
        | none => simp [licensed] at computed
        | some identity =>
            cases decoded : HOLLightFiniteCommandData.decode data with
            | none => simp [licensed, decoded] at computed
            | some command =>
                cases admitted : HOLLightFiniteAdmissionTables.admitWithTable policy
                    (HOLLightFiniteContextData.toTable contextData ((HOLLightFiniteContextData.valid_iff _).mp formed)) cache command with
                | none => simp [licensed, decoded, admitted] at computed
                | some admittedOutput =>
                    cases parentsKnown : DerivationGraph.lookupPremises cache command.parents with
                    | none => simp [licensed, decoded, admitted, parentsKnown] at computed
                    | some parents =>
                        have checked := congrArg (Option.map Sigma.fst) admitted
                        rw [HOLLightFiniteAdmissionTables.admitWithTable_output_exact] at checked
                        have outputChecked : command.check policy
                            (HOLLightFiniteContextData.toContext contextData ((HOLLightFiniteContextData.valid_iff _).mp formed)) cache = some admittedOutput.1 := checked
                        refine ⟨contextData, (HOLLightFiniteContextData.valid_iff _).mp formed,
                          command, admittedOutput.1, admittedOutput.2, parents, rfl, rfl, rfl, outputChecked, parentsKnown, ?_⟩
                        have same : updated snapshot before data command admittedOutput.1 admittedOutput.2 parents = prepared := by
                          simpa [licensed, decoded, admitted, parentsKnown] using computed
                        exact same.symm
      · contradiction

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotAdmission
