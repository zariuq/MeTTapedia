import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotInstallation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InteractionFormation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactInteractionExecution

/-!
# One ordinary private snapshot interaction activates actual source entries

Installation consumes the old snapshot and public request. It produces the
computed successor snapshot, actual canonical metadata delta and exact source
theorem outputs in the same RuleInstance. Later source use reads that private
snapshot and consults its real catalog lookup. Handle formation is the full
existing receive/peek/observe/send discipline on the actual two-way CMR step.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotActivation

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic
open InferenceSchemaActivation (Tm action)
open HOLLightSnapshotData HOLLightSnapshotAdmission

abbrev Location := InferenceSchemaKernel.Space ⊕ Bool
abbrev Value := Location × Tm
abbrev locatedAction := LocatedSubstitution.action (N := Location) action

def requests : Location := .inl .requests
def judgments : Location := .inl .judgments
def licenses : Location := .inr false
def snapshots : Location := .inr true

def tagged (name : String) (data : Data) : Tm :=
  .node (.inr name) (.cons 0 (WireDataABT.encode data) .nil)

theorem tagged_fixed (name : String) (data : Data)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) :
    action.apply assignment (tagged name data) = tagged name data := by
  apply ABTProtectedParameters.supported_term_fixed
  simpa [tagged, Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.supportedAt,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.Fields.supportedAt] using WireDataABT.encode_supported data

def snapshotPayload (snapshot : Snapshot) : Tm := tagged "registered.snapshot" (codec.put snapshot)

theorem snapshotPayload_injective : Function.Injective snapshotPayload := by
  intro first second same
  have inner : WireDataABT.encode (codec.put first) = WireDataABT.encode (codec.put second) := by
    simpa [snapshotPayload, tagged] using same
  exact codec.put_injective (WireDataABT.encode_injective inner)

def installRequest (before : Nat) (data : Data) (cache : Array Theorem) : Tm :=
  tagged "registered.snapshot.install" (.pair (.atom before) (.pair data ((Codec.list theoremCodec).put cache.toList)))

def runRequest (source : Nat) (cache : Array Theorem) : Tm :=
  tagged "registered.snapshot.run" (.pair (.atom source) ((Codec.list theoremCodec).put cache.toList))

def metadataDelta (before after : Snapshot) : List Value :=
  ((after.store.rows \ before.store.rows).sort (encodedLe (Codec.prod Codec.nat keyCodec))).map
    (fun row => (licenses, HOLLightCanonicalLicenses.payload row.2))

def installRule (beforeSnapshot : Snapshot) (before : Nat) (data : Data) (cache : Array Theorem)
    (prepared : Prepared) : RuleInstance Value :=
  ⟨[(snapshots, snapshotPayload beforeSnapshot), (requests, installRequest before data cache)],
    prepared.parents.map (fun fact => (judgments, HOLLightContextActivation.theoremPayload before fact)), [], [],
    (snapshots, snapshotPayload prepared.snapshot) ::
      (metadataDelta beforeSnapshot prepared.snapshot ++
        prepared.output.theorems.map (fun fact => (judgments, HOLLightContextActivation.theoremPayload prepared.after fact)))⟩

def installActivate (policy : AxiomPolicy) [DecidablePred policy] (snapshot : Snapshot) (before : Nat)
    (data : Data) (cache : Array Theorem) : Option (RuleInstance Value) :=
  (prepare policy snapshot before data cache).map (installRule snapshot before data cache)

def runFromResult (snapshot : Snapshot) (source : Nat) (entry : RawEntry) (cache : Array Theorem)
    (output : Output) (parents : List Theorem) : RuleInstance Value :=
  ⟨[(requests, runRequest source cache)],
    (snapshots, snapshotPayload snapshot) ::
      parents.map (fun fact => (judgments, HOLLightContextActivation.theoremPayload entry.1 fact)), [], [],
    output.theorems.map (fun fact => (judgments, HOLLightContextActivation.theoremPayload entry.2.1 fact))⟩

def runActivate (policy : AxiomPolicy) [DecidablePred policy] (snapshot : Snapshot) (source : Nat)
    (cache : Array Theorem) : Option (RuleInstance Value) := do
  let (entry, command) ← lookup snapshot source
  let sourceContext ← context snapshot entry.1
  let _ ← snapshot.store.lookup (.inl entry.1)
  let output ← command.check policy sourceContext cache
  let parents ← DerivationGraph.lookupPremises cache command.parents
  pure (runFromResult snapshot source entry cache output parents)

theorem unknown_source_cannot_activate (policy : AxiomPolicy) [DecidablePred policy] (snapshot : Snapshot)
    (source : Nat) (cache : Array Theorem) (absent : lookup snapshot source = none) :
    runActivate policy snapshot source cache = none := by simp [runActivate, absent]

theorem run_origin (policy : AxiomPolicy) [DecidablePred policy] (snapshot : Snapshot)
    (source : Nat) (cache : Array Theorem) {raw : RuleInstance Value}
    (computed : runActivate policy snapshot source cache = some raw) :
    ∃ entry command sourceContext output parents,
      lookup snapshot source = some (entry, command) ∧ context snapshot entry.1 = some sourceContext ∧
      (snapshot.store.lookup (.inl entry.1)).isSome = true ∧ command.check policy sourceContext cache = some output ∧
      DerivationGraph.lookupPremises cache command.parents = some parents ∧ raw = runFromResult snapshot source entry cache output parents := by
  cases sourceKnown : lookup snapshot source with
  | none => simp [runActivate, sourceKnown] at computed
  | some loaded =>
      obtain ⟨entry, command⟩ := loaded
      cases contextKnown : context snapshot entry.1 with
      | none => simp [runActivate, sourceKnown, contextKnown] at computed
      | some sourceContext =>
          cases licensed : snapshot.store.lookup (.inl entry.1) with
          | none => simp [runActivate, sourceKnown, contextKnown, licensed] at computed
          | some identity =>
              cases checked : command.check policy sourceContext cache with
              | none => simp [runActivate, sourceKnown, contextKnown, licensed, checked] at computed
              | some output =>
                  cases selected : DerivationGraph.lookupPremises cache command.parents with
                  | none => simp [runActivate, sourceKnown, contextKnown, licensed, selected] at computed
                  | some parents =>
                      have same : runFromResult snapshot source entry cache output parents = raw := by
                        simpa [runActivate, sourceKnown, contextKnown, licensed, checked, selected] using computed
                      exact ⟨entry, command, sourceContext, output, parents, rfl, contextKnown, by rw [licensed]; rfl, checked, selected, same.symm⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotActivation
