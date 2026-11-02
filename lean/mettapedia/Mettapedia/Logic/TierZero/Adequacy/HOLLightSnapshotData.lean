import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextSource
import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandData
import Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalContextRegistry
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStoreData

/-!
# Private finite context, source catalog and canonical-registry snapshot data

The snapshot stores original finite context rows and original command data.
Catalog lookup actually selects a stored source command. Its routed source
meaning is an invariant earned when that command is admitted; decoding does
not replay old admissions. A finite codec exposes every operational field.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotData

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open HOLLightCanonicalLicenses (Key Store)
open HOLLightFiniteContextData (ContextData)

/-- Source/target immutable context IDs and the original finite command envelope. -/
abbrev RawEntry := Nat × Nat × Data

def rawDataCodec : Codec Data := ⟨id, some, fun _ => rfl⟩

def entryCodec : Codec RawEntry := Codec.prod Codec.nat (Codec.prod Codec.nat rawDataCodec)

def keyCodec : Codec Key where
  put
    | .inl context => .pair (.atom 0) (.atom context)
    | .inr (before, after) => .pair (.atom 1) (.pair (.atom before) (.atom after))
  get
    | .pair (.atom 0) (.atom context) => some (.inl context)
    | .pair (.atom 1) (.pair (.atom before) (.atom after)) => some (.inr (before, after))
    | _ => none
  get_put := by intro key; cases key with | inl => rfl | inr pair => cases pair; rfl

def arrayCodec {A : Type} (element : Codec A) : Codec (Array A) :=
  (Codec.list element).mapped Array.toList (fun entries => some entries.toArray)
    (by intro entries; simp)

structure Snapshot where
  contexts : Array ContextData
  store : Store
  entries : Array RawEntry
  catalog : List Nat

def codec : Codec Snapshot :=
  (Codec.prod (arrayCodec HOLLightFiniteContextData.codec)
    (Codec.prod (CanonicalMetadataStoreData.storeCodec keyCodec)
      (Codec.prod (arrayCodec entryCodec) (Codec.list Codec.nat)))).mapped
    (fun snapshot => (snapshot.contexts, snapshot.store, snapshot.entries, snapshot.catalog))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩) (fun _ => rfl)

def context (snapshot : Snapshot) (identifier : Nat) : Option TheoryContext := do
  let data ← snapshot.contexts[identifier]?
  HOLLightFiniteContextData.decode data

def interpret (snapshot : Snapshot) (fallback : TheoryContext) (identifier : Nat) : TheoryContext :=
  (context snapshot identifier).getD fallback

def lookup (snapshot : Snapshot) (source : Nat) : Option (RawEntry × Command) := do
  if source ∈ snapshot.catalog then
    let entry ← snapshot.entries[source]?
    let command ← HOLLightFiniteCommandData.decode entry.2.2
    pure (entry, command)
  else none

def initial {root : TheoryContext} (table : DeclarationTable.Table root) : Snapshot :=
  ⟨#[HOLLightFiniteContextSource.ofTable table], HOLLightCanonicalContextRegistry.initialized 0, #[], []⟩

theorem initial_context {root : TheoryContext} (table : DeclarationTable.Table root) :
    context (initial table) 0 = some root := HOLLightFiniteContextSource.decode_ofTable table

theorem initial_source_absent {root : TheoryContext} (table : DeclarationTable.Table root) (source : Nat) :
    lookup (initial table) source = none := by simp [lookup, initial]

theorem unknown_catalog_source_refused (snapshot : Snapshot) (source : Nat) (absent : source ∉ snapshot.catalog) :
    lookup snapshot source = none := by simp [lookup, absent]

theorem lookup_origin (snapshot : Snapshot) (source : Nat) {entry : RawEntry} {command : Command}
    (found : lookup snapshot source = some (entry, command)) :
    source ∈ snapshot.catalog ∧ snapshot.entries[source]? = some entry ∧
      HOLLightFiniteCommandData.decode entry.2.2 = some command := by
  unfold lookup at found
  split at found
  · rename_i installed
    cases rawKnown : snapshot.entries[source]? with
    | none => simp [rawKnown] at found
    | some raw =>
        cases decoded : HOLLightFiniteCommandData.decode raw.2.2 with
        | none => simp [rawKnown, decoded] at found
        | some checked =>
            have equal : (raw, checked) = (entry, command) := by simpa [rawKnown, decoded] using found
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
            exact ⟨installed, rfl, decoded⟩
  · contradiction

theorem wire_roundtrip (snapshot : Snapshot) : codec.get (codec.put snapshot) = some snapshot := codec.get_put snapshot

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotData
