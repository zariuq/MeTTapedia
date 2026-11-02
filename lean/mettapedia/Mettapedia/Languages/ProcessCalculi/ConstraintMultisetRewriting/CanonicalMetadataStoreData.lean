import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStore
import Mettapedia.OSLF.Syntax.BindingWireBinary

/-!
# Finite data for the existing canonical private registry and physical store

The ordered unique keys determine their original indices and actual rows.
Decoding checks uniqueness and reconstructs the same canonical Store; it
neither invents fresh identities nor replays source declarations or proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStoreData

open Mettapedia.OSLF.Binding.WireCodec
open CanonicalMetadataRegistry CanonicalMetadataStore

variable {K : Type} [DecidableEq K]

theorem find_of_get {keys : List K} (unique : keys.Nodup) {key : K} {index : Nat}
    (selected : keys[index]? = some key) : find key keys = some index := by
  induction keys generalizing index with
  | nil => simp at selected
  | cons first rest earlier =>
      cases index with
      | zero =>
          have same : first = key := Option.some.inj selected
          simp [find, same]
      | succ index =>
          have remaining : rest[index]? = some key := selected
          have different : first ≠ key := by
            intro same
            exact (List.nodup_cons.mp unique).1 (same ▸ List.mem_of_getElem? remaining)
          simp [find, different, earlier (List.nodup_cons.mp unique).2 remaining]

def physicalRows (registry : Registry K) : Finset (Nat × K) :=
  (registry.keys.zipIdx.map (fun entry => (entry.2, entry.1))).toFinset

theorem physicalRows_represented (registry : Registry K) : Represents registry (physicalRows registry) := by
  intro index key
  constructor
  · intro member
    obtain ⟨entry, selected, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have same : entry = (key, index) := by
      obtain ⟨candidate, position⟩ := entry
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      rfl
    subst entry
    exact find_of_get registry.unique (List.mk_mem_zipIdx_iff_getElem?.mp selected)
  · intro found
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨(key, index), List.mk_mem_zipIdx_iff_getElem?.mpr (find_get found), rfl⟩

def fromRegistry (registry : Registry K) : Store K :=
  ⟨registry, physicalRows registry, physicalRows_represented registry⟩

theorem fromRegistry_exact (store : Store K) : fromRegistry store.registry = store := by
  cases store with
  | mk registry rows represented =>
      have sameRows : physicalRows registry = rows := by
        ext row
        exact (physicalRows_represented registry row.1 row.2).trans (represented row.1 row.2).symm
      subst rows
      rfl

def registryGet (codec : Codec K) (data : Data) : Option (Registry K) := do
  let keys ← (Codec.list codec).get data
  if unique : keys.Nodup then some ⟨keys, unique⟩ else none

theorem registry_roundtrip (codec : Codec K) (registry : Registry K) :
    registryGet codec ((Codec.list codec).put registry.keys) = some registry := by
  simp only [registryGet, (Codec.list codec).get_put]
  change (if unique : registry.keys.Nodup then some ⟨registry.keys, unique⟩ else none) = some registry
  rw [dif_pos registry.unique]

def registryCodec (codec : Codec K) : Codec (Registry K) :=
  ⟨fun registry => (Codec.list codec).put registry.keys, registryGet codec, registry_roundtrip codec⟩

def storeCodec (codec : Codec K) : Codec (Store K) :=
  (registryCodec codec).mapped (·.registry) (fun registry => some (fromRegistry registry))
    (fun store => congrArg some (fromRegistry_exact store))

theorem store_roundtrip (codec : Codec K) (store : Store K) :
    (storeCodec codec).get ((storeCodec codec).put store) = some store := (storeCodec codec).get_put store

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStoreData
