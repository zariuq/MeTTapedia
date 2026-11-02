import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStoreData

/-! # Canonical-store data roundtrips and duplicate-key refusal -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStoreDataControls

open Mettapedia.OSLF.Binding.WireCodec
open CanonicalMetadataStore CanonicalMetadataStoreData

def twoKeys : Store Nat := (((Store.empty (K := Nat)).intern 7).1.intern 9).1

theorem actual_finite_store_roundtrips :
    (storeCodec Codec.nat).get ((storeCodec Codec.nat).put twoKeys) = some twoKeys := store_roundtrip _ _

theorem original_rows_recovered : (fromRegistry twoKeys.registry).rows = {(0, 7), (1, 9)} := by decide

theorem repeated_key_data_refused : registryGet Codec.nat ((Codec.list Codec.nat).put [7, 7]) = none := by
  simp [registryGet, (Codec.list Codec.nat).get_put]

theorem ordered_keys_keep_old_indices : (fromRegistry twoKeys.registry).lookup 7 = some 0 := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CanonicalMetadataStoreDataControls
