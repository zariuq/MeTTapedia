import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RetainedTypePayloads
import Mettapedia.Machines.MutableObservationIdentity

/-! # Retained type-payload and permitted-write dependencies -/

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RetainedTypePayloads

#print axioms copy_eq
#print axioms copyList_eq
#print axioms admitted_observe
#print axioms admittedList_observe
#print axioms admittedList_iff
#print axioms admitted_equal_iff
#print axioms find_exact
#print axioms intern_sound
#print axioms retained_observation_stable
#print axioms intern_preserves_materialized
#print axioms unsafe_declines
#print axioms encodeChild_readback
#print axioms encodeChildren_readback
#print axioms encodeKey_readback
#print axioms retained_key_source_congruence
#print axioms Controls.ordinary_grammar_admitted
#print axioms Controls.colliding_hashes_still_compare_payloads
#print axioms Controls.ground_external_payload_not_admitted
#print axioms Controls.mutable_initially_equal
#print axioms Controls.mutable_copy_keeps_handle
#print axioms Controls.mutable_reuse_changes_observation
#print axioms Controls.output_check_rejects_conflation
#print axioms Controls.immutable_output_does_not_stabilize_service

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RetainedTypePayloads

#print axioms Mettapedia.Machines.MutableObservationIdentity.unrestricted_iff_identity
#print axioms Mettapedia.Machines.MutableObservationIdentity.same_observations_history
#print axioms Mettapedia.Machines.MutableObservationIdentity.Controls.clearing_cache_does_not_repair_published_reference
