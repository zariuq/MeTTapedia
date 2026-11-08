import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec

/-! # Current 64-bit frame and two-word variable codec audit -/

#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.wellFormed
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.fits64
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.facts
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.live_admits
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.leaves
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.choose_exact
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.live_pack
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.encode_nat_exact
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.encoding_bound
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.encode_exact
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.encoded_toNat
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.decode_encode
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.encode_injective
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.locate_live
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.parts_live
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.reserved_case
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.decode_nat_exact
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.decode_exact
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.encode_decode
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.native_decode_encode
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.decoded_valid
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.reserved_rejected
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.zero_handle_rejected
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.zero_generation_rejected
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.invalid_not_wrapped
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.arity
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.generated_part
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.generated_validity
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.generated_encoder
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.generated_admitted_parts
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.native_hot_fields
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.variable_components
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.variable_encoding_injective
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.distinct_frames_qualify_apart
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.Controls.first_identity_uses_high_word
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.Controls.last_layout_identity_roundtrips
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.Controls.last_handle_is_layout_valid_but_not_issued
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.Controls.last_issued_identity_roundtrips
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.Controls.zero_and_reserved_rejected
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.Controls.oversized_fields_do_not_wrap
#print axioms Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaCurrentFrameCodec.Controls.variable_base_keeps_all_64_bits

