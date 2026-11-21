(* Calibration controls for the independent ordinary-row contract. *)

needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/ordinary_pack_spec.ml";;

let ORDINARY_BANK_SELECTS_CONSTANT = prove
 (`ordinary_fire_spec [[word 11; word 22; word 33; word 44]] [word 55]
     [] [(0,2); (1,0)] = SOME [word 33; word 55]`,
  REWRITE_TAC[ordinary_fire_spec; ordinary_guards_hold; ordinary_selected;
    ordinary_field; ordinary_row; ALL; MAP; LENGTH; EL; HD; TL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[HD; TL]);;

let ORDINARY_BANK_REFUSES_MISMATCH = prove
 (`ordinary_fire_spec [[word 11; word 22; word 33; word 44]] []
     [(0,0,0,1)] [(0,2)] = NONE`,
  REWRITE_TAC[ordinary_fire_spec; ordinary_guards_hold; ordinary_guard_holds;
    ordinary_field; ordinary_row; ALL; LENGTH; EL; HD; TL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[HD; TL] THEN CONV_TAC WORD_REDUCE_CONV);;

let ORDINARY_BANK_REFUSES_BAD_COLUMN = prove
 (`~ordinary_valid [[word 11; word 22; word 33; word 44]] [4] [] [] [(0,4)]`,
  REWRITE_TAC[ordinary_valid; ordinary_row_valid; ordinary_make_valid;
    ALL; LENGTH; EL; HD; TL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let ORDINARY_BANK_REFUSES_SHORT_SOURCE = prove
 (`ordinary_pack_rejects [word 11; word 22; word 33; word 44] [word 1]
     [] [word 0; word 0; word 0; word 0] [word 0; word 0]`,
  REWRITE_TAC[ordinary_pack_rejects; ordinary_pack_offsets_valid;
    ordinary_pack_shape_valid; ALL; LENGTH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;
