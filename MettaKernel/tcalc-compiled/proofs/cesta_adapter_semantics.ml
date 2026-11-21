(* Ordinary-row refinement through capacity-preserving pack suffixes. *)

needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/ordinary_pack_spec.ml";;

let FLAT_GUARD_VALID_APPEND_LEFT = prove
 (`!fs rs fs' rs' g.
     flat_guard_valid fs rs g
     ==> flat_guard_valid (APPEND fs fs') (APPEND rs rs') g`,
  REWRITE_TAC[flat_guard_valid; flat_offset; flat_offset0;
              LENGTH_APPEND; EL_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FLAT_MAKE_VALID_APPEND_LEFT = prove
 (`!fs rs fs' rs' m.
     flat_make_valid fs rs m
     ==> flat_make_valid (APPEND fs fs') (APPEND rs rs') m`,
  REWRITE_TAC[flat_make_valid; flat_offset; LENGTH_APPEND; EL_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FLAT_GUARD_HOLDS_APPEND_LEFT = prove
 (`!fs rs fs' rs' g.
     flat_guard_valid fs rs g
     ==> (flat_guard_holds (APPEND fs fs') (APPEND rs rs') g <=>
          flat_guard_holds fs rs g)`,
  REWRITE_TAC[flat_guard_valid; flat_guard_holds; flat_offset; flat_offset0;
              EL_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let FLAT_FIELD_APPEND_LEFT = prove
 (`!fs rs fs' rs' m.
     flat_make_valid fs rs m
     ==> flat_field (APPEND fs fs') (APPEND rs rs') m = flat_field fs rs m`,
  REWRITE_TAC[flat_make_valid; flat_field; flat_offset; EL_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let FLAT_VALID_APPEND_LEFT = prove
 (`!fs rs gs ms fs' rs'.
     flat_valid fs rs gs ms
     ==> flat_valid (APPEND fs fs') (APPEND rs rs') gs ms`,
  REWRITE_TAC[flat_valid] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `flat_guard_valid fs rs` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FLAT_GUARD_VALID_APPEND_LEFT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `flat_make_valid fs rs` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FLAT_MAKE_VALID_APPEND_LEFT THEN ASM_REWRITE_TAC[]]);;

let FLAT_GUARDS_HOLD_APPEND_LEFT = prove
 (`!fs rs gs ms fs' rs'.
     flat_valid fs rs gs ms
     ==> (flat_guards_hold (APPEND fs fs') (APPEND rs rs') gs <=>
          flat_guards_hold fs rs gs)`,
  REWRITE_TAC[flat_valid; flat_guards_hold] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (INST [`flat_guard_valid fs rs`,`R:int32->bool`]
    (INST_TYPE [`:int32`,`:A`] ALL_EQ)) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FLAT_GUARD_HOLDS_APPEND_LEFT THEN
    ASM_REWRITE_TAC[]]);;

let FLAT_SELECTED_APPEND_LEFT = prove
 (`!fs rs gs ms fs' rs'.
     flat_valid fs rs gs ms
     ==> flat_selected (APPEND fs fs') (APPEND rs rs') ms =
         flat_selected fs rs ms`,
  REWRITE_TAC[flat_valid; flat_selected] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (ISPECL
   [`flat_field (APPEND fs fs') (APPEND rs rs')`;
    `flat_field fs rs`; `ms:int32 list`] MAP_EQ) THEN
  MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `flat_make_valid fs rs` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FLAT_FIELD_APPEND_LEFT THEN ASM_REWRITE_TAC[]);;

let ORDINARY_ADAPTER_PACKED_VALID = prove
 (`!source offsets constants fields rows ars guards makes.
     ordinary_valid
       (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list)))
       ars constants guards makes
     ==> flat_valid
       (ordinary_pack_result_fields source offsets constants fields)
       (ordinary_pack_result_rows source offsets rows)
       (ordinary_pack_guards guards) (ordinary_pack_makes makes)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ordinary_pack_result_fields; ordinary_pack_result_rows] THEN
  ASM_MESON_TAC[FLAT_VALID_APPEND_LEFT; ORDINARY_PACKED_VALID]);;

let ORDINARY_ADAPTER_FIRE_REFINEMENT = prove
 (`!source offsets constants fields rows ars guards makes.
     ordinary_valid
       (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list)))
       ars constants guards makes
     ==> (if flat_guards_hold
               (ordinary_pack_result_fields source offsets constants fields)
               (ordinary_pack_result_rows source offsets rows)
               (ordinary_pack_guards guards)
          then SOME(flat_selected
               (ordinary_pack_result_fields source offsets constants fields)
               (ordinary_pack_result_rows source offsets rows)
               (ordinary_pack_makes makes))
          else NONE) =
         ordinary_fire_spec
           (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list)))
           constants guards makes`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `flat_valid
      (ordinary_fields
        (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list))) constants)
      (ordinary_rows
        (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list))))
      (ordinary_pack_guards guards) (ordinary_pack_makes makes)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ORDINARY_PACKED_VALID THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ordinary_pack_result_fields; ordinary_pack_result_rows] THEN
  SUBGOAL_THEN
   `flat_guards_hold
      (APPEND
        (ordinary_fields
          (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list)))
          constants)
        (ordinary_drop (4 * LENGTH offsets + LENGTH constants) fields))
      (APPEND
        (ordinary_rows
          (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list))))
        (ordinary_drop (LENGTH offsets + 1) rows))
      (ordinary_pack_guards guards) =
    flat_guards_hold
      (ordinary_fields
        (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list)))
        constants)
      (ordinary_rows
        (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list))))
      (ordinary_pack_guards guards)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FLAT_GUARDS_HOLD_APPEND_LEFT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `flat_selected
      (APPEND
        (ordinary_fields
          (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list)))
          constants)
        (ordinary_drop (4 * LENGTH offsets + LENGTH constants) fields))
      (APPEND
        (ordinary_rows
          (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list))))
        (ordinary_drop (LENGTH offsets + 1) rows))
      (ordinary_pack_makes makes) =
    flat_selected
      (ordinary_fields
        (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list)))
        constants)
      (ordinary_rows
        (ordinary_arena_rows source (MAP (\offset. val offset) (offsets:int32 list))))
      (ordinary_pack_makes makes)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FLAT_SELECTED_APPEND_LEFT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ORDINARY_FIRE_REFINEMENT THEN ASM_MESON_TAC[]);;
