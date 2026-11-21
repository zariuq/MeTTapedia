(* Exact linked-byte invalid-offset rejection proof for ordinary_flat_pack. *)

let ORDINARY_PACK_FIRST_BAD_OFFSET = prove
 (`!source offsets.
    ~(ordinary_pack_offsets_valid source offsets)
    ==> ?n. n < LENGTH offsets /\
            ~(val(EL n offsets:int32) + 4 <= LENGTH source) /\
            !i. i < n ==> val(EL i offsets:int32) + 4 <= LENGTH source`,
  REWRITE_TAC[ordinary_pack_offsets_valid; GSYM ALL_EL] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?n. n < LENGTH(offsets:int32 list) /\
        ~(val(EL n offsets:int32) + 4 <= LENGTH(source:int32 list))`
  MP_TAC THENL
   [ASM_MESON_TAC[]; GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_ARITH_TAC);;

let ORDINARY_PACK_OFFSET_SUB = prove
 (`!n (offset:int32).
    n < 2 EXP 64 /\ val offset <= n
    ==> val(word_sub (word n:int64) (word_zx offset:int64)) = n - val offset`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `val(word_zx (offset:int32):int64) = val(offset:int32)` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN ASM_ARITH_TAC);;
