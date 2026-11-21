(* Ordinary four-word rows and their exact flat_fire representation. *)

needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/flat_spec.ml";;

let ordinary_drop = new_recursive_definition num_RECURSION
 `(!l:A list. ordinary_drop 0 l = l) /\
  (!n l:A list. ordinary_drop (SUC n) l =
     if l = [] then [] else ordinary_drop n (TL l))`;;

let ordinary_row = new_definition
 `ordinary_row (ps:(int32 list) list) (cs:int32 list) i =
    if i < LENGTH ps then EL i ps else cs`;;

let ordinary_field = new_definition
 `ordinary_field ps cs (i,j) = EL j (ordinary_row ps cs i)`;;

let ordinary_guard_holds = new_definition
 `ordinary_guard_holds ps cs (i,j,i0,j0) <=>
    ordinary_field ps cs (i,j) = ordinary_field ps cs (i0,j0)`;;

let ordinary_guards_hold = new_definition
 `ordinary_guards_hold ps cs gs = ALL (ordinary_guard_holds ps cs) gs`;;

let ordinary_selected = new_definition
 `ordinary_selected ps cs ms = MAP (ordinary_field ps cs) ms`;;

let ordinary_fire_spec = new_definition
 `ordinary_fire_spec ps cs gs ms =
    if ordinary_guards_hold ps cs gs
    then SOME(ordinary_selected ps cs ms) else NONE`;;

let ordinary_pack_make = new_definition
 `ordinary_pack_make (i,j) = (word (i + 256 * j):int32)`;;

let ordinary_pack_guard = new_definition
 `ordinary_pack_guard (i,j,i0,j0) =
    (word (i + 256 * j + 65536 * i0 + 16777216 * j0):int32)`;;

let ordinary_pack_guards = new_definition
 `ordinary_pack_guards gs = MAP ordinary_pack_guard gs`;;

let ordinary_pack_makes = new_definition
 `ordinary_pack_makes ms = MAP ordinary_pack_make ms`;;

let ordinary_rows = new_definition
 `ordinary_rows (ps:(int32 list) list) =
    list_of_seq (\i. (word (4 * i):int32)) (LENGTH ps + 1)`;;

let ordinary_premise_fields = new_definition
 `ordinary_premise_fields (ps:(int32 list) list) =
    list_of_seq (\k. EL (k MOD 4) (EL (k DIV 4) ps)) (4 * LENGTH ps)`;;

let ordinary_fields = new_definition
 `ordinary_fields ps cs = APPEND (ordinary_premise_fields ps) cs`;;

let ordinary_row_valid = new_definition
 `ordinary_row_valid (ps:(int32 list) list) (ars:num list) <=>
    LENGTH ars = LENGTH ps /\
    ALL (\p. LENGTH p = 4) ps /\ ALL (\a. a <= 4) ars`;;

let ordinary_make_valid = new_definition
 `ordinary_make_valid (ps:(int32 list) list) (ars:num list) (cs:int32 list) (i,j) <=>
    i <= LENGTH ps /\
    (i < LENGTH ps ==> j < EL i ars) /\
    (i = LENGTH ps ==> j < LENGTH cs)`;;

let ordinary_guard_valid = new_definition
 `ordinary_guard_valid ps ars cs (i,j,i0,j0) <=>
    ordinary_make_valid ps ars cs (i,j) /\
    ordinary_make_valid ps ars cs (i0,j0)`;;

let ordinary_valid = new_definition
 `ordinary_valid ps ars cs gs ms <=>
    ordinary_row_valid ps ars /\
    LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    LENGTH gs <= 32 /\ LENGTH ms <= 32 /\
    ALL (ordinary_guard_valid ps ars cs) gs /\
    ALL (ordinary_make_valid ps ars cs) ms`;;

let ordinary_arena_row = new_definition
 `ordinary_arena_row (source:int32 list) offset =
    list_of_seq (\j. EL (offset + j) source) 4`;;

let ordinary_arena_rows = new_definition
 `ordinary_arena_rows (source:int32 list) offsets =
    MAP (ordinary_arena_row source) offsets`;;

let ordinary_arena_offsets_valid = new_definition
 `ordinary_arena_offsets_valid (source:int32 list) offsets <=>
    ALL (\offset. offset + 4 <= LENGTH source) offsets`;;

let NATURAL_PACK2_PROJECTIONS = prove
 (`!i j. i < 256
      ==> (i + 256 * j) DIV 256 = j /\ (i + 256 * j) MOD 256 = i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `j:num` THEN ASM_ARITH_TAC]);;

let NATURAL_PACK4_PROJECTIONS = prove
 (`!i j i0 j0. i < 256 /\ j < 256 /\ i0 < 256
      ==> (i + 256 * j + 65536 * i0 + 16777216 * j0) DIV 256 =
            j + 256 * i0 + 65536 * j0 /\
          (i + 256 * j + 65536 * i0 + 16777216 * j0) MOD 256 = i /\
          (i + 256 * j + 65536 * i0 + 16777216 * j0) DIV 65536 =
            i0 + 256 * j0 /\
          (i + 256 * j + 65536 * i0 + 16777216 * j0) DIV 16777216 = j0 /\
          (j + 256 * i0 + 65536 * j0) MOD 256 = j`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `j + 256 * i0 + 65536 * j0` THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i + 256 * j` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i + 256 * j + 65536 * i0` THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i0 + 256 * j0` THEN ASM_ARITH_TAC]);;

let ORDINARY_PACK_MAKE_PROJECTIONS = prove
 (`!i j. i < 256 /\ j < 256
      ==> flat_i (ordinary_pack_make(i,j)) = i /\
          flat_j (ordinary_pack_make(i,j)) = j`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[flat_i; flat_j; ordinary_pack_make;
              ARITH_RULE `255 = 2 EXP 8 - 1`;
              VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR;
              VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(i + 256 * j) MOD 4294967296 = i + 256 * j`
    (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[NATURAL_PACK2_PROJECTIONS; MOD_LT]]);;

let ORDINARY_PACK_GUARD_PROJECTIONS = prove
 (`!i j i0 j0. i < 256 /\ j < 256 /\ i0 < 256 /\ j0 < 256
      ==> flat_i (ordinary_pack_guard(i,j,i0,j0)) = i /\
          flat_j (ordinary_pack_guard(i,j,i0,j0)) = j /\
          flat_i0 (ordinary_pack_guard(i,j,i0,j0)) = i0 /\
          flat_j0 (ordinary_pack_guard(i,j,i0,j0)) = j0`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[flat_i; flat_j; flat_i0; flat_j0; ordinary_pack_guard;
              ARITH_RULE `255 = 2 EXP 8 - 1`;
              VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR;
              VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
    `(i + 256 * j + 65536 * i0 + 16777216 * j0) MOD 4294967296 =
     i + 256 * j + 65536 * i0 + 16777216 * j0`
    (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(j + 256 * i0 + 65536 * j0) MOD 256 = j`
      ASSUME_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i0 + 256 * j0` THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[NATURAL_PACK4_PROJECTIONS; NATURAL_PACK2_PROJECTIONS]]]);;

let ORDINARY_ROWS_LENGTH = prove
 (`!ps. LENGTH(ordinary_rows ps) = LENGTH ps + 1`,
  REWRITE_TAC[ordinary_rows; LENGTH_LIST_OF_SEQ]);;

let ORDINARY_ROWS_EL = prove
 (`!ps i. i <= LENGTH ps ==> EL i (ordinary_rows ps) = word(4 * i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ordinary_rows] THEN
  MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_ARITH_TAC);;

let ORDINARY_ROWS_VAL = prove
 (`!ps i. LENGTH ps <= 24 /\ i <= LENGTH ps
      ==> val(EL i (ordinary_rows ps):int32) = 4 * i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EL i (ordinary_rows ps) = word(4 * i):int32`
    (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC ORDINARY_ROWS_EL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let ORDINARY_ARENA_ROW_LENGTH = prove
 (`!source offset. LENGTH(ordinary_arena_row source offset) = 4`,
  REWRITE_TAC[ordinary_arena_row; LENGTH_LIST_OF_SEQ]);;

let ORDINARY_ARENA_ROW_EL = prove
 (`!source offset j. j < 4
      ==> EL j (ordinary_arena_row source offset) = EL (offset + j) source`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ordinary_arena_row] THEN
  MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_REWRITE_TAC[]);;

let ORDINARY_ARENA_ROWS_EL = prove
 (`!source offsets i j. i < LENGTH offsets /\ j < 4
      ==> EL j (EL i (ordinary_arena_rows source offsets)) =
          EL (EL i offsets + j) source`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ordinary_arena_rows; EL_MAP; ORDINARY_ARENA_ROW_EL]);;

let ORDINARY_ARENA_ROW_VALID = prove
 (`!source offsets ars.
    LENGTH ars = LENGTH offsets /\ ALL (\a. a <= 4) ars
    ==> ordinary_row_valid (ordinary_arena_rows source offsets) ars`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ordinary_row_valid; ordinary_arena_rows; LENGTH_MAP; ALL_MAP; o_DEF] THEN
  ASM_SIMP_TAC[ORDINARY_ARENA_ROW_LENGTH; ALL_T]);;

let ORDINARY_ARENA_OFFSET_BOUND = prove
 (`!source offsets i.
    ordinary_arena_offsets_valid source offsets /\ i < LENGTH offsets
    ==> EL i offsets + 4 <= LENGTH source`,
  REWRITE_TAC[ordinary_arena_offsets_valid; GSYM ALL_EL] THEN MESON_TAC[]);;

let ORDINARY_ARENA_OFFSETS_CESTA = prove
 (`!source offsets.
    ordinary_arena_offsets_valid source offsets <=>
    ALL (\offset. offset <= LENGTH source /\
                  4 <= LENGTH source - offset) offsets`,
  REWRITE_TAC[ordinary_arena_offsets_valid;
    ARITH_RULE `!n offset. offset + 4 <= n <=>
                           offset <= n /\ 4 <= n - offset`]);;

let ORDINARY_FIELDS_LENGTH = prove
 (`!ps cs. LENGTH(ordinary_fields ps cs) = 4 * LENGTH ps + LENGTH cs`,
  REWRITE_TAC[ordinary_fields; ordinary_premise_fields;
              LENGTH_APPEND; LENGTH_LIST_OF_SEQ]);;

let ORDINARY_PREMISE_LENGTH = prove
 (`!ps ars i. ordinary_row_valid ps ars /\ i < LENGTH ps
      ==> LENGTH(EL i ps) = 4`,
  REWRITE_TAC[ordinary_row_valid; GSYM ALL_EL] THEN MESON_TAC[]);;

let ORDINARY_ARITY_BOUND = prove
 (`!ps ars i. ordinary_row_valid ps ars /\ i < LENGTH ps
      ==> EL i ars <= 4`,
  REWRITE_TAC[ordinary_row_valid; GSYM ALL_EL] THEN MESON_TAC[]);;

let ORDINARY_MAKE_BOUNDS = prove
 (`!ps ars cs i j.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    ordinary_make_valid ps ars cs (i,j)
    ==> i <= LENGTH ps /\ i < 256 /\ j < 256 /\
        4 * i + j < LENGTH(ordinary_fields ps cs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinary_make_valid] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i < LENGTH (ps:(int32 list) list)` THENL
   [SUBGOAL_THEN `j < EL i ars` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `EL i ars <= 4` ASSUME_TAC THENL
     [ASM_MESON_TAC[ORDINARY_ARITY_BOUND]; ALL_TAC] THEN
    REWRITE_TAC[ORDINARY_FIELDS_LENGTH] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `i = LENGTH (ps:(int32 list) list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `j < LENGTH (cs:int32 list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ORDINARY_FIELDS_LENGTH] THEN ASM_ARITH_TAC]);;

let ORDINARY_PREMISE_FIELDS_EL = prove
 (`!ps ars i j.
    ordinary_row_valid ps ars /\ i < LENGTH ps /\ j < 4
    ==> EL (4 * i + j) (ordinary_fields ps cs) = EL j (EL i ps)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ordinary_fields; EL_APPEND; ordinary_premise_fields;
              LENGTH_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `4 * i + j < 4 * LENGTH (ps:(int32 list) list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(4 * i + j) DIV 4 = i /\ (4 * i + j) MOD 4 = j`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4 * i + j < 4 * LENGTH (ps:(int32 list) list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[EL_LIST_OF_SEQ]]);;

let ORDINARY_CONSTANT_FIELDS_EL = prove
 (`!ps cs j. j < LENGTH cs
      ==> EL (4 * LENGTH ps + j) (ordinary_fields ps cs) = EL j cs`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ordinary_fields; EL_APPEND; ordinary_premise_fields;
              LENGTH_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `~(4 * LENGTH (ps:(int32 list) list) + j <
                 4 * LENGTH ps)` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_REWRITE_TAC[ARITH_RULE `!n j. (4 * n + j) - 4 * n = j`]]);;

let ORDINARY_OFFSET_COMPONENTS = prove
 (`!ps i j m.
    LENGTH ps <= 24 /\ i <= LENGTH ps /\ i < 256 /\ j < 256 /\
    flat_i m = i /\ flat_j m = j
    ==> flat_offset (ordinary_rows ps) m = 4 * i + j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(EL i (ordinary_rows ps):int32) = 4 * i` ASSUME_TAC THENL
   [MATCH_MP_TAC ORDINARY_ROWS_VAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `j < 2 EXP 32 /\ 4 * i + j < 2 EXP 32` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[flat_offset; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[MOD_LT]);;

let ORDINARY_OFFSET0_COMPONENTS = prove
 (`!ps i j g.
    LENGTH ps <= 24 /\ i <= LENGTH ps /\ i < 256 /\ j < 256 /\
    flat_i0 g = i /\ flat_j0 g = j
    ==> flat_offset0 (ordinary_rows ps) g = 4 * i + j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(EL i (ordinary_rows ps):int32) = 4 * i` ASSUME_TAC THENL
   [MATCH_MP_TAC ORDINARY_ROWS_VAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `j < 2 EXP 32 /\ 4 * i + j < 2 EXP 32` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[flat_offset0; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[MOD_LT]);;

let ORDINARY_PACKED_MAKE_OFFSET = prove
 (`!ps ars cs i j.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    ordinary_make_valid ps ars cs (i,j)
    ==> flat_offset (ordinary_rows ps) (ordinary_pack_make(i,j)) = 4 * i + j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i <= LENGTH (ps:(int32 list) list) /\ i < 256 /\ j < 256 /\
                4 * i + j < LENGTH(ordinary_fields ps cs)`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_MAKE_BOUNDS]; ALL_TAC] THEN
  MATCH_MP_TAC ORDINARY_OFFSET_COMPONENTS THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ORDINARY_PACK_MAKE_PROJECTIONS]);;

let ORDINARY_FIELDS_EL = prove
 (`!ps ars cs i j.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    ordinary_make_valid ps ars cs (i,j)
    ==> EL (4 * i + j) (ordinary_fields ps cs) = ordinary_field ps cs (i,j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinary_make_valid] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i < LENGTH (ps:(int32 list) list)` THENL
   [SUBGOAL_THEN `j < EL i ars` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `EL i ars <= 4` ASSUME_TAC THENL
     [ASM_MESON_TAC[ORDINARY_ARITY_BOUND]; ALL_TAC] THEN
    SUBGOAL_THEN `j < 4` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ordinary_field; ordinary_row] THEN
    MATCH_MP_TAC ORDINARY_PREMISE_FIELDS_EL THEN
    ASM_MESON_TAC[ordinary_row_valid];
    SUBGOAL_THEN `i = LENGTH (ps:(int32 list) list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `j < LENGTH (cs:int32 list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ordinary_field; ordinary_row; LT_REFL] THEN
    MATCH_MP_TAC ORDINARY_CONSTANT_FIELDS_EL THEN ASM_REWRITE_TAC[]]);;

let ORDINARY_PACKED_MAKE_FIELD = prove
 (`!ps ars cs i j.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    ordinary_make_valid ps ars cs (i,j)
    ==> flat_field (ordinary_fields ps cs) (ordinary_rows ps)
          (ordinary_pack_make(i,j)) = ordinary_field ps cs (i,j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[flat_field] THEN
  SUBGOAL_THEN
    `flat_offset (ordinary_rows ps) (ordinary_pack_make(i,j)) = 4 * i + j`
    (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC ORDINARY_PACKED_MAKE_OFFSET THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ORDINARY_FIELDS_EL THEN ASM_MESON_TAC[]);;

let ORDINARY_PACKED_GUARD_OFFSET = prove
 (`!ps ars cs i j i0 j0.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    ordinary_guard_valid ps ars cs (i,j,i0,j0)
    ==> flat_offset (ordinary_rows ps) (ordinary_pack_guard(i,j,i0,j0)) =
          4 * i + j /\
        flat_offset0 (ordinary_rows ps) (ordinary_pack_guard(i,j,i0,j0)) =
          4 * i0 + j0`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
    `ordinary_make_valid ps ars cs (i,j) /\
     ordinary_make_valid ps ars cs (i0,j0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ordinary_guard_valid]; ALL_TAC] THEN
  SUBGOAL_THEN `i <= LENGTH (ps:(int32 list) list) /\ i < 256 /\ j < 256` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_MAKE_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `i0 <= LENGTH (ps:(int32 list) list) /\ i0 < 256 /\ j0 < 256` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_MAKE_BOUNDS]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ORDINARY_OFFSET_COMPONENTS;
    MATCH_MP_TAC ORDINARY_OFFSET0_COMPONENTS] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ORDINARY_PACK_GUARD_PROJECTIONS]);;

let ORDINARY_PACKED_GUARD_FIELD = prove
 (`!ps ars cs g.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    ordinary_guard_valid ps ars cs g
    ==> (flat_guard_holds (ordinary_fields ps cs) (ordinary_rows ps)
          (ordinary_pack_guard g) <=> ordinary_guard_holds ps cs g)`,
  REWRITE_TAC[FORALL_PAIR_THM; ordinary_guard_valid] THEN
  INTRO_TAC "![ps] [ars] [cs] [i] [j] [i0] [j0]" THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `flat_offset (ordinary_rows ps) (ordinary_pack_guard(i,j,i0,j0)) =
       4 * i + j /\
     flat_offset0 (ordinary_rows ps) (ordinary_pack_guard(i,j,i0,j0)) =
       4 * i0 + j0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC (ISPECL
      [`ps:(int32 list) list`; `ars:num list`; `cs:int32 list`;
       `i:num`; `j:num`; `i0:num`; `j0:num`]
      ORDINARY_PACKED_GUARD_OFFSET) THEN
    ASM_REWRITE_TAC[ordinary_guard_valid]; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL (4 * i + j) (ordinary_fields ps cs) = ordinary_field ps cs (i,j) /\
     EL (4 * i0 + j0) (ordinary_fields ps cs) = ordinary_field ps cs (i0,j0)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC (ISPECL
        [`ps:(int32 list) list`; `ars:num list`; `cs:int32 list`;
         `i:num`; `j:num`] ORDINARY_FIELDS_EL) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC (ISPECL
        [`ps:(int32 list) list`; `ars:num list`; `cs:int32 list`;
         `i0:num`; `j0:num`] ORDINARY_FIELDS_EL) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[flat_guard_holds; ordinary_guard_holds]);;

let ORDINARY_PACKED_MAKE_VALID = prove
 (`!ps ars cs m.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    ordinary_make_valid ps ars cs m
    ==> flat_make_valid (ordinary_fields ps cs) (ordinary_rows ps)
          (ordinary_pack_make m)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  INTRO_TAC "![ps] [ars] [cs] [i] [j]" THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `flat_offset (ordinary_rows ps) (ordinary_pack_make(i,j)) = 4 * i + j`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ORDINARY_PACKED_MAKE_OFFSET THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `i <= LENGTH (ps:(int32 list) list) /\ i < 256 /\ j < 256 /\
                4 * i + j < LENGTH(ordinary_fields ps cs)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_MAKE_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `flat_i (ordinary_pack_make(i,j)) = i` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_PACK_MAKE_PROJECTIONS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[flat_make_valid; ORDINARY_ROWS_LENGTH] THEN ASM_ARITH_TAC);;

let ORDINARY_PACKED_GUARD_VALID = prove
 (`!ps ars cs g.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    ordinary_guard_valid ps ars cs g
    ==> flat_guard_valid (ordinary_fields ps cs) (ordinary_rows ps)
          (ordinary_pack_guard g)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  INTRO_TAC "![ps] [ars] [cs] [i] [j] [i0] [j0]" THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `flat_offset (ordinary_rows ps) (ordinary_pack_guard(i,j,i0,j0)) =
       4 * i + j /\
     flat_offset0 (ordinary_rows ps) (ordinary_pack_guard(i,j,i0,j0)) =
       4 * i0 + j0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ORDINARY_PACKED_GUARD_OFFSET THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `ordinary_make_valid ps ars cs (i,j) /\
     ordinary_make_valid ps ars cs (i0,j0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ordinary_guard_valid]; ALL_TAC] THEN
  SUBGOAL_THEN `i <= LENGTH (ps:(int32 list) list) /\ i < 256 /\ j < 256 /\
                4 * i + j < LENGTH(ordinary_fields ps cs)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_MAKE_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `i0 <= LENGTH (ps:(int32 list) list) /\ i0 < 256 /\ j0 < 256 /\
                4 * i0 + j0 < LENGTH(ordinary_fields ps cs)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_MAKE_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `flat_i (ordinary_pack_guard(i,j,i0,j0)) = i /\
                flat_i0 (ordinary_pack_guard(i,j,i0,j0)) = i0`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_PACK_GUARD_PROJECTIONS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[flat_guard_valid; ORDINARY_ROWS_LENGTH] THEN ASM_ARITH_TAC);;

let ORDINARY_PACKED_VALID = prove
 (`!ps ars cs gs ms. ordinary_valid ps ars cs gs ms
    ==> flat_valid (ordinary_fields ps cs) (ordinary_rows ps)
          (ordinary_pack_guards gs) (ordinary_pack_makes ms)`,
  REWRITE_TAC[ordinary_valid] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[flat_valid; ordinary_pack_guards; ordinary_pack_makes;
              ALL_MAP; o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `ordinary_guard_valid ps ars cs` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      MATCH_MP_TAC (ISPECL
        [`ps:(int32 list) list`; `ars:num list`; `cs:int32 list`;
         `x:(num#num#num#num)`] ORDINARY_PACKED_GUARD_VALID) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC `ordinary_make_valid ps ars cs` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      MATCH_MP_TAC (ISPECL
        [`ps:(int32 list) list`; `ars:num list`; `cs:int32 list`;
         `x:(num#num)`] ORDINARY_PACKED_MAKE_VALID) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

let ORDINARY_PACKED_GUARDS_HOLD = prove
 (`!ps ars cs gs.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32
    ==> ALL (ordinary_guard_valid ps ars cs) gs
    ==> flat_guards_hold (ordinary_fields ps cs) (ordinary_rows ps)
          (ordinary_pack_guards gs) = ordinary_guards_hold ps cs gs`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[flat_guards_hold; ordinary_guards_hold;
              ordinary_pack_guards; ALL_MAP; o_THM] THEN
  SPEC_TAC(`gs:(num#num#num#num) list`,`gs:(num#num#num#num) list`) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; ALL];
    REWRITE_TAC[MAP; ALL] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN
      `(ALL (flat_guard_holds (ordinary_fields ps cs) (ordinary_rows ps) o
             ordinary_pack_guard) t <=> ALL (ordinary_guard_holds ps cs) t)`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN
      `flat_guard_holds (ordinary_fields ps cs) (ordinary_rows ps)
         (ordinary_pack_guard h) <=> ordinary_guard_holds ps cs h`
      ASSUME_TAC THENL
     [MATCH_MP_TAC (ISPECL
        [`ps:(int32 list) list`; `ars:num list`; `cs:int32 list`;
         `h:(num#num#num#num)`] ORDINARY_PACKED_GUARD_FIELD) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

let ORDINARY_PACKED_SELECTED = prove
 (`!ps ars cs ms.
    ordinary_row_valid ps ars /\ LENGTH ps <= 24 /\ LENGTH cs <= 32 /\
    ALL (ordinary_make_valid ps ars cs) ms
    ==> flat_selected (ordinary_fields ps cs) (ordinary_rows ps)
          (ordinary_pack_makes ms) = ordinary_selected ps cs ms`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[flat_selected; ordinary_selected; ordinary_pack_makes;
              GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[o_THM] THEN MATCH_MP_TAC ALL_IMP THEN
  EXISTS_TAC `ordinary_make_valid ps ars cs` THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_MESON_TAC[REWRITE_RULE[PAIR] (SPECL
      [`ps:(int32 list) list`; `ars:num list`; `cs:int32 list`;
       `FST (x:(num#num))`; `SND (x:(num#num))`]
      ORDINARY_PACKED_MAKE_FIELD)];
    ASM_REWRITE_TAC[]]);;

let ORDINARY_FIRE_REFINEMENT = prove
 (`!ps ars cs gs ms. ordinary_valid ps ars cs gs ms
    ==> (if flat_guards_hold (ordinary_fields ps cs) (ordinary_rows ps)
             (ordinary_pack_guards gs)
         then SOME(flat_selected (ordinary_fields ps cs) (ordinary_rows ps)
                     (ordinary_pack_makes ms))
         else NONE) = ordinary_fire_spec ps cs gs ms`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ordinary_valid]) THEN
  REWRITE_TAC[ordinary_fire_spec] THEN
  SUBGOAL_THEN
    `flat_guards_hold (ordinary_fields ps cs) (ordinary_rows ps)
       (ordinary_pack_guards gs) = ordinary_guards_hold ps cs gs`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[ORDINARY_PACKED_GUARDS_HOLD]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC (ISPECL
    [`ps:(int32 list) list`; `ars:num list`; `cs:int32 list`;
     `ms:(num#num) list`] ORDINARY_PACKED_SELECTED) THEN ASM_REWRITE_TAC[]);;

let ORDINARY_WROW_INDEX_NONWRAP = prove
 (`!r j. r < 2 EXP 28 /\ j < 4
      ==> val(word(4 * r + j):int32) = 4 * r + j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

