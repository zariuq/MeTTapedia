(* Exact linked-byte successful packing proof for ordinary_flat_pack. *)

let FLAT_WORDLIST_SPLICE_32 = prove
 (`!a (old:int32 list) (new:int32 list) k s t.
    k < LENGTH old /\ k < LENGTH new /\
    (wordlist_from_memory(a,k) s:int32 list) = flat_prefix k new /\
    (wordlist_from_memory(word_add a (word(4 * k)),LENGTH old - k) s:int32 list) =
      ordinary_drop k old /\
    (wordlist_from_memory(a,k) t:int32 list) = wordlist_from_memory(a,k) s /\
    (wordlist_from_memory
      (word_add a (word(4 * (k + 1))),LENGTH old - (k + 1)) t:int32 list) =
    wordlist_from_memory
      (word_add a (word(4 * (k + 1))),LENGTH old - (k + 1)) s /\
    read (memory :> bytes32 (word_add a (word(4 * k)))) t = EL k new
      ==> (wordlist_from_memory(a,k + 1) t:int32 list) = flat_prefix (k + 1) new /\
          (wordlist_from_memory
            (word_add a (word(4 * (k + 1))),LENGTH old - (k + 1)) t:int32 list) =
          ordinary_drop (k + 1) old`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`a:int64`; `k:num`; `new:int32 list`; `s:x86state`;
      `t:x86state`] FLAT_WORDLIST_PREFIX_32) THEN
    ASM_REWRITE_TAC[ADD1];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < LENGTH(old:int32 list) - k` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `TL(ordinary_drop k (old:int32 list)) = ordinary_drop (k + 1) old`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `ordinary_drop k (old:int32 list) =
        CONS (EL k old) (ordinary_drop (k + 1) old)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC ORDINARY_DROP_SUC_EL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[TL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add a (word(4 * k)):int64`;
    `LENGTH(old:int32 list) - k`; `s:x86state`]
    WORDLIST_FROM_MEMORY_TAIL_32) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_add (word_add a (word(4 * k))) (word 4) =
      word_add a (word(4 * (k + 1))):int64 /\
    LENGTH(old:int32 list) - k - 1 = LENGTH old - (k + 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC;
                  ARITH_RULE `4 * (k + 1) = 4 * k + 4`;
                  GSYM WORD_ADD];
      ASM_ARITH_TAC]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let ORDINARY_PACK_RESULT_FIELDS_LENGTH = prove
 (`!source offsets constants fields.
    4 * LENGTH offsets + LENGTH constants <= LENGTH fields
      ==> LENGTH(ordinary_pack_result_fields source offsets constants fields) =
          LENGTH fields`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ordinary_pack_result_fields; LENGTH_APPEND;
              ORDINARY_FIELDS_LENGTH; LENGTH_ORDINARY_DROP;
              ordinary_arena_rows; LENGTH_MAP] THEN
  ASM_ARITH_TAC);;

let ORDINARY_PACK_RESULT_ROWS_LENGTH = prove
 (`!source offsets rows.
    LENGTH offsets + 1 <= LENGTH rows
      ==> LENGTH(ordinary_pack_result_rows source offsets rows) = LENGTH rows`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ordinary_pack_result_rows; LENGTH_APPEND;
              ORDINARY_ROWS_LENGTH; LENGTH_ORDINARY_DROP;
              ordinary_arena_rows; LENGTH_MAP] THEN
  ASM_ARITH_TAC);;

let ORDINARY_PACK_RESULT_PREMISE_EL = prove
 (`!source offsets constants fields i j.
    i < LENGTH offsets /\ j < 4 /\
    4 * LENGTH offsets + LENGTH constants <= LENGTH fields
      ==> EL (4 * i + j)
            (ordinary_pack_result_fields source offsets constants fields) =
          EL (val(EL i offsets:int32) + j) source`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4 * i + j < 4 * LENGTH(offsets:int32 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(4 * i + j) DIV 4 = i /\ (4 * i + j) MOD 4 = j`
  STRIP_ASSUME_TAC THENL [MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `4 * i + j < 4 * LENGTH(offsets:int32 list) + LENGTH(constants:int32 list)`
  ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ordinary_pack_result_fields; EL_APPEND; ORDINARY_FIELDS_LENGTH;
              ordinary_arena_rows; LENGTH_MAP] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[ordinary_fields; EL_APPEND; ordinary_premise_fields;
              LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; ordinary_arena_rows; EL_MAP; LENGTH_MAP;
               ORDINARY_ARENA_ROW_EL]);;

let ORDINARY_PACK_RESULT_CONSTANT_EL = prove
 (`!source offsets constants fields j.
    j < LENGTH constants /\
    4 * LENGTH offsets + LENGTH constants <= LENGTH fields
      ==> EL (4 * LENGTH offsets + j)
            (ordinary_pack_result_fields source offsets constants fields) =
          EL j constants`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `4 * LENGTH(offsets:int32 list) + j <
      4 * LENGTH offsets + LENGTH(constants:int32 list)`
  ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ordinary_pack_result_fields; EL_APPEND; ORDINARY_FIELDS_LENGTH;
              ordinary_arena_rows; LENGTH_MAP] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[ordinary_fields; EL_APPEND; ordinary_premise_fields;
              LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[LENGTH_MAP; ARITH_RULE `~(4 * n + j < 4 * n)`;
               ARITH_RULE `(4 * n + j) - 4 * n = j`]);;

let ORDINARY_PACK_RESULT_ROW_EL = prove
 (`!source offsets rows i.
    i <= LENGTH offsets /\ LENGTH offsets + 1 <= LENGTH rows
      ==> EL i (ordinary_pack_result_rows source offsets rows) = word(4 * i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH(offsets:int32 list) + 1` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ordinary_pack_result_rows; EL_APPEND; ORDINARY_ROWS_LENGTH;
              ordinary_arena_rows; LENGTH_MAP] THEN
  ASM_SIMP_TAC[ORDINARY_ROWS_EL; LENGTH_MAP]);;
