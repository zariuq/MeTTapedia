(* Generic 32-bit workspace prefixes, suffixes, and wordlist decomposition. *)

let FLAT_PREFIX_APPEND_LEFT = prove
 (`!xs ys. flat_prefix (LENGTH xs) (APPEND xs ys) = xs`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; flat_prefix; APPEND; NOT_CONS_NIL; HD; TL] THEN
  ASM_REWRITE_TAC[]);;

let ORDINARY_DROP_APPEND_LEFT = prove
 (`!(xs:A list) ys. ordinary_drop (LENGTH xs) (APPEND xs ys) = ys`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ordinary_drop; APPEND; NOT_CONS_NIL; HD; TL] THEN
  ASM_REWRITE_TAC[]);;

let FLAT_PREFIX_DROP = prove
 (`!(l:int32 list) k. k <= LENGTH l
      ==> APPEND (flat_prefix k l) (ordinary_drop k l) = l`,
  LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; flat_prefix; ordinary_drop; APPEND; NOT_CONS_NIL;
               HD; TL; LE; LE_SUC]);;

let LENGTH_FLAT_PREFIX = prove
 (`!(l:int32 list) k. k <= LENGTH l ==> LENGTH(flat_prefix k l) = k`,
  LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; flat_prefix; NOT_CONS_NIL; HD; TL; LE; LE_SUC]);;

let ORDINARY_DROP_SUC_EL = prove
 (`!(l:A list) k. k < LENGTH l
      ==> ordinary_drop k l = CONS (EL k l) (ordinary_drop (k + 1) l)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THENL
   [LIST_INDUCT_TAC THENL
     [REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[LENGTH; GSYM ADD1; ONE; ordinary_drop;
                  NOT_CONS_NIL; EL; HD; TL]];
    FIRST_X_ASSUM(LABEL_TAC "ih") THEN LIST_INDUCT_TAC THENL
     [REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[LENGTH; LT_SUC] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `ordinary_drop (SUC k) (CONS (h:A) t) = ordinary_drop k t /\
        EL (SUC k) (CONS h t) = EL k t /\
        ordinary_drop (SUC k + 1) (CONS h t) = ordinary_drop (k + 1) t`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [REWRITE_TAC[ordinary_drop; NOT_CONS_NIL; TL];
          REWRITE_TAC[EL; TL];
          REWRITE_TAC[ARITH_RULE `SUC k + 1 = SUC(k + 1)`;
                      ordinary_drop; NOT_CONS_NIL; TL]];
        ASM_MESON_TAC[]]]]);;

let WORDLIST_EL_32 = prove
 (`!a n s i. i < n
      ==> EL i (wordlist_from_memory(a,n) s:int32 list) =
          read (memory :> bytes32 (word_add a (word(4 * i)))) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`wordlist_from_memory(a,n) s:int32 list`;
    `a:int64`; `s:x86state`; `i:num`] FLAT_READ) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; EQ_SYM_EQ]);;

let WORDLIST_READS_32 = prove
 (`!a (xs:int32 list) s.
    wordlist_from_memory(a,LENGTH xs) s = xs
      ==> !i. i < LENGTH xs
              ==> read (memory :> bytes32 (word_add a (word(4 * i)))) s =
                    EL i xs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]);;

let WORDLIST_FROM_MEMORY_SPLIT_32 = prove
 (`!a k n s. k <= n
      ==> wordlist_from_memory(a,n) s : int32 list =
          APPEND (wordlist_from_memory(a,k) s)
            (wordlist_from_memory(word_add a (word(4 * k)),n - k) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_WORDLIST_FROM_MEMORY;
    LENGTH_APPEND] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY] THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < n:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `EL i (wordlist_from_memory(a,n) s:int32 list) =
      read (memory :> bytes32 (word_add a (word(4 * i)))) s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WORDLIST_EL_32 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i < k:num` THENL
   [SUBGOAL_THEN
     `EL i (wordlist_from_memory(a,k) s:int32 list) =
        read (memory :> bytes32 (word_add a (word(4 * i)))) s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC WORDLIST_EL_32 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_APPEND; LENGTH_WORDLIST_FROM_MEMORY];
    SUBGOAL_THEN `i - k < n - k:num` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `EL (i - k) (wordlist_from_memory(word_add a (word(4 * k)),n - k) s:int32 list) =
        read (memory :> bytes32
          (word_add (word_add a (word(4 * k))) (word(4 * (i - k))))) s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC WORDLIST_EL_32 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `4 * k + 4 * (i - k) = 4 * i` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add a (word(4 * k))) (word(4 * (i - k))) =
        word_add a (word(4 * i)):int64`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[EL_APPEND; LENGTH_WORDLIST_FROM_MEMORY] THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(i < k) ==> i - k + k = i`]]);;

let WORDLIST_FROM_MEMORY_TAIL_32 = prove
 (`!a n s. 0 < n
      ==> TL(wordlist_from_memory(a,n) s:int32 list) =
          wordlist_from_memory(word_add a (word 4),n - 1) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_WORDLIST_FROM_MEMORY] THEN
  SUBGOAL_THEN `LENGTH(TL(wordlist_from_memory(a,n) s:int32 list)) = n - 1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(wordlist_from_memory(a,n) s:int32 list = [])` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_WORDLIST_FROM_MEMORY] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `wordlist_from_memory(a,n) s:int32 list` LENGTH_TL) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EL_TL] THEN
  SUBGOAL_THEN `i + 1 < n:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `i + 1:num`; `s:x86state`]
    (INST_TYPE [`:4`,`:N`] EL_WORDLIST_FROM_MEMORY)) THEN
  ASM_REWRITE_TAC[DIMINDEX_4] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`word_add a (word 4):int64`; `n - 1:num`; `i:num`;
    `s:x86state`] (INST_TYPE [`:4`,`:N`] EL_WORDLIST_FROM_MEMORY)) THEN
  ASM_REWRITE_TAC[DIMINDEX_4] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(word_add (a:int64) (word(4 * (i + 1)):int64):int64) =
    (word_add (word_add a (word 4:int64)) (word(4 * i):int64):int64)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                ARITH_RULE `4 * (i + 1) = 4 + 4 * i`];
    ASM_REWRITE_TAC[]]);;

let LENGTH_ORDINARY_DROP = prove
 (`!(l:A list) n. LENGTH(ordinary_drop n l) = LENGTH l - n`,
  LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; ordinary_drop; NOT_CONS_NIL; TL; SUB_0; SUB_SUC;
               GSYM ADD1; ONE]);;

let WORDLIST_PREFIX_32 = prove
 (`!a k (xs:int32 list) s.
    k <= LENGTH xs /\ wordlist_from_memory(a,LENGTH xs) s = xs
    ==> wordlist_from_memory(a,k) s = flat_prefix k xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `k:num`; `LENGTH(xs:int32 list)`; `s:x86state`]
    WORDLIST_FROM_MEMORY_SPLIT_32) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN ASSUME_TAC THEN
  MP_TAC(ISPECL [`wordlist_from_memory(a,k) s:int32 list`;
    `wordlist_from_memory(word_add a (word(4 * k)),LENGTH(xs:int32 list) - k) s:int32 list`]
    FLAT_PREFIX_APPEND_LEFT) THEN
  REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  DISCH_THEN (ACCEPT_TAC o SYM));;

let FLAT_FULL_OUTPUT_LENGTH = prove
 (`!fs rs gs ms (ds:int32 list).
    LENGTH ms <= LENGTH ds
    ==> LENGTH(APPEND
         (if flat_guards_hold fs rs gs then flat_selected fs rs ms
          else flat_prefix (LENGTH ms) ds)
         (ordinary_drop (LENGTH ms) ds)) = LENGTH ds`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH(flat_prefix (LENGTH(ms:int32 list)) (ds:int32 list)) = LENGTH ms`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_FLAT_PREFIX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `flat_guards_hold fs rs gs` THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_ORDINARY_DROP; flat_selected; LENGTH_MAP] THEN
  ASM_ARITH_TAC);;

let FLAT_OUTPUT_PREFIX_LENGTH = prove
 (`!fs rs gs ms (ds:int32 list).
    LENGTH ms <= LENGTH ds
    ==> LENGTH
         (if flat_guards_hold fs rs gs then flat_selected fs rs ms
          else flat_prefix (LENGTH ms) ds) = LENGTH ms`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `flat_guards_hold fs rs gs` THEN
  ASM_SIMP_TAC[flat_selected; LENGTH_MAP; LENGTH_FLAT_PREFIX]);;

let FLAT_WORDLIST_OUTPUT_PREFIX = prove
 (`!fs rs gs ms (ds:int32 list) (dest:int64) s.
    LENGTH ms <= LENGTH ds /\
    wordlist_from_memory
      (dest,LENGTH
        (if flat_guards_hold fs rs gs then flat_selected fs rs ms
         else flat_prefix (LENGTH ms) ds)) s =
      (if flat_guards_hold fs rs gs then flat_selected fs rs ms
       else flat_prefix (LENGTH ms) ds)
    ==> wordlist_from_memory(dest,LENGTH ms) s =
      (if flat_guards_hold fs rs gs then flat_selected fs rs ms
       else flat_prefix (LENGTH ms) ds)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH
     (if flat_guards_hold fs rs gs then flat_selected fs rs ms
      else flat_prefix (LENGTH(ms:int32 list)) ds) = LENGTH ms`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FLAT_OUTPUT_PREFIX_LENGTH THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun len -> FIRST_X_ASSUM(fun h ->
      ACCEPT_TAC(REWRITE_RULE[len] h)))]);;

let FLAT_ORTHOGONAL_BYTES = prove
 (`!(a:int64) k b j.
    nonoverlapping (a,k) (b,j)
    ==> orthogonal_components (memory :> bytes(a,k)) (memory :> bytes(b,j))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN
  CONJ_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV;
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; GSYM nonoverlapping] THEN
    ASM_REWRITE_TAC[]]);;

let FLAT_ORTHOGONAL_COMPONENTS_SYM = prove
 (`!c:(x86state,A)component d:(x86state,B)component.
    orthogonal_components c d ==> orthogonal_components d c`,
  REWRITE_TAC[orthogonal_components] THEN MESON_TAC[]);;

let FLAT_READ_OVER_WRITE_ORTHOGONAL_TAC =
  let tac_orth = (MATCH_MP_TAC o prove)
   (`orthogonal_components (c:(x86state,A)component) (d:(x86state,B)component) /\
     read c (s':x86state) = read c s
     ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]) in
  let rec tac g =
   (REFL_TAC ORELSE
    (tac_orth THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC ORELSE
      (MATCH_MP_TAC FLAT_ORTHOGONAL_COMPONENTS_SYM THEN
       FIRST_ASSUM ACCEPT_TAC) ORELSE ORTHOGONAL_COMPONENTS_TAC ORELSE
      (MATCH_MP_TAC FLAT_ORTHOGONAL_BYTES THEN NONOVERLAPPING_TAC); tac])) g in
  tac;;

let WORDLIST_FULL_SPLICE_32 = prove
 (`!a k (xs:int32 list) ys s t.
    k <= LENGTH xs /\
    wordlist_from_memory(a,LENGTH xs) s = xs /\
    wordlist_from_memory(a,k) t = ys /\
    wordlist_from_memory(word_add a (word(4 * k)),LENGTH(xs:int32 list) - k) t : int32 list =
      wordlist_from_memory(word_add a (word(4 * k)),LENGTH(xs:int32 list) - k) s
    ==> wordlist_from_memory(a,LENGTH xs) t =
          APPEND ys (ordinary_drop k xs)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `k:num`; `LENGTH(xs:int32 list)`; `t:x86state`]
    WORDLIST_FROM_MEMORY_SPLIT_32) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `k:num`; `LENGTH(xs:int32 list)`; `s:x86state`]
    WORDLIST_FROM_MEMORY_SPLIT_32) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN ASSUME_TAC THEN
  SUBGOAL_THEN
   `ordinary_drop k (xs:int32 list) =
      wordlist_from_memory(word_add a (word(4 * k)),LENGTH(xs:int32 list) - k) s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`wordlist_from_memory(a,k) s:int32 list`;
      `wordlist_from_memory(word_add a (word(4 * k)),LENGTH(xs:int32 list) - k) s:int32 list`]
      ORDINARY_DROP_APPEND_LEFT) THEN
    REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
