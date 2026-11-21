(* Accumulated full-workspace safety across a tight-prefix leaf execution. *)

let FLAT_TRACE_REGION_TAC =
  REPEAT ((DISJ1_TAC THEN
    (MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL ORELSE
     (MATCH_MP_TAC CESTA_CONTAINED_PREFIX THEN ASM_ARITH_TAC))) ORELSE
   DISJ2_TAC) THEN
  (MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL ORELSE
   (MATCH_MP_TAC CESTA_CONTAINED_PREFIX THEN ASM_ARITH_TAC));;

let FLAT_TRACE_APPEND_FULL = prove
 (`!e (e2:uarch_event list) (e3:uarch_event list)
      fields rows guards make dest scratch
      (fs:int32 list) (rs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) stackpointer s0 s1.
    LENGTH ms <= LENGTH ds /\ LENGTH ms <= LENGTH zs /\
    val dest + 4 * LENGTH ds <= 2 EXP 64 /\
    val scratch + 4 * LENGTH zs <= 2 EXP 64 /\
    read events s0 = APPEND e2 e /\
    memaccess_inbounds e2
      [fields,4 * LENGTH fs; rows,4 * LENGTH rs;
       guards,4 * LENGTH gs; make,4 * LENGTH ms;
       dest,4 * LENGTH ds; scratch,4 * LENGTH zs;
       word_sub stackpointer (word 48),72]
      [dest,4 * LENGTH ms; scratch,4 * LENGTH ms;
       word_sub stackpointer (word 48),48] /\
    read events s1 = APPEND e3 (read events s0) /\
    memaccess_inbounds e3
      [fields,4 * LENGTH fs; rows,4 * LENGTH rs;
       guards,4 * LENGTH gs; make,4 * LENGTH ms;
       dest,4 * LENGTH ms; scratch,4 * LENGTH ms;
       word_sub stackpointer (word 48),72]
      [dest,4 * LENGTH ms; scratch,4 * LENGTH ms;
       word_sub stackpointer (word 48),48]
    ==> flat_trace e fields rows guards make dest scratch fs rs gs ms ds zs
          stackpointer s1`,
  REWRITE_TAC[flat_trace] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LENGTH_FLAT_PREFIX] THEN
  EXISTS_TAC `APPEND e3 e2:uarch_event list` THEN
  ASM_REWRITE_TAC[APPEND_ASSOC; MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (ISPECL
    [`e3:uarch_event list`;
     `[(fields:int64),4 * LENGTH(fs:int32 list);
       (rows:int64),4 * LENGTH(rs:int32 list);
       (guards:int64),4 * LENGTH(gs:int32 list);
       (make:int64),4 * LENGTH(ms:int32 list);
       (dest:int64),4 * LENGTH ms;
       (scratch:int64),4 * LENGTH ms;
       word_sub (stackpointer:int64) (word 48),72]`;
     `[(fields:int64),4 * LENGTH(fs:int32 list);
       (rows:int64),4 * LENGTH(rs:int32 list);
       (guards:int64),4 * LENGTH(gs:int32 list);
       (make:int64),4 * LENGTH(ms:int32 list);
       (dest:int64),4 * LENGTH(ds:int32 list);
       (scratch:int64),4 * LENGTH(zs:int32 list);
       word_sub (stackpointer:int64) (word 48),72]`;
     `[(dest:int64),4 * LENGTH(ms:int32 list);
       (scratch:int64),4 * LENGTH ms;
       word_sub (stackpointer:int64) (word 48),48]`;
     `[(dest:int64),4 * LENGTH(ms:int32 list);
       (scratch:int64),4 * LENGTH ms;
       word_sub (stackpointer:int64) (word 48),48]`]
    MEMACCESS_INBOUNDS_CONTAINED)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ALL; EX] THEN REPEAT CONJ_TAC THEN FLAT_TRACE_REGION_TAC;
    ASM_REWRITE_TAC[]]);;

let FLAT_TRACE_WIDEN_FULL = prove
 (`!e fields rows guards make dest scratch
      (fs:int32 list) (rs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) stackpointer s.
    LENGTH ms <= LENGTH ds /\ LENGTH ms <= LENGTH zs /\
    val dest + 4 * LENGTH ds <= 2 EXP 64 /\
    val scratch + 4 * LENGTH zs <= 2 EXP 64 /\
    flat_trace e fields rows guards make dest scratch fs rs gs ms
      (flat_prefix (LENGTH ms) ds) (flat_prefix (LENGTH ms) zs) stackpointer s
    ==> flat_trace e fields rows guards make dest scratch fs rs gs ms ds zs
          stackpointer s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_trace]) THEN
  REPEAT STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN
   `LENGTH(flat_prefix (LENGTH(ms:int32 list)) (ds:int32 list)) = LENGTH ms /\
    LENGTH(flat_prefix (LENGTH(ms:int32 list)) (zs:int32 list)) = LENGTH ms`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 th; CONJUNCT2 th])) THENL
   [CONJ_TAC THEN MATCH_MP_TAC LENGTH_FLAT_PREFIX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[flat_trace] THEN
  EXISTS_TAC `e2:uarch_event list` THEN
  ASM_SIMP_TAC[LENGTH_FLAT_PREFIX] THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (ISPECL
    [`e2:uarch_event list`;
     `[(fields:int64),4 * LENGTH(fs:int32 list);
       (rows:int64),4 * LENGTH(rs:int32 list);
       (guards:int64),4 * LENGTH(gs:int32 list);
       (make:int64),4 * LENGTH(ms:int32 list);
       (dest:int64),4 * LENGTH ms;
       (scratch:int64),4 * LENGTH ms;
       word_sub (stackpointer:int64) (word 48),72]`;
     `[(fields:int64),4 * LENGTH(fs:int32 list);
       (rows:int64),4 * LENGTH(rs:int32 list);
       (guards:int64),4 * LENGTH(gs:int32 list);
       (make:int64),4 * LENGTH(ms:int32 list);
       (dest:int64),4 * LENGTH(ds:int32 list);
       (scratch:int64),4 * LENGTH(zs:int32 list);
       word_sub (stackpointer:int64) (word 48),72]`;
     `[(dest:int64),4 * LENGTH(ms:int32 list);
       (scratch:int64),4 * LENGTH ms;
       word_sub (stackpointer:int64) (word 48),48]`;
     `[(dest:int64),4 * LENGTH(ms:int32 list);
       (scratch:int64),4 * LENGTH ms;
       word_sub (stackpointer:int64) (word 48),48]`]
    MEMACCESS_INBOUNDS_CONTAINED)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ALL; EX] THEN REPEAT CONJ_TAC THEN FLAT_TRACE_REGION_TAC;
    ASM_REWRITE_TAC[]]);;

let FLAT_TRACE_COMPOSE_FULL = prove
 (`!e fields rows guards make dest scratch
      (fs:int32 list) (rs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) stackpointer s0 s1.
    LENGTH ms <= LENGTH ds /\ LENGTH ms <= LENGTH zs /\
    val dest + 4 * LENGTH ds <= 2 EXP 64 /\
    val scratch + 4 * LENGTH zs <= 2 EXP 64 /\
    flat_trace e fields rows guards make dest scratch fs rs gs ms ds zs
      stackpointer s0 /\
    flat_trace (read events s0) fields rows guards make dest scratch fs rs gs ms
      (flat_prefix (LENGTH ms) ds) (flat_prefix (LENGTH ms) zs) stackpointer s1
    ==> flat_trace e fields rows guards make dest scratch fs rs gs ms ds zs
          stackpointer s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_trace]) THEN
  REPEAT STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN
   `LENGTH(flat_prefix (LENGTH(ms:int32 list)) (ds:int32 list)) = LENGTH ms /\
    LENGTH(flat_prefix (LENGTH(ms:int32 list)) (zs:int32 list)) = LENGTH ms`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 th; CONJUNCT2 th]) THEN
              ASSUME_TAC th) THENL
   [CONJ_TAC THEN MATCH_MP_TAC LENGTH_FLAT_PREFIX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FLAT_TRACE_APPEND_FULL THEN
  MAP_EVERY EXISTS_TAC
    [`e2':uarch_event list`; `e2:uarch_event list`; `s0:x86state`] THEN
  ASM_SIMP_TAC[APPEND_ASSOC; LENGTH_FLAT_PREFIX]);;
