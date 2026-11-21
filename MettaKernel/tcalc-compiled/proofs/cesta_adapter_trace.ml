(* Event-bound widening and append composition for the linked adapter. *)

let ORDINARY_ADAPTER_PRE_PACK_STACK_IN_FULL = prove
 (`!sp:int64. word_sub sp (word 152) =
    word_add (word_sub sp (word 232)) (word 80)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_ADAPTER_PRE_PACK_STACK_CONTAINED = prove
 (`!sp:int64. contained_modulo (2 EXP 64)
    (val(word_sub sp (word 152)),152)
    (val(word_sub sp (word 232)),232)`,
  GEN_TAC THEN REWRITE_TAC[ORDINARY_ADAPTER_PRE_PACK_STACK_IN_FULL] THEN
  CONTAINED_TAC);;

let ORDINARY_ADAPTER_PRE_PACK_BYTES_SUBSUMED = prove
 (`!stackpointer:int64.
    ASSIGNS (memory :> bytes(word_sub stackpointer (word 152),152)) subsumed
    ASSIGNS (memory :> bytes(word_sub stackpointer (word 232),232))`,
  GEN_TAC THEN MATCH_MP_TAC SUBSUMED_ASSIGNS_SUBCOMPONENTS THEN
  MATCH_MP_TAC(ISPECL [`word_sub stackpointer (word 152):int64`;
    `word_sub stackpointer (word 232):int64`; `152:num`; `232:num`]
    SUBSUMED_ASSIGNS_BYTES) THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  ACCEPT_TAC(SPEC `stackpointer:int64`
    ORDINARY_ADAPTER_PRE_PACK_STACK_CONTAINED));;

let ORDINARY_ADAPTER_PRE_PACK_MEMORY_SUBSUMED = prove
 (`!fields rows dest scratch (fields_xs:int32 list) (rows_xs:int32 list)
      (dest_xs:int32 list) (scratch_xs:int32 list) stackpointer.
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 152),152)] subsumed
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 232),232);
               memory :> bytes(word_add stackpointer (word 8),16);
               memory :> bytes(fields,4 * LENGTH fields_xs);
               memory :> bytes(rows,4 * LENGTH rows_xs);
               memory :> bytes(dest,4 * LENGTH dest_xs);
               memory :> bytes(scratch,4 * LENGTH scratch_xs)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAYCHANGE_SING] THEN
  ONCE_REWRITE_TAC[MAYCHANGE] THEN
  MATCH_MP_TAC SUBSUMED_SEQ_LEFT THEN CONJ_TAC THENL
   [ACCEPT_TAC(SPEC `stackpointer:int64`
      ORDINARY_ADAPTER_PRE_PACK_BYTES_SUBSUMED);
    SUBSUMED_ID_MAYCHANGE_TAC]);;

let ORDINARY_ADAPTER_PRE_PACK_FRAME_SUBSUMED = prove
 (`!fields rows dest scratch (fields_xs:int32 list) (rows_xs:int32 list)
      (dest_xs:int32 list) (scratch_xs:int32 list) stackpointer P Q.
    ensures x86 P Q (ordinary_adapter_pre_pack_frame stackpointer)
    ==> ensures x86 P Q
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
         scratch_xs stackpointer)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `ordinary_adapter_pre_pack_frame stackpointer` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ordinary_adapter_frame; ordinary_adapter_pre_pack_frame;
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN CONJ_TAC) THEN
    TRY(MATCH_ACCEPT_TAC SUBSUMED_REFL) THEN
    ACCEPT_TAC(SPECL [`fields:int64`; `rows:int64`; `dest:int64`;
      `scratch:int64`; `fields_xs:int32 list`; `rows_xs:int32 list`;
      `dest_xs:int32 list`; `scratch_xs:int32 list`; `stackpointer:int64`]
      ORDINARY_ADAPTER_PRE_PACK_MEMORY_SUBSUMED);
    FIRST_ASSUM ACCEPT_TAC]);;

let ORDINARY_ADAPTER_TRACE_STACK_ADDRESSES = prove
 (`!stackpointer:int64.
     word_sub stackpointer (word 120) =
       word_add (word_sub stackpointer (word 232)) (word 112) /\
     word_sub stackpointer (word 152) =
       word_add (word_sub stackpointer (word 232)) (word 80)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_ADAPTER_PRE_PACK_BOUNDS_WIDEN = prove
 (`!e (source:int64) (premises:int64) (constants:int64) (guards:int64)
      (makes:int64) (fields:int64) (rows:int64) (dest:int64) (scratch:int64)
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (guards_xs:int32 list) (makes_xs:int32 list) (fields_xs:int32 list)
      (rows_xs:int32 list) (dest_xs:int32 list) (scratch_xs:int32 list)
      (stackpointer:int64).
    memaccess_inbounds e
      [(word_sub stackpointer (word 120),224)]
      [(word_sub stackpointer (word 152),152)]
    ==> memaccess_inbounds e
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs);
       (word_sub stackpointer (word 232),336)]
      [(word_sub stackpointer (word 232),232);
       (word_add stackpointer (word 8),16);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (ISPECL
    [`e:uarch_event list`;
     `[(word_sub (stackpointer:int64) (word 120),224)]`;
     `[(source:int64,4 * LENGTH(source_xs:int32 list));
       (premises:int64,4 * LENGTH(offsets:int32 list));
       (constants:int64,4 * LENGTH(constants_xs:int32 list));
       (guards:int64,4 * LENGTH(guards_xs:int32 list));
       (makes:int64,4 * LENGTH(makes_xs:int32 list));
       (fields:int64,4 * LENGTH(fields_xs:int32 list));
       (rows:int64,4 * LENGTH(rows_xs:int32 list));
       (dest:int64,4 * LENGTH(dest_xs:int32 list));
       (scratch:int64,4 * LENGTH(scratch_xs:int32 list));
       (word_sub stackpointer (word 232),336)]`;
     `[(word_sub (stackpointer:int64) (word 152),152)]`;
     `[(word_sub (stackpointer:int64) (word 232),232);
       (word_add stackpointer (word 8),16);
       ((fields:int64),4 * LENGTH(fields_xs:int32 list));
       ((rows:int64),4 * LENGTH(rows_xs:int32 list));
       ((dest:int64),4 * LENGTH(dest_xs:int32 list));
       ((scratch:int64),4 * LENGTH(scratch_xs:int32 list))]`]
    MEMACCESS_INBOUNDS_CONTAINED)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ALL; EX; ORDINARY_ADAPTER_TRACE_STACK_ADDRESSES] THEN
    REPEAT CONJ_TAC THENL
     [REPLICATE_TAC 9 DISJ2_TAC THEN
      MATCH_MP_TAC CESTA_CONTAINED_OFFSET THEN ARITH_TAC;
      DISJ1_TAC THEN MATCH_MP_TAC CESTA_CONTAINED_OFFSET THEN ARITH_TAC];
    FIRST_ASSUM ACCEPT_TAC]);;

let ORDINARY_ADAPTER_REJECT_BOUNDS_WIDEN = prove
 (`!e (source:int64) (premises:int64) (constants:int64) (guards:int64)
      (makes:int64) (fields:int64) (rows:int64) (dest:int64) (scratch:int64)
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (guards_xs:int32 list) (makes_xs:int32 list) (fields_xs:int32 list)
      (rows_xs:int32 list) (dest_xs:int32 list) (scratch_xs:int32 list)
      (stackpointer:int64).
    memaccess_inbounds e
      [(word_sub stackpointer (word 120),224)]
      [(word_sub stackpointer (word 120),120)]
    ==> memaccess_inbounds e
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs);
       (word_sub stackpointer (word 232),336)]
      [(word_sub stackpointer (word 232),232);
       (word_add stackpointer (word 8),16);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ORDINARY_ADAPTER_PRE_PACK_BOUNDS_WIDEN THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (ISPECL
    [`e:uarch_event list`;
     `[(word_sub (stackpointer:int64) (word 120),224)]`;
     `[(word_sub (stackpointer:int64) (word 120),224)]`;
     `[(word_sub (stackpointer:int64) (word 120),120)]`;
     `[(word_sub (stackpointer:int64) (word 152),152)]`]
    MEMACCESS_INBOUNDS_CONTAINED)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ALL; EX; WORD_RULE
      `word_sub (x:int64) (word 120) =
        word_add (word_sub x (word 152)) (word 32)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      MATCH_MP_TAC CESTA_CONTAINED_OFFSET THEN ARITH_TAC];
    FIRST_ASSUM ACCEPT_TAC]);;

let ORDINARY_ADAPTER_REJECT_TRACE_WIDEN = prove
 (`!e (source:int64) (premises:int64) (constants:int64) (guards:int64)
      (makes:int64) (fields:int64) (rows:int64) (dest:int64) (scratch:int64)
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (guards_xs:int32 list) (makes_xs:int32 list) (fields_xs:int32 list)
      (rows_xs:int32 list) (dest_xs:int32 list) (scratch_xs:int32 list)
      (stackpointer:int64) (s:x86state).
    ordinary_adapter_reject_trace e stackpointer s
    ==> ordinary_adapter_trace e source premises constants guards makes fields rows
          dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
          rows_xs dest_xs scratch_xs stackpointer s`,
  REWRITE_TAC[ordinary_adapter_reject_trace; ordinary_adapter_trace] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `e2:uarch_event list` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC ORDINARY_ADAPTER_REJECT_BOUNDS_WIDEN THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let ORDINARY_ADAPTER_PACK_BOUNDS_WIDEN = prove
 (`!e (source:int64) (premises:int64) (constants:int64) (guards:int64)
      (makes:int64) (fields:int64) (rows:int64) (dest:int64) (scratch:int64)
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (guards_xs:int32 list) (makes_xs:int32 list) (fields_xs:int32 list)
      (rows_xs:int32 list) (dest_xs:int32 list) (scratch_xs:int32 list)
      (stackpointer:int64).
    memaccess_inbounds e
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (word_sub (word_sub stackpointer (word 160)) (word 72),112)]
      [(word_sub (word_sub stackpointer (word 160)) (word 72),72);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)]
    ==> memaccess_inbounds e
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs);
       (word_sub stackpointer (word 232),336)]
      [(word_sub stackpointer (word 232),232);
       (word_add stackpointer (word 8),16);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (ISPECL
    [`e:uarch_event list`;
     `[(source:int64,4 * LENGTH(source_xs:int32 list));
       (premises:int64,4 * LENGTH(offsets:int32 list));
       (constants:int64,4 * LENGTH(constants_xs:int32 list));
       (word_sub (word_sub (stackpointer:int64) (word 160)) (word 72),112)]`;
     `[((source:int64),4 * LENGTH(source_xs:int32 list));
       ((premises:int64),4 * LENGTH(offsets:int32 list));
       ((constants:int64),4 * LENGTH(constants_xs:int32 list));
       ((guards:int64),4 * LENGTH(guards_xs:int32 list));
       ((makes:int64),4 * LENGTH(makes_xs:int32 list));
       ((fields:int64),4 * LENGTH(fields_xs:int32 list));
       ((rows:int64),4 * LENGTH(rows_xs:int32 list));
       ((dest:int64),4 * LENGTH(dest_xs:int32 list));
       ((scratch:int64),4 * LENGTH(scratch_xs:int32 list));
       (word_sub (stackpointer:int64) (word 232),336)]`;
     `[(word_sub (word_sub (stackpointer:int64) (word 160)) (word 72),72);
       ((fields:int64),4 * LENGTH(fields_xs:int32 list));
       ((rows:int64),4 * LENGTH(rows_xs:int32 list))]`;
     `[(word_sub (stackpointer:int64) (word 232),232);
       (word_add stackpointer (word 8),16);
       ((fields:int64),4 * LENGTH(fields_xs:int32 list));
       ((rows:int64),4 * LENGTH(rows_xs:int32 list));
       ((dest:int64),4 * LENGTH(dest_xs:int32 list));
       ((scratch:int64),4 * LENGTH(scratch_xs:int32 list))]`]
    MEMACCESS_INBOUNDS_CONTAINED)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ordinary_pack_word_sub_sub] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ALL; EX] THEN REPEAT CONJ_TAC THENL
     [DISJ1_TAC THEN MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      DISJ2_TAC THEN DISJ1_TAC THEN MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      REPLICATE_TAC 2 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      REPLICATE_TAC 9 DISJ2_TAC THEN
      MATCH_MP_TAC CESTA_CONTAINED_PREFIX THEN ARITH_TAC;
      DISJ1_TAC THEN MATCH_MP_TAC CESTA_CONTAINED_PREFIX THEN ARITH_TAC;
      REPLICATE_TAC 2 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      REPLICATE_TAC 3 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL];
    FIRST_ASSUM ACCEPT_TAC]);;

let ORDINARY_ADAPTER_LEAF_BOUNDS_WIDEN = prove
 (`!e (source:int64) (premises:int64) (constants:int64) (guards:int64)
      (makes:int64) (fields:int64) (rows:int64) (dest:int64) (scratch:int64)
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fs:int32 list) (rs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (stackpointer:int64).
    LENGTH ms <= LENGTH ds /\ LENGTH ms <= LENGTH zs /\
    memaccess_inbounds e
      [(fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
       (guards,4 * LENGTH gs); (makes,4 * LENGTH ms);
       (dest,4 * LENGTH ds); (scratch,4 * LENGTH zs);
       (word_sub stackpointer (word 48),72)]
      [(dest,4 * LENGTH ms); (scratch,4 * LENGTH ms);
       (word_sub stackpointer (word 48),48)]
    ==> memaccess_inbounds e
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH gs);
       (makes,4 * LENGTH ms); (fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
       (dest,4 * LENGTH ds); (scratch,4 * LENGTH zs);
       (word_sub stackpointer (word 232),336)]
      [(word_sub stackpointer (word 232),232);
       (word_add stackpointer (word 8),16);
       (fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
       (dest,4 * LENGTH ds); (scratch,4 * LENGTH zs)]`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] (ISPECL
    [`e:uarch_event list`;
     `[(fields:int64,4 * LENGTH(fs:int32 list));
       (rows:int64,4 * LENGTH(rs:int32 list));
       (guards:int64,4 * LENGTH(gs:int32 list));
       (makes:int64,4 * LENGTH(ms:int32 list));
       (dest:int64,4 * LENGTH(ds:int32 list));
       (scratch:int64,4 * LENGTH(zs:int32 list));
       (word_sub (stackpointer:int64) (word 48),72)]`;
     `[(source:int64,4 * LENGTH(source_xs:int32 list));
       (premises:int64,4 * LENGTH(offsets:int32 list));
       (constants:int64,4 * LENGTH(constants_xs:int32 list));
       (guards:int64,4 * LENGTH(gs:int32 list));
       (makes:int64,4 * LENGTH(ms:int32 list));
       (fields:int64,4 * LENGTH(fs:int32 list));
       (rows:int64,4 * LENGTH(rs:int32 list));
       (dest:int64,4 * LENGTH(ds:int32 list));
       (scratch:int64,4 * LENGTH(zs:int32 list));
       (word_sub (stackpointer:int64) (word 232),336)]`;
     `[(dest:int64,4 * LENGTH(ms:int32 list));
       (scratch:int64,4 * LENGTH(ms:int32 list));
       (word_sub (stackpointer:int64) (word 48),48)]`;
     `[(word_sub (stackpointer:int64) (word 232),232);
       (word_add stackpointer (word 8),16);
       (fields:int64,4 * LENGTH(fs:int32 list));
       (rows:int64,4 * LENGTH(rs:int32 list));
       (dest:int64,4 * LENGTH(ds:int32 list));
       (scratch:int64,4 * LENGTH(zs:int32 list))]`]
    MEMACCESS_INBOUNDS_CONTAINED)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ALL; EX; WORD_RULE
      `word_sub (x:int64) (word 48) =
        word_add (word_sub x (word 232)) (word 184)`] THEN
    REPEAT CONJ_TAC THENL
     [REPLICATE_TAC 5 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      REPLICATE_TAC 6 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      REPLICATE_TAC 3 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      REPLICATE_TAC 4 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      REPLICATE_TAC 7 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      REPLICATE_TAC 8 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_ACCEPT_TAC CESTA_CONTAINED_REFL;
      REPLICATE_TAC 9 DISJ2_TAC THEN
      MATCH_MP_TAC CESTA_CONTAINED_OFFSET THEN ARITH_TAC;
      REPLICATE_TAC 4 DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_MP_TAC CESTA_CONTAINED_PREFIX THEN ASM_ARITH_TAC;
      REPLICATE_TAC 5 DISJ2_TAC THEN MATCH_MP_TAC CESTA_CONTAINED_PREFIX THEN
      ASM_ARITH_TAC;
      DISJ1_TAC THEN MATCH_MP_TAC CESTA_CONTAINED_OFFSET THEN ARITH_TAC];
    FIRST_ASSUM ACCEPT_TAC]);;

let ORDINARY_ADAPTER_TRACE_APPEND = prove
 (`!e (e2:uarch_event list) (e3:uarch_event list)
      (source:int64) (premises:int64) (constants:int64) (guards:int64)
      (makes:int64) (fields:int64) (rows:int64) (dest:int64) (scratch:int64)
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (guards_xs:int32 list) (makes_xs:int32 list) (fields_xs:int32 list)
      (rows_xs:int32 list) (dest_xs:int32 list) (scratch_xs:int32 list)
      (stackpointer:int64) (s0:x86state) (s1:x86state).
    read events s0 = APPEND e2 e /\
    memaccess_inbounds e2
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs);
       (word_sub stackpointer (word 232),336)]
      [(word_sub stackpointer (word 232),232);
       (word_add stackpointer (word 8),16);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)] /\
    read events s1 = APPEND e3 (read events s0) /\
    memaccess_inbounds e3
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs);
       (word_sub stackpointer (word 232),336)]
      [(word_sub stackpointer (word 232),232);
       (word_add stackpointer (word 8),16);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)]
    ==> ordinary_adapter_trace e source premises constants guards makes fields rows
          dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
          rows_xs dest_xs scratch_xs stackpointer s1`,
  REWRITE_TAC[ordinary_adapter_trace] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `APPEND e3 e2:uarch_event list` THEN
  ASM_REWRITE_TAC[APPEND_ASSOC; MEMACCESS_INBOUNDS_APPEND]);;

let rec ordinary_adapter_composed_raw_event_finish : tactic = fun ((_,w) as goal) ->
  if is_exists w then
    (SAFE_META_EXISTS_TAC allowed_vars_e THEN CONJ_TAC THENL
     [EXISTS_E2_TAC allowed_vars_e; ordinary_adapter_composed_raw_event_finish]) goal
  else
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     FIRST_X_ASSUM (ACCEPT_TAC o MATCH_MP ORDINARY_ADAPTER_PRE_PACK_BOUNDS_WIDEN) ORELSE
     FIRST_X_ASSUM (ACCEPT_TAC o MATCH_MP ORDINARY_ADAPTER_PACK_BOUNDS_WIDEN) ORELSE
     (MATCH_MP_TAC ORDINARY_ADAPTER_LEAF_BOUNDS_WIDEN THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC; ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]) ORELSE
     (ordinary_adapter_split_append_events THENL
       [ordinary_adapter_composed_raw_event_finish;
        ordinary_adapter_composed_raw_event_finish]) ORELSE
     ordinary_adapter_concrete_event_finish) goal;;

let ordinary_adapter_composed_final_finish : tactic = fun ((_,w) as goal) ->
  if is_exists w then
    (ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[ORDINARY_ADAPTER_AFTER_PACK_STACK_IN_FULL] THEN
     TRY DISCHARGE_SAFETY_PROPERTY_TAC THEN
     ordinary_adapter_composed_raw_event_finish) goal
  else if is_comb w && name_of(fst(strip_comb w)) = "memaccess_inbounds" then
    ordinary_adapter_composed_raw_event_finish goal
  else ordinary_adapter_final_finish goal;;
