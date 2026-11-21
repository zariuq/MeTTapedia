(* Exact linked-byte successful execution of Cesta ordinary_flat_pack. *)

let ordinary_pack_outer_inv = new_definition
 `ordinary_pack_outer_inv source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 i s <=>
    ordinary_pack_offset_saved stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 s /\
    read R14 s = word i /\ read RBX s = word(4 * i) /\
    read RCX s = word(LENGTH offsets) /\
    read R11 s = premises /\ read RSI s = word(LENGTH fields_xs) /\
    read R8 s = source /\ read R9 s = word(LENGTH source_xs) /\
    read R10 s = fields /\ read RDI s = rows /\
    read RBP s = constants /\ read R12 s = word(LENGTH constants_xs) /\
    read R13 s = word(4 * LENGTH offsets) /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(fields,4 * i) s =
      flat_prefix (4 * i)
        (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs) /\
    wordlist_from_memory
      (word_add fields (word(4 * (4 * i))),LENGTH fields_xs - 4 * i) s =
      ordinary_drop (4 * i) fields_xs /\
    wordlist_from_memory(rows,i) s =
      flat_prefix i (ordinary_pack_result_rows source_xs offsets rows_xs) /\
    wordlist_from_memory(word_add rows (word(4 * i)),LENGTH rows_xs - i) s =
      ordinary_drop i rows_xs`;;

let ordinary_pack_outer_entry = new_definition
 `ordinary_pack_outer_entry pc source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_pack_mc /\
    read RIP s = word(pc + 0x182) /\
    ordinary_pack_outer_inv source premises constants fields rows source_xs
      offsets constants_xs fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 0 s /\
    ordinary_pack_trace e source premises constants fields rows source_xs offsets
      constants_xs fields_xs rows_xs stackpointer s`;;

let ordinary_pack_copy_inv = new_definition
 `ordinary_pack_copy_inv source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 i j s <=>
    ordinary_pack_offset_saved stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 s /\
    read RAX s = word(val(EL i offsets:int32) + j) /\
    read RDX s = word(4 * i + j) /\
    read R14 s = word i /\ read RBX s = word(4 * i) /\
    read RCX s = word(LENGTH offsets) /\
    read R11 s = premises /\ read RSI s = word(LENGTH fields_xs) /\
    read R8 s = source /\ read R9 s = word(LENGTH source_xs) /\
    read R10 s = fields /\ read RDI s = rows /\
    read RBP s = constants /\ read R12 s = word(LENGTH constants_xs) /\
    read R13 s = word(4 * LENGTH offsets) /\
    read (memory :> bytes64 (word_add (read RSP s) (word 8))) s =
      word(val(EL i offsets:int32) + 4) /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(fields,4 * i + j) s =
      flat_prefix (4 * i + j)
        (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs) /\
    wordlist_from_memory
      (word_add fields (word(4 * (4 * i + j))),LENGTH fields_xs - (4 * i + j)) s =
      ordinary_drop (4 * i + j) fields_xs /\
    wordlist_from_memory(rows,i + 1) s =
      flat_prefix (i + 1) (ordinary_pack_result_rows source_xs offsets rows_xs) /\
    wordlist_from_memory
      (word_add rows (word(4 * (i + 1))),LENGTH rows_xs - (i + 1)) s =
      ordinary_drop (i + 1) rows_xs /\
    (read ZF s <=> j = 4)`;;

let ordinary_pack_constants_inv = new_definition
 `ordinary_pack_constants_inv source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 j s <=>
    ordinary_pack_offset_saved stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 s /\
    read RDX s = word j /\ read RCX s = word(4 * LENGTH offsets + j) /\
    read R9 s = word(LENGTH constants_xs) /\
    read RAX s = word(LENGTH fields_xs) /\
    read R8 s = constants /\ read R10 s = fields /\ read RDI s = rows /\
    read RBP s = constants /\ read R12 s = word(LENGTH constants_xs) /\
    read R13 s = word(4 * LENGTH offsets) /\
    read R11 s = premises /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(fields,4 * LENGTH offsets + j) s =
      flat_prefix (4 * LENGTH offsets + j)
        (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs) /\
    wordlist_from_memory
      (word_add fields (word(4 * (4 * LENGTH offsets + j))),
       LENGTH fields_xs - (4 * LENGTH offsets + j)) s =
      ordinary_drop (4 * LENGTH offsets + j) fields_xs /\
    wordlist_from_memory(rows,LENGTH offsets + 1) s =
      flat_prefix (LENGTH offsets + 1)
        (ordinary_pack_result_rows source_xs offsets rows_xs) /\
    wordlist_from_memory
      (word_add rows (word(4 * (LENGTH offsets + 1))),
       LENGTH rows_xs - (LENGTH offsets + 1)) s =
      ordinary_drop (LENGTH offsets + 1) rows_xs`;;

let ordinary_pack_constants_entry = new_definition
 `ordinary_pack_constants_entry pc source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_pack_mc /\
    read RIP s = word(pc + 0x1e5) /\
    ordinary_pack_constants_inv source premises constants fields rows source_xs
      offsets constants_xs fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 0 s /\
    ordinary_pack_trace e source premises constants fields rows source_xs offsets
      constants_xs fields_xs rows_xs stackpointer s`;;

let ordinary_pack_accept_source_exfalso : tactic = fun ((asl,w) as goal) ->
  let fact tm = try Some(snd(List.find (fun (_,th) -> concl th = tm) asl))
                with Not_found -> None in
  match fact `LENGTH(source_xs:int32 list) = 0`,
        fact `val(EL 0 offsets:int32) + 4 <= LENGTH(source_xs:int32 list)` with
  | Some zero,Some bound ->
      let f = REWRITE_RULE [zero; ARITH_RULE `n + 4 <= 0 <=> F`] bound in
      ACCEPT_TAC (MATCH_MP (TAUT (mk_imp(`F`,w))) f) goal
  | _ -> ALL_TAC goal;;

let ORDINARY_PACK_ACCEPT_STACK_EVENT_ADDRESSES = prove
 (`!sp:int64.
    word_sub sp (word 48) = word_add (word_sub sp (word 72)) (word 24) /\
    word_sub sp (word 40) = word_add (word_sub sp (word 72)) (word 32) /\
    word_sub sp (word 32) = word_add (word_sub sp (word 72)) (word 40) /\
    word_sub sp (word 24) = word_add (word_sub sp (word 72)) (word 48) /\
    word_sub sp (word 16) = word_add (word_sub sp (word 72)) (word 56) /\
    word_sub sp (word 8) = word_add (word_sub sp (word 72)) (word 64) /\
    word_add sp (word 8) = word_add (word_sub sp (word 72)) (word 80) /\
    word_add sp (word 16) = word_add (word_sub sp (word 72)) (word 88) /\
    word_add sp (word 24) = word_add (word_sub sp (word 72)) (word 96) /\
    word_add sp (word 32) = word_add (word_sub sp (word 72)) (word 104)`,
  CONV_TAC WORD_RULE);;

let rec ordinary_pack_accept_raw_event_finish : tactic = fun ((_,w) as goal) ->
  if is_exists w then
    (SAFE_META_EXISTS_TAC allowed_vars_e THEN CONJ_TAC THENL
     [EXISTS_E2_TAC allowed_vars_e; ordinary_pack_accept_raw_event_finish]) goal
  else
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
       [REWRITE_TAC[ORDINARY_PACK_ACCEPT_STACK_EVENT_ADDRESSES] THEN
        ordinary_pack_concrete_event_finish;
        FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[]]) ORELSE
     (REWRITE_TAC[ORDINARY_PACK_ACCEPT_STACK_EVENT_ADDRESSES] THEN
      ordinary_pack_concrete_event_finish)) goal;;

let ordinary_pack_accept_final_finish : tactic = fun ((_,w) as goal) ->
  if is_exists w then
    (RULE_ASSUM_TAC(REWRITE_RULE[ORDINARY_PACK_ACCEPT_STACK_EVENT_ADDRESSES]) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[ORDINARY_PACK_ACCEPT_STACK_EVENT_ADDRESSES] THEN
     TRY DISCHARGE_SAFETY_PROPERTY_TAC THEN
     ordinary_pack_accept_raw_event_finish) goal
  else if is_comb w && name_of(fst(strip_comb w)) = "memaccess_inbounds" then
    ordinary_pack_accept_raw_event_finish goal
  else ordinary_pack_final_finish goal;;

let ordinary_pack_accept_return_finish : tactic =
  (SUBGOAL_THEN
   `(EventLoad(stackpointer:int64,8):uarch_event) =
    EventLoad(word_add (word_sub stackpointer (word 72)) (word 72),8)`
  ASSUME_TAC THENL [REWRITE_TAC[ORDINARY_PACK_STACK_RESTORE]; ALL_TAC]) THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[ORDINARY_PACK_STACK_RESTORE]) THEN
  ordinary_pack_accept_final_finish;;

let ordinary_pack_outer_entry_finish : tactic =
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ordinary_pack_outer_entry; ordinary_pack_outer_inv;
              ordinary_pack_trace; ordinary_pack_offset_saved] THEN
  REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN ordinary_pack_try_arith THEN
  ordinary_pack_accept_final_finish;;

let ordinary_pack_splice_tac length_lemma element_lemma =
  MATCH_MP_TAC FLAT_WORDLIST_SPLICE_32 THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_MESON_TAC[length_lemma];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[WORDLIST_FROM_MEMORY_32] THEN READ_OVER_WRITE_ORTHOGONAL_TAC;
    REWRITE_TAC[WORDLIST_FROM_MEMORY_32] THEN READ_OVER_WRITE_ORTHOGONAL_TAC;
    ASM_MESON_TAC[element_lemma]];;

let ordinary_pack_constants_finish state : tactic =
  let outputs = subst [state,`c14:x86state`]
   `wordlist_from_memory(fields,LENGTH fields_xs) c14 =
      ordinary_pack_result_fields source_xs offsets constants_xs fields_xs /\
    wordlist_from_memory(rows,LENGTH rows_xs) c14 =
      ordinary_pack_result_rows source_xs offsets rows_xs` in
  SUBGOAL_THEN outputs ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`fields:int64`;
        `4 * LENGTH(offsets:int32 list) + LENGTH(constants_xs:int32 list)`;
        `LENGTH(fields_xs:int32 list)`; state]
        WORDLIST_FROM_MEMORY_SPLIT_32) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ordinary_pack_result_fields] THEN
      ASM_REWRITE_TAC[FLAT_PREFIX_APPEND_LEFT; ORDINARY_FIELDS_LENGTH];
      MP_TAC(ISPECL [`rows:int64`; `LENGTH(offsets:int32 list) + 1`;
        `LENGTH(rows_xs:int32 list)`; state]
        WORDLIST_FROM_MEMORY_SPLIT_32) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ordinary_pack_result_rows] THEN
      ASM_REWRITE_TAC[FLAT_PREFIX_APPEND_LEFT; ORDINARY_ROWS_LENGTH]];
    ALL_TAC] THEN
  ordinary_pack_accept_return_finish;;

let ORDINARY_PACK_VALIDATE_ACCEPT_MC = prove
 (`!pc source premises constants fields rows source_xs offsets constants_xs
      fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_pack_span_valid source source_xs /\
    ordinary_pack_span_valid premises offsets /\
    ordinary_pack_span_valid constants constants_xs /\
    ordinary_pack_span_valid fields fields_xs /\
    ordinary_pack_span_valid rows rows_xs /\
    ordinary_pack_shape_valid offsets constants_xs fields_xs rows_xs /\
    ordinary_pack_offsets_valid source_xs offsets /\
    72 <= val stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 72),80))
      [(word pc,LENGTH ordinary_pack_mc);
       (source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (word pc,LENGTH ordinary_pack_mc))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (fields,4 * LENGTH fields_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (rows,4 * LENGTH rows_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs)]
    ==> ensures x86
      (\s. ordinary_pack_entry pc source premises constants fields rows
         source_xs offsets constants_xs fields_xs rows_xs
         stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
         init_r14 init_r15 e s)
      (\s. ordinary_pack_outer_entry pc source premises constants fields rows
         source_xs offsets constants_xs fields_xs rows_xs stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s)
      (ordinary_pack_frame fields rows fields_xs rows_xs stackpointer)`,
  REWRITE_TAC[ordinary_pack_span_valid; ordinary_pack_entry;
              ordinary_pack_outer_entry; ordinary_pack_outer_inv;
              ordinary_pack_trace; ordinary_pack_frame; ordinary_pack_reject_frame;
              C_ARGUMENTS; SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; fst ORDINARY_PACK_EXEC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(offsets:int32 list) <= 24 /\
    LENGTH(constants_xs:int32 list) <= 32 /\
    4 * LENGTH(offsets:int32 list) + LENGTH(constants_xs:int32 list) <=
      LENGTH(fields_xs:int32 list) /\
    LENGTH(offsets:int32 list) + 1 <= LENGTH(rows_xs:int32 list)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ordinary_pack_shape_valid]; ALL_TAC] THEN
  ordinary_pack_validate_spans THEN
  ordinary_pack_shape_exfalso THEN
  MP_TAC(ISPECL [`premises:int64`; `offsets:int32 list`; `s0:x86state`]
    WORDLIST_READS_32) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  span_zero_cases `LENGTH(offsets:int32 list)` THENL
   [ordinary_pack_offset_steps_to `word(pc + 0x182):int64` 60 THEN
    ordinary_pack_outer_entry_finish;
    SUBGOAL_THEN `0 < LENGTH(offsets:int32 list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `val(EL 0 offsets:int32) + 4 <= LENGTH(source_xs:int32 list)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[ordinary_pack_offsets_valid; GSYM ALL_EL]; ALL_TAC] THEN
    ordinary_pack_accept_source_exfalso] THEN
  ordinary_pack_offset_steps_to `word(pc + 0x130):int64` 45 THEN
  ENSURES_WHILE_UP2_TAC `LENGTH(offsets:int32 list)` `pc + 0x130` `pc + 0x14c`
   `\i s. ordinary_pack_offset_saved stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
      read RBX s = word i /\
      read RCX s = word(LENGTH(offsets:int32 list)) /\
      read RSI s = word(LENGTH(source_xs:int32 list)) /\
      read R11 s = premises /\
      read R8 s = rows /\ read R9 s = source /\
      read RDX s = constants /\ read RDI s = word(LENGTH(fields_xs:int32 list)) /\
      read R10 s = fields /\
      read R12 s = word(LENGTH(constants_xs:int32 list)) /\
      read R15 s = constants /\
      wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
      wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
      (read ZF s <=> i = LENGTH(offsets:int32 list))` THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ordinary_pack_offset_saved] THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i < LENGTH(offsets:int32 list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `val(EL i offsets:int32) + 4 <= LENGTH(source_xs:int32 list)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[ordinary_pack_offsets_valid; GSYM ALL_EL]; ALL_TAC] THEN
    REWRITE_TAC[ordinary_pack_offset_saved] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes32 (word_add premises (word(4 * i)))) s0 =
        EL i offsets:int32`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ordinary_pack_offset_steps (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ordinary_pack_offset_saved] THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN ordinary_pack_try_arith;
    REWRITE_TAC[ordinary_pack_offset_saved] THEN ENSURES_INIT_TAC "s0" THEN
    ordinary_pack_offset_steps [1] THEN
    ordinary_pack_offset_steps_to `word(pc + 0x182):int64` 25 THEN
    ordinary_pack_outer_entry_finish]);;

let ORDINARY_PACK_ROWS_ACCEPT_MC = prove
 (`!pc source premises constants fields rows source_xs offsets constants_xs
      fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_pack_span_valid source source_xs /\
    ordinary_pack_span_valid premises offsets /\
    ordinary_pack_span_valid constants constants_xs /\
    ordinary_pack_span_valid fields fields_xs /\
    ordinary_pack_span_valid rows rows_xs /\
    ordinary_pack_shape_valid offsets constants_xs fields_xs rows_xs /\
    ordinary_pack_offsets_valid source_xs offsets /\
    72 <= val stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 72),80))
      [(word pc,LENGTH ordinary_pack_mc);
       (source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (word pc,LENGTH ordinary_pack_mc))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (fields,4 * LENGTH fields_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (rows,4 * LENGTH rows_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs)]
    ==> ensures x86
      (ordinary_pack_outer_entry pc source premises constants fields rows
         source_xs offsets constants_xs fields_xs rows_xs stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (\s. ordinary_pack_constants_entry pc source premises constants fields rows
         source_xs offsets constants_xs fields_xs rows_xs stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s)
      (ordinary_pack_frame fields rows fields_xs rows_xs stackpointer)`,
  REWRITE_TAC[ordinary_pack_span_valid; ordinary_pack_outer_entry;
              ordinary_pack_constants_entry; ordinary_pack_constants_inv;
              ordinary_pack_trace; ordinary_pack_frame; ordinary_pack_reject_frame;
              SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; fst ORDINARY_PACK_EXEC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(offsets:int32 list) <= 24 /\
    LENGTH(constants_xs:int32 list) <= 32 /\
    4 * LENGTH(offsets:int32 list) + LENGTH(constants_xs:int32 list) <=
      LENGTH(fields_xs:int32 list) /\
    LENGTH(offsets:int32 list) + 1 <= LENGTH(rows_xs:int32 list)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ordinary_pack_shape_valid]; ALL_TAC] THEN
  MAP_EVERY VAL_INT64_TAC
   [`LENGTH(source_xs:int32 list)`; `LENGTH(offsets:int32 list)`;
    `LENGTH(constants_xs:int32 list)`; `LENGTH(fields_xs:int32 list)`;
    `LENGTH(rows_xs:int32 list)`] THEN
  span_zero_cases `LENGTH(offsets:int32 list)` THENL
   [ordinary_pack_offset_steps_to `word(pc + 0x1e5):int64` 12 THEN
    SUBGOAL_THEN
     `wordlist_from_memory(rows,LENGTH offsets + 1) d9 =
        flat_prefix (LENGTH offsets + 1)
          (ordinary_pack_result_rows source_xs offsets rows_xs) /\
      wordlist_from_memory
        (word_add rows (word(4 * (LENGTH offsets + 1))),
         LENGTH rows_xs - (LENGTH offsets + 1)) d9 =
        ordinary_drop (LENGTH offsets + 1) rows_xs`
    ASSUME_TAC THENL
     [ordinary_pack_splice_tac ORDINARY_PACK_RESULT_ROWS_LENGTH
        ORDINARY_PACK_RESULT_ROW_EL; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ordinary_pack_constants_entry; ordinary_pack_constants_inv;
                    ordinary_pack_trace; ADD_CLAUSES;
                    flat_prefix; ordinary_drop; WORDLIST_FROM_MEMORY_CLAUSES] THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
    ordinary_pack_try_arith THEN
    ordinary_pack_accept_final_finish;
    ALL_TAC] THEN
  ENSURES_WHILE_UP2_TAC `LENGTH(offsets:int32 list)` `pc + 0x182` `pc + 0x1c3`
   `\i s. ordinary_pack_outer_inv source premises constants fields rows source_xs
      offsets constants_xs fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 i s` THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ordinary_pack_outer_inv];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i < LENGTH(offsets:int32 list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `val(EL i offsets:int32) + 4 <= LENGTH(source_xs:int32 list)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[ordinary_pack_offsets_valid; GSYM ALL_EL]; ALL_TAC] THEN
    REWRITE_TAC[ordinary_pack_outer_inv] THEN ENSURES_INIT_TAC "a0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes32 (word_add premises (word(4 * i)))) a0 =
        EL i offsets:int32`
    ASSUME_TAC THENL [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ordinary_pack_offset_steps (1--7) THEN
    ENSURES_WHILE_UP2_TAC `4` `pc + 0x19a` `pc + 0x1b9`
     `\j s. ordinary_pack_copy_inv source premises constants fields rows source_xs
        offsets constants_xs fields_xs rows_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 i j s` THEN
    BETA_TAC THEN REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      SUBGOAL_THEN
       `wordlist_from_memory(rows,i + 1) a7 =
          flat_prefix (i + 1)
            (ordinary_pack_result_rows source_xs offsets rows_xs) /\
        wordlist_from_memory
          (word_add rows (word(4 * (i + 1))),LENGTH rows_xs - (i + 1)) a7 =
          ordinary_drop (i + 1) rows_xs`
      ASSUME_TAC THENL
       [ordinary_pack_splice_tac ORDINARY_PACK_RESULT_ROWS_LENGTH
          ORDINARY_PACK_RESULT_ROW_EL; ALL_TAC] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[ordinary_pack_copy_inv] THEN
      REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
      ordinary_pack_try_arith THEN TRY (ASM_MESON_TAC[]);
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `j < 4` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `val(EL i offsets:int32) + j < LENGTH(source_xs:int32 list)`
      ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `4 * i + j < LENGTH(fields_xs:int32 list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ordinary_pack_copy_inv] THEN ENSURES_INIT_TAC "b0" THEN
      SUBGOAL_THEN
       `read (memory :> bytes32
          (word_add source (word(4 * (val(EL i offsets:int32) + j))))) b0 =
          EL (val(EL i offsets:int32) + j) source_xs`
      ASSUME_TAC THENL [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ordinary_pack_offset_steps (1--9) THEN
      SUBGOAL_THEN
       `wordlist_from_memory(fields,4 * i + (j + 1)) b9 =
          flat_prefix (4 * i + (j + 1))
            (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs) /\
        wordlist_from_memory
          (word_add fields (word(4 * (4 * i + (j + 1)))),
           LENGTH fields_xs - (4 * i + (j + 1))) b9 =
          ordinary_drop (4 * i + (j + 1)) fields_xs`
      ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `4 * i + (j + 1) = 4 * i + j + 1`] THEN
        ordinary_pack_splice_tac ORDINARY_PACK_RESULT_FIELDS_LENGTH
          ORDINARY_PACK_RESULT_PREMISE_EL; ALL_TAC] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[ordinary_pack_copy_inv] THEN
      REWRITE_TAC[ARITH_RULE `4 * i + (j + 1) = 4 * i + j + 1`] THEN
      REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN ordinary_pack_try_arith;
      REWRITE_TAC[ordinary_pack_copy_inv] THEN ENSURES_INIT_TAC "c0" THEN
      ordinary_pack_offset_steps (1--3) THEN
      ASM_CASES_TAC `i + 1 < LENGTH(offsets:int32 list)` THENL
       [ordinary_pack_offset_steps [1]; ALL_TAC] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[ordinary_pack_outer_inv] THEN
      REWRITE_TAC[ARITH_RULE `4 * i + 4 = 4 * (i + 1)`] THEN
      REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN ordinary_pack_try_arith];
    REWRITE_TAC[ordinary_pack_outer_inv] THEN ENSURES_INIT_TAC "d0" THEN
    ordinary_pack_offset_steps (1--3) THEN
    ordinary_pack_offset_steps_to `word(pc + 0x1e5):int64` 10 THEN
    SUBGOAL_THEN
     `wordlist_from_memory(rows,LENGTH offsets + 1) d10 =
        flat_prefix (LENGTH offsets + 1)
          (ordinary_pack_result_rows source_xs offsets rows_xs) /\
      wordlist_from_memory
        (word_add rows (word(4 * (LENGTH offsets + 1))),
         LENGTH rows_xs - (LENGTH offsets + 1)) d10 =
        ordinary_drop (LENGTH offsets + 1) rows_xs`
    ASSUME_TAC THENL
     [ordinary_pack_splice_tac ORDINARY_PACK_RESULT_ROWS_LENGTH
        ORDINARY_PACK_RESULT_ROW_EL; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ordinary_pack_constants_entry; ordinary_pack_constants_inv;
                    ordinary_pack_trace; ADD_CLAUSES] THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
    ordinary_pack_try_arith THEN
    ordinary_pack_accept_final_finish]);;

let ORDINARY_PACK_CONSTANTS_ACCEPT_MC = prove
 (`!pc source premises constants fields rows source_xs offsets constants_xs
      fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_pack_span_valid source source_xs /\
    ordinary_pack_span_valid premises offsets /\
    ordinary_pack_span_valid constants constants_xs /\
    ordinary_pack_span_valid fields fields_xs /\
    ordinary_pack_span_valid rows rows_xs /\
    ordinary_pack_shape_valid offsets constants_xs fields_xs rows_xs /\
    ordinary_pack_offsets_valid source_xs offsets /\
    72 <= val stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 72),80))
      [(word pc,LENGTH ordinary_pack_mc);
       (source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (word pc,LENGTH ordinary_pack_mc))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (fields,4 * LENGTH fields_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (rows,4 * LENGTH rows_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs)]
    ==> ensures x86
      (ordinary_pack_constants_entry pc source premises constants fields rows
         source_xs offsets constants_xs fields_xs rows_xs stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (\s. ordinary_pack_return 1 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_pack_trace e source premises constants fields rows
             source_xs offsets constants_xs fields_xs rows_xs stackpointer s /\
           wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
           wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
           wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
           wordlist_from_memory(fields,LENGTH fields_xs) s =
             ordinary_pack_result_fields source_xs offsets constants_xs fields_xs /\
           wordlist_from_memory(rows,LENGTH rows_xs) s =
             ordinary_pack_result_rows source_xs offsets rows_xs)
      (ordinary_pack_frame fields rows fields_xs rows_xs stackpointer)`,
  REWRITE_TAC[ordinary_pack_span_valid; ordinary_pack_constants_entry;
              ordinary_pack_return; ordinary_pack_trace; ordinary_pack_frame;
              ordinary_pack_reject_frame; SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; fst ORDINARY_PACK_EXEC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(offsets:int32 list) <= 24 /\
    LENGTH(constants_xs:int32 list) <= 32 /\
    4 * LENGTH(offsets:int32 list) + LENGTH(constants_xs:int32 list) <=
      LENGTH(fields_xs:int32 list) /\
    LENGTH(offsets:int32 list) + 1 <= LENGTH(rows_xs:int32 list)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ordinary_pack_shape_valid]; ALL_TAC] THEN
  MAP_EVERY VAL_INT64_TAC
   [`LENGTH(source_xs:int32 list)`; `LENGTH(offsets:int32 list)`;
    `LENGTH(constants_xs:int32 list)`; `LENGTH(fields_xs:int32 list)`;
    `LENGTH(rows_xs:int32 list)`] THEN
  span_zero_cases `LENGTH(constants_xs:int32 list)` THENL
   [ENSURES_INIT_TAC "z0" THEN ordinary_pack_steps_to_return 20 THEN
    ordinary_pack_constants_finish `z13:x86state`;
    ALL_TAC] THEN
  ENSURES_WHILE_UP2_TAC `LENGTH(constants_xs:int32 list)` `pc + 0x1e5` `pc + 0x1ff`
   `\j s. ordinary_pack_constants_inv source premises constants fields rows source_xs
      offsets constants_xs fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 j s` THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ordinary_pack_constants_inv];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `j < LENGTH(constants_xs:int32 list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `4 * LENGTH(offsets:int32 list) + j < LENGTH(fields_xs:int32 list)`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ordinary_pack_constants_inv] THEN ENSURES_INIT_TAC "b0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes32 (word_add constants (word(4 * j)))) b0 =
        EL j constants_xs`
    ASSUME_TAC THENL [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ordinary_pack_offset_steps (1--8) THEN
    SUBGOAL_THEN
     `wordlist_from_memory(fields,4 * LENGTH offsets + (j + 1)) b8 =
        flat_prefix (4 * LENGTH offsets + (j + 1))
          (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs) /\
      wordlist_from_memory
        (word_add fields (word(4 * (4 * LENGTH offsets + (j + 1)))),
         LENGTH fields_xs - (4 * LENGTH offsets + (j + 1))) b8 =
        ordinary_drop (4 * LENGTH offsets + (j + 1)) fields_xs`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * n + (j + 1) = 4 * n + j + 1`] THEN
      ordinary_pack_splice_tac ORDINARY_PACK_RESULT_FIELDS_LENGTH
        ORDINARY_PACK_RESULT_CONSTANT_EL; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ordinary_pack_constants_inv] THEN
    REWRITE_TAC[ARITH_RULE `4 * n + (j + 1) = 4 * n + j + 1`] THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN ordinary_pack_try_arith;
    REWRITE_TAC[ordinary_pack_constants_inv] THEN ENSURES_INIT_TAC "c0" THEN
    ordinary_pack_offset_steps_to `returnaddress:int64` 20 THEN
    ordinary_pack_constants_finish `c14:x86state`]);;

let ORDINARY_PACK_FRAME_IDEMPOTENT = prove
 (`!fields rows (fields_xs:int32 list) (rows_xs:int32 list) stackpointer.
    ordinary_pack_frame fields rows fields_xs rows_xs stackpointer ,,
    ordinary_pack_frame fields rows fields_xs rows_xs stackpointer =
    ordinary_pack_frame fields rows fields_xs rows_xs stackpointer`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinary_pack_frame;
    ordinary_pack_reject_frame; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    SOME_FLAGS] THEN MAYCHANGE_IDEMPOT_TAC);;

let ORDINARY_PACK_TRANS = prove
 (`!fields rows (fields_xs:int32 list) (rows_xs:int32 list) stackpointer P Q R.
    ensures x86 P Q (ordinary_pack_frame fields rows fields_xs rows_xs stackpointer) /\
    ensures x86 Q R (ordinary_pack_frame fields rows fields_xs rows_xs stackpointer)
      ==> ensures x86 P R
        (ordinary_pack_frame fields rows fields_xs rows_xs stackpointer)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `Q:x86state->bool` THEN
  REWRITE_TAC[ORDINARY_PACK_FRAME_IDEMPOTENT] THEN ASM_REWRITE_TAC[]);;

let ORDINARY_PACK_MC_CORRECT = prove
 (`!pc source premises constants fields rows source_xs offsets constants_xs
      fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_pack_span_valid source source_xs /\
    ordinary_pack_span_valid premises offsets /\
    ordinary_pack_span_valid constants constants_xs /\
    ordinary_pack_span_valid fields fields_xs /\
    ordinary_pack_span_valid rows rows_xs /\
    ordinary_pack_shape_valid offsets constants_xs fields_xs rows_xs /\
    ordinary_pack_offsets_valid source_xs offsets /\
    72 <= val stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 72),80))
      [(word pc,LENGTH ordinary_pack_mc);
       (source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (word pc,LENGTH ordinary_pack_mc))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (fields,4 * LENGTH fields_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (rows,4 * LENGTH rows_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs)]
    ==> ensures x86
      (\s. ordinary_pack_entry pc source premises constants fields rows
         source_xs offsets constants_xs fields_xs rows_xs
         stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
         init_r14 init_r15 e s)
      (\s. ordinary_pack_return 1 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_pack_trace e source premises constants fields rows
             source_xs offsets constants_xs fields_xs rows_xs stackpointer s /\
           wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
           wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
           wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
           wordlist_from_memory(fields,LENGTH fields_xs) s =
             ordinary_pack_result_fields source_xs offsets constants_xs fields_xs /\
           wordlist_from_memory(rows,LENGTH rows_xs) s =
             ordinary_pack_result_rows source_xs offsets rows_xs)
      (ordinary_pack_frame fields rows fields_xs rows_xs stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ORDINARY_PACK_TRANS THEN
  EXISTS_TAC `\s. ordinary_pack_outer_entry pc source premises constants fields rows
    source_xs offsets constants_xs fields_xs rows_xs stackpointer returnaddress
    init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ORDINARY_PACK_VALIDATE_ACCEPT_MC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ORDINARY_PACK_TRANS THEN
    EXISTS_TAC `\s. ordinary_pack_constants_entry pc source premises constants fields
      rows source_xs offsets constants_xs fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_PACK_ROWS_ACCEPT_MC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ORDINARY_PACK_CONSTANTS_ACCEPT_MC THEN ASM_REWRITE_TAC[]]]);;
