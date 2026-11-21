(* Exact linked-byte rejection at the first invalid premise offset. *)

let ordinary_pack_offset_exfalso : tactic = fun ((asl,w) as goal) ->
  let fact tm = try Some(snd(List.find (fun (_,th) -> concl th = tm) asl))
                with Not_found -> None in
  match fact `N < LENGTH(offsets:int32 list)`,
        fact `LENGTH(offsets:int32 list) = 0` with
  | Some bad,Some zero ->
      ACCEPT_TAC (MATCH_MP (TAUT (mk_imp(`F`,w))) (REWRITE_RULE
        [zero; ARITH_RULE `N < 0 <=> F`] bad)) goal
  | _ -> ALL_TAC goal;;

let ordinary_pack_marker text : tactic = fun goal ->
  Printf.printf "OFFSET_MARKER %s\n%!" text; ALL_TAC goal;;

let ordinary_pack_prepare_pup goal =
  let (meta,goals,justification) = (BETA_TAC THEN REPEAT CONJ_TAC) goal in
  Printf.printf "OFFSET_PUP_OBLIGATIONS %d\n%!" (length goals);
  (meta,goals,justification);;

let ordinary_pack_offset_reject_finish : tactic =
  ordinary_pack_offset_steps_to `returnaddress:int64` 20 THEN
  ordinary_pack_return_finish;;

let ordinary_pack_offset_bad_at_loop n : tactic =
  ordinary_pack_marker "BAD_AT_LOOP" THEN
  let bad = subst [n,`N:num`]
    `LENGTH(source_xs:int32 list) < val(EL (N:num) offsets:int32) + 4` in
  let source_bad = subst [n,`N:num`]
    `~(val(EL (N:num) offsets:int32) + 4 <= LENGTH(source_xs:int32 list))` in
  let positive = subst [n,`N:num`]
    `0 < val(EL (N:num) offsets:int32)` in
  SUBGOAL_THEN bad ASSUME_TAC THENL
   [(fun ((asl,_) as goal) ->
      let candidate th =
        let c = concl th in
        is_neg c &&
        let u = dest_neg c in
        is_comb u && is_comb(rator u) &&
        name_of(fst(strip_comb u)) = "<=" && c = source_bad in
      let premise = snd (List.find (fun (_,th) -> candidate th) asl) in
      let bad_th = MP (ARITH_RULE (mk_imp(source_bad,bad))) premise in
      ACCEPT_TAC bad_th goal);
    ALL_TAC] THEN
  ordinary_pack_marker "BAD_DERIVED" THEN
  SUBGOAL_THEN (subst [n,`N:num`]
    `read (memory :> bytes32
       (word_add premises (word(4 * N)))) s0 = EL (N:num) offsets:int32`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC positive THEN
  ordinary_pack_offset_steps [1] THEN
  ordinary_pack_marker "BAD_FIRST_STEP" THEN
  ordinary_pack_offset_steps [1] THEN
  ordinary_pack_marker "BAD_SECOND_STEP" THEN
  ASM_CASES_TAC (subst [n,`N:num`]
    `LENGTH(source_xs:int32 list) < val(EL (N:num) offsets:int32)`) THEN
  ordinary_pack_offset_steps [1] THEN
  ordinary_pack_marker "BAD_THIRD_STEP" THEN
  SUBGOAL_THEN (subst [n,`N:num`]
    `read (memory :> bytes32
       (word_add premises (word(4 * N)))) s0 = EL (N:num) offsets:int32`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ordinary_pack_offset_reject_finish;;

let ORDINARY_PACK_REJECT_FRAME_IDEMPOTENT = prove
 (`!stackpointer.
    ordinary_pack_reject_frame stackpointer ,,
    ordinary_pack_reject_frame stackpointer =
    ordinary_pack_reject_frame stackpointer`,
  GEN_TAC THEN REWRITE_TAC[ordinary_pack_reject_frame;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
  MAYCHANGE_IDEMPOT_TAC);;

let ORDINARY_PACK_REJECT_TRANS = prove
 (`!stackpointer P Q R.
    ensures x86 P Q (ordinary_pack_reject_frame stackpointer) /\
    ensures x86 Q R (ordinary_pack_reject_frame stackpointer)
    ==> ensures x86 P R (ordinary_pack_reject_frame stackpointer)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `Q:x86state->bool` THEN
  REWRITE_TAC[ORDINARY_PACK_REJECT_FRAME_IDEMPOTENT] THEN ASM_REWRITE_TAC[]);;

let ordinary_pack_offset_loop_entry = new_definition
 `ordinary_pack_offset_loop_entry pc source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_pack_mc /\
    read RIP s = word(pc + 0x130) /\
    ordinary_pack_offset_saved stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 s /\
    read RBX s = word 0 /\
    read RCX s = word(LENGTH offsets) /\
    read RSI s = word(LENGTH source_xs) /\
    read R11 s = premises /\
    read R8 s = rows /\ read R9 s = source /\
    read RDX s = constants /\ read RDI s = word(LENGTH fields_xs) /\
    read R10 s = fields /\
    read R12 s = word(LENGTH constants_xs) /\
    read R15 s = constants /\
    (read ZF s <=> 0 = LENGTH offsets) /\
    ordinary_pack_trace e source premises constants fields rows source_xs offsets
      constants_xs fields_xs rows_xs stackpointer s /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
    wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs`;;

let ordinary_pack_expose_offset_loop_entry ((asl,_) as goal) =
  let (_,entry) = List.find (fun (_,th) ->
    exists (fun t -> name_of t = "ordinary_pack_offset_loop_entry")
      (find_terms is_const (concl th))) asl in
  (MP_TAC (REWRITE_RULE[ordinary_pack_offset_loop_entry;
                        ordinary_pack_offset_saved; ordinary_pack_trace] entry) THEN
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) goal;;

let ordinary_pack_offset_loop_entry_finish : tactic =
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ordinary_pack_offset_loop_entry; ordinary_pack_trace;
              ordinary_pack_offset_saved] THEN
  REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
  ordinary_pack_try_arith THEN ordinary_pack_final_finish;;

let ORDINARY_PACK_OFFSET_REJECT_MC_CORRECT = prove
 (`!pc source premises constants fields rows source_xs offsets constants_xs
      fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_pack_span_valid source source_xs /\
    ordinary_pack_span_valid premises offsets /\
    ordinary_pack_span_valid constants constants_xs /\
    ordinary_pack_span_valid fields fields_xs /\
    ordinary_pack_span_valid rows rows_xs /\
    ordinary_pack_shape_valid offsets constants_xs fields_xs rows_xs /\
    ~(ordinary_pack_offsets_valid source_xs offsets) /\
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
      (\s. ordinary_pack_return 0 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_pack_trace e source premises constants fields rows
             source_xs offsets constants_xs fields_xs rows_xs stackpointer s /\
           wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
           wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
           wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
           wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
           wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs)
      (ordinary_pack_reject_frame stackpointer)`,
  REWRITE_TAC[ordinary_pack_span_valid; ordinary_pack_entry;
              ordinary_pack_return; ordinary_pack_trace;
              ordinary_pack_reject_frame; C_ARGUMENTS; SOME_FLAGS; ALL;
              NONOVERLAPPING_CLAUSES; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst ORDINARY_PACK_EXEC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(offsets:int32 list) <= 24 /\
    LENGTH(constants_xs:int32 list) <= 32 /\
    4 * LENGTH(offsets:int32 list) + LENGTH(constants_xs:int32 list) <=
      LENGTH(fields_xs:int32 list) /\
    LENGTH(offsets:int32 list) + 1 <= LENGTH(rows_xs:int32 list)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ordinary_pack_shape_valid]; ALL_TAC] THEN
  MP_TAC(ISPECL [`source_xs:int32 list`; `offsets:int32 list`]
    ORDINARY_PACK_FIRST_BAD_OFFSET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE
    [ordinary_pack_reject_frame; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
     SOME_FLAGS] ORDINARY_PACK_REJECT_TRANS) THEN
  EXISTS_TAC `ordinary_pack_offset_loop_entry pc source premises constants fields
    rows source_xs offsets constants_xs fields_xs rows_xs stackpointer returnaddress
    init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e` THEN
  CONJ_TAC THENL
   [ordinary_pack_validate_spans THEN
    ordinary_pack_marker "VALIDATED" THEN
    ordinary_pack_offset_exfalso THEN
    ordinary_pack_shape_exfalso THEN
    ordinary_pack_marker "AFTER_EXFALSO" THEN
    ordinary_pack_offset_steps_to `word(pc + 0x130):int64` 45 THEN
    ordinary_pack_marker "AT_OFFSET_LOOP" THEN
    ordinary_pack_offset_loop_entry_finish;
    REWRITE_TAC[ordinary_pack_offset_loop_entry; ordinary_pack_offset_saved] THEN
    ENSURES_INIT_TAC "s0" THEN
    ordinary_pack_expose_offset_loop_entry THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ASM_CASES_TAC `N = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`premises:int64`; `offsets:int32 list`; `s0:x86state`]
        WORDLIST_READS_32) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ordinary_pack_offset_bad_at_loop `0`;
      ALL_TAC] THEN

  ENSURES_WHILE_PUP_TAC `N:num` `pc + 0x130` `pc + 0x14c`
   `\i s.
     (ordinary_pack_offset_saved stackpointer returnaddress
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
      wordlist_from_memory(premises,LENGTH offsets) s = offsets) /\
     (read ZF s <=> i = LENGTH(offsets:int32 list))` THEN
  ordinary_pack_prepare_pup THENL
   [ASM_ARITH_TAC;

    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ordinary_pack_offset_saved] THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE);

    ALL_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ordinary_pack_offset_saved] THEN ENSURES_INIT_TAC "s0" THEN
    ordinary_pack_offset_steps [1] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ordinary_pack_offset_saved] THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
    ordinary_pack_try_arith;

    REWRITE_TAC[ordinary_pack_offset_saved] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes32 (word_add premises (word(4 * N)))) s0 =
        EL N offsets:int32`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ordinary_pack_offset_steps [1] THEN
    ordinary_pack_offset_bad_at_loop `N:num`] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH(offsets:int32 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `val(EL i offsets:int32) + 4 <= LENGTH(source_xs:int32 list)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ordinary_pack_offset_saved] THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `read (memory :> bytes32 (word_add premises (word(4 * i)))) s0 =
      EL i offsets:int32`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ordinary_pack_offset_steps (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ordinary_pack_offset_saved] THEN
  REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
  ordinary_pack_try_arith]);;
