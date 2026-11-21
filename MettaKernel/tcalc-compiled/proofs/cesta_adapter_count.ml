let ordinary_adapter_count_exfalso ((asl,w) as goal) =
  try
    let (_,bad) = List.find (fun (_,th) -> concl th =
      `32 < LENGTH(guards_xs:int32 list) \/ 32 < LENGTH(makes_xs:int32 list) \/
       LENGTH(dest_xs:int32 list) < LENGTH(makes_xs:int32 list) \/
       LENGTH(scratch_xs:int32 list) < LENGTH(makes_xs:int32 list)`) asl in
    let zero_facts = List.filter_map (fun (_,th) ->
      try if rhs(concl th) = `0:num` then Some th else None
      with Failure _ -> None) asl in
    let simplified = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE zero_facts bad) in
    if concl simplified = `F`
    then ACCEPT_TAC(MATCH_MP (TAUT(mk_imp(`F`,w))) simplified) goal
    else ALL_TAC goal
  with Not_found -> ALL_TAC goal;;

let ORDINARY_ADAPTER_COUNT_REJECT_MC_CORRECT = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_adapter_span_valid source source_xs /\
    ordinary_adapter_span_valid premises offsets /\
    ordinary_adapter_span_valid constants constants_xs /\
    ordinary_adapter_span_valid guards guards_xs /\
    ordinary_adapter_span_valid makes makes_xs /\
    ordinary_adapter_span_valid fields fields_xs /\
    ordinary_adapter_span_valid rows rows_xs /\
    ordinary_adapter_span_valid dest dest_xs /\
    ordinary_adapter_span_valid scratch scratch_xs /\
    (32 < LENGTH guards_xs \/ 32 < LENGTH makes_xs \/
     LENGTH dest_xs < LENGTH makes_xs \/ LENGTH scratch_xs < LENGTH makes_xs) /\
    120 <= val stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 120),128))
      [(word pc,LENGTH ordinary_cesta_mc);
       (source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs)]
    ==> ensures x86
      (ordinary_adapter_entry pc source premises constants guards makes fields rows
         dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
         rows_xs dest_xs scratch_xs stackpointer returnaddress
         init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (\s. ordinary_adapter_return 2 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_adapter_reject_trace e stackpointer s /\
           wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
           wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
           wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
           wordlist_from_memory(guards,LENGTH guards_xs) s = guards_xs /\
           wordlist_from_memory(makes,LENGTH makes_xs) s = makes_xs /\
           wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
           wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs /\
           wordlist_from_memory(dest,LENGTH dest_xs) s = dest_xs /\
           wordlist_from_memory(scratch,LENGTH scratch_xs) s = scratch_xs)
      (ordinary_adapter_reject_frame stackpointer)`,
  REWRITE_TAC[ordinary_adapter_span_valid; ordinary_adapter_entry;
              ordinary_adapter_return; ordinary_adapter_reject_trace;
              ordinary_adapter_reject_frame; C_ARGUMENTS; SOME_FLAGS; ALL;
              NONOVERLAPPING_CLAUSES; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst ORDINARY_CESTA_EXEC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY VAL_INT64_TAC
    [`LENGTH(source_xs:int32 list)`; `LENGTH(offsets:int32 list)`;
     `LENGTH(constants_xs:int32 list)`; `LENGTH(guards_xs:int32 list)`;
     `LENGTH(makes_xs:int32 list)`; `LENGTH(fields_xs:int32 list)`;
     `LENGTH(rows_xs:int32 list)`; `LENGTH(dest_xs:int32 list)`;
     `LENGTH(scratch_xs:int32 list)`] THEN
  SUBGOAL_THEN
   `word_ushr (word(LENGTH(source_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(offsets:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(constants_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(guards_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(makes_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(fields_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(rows_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(dest_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(scratch_xs:int32 list)):int64) 61 = word 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CESTA_LENGTH_SHIFT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_and (word_zx (source:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (premises:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (constants:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (guards:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (makes:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (fields:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (rows:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (dest:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (scratch:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (source:int64):int32) (word 3) = word 0 /\
    word_and (word_zx (premises:int64):int32) (word 3) = word 0 /\
    word_and (word_zx (constants:int64):int32) (word 3) = word 0 /\
    word_and (word_zx (guards:int64):int32) (word 3) = word 0 /\
    word_and (word_zx (makes:int64):int32) (word 3) = word 0 /\
    word_and (word_zx (fields:int64):int32) (word 3) = word 0 /\
    word_and (word_zx (rows:int64):int32) (word 3) = word 0 /\
    word_and (word_zx (dest:int64):int32) (word 3) = word 0 /\
    word_and (word_zx (scratch:int64):int32) (word 3) = word 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CESTA_ALIGNED_BYTE; CESTA_ALIGNED_WORD32]; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ordinary_adapter_expose_entry THEN
  (fun goal -> Printf.printf "CESTA_ADAPTER initial goal\n%!"; ALL_TAC goal) THEN
  PRINT_GOAL_TAC THEN
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--25) THEN
  (* The source split follows its length test.  Every later span split starts
     at that span's test, so both branches include the test instruction. *)
  span_zero_cases `LENGTH(source_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--1);
    SUBGOAL_THEN `~(val (source:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--8)] THEN
  (span_zero_cases `LENGTH(offsets:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (premises:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)]) THEN
  TRY ordinary_adapter_count_exfalso THEN
  (span_zero_cases `LENGTH(constants_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (constants:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)]) THEN
  TRY ordinary_adapter_count_exfalso THEN
  (span_zero_cases `LENGTH(guards_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (guards:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--10)]) THEN
  TRY ordinary_adapter_count_exfalso THEN
  (span_zero_cases `LENGTH(makes_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (makes:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--10)]) THEN
  TRY ordinary_adapter_count_exfalso THEN
  (span_zero_cases `LENGTH(fields_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (fields:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--11)]) THEN
  TRY ordinary_adapter_count_exfalso THEN
  (span_zero_cases `LENGTH(rows_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (rows:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)]) THEN
  TRY ordinary_adapter_count_exfalso THEN
  (span_zero_cases `LENGTH(dest_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (dest:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)]) THEN
  TRY ordinary_adapter_count_exfalso THEN
  (span_zero_cases `LENGTH(scratch_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (scratch:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)]) THEN
  TRY ordinary_adapter_count_exfalso THEN
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9) THEN
  (ASM_CASES_TAC
   `32 < LENGTH(guards_xs:int32 list) \/ 32 < LENGTH(makes_xs:int32 list) \/
    LENGTH(dest_xs:int32 list) < LENGTH(makes_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--3)]) THEN
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9) THEN
  (SUBGOAL_THEN
   `(EventLoad(stackpointer:int64,8):uarch_event) =
    EventLoad(word_add (word_sub stackpointer (word 120)) (word 120),8)`
  ASSUME_TAC THENL [REWRITE_TAC[ORDINARY_ADAPTER_STACK_RESTORE]; ALL_TAC]) THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[ORDINARY_ADAPTER_STACK_RESTORE]) THEN
  ordinary_adapter_final_finish);;

