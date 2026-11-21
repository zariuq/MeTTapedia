(* Composition at the Cesta adapter's actual ordinary_flat_pack call. *)

loadt "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/cesta_adapter_pack_core.ml";;

let ORDINARY_ADAPTER_BEFORE_PACK_MC = prove
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
    ~(32 < LENGTH guards_xs \/ 32 < LENGTH makes_xs \/
      LENGTH dest_xs < LENGTH makes_xs \/ LENGTH scratch_xs < LENGTH makes_xs) /\
    152 <= val stackpointer /\
    ALL (nonoverlapping (word_sub stackpointer (word 152),152))
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
      (ordinary_adapter_before_pack pc source premises constants guards makes fields rows
         dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
         rows_xs dest_xs scratch_xs stackpointer returnaddress
         init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_pre_pack_frame stackpointer)`,
  REWRITE_TAC[ordinary_adapter_span_valid; ordinary_adapter_entry;
              ordinary_adapter_before_pack; ordinary_adapter_pre_pack_trace;
              ordinary_adapter_pre_pack_frame; C_ARGUMENTS; SOME_FLAGS; ALL;
              NONOVERLAPPING_CLAUSES; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst ORDINARY_CESTA_EXEC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `~(32 < LENGTH(guards_xs:int32 list)) /\
    ~(32 < LENGTH(makes_xs:int32 list)) /\
    ~(LENGTH(dest_xs:int32 list) < LENGTH(makes_xs:int32 list)) /\
    ~(LENGTH(scratch_xs:int32 list) < LENGTH(makes_xs:int32 list))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
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
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--25) THEN
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
  (span_zero_cases `LENGTH(constants_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (constants:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)]) THEN
  (span_zero_cases `LENGTH(guards_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (guards:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--10)]) THEN
  (span_zero_cases `LENGTH(makes_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (makes:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--10)]) THEN
  (span_zero_cases `LENGTH(fields_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (fields:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--11)]) THEN
  (span_zero_cases `LENGTH(rows_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (rows:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)]) THEN
  (span_zero_cases `LENGTH(dest_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (dest:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)]) THEN
  (span_zero_cases `LENGTH(scratch_xs:int32 list)` THENL
   [ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--2);
    SUBGOAL_THEN `~(val (scratch:int64) = 0)` ASSUME_TAC THENL
     [ordinary_adapter_meson; ALL_TAC] THEN
    ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--9)]) THEN
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--28) THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  TRY (CONV_TAC WORD_RULE) THEN ordinary_pack_try_arith THEN
  TRY (ASM_REWRITE_TAC[ORDINARY_ADAPTER_STACK_RESTORE]) THEN
  ordinary_adapter_final_finish);;
