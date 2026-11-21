(* Exact linked-byte rejection at the ordinary_flat_pack call. *)

let ORDINARY_ADAPTER_PACK_REJECT_CALL = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_adapter_span_valid source source_xs /\
    ordinary_adapter_span_valid premises offsets /\
    ordinary_adapter_span_valid constants constants_xs /\
    ordinary_adapter_span_valid fields fields_xs /\
    ordinary_adapter_span_valid rows rows_xs /\
    ordinary_pack_rejects source_xs offsets constants_xs fields_xs rows_xs /\
    72 <= val (word_sub stackpointer (word 160)) /\
    ALL (nonoverlapping
      (word_sub (word_sub stackpointer (word 160)) (word 72),80))
      [(word (pc + 0xd3),LENGTH ordinary_pack_mc);
       (source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (word (pc + 0xd3),LENGTH ordinary_pack_mc))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs)] /\
    ALL (nonoverlapping (fields,4 * LENGTH fields_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (rows,4 * LENGTH rows_xs);
       (guards,4 * LENGTH guards_xs); (makes,4 * LENGTH makes_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs);
       (word_sub stackpointer (word 152),168)] /\
    ALL (nonoverlapping (rows,4 * LENGTH rows_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs);
       (guards,4 * LENGTH guards_xs); (makes,4 * LENGTH makes_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs);
       (word_sub stackpointer (word 152),168)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 232),240))
      [(guards,4 * LENGTH guards_xs); (makes,4 * LENGTH makes_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)]
    ==> ensures x86
      (ordinary_adapter_before_pack pc source premises constants guards makes fields
         rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
         fields_xs rows_xs dest_xs scratch_xs stackpointer returnaddress
         init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_after_pack pc source premises constants guards makes fields
         rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
         fields_xs rows_xs dest_xs scratch_xs 0 stackpointer returnaddress
         init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
         scratch_xs stackpointer)`,
  REWRITE_TAC[ordinary_adapter_before_pack; ordinary_adapter_after_pack;
              ordinary_adapter_pre_pack_trace; ordinary_adapter_trace;
              ordinary_adapter_frame; ordinary_adapter_span_valid;
              ordinary_pack_span_valid; C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALL;
              NONOVERLAPPING_CLAUSES; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WORDLIST_FROM_MEMORY_32; fst ORDINARY_CESTA_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC ORDINARY_CESTA_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_sub (x:int64) (word 152)) (word 8) =
       word_sub x (word 160)`]) THEN
  X86_SUBROUTINE_SIM_TAC
    (ordinary_cesta_mc,ORDINARY_CESTA_EXEC,0xd3,ordinary_pack_mc,
     ORDINARY_PACK_REJECT_MC_CORRECT)
    [`pc + 0xd3`; `source:int64`; `premises:int64`; `constants:int64`;
     `fields:int64`; `rows:int64`; `source_xs:int32 list`; `offsets:int32 list`;
     `constants_xs:int32 list`; `fields_xs:int32 list`; `rows_xs:int32 list`;
     `word_sub (stackpointer:int64) (word 160)`; `word (pc + 0x552):int64`;
     `word (LENGTH(guards_xs:int32 list)):int64`; `fields:int64`;
     `word (LENGTH(fields_xs:int32 list)):int64`;
     `word (LENGTH(fields_xs:int32 list)):int64`; `rows:int64`;
     `word (LENGTH(rows_xs:int32 list)):int64`;
     `read events s1:uarch_event list`] 2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ordinary_pack_return; C_RETURN;
                              WORDLIST_FROM_MEMORY_32]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes64 stackpointer) s2 =
      read (memory :> bytes64 stackpointer) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 48))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 48))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 40))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 40))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 32))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 24))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 16))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 8))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 112))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 112))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 104))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 104))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 96))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 96))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 88))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 88))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 72))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 72))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 64))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 64))) s0 /\
    read (memory :> bytes (guards,4 * LENGTH(guards_xs:int32 list))) s2 =
      read (memory :> bytes (guards,4 * LENGTH guards_xs)) s0 /\
    read (memory :> bytes (makes,4 * LENGTH(makes_xs:int32 list))) s2 =
      read (memory :> bytes (makes,4 * LENGTH makes_xs)) s0 /\
    read (memory :> bytes (dest,4 * LENGTH(dest_xs:int32 list))) s2 =
      read (memory :> bytes (dest,4 * LENGTH dest_xs)) s0 /\
    read (memory :> bytes (scratch,4 * LENGTH(scratch_xs:int32 list))) s2 =
      read (memory :> bytes (scratch,4 * LENGTH scratch_xs)) s0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ordinary_adapter_preservation_tac; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ordinary_adapter_after_pack; ordinary_adapter_trace;
              C_ARGUMENTS; C_RETURN] THEN
  REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
  ordinary_adapter_composed_final_finish);;
