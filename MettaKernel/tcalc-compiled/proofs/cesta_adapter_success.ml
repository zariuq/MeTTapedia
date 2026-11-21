(* Exact linked-byte success continuation from ordinary_flat_pack to flat_fire. *)

let ordinary_adapter_before_leaf = new_definition
 `ordinary_adapter_before_leaf pc (source:int64) (premises:int64) (constants:int64)
      (guards:int64) (makes:int64) (fields:int64) (rows:int64)
      (dest:int64) (scratch:int64) (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_cesta_mc /\
    read RIP s = word pc /\
    read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    read (memory :> bytes64 (word_add stackpointer (word 8))) s = dest /\
    read (memory :> bytes64 (word_add stackpointer (word 16))) s = scratch /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15 /\
    C_ARGUMENTS [fields; rows; guards; word(LENGTH guards_xs); makes;
                 word(LENGTH makes_xs)] s /\
    ordinary_adapter_trace e source premises constants guards makes fields rows
      dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer s /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(guards,LENGTH guards_xs) s = guards_xs /\
    wordlist_from_memory(makes,LENGTH makes_xs) s = makes_xs /\
    wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
    wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs /\
    wordlist_from_memory(dest,LENGTH dest_xs) s = dest_xs /\
    wordlist_from_memory(scratch,LENGTH scratch_xs) s = scratch_xs`;;

let ORDINARY_ADAPTER_PACK_ACCEPT_CONTINUE = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    120 <= val stackpointer /\
    nonoverlapping (word_sub stackpointer (word 120),128)
      (word pc,LENGTH ordinary_cesta_mc) /\
    nonoverlapping (word pc,LENGTH ordinary_cesta_mc)
      (word_add stackpointer (word 8),16) /\
    ALL (nonoverlapping (word_add stackpointer (word 8),16))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs)]
    ==> ensures x86
      (ordinary_adapter_after_pack pc source premises constants guards makes fields
         rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
         fields_xs rows_xs dest_xs scratch_xs 1 stackpointer returnaddress
         init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_before_leaf pc source premises constants guards makes fields
         rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
         fields_xs rows_xs dest_xs scratch_xs stackpointer returnaddress
         init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
         scratch_xs stackpointer)`,
  REWRITE_TAC[ordinary_adapter_after_pack; ordinary_adapter_before_leaf;
              ordinary_adapter_frame; ordinary_adapter_trace; C_ARGUMENTS;
              C_RETURN; SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WORDLIST_FROM_MEMORY_32; fst ORDINARY_CESTA_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ordinary_adapter_expose_after_pack THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORDLIST_FROM_MEMORY_32]) THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--21) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(source,4 * LENGTH(source_xs:int32 list))) s21 =
      read (memory :> bytes(source,4 * LENGTH source_xs)) s0 /\
    read (memory :> bytes(premises,4 * LENGTH(offsets:int32 list))) s21 =
      read (memory :> bytes(premises,4 * LENGTH offsets)) s0 /\
    read (memory :> bytes(constants,4 * LENGTH(constants_xs:int32 list))) s21 =
      read (memory :> bytes(constants,4 * LENGTH constants_xs)) s0 /\
    read (memory :> bytes(guards,4 * LENGTH(guards_xs:int32 list))) s21 =
      read (memory :> bytes(guards,4 * LENGTH guards_xs)) s0 /\
    read (memory :> bytes(makes,4 * LENGTH(makes_xs:int32 list))) s21 =
      read (memory :> bytes(makes,4 * LENGTH makes_xs)) s0 /\
    read (memory :> bytes(fields,4 * LENGTH(fields_xs:int32 list))) s21 =
      read (memory :> bytes(fields,4 * LENGTH fields_xs)) s0 /\
    read (memory :> bytes(rows,4 * LENGTH(rows_xs:int32 list))) s21 =
      read (memory :> bytes(rows,4 * LENGTH rows_xs)) s0 /\
    read (memory :> bytes(dest,4 * LENGTH(dest_xs:int32 list))) s21 =
      read (memory :> bytes(dest,4 * LENGTH dest_xs)) s0 /\
    read (memory :> bytes(scratch,4 * LENGTH(scratch_xs:int32 list))) s21 =
      read (memory :> bytes(scratch,4 * LENGTH scratch_xs)) s0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ordinary_adapter_preservation_tac; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ordinary_adapter_before_leaf; ordinary_adapter_trace;
              C_ARGUMENTS; C_RETURN] THEN
  REPEAT CONJ_TAC THEN
  TRY (CONV_TAC WORD_RULE) THEN
  TRY (ASM_REWRITE_TAC[ORDINARY_ADAPTER_STACK_RESTORE;
                       ORDINARY_ADAPTER_AFTER_PACK_RETURN_ADDRESS]) THEN
  PRINT_GOAL_TAC THEN ordinary_adapter_final_finish THEN PRINT_GOAL_TAC);;
