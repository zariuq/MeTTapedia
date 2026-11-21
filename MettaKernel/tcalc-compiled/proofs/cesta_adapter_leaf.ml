(* Exact linked-byte composition at the adapter's flat_fire tail jump. *)

let ordinary_adapter_freeze_entry (sim : thm list -> tactic) : tactic =
  fun ((asl,_) as goal) ->
    let freeze th =
      let tm = concl th in
      let code_fact =
        try name_of(fst(strip_comb tm)) = "bytes_loaded"
        with Failure _ -> false in
      vfree_in `s0:x86state` tm && not code_fact && not(maychange_term tm) in
    let frozen = map snd (filter (fun (_,th) -> freeze th) asl) in
    (DISCARD_ASSUMPTIONS_TAC freeze THEN sim frozen) goal;;

let ORDINARY_ADAPTER_LEAF_FRAME_SUBSUMED = prove
 (`!fields rows dest scratch (fields_xs:int32 list) (rows_xs:int32 list)
      (makes_xs:int32 list) (dest_xs:int32 list) (scratch_xs:int32 list)
      stackpointer.
    LENGTH makes_xs <= LENGTH dest_xs /\ LENGTH makes_xs <= LENGTH scratch_xs
    ==>
    (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
     MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(dest,4 * LENGTH makes_xs);
                memory :> bytes(scratch,4 * LENGTH makes_xs);
                memory :> bytes(word_sub stackpointer (word 48),48)]) subsumed
    ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
      scratch_xs stackpointer`,
  REWRITE_TAC[ordinary_adapter_frame; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN PRINT_GOAL_TAC THEN SUBSUMED_MAYCHANGE_TAC);;

let ORDINARY_ADAPTER_LEAF_MC = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_pack_shape_valid offsets constants_xs fields_xs rows_xs /\
    flat_valid
      (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
      (ordinary_pack_result_rows source_xs offsets rows_xs) guards_xs makes_xs /\
    LENGTH makes_xs <= LENGTH dest_xs /\ LENGTH makes_xs <= LENGTH scratch_xs /\
    val dest + 4 * LENGTH dest_xs <= 2 EXP 64 /\
    val scratch + 4 * LENGTH scratch_xs <= 2 EXP 64 /\
    LENGTH fields_xs < 2 EXP 58 /\ LENGTH rows_xs < 2 EXP 58 /\
    LENGTH guards_xs < 2 EXP 58 /\ LENGTH makes_xs < 2 EXP 58 /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc); (word_sub stackpointer (word 48),56)]
      [(fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (guards,4 * LENGTH guards_xs); (makes,4 * LENGTH makes_xs);
       (dest,4 * LENGTH makes_xs); (scratch,4 * LENGTH makes_xs)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub stackpointer (word 48),56) /\
    ALL (nonoverlapping (scratch,4 * LENGTH makes_xs))
      [(fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (guards,4 * LENGTH guards_xs); (makes,4 * LENGTH makes_xs);
       (dest,4 * LENGTH makes_xs)] /\
    ALL (nonoverlapping (dest,4 * LENGTH makes_xs))
      [(fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (guards,4 * LENGTH guards_xs); (makes,4 * LENGTH makes_xs)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc) (dest,4 * LENGTH dest_xs) /\
    nonoverlapping (word pc,LENGTH flat_fire_mc) (scratch,4 * LENGTH scratch_xs) /\
    nonoverlapping (dest,4 * LENGTH dest_xs) (scratch,4 * LENGTH scratch_xs) /\
    nonoverlapping (dest,4 * LENGTH dest_xs)
      (word_sub stackpointer (word 48),48) /\
    nonoverlapping (scratch,4 * LENGTH scratch_xs)
      (word_sub stackpointer (word 48),48) /\
    ALL (nonoverlapping (dest,4 * LENGTH makes_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs)] /\
    ALL (nonoverlapping (scratch,4 * LENGTH makes_xs))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs)] /\
    ALL (nonoverlapping (word pc,LENGTH ordinary_cesta_mc))
      [(fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)] /\
    nonoverlapping (word pc,LENGTH ordinary_cesta_mc)
      (word_sub stackpointer (word 48),48) /\
    ALL (nonoverlapping (word_sub stackpointer (word 48),48))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs)]
    ==> ensures x86
      (ordinary_adapter_before_leaf pc source premises constants guards makes fields
         rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
         (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
         (ordinary_pack_result_rows source_xs offsets rows_xs)
         dest_xs scratch_xs stackpointer returnaddress
         init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (\s. ordinary_adapter_return
             (bitval (flat_guards_hold
               (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
               (ordinary_pack_result_rows source_xs offsets rows_xs) guards_xs))
             stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
             init_r14 init_r15 s /\
           ordinary_adapter_trace e source premises constants guards makes fields rows
             dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
             rows_xs dest_xs scratch_xs stackpointer s /\
           wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
           wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
           wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
           wordlist_from_memory(guards,LENGTH guards_xs) s = guards_xs /\
           wordlist_from_memory(makes,LENGTH makes_xs) s = makes_xs /\
           wordlist_from_memory(fields,LENGTH fields_xs) s =
             ordinary_pack_result_fields source_xs offsets constants_xs fields_xs /\
           wordlist_from_memory(rows,LENGTH rows_xs) s =
             ordinary_pack_result_rows source_xs offsets rows_xs /\
           wordlist_from_memory(dest,LENGTH dest_xs) s =
             APPEND
               (if flat_guards_hold
                 (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
                 (ordinary_pack_result_rows source_xs offsets rows_xs) guards_xs
                then flat_selected
                  (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
                  (ordinary_pack_result_rows source_xs offsets rows_xs) makes_xs
                else flat_prefix (LENGTH makes_xs) dest_xs)
               (ordinary_drop (LENGTH makes_xs) dest_xs) /\
           wordlist_from_memory(scratch,LENGTH scratch_xs) s =
             APPEND
               (if flat_guards_hold
                 (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
                 (ordinary_pack_result_rows source_xs offsets rows_xs) guards_xs
                then flat_selected
                  (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
                  (ordinary_pack_result_rows source_xs offsets rows_xs) makes_xs
                else flat_prefix (LENGTH makes_xs) scratch_xs)
               (ordinary_drop (LENGTH makes_xs) scratch_xs))
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
         scratch_xs stackpointer)`,
  REWRITE_TAC[ordinary_adapter_before_leaf; ordinary_adapter_return;
              ordinary_adapter_frame; ordinary_pack_shape_valid;
              C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WORDLIST_FROM_MEMORY_32; fst ORDINARY_CESTA_EXEC;
              COMPUTE_LENGTH_RULE flat_fire_mc] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH(ordinary_pack_result_fields source_xs offsets constants_xs
      (fields_xs:int32 list)) = LENGTH fields_xs /\
    LENGTH(ordinary_pack_result_rows source_xs offsets (rows_xs:int32 list)) =
      LENGTH rows_xs`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_PACK_RESULT_FIELDS_LENGTH;
      MATCH_MP_TAC ORDINARY_PACK_RESULT_ROWS_LENGTH] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ordinary_adapter_before_leaf;
                              ordinary_adapter_trace; C_ARGUMENTS;
                              WORDLIST_FROM_MEMORY_32]) THEN
  REPEAT (FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ordinary_adapter_freeze_entry (fun frozen ->
    X86_SUBROUTINE_SIM_TAC
      (ordinary_cesta_mc,ORDINARY_CESTA_EXEC,0,flat_fire_mc,
       FLAT_FIRE_TRACED_FULL_WORKSPACE_CORRECT)
      [`fields:int64`; `rows:int64`; `guards:int64`; `makes:int64`; `dest:int64`;
       `scratch:int64`;
       `ordinary_pack_result_fields source_xs offsets constants_xs
          fields_xs:int32 list`;
       `ordinary_pack_result_rows source_xs offsets rows_xs:int32 list`;
       `guards_xs:int32 list`; `makes_xs:int32 list`; `dest_xs:int32 list`;
       `scratch_xs:int32 list`; `pc:num`; `stackpointer:int64`;
       `returnaddress:int64`; `init_rbp:int64`; `init_rbx:int64`;
       `init_r12:int64`; `init_r13:int64`; `init_r14:int64`; `init_r15:int64`;
       `read events s0:uarch_event list`] 1 THENL
     [MAP_EVERY ASSUME_TAC frozen THEN
      REPEAT CONJ_TAC THEN
      TRY (ASM_REWRITE_TAC[C_ARGUMENTS; WORDLIST_FROM_MEMORY_32]) THEN
      TRY (MATCH_ACCEPT_TAC FLAT_TRACE_AT_ENTRY) THEN PRINT_GOAL_TAC;
      MAP_EVERY ASSUME_TAC frozen THEN
      RULE_ASSUM_TAC(REWRITE_RULE[flat_return; flat_trace; C_RETURN;
                                  WORDLIST_FROM_MEMORY_32]) THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN
   `read (memory :> bytes(source,4 * LENGTH(source_xs:int32 list))) s1 =
      read (memory :> bytes(source,4 * LENGTH source_xs)) s0 /\
    read (memory :> bytes(premises,4 * LENGTH(offsets:int32 list))) s1 =
      read (memory :> bytes(premises,4 * LENGTH offsets)) s0 /\
    read (memory :> bytes(constants,4 * LENGTH(constants_xs:int32 list))) s1 =
      read (memory :> bytes(constants,4 * LENGTH constants_xs)) s0 /\
    read (memory :> bytes(guards,4 * LENGTH(guards_xs:int32 list))) s1 =
      read (memory :> bytes(guards,4 * LENGTH guards_xs)) s0 /\
    read (memory :> bytes(makes,4 * LENGTH(makes_xs:int32 list))) s1 =
      read (memory :> bytes(makes,4 * LENGTH makes_xs)) s0 /\
    read (memory :> bytes(fields,4 * LENGTH(fields_xs:int32 list))) s1 =
      read (memory :> bytes(fields,4 * LENGTH fields_xs)) s0 /\
    read (memory :> bytes(rows,4 * LENGTH(rows_xs:int32 list))) s1 =
      read (memory :> bytes(rows,4 * LENGTH rows_xs)) s0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ordinary_adapter_preservation_tac; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ordinary_adapter_trace; WORDLIST_FROM_MEMORY_32] THEN
  REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
  PRINT_GOAL_TAC THEN W (fun (_,w) ->
    if is_comb w && name_of(fst(strip_comb w)) = "subsumed" then
      SUBSUMED_MAYCHANGE_TAC
    else if maychange_term w then MONOTONE_MAYCHANGE_TAC
    else ordinary_adapter_composed_final_finish)]));;
