(* Three exact linked-byte paths through the ordinary adapter. *)

let ORDINARY_ADAPTER_COUNT_REJECT_PATH = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_adapter_machine_valid pc source premises constants guards makes fields
      rows dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer /\
    (32 < LENGTH guards_xs \/ 32 < LENGTH makes_xs \/
     LENGTH dest_xs < LENGTH makes_xs \/ LENGTH scratch_xs < LENGTH makes_xs)
    ==> ensures x86
      (ordinary_adapter_entry pc source premises constants guards makes fields rows
        dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_output source premises constants guards makes fields rows
        dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
        scratch_xs stackpointer)`,
  REWRITE_TAC[ordinary_adapter_machine_valid; ordinary_adapter_spans_valid;
              ordinary_adapter_stack_valid; ordinary_adapter_exclusions] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ordinary_adapter_rejects source_xs offsets constants_xs guards_xs makes_xs
      fields_xs rows_xs dest_xs scratch_xs`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ORDINARY_ADAPTER_REJECTS_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC ORDINARY_ADAPTER_REJECT_FRAME_SUBSUMED THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC
   `ordinary_adapter_reject_result source premises constants guards makes fields rows
      dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ORDINARY_ADAPTER_REJECT_OUTPUT THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC
     `\s. ordinary_adapter_return 2 stackpointer returnaddress init_rbp init_rbx
            init_r12 init_r13 init_r14 init_r15 s /\
          ordinary_adapter_reject_trace e stackpointer s /\
          wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
          wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
          wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
          wordlist_from_memory(guards,LENGTH guards_xs) s = guards_xs /\
          wordlist_from_memory(makes,LENGTH makes_xs) s = makes_xs /\
          wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
          wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs /\
          wordlist_from_memory(dest,LENGTH dest_xs) s = dest_xs /\
          wordlist_from_memory(scratch,LENGTH scratch_xs) s = scratch_xs` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ordinary_adapter_reject_result; ordinary_adapter_raw_output] THEN
      GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC ORDINARY_ADAPTER_REJECT_TRACE_WIDEN THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC ORDINARY_ADAPTER_COUNT_REJECT_MC_CORRECT THEN
      ASM_REWRITE_TAC[]]]);;

let ORDINARY_ADAPTER_PACK_REJECT_PATH = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_adapter_machine_valid pc source premises constants guards makes fields
      rows dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer /\
    ~(32 < LENGTH guards_xs \/ 32 < LENGTH makes_xs \/
      LENGTH dest_xs < LENGTH makes_xs \/ LENGTH scratch_xs < LENGTH makes_xs) /\
    ordinary_pack_rejects source_xs offsets constants_xs fields_xs rows_xs
    ==> ensures x86
      (ordinary_adapter_entry pc source premises constants guards makes fields rows
        dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_output source premises constants guards makes fields rows
        dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
        scratch_xs stackpointer)`,
  REWRITE_TAC[ordinary_adapter_machine_valid; ordinary_adapter_spans_valid;
              ordinary_adapter_stack_valid; ordinary_adapter_exclusions] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ordinary_adapter_rejects source_xs offsets constants_xs guards_xs makes_xs
      fields_xs rows_xs dest_xs scratch_xs`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ORDINARY_ADAPTER_REJECTS_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC
   `ordinary_adapter_reject_result source premises constants guards makes fields rows
      dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ORDINARY_ADAPTER_REJECT_OUTPUT THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC
     `ordinary_adapter_before_pack pc source premises constants guards makes fields
        rows dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_PRE_PACK_FRAME_SUBSUMED THEN
      MATCH_MP_TAC ORDINARY_ADAPTER_BEFORE_PACK_MC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
      EXISTS_TAC
       `ordinary_adapter_after_pack pc source premises constants guards makes fields
          rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
          fields_xs rows_xs dest_xs scratch_xs 0 stackpointer returnaddress
          init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ORDINARY_ADAPTER_PACK_REJECT_CALL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC ORDINARY_ADAPTER_REJECT_FRAME_SUBSUMED THEN
        REWRITE_TAC[ordinary_adapter_reject_result; ordinary_adapter_raw_output] THEN
        MATCH_MP_TAC ORDINARY_ADAPTER_PACK_REJECT_CONTINUE THEN
        ASM_REWRITE_TAC[]]]]);;

let ORDINARY_ADAPTER_ACCEPT_PATH = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_adapter_machine_valid pc source premises constants guards makes fields
      rows dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer /\
    ~(ordinary_adapter_rejects source_xs offsets constants_xs guards_xs makes_xs
        fields_xs rows_xs dest_xs scratch_xs)
    ==> ensures x86
      (ordinary_adapter_entry pc source premises constants guards makes fields rows
        dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_output source premises constants guards makes fields rows
        dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
        scratch_xs stackpointer)`,
  REWRITE_TAC[ordinary_adapter_machine_valid; ordinary_adapter_spans_valid;
              ordinary_adapter_stack_valid; ordinary_adapter_exclusions] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~(32 < LENGTH guards_xs \/ 32 < LENGTH makes_xs \/
      LENGTH dest_xs < LENGTH makes_xs \/ LENGTH scratch_xs < LENGTH makes_xs)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_ADAPTER_REJECTS_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ordinary_adapter_shape_valid offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs /\
    ordinary_adapter_offsets_valid source_xs offsets`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ordinary_adapter_rejects]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ordinary_pack_shape_valid offsets constants_xs fields_xs rows_xs /\
    ordinary_pack_offsets_valid source_xs offsets`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_ADAPTER_SHAPE_VALID; ordinary_adapter_offsets_valid;
                  ordinary_pack_offsets_valid];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(guards_xs:int32 list) < 2 EXP 58 /\
    LENGTH(makes_xs:int32 list) < 2 EXP 58`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `flat_valid
      (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
      (ordinary_pack_result_rows source_xs offsets rows_xs) guards_xs makes_xs`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC
   `ordinary_adapter_accept_result source premises constants guards makes fields rows
      dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC ORDINARY_ADAPTER_ACCEPT_OUTPUT THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC
     `ordinary_adapter_before_pack pc source premises constants guards makes fields
        rows dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_PRE_PACK_FRAME_SUBSUMED THEN
      MATCH_MP_TAC ORDINARY_ADAPTER_BEFORE_PACK_MC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
      EXISTS_TAC
       `ordinary_adapter_after_pack pc source premises constants guards makes fields
          rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
          (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
          (ordinary_pack_result_rows source_xs offsets rows_xs)
          dest_xs scratch_xs 1 stackpointer returnaddress
          init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ORDINARY_ADAPTER_PACK_ACCEPT_CALL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
        EXISTS_TAC
         `ordinary_adapter_before_leaf pc source premises constants guards makes fields
            rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
            (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
            (ordinary_pack_result_rows source_xs offsets rows_xs)
            dest_xs scratch_xs stackpointer returnaddress
            init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC ORDINARY_ADAPTER_PACK_ACCEPT_CONTINUE THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[ordinary_adapter_accept_result; ordinary_adapter_raw_output] THEN
          MATCH_MP_TAC ORDINARY_ADAPTER_LEAF_MC THEN ASM_REWRITE_TAC[]]]]]);;

let ORDINARY_ADAPTER_MC_CORRECT = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_adapter_machine_valid pc source premises constants guards makes fields
      rows dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer
    ==> ensures x86
      (ordinary_adapter_entry pc source premises constants guards makes fields rows
        dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_output source premises constants guards makes fields rows
        dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
        rows_xs dest_xs scratch_xs stackpointer returnaddress
        init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
        scratch_xs stackpointer)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC
   `32 < LENGTH(guards_xs:int32 list) \/ 32 < LENGTH(makes_xs:int32 list) \/
    LENGTH(dest_xs:int32 list) < LENGTH(makes_xs:int32 list) \/
    LENGTH(scratch_xs:int32 list) < LENGTH(makes_xs:int32 list)` THENL
   [MATCH_MP_TAC ORDINARY_ADAPTER_COUNT_REJECT_PATH THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC
     `ordinary_adapter_rejects source_xs offsets constants_xs guards_xs makes_xs
        fields_xs rows_xs dest_xs scratch_xs` THENL
     [SUBGOAL_THEN
       `ordinary_pack_rejects source_xs offsets constants_xs fields_xs rows_xs`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[ORDINARY_ADAPTER_REJECTS_EQ]; ALL_TAC] THEN
      MATCH_MP_TAC ORDINARY_ADAPTER_PACK_REJECT_PATH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ORDINARY_ADAPTER_ACCEPT_PATH THEN ASM_REWRITE_TAC[]]]);;
