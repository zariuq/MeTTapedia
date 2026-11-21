(* Common caller-visible result for all three adapter paths. *)

let ordinary_adapter_raw_output = new_definition
 `ordinary_adapter_raw_output returnvalue (result_fields:int32 list)
      (result_rows:int32 list) (result_dest:int32 list)
      (result_scratch:int32 list) source premises constants guards makes fields rows dest scratch
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (guards_xs:int32 list) (makes_xs:int32 list) (fields_xs:int32 list)
      (rows_xs:int32 list) (dest_xs:int32 list) (scratch_xs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 e s <=>
    ordinary_adapter_return returnvalue stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s /\
    ordinary_adapter_trace e source premises constants guards makes fields rows
      dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer s /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(guards,LENGTH guards_xs) s = guards_xs /\
    wordlist_from_memory(makes,LENGTH makes_xs) s = makes_xs /\
    wordlist_from_memory(fields,LENGTH fields_xs) s = result_fields /\
    wordlist_from_memory(rows,LENGTH rows_xs) s = result_rows /\
    wordlist_from_memory(dest,LENGTH dest_xs) s = result_dest /\
    wordlist_from_memory(scratch,LENGTH scratch_xs) s = result_scratch`;;

let ordinary_adapter_output = new_definition
 `ordinary_adapter_output source premises constants guards makes fields rows
      dest scratch (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    ordinary_adapter_raw_output
      (ordinary_adapter_return_value source_xs offsets constants_xs guards_xs
        makes_xs fields_xs rows_xs dest_xs scratch_xs)
      (ordinary_adapter_result_fields source_xs offsets constants_xs guards_xs
        makes_xs fields_xs rows_xs dest_xs scratch_xs)
      (ordinary_adapter_result_rows source_xs offsets constants_xs guards_xs
        makes_xs fields_xs rows_xs dest_xs scratch_xs)
      (ordinary_adapter_result_dest source_xs offsets constants_xs guards_xs
        makes_xs fields_xs rows_xs dest_xs scratch_xs)
      (ordinary_adapter_result_scratch source_xs offsets constants_xs guards_xs
        makes_xs fields_xs rows_xs dest_xs scratch_xs)
      source premises constants guards makes fields rows dest scratch source_xs
      offsets constants_xs guards_xs makes_xs fields_xs rows_xs dest_xs scratch_xs
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 e s`;;

let ordinary_adapter_reject_result = new_definition
 `ordinary_adapter_reject_result source premises constants guards makes fields rows
      dest scratch (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    ordinary_adapter_raw_output 2 fields_xs rows_xs dest_xs scratch_xs
      source premises constants guards makes fields rows dest scratch source_xs
      offsets constants_xs guards_xs makes_xs fields_xs rows_xs dest_xs scratch_xs
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 e s`;;

let ordinary_adapter_accept_result = new_definition
 `ordinary_adapter_accept_result source premises constants guards makes fields rows
      dest scratch (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    ordinary_adapter_raw_output
      (bitval (flat_guards_hold
        (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
        (ordinary_pack_result_rows source_xs offsets rows_xs) guards_xs))
      (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
      (ordinary_pack_result_rows source_xs offsets rows_xs)
      (APPEND
        (if flat_guards_hold
          (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
          (ordinary_pack_result_rows source_xs offsets rows_xs) guards_xs
         then flat_selected
          (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
          (ordinary_pack_result_rows source_xs offsets rows_xs) makes_xs
         else flat_prefix (LENGTH makes_xs) dest_xs)
        (ordinary_drop (LENGTH makes_xs) dest_xs))
      (APPEND
        (if flat_guards_hold
          (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
          (ordinary_pack_result_rows source_xs offsets rows_xs) guards_xs
         then flat_selected
          (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
          (ordinary_pack_result_rows source_xs offsets rows_xs) makes_xs
         else flat_prefix (LENGTH makes_xs) scratch_xs)
        (ordinary_drop (LENGTH makes_xs) scratch_xs))
      source premises constants guards makes fields rows dest scratch source_xs
      offsets constants_xs guards_xs makes_xs fields_xs rows_xs dest_xs scratch_xs
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 e s`;;

let ORDINARY_ADAPTER_REJECT_OUTPUT = prove
 (`!source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s.
    ordinary_adapter_rejects source_xs offsets constants_xs guards_xs makes_xs
      fields_xs rows_xs dest_xs scratch_xs /\
    ordinary_adapter_reject_result source premises constants guards makes fields rows
      dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 e s
    ==> ordinary_adapter_output source premises constants guards makes fields rows
          dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
          rows_xs dest_xs scratch_xs stackpointer returnaddress init_rbp init_rbx
          init_r12 init_r13 init_r14 init_r15 e s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (fun th -> REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC
      (REWRITE_RULE[ordinary_adapter_reject_result; ordinary_adapter_raw_output]
        th))) THEN
  REWRITE_TAC[ordinary_adapter_output; ordinary_adapter_raw_output] THEN
  FIRST_ASSUM(fun th ->
    ASM_REWRITE_TAC[MATCH_MP ORDINARY_ADAPTER_REJECT_OUTPUTS th]));;

let ORDINARY_ADAPTER_ACCEPT_OUTPUT = prove
 (`!source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s.
    ~(ordinary_adapter_rejects source_xs offsets constants_xs guards_xs makes_xs
        fields_xs rows_xs dest_xs scratch_xs) /\
    ordinary_adapter_accept_result source premises constants guards makes fields rows
      dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 e s
    ==> ordinary_adapter_output source premises constants guards makes fields rows
          dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
          rows_xs dest_xs scratch_xs stackpointer returnaddress init_rbp init_rbx
          init_r12 init_r13 init_r14 init_r15 e s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (fun th -> REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC
      (REWRITE_RULE[ordinary_adapter_accept_result; ordinary_adapter_raw_output]
        th))) THEN
  REWRITE_TAC[ordinary_adapter_output; ordinary_adapter_raw_output] THEN
  FIRST_ASSUM(fun th ->
    ASM_REWRITE_TAC[MATCH_MP ORDINARY_ADAPTER_ACCEPT_OUTPUTS th]));;

let ordinary_adapter_spans_valid = new_definition
 `ordinary_adapter_spans_valid (source:int64) (premises:int64) (constants:int64)
      (guards:int64) (makes:int64) (fields:int64) (rows:int64) (dest:int64)
      (scratch:int64) (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) <=>
    ordinary_adapter_span_valid source source_xs /\
    ordinary_adapter_span_valid premises offsets /\
    ordinary_adapter_span_valid constants constants_xs /\
    ordinary_adapter_span_valid guards guards_xs /\
    ordinary_adapter_span_valid makes makes_xs /\
    ordinary_adapter_span_valid fields fields_xs /\
    ordinary_adapter_span_valid rows rows_xs /\
    ordinary_adapter_span_valid dest dest_xs /\
    ordinary_adapter_span_valid scratch scratch_xs`;;

let ordinary_adapter_stack_valid = new_definition
 `ordinary_adapter_stack_valid (stackpointer:int64) <=>
    120 <= val stackpointer /\ 152 <= val stackpointer /\
    72 <= val (word_sub stackpointer (word 160))`;;

let ordinary_adapter_exclusions = new_definition
 `ordinary_adapter_exclusions pc (source:int64) (premises:int64) (constants:int64)
      (guards:int64) (makes:int64) (fields:int64) (rows:int64) (dest:int64)
      (scratch:int64) (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) (stackpointer:int64) <=>
    ALL (nonoverlapping (word_sub stackpointer (word 120),128))
      [(word pc,LENGTH ordinary_cesta_mc);
       (source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 152),152))
      [(word pc,LENGTH ordinary_cesta_mc);
       (source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs)] /\
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
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)] /\
    ALL (nonoverlapping (word pc,LENGTH ordinary_cesta_mc))
      [(fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
       (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)] /\
    nonoverlapping (word pc,LENGTH ordinary_cesta_mc)
      (word_add stackpointer (word 8),16) /\
    ALL (nonoverlapping (word_add stackpointer (word 8),16))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
       (scratch,4 * LENGTH scratch_xs)] /\
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
    ALL (nonoverlapping (word_sub stackpointer (word 48),48))
      [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
       (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
       (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
       (rows,4 * LENGTH rows_xs)]`;;

let ordinary_adapter_machine_valid = new_definition
 `ordinary_adapter_machine_valid pc (source:int64) (premises:int64)
      (constants:int64) (guards:int64) (makes:int64) (fields:int64) (rows:int64)
      (dest:int64) (scratch:int64) (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) (stackpointer:int64) <=>
    ordinary_adapter_spans_valid source premises constants guards makes fields rows
      dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs /\
    ordinary_adapter_stack_valid stackpointer /\
    ordinary_adapter_exclusions pc source premises constants guards makes fields rows
      dest scratch source_xs offsets constants_xs guards_xs makes_xs fields_xs
      rows_xs dest_xs scratch_xs stackpointer /\
    LENGTH fields_xs < 2 EXP 58 /\ LENGTH rows_xs < 2 EXP 58 /\
    (~(ordinary_adapter_rejects source_xs offsets constants_xs guards_xs makes_xs
        fields_xs rows_xs dest_xs scratch_xs) ==>
     flat_valid
       (ordinary_pack_result_fields source_xs offsets constants_xs fields_xs)
       (ordinary_pack_result_rows source_xs offsets rows_xs) guards_xs makes_xs)`;;

