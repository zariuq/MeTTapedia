(* Unified exact linked-byte refusal for Cesta ordinary_flat_pack. *)

let ORDINARY_PACK_REJECT_MC_CORRECT = prove
 (`!pc source premises constants fields rows source_xs offsets constants_xs
      fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_pack_span_valid source source_xs /\
    ordinary_pack_span_valid premises offsets /\
    ordinary_pack_span_valid constants constants_xs /\
    ordinary_pack_span_valid fields fields_xs /\
    ordinary_pack_span_valid rows rows_xs /\
    ordinary_pack_rejects source_xs offsets constants_xs fields_xs rows_xs /\
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `ordinary_pack_shape_valid offsets constants_xs fields_xs rows_xs` THENL
   [SUBGOAL_THEN
     `~(ordinary_pack_offsets_valid source_xs offsets)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ordinary_pack_rejects]; ALL_TAC] THEN
    MATCH_MP_TAC ORDINARY_PACK_OFFSET_REJECT_MC_CORRECT THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC
     `24 < LENGTH(offsets:int32 list) \/ 32 < LENGTH(constants_xs:int32 list)` THENL
     [MATCH_MP_TAC ORDINARY_PACK_COUNT_REJECT_MC_CORRECT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ORDINARY_PACK_CAPACITY_REJECT_MC_CORRECT THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `LENGTH(offsets:int32 list) <= 24 /\
        LENGTH(constants_xs:int32 list) <= 32` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[ordinary_pack_rejects; ordinary_pack_shape_valid]]]);;
