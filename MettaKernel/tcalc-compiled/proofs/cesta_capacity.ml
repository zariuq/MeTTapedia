(* Exact linked-byte capacity-rejection proof for Cesta ordinary_flat_pack. *)

let ordinary_pack_capacity_controls ((asl,_) as goal) =
  let stateful th = exists (fun v -> type_of v = `:x86state`) (frees(concl th)) in
  let fact tm =
    let head = fst(strip_comb tm) in
    try Some(snd(List.find (fun (_,th) ->
      let c = concl th in
      not(stateful th) && is_comb c && fst(strip_comb c) = head && c = tm) asl))
    with Not_found -> None in
  let assume_new th goal =
    if exists (fun (_,old) -> concl old = concl th) asl then ALL_TAC goal
    else ASSUME_TAC th goal in
  match fact `~(0 < LENGTH(offsets:int32 list))` with
  | None -> ALL_TAC goal
  | Some zero ->
      let derived =
        (match fact `LENGTH(fields_xs:int32 list) <
                       4 * LENGTH(offsets:int32 list) + LENGTH(constants_xs:int32 list)` with
         | Some bad -> [MP (MP (ARITH_RULE (mk_imp(concl zero,
             mk_imp(concl bad,
               `LENGTH(fields_xs:int32 list) < LENGTH(constants_xs:int32 list)`))))
             zero) bad]
         | None -> []) @
        (match fact `LENGTH(rows_xs:int32 list) < LENGTH(offsets:int32 list) + 1` with
         | Some bad -> [MP (MP (ARITH_RULE (mk_imp(concl zero,
             mk_imp(concl bad,`LENGTH(rows_xs:int32 list) < 1`)))) zero) bad]
         | None -> []) in
      MAP_EVERY assume_new derived goal;;

let ORDINARY_PACK_CAPACITY_REJECT_MC_CORRECT = prove
 (`!pc source premises constants fields rows source_xs offsets constants_xs
      fields_xs rows_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    ordinary_pack_span_valid source source_xs /\
    ordinary_pack_span_valid premises offsets /\
    ordinary_pack_span_valid constants constants_xs /\
    ordinary_pack_span_valid fields fields_xs /\
    ordinary_pack_span_valid rows rows_xs /\
    LENGTH offsets <= 24 /\ LENGTH constants_xs <= 32 /\
    (LENGTH fields_xs < 4 * LENGTH offsets + LENGTH constants_xs \/
     LENGTH rows_xs < LENGTH offsets + 1) /\
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
  ordinary_pack_validate_spans THEN
  (ASM_CASES_TAC
    `LENGTH(fields_xs:int32 list) <
       4 * LENGTH(offsets:int32 list) + LENGTH(constants_xs:int32 list)` THENL
   [(ASM_CASES_TAC
      `LENGTH(rows_xs:int32 list) < LENGTH(offsets:int32 list) + 1` THENL
     [ALL_TAC; ALL_TAC]);
    SUBGOAL_THEN
     `LENGTH(rows_xs:int32 list) < LENGTH(offsets:int32 list) + 1`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]]) THEN
  ordinary_pack_capacity_controls THEN
  ordinary_pack_steps_to_return 50 THEN
  ordinary_pack_return_finish);;
