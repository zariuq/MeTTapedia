(* Exact linked-byte continuations after the Cesta ordinary_flat_pack call. *)

let ordinary_adapter_after_pack = new_definition
 `ordinary_adapter_after_pack pc (source:int64) (premises:int64) (constants:int64)
      (guards:int64) (makes:int64) (fields:int64) (rows:int64)
      (dest:int64) (scratch:int64) (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) returnvalue stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_cesta_mc /\
    read RIP s = word(pc + 0x552) /\
    read RSP s = word_sub stackpointer (word 152) /\
    read RAX s = word returnvalue /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    read (memory :> bytes64 (word_sub stackpointer (word 48))) s = init_rbx /\
    read (memory :> bytes64 (word_sub stackpointer (word 40))) s = init_rbp /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s = init_r12 /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s = init_r13 /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s = init_r14 /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) s = init_r15 /\
    read (memory :> bytes64 (word_sub stackpointer (word 112))) s = dest /\
    read (memory :> bytes64 (word_sub stackpointer (word 104))) s = scratch /\
    read (memory :> bytes64 (word_sub stackpointer (word 96))) s = guards /\
    read (memory :> bytes64 (word_sub stackpointer (word 88))) s =
      word(LENGTH makes_xs) /\
    read (memory :> bytes64 (word_sub stackpointer (word 72))) s = makes /\
    read (memory :> bytes64 (word_sub stackpointer (word 64))) s = rows /\
    read RBP s = word(LENGTH guards_xs) /\
    read RBX s = fields /\
    read R12 s = word(LENGTH fields_xs) /\
    read R13 s = word(LENGTH fields_xs) /\
    read R14 s = rows /\
    read R15 s = word(LENGTH rows_xs) /\
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

let ordinary_adapter_expose_after_pack ((asl,_) as goal) =
  let (_,entry) = List.find (fun (_,th) ->
    exists (fun t -> name_of t = "ordinary_adapter_after_pack")
      (find_terms is_const (concl th))) asl in
  (MP_TAC (REWRITE_RULE[ordinary_adapter_after_pack;
                        ordinary_adapter_trace] entry) THEN
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) goal;;

let ORDINARY_ADAPTER_SEQ_PRESERVES_READ = prove
 (`!c:(x86state,A)component (R1:x86state->x86state->bool) R2 s s'.
      (!s s'. R1 s s' ==> read c s' = read c s) /\
      (!s s'. R2 s s' ==> read c s' = read c s) /\
      (R1 ,, R2) s s'
      ==> read c s' = read c s`,
  REWRITE_TAC[seq] THEN MESON_TAC[]);;

let rec ordinary_adapter_preservation_tac : tactic = fun ((asl,w) as goal) ->
  if is_forall w then
    (REPEAT GEN_TAC THEN DISCH_TAC THEN ordinary_adapter_preservation_tac) goal
  else
    let left,right = dest_eq w in
    let c = rand(rator left) in
    let final = rand left and initial = rand right in
    let compatible th =
      maychange_term(concl th) &&
      rand(rator(concl th)) = initial && rand(concl th) = final in
    let frame = tryfind (fun (_,th) ->
      if compatible th then th else failwith "incompatible") asl in
    let relation = rator(rator(concl frame)) in
    let op,args = strip_comb relation in
    if name_of op = ",," then
     (print_endline ("PRESERVATION_SEQUENCE " ^
        string_of_thm ORDINARY_ADAPTER_SEQ_PRESERVES_READ);
      List.iter (fun (label,tm) -> Printf.printf "%s = %s : %s\n%!"
        label (string_of_term tm) (string_of_type(type_of tm)))
        ["c",c; "initial",initial; "final",final];
      let r1,r2 = match args with [r1;r2] -> r1,r2
        | _ -> failwith "ordinary adapter sequence" in
      List.iter (fun (label,tm) -> Printf.printf "%s = %s : %s\n%!"
        label (string_of_term tm) (string_of_type(type_of tm)))
        ["r1",r1; "r2",r2];
      (MATCH_MP_TAC (ISPECL [c;r1;r2;initial;final]
         ORDINARY_ADAPTER_SEQ_PRESERVES_READ) THEN
       REPEAT CONJ_TAC THENL
        [ordinary_adapter_preservation_tac;
         ordinary_adapter_preservation_tac;
         ACCEPT_TAC frame]) goal)
    else if name_of op = "MAYCHANGE" then
      let cs = hd args in
      (MATCH_MP_TAC (ISPECL [c;cs;initial;final]
         MAYCHANGE_PRESERVES_ORTHOGONAL_COMPONENT) THEN
       CONJ_TAC THENL
        [SIMP_TAC[ALL] THEN ORTHOGONAL_COMPONENTS_TAC; ACCEPT_TAC frame]) goal
    else failwith "ordinary adapter frame relation";;

let ordinary_adapter_frame_preservation initial final : tactic =
  ordinary_adapter_preservation_tac;;

let ORDINARY_ADAPTER_PACK_REJECT_CONTINUE = prove
 (`!pc source premises constants guards makes fields rows dest scratch
      source_xs offsets constants_xs guards_xs makes_xs fields_xs rows_xs
      dest_xs scratch_xs stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e.
    120 <= val stackpointer /\
    nonoverlapping (word_sub stackpointer (word 120),128)
      (word pc,LENGTH ordinary_cesta_mc)
    ==> ensures x86
      (ordinary_adapter_after_pack pc source premises constants guards makes fields
         rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
         fields_xs rows_xs dest_xs scratch_xs 0 stackpointer returnaddress
         init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e)
      (\s. ordinary_adapter_return 2 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_adapter_trace e source premises constants guards makes fields
             rows dest scratch source_xs offsets constants_xs guards_xs makes_xs
             fields_xs rows_xs dest_xs scratch_xs stackpointer s /\
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
  REWRITE_TAC[ordinary_adapter_after_pack; ordinary_adapter_return;
              ordinary_adapter_reject_frame; ordinary_adapter_trace; C_RETURN;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              WORDLIST_FROM_MEMORY_32; fst ORDINARY_CESTA_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ordinary_adapter_expose_after_pack THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORDLIST_FROM_MEMORY_32]) THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ordinary_adapter_steps ORDINARY_CESTA_EXEC (1--12) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(source,4 * LENGTH(source_xs:int32 list))) s12 =
      read (memory :> bytes(source,4 * LENGTH source_xs)) s0 /\
    read (memory :> bytes(premises,4 * LENGTH(offsets:int32 list))) s12 =
      read (memory :> bytes(premises,4 * LENGTH offsets)) s0 /\
    read (memory :> bytes(constants,4 * LENGTH(constants_xs:int32 list))) s12 =
      read (memory :> bytes(constants,4 * LENGTH constants_xs)) s0 /\
    read (memory :> bytes(guards,4 * LENGTH(guards_xs:int32 list))) s12 =
      read (memory :> bytes(guards,4 * LENGTH guards_xs)) s0 /\
    read (memory :> bytes(makes,4 * LENGTH(makes_xs:int32 list))) s12 =
      read (memory :> bytes(makes,4 * LENGTH makes_xs)) s0 /\
    read (memory :> bytes(fields,4 * LENGTH(fields_xs:int32 list))) s12 =
      read (memory :> bytes(fields,4 * LENGTH fields_xs)) s0 /\
    read (memory :> bytes(rows,4 * LENGTH(rows_xs:int32 list))) s12 =
      read (memory :> bytes(rows,4 * LENGTH rows_xs)) s0 /\
    read (memory :> bytes(dest,4 * LENGTH(dest_xs:int32 list))) s12 =
      read (memory :> bytes(dest,4 * LENGTH dest_xs)) s0 /\
    read (memory :> bytes(scratch,4 * LENGTH(scratch_xs:int32 list))) s12 =
      read (memory :> bytes(scratch,4 * LENGTH scratch_xs)) s0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    ordinary_adapter_frame_preservation `s0:x86state` `s12:x86state`;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  TRY (CONV_TAC WORD_RULE) THEN
  TRY (ASM_REWRITE_TAC[ORDINARY_ADAPTER_STACK_RESTORE]) THEN
  PRINT_GOAL_TAC THEN ordinary_adapter_final_finish THEN PRINT_GOAL_TAC);;
