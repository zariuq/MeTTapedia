(* Shared state and symbolic-execution tactics for premise-offset loops. *)

let ordinary_pack_offset_saved = new_definition
 `ordinary_pack_offset_saved stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    read RSP s = word_sub stackpointer (word 72) /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) s = init_r15 /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s = init_r14 /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s = init_r13 /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s = init_r12 /\
    read (memory :> bytes64 (word_sub stackpointer (word 40))) s = init_rbp /\
    read (memory :> bytes64 (word_sub stackpointer (word 48))) s = init_rbx`;;

let ordinary_pack_offset_normalize_state : tactic =
  ordinary_pack_normalize_state THEN
  fun ((asl,_) as goal) ->
    let stateful th = exists (fun v -> type_of v = `:x86state`) (frees(concl th)) in
    let facts = filter (fun th -> not(stateful th)) (map snd asl) in
    let memory_read_facts = map snd (filter (fun (_,th) ->
      let c = concl th in
      is_eq c &&
      let l,r = dest_eq c in
      exists (fun t -> name_of t = "bytes32") (find_terms is_const l) &&
      not (exists (fun v -> type_of v = `:x86state`) (frees r))) asl) in
    RULE_ASSUM_TAC (fun th -> if stateful th then
      (try REWRITE_RULE ([ORDINARY_PACK_OFFSET_SUB; VAL_WORD_EQ_EQ; VAL_WORD_ZX;
                          DIMINDEX_32; DIMINDEX_64; WORD_ADD_0] @
                         facts @ memory_read_facts) th
       with Failure _ -> th)
      else th) goal;;

let ordinary_pack_offset_steps indices =
  MAP_EVERY (fun _ goal ->
    let fresh = ordinary_pack_next_state_name goal in
    (ordinary_pack_offset_normalize_state THEN
     X86_VERBOSE_STEP_TAC ORDINARY_PACK_EXEC fresh THEN
     ordinary_pack_offset_normalize_state) goal) indices;;

let ordinary_pack_offset_steps_to target fuel =
  ASSUME_TAC(ARITH_RULE `!a b. ~(a < b) /\ ~(a = b) <=> b < a`) THEN
  ordinary_pack_steps_to_gen ordinary_pack_offset_normalize_state
    ORDINARY_PACK_EXEC target fuel;;
