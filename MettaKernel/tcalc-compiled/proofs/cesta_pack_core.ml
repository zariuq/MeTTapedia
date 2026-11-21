(* Exact linked-byte proof for the Cesta-generated ordinary_flat_pack.
   The checked-failure stub is outside the admitted valid-span contract. *)

let ordinary_pack_linked_image_mc =
  define_from_elf "ordinary_pack_linked_image_mc" ordinary_pack_object;;

(* Prove the exact linked pack body, not its relocatable standalone counterpart.
   Adapter composition obtains this body at offset 0xd3 in the same image. *)
let ordinary_pack_mc = define_word_list "ordinary_pack_mc"
  (term_of_bytes(Bytes.sub (load_elf_contents_x86 ordinary_pack_object)
                  0xd3 0x212));;

let ORDINARY_PACK_IN_IMAGE = BYTES_LOADED_SUBPROGRAM_RULE
  ordinary_pack_linked_image_mc ordinary_pack_mc 0xd3;;

let ORDINARY_PACK_EXEC = X86_MK_EXEC_RULE ordinary_pack_mc;;

needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/ordinary_pack_spec.ml";;

let ordinary_pack_entry = new_definition
 `ordinary_pack_entry pc source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_pack_mc /\
    read RIP s = word pc /\
    read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    C_ARGUMENTS [source; word(LENGTH source_xs);
                 premises; word(LENGTH offsets);
                 constants; word(LENGTH constants_xs)] s /\
    read (memory :> bytes64 (word_add stackpointer (word 8))) s = fields /\
    read (memory :> bytes64 (word_add stackpointer (word 16))) s =
      word(LENGTH fields_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 24))) s = rows /\
    read (memory :> bytes64 (word_add stackpointer (word 32))) s =
      word(LENGTH rows_xs) /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15 /\
    read events s = e /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
    wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs`;;

let ordinary_pack_return = new_definition
 `ordinary_pack_return returnvalue stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    read RIP s = returnaddress /\
    read RSP s = word_add stackpointer (word 8) /\
    C_RETURN s = word returnvalue /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15`;;

let ordinary_pack_trace = new_definition
 `ordinary_pack_trace e source premises constants fields rows
      (source_xs:int32 list) (offsets:int32 list) (constants_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) stackpointer s <=>
    ?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2
           [(source,4 * LENGTH source_xs);
            (premises,4 * LENGTH offsets);
            (constants,4 * LENGTH constants_xs);
            (word_sub stackpointer (word 72),112)]
           [(word_sub stackpointer (word 72),72);
            (fields,4 * LENGTH fields_xs);
            (rows,4 * LENGTH rows_xs)]`;;

let ordinary_pack_reject_frame = new_definition
 `ordinary_pack_reject_frame stackpointer : x86state->x86state->bool =
    MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 72),72)]`;;

let ordinary_pack_frame = new_definition
 `ordinary_pack_frame fields rows (fields_xs:int32 list) (rows_xs:int32 list)
      stackpointer : x86state->x86state->bool =
    ordinary_pack_reject_frame stackpointer ,,
    MAYCHANGE [memory :> bytes(fields,4 * LENGTH fields_xs);
               memory :> bytes(rows,4 * LENGTH rows_xs)]`;;

let ordinary_pack_word_sub_sub = prove
 (`!(x:N word) m n.
     word_sub (word_sub x (word m)) (word n) = word_sub x (word (m + n))`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_STACK_RESTORE = prove
 (`!sp:int64.
     word_add (word_sub sp (word 72)) (word 72) = sp /\
     word_add (word_sub sp (word 72)) (word 80) = word_add sp (word 8) /\
     word_add (word_sub sp (word 72)) (word 88) = word_add sp (word 16) /\
     word_add (word_sub sp (word 72)) (word 96) = word_add sp (word 24) /\
     word_add (word_sub sp (word 72)) (word 104) = word_add sp (word 32)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_WORD_SCALE4 = prove
 (`!n. word_shl (word n:int64) 2 = word(4 * n)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_WORD_FIELD_COUNT = prove
 (`!nk nc. word_add (word nc:int64) (word_shl (word nk) 2) =
             word(4 * nk + nc)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_WORD_FIELD_COUNT_ADD = prove
 (`!nk nc. word_add (word nc:int64) (word(4 * nk)) = word(4 * nk + nc)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_WORD_ROW_COUNT = prove
 (`!n. word_add (word n:int64) (word 1) = word(n + 1)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_PACK_COUNT_VAL = prove
 (`!nk nc. nk <= 24 /\ nc <= 32
     ==> val(word(4 * nk + nc):int64) = 4 * nk + nc /\
         val(word(nk + 1):int64) = nk + 1 /\
         val(word(4 * nk):int64) = 4 * nk`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
  ASM_ARITH_TAC);;

let ORDINARY_WORD_ZX_EQ_0 = prove
 (`!x:M word. dimindex(:M) <= dimindex(:N)
     ==> ((word_zx:M word->N word) x = word 0 <=> x = word 0)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD_ZX; VAL_WORD_0]);;

let ordinary_pack_normalize_state : tactic = fun ((asl,_) as goal) ->
  let stateful th = exists (fun v -> type_of v = `:x86state`) (frees(concl th)) in
  let base_facts = filter (fun th -> not(stateful th)) (map snd asl) in
  let zero_facts = filter (fun th ->
    try rhs(concl th) = `0:num` with Failure _ -> false) base_facts in
  let normalized_facts = List.filter_map (fun th ->
    try let th' = CONV_RULE NUM_REDUCE_CONV
          (REWRITE_RULE (ADD_CLAUSES::zero_facts) th) in
        if concl th' = `T` then None else Some th'
    with Failure _ -> None) base_facts in
  let arith_facts = base_facts @ normalized_facts in
  let facts = arith_facts @ List.filter_map (fun th ->
    try Some(REWRITE_RULE[ARITH_RULE `a <= b <=> ~(b < a)`] th)
    with Failure _ -> None) arith_facts in
  let rules = [ordinary_pack_word_sub_sub;
               ORDINARY_PACK_STACK_RESTORE; CESTA_STACK_RESTORE; CESTA_BYTE_RESIDUE; CESTA_LOW_BYTE_JOIN;
               CESTA_SUB_ZERO; WORD_AND_0; WORD_OR_0; WORD_OR_EQ_0;
               ORDINARY_PACK_WORD_SCALE4; ORDINARY_PACK_WORD_FIELD_COUNT;
               ORDINARY_PACK_WORD_FIELD_COUNT_ADD; ORDINARY_PACK_WORD_ROW_COUNT; ORDINARY_PACK_COUNT_VAL;
               WORD_ULT; WORD_ULE; VAL_WORD_EQ_EQ;
               ORDINARY_WORD_ZX_EQ_0; WORD_OR_REFL; WORD_AND_REFL;
               WORD_SUB_0; VAL_WORD_0; VAL_WORD_1; VAL_EQ_0; ARITH_EQ;
               REFL_CLAUSE; COND_CLAUSES; NOT_CLAUSES; CONJUNCT1 LT; LENGTH;
               DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128;
               ARITH_RULE `n = 0 <=> ~(0 < n)`;
               ARITH_RULE `n <= 0 <=> n = 0`;
               ARITH_RULE `~(a < b) /\ ~(a = b) <=> b < a`;
               ARITH_RULE `~(a < b \/ a = b) <=> b < a`] in
  let try_rule rs th = try REWRITE_RULE rs th with Failure _ -> th in
  let try_conv conv th = try CONV_RULE conv th with Failure _ -> th in
  (RULE_ASSUM_TAC (fun th -> if stateful th then
    try_rule (rules @ facts) (try_conv WORD_REDUCE_CONV (try_rule rules th))
    else th) THEN
   RULE_ASSUM_TAC (fun th ->
     let c = concl th in
     if is_eq c && is_read_rip(fst(dest_eq c)) then
       simplify_conditionals_with_facts facts
         (SIMP_RULE ((COND_CLAUSES::NOT_CLAUSES::rules) @ facts) th)
     else th)) goal;;

let ordinary_pack_data_finish : tactic =
  REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES; flat_prefix; ordinary_drop;
              EQ_SYM_EQ; GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[];;

let ordinary_pack_concrete_event_finish : tactic =
  TRY (REWRITE_TAC[ordinary_pack_word_sub_sub; ORDINARY_PACK_STACK_RESTORE;
    WORD_RULE `word_add (word_sub (word_sub x (word 72)) (word 72)) (word 80):int64 =
      word_add (word_sub x (word 72)) (word 8)`;
    WORD_RULE `word_add (word_sub (word_sub x (word 72)) (word 72)) (word 96):int64 =
      word_add (word_sub x (word 72)) (word 24)`;
    WORD_RULE `word_add (word_sub (word_sub x (word 72)) (word 72)) (word 104):int64 =
      word_add (word_sub x (word 72)) (word 32)`;
    WORD_RULE `word_add (word_sub x (word 144)) (word 80):int64 =
      word_add (word_sub x (word 72)) (word 8)`;
    WORD_RULE `word_add (word_sub x (word 144)) (word 96):int64 =
      word_add (word_sub x (word 72)) (word 24)`;
    WORD_RULE `word_add (word_sub x (word 144)) (word 104):int64 =
      word_add (word_sub x (word 72)) (word 32)`;
    WORD_RULE `word_add x (word 8):int64 =
      word_add (word_sub x (word 72)) (word 80)`;
    WORD_RULE `word_add x (word 16):int64 =
      word_add (word_sub x (word 72)) (word 88)`;
    WORD_RULE `word_add x (word 24):int64 =
      word_add (word_sub x (word 72)) (word 96)`;
    WORD_RULE `word_add x (word 32):int64 =
      word_add (word_sub x (word 72)) (word 104)`;
    WORD_RULE `word_sub x (word 8):int64 =
      word_add (word_sub x (word 72)) (word 64)`;
    WORD_RULE `word_sub x (word 16):int64 =
      word_add (word_sub x (word 72)) (word 56)`;
    WORD_RULE `word_sub x (word 24):int64 =
      word_add (word_sub x (word 72)) (word 48)`;
    WORD_RULE `word_sub x (word 32):int64 =
      word_add (word_sub x (word 72)) (word 40)`;
    WORD_RULE `word_sub x (word 40):int64 =
      word_add (word_sub x (word 72)) (word 32)`;
    WORD_RULE `word_sub x (word 48):int64 =
      word_add (word_sub x (word 72)) (word 24)`]) THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let numeric tm =
      exists (fun op -> is_binary op tm &&
        type_of(fst(dest_binary op tm)) = `:num`)
        ["="; "<"; "<="; ">"; ">="] in
    let c = concl th in
    not(numeric c || (is_neg c && numeric(dest_neg c)))) THEN
  DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN
  REPEAT ((DISJ1_TAC THEN CONTAINED_TAC) ORELSE DISJ2_TAC) THEN
  TRY CONTAINED_TAC;;

let ordinary_pack_raw_event_finish : tactic =
  FIRST_ASSUM ACCEPT_TAC ORELSE
  (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
   [ordinary_pack_concrete_event_finish;
    FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[]]);;

let ordinary_pack_final_finish : tactic = fun ((_,w) as goal) ->
  if is_exists w then
    (ASM_REWRITE_TAC[] THEN TRY DISCHARGE_SAFETY_PROPERTY_TAC THEN
     ordinary_pack_raw_event_finish) goal
  else if is_comb w && name_of(fst(strip_comb w)) = "memaccess_inbounds" then
    ordinary_pack_concrete_event_finish goal
  else
    (ordinary_pack_data_finish ORELSE
     (PRINT_GOAL_TAC THEN FAIL_TAC "ordinary pack final residual")) goal;;

(* Do not send event existentials, memory equations, or other large symbolic
   goals to arithmetic search with the entire simulation context. *)
let ordinary_pack_try_arith : tactic = fun ((_,w) as goal) ->
  let rec arithmetic tm =
    if is_neg tm then arithmetic(dest_neg tm)
    else exists (fun op -> is_binary op tm &&
                 type_of(snd(dest_binary op tm)) = `:num`)
           ["=";"<";"<=";">";">="] in
  (if arithmetic w then ASM_ARITH_TAC else ALL_TAC) goal;;

let ordinary_pack_return_finish : tactic =
  (SUBGOAL_THEN
   `(EventLoad(stackpointer:int64,8):uarch_event) =
    EventLoad(word_add (word_sub stackpointer (word 72)) (word 72),8)`
  ASSUME_TAC THENL [REWRITE_TAC[ORDINARY_PACK_STACK_RESTORE]; ALL_TAC]) THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  TRY (ASM_REWRITE_TAC[ORDINARY_PACK_STACK_RESTORE]) THEN
  ordinary_pack_final_finish;;

(* Instruction counts are branch-local. Preserve the current state's prefix so
   b0/d0 loop executions produce b1/d1 rather than unrelated s1 states. *)
let ordinary_pack_next_state_name ((_,w):goal) =
  let name = fst (dest_var (rand w)) in
  let rec suffix_start i =
    if i > 0 && String.get name (i - 1) >= '0' &&
       String.get name (i - 1) <= '9'
    then suffix_start (i - 1) else i in
  let split = suffix_start (String.length name) in
  try
    let index = int_of_string
      (String.sub name split (String.length name - split)) in
    String.sub name 0 split ^ string_of_int(index + 1)
  with _ -> "s1";;

let ordinary_pack_control_step exec goal =
  let fresh = ordinary_pack_next_state_name goal in
  (ordinary_pack_normalize_state THEN
   X86_VERBOSE_STEP_TAC exec fresh THEN ordinary_pack_normalize_state) goal;;

let ordinary_pack_steps exec indices =
  MAP_EVERY (fun _ goal -> ordinary_pack_control_step exec goal) indices;;

let ordinary_pack_rip_value tm =
  match tm with
    Comb(Comb(Const("=",_),
              Comb(Comb(Const("read",_),Const("RIP",_)),_)),value) -> Some value
  | _ -> None;;

let ordinary_pack_at_rip target ((asl,_):goal) =
  exists (fun (_,th) ->
    match ordinary_pack_rip_value(concl th) with
      Some value -> value = target
    | None -> false) asl;;

let ordinary_pack_debug_stage name conv tm =
  Printf.printf "X86_DEBUG_STAGE %s\n%!" name;
  try conv tm with e ->
    Printf.printf "X86_DEBUG_FAILURE %s on %s\n%!" name (string_of_term tm);
    raise e;;

let ordinary_pack_debug_conv decode_ths ths tm =
  let pc_th = find (fun th ->
    let c = concl th in is_eq c && is_read_rip (fst (dest_eq c))) ths in
  let bytes_loaded_mc_ths = filter (fun th ->
    let cc = concl th in
    is_comb cc && fst (strip_comb cc) = `bytes_loaded` &&
    last (snd (strip_comb cc)) = `ordinary_pack_mc`) ths in
  let eth = tryfind (fun loaded_mc_th ->
    GEN_REWRITE_CONV I [X86_THM decode_ths loaded_mc_th pc_th] tm)
    bytes_loaded_mc_ths in
  let x86_execute_case_rules =
    let ts = find_terms is_const (concl eth) in
    filter_map (fun t ->
      try Some (assoc (name_of t) X86_EXECUTE_CASES) with Failure _ -> None) ts in
  let stage name conv = ordinary_pack_debug_stage name conv in
  (K eth THENC
   stage "execute_cases" (PURE_ONCE_REWRITE_CONV x86_execute_case_rules) THENC
   stage "events" (REWRITE_CONV[add_store_event;add_load_event;SEQ_ID]) THENC
   stage "operand_size" (ONCE_DEPTH_CONV OPERAND_SIZE_CONV) THENC
   stage "conditions" (REWRITE_CONV[condition_semantics; aligned_OPERAND128;
                                    aligned_OPERAND256]) THENC
   stage "operand_cases" (REWRITE_CONV[OPERAND_SIZE_CASES]) THENC
   stage "operands" (REWRITE_CONV[OPERAND_CLAUSES]) THENC
   stage "bsid" (ONCE_DEPTH_CONV BSID_SEMANTICS_CONV) THENC
   stage "operations" (REWRITE_CONV X86_OPERATION_CLAUSES) THENC
   stage "rvalues" (REWRITE_CONV[READ_RVALUE;
     ASSIGN_ZEROTOP_32; READ_ZEROTOP_32; WRITE_ZEROTOP_32;
     ASSIGN_ZEROTOP_128; READ_ZEROTOP_128; WRITE_ZEROTOP_128;
     READ_BOTTOM_128]) THENC
   stage "word_num_1" (DEPTH_CONV WORD_NUM_RED_CONV) THENC
   stage "seq" (REWRITE_CONV[SEQ; condition_semantics]) THENC
   stage "bytesize" (REWRITE_CONV[bytesize]) THENC
   stage "undefined" (GEN_REWRITE_CONV TOP_DEPTH_CONV
     [UNDEFINED_VALUE; UNDEFINED_VALUES; SEQ_ID]) THENC
   stage "assigns_pull" (GEN_REWRITE_CONV TOP_DEPTH_CONV
     [ASSIGNS_PULL_ZEROTOP_THM; ASSIGNS_PULL_THM]) THENC
   stage "assigns" (REWRITE_CONV[ASSIGNS_THM]) THENC
   stage "seq_pull" (GEN_REWRITE_CONV TOP_DEPTH_CONV [SEQ_PULL_THM; BETA_THM]) THENC
   stage "unwind" (GEN_REWRITE_CONV TOP_DEPTH_CONV
     [assign; seq; UNWIND_THM1; BETA_THM]) THENC
   stage "write_bottom" (TRY_CONV(REWRITE_CONV[WRITE_BOTTOM_128])) THENC
   stage "ymm" (TRY_CONV(REWRITE_CONV READ_YMM_SSE_EQUIV)) THENC
   stage "empty" (REWRITE_CONV[]) THENC
   stage "short" (REWRITE_CONV[WRITE_SHORT; READ_SHORT]) THENC
   stage "read_over_write" (TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THENC
   stage "force_conditional" (X86_FORCE_CONDITIONAL_CONV ths) THENC
   stage "word_add" (ONCE_DEPTH_CONV
     (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
      GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
      RAND_CONV NUM_REDUCE_CONV)) THENC
   stage "write_over_write" (TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THENC
   stage "assumptions" (GEN_REWRITE_CONV
     (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths) THENC
   stage "word_val" (GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL]) THENC
   stage "pc_plus" (ONCE_DEPTH_CONV WORD_PC_PLUS_CONV) THENC
   stage "word_num_2" (DEPTH_CONV WORD_NUM_RED_CONV) THENC
   stage "relative" (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) tm;;

let ordinary_pack_debug_basic_step =
  GEN_BASIC_STEP_TAC "X86" `x86` `:x86state` ordinary_pack_debug_conv
    (REPEAT X86_UNDEFINED_CHOOSE_TAC);;

let ordinary_pack_debug_basic_step_traced decode_ths sname store =
  ordinary_pack_debug_basic_step decode_ths sname store THEN
  (fun goal -> Printf.printf "X86_DEBUG_BASIC_STEP_DONE\n%!"; ALL_TAC goal);;

let ordinary_pack_debug_marker name : tactic = fun goal ->
  Printf.printf "X86_DEBUG_UPDATE %s\n%!" name; ALL_TAC goal;;

let ordinary_pack_debug_step (mc_length_th,decode_ths) sname =
  ordinary_pack_debug_basic_step_traced decode_ths sname None THEN
  ordinary_pack_debug_marker "loaded_code_begin" THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update mc_length_th) THEN
  ordinary_pack_debug_marker "assumptions_begin" THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  ordinary_pack_debug_marker "maychange_begin" THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  ordinary_pack_debug_marker "new_rule_begin" THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    Printf.printf "X86_DEBUG_UPDATE new_rule_done %d\n%!" (length thl);
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ordinary_pack_debug_marker "simplify_begin" THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    ordinary_pack_debug_marker "strip_begin" THEN
    STRIP_TAC) THEN
  DISCARD_OLDSTATE_TAC sname THEN CLARIFY_TAC THEN
  ordinary_pack_debug_marker "step_done";;

let ordinary_pack_at_terminal_return target ((asl,_):goal) =
  target = `returnaddress:int64` &&
  not (exists (fun (_,th) ->
    match ordinary_pack_rip_value(concl th) with
      Some _ -> true
    | None -> false) asl);;

let rec ordinary_pack_steps_to_gen normalize exec target fuel goal =
  if ordinary_pack_at_rip target goal ||
     ordinary_pack_at_terminal_return target goal then ALL_TAC goal
  else if fuel = 0 then
    let (asl,_) = goal in
    let values = List.filter_map
      (fun (_,th) -> ordinary_pack_rip_value(concl th)) asl in
    failwith ("ordinary_pack_steps_to_gen: target " ^ string_of_term target ^
              ", current " ^ String.concat "," (map string_of_term values))
  else
    let (asl,_) = goal in
    let fresh = ordinary_pack_next_state_name goal in
    let values = List.filter_map
      (fun (_,th) -> ordinary_pack_rip_value(concl th)) asl in
    (try
       Printf.printf "ordinary_pack_steps_to_gen: predecessor %s\n%!"
         (String.concat "," (map string_of_term values));
       (normalize THEN
        X86_VERBOSE_STEP_TAC exec fresh THEN normalize THEN
        (fun goal ->
          Printf.printf "ordinary_pack_steps_to_gen: post-step\n%!";
          if ordinary_pack_at_rip target goal ||
             ordinary_pack_at_terminal_return target goal
          then ALL_TAC goal
          else ordinary_pack_steps_to_gen normalize exec target (fuel - 1) goal)) goal
     with e ->
       Printf.printf "ordinary_pack_steps_to_gen: failing predecessor %s\n%s%!"
         (String.concat "," (map string_of_term values))
         (Printexc.get_backtrace());
       let _ = PRINT_GOAL_TAC goal in
       raise e);;

let ordinary_pack_steps_to target fuel =
  ASSUME_TAC(ARITH_RULE `!a b. ~(a < b) /\ ~(a = b) <=> b < a`) THEN
  ordinary_pack_steps_to_gen ordinary_pack_normalize_state ORDINARY_PACK_EXEC
    target fuel;;

let ordinary_pack_steps_to_return fuel =
  ordinary_pack_steps_to `returnaddress:int64` fuel;;

let ordinary_pack_sim_return exec steps =
  GHOST_INTRO_TAC `rax_before_return:int64` `read RAX` THEN
  GHOST_INTRO_TAC `r8_before_return:int64` `read R8` THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ordinary_pack_steps exec (1--steps) THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ORDINARY_PACK_STACK_RESTORE] THEN
  SUBGOAL_THEN
   `(EventLoad(stackpointer:int64,8):uarch_event) =
    EventLoad(word_add (word_sub stackpointer (word 72)) (word 72),8)`
  ASSUME_TAC THENL [REWRITE_TAC[ORDINARY_PACK_STACK_RESTORE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (DISCHARGE_SAFETY_PROPERTY_TAC ORELSE ASM_MESON_TAC[]);;

let ordinary_pack_count_exfalso : tactic = fun ((asl,w) as goal) ->
  let fact tm = try Some(snd(List.find (fun (_,th) -> concl th = tm) asl))
                with Not_found -> None in
  let close_false f = ACCEPT_TAC (MATCH_MP (TAUT (mk_imp(`F`,w))) f) goal in
  let close_positive positive_th nonpositive_th =
    let p = concl positive_th in
    close_false (MP (MP (TAUT (mk_imp(concl nonpositive_th,
      mk_imp(p,`F`)))) nonpositive_th) positive_th) in
  let close_derived bad nonpositive =
    let p = dest_neg(concl nonpositive) in
    close_positive (MP (ARITH_RULE (mk_imp(concl bad,p))) bad) nonpositive in
  let close th zero bound = close_false (REWRITE_RULE [zero; bound] th) in
  let close_on_zero bad length_tm bound =
    match fact (mk_eq(length_tm,`0:num`)),
          fact (mk_neg(mk_binary "<" (`0:num`,length_tm))) with
    | Some z,_ -> close bad z bound
    | _,Some np -> close_derived bad np
    | _ -> ALL_TAC goal in
  match fact `32 < LENGTH(constants_xs:int32 list)` with
  | Some bad -> close_on_zero bad `LENGTH(constants_xs:int32 list)`
      (ARITH_RULE `32 < 0 <=> F`)
  | None ->
    match fact `24 < LENGTH(offsets:int32 list)` with
    | Some bad -> close_on_zero bad `LENGTH(offsets:int32 list)`
        (ARITH_RULE `24 < 0 <=> F`)
    | None ->
      match fact `24 < LENGTH(offsets:int32 list) \/
                   32 < LENGTH(constants_xs:int32 list)`,
            fact `~(0 < LENGTH(offsets:int32 list))`,
            fact `~(0 < LENGTH(constants_xs:int32 list))` with
      | Some bad,Some z1,Some z2 ->
          let p = mk_disj(`0 < LENGTH(offsets:int32 list)`,
                          `0 < LENGTH(constants_xs:int32 list)`) in
          let pos = MP (ARITH_RULE (mk_imp(concl bad,p))) bad in
          close_false (MP (MP (MP (TAUT (mk_imp(p,
            mk_imp(concl z1,mk_imp(concl z2,`F`))))) pos) z1) z2)
      | _ -> ALL_TAC goal;;

let ordinary_pack_shape_exfalso : tactic = fun ((asl,w) as goal) ->
  let fact tm = try Some(snd(List.find (fun (_,th) -> concl th = tm) asl))
                with Not_found -> None in
  let close_false f = ACCEPT_TAC (MATCH_MP (TAUT (mk_imp(`F`,w))) f) goal in
  let close_positive positive_th nonpositive_th =
    let p = concl positive_th in
    close_false (MP (MP (TAUT (mk_imp(concl nonpositive_th,
      mk_imp(p,`F`)))) nonpositive_th) positive_th) in
  let nz = fact `~(LENGTH(offsets:int32 list) = 0)` in
  let nzpos = fact `0 < LENGTH(offsets:int32 list)` in
  let capf = fact
    `4 * LENGTH(offsets:int32 list) + LENGTH(constants_xs:int32 list) <=
       LENGTH(fields_xs:int32 list)` in
  let capr = fact
    `LENGTH(offsets:int32 list) + 1 <= LENGTH(rows_xs:int32 list)` in
  let zf = fact `LENGTH(fields_xs:int32 list) = 0` in
  let zr = fact `LENGTH(rows_xs:int32 list) = 0` in
  let zpf = fact `~(0 < LENGTH(fields_xs:int32 list))` in
  let zpr = fact `~(0 < LENGTH(rows_xs:int32 list))` in
  match capr,zr,zpr with
  | Some cap,Some zero,_ ->
      close_false (REWRITE_RULE [zero; ARITH_RULE `n + 1 <= 0 <=> F`] cap)
  | Some cap,_,Some nonpositive ->
      close_positive (MP (ARITH_RULE (mk_imp(concl cap,
        `0 < LENGTH(rows_xs:int32 list)`))) cap) nonpositive
  | _ ->
    match capf,zf,zpf,nz,nzpos with
    | Some cap,Some zero,_,Some nonzero,_ ->
        close_false (REWRITE_RULE [zero; nonzero;
          ARITH_RULE `4 * n + nc <= 0 <=> n = 0 /\ nc = 0`] cap)
    | Some cap,_,Some nonpositive,_,Some positive ->
        close_positive
          (MP (MP (ARITH_RULE (mk_imp(concl positive,
             mk_imp(concl cap,`0 < LENGTH(fields_xs:int32 list)`))))
             positive) cap) nonpositive
    | _ -> ALL_TAC goal;;

let ordinary_pack_meson ((asl,w) as goal) =
  let (_,span) = List.find (fun (_,th) ->
    try snd (dest_disj (concl th)) = w with Failure _ -> false) asl in
  let zero = fst (dest_disj (concl span)) in
  let (_,nonempty) = List.find (fun (_,th) -> concl th = mk_neg zero) asl in
  MESON_TAC[span; nonempty] goal;;

let ordinary_pack_validate_spans : tactic =
  TRY (MP_TAC(ISPECL [`LENGTH(offsets:int32 list)`;
                        `LENGTH(constants_xs:int32 list)`]
    ORDINARY_PACK_COUNT_VAL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN
  MAP_EVERY VAL_INT64_TAC
    [`LENGTH(source_xs:int32 list)`; `LENGTH(offsets:int32 list)`;
     `LENGTH(constants_xs:int32 list)`; `LENGTH(fields_xs:int32 list)`;
     `LENGTH(rows_xs:int32 list)`] THEN
  SUBGOAL_THEN
   `word_ushr (word(LENGTH(source_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(offsets:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(constants_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(fields_xs:int32 list)):int64) 61 = word 0 /\
    word_ushr (word(LENGTH(rows_xs:int32 list)):int64) 61 = word 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CESTA_LENGTH_SHIFT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_and (word_zx (source:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (premises:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (constants:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (fields:int64):byte) (word 3) = word 0 /\
    word_and (word_zx (rows:int64):byte) (word 3) = word 0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CESTA_ALIGNED_BYTE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(LENGTH(source_xs:int32 list) = 0 \/ ~(val(source:int64) = 0)) /\
    (LENGTH(offsets:int32 list) = 0 \/ ~(val(premises:int64) = 0)) /\
    (LENGTH(constants_xs:int32 list) = 0 \/ ~(val(constants:int64) = 0)) /\
    (LENGTH(fields_xs:int32 list) = 0 \/ ~(val(fields:int64) = 0)) /\
    (LENGTH(rows_xs:int32 list) = 0 \/ ~(val(rows:int64) = 0))`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [ASM_MESON_TAC[VAL_EQ_0]; ALL_TAC] THEN
  GHOST_INTRO_TAC `rax_before_return:int64` `read RAX` THEN
  GHOST_INTRO_TAC `r8_before_return:int64` `read R8` THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ordinary_pack_steps ORDINARY_PACK_EXEC (1--9) THEN
  SUBGOAL_THEN
   `word_add (read RSP s9) (word 80) = word_add stackpointer (word 8) /\
    word_add (read RSP s9) (word 88) = word_add stackpointer (word 16) /\
    word_add (read RSP s9) (word 96) = word_add stackpointer (word 24) /\
    word_add (read RSP s9) (word 104) = word_add stackpointer (word 32)`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes64 (word_add (read RSP s9) (word 80))) s9 = fields /\
    read (memory :> bytes64 (word_add (read RSP s9) (word 88))) s9 =
      word(LENGTH(fields_xs:int32 list)) /\
    read (memory :> bytes64 (word_add (read RSP s9) (word 96))) s9 = rows /\
    read (memory :> bytes64 (word_add (read RSP s9) (word 104))) s9 =
      word(LENGTH(rows_xs:int32 list))`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ordinary_pack_steps ORDINARY_PACK_EXEC (10--13) THEN
  span_zero_cases `LENGTH(source_xs:int32 list)` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(source:int64) = 0)` ASSUME_TAC THENL
     [ordinary_pack_meson; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--7) THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (8--9)] THEN
  (span_zero_cases `LENGTH(offsets:int32 list)` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(premises:int64) = 0)` ASSUME_TAC THENL
     [ordinary_pack_meson; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--9)]) THEN
  (span_zero_cases `LENGTH(constants_xs:int32 list)` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(constants:int64) = 0)` ASSUME_TAC THENL
     [ordinary_pack_meson; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--9)]) THEN
  (span_zero_cases `LENGTH(fields_xs:int32 list)` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(fields:int64) = 0)` ASSUME_TAC THENL
     [ordinary_pack_meson; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--2) THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (3--9)]) THEN
  (span_zero_cases `LENGTH(rows_xs:int32 list)` THENL
   [ordinary_pack_steps ORDINARY_PACK_EXEC (1--2);
    SUBGOAL_THEN `~(val(rows:int64) = 0)` ASSUME_TAC THENL
     [ordinary_pack_meson; ALL_TAC] THEN
    ordinary_pack_steps ORDINARY_PACK_EXEC (1--9)]);;

