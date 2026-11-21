(* Full-workspace composition of the exact flat_fire leaf theorem. *)

let FLAT_FIRE_FULL_WORKSPACE_CORRECT = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      pc stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15.
    flat_valid fs rs gs ms /\
    LENGTH ms <= LENGTH ds /\ LENGTH ms <= LENGTH zs /\
    val dest + 4 * LENGTH ds <= 2 EXP 64 /\
    val scratch + 4 * LENGTH zs <= 2 EXP 64 /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc); (word_sub stackpointer (word 48),56)]
      [(fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
       (dest,4 * LENGTH ms); (scratch,4 * LENGTH ms)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub stackpointer (word 48),56) /\
    ALL (nonoverlapping (scratch,4 * LENGTH ms))
      [(fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms); (dest,4 * LENGTH ms)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc) (dest,4 * LENGTH ds) /\
    nonoverlapping (word pc,LENGTH flat_fire_mc) (scratch,4 * LENGTH zs) /\
    nonoverlapping (dest,4 * LENGTH ds) (scratch,4 * LENGTH zs) /\
    nonoverlapping (dest,4 * LENGTH ds)
      (word_sub stackpointer (word 48),48) /\
    nonoverlapping (scratch,4 * LENGTH zs)
      (word_sub stackpointer (word 48),48)
    ==> ensures x86
      (\s. bytes_loaded s (word pc) flat_fire_mc /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           read (memory :> bytes64 (word_add stackpointer (word 8))) s = dest /\
           read (memory :> bytes64 (word_add stackpointer (word 16))) s = scratch /\
           read RBP s = init_rbp /\ read RBX s = init_rbx /\
           read R12 s = init_r12 /\ read R13 s = init_r13 /\
           read R14 s = init_r14 /\ read R15 s = init_r15 /\
           C_ARGUMENTS [fields; rows; guards; word (LENGTH gs); make;
                        word (LENGTH ms)] s /\
           wordlist_from_memory(fields,LENGTH fs) s = fs /\
           wordlist_from_memory(rows,LENGTH rs) s = rs /\
           wordlist_from_memory(guards,LENGTH gs) s = gs /\
           wordlist_from_memory(make,LENGTH ms) s = ms /\
           wordlist_from_memory(dest,LENGTH ds) s = ds /\
           wordlist_from_memory(scratch,LENGTH zs) s = zs)
      (\s. flat_return dest scratch
             (APPEND
               (if flat_guards_hold fs rs gs then flat_selected fs rs ms
                else flat_prefix (LENGTH ms) ds)
               (ordinary_drop (LENGTH ms) ds))
             (APPEND
               (if flat_guards_hold fs rs gs then flat_selected fs rs ms
                else flat_prefix (LENGTH ms) zs)
               (ordinary_drop (LENGTH ms) zs))
             (bitval (flat_guards_hold fs rs gs)) stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
                  memory :> bytes(scratch,4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[C_RETURN; C_ARGUMENTS; SOME_FLAGS; flat_return;
              fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH(flat_prefix (LENGTH(ms:int32 list)) (ds:int32 list)) = LENGTH ms /\
    LENGTH(flat_prefix (LENGTH(ms:int32 list)) (zs:int32 list)) = LENGTH ms`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LENGTH_FLAT_PREFIX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `wordlist_from_memory(dest,LENGTH(ms:int32 list)) s0 =
      flat_prefix (LENGTH ms) ds /\
    wordlist_from_memory(scratch,LENGTH(ms:int32 list)) s0 =
      flat_prefix (LENGTH ms) zs`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WORDLIST_PREFIX_32 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X86_SUBROUTINE_SIM_TAC
    (flat_fire_mc,FLAT_FIRE_EXEC,0,flat_fire_mc,FLAT_FIRE_CORRECT)
    [`fields:int64`; `rows:int64`; `guards:int64`; `make:int64`; `dest:int64`;
     `scratch:int64`; `fs:int32 list`; `rs:int32 list`; `gs:int32 list`;
     `ms:int32 list`; `flat_prefix (LENGTH(ms:int32 list)) ds:int32 list`;
     `flat_prefix (LENGTH(ms:int32 list)) zs:int32 list`;
     `pc:num`; `stackpointer:int64`; `returnaddress:int64`; `init_rbp:int64`;
     `init_rbx:int64`; `init_r12:int64`; `init_r13:int64`; `init_r14:int64`;
     `init_r15:int64`] 1 THEN
  ASM_REWRITE_TAC[C_ARGUMENTS] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_return; C_RETURN]) THEN
  REPEAT (FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add dest (word(4 * LENGTH(ms:int32 list))),
                          4 * (LENGTH(ds:int32 list) - LENGTH ms))) s1 =
    read (memory :> bytes(word_add dest (word(4 * LENGTH ms)),
                          4 * (LENGTH ds - LENGTH ms))) s0 /\
    read (memory :> bytes(word_add scratch (word(4 * LENGTH(ms:int32 list))),
                          4 * (LENGTH(zs:int32 list) - LENGTH ms))) s1 =
    read (memory :> bytes(word_add scratch (word(4 * LENGTH ms)),
                          4 * (LENGTH zs - LENGTH ms))) s0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (maychange_term o concl)) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FLAT_READ_OVER_WRITE_ORTHOGONAL_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[FLAT_FULL_OUTPUT_LENGTH; FLAT_OUTPUT_PREFIX_LENGTH] THEN
  REPEAT CONJ_TAC THEN TRY (ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC WORDLIST_FULL_SPLICE_32 THEN
  REPEAT CONJ_TAC THEN TRY (ASM_REWRITE_TAC[]) THEN
  TRY (MATCH_MP_TAC FLAT_WORDLIST_OUTPUT_PREFIX THEN ASM_REWRITE_TAC[]) THEN
  TRY (EXISTS_TAC `s0:x86state`) THEN REPEAT CONJ_TAC THEN
  TRY (MATCH_MP_TAC FLAT_WORDLIST_OUTPUT_PREFIX THEN ASM_REWRITE_TAC[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORDLIST_FROM_MEMORY_32]) THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_32] THEN ASM_REWRITE_TAC[]);;
