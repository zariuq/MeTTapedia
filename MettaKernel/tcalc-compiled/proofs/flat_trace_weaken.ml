(* Recover the functional leaf contract from its traced strengthening. *)

let FLAT_FIRE_CORRECT = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list) (gs:int32 list)
           (ms:int32 list) (ds:int32 list) (zs:int32 list) pc stackpointer
    returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15.
    flat_valid fs rs gs ms /\
    LENGTH ds = LENGTH ms /\ LENGTH zs = LENGTH ms /\
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
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms); (dest,4 * LENGTH ms)]
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
           wordlist_from_memory(dest,LENGTH ms) s = ds /\
           wordlist_from_memory(scratch,LENGTH ms) s = zs)
      (\s. flat_return dest scratch
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else ds)
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else zs)
             (bitval (flat_guards_hold fs rs gs))
             stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
             init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
                  memory :> bytes(scratch,4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ensures] THEN BETA_TAC THEN X_GEN_TAC `s:x86state` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `flat_trace (read events s) fields rows guards make dest scratch
      (fs:int32 list) (rs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) stackpointer s`
  ASSUME_TAC THENL [MATCH_ACCEPT_TAC FLAT_TRACE_AT_ENTRY; ALL_TAC] THEN
  MP_TAC (REWRITE_RULE[ensures] (ISPECL
    [`fields:int64`; `rows:int64`; `guards:int64`; `make:int64`; `dest:int64`;
     `scratch:int64`; `fs:int32 list`; `rs:int32 list`; `gs:int32 list`;
     `ms:int32 list`; `ds:int32 list`; `zs:int32 list`;
     `pc:num`; `stackpointer:int64`; `returnaddress:int64`; `init_rbp:int64`;
     `init_rbx:int64`; `init_r12:int64`; `init_r13:int64`; `init_r14:int64`;
     `init_r15:int64`; `read events s:uarch_event list`]
    FLAT_FIRE_TRACED_CORRECT)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `s:x86state`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  GEN_TAC THEN MESON_TAC[]);;
