(* Memory-access trace safety of the exact flat_fire leaf, including its
   incoming stack arguments and full destination/scratch workspaces. *)

let FLAT_FIRE_FULL_WORKSPACE_SAFE = prove
 (`?f_events. !e fields rows guards make dest scratch (fs:int32 list)
      (rs:int32 list) (gs:int32 list) (ms:int32 list) (ds:int32 list)
      (zs:int32 list) pc stackpointer returnaddress init_rbp init_rbx init_r12
      init_r13 init_r14 init_r15.
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
           wordlist_from_memory(scratch,LENGTH zs) s = zs /\
           read events s = e)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           ?e2. read events s = APPEND e2 e /\
                e2 = f_events fields rows guards make dest scratch fs rs gs ms ds zs
                        pc stackpointer returnaddress /\
                memaccess_inbounds e2
                  [(fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
                   (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
                   (dest,4 * LENGTH ds); (scratch,4 * LENGTH zs);
                   (word_sub stackpointer (word 48),72)]
                  [(dest,4 * LENGTH ms); (scratch,4 * LENGTH ms);
                   (word_sub stackpointer (word 48),48)])
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
                  memory :> bytes(scratch,4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  PROVE_SAFETY_SPEC_TAC FLAT_FIRE_EXEC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
