(* Accumulated memory-access trace for the flat-rule leaf. *)

let flat_trace = new_definition
 `flat_trace e fields rows guards make dest scratch (fs:int32 list)
      (rs:int32 list) (gs:int32 list) (ms:int32 list) (ds:int32 list)
      (zs:int32 list) stackpointer s <=>
    ?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2
           [(fields,4 * LENGTH fs); (rows,4 * LENGTH rs);
            (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
            (dest,4 * LENGTH ds); (scratch,4 * LENGTH zs);
            (word_sub stackpointer (word 48),72)]
           [(dest,4 * LENGTH ms); (scratch,4 * LENGTH ms);
            (word_sub stackpointer (word 48),48)]`;;

let FLAT_TRACE_AT_ENTRY = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      stackpointer s.
    flat_trace (read events s) fields rows guards make dest scratch
      fs rs gs ms ds zs stackpointer s`,
  REWRITE_TAC[flat_trace] THEN REPEAT GEN_TAC THEN
  EXISTS_TAC `[]:uarch_event list` THEN
  REWRITE_TAC[APPEND; APPEND_NIL; memaccess_inbounds; memaccess_inbounds_def; ALL]);;
