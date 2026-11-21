(* State contracts at the Cesta adapter's ordinary_flat_pack call. *)

let ordinary_adapter_pre_pack_trace = new_definition
 `ordinary_adapter_pre_pack_trace e stackpointer s <=>
    ?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2
           [(word_sub stackpointer (word 120),224)]
           [(word_sub stackpointer (word 152),152)]`;;

let ordinary_adapter_pre_pack_frame = new_definition
 `ordinary_adapter_pre_pack_frame stackpointer : x86state->x86state->bool =
    MAYCHANGE [RSP; RBX; RBP; R12; R13; R14; R15] ,,
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 152),152)]`;;

let ordinary_adapter_before_pack = new_definition
 `ordinary_adapter_before_pack pc (source:int64) (premises:int64) (constants:int64)
      (guards:int64) (makes:int64) (fields:int64) (rows:int64)
      (dest:int64) (scratch:int64) (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_cesta_mc /\
    read RIP s = word(pc + 0x54d) /\
    read RSP s = word_sub stackpointer (word 152) /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    read (memory :> bytes64 (word_sub stackpointer (word 48))) s = init_rbx /\
    read (memory :> bytes64 (word_sub stackpointer (word 40))) s = init_rbp /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s = init_r12 /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s = init_r13 /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s = init_r14 /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) s = init_r15 /\
    C_ARGUMENTS [source; word(LENGTH source_xs);
                 premises; word(LENGTH offsets);
                 constants; word(LENGTH constants_xs)] s /\
    read (memory :> bytes64 (word_sub stackpointer (word 152))) s = fields /\
    read (memory :> bytes64 (word_sub stackpointer (word 144))) s =
      word(LENGTH fields_xs) /\
    read (memory :> bytes64 (word_sub stackpointer (word 136))) s = rows /\
    read (memory :> bytes64 (word_sub stackpointer (word 128))) s =
      word(LENGTH rows_xs) /\
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
    ordinary_adapter_pre_pack_trace e stackpointer s /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(guards,LENGTH guards_xs) s = guards_xs /\
    wordlist_from_memory(makes,LENGTH makes_xs) s = makes_xs /\
    wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
    wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs /\
    wordlist_from_memory(dest,LENGTH dest_xs) s = dest_xs /\
    wordlist_from_memory(scratch,LENGTH scratch_xs) s = scratch_xs`;;
