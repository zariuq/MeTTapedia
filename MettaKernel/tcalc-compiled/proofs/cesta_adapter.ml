(* Exact linked-byte proof for the Cesta-generated ordinary_flat_adapter.
   The leaf and pack are separate linked subprograms; their proofs are composed
   at the actual call sites rather than identified with the adapter's entry. *)

let ordinary_cesta_mc = define_from_elf "ordinary_cesta_mc" ordinary_cesta_object;;
Printf.printf "CESTA_ADAPTER defined bytes\n%!";;

let ORDINARY_CESTA_EXEC = X86_MK_EXEC_RULE ordinary_cesta_mc;;
Printf.printf "CESTA_ADAPTER exec rule\n%!";;

Printf.printf "CESTA_ADAPTER defining span\n%!";;
let ordinary_adapter_span_valid = new_definition
 `ordinary_adapter_span_valid (a:int64) (xs:int32 list) <=>
    LENGTH xs < 2 EXP 61 /\
    (LENGTH xs = 0 \/ ~(a = word 0)) /\
    word_and a (word 3) = word 0 /\
    val a + 4 * LENGTH xs <= 2 EXP 64`;;
Printf.printf "CESTA_ADAPTER span defined\n%!";;

let ordinary_adapter_offsets_valid = new_definition
 `ordinary_adapter_offsets_valid (source:int32 list) (offsets:int32 list) <=>
    ALL (\offset. val offset + 4 <= LENGTH source) offsets`;;
Printf.printf "CESTA_ADAPTER offsets defined\n%!";;

let ordinary_adapter_shape_valid = new_definition
 `ordinary_adapter_shape_valid (offsets:int32 list) (constants:int32 list)
      (guards:int32 list) (makes:int32 list) (fields:int32 list)
      (rows:int32 list) (dest:int32 list) (scratch:int32 list) <=>
    LENGTH offsets <= 24 /\ LENGTH constants <= 32 /\
    LENGTH guards <= 32 /\ LENGTH makes <= 32 /\
    4 * LENGTH offsets + LENGTH constants <= LENGTH fields /\
    LENGTH offsets + 1 <= LENGTH rows /\
    LENGTH makes <= LENGTH dest /\ LENGTH makes <= LENGTH scratch`;;
Printf.printf "CESTA_ADAPTER shape defined\n%!";;

let ordinary_adapter_rejects = new_definition
 `ordinary_adapter_rejects (source:int32 list) (offsets:int32 list)
      (constants:int32 list) (guards:int32 list) (makes:int32 list)
      (fields:int32 list) (rows:int32 list) (dest:int32 list)
      (scratch:int32 list) <=>
    ~(ordinary_adapter_shape_valid offsets constants guards makes fields rows
        dest scratch) \/
    ~(ordinary_adapter_offsets_valid source offsets)`;;

let ordinary_adapter_result_fields = new_definition
 `ordinary_adapter_result_fields (source:int32 list) (offsets:int32 list)
      constants guards makes (fields:int32 list) rows dest scratch =
    if ordinary_adapter_rejects source offsets constants guards makes fields rows
        dest scratch
    then fields
    else ordinary_pack_result_fields source offsets constants fields`;;

let ordinary_adapter_result_rows = new_definition
 `ordinary_adapter_result_rows (source:int32 list) (offsets:int32 list)
      constants guards makes fields (rows:int32 list) dest scratch =
    if ordinary_adapter_rejects source offsets constants guards makes fields rows
        dest scratch
    then rows
    else ordinary_pack_result_rows source offsets rows`;;

let ordinary_adapter_result_dest = new_definition
 `ordinary_adapter_result_dest source offsets constants guards makes fields rows
      (dest:int32 list) scratch =
    if ordinary_adapter_rejects source offsets constants guards makes fields rows
        dest scratch
    then dest
    else APPEND
      (if flat_guards_hold
            (ordinary_pack_result_fields source offsets constants fields)
            (ordinary_pack_result_rows source offsets rows) guards
       then flat_selected
            (ordinary_pack_result_fields source offsets constants fields)
            (ordinary_pack_result_rows source offsets rows) makes
       else flat_prefix (LENGTH makes) dest)
      (ordinary_drop (LENGTH makes) dest)`;;

let ordinary_adapter_result_scratch = new_definition
 `ordinary_adapter_result_scratch source offsets constants guards makes fields rows
      dest (scratch:int32 list) =
    if ordinary_adapter_rejects source offsets constants guards makes fields rows
        dest scratch
    then scratch
    else APPEND
      (if flat_guards_hold
            (ordinary_pack_result_fields source offsets constants fields)
            (ordinary_pack_result_rows source offsets rows) guards
       then flat_selected
            (ordinary_pack_result_fields source offsets constants fields)
            (ordinary_pack_result_rows source offsets rows) makes
       else flat_prefix (LENGTH makes) scratch)
      (ordinary_drop (LENGTH makes) scratch)`;;

let ordinary_adapter_return_value = new_definition
 `ordinary_adapter_return_value source offsets constants guards makes fields rows
      dest scratch =
    if ordinary_adapter_rejects source offsets constants guards makes fields rows
        dest scratch
    then 2
    else bitval(flat_guards_hold
      (ordinary_pack_result_fields source offsets constants fields)
      (ordinary_pack_result_rows source offsets rows) guards)`;;

let ORDINARY_ADAPTER_SPAN_VALID = prove
 (`!a xs. ordinary_adapter_span_valid a xs <=> ordinary_pack_span_valid a xs`,
  REWRITE_TAC[ordinary_adapter_span_valid; ordinary_pack_span_valid]);;

let ORDINARY_ADAPTER_SHAPE_VALID = prove
 (`!offsets constants guards makes fields rows dest scratch.
    ordinary_adapter_shape_valid offsets constants guards makes fields rows
      dest scratch <=>
    LENGTH guards <= 32 /\ LENGTH makes <= 32 /\
    LENGTH makes <= LENGTH dest /\ LENGTH makes <= LENGTH scratch /\
    ordinary_pack_shape_valid offsets constants fields rows`,
  REWRITE_TAC[ordinary_adapter_shape_valid; ordinary_pack_shape_valid] THEN
  MESON_TAC[]);;

let ORDINARY_ADAPTER_REJECTS_EQ = prove
 (`!source offsets constants guards makes fields rows dest scratch.
    ordinary_adapter_rejects source offsets constants guards makes fields rows
      dest scratch <=>
    32 < LENGTH guards \/ 32 < LENGTH makes \/
    LENGTH dest < LENGTH makes \/ LENGTH scratch < LENGTH makes \/
    ordinary_pack_rejects source offsets constants fields rows`,
  REWRITE_TAC[ordinary_adapter_rejects; ordinary_adapter_offsets_valid;
              ordinary_pack_rejects; ordinary_pack_offsets_valid;
              ORDINARY_ADAPTER_SHAPE_VALID; NOT_LE] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN
  CONV_TAC TAUT);;

let ORDINARY_ADAPTER_REJECT_OUTPUTS = prove
 (`!source offsets constants guards makes fields rows dest scratch.
    ordinary_adapter_rejects source offsets constants guards makes fields rows
      dest scratch
    ==> ordinary_adapter_result_fields source offsets constants guards makes
          fields rows dest scratch = fields /\
        ordinary_adapter_result_rows source offsets constants guards makes
          fields rows dest scratch = rows /\
        ordinary_adapter_result_dest source offsets constants guards makes
          fields rows dest scratch = dest /\
        ordinary_adapter_result_scratch source offsets constants guards makes
          fields rows dest scratch = scratch /\
        ordinary_adapter_return_value source offsets constants guards makes
          fields rows dest scratch = 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ordinary_adapter_result_fields; ordinary_adapter_result_rows;
                  ordinary_adapter_result_dest; ordinary_adapter_result_scratch;
                  ordinary_adapter_return_value]);;

let ORDINARY_ADAPTER_ACCEPT_OUTPUTS = prove
 (`!source offsets constants guards makes fields rows dest scratch.
    ~(ordinary_adapter_rejects source offsets constants guards makes fields rows
        dest scratch)
    ==> ordinary_adapter_result_fields source offsets constants guards makes
          fields rows dest scratch =
        ordinary_pack_result_fields source offsets constants fields /\
        ordinary_adapter_result_rows source offsets constants guards makes
          fields rows dest scratch =
        ordinary_pack_result_rows source offsets rows /\
        ordinary_adapter_result_dest source offsets constants guards makes
          fields rows dest scratch =
        APPEND
          (if flat_guards_hold
            (ordinary_pack_result_fields source offsets constants fields)
            (ordinary_pack_result_rows source offsets rows) guards
           then flat_selected
            (ordinary_pack_result_fields source offsets constants fields)
            (ordinary_pack_result_rows source offsets rows) makes
           else flat_prefix (LENGTH makes) dest)
          (ordinary_drop (LENGTH makes) dest) /\
        ordinary_adapter_result_scratch source offsets constants guards makes
          fields rows dest scratch =
        APPEND
          (if flat_guards_hold
            (ordinary_pack_result_fields source offsets constants fields)
            (ordinary_pack_result_rows source offsets rows) guards
           then flat_selected
            (ordinary_pack_result_fields source offsets constants fields)
            (ordinary_pack_result_rows source offsets rows) makes
           else flat_prefix (LENGTH makes) scratch)
          (ordinary_drop (LENGTH makes) scratch) /\
        ordinary_adapter_return_value source offsets constants guards makes
          fields rows dest scratch =
        bitval(flat_guards_hold
          (ordinary_pack_result_fields source offsets constants fields)
          (ordinary_pack_result_rows source offsets rows) guards)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ordinary_adapter_result_fields; ordinary_adapter_result_rows;
                  ordinary_adapter_result_dest; ordinary_adapter_result_scratch;
                  ordinary_adapter_return_value]);;

let ordinary_adapter_entry = new_definition
 `ordinary_adapter_entry pc source premises constants guards makes fields rows
      dest scratch (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 e s <=>
    bytes_loaded s (word pc) ordinary_cesta_mc /\
    read RIP s = word (pc + 0x2e5) /\
    read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    C_ARGUMENTS [source; word(LENGTH source_xs);
                 premises; word(LENGTH offsets);
                 constants; word(LENGTH constants_xs)] s /\
    read (memory :> bytes64 (word_add stackpointer (word 8))) s = guards /\
    read (memory :> bytes64 (word_add stackpointer (word 16))) s =
      word(LENGTH guards_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 24))) s = makes /\
    read (memory :> bytes64 (word_add stackpointer (word 32))) s =
      word(LENGTH makes_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 40))) s = fields /\
    read (memory :> bytes64 (word_add stackpointer (word 48))) s =
      word(LENGTH fields_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 56))) s = rows /\
    read (memory :> bytes64 (word_add stackpointer (word 64))) s =
      word(LENGTH rows_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 72))) s = dest /\
    read (memory :> bytes64 (word_add stackpointer (word 80))) s =
      word(LENGTH dest_xs) /\
    read (memory :> bytes64 (word_add stackpointer (word 88))) s = scratch /\
    read (memory :> bytes64 (word_add stackpointer (word 96))) s =
      word(LENGTH scratch_xs) /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15 /\
    read events s = e /\
    wordlist_from_memory(source,LENGTH source_xs) s = source_xs /\
    wordlist_from_memory(premises,LENGTH offsets) s = offsets /\
    wordlist_from_memory(constants,LENGTH constants_xs) s = constants_xs /\
    wordlist_from_memory(guards,LENGTH guards_xs) s = guards_xs /\
    wordlist_from_memory(makes,LENGTH makes_xs) s = makes_xs /\
    wordlist_from_memory(fields,LENGTH fields_xs) s = fields_xs /\
    wordlist_from_memory(rows,LENGTH rows_xs) s = rows_xs /\
    wordlist_from_memory(dest,LENGTH dest_xs) s = dest_xs /\
    wordlist_from_memory(scratch,LENGTH scratch_xs) s = scratch_xs`;;
Printf.printf "CESTA_ADAPTER entry defined\n%!";;

let ordinary_adapter_return = new_definition
 `ordinary_adapter_return returnvalue stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    read RIP s = returnaddress /\
    read RSP s = word_add stackpointer (word 8) /\
    C_RETURN s = word returnvalue /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15`;;
Printf.printf "CESTA_ADAPTER return defined\n%!";;

let ordinary_adapter_reject_frame = new_definition
 `ordinary_adapter_reject_frame stackpointer : x86state->x86state->bool =
    MAYCHANGE [RSP; RBX; RBP; R12; R13; R14; R15] ,,
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 120),120)]`;;
Printf.printf "CESTA_ADAPTER reject frame defined\n%!";;

(* The four outgoing stack arguments and pack return address place pack entry
   160 bytes below adapter entry; the pack's own frame reaches 72 bytes lower.
   The successful tail jump also replaces the incoming dest/scratch argument
   slots at sp+8 and sp+16, but preserves the return address at sp. *)
let ordinary_adapter_frame = new_definition
 `ordinary_adapter_frame fields rows dest scratch
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer : x86state->x86state->bool =
    MAYCHANGE [RSP; RBX; RBP; R12; R13; R14; R15] ,,
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 232),232);
               memory :> bytes(word_add stackpointer (word 8),16);
               memory :> bytes(fields,4 * LENGTH fields_xs);
               memory :> bytes(rows,4 * LENGTH rows_xs);
               memory :> bytes(dest,4 * LENGTH dest_xs);
               memory :> bytes(scratch,4 * LENGTH scratch_xs)]`;;
Printf.printf "CESTA_ADAPTER full frame defined\n%!";;

let ORDINARY_ADAPTER_FRAME_IDEMPOTENT = prove
 (`!fields rows dest scratch (fields_xs:int32 list) (rows_xs:int32 list)
      (dest_xs:int32 list) (scratch_xs:int32 list) stackpointer.
    ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
      scratch_xs stackpointer ,,
    ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
      scratch_xs stackpointer =
    ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
      scratch_xs stackpointer`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinary_adapter_frame;
    ordinary_adapter_reject_frame; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    SOME_FLAGS] THEN MAYCHANGE_IDEMPOT_TAC);;

let ORDINARY_ADAPTER_TRANS = prove
 (`!fields rows dest scratch (fields_xs:int32 list) (rows_xs:int32 list)
      (dest_xs:int32 list) (scratch_xs:int32 list) stackpointer P Q R.
    ensures x86 P Q
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
         scratch_xs stackpointer) /\
    ensures x86 Q R
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
         scratch_xs stackpointer)
    ==> ensures x86 P R
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
         scratch_xs stackpointer)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `Q:x86state->bool` THEN
  REWRITE_TAC[ORDINARY_ADAPTER_FRAME_IDEMPOTENT] THEN ASM_REWRITE_TAC[]);;

let ORDINARY_ADAPTER_REJECT_FRAME_IDEMPOTENT = prove
 (`!stackpointer.
    ordinary_adapter_reject_frame stackpointer ,,
    ordinary_adapter_reject_frame stackpointer =
    ordinary_adapter_reject_frame stackpointer`,
  GEN_TAC THEN REWRITE_TAC[ordinary_adapter_reject_frame;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
  MAYCHANGE_IDEMPOT_TAC);;

let ORDINARY_ADAPTER_REJECT_TRANS = prove
 (`!stackpointer P Q R.
    ensures x86 P Q (ordinary_adapter_reject_frame stackpointer) /\
    ensures x86 Q R (ordinary_adapter_reject_frame stackpointer)
    ==> ensures x86 P R (ordinary_adapter_reject_frame stackpointer)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `Q:x86state->bool` THEN
  REWRITE_TAC[ORDINARY_ADAPTER_REJECT_FRAME_IDEMPOTENT] THEN ASM_REWRITE_TAC[]);;

let ORDINARY_ADAPTER_REJECT_STACK_IN_FULL = prove
 (`!sp:int64. word_sub sp (word 120) =
    word_add (word_sub sp (word 232)) (word 112)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_ADAPTER_REJECT_STACK_CONTAINED = prove
 (`!sp:int64. contained_modulo (2 EXP 64)
    (val(word_sub sp (word 120)),120)
    (val(word_sub sp (word 232)),232)`,
  GEN_TAC THEN REWRITE_TAC[ORDINARY_ADAPTER_REJECT_STACK_IN_FULL] THEN
  CONTAINED_TAC);;

let ORDINARY_ADAPTER_REJECT_BYTES_SUBSUMED = prove
 (`!stackpointer:int64.
    ASSIGNS (memory :> bytes(word_sub stackpointer (word 120),120)) subsumed
    ASSIGNS (memory :> bytes(word_sub stackpointer (word 232),232))`,
  GEN_TAC THEN MATCH_MP_TAC SUBSUMED_ASSIGNS_SUBCOMPONENTS THEN
  MATCH_MP_TAC(ISPECL [`word_sub stackpointer (word 120):int64`;
    `word_sub stackpointer (word 232):int64`; `120:num`; `232:num`]
    SUBSUMED_ASSIGNS_BYTES) THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  ACCEPT_TAC(SPEC `stackpointer:int64`
    ORDINARY_ADAPTER_REJECT_STACK_CONTAINED));;

let ORDINARY_ADAPTER_REJECT_MEMORY_SUBSUMED = prove
 (`!fields rows dest scratch (fields_xs:int32 list) (rows_xs:int32 list)
      (dest_xs:int32 list) (scratch_xs:int32 list) stackpointer.
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 120),120)] subsumed
    MAYCHANGE [memory :> bytes(word_sub stackpointer (word 232),232);
               memory :> bytes(word_add stackpointer (word 8),16);
               memory :> bytes(fields,4 * LENGTH fields_xs);
               memory :> bytes(rows,4 * LENGTH rows_xs);
               memory :> bytes(dest,4 * LENGTH dest_xs);
               memory :> bytes(scratch,4 * LENGTH scratch_xs)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAYCHANGE_SING] THEN
  ONCE_REWRITE_TAC[MAYCHANGE] THEN
  MATCH_MP_TAC SUBSUMED_SEQ_LEFT THEN CONJ_TAC THENL
   [ACCEPT_TAC(SPEC `stackpointer:int64`
      ORDINARY_ADAPTER_REJECT_BYTES_SUBSUMED);
    SUBSUMED_ID_MAYCHANGE_TAC]);;

let ORDINARY_ADAPTER_REJECT_FRAME_SUBSUMED = prove
 (`!fields rows dest scratch (fields_xs:int32 list) (rows_xs:int32 list)
      (dest_xs:int32 list) (scratch_xs:int32 list) stackpointer P Q.
    ensures x86 P Q (ordinary_adapter_reject_frame stackpointer)
    ==> ensures x86 P Q
      (ordinary_adapter_frame fields rows dest scratch fields_xs rows_xs dest_xs
         scratch_xs stackpointer)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC `ordinary_adapter_reject_frame stackpointer` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ordinary_adapter_frame; ordinary_adapter_reject_frame;
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN CONJ_TAC) THEN
    TRY(MATCH_ACCEPT_TAC SUBSUMED_REFL) THEN
    ACCEPT_TAC(SPECL [`fields:int64`; `rows:int64`; `dest:int64`;
      `scratch:int64`; `fields_xs:int32 list`; `rows_xs:int32 list`;
      `dest_xs:int32 list`; `scratch_xs:int32 list`; `stackpointer:int64`]
      ORDINARY_ADAPTER_REJECT_MEMORY_SUBSUMED);
    FIRST_ASSUM ACCEPT_TAC]);;

let ORDINARY_ADAPTER_WORD_SUB_SUB = prove
 (`!(x:N word) m n.
     word_sub (word_sub x (word m)) (word n) = word_sub x (word (m + n))`,
  CONV_TAC WORD_RULE);;

let ORDINARY_ADAPTER_BYTE_ZX32_ZX = prove
 (`!x:byte. (word_zx ((word_zx x:int32)):byte) = x`,
  CONV_TAC WORD_BLAST);;

let ORDINARY_ADAPTER_BYTE_ZX64_ZX = prove
 (`!x:byte. (word_zx ((word_zx x:int64)):byte) = x`,
  CONV_TAC WORD_BLAST);;

let ORDINARY_ADAPTER_STACK_RESTORE = prove
 (`!sp:int64.
     word_add (word_sub sp (word 120)) (word 120) = sp /\
     word_add (word_sub sp (word 120)) (word 128) = word_add sp (word 8) /\
     word_add (word_sub sp (word 120)) (word 136) = word_add sp (word 16) /\
     word_add (word_sub sp (word 120)) (word 144) = word_add sp (word 24) /\
     word_add (word_sub sp (word 120)) (word 152) = word_add sp (word 32) /\
     word_add (word_sub sp (word 120)) (word 160) = word_add sp (word 40) /\
     word_add (word_sub sp (word 120)) (word 168) = word_add sp (word 48) /\
     word_add (word_sub sp (word 120)) (word 176) = word_add sp (word 56) /\
     word_add (word_sub sp (word 120)) (word 184) = word_add sp (word 64) /\
     word_add (word_sub sp (word 120)) (word 192) = word_add sp (word 72) /\
     word_add (word_sub sp (word 120)) (word 200) = word_add sp (word 80) /\
     word_add (word_sub sp (word 120)) (word 208) = word_add sp (word 88) /\
     word_add (word_sub sp (word 120)) (word 216) = word_add sp (word 96)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_ADAPTER_AFTER_PACK_STACK_IN_FULL = prove
 (`!stackpointer:int64.
     word_add (word_sub stackpointer (word 152)) (word 104) =
       word_add (word_sub stackpointer (word 232)) (word 184) /\
     word_add (word_sub stackpointer (word 152)) (word 112) =
       word_add (word_sub stackpointer (word 232)) (word 192) /\
     word_add (word_sub stackpointer (word 152)) (word 120) =
       word_add (word_sub stackpointer (word 232)) (word 200) /\
     word_add (word_sub stackpointer (word 152)) (word 128) =
       word_add (word_sub stackpointer (word 232)) (word 208) /\
     word_add (word_sub stackpointer (word 152)) (word 136) =
       word_add (word_sub stackpointer (word 232)) (word 216) /\
     word_add (word_sub stackpointer (word 152)) (word 144) =
       word_add (word_sub stackpointer (word 232)) (word 224) /\
     word_add (word_sub stackpointer (word 152)) (word 152) =
       word_add (word_sub stackpointer (word 232)) (word 232)`,
  CONV_TAC WORD_RULE);;

let ordinary_adapter_reject_trace = new_definition
 `ordinary_adapter_reject_trace e stackpointer s <=>
    ?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2
           [(word_sub stackpointer (word 120),224)]
           [(word_sub stackpointer (word 120),120)]`;;

let ordinary_adapter_trace = new_definition
 `ordinary_adapter_trace e (source:int64) (premises:int64) (constants:int64)
      (guards:int64) (makes:int64) (fields:int64) (rows:int64)
      (dest:int64) (scratch:int64) (source_xs:int32 list) (offsets:int32 list)
      (constants_xs:int32 list) (guards_xs:int32 list) (makes_xs:int32 list)
      (fields_xs:int32 list) (rows_xs:int32 list) (dest_xs:int32 list)
      (scratch_xs:int32 list) stackpointer s <=>
    ?e2. read events s = APPEND e2 e /\
         memaccess_inbounds e2
           [(source,4 * LENGTH source_xs); (premises,4 * LENGTH offsets);
            (constants,4 * LENGTH constants_xs); (guards,4 * LENGTH guards_xs);
            (makes,4 * LENGTH makes_xs); (fields,4 * LENGTH fields_xs);
            (rows,4 * LENGTH rows_xs); (dest,4 * LENGTH dest_xs);
            (scratch,4 * LENGTH scratch_xs);
            (word_sub stackpointer (word 232),336)]
           [(word_sub stackpointer (word 232),232);
            (word_add stackpointer (word 8),16);
            (fields,4 * LENGTH fields_xs); (rows,4 * LENGTH rows_xs);
            (dest,4 * LENGTH dest_xs); (scratch,4 * LENGTH scratch_xs)]`;;

let ORDINARY_ADAPTER_AFTER_PACK_RETURN_ADDRESS = prove
 (`!stackpointer:int64.
     word_add (word_sub stackpointer (word 152)) (word 104) =
       word_sub stackpointer (word 48) /\
     word_add (word_sub stackpointer (word 152)) (word 112) =
       word_sub stackpointer (word 40) /\
     word_add (word_sub stackpointer (word 152)) (word 120) =
       word_sub stackpointer (word 32) /\
     word_add (word_sub stackpointer (word 152)) (word 128) =
       word_sub stackpointer (word 24) /\
     word_add (word_sub stackpointer (word 152)) (word 136) =
       word_sub stackpointer (word 16) /\
     word_add (word_sub stackpointer (word 152)) (word 144) =
       word_sub stackpointer (word 8) /\
     word_add (word_sub stackpointer (word 152)) (word 152) = stackpointer /\
     word_add (word_sub stackpointer (word 152)) (word 160) =
       word_add stackpointer (word 8) /\
     word_add (word_sub stackpointer (word 152)) (word 168) =
       word_add stackpointer (word 16)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_ADAPTER_AFTER_PACK_ARGUMENT_ADDRESSES = prove
 (`!stackpointer:int64.
     word_add (word_sub stackpointer (word 152)) (word 40) =
       word_sub stackpointer (word 112) /\
     word_add (word_sub stackpointer (word 152)) (word 48) =
       word_sub stackpointer (word 104) /\
     word_add (word_sub stackpointer (word 152)) (word 56) =
       word_sub stackpointer (word 96) /\
     word_add (word_sub stackpointer (word 152)) (word 64) =
       word_sub stackpointer (word 88) /\
     word_add (word_sub stackpointer (word 152)) (word 80) =
       word_sub stackpointer (word 72) /\
     word_add (word_sub stackpointer (word 152)) (word 88) =
       word_sub stackpointer (word 64)`,
  CONV_TAC WORD_RULE);;

let ORDINARY_ADAPTER_EVENT_STACK_ADDRESSES = prove
 (`!stackpointer:int64.
     word_sub stackpointer (word 8) =
       word_add (word_sub stackpointer (word 232)) (word 224) /\
     word_sub stackpointer (word 16) =
       word_add (word_sub stackpointer (word 232)) (word 216) /\
     word_sub stackpointer (word 24) =
       word_add (word_sub stackpointer (word 232)) (word 208) /\
     word_sub stackpointer (word 32) =
       word_add (word_sub stackpointer (word 232)) (word 200) /\
     word_sub stackpointer (word 40) =
       word_add (word_sub stackpointer (word 232)) (word 192) /\
     word_sub stackpointer (word 48) =
       word_add (word_sub stackpointer (word 232)) (word 184) /\
     word_add stackpointer (word 8) =
       word_add (word_sub stackpointer (word 232)) (word 240) /\
     word_add stackpointer (word 16) =
       word_add (word_sub stackpointer (word 232)) (word 248) /\
     word_add (word_sub stackpointer (word 152)) (word 40) =
       word_add (word_sub stackpointer (word 232)) (word 120) /\
     word_add (word_sub stackpointer (word 152)) (word 48) =
       word_add (word_sub stackpointer (word 232)) (word 128) /\
     word_add (word_sub stackpointer (word 152)) (word 56) =
       word_add (word_sub stackpointer (word 232)) (word 136) /\
     word_add (word_sub stackpointer (word 152)) (word 64) =
       word_add (word_sub stackpointer (word 232)) (word 144) /\
     word_add (word_sub stackpointer (word 152)) (word 80) =
       word_add (word_sub stackpointer (word 232)) (word 160) /\
     word_add (word_sub stackpointer (word 152)) (word 88) =
       word_add (word_sub stackpointer (word 232)) (word 168)`,
  CONV_TAC WORD_RULE);;

let ordinary_adapter_split_append_events : tactic = fun ((_,w) as goal) ->
  let op,args = strip_comb w in
  Printf.printf "ADAPTER_SPLIT op=%s arity=%d goal=%s\n%!"
    (name_of op) (length args) (string_of_term w);
  match args with
  | [ev;rr;wr] when name_of op = "memaccess_inbounds" ->
      let e1,e2 = dest_binary "APPEND" ev in
      (MATCH_MP_TAC (snd(EQ_IMP_RULE (ISPECL [e1;e2;rr;wr]
         MEMACCESS_INBOUNDS_APPEND))) THEN CONJ_TAC) goal
  | _ -> failwith "ordinary adapter append event split";;

let ordinary_adapter_concrete_event_finish : tactic =
  FIRST_ASSUM ACCEPT_TAC ORELSE
  (REWRITE_TAC[ORDINARY_ADAPTER_AFTER_PACK_STACK_IN_FULL;
               ORDINARY_ADAPTER_EVENT_STACK_ADDRESSES] THEN
   DISCARD_ASSUMPTIONS_TAC (fun th ->
     let numeric tm =
       exists (fun op -> is_binary op tm &&
         type_of(fst(dest_binary op tm)) = `:num`)
         ["="; "<"; "<="; ">"; ">="] in
     let c = concl th in
     not(numeric c || (is_neg c && numeric(dest_neg c)))) THEN
   DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN
   REPEAT ((DISJ1_TAC THEN CONTAINED_TAC) ORELSE DISJ2_TAC) THEN
   TRY CONTAINED_TAC);;

let rec ordinary_adapter_raw_event_finish : tactic = fun ((_,w) as goal) ->
  if is_exists w then
    (SAFE_META_EXISTS_TAC allowed_vars_e THEN CONJ_TAC THENL
     [EXISTS_E2_TAC allowed_vars_e; ordinary_adapter_raw_event_finish]) goal
  else
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     (ordinary_adapter_split_append_events THENL
       [ordinary_adapter_concrete_event_finish;
        FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[]])) goal;;

let ordinary_adapter_maychange_finish : tactic =
  let pth = prove
   (`(R:x86state->x86state->bool) s s' ==> R subsumed R' ==> R' s s'`,
    REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
  fun ((_,w) as goal) ->
    let initial = rand(rator w) and final = rand w in
    let compatible th =
      maychange_term(concl th) &&
      rand(rator(concl th)) = initial && rand(concl th) = final in
    (FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP pth o check compatible) THEN
     REWRITE_TAC[ETA_AX; ORDINARY_ADAPTER_AFTER_PACK_RETURN_ADDRESS] THEN
     PRINT_GOAL_TAC THEN SUBSUMED_MAYCHANGE_TAC) goal;;

let ordinary_adapter_final_finish : tactic = fun ((asl,w) as goal) ->
  if is_exists w then
    (ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[ORDINARY_ADAPTER_AFTER_PACK_STACK_IN_FULL] THEN
     TRY DISCHARGE_SAFETY_PROPERTY_TAC THEN
     ordinary_adapter_raw_event_finish) goal
  else if is_comb w && name_of(fst(strip_comb w)) = "memaccess_inbounds" then
    ordinary_adapter_raw_event_finish goal
  else if is_eq w then
    (RULE_ASSUM_TAC(REWRITE_RULE[ORDINARY_ADAPTER_AFTER_PACK_RETURN_ADDRESS;
                                 ORDINARY_ADAPTER_AFTER_PACK_ARGUMENT_ADDRESSES]) THEN
     REWRITE_TAC[ORDINARY_ADAPTER_AFTER_PACK_RETURN_ADDRESS;
                 ORDINARY_ADAPTER_AFTER_PACK_ARGUMENT_ADDRESSES] THEN
     (fun ((asl,w) as goal) ->
       let symmetric th =
         if concl th = w then th else
         let l,r = dest_eq w in
         if concl th = mk_eq(r,l) then SYM th else failwith "not symmetric" in
       try ACCEPT_TAC(tryfind (fun (_,th) -> symmetric th) asl) goal
       with Failure _ ->
         ((REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES; WORDLIST_FROM_MEMORY_32; EQ_SYM_EQ;
                      GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]) ORELSE
          (PRINT_GOAL_TAC THEN FAIL_TAC "ordinary adapter equality residual")) goal)) goal
  else if maychange_term w then ordinary_adapter_maychange_finish goal
  else
    ((REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES; WORDLIST_FROM_MEMORY_32; EQ_SYM_EQ;
                 GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]) ORELSE
     (PRINT_GOAL_TAC THEN FAIL_TAC "ordinary adapter final residual")) goal;;

let ordinary_adapter_normalize_state : tactic = fun ((asl,_) as goal) ->
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
  let word_facts = List.filter_map (fun th ->
    try Some(REWRITE_RULE[VAL_EQ_0] th) with Failure _ -> None)
    arith_facts in
  let facts = arith_facts @ word_facts @ List.filter_map (fun th ->
    try Some(REWRITE_RULE[ARITH_RULE `a <= b <=> ~(b < a)`] th)
    with Failure _ -> None) arith_facts in
  let rules = [ORDINARY_ADAPTER_WORD_SUB_SUB; ORDINARY_ADAPTER_STACK_RESTORE;
               CESTA_STACK_RESTORE; CESTA_BYTE_RESIDUE; CESTA_LOW_BYTE_JOIN;
               CESTA_READ_BYTES8_64; CESTA_READ_BYTES32_64; CESTA_SUB_ZERO;
               ORDINARY_ADAPTER_BYTE_ZX32_ZX; ORDINARY_ADAPTER_BYTE_ZX64_ZX;
               ORDINARY_WORD_ZX_EQ_0; WORD_ZX_0; WORD_ZX_ZX;
               DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
               WORD_AND_0; WORD_OR_0; WORD_OR_REFL; WORD_AND_REFL;
               WORD_SUB_0; VAL_WORD_0; VAL_WORD_1; VAL_EQ_0; ARITH_EQ;
               REFL_CLAUSE; COND_CLAUSES; NOT_CLAUSES; CONJUNCT1 LT; LENGTH;
               ARITH_RULE `n = 0 <=> ~(0 < n)`;
               ARITH_RULE `2305843009213693951 < n <=> ~(n < 2 EXP 61)`;
               ARITH_RULE `n <= 0 <=> n = 0`;
               ARITH_RULE `~(a < b) /\ ~(a = b) <=> b < a`;
               ARITH_RULE `~(a < b \/ a = b) <=> b < a`] in
  let try_rule rs th = try REWRITE_RULE rs th with Failure _ -> th in
  let try_conv conv th = try CONV_RULE conv th with Failure _ -> th in
  let memory_word_facts = List.filter_map (fun (_,th) ->
    try let l,_ = dest_eq(concl th) in
        if exists (fun t -> name_of t = "memory")
             (find_terms is_const l)
        then Some th else None
    with Failure _ -> None) asl in
  (RULE_ASSUM_TAC (fun th -> if stateful th then
    try_rule (rules @ facts) (try_conv WORD_REDUCE_CONV (try_rule rules th))
    else th) THEN
   RULE_ASSUM_TAC (fun th ->
     let c = concl th in
     if is_eq c && is_read_rip(fst(dest_eq c)) then
       let th' = simplify_conditionals_with_facts facts
         (SIMP_RULE ((COND_CLAUSES::NOT_CLAUSES::rules) @
                     facts @ memory_word_facts) th) in
       Printf.printf "ADAPTER_RIP_NORMALIZE %s => %s\n%!"
         (string_of_term(concl th)) (string_of_term(concl th'));
       th'
     else th)) goal;;

let ordinary_adapter_normalize_control sname ((asl,_) as goal) =
  let sv = mk_var(sname,`:x86state`) in
  let has_components names th =
    exists (fun t -> mem (name_of t) names)
      (find_terms (fun t -> is_const t && mem (name_of t) names) (concl th)) in
  let previous_reads = filter (fun (_,th) ->
    not (vfree_in sv (concl th)) && has_components ["read"] th) asl in
  let arithmetic = filter (fun (_,th) ->
    not (exists (fun v -> type_of v = `:x86state`) (frees(concl th)))) asl in
  RULE_ASSUM_TAC (fun th ->
    if vfree_in sv (concl th) && has_components ["read"] th then
      (try REWRITE_RULE
        (CESTA_READ_BYTES8_64 :: CESTA_READ_BYTES32_64 ::
         map snd (previous_reads @ arithmetic)) th
       with Failure _ -> th)
    else th) goal;;

let ordinary_adapter_discard_obsolete sname ((asl,_) as goal) =
  let v = mk_var(sname,`:x86state`) in
  let rec unbound_statevars_of_read bound_svars tm =
    match tm with
    | Comb(Comb(Const("read",_),_),s) ->
        if mem s bound_svars then [] else [s]
    | Comb(a,b) ->
        union (unbound_statevars_of_read bound_svars a)
              (unbound_statevars_of_read bound_svars b)
    | Abs(v,t) -> unbound_statevars_of_read (v::bound_svars) t
    | _ -> [] in
  let dependencies = map (fun (_,th) -> unbound_statevars_of_read [] (concl th)) asl in
  let initial = itlist (fun us acc ->
    if mem v us then union (subtract us [v]) acc else acc) dependencies [] in
  let rec reachable needed =
    let expanded = itlist (fun us acc ->
      if filter (fun s -> mem s needed) us <> [] then union us acc else acc)
      dependencies needed in
    if expanded = needed then needed else reachable expanded in
  let needed = reachable initial in
  DISCARD_ASSUMPTIONS_TAC (fun thm ->
    let us = unbound_statevars_of_read [] (concl thm) in
    us <> [] && not (mem v us) && filter (fun s -> mem s needed) us = []) goal;;

let ordinary_adapter_control_step exec sname =
  X86_VERBOSE_STEP_TAC exec sname THEN
  ordinary_adapter_normalize_control sname THEN
  ordinary_adapter_discard_obsolete sname THEN CLARIFY_TAC;;

let ordinary_adapter_expose_entry ((asl,_) as goal) =
  let (_,entry) = List.find (fun (_,th) ->
    exists (fun t -> name_of t = "ordinary_adapter_entry")
      (find_terms is_const (concl th))) asl in
  (MP_TAC (REWRITE_RULE[ordinary_adapter_entry; C_ARGUMENTS] entry) THEN
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) goal;;

let ordinary_adapter_meson ((asl,w) as goal) =
  let word_w = rhs (concl (REWRITE_CONV[VAL_EQ_0] w)) in
  let (_,span) = List.find (fun (_,th) ->
    try let rhs_disj = snd (dest_disj (concl th)) in
        rhs_disj = w || rhs_disj = word_w
    with Failure _ -> false) asl in
  let zero = fst (dest_disj (concl span)) in
  let (_,nonempty) = List.find (fun (_,th) -> concl th = mk_neg zero) asl in
  MESON_TAC[span; nonempty; VAL_EQ_0] goal;;

let ordinary_adapter_rip_value tm =
  match tm with
    Comb(Comb(Const("=",_),
              Comb(Comb(Const("read",_),Const("RIP",_)),_)),value) -> Some value
  | _ -> None;;

let ordinary_adapter_debug_stage name conv tm =
  Printf.printf "ADAPTER_CONV %s\n%!" name;
  try conv tm with e ->
    Printf.printf "ADAPTER_CONV_FAILURE %s on %s\n%!" name (string_of_term tm);
    raise e;;

let ordinary_adapter_debug_conv decode_ths ths tm =
  let pc_th = find (fun th ->
    let c = concl th in is_eq c && is_read_rip (fst (dest_eq c))) ths in
  let bytes_loaded_mc_ths = filter (fun th ->
    let cc = concl th in
    is_comb cc && fst (strip_comb cc) = `bytes_loaded` &&
    last (snd (strip_comb cc)) = `ordinary_cesta_mc`) ths in
  let eth = tryfind (fun loaded_mc_th ->
    GEN_REWRITE_CONV I [X86_THM decode_ths loaded_mc_th pc_th] tm)
    bytes_loaded_mc_ths in
  let x86_execute_case_rules =
    let ts = find_terms is_const (concl eth) in
    filter_map (fun t ->
      try Some (assoc (name_of t) X86_EXECUTE_CASES) with Failure _ -> None) ts in
  let stage name conv = ordinary_adapter_debug_stage name conv in
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

let ordinary_adapter_debug_basic_marker name : tactic = fun goal ->
  Printf.printf "ADAPTER_BASIC %s\n%!" name; ALL_TAC goal;;

let ordinary_adapter_debug_basic_step decode_ths sname store (asl,w) =
  let sv = rand w and sv' = mk_var(sname,`:x86state`) in
  let atm = mk_comb(mk_comb(`x86`,sv),sv') in
  let eth = ordinary_adapter_debug_conv decode_ths (map snd asl) atm in
  (match store with
   | Some r -> r := rhs (concl eth)
   | None -> ());
  let progress_tac =
    let c,_ = strip_comb w in
    if name_of c = "eventually" then
      GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC
    else if name_of c = "eventually_n" then
      let stepn = dest_numeral(rand(rator(rator w))) in
      let stepn_decr = stepn -/ num 1 in
      let stepn_thm = GSYM (NUM_ADD_CONV
        (mk_binary "+" (`1:num`,mk_numeral(stepn_decr)))) in
      GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [stepn_thm] THEN
      GEN_REWRITE_TAC I [EVENTUALLY_N_STEP]
    else failwith "ordinary_adapter_debug_basic_step: bad goal" in
  (ordinary_adapter_debug_basic_marker "progress_begin" THEN
   progress_tac THEN
   ordinary_adapter_debug_basic_marker "progress_done" THEN
   CONJ_TAC THENL
   [ordinary_adapter_debug_basic_marker "state_eq_begin" THEN
    GEN_REWRITE_TAC BINDER_CONV [eth] THEN
    ordinary_adapter_debug_basic_marker "state_eq_rewrite_done" THEN
    (CONV_TAC EXISTS_NONTRIVIAL_CONV ORELSE
     (PRINT_GOAL_TAC THEN FAIL_TAC "ordinary adapter state equality ill-formed"));
    ordinary_adapter_debug_basic_marker "new_state_begin" THEN
    X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth] THEN
    ordinary_adapter_debug_basic_marker "new_state_rewrite_done" THEN
    REPEAT X86_UNDEFINED_CHOOSE_TAC THEN
    ordinary_adapter_debug_basic_marker "undefined_done"]) (asl,w);;

let ordinary_adapter_debug_marker name : tactic = fun goal ->
  Printf.printf "ADAPTER_UPDATE %s\n%!" name; ALL_TAC goal;;

let ordinary_adapter_debug_step (mc_length_th,decode_ths) sname =
  ordinary_adapter_debug_marker "basic_begin" THEN
  ordinary_adapter_debug_basic_step decode_ths sname None THEN
  ordinary_adapter_debug_marker "basic_done" THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC (MATCH_MP bytes_loaded_update mc_length_th) THEN
  ordinary_adapter_debug_marker "loaded_done" THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  ordinary_adapter_debug_marker "assumptions_done" THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  ordinary_adapter_debug_marker "maychange_done" THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    Printf.printf "ADAPTER_UPDATE new_rule_done %d\n%!" (length thl);
    map (fun th -> Printf.printf "ADAPTER_NEW_RULE %s\n%!"
      (string_of_term(concl th))) thl;
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ordinary_adapter_debug_marker "simplify_begin" THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    ordinary_adapter_debug_marker "simplify_done" THEN
    STRIP_TAC) THEN
  DISCARD_OLDSTATE_TAC sname THEN CLARIFY_TAC THEN
  ordinary_adapter_debug_marker "step_done";;

(* Step lists are branch-local instruction counts, not reusable state names. *)
let ordinary_adapter_next_index ((_,w):goal) =
  let name = fst (dest_var (rand w)) in
  try
    if String.get name 0 <> 's' then 1 else
    int_of_string (String.sub name 1 (String.length name - 1)) + 1
  with _ -> 1;;

let ordinary_adapter_steps exec indices =
  MAP_EVERY (fun index ((asl,_) as goal) ->
    let fresh = ordinary_adapter_next_index goal in
    let values = List.filter_map
      (fun (_,th) -> ordinary_adapter_rip_value(concl th)) asl in
    Printf.printf "ADAPTER_STEP %d (s%d) predecessor %s\n%!" index fresh
      (String.concat "," (map string_of_term values));
    ((if exists (fun v -> find_terms is_cond v <> []) values
      then PRINT_GOAL_TAC else ALL_TAC) THEN
     ordinary_adapter_normalize_state THEN
     ordinary_adapter_control_step exec ("s" ^ string_of_int fresh) THEN
     ordinary_adapter_normalize_state THEN
     (if mem `word(pc + 970):int64` values ||
         mem `word(pc + 973):int64` values
      then PRINT_GOAL_TAC else ALL_TAC)) goal)
    indices;;

let ORDINARY_ADAPTER_RIP_ZERO_TEST = prove
 (`!n s (a:int64) b.
    ~(0 < n) /\
    read RIP (s:x86state) = (if ~(0 < n) then a else b)
    ==> read RIP s = a`,
  REPEAT STRIP_TAC THEN ordinary_adapter_normalize_state THEN ASM_REWRITE_TAC[]);;

let ORDINARY_ADAPTER_RIP_NONZERO_TEST = prove
 (`!n s (a:int64) b.
    0 < n /\ read RIP (s:x86state) = (if 0 < n then a else b)
    ==> read RIP s = a`,
  REPEAT STRIP_TAC THEN ordinary_adapter_normalize_state THEN ASM_REWRITE_TAC[]);;

let ORDINARY_ADAPTER_RIP_POINTER_TEST = prove
 (`!p s (a:int64) b.
    ~(val (p:int64) = 0) /\
    read RIP (s:x86state) = (if ~(p = word 0) then a else b)
    ==> read RIP s = a`,
  REPEAT STRIP_TAC THEN ordinary_adapter_normalize_state THEN ASM_REWRITE_TAC[]);;

