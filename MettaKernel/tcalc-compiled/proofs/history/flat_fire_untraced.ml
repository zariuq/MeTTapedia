(* Generic flat-rule firing on the x86-64 model of s2n-bignum. *)

needs "x86/proofs/base.ml";;

type_invention_error := true;;

let flat_fire_mc =
  define_assert_from_elf "flat_fire_mc" flat_fire_object
[
  0xf3; 0x0f; 0x1e; 0xfa;
  0x55; 0x53; 0x41; 0x54; 0x41; 0x55; 0x41; 0x56; 0x41; 0x57;
  0x4c; 0x8b; 0x64; 0x24; 0x38; 0x4c; 0x8b; 0x6c; 0x24; 0x40;
  0x45; 0x31; 0xd2; 0x45; 0x31; 0xdb; 0x48; 0x85; 0xc9; 0x74; 0x4d;
  0x42; 0x8b; 0x04; 0x92; 0x89; 0xc3; 0x81; 0xe3; 0xff; 0x00; 0x00; 0x00;
  0x89; 0xc5; 0xc1; 0xed; 0x08; 0x81; 0xe5; 0xff; 0x00; 0x00; 0x00;
  0x41; 0x89; 0xc6; 0x41; 0xc1; 0xee; 0x10;
  0x41; 0x81; 0xe6; 0xff; 0x00; 0x00; 0x00; 0xc1; 0xe8; 0x18;
  0x44; 0x8b; 0x3c; 0x9e; 0x41; 0x01; 0xef; 0x42; 0x8b; 0x1c; 0xb6;
  0x01; 0xc3; 0x42; 0x8b; 0x04; 0xbf; 0xbd; 0x01; 0x00; 0x00; 0x00;
  0x3b; 0x04; 0x9f; 0x44; 0x0f; 0x45; 0xdd;
  0x49; 0xff; 0xc2; 0x49; 0x39; 0xca; 0x75; 0xb3;
  0x45; 0x85; 0xdb; 0x75; 0x51;
  0x45; 0x31; 0xd2; 0x4d; 0x85; 0xc9; 0x74; 0x29;
  0x43; 0x8b; 0x04; 0x90; 0x89; 0xc3; 0x81; 0xe3; 0xff; 0x00; 0x00; 0x00;
  0xc1; 0xe8; 0x08; 0x25; 0xff; 0x00; 0x00; 0x00;
  0x8b; 0x2c; 0x9e; 0x01; 0xc5; 0x8b; 0x04; 0xaf;
  0x43; 0x89; 0x44; 0x95; 0x00; 0x49; 0xff; 0xc2; 0x4d; 0x39; 0xca; 0x75; 0xd7;
  0x45; 0x31; 0xd2; 0x4d; 0x85; 0xc9; 0x74; 0x11;
  0x43; 0x8b; 0x44; 0x95; 0x00; 0x43; 0x89; 0x04; 0x94;
  0x49; 0xff; 0xc2; 0x4d; 0x39; 0xca; 0x75; 0xef;
  0xb8; 0x01; 0x00; 0x00; 0x00; 0xeb; 0x02; 0x31; 0xc0;
  0x41; 0x5f; 0x41; 0x5e; 0x41; 0x5d; 0x41; 0x5c; 0x5b; 0x5d; 0xc3
];;

let FLAT_FIRE_EXEC = X86_MK_EXEC_RULE flat_fire_mc;;

let flat_prefix = new_recursive_definition num_RECURSION
 `(flat_prefix 0 (l:int32 list) = []) /\
  (flat_prefix (SUC n) l =
     if l = [] then [] else CONS (HD l) (flat_prefix n (TL l)))`;;

let FLAT_PREFIX_SUC_EL = prove
 (`!l (i:num). i < LENGTH l
      ==> flat_prefix (i + 1) l = APPEND (flat_prefix i l) [EL i l]`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[GSYM ADD1] THEN ONCE_REWRITE_TAC[flat_prefix] THEN
    REWRITE_TAC[CONJUNCT1 flat_prefix; NOT_CONS_NIL; HD; TL; APPEND; EL];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH; GSYM ADD1] THEN ONCE_REWRITE_TAC[flat_prefix] THEN
  REWRITE_TAC[CONJUNCT1 flat_prefix; NOT_CONS_NIL; HD; TL; APPEND; EL] THEN
  DISCH_TAC THEN REWRITE_TAC[ADD1] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LT_SUC]) THEN REWRITE_TAC[];
    REWRITE_TAC[]]);;

let FLAT_PREFIX_MAP = prove
 (`!f l n. flat_prefix n (MAP f l) = MAP f (flat_prefix n l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[flat_prefix; MAP; NOT_CONS_NIL; HD; TL] THEN
  ASM_REWRITE_TAC[]);;

let FLAT_PREFIX_ALL = prove
 (`!l. flat_prefix (LENGTH l) l = l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; flat_prefix; NOT_CONS_NIL; HD; TL] THEN
  ASM_REWRITE_TAC[]);;

let flat_i = new_definition
 `flat_i (g:int32) = val (word_and g (word 255))`;;
let flat_j = new_definition
 `flat_j (g:int32) = val (word_and (word_ushr g 8) (word 255))`;;
let flat_i0 = new_definition
 `flat_i0 (g:int32) = val (word_and (word_ushr g 16) (word 255))`;;
let flat_j0 = new_definition
 `flat_j0 (g:int32) = val (word_ushr g 24)`;;

let flat_offset = new_definition
 `flat_offset (rs:int32 list) m =
    val (word_add (EL (flat_i m) rs) (word (flat_j m)):int32)`;;

let flat_offset0 = new_definition
 `flat_offset0 (rs:int32 list) g =
    val (word_add (EL (flat_i0 g) rs) (word (flat_j0 g)):int32)`;;

let flat_field = new_definition
 `flat_field (fs:int32 list) (rs:int32 list) m =
    EL (flat_offset rs m) fs`;;

let flat_guard_holds = new_definition
 `flat_guard_holds (fs:int32 list) (rs:int32 list) g <=>
    EL (flat_offset rs g) fs = EL (flat_offset0 rs g) fs`;;

let flat_guard_valid = new_definition
 `flat_guard_valid (fs:int32 list) (rs:int32 list) g <=>
    flat_i g < LENGTH rs /\ flat_i0 g < LENGTH rs /\
    flat_offset rs g < LENGTH fs /\ flat_offset0 rs g < LENGTH fs`;;

let flat_make_valid = new_definition
 `flat_make_valid (fs:int32 list) (rs:int32 list) m <=>
    flat_i m < LENGTH rs /\ flat_offset rs m < LENGTH fs`;;

let flat_guards_hold = new_definition
 `flat_guards_hold (fs:int32 list) (rs:int32 list) gs = ALL (flat_guard_holds fs rs) gs`;;

let flat_selected = new_definition
 `flat_selected (fs:int32 list) (rs:int32 list) ms = MAP (flat_field fs rs) ms`;;

let flat_valid = new_definition
 `flat_valid (fs:int32 list) (rs:int32 list) gs ms <=>
    ALL (flat_guard_valid fs rs) gs /\ ALL (flat_make_valid fs rs) ms`;;

let flat_saved = new_definition
 `flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
              init_r14 init_r15 s <=>
    read RSP s = word_sub stackpointer (word 48) /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) s = init_rbp /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s = init_rbx /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s = init_r12 /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s = init_r13 /\
    read (memory :> bytes64 (word_sub stackpointer (word 40))) s = init_r14 /\
    read (memory :> bytes64 (word_sub stackpointer (word 48))) s = init_r15`;;

let flat_mid = new_definition
 `flat_mid pc fields rows guards make dest scratch (fs:int32 list) (rs:int32 list) (gs:int32 list)
           (ms:int32 list) (ds:int32 list) (zs:int32 list)
           stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
           init_r14 init_r15 s <=>
    bytes_loaded s (word pc) flat_fire_mc /\
    read RIP s = word (pc + 0x70) /\
    read RDI s = fields /\ read RSI s = rows /\ read RDX s = guards /\
    read RCX s = word (LENGTH gs) /\ read R8 s = make /\
    read R9 s = word (LENGTH ms) /\ read R12 s = dest /\ read R13 s = scratch /\
    read R11 s = word (bitval (~flat_guards_hold fs rs gs)) /\
    wordlist_of_num (LENGTH fs) (read (memory :> bytes(fields,4 * LENGTH fs)) s) = fs /\
    wordlist_of_num (LENGTH rs) (read (memory :> bytes(rows,4 * LENGTH rs)) s) = rs /\
    wordlist_of_num (LENGTH gs) (read (memory :> bytes(guards,4 * LENGTH gs)) s) = gs /\
    wordlist_of_num (LENGTH ms) (read (memory :> bytes(make,4 * LENGTH ms)) s) = ms /\
    wordlist_of_num (LENGTH ms) (read (memory :> bytes(dest,4 * LENGTH ms)) s) = ds /\
    wordlist_of_num (LENGTH ms) (read (memory :> bytes(scratch,4 * LENGTH ms)) s) = zs /\
    flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
               init_r14 init_r15 s`;;

let flat_make_inv = new_definition
 `flat_make_inv fields rows make dest scratch (fs:int32 list) (rs:int32 list)
                (ms:int32 list) (ds:int32 list)
                stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                init_r14 init_r15 i s <=>
    read RDI s = fields /\ read RSI s = rows /\ read R8 s = make /\
    read R9 s = word (LENGTH ms) /\ read R12 s = dest /\ read R13 s = scratch /\
    read R10 s = word i /\
    wordlist_of_num (LENGTH fs) (read (memory :> bytes(fields,4 * LENGTH fs)) s) = fs /\
    wordlist_of_num (LENGTH rs) (read (memory :> bytes(rows,4 * LENGTH rs)) s) = rs /\
    wordlist_of_num (LENGTH ms) (read (memory :> bytes(make,4 * LENGTH ms)) s) = ms /\
    wordlist_of_num (LENGTH ms) (read (memory :> bytes(dest,4 * LENGTH ms)) s) = ds /\
    (wordlist_from_memory(scratch,i) s : int32 list) =
      flat_prefix i (flat_selected fs rs ms) /\
    flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
               init_r14 init_r15 s`;;

let flat_make_done = new_definition
 `flat_make_done pc dest scratch (os:int32 list) (ds:int32 list)
                 stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                 init_r14 init_r15 s <=>
    bytes_loaded s (word pc) flat_fire_mc /\
    read RIP s = word (pc + 0xa6) /\
    read R9 s = word (LENGTH os) /\
    read R12 s = dest /\ read R13 s = scratch /\
    (wordlist_from_memory(scratch,LENGTH os) s : int32 list) = os /\
    wordlist_of_num (LENGTH os) (read (memory :> bytes(dest,4 * LENGTH os)) s) = ds /\
    flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
               init_r14 init_r15 s`;;

let FLAT_GUARD_VALID_EL = prove
 (`!fs rs gs ms i. flat_valid fs rs gs ms /\ i < LENGTH gs
      ==> flat_guard_valid fs rs (EL i gs)`,
  REWRITE_TAC[flat_valid; GSYM ALL_EL] THEN MESON_TAC[]);;

let FLAT_MAKE_VALID_EL = prove
 (`!fs rs gs ms i. flat_valid fs rs gs ms /\ i < LENGTH ms
      ==> flat_make_valid fs rs (EL i ms)`,
  REWRITE_TAC[flat_valid; GSYM ALL_EL] THEN MESON_TAC[]);;

let FLAT_BAD_WORD = prove
 (`!P Q. word_or (word (bitval (~P)):int64) (word (bitval (~Q))) =
         word (bitval (~(P /\ Q)))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let FLAT_READ = prove
 (`!(fs:int32 list) (a:int64) (s:x86state) i.
      i < LENGTH fs /\ wordlist_from_memory(a,LENGTH fs) s = fs
      ==> read (memory :> bytes32 (word_add a (word (4 * i)))) s = EL i fs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `LENGTH(fs:int32 list)`; `i:num`; `s:x86state`]
                (INST_TYPE [`:4`,`:N`] EL_WORDLIST_FROM_MEMORY)) THEN
  ASM_REWRITE_TAC[BYTES32_WBYTES; DIMINDEX_4; EQ_SYM_EQ]);;

let WORDLIST_FROM_MEMORY_32 = prove
 (`!a n s. wordlist_from_memory(a,n) s : int32 list =
           wordlist_of_num n (read (memory :> bytes(a,4 * n)) s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `s:x86state`]
                (INST_TYPE [`:4`,`:N`] WORDLIST_FROM_MEMORY)) THEN
  REWRITE_TAC[DIMINDEX_4]);;

let FLAT_WORDLIST_PREFIX_32 = prove
 (`!(a:int64) i (l:int32 list) (s:x86state) (t:x86state).
    i < LENGTH l /\
    (wordlist_from_memory(a,i) s : int32 list) = flat_prefix i l /\
    (wordlist_from_memory(a,i) t : int32 list) = wordlist_from_memory(a,i) s /\
    read (memory :> bytes32 (word_add a (word (4 * i)))) t = EL i l
    ==> wordlist_from_memory(a,SUC i) t = flat_prefix (i + 1) l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `i:num`; `t:x86state`]
    (INST_TYPE [`:4`,`:N`] (CONJUNCT2 WORDLIST_FROM_MEMORY_CLAUSES))) THEN
  REWRITE_TAC[DIMINDEX_4; GSYM BYTES32_WBYTES] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[FLAT_PREFIX_SUC_EL]);;

let FLAT_WORD_ZX_EQ_32_64 = prove
 (`!(x:int32) y. (word_zx x:int64) = word_zx y <=> x = y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_64] THEN
  SUBGOAL_THEN `val (x:int32) < 2 EXP 64 /\ val (y:int32) < 2 EXP 64`
  ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
      ARITH_TAC;
      MP_TAC(ISPEC `y:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
      ARITH_TAC];
    ASM_SIMP_TAC[MOD_LT]]);;

let FLAT_ZX_TAC =
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_WORD_SIMPLE; DIMINDEX_32; DIMINDEX_64;
           ARITH_LE; ARITH_LT];;

let FLAT_CMOV_ACC = prove
 (`!p q. (word_zx:int32->int64) (if ~q then word 1 else word (bitval (~p))) =
         word (bitval (~(p /\ q)))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN BOOL_CASES_TAC `q:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

let FLAT_STACK24 = prove
 (`!(sp:int64). word_sub sp (word 24) =
        word_sub (word_sub (word_sub sp (word 8)) (word 8)) (word 8)`,
  CONV_TAC WORD_RULE);;
let FLAT_STACK32 = prove
 (`!(sp:int64). word_sub sp (word 32) =
        word_sub (word_sub (word_sub (word_sub sp (word 8)) (word 8)) (word 8))
                 (word 8)`,
  CONV_TAC WORD_RULE);;
let FLAT_STACK40 = prove
 (`!(sp:int64). word_sub sp (word 40) =
        word_sub (word_sub (word_sub (word_sub (word_sub sp (word 8)) (word 8))
                  (word 8)) (word 8)) (word 8)`,
  CONV_TAC WORD_RULE);;
let FLAT_STACK48 = prove
 (`!(sp:int64). word_sub sp (word 48) =
        word_sub (word_sub (word_sub (word_sub (word_sub (word_sub (sp) (word 8)) (word 8)) (word 8)) (word 8)) (word 8)) (word 8)`,
  CONV_TAC WORD_RULE);;

let FLAT_SUB_SUB = WORD_RULE
 `word_sub (word_sub (x:int64) (word a)) (word b) = word_sub x (word (a + b))`;;

let FLAT_PROLOGUE_SUBSUMED = prove
 (`(MAYCHANGE [RIP] ,, MAYCHANGE [events] ,, MAYCHANGE [RSP] ,,
    MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 8))] ,,
    MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 16))] ,,
    MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 24))] ,,
    MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 32))] ,,
    MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 40))] ,,
    MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 48))] ,,
    MAYCHANGE [R12] ,, MAYCHANGE [R13] ,, MAYCHANGE [R10] ,,
    MAYCHANGE [ZF] ,, MAYCHANGE [SF] ,, MAYCHANGE [PF] ,,
    MAYCHANGE [CF] ,, MAYCHANGE [OF] ,, MAYCHANGE [AF] ,, MAYCHANGE [R11])
   subsumed
   (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(dest,4 * LENGTH (ms:int32 list));
               memory :> bytes(scratch,4 * LENGTH ms);
               memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[ETA_AX;
    WORD_RULE `word_sub x (word 8):int64 =
      word_add (word_sub x (word 48)) (word 40)`;
    WORD_RULE `word_sub x (word 16):int64 =
      word_add (word_sub x (word 48)) (word 32)`;
    WORD_RULE `word_sub x (word 24):int64 =
      word_add (word_sub x (word 48)) (word 24)`;
    WORD_RULE `word_sub x (word 32):int64 =
      word_add (word_sub x (word 48)) (word 16)`;
    WORD_RULE `word_sub x (word 40):int64 =
      word_add (word_sub x (word 48)) (word 8)`] THEN
  SUBSUMED_MAYCHANGE_TAC);;

let flat_guard_inv = new_definition
 `flat_guard_inv fields rows guards make dest scratch (fs:int32 list) (rs:int32 list) (gs:int32 list)
           (ms:int32 list) (ds:int32 list) (zs:int32 list)
                 stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                 init_r14 init_r15 i s <=>
    read RDI s = fields /\ read RSI s = rows /\ read RDX s = guards /\
    read RCX s = word (LENGTH gs) /\ read R8 s = make /\
    read R9 s = word (LENGTH ms) /\ read R12 s = dest /\ read R13 s = scratch /\
    read R10 s = word i /\
    read R11 s = word (bitval (~flat_guards_hold fs rs (flat_prefix i gs))) /\
    wordlist_of_num (LENGTH fs) (read (memory :> bytes(fields,4 * LENGTH fs)) s) = fs /\
    wordlist_of_num (LENGTH rs) (read (memory :> bytes(rows,4 * LENGTH rs)) s) = rs /\
    wordlist_of_num (LENGTH gs) (read (memory :> bytes(guards,4 * LENGTH gs)) s) = gs /\
    wordlist_of_num (LENGTH ms) (read (memory :> bytes(make,4 * LENGTH ms)) s) = ms /\
    wordlist_of_num (LENGTH ms) (read (memory :> bytes(dest,4 * LENGTH ms)) s) = ds /\
    wordlist_of_num (LENGTH ms) (read (memory :> bytes(scratch,4 * LENGTH ms)) s) = zs /\
    flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
               init_r14 init_r15 s`;;

let FLAT_GUARD_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[flat_guard_inv; flat_saved] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `flat_guard_valid fs rs (EL i gs)` ASSUME_TAC THENL
   [MATCH_MP_TAC FLAT_GUARD_VALID_EL THEN EXISTS_TAC `ms:int32 list` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_guard_valid]) THEN
  SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes32 (word_add guards (word (4 * i)))) (s0:x86state) =
      EL i (gs:int32 list) /\
    read (memory :> bytes32 (word_add rows (word (4 * flat_i (EL i gs))))) s0 =
      EL (flat_i (EL i gs)) (rs:int32 list) /\
    read (memory :> bytes32 (word_add rows (word (4 * flat_i0 (EL i gs))))) s0 =
      EL (flat_i0 (EL i gs)) rs /\
    read (memory :> bytes32 (word_add fields
      (word (4 * flat_offset rs (EL i gs))))) s0 =
      EL (flat_offset rs (EL i gs)) (fs:int32 list) /\
    read (memory :> bytes32 (word_add fields
      (word (4 * flat_offset0 rs (EL i gs))))) s0 =
      EL (flat_offset0 rs (EL i gs)) fs`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN
    ASM_MESON_TAC[FLAT_READ; flat_guard_valid; flat_offset; flat_offset0;
                  WORDLIST_FROM_MEMORY_32];
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (1--10) THEN
  SUBGOAL_THEN
   `read RBX s10 = word (flat_i (EL i gs)) /\
    read RBP s10 = word (flat_j (EL i gs)) /\
    read R14 s10 = word (flat_i0 (EL i gs)) /\
    read RAX s10 = word (flat_j0 (EL i gs))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[flat_i; flat_j; flat_i0; flat_j0; GSYM word_zx] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;
    DISCARD_MATCHING_ASSUMPTIONS
     [`read RBX s = x`; `read RBP s = x`; `read R14 s = x`; `read RAX s = x`] THEN
    STRIP_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `flat_i (EL i gs) < LENGTH (rs:int32 list) /\ (x:bool)`)
           (concl th)
    then STRIP_ASSUME_TAC th else failwith "not the bounds") THEN
  VAL_INT64_TAC `flat_i (EL i (gs:int32 list))` THEN
  VAL_INT64_TAC `flat_i0 (EL i (gs:int32 list))` THEN
  VAL_INT64_TAC `flat_offset rs (EL i (gs:int32 list))` THEN
  VAL_INT64_TAC `flat_offset0 rs (EL i (gs:int32 list))` THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (11--12) THEN
  SUBGOAL_THEN `read R15 s12 = word (flat_offset rs (EL i gs))` MP_TAC THENL
   [ASM_REWRITE_TAC[flat_offset; GSYM word_zx] THEN FLAT_ZX_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`read R15 s = x`] THEN STRIP_TAC] THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (13--14) THEN
  SUBGOAL_THEN `read RBX s14 = word (flat_offset0 rs (EL i gs))` MP_TAC THENL
   [ASM_REWRITE_TAC[flat_offset0; GSYM word_zx] THEN FLAT_ZX_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`read RBX s = x`] THEN STRIP_TAC] THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (15--18) THEN
  SUBGOAL_THEN
   `read R11 s18 =
    word (bitval (~flat_guards_hold fs rs (flat_prefix (i + 1) gs)))`
  MP_TAC THENL
   [ASM_SIMP_TAC[flat_guards_hold; FLAT_PREFIX_SUC_EL; ALL_APPEND; ALL;
                 flat_guard_holds] THEN
    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_LE; ARITH_LT;
             VAL_WORD_SUB_EQ_0; VAL_EQ; FLAT_CMOV_ACC];
    DISCARD_MATCHING_ASSUMPTIONS [`read R11 s = x`] THEN STRIP_TAC] THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (19--20) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0] THEN
  VAL_INT64_TAC `i + 1` THEN ASM_REWRITE_TAC[];;

let FLAT_FIRE_GUARDS_NONZERO = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list) (gs:int32 list)
           (ms:int32 list) (ds:int32 list) (zs:int32 list) pc stackpointer
    returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15.
    flat_valid fs rs gs ms /\ 0 < LENGTH gs /\
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
      (\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                    stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                    init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
                  memory :> bytes(scratch,4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; flat_mid; flat_saved; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ENSURES_WHILE_PAUP_TAC `0` `LENGTH(gs:int32 list)` `pc + 0x23` `pc + 0x6e`
   `\i s. flat_guard_inv fields rows guards make dest scratch fs rs gs ms ds zs
                         stackpointer returnaddress init_rbp init_rbx init_r12
                         init_r13 init_r14 init_r15 i s /\
          (read ZF s <=> i = LENGTH gs)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[flat_guard_inv; flat_saved; flat_prefix; ALL; flat_guards_hold;
                BITVAL_CLAUSES; WORDLIST_FROM_MEMORY_32] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC FLAT_FIRE_EXEC (1--7) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FLAT_SUB_SUB]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    SUBGOAL_THEN
     `read (memory :> bytes64
        (word_add (word_sub stackpointer (word 48)) (word 56))) s7 = dest /\
      read (memory :> bytes64
        (word_add (word_sub stackpointer (word 48)) (word 64))) s7 = scratch`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[WORD_RULE
       `word_add (word_sub x (word 48)) (word 56):int64 = word_add x (word 8)`;
                  WORD_RULE
       `word_add (word_sub x (word 48)) (word 64):int64 = word_add x (word 16)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X86_STEPS_TAC FLAT_FIRE_EXEC (8--13) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FLAT_SUB_SUB]) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`];
      FIRST_ASSUM
       (ACCEPT_TAC o MATCH_MP (REWRITE_RULE[subsumed] FLAT_PROLOGUE_SUBSUMED) o
        check (maychange_term o concl))];
    FLAT_GUARD_BODY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[flat_guard_inv; flat_saved; WORDLIST_FROM_MEMORY_32] THEN
    X86_SIM_TAC FLAT_FIRE_EXEC [1];
    ASM_REWRITE_TAC[flat_guard_inv; flat_mid; flat_saved; FLAT_PREFIX_ALL;
                    WORDLIST_FROM_MEMORY_32] THEN
    X86_SIM_TAC FLAT_FIRE_EXEC [1] THEN
    ASM_REWRITE_TAC[flat_mid; flat_saved]]);;


let FLAT_FIRE_GUARDS_ZERO = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list)
    (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
    pc stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
    init_r15.
    flat_valid fs rs gs ms /\ gs = [] /\
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
      (\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                    stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                    init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
                  memory :> bytes(scratch,4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; flat_mid; flat_saved; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_32; flat_guards_hold; ALL;
                  wordlist_of_num] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (1--7) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FLAT_SUB_SUB]) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN
   `read (memory :> bytes64
      (word_add (word_sub stackpointer (word 48)) (word 56))) s7 = dest /\
    read (memory :> bytes64
      (word_add (word_sub stackpointer (word 48)) (word 64))) s7 = scratch`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_add (word_sub x (word 48)) (word 56):int64 = word_add x (word 8)`;
                WORD_RULE
     `word_add (word_sub x (word 48)) (word 64):int64 = word_add x (word 16)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (8--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FLAT_SUB_SUB]) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; wordlist_of_num; READ_MEMORY_BYTES_TRIVIAL;
              BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_0] THEN
  FIRST_ASSUM
   (ACCEPT_TAC o MATCH_MP (REWRITE_RULE[subsumed] FLAT_PROLOGUE_SUBSUMED) o
    check (maychange_term o concl)));;


let FLAT_MAKE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[flat_make_inv; flat_saved; WORDLIST_FROM_MEMORY_32] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `flat_make_valid fs rs (EL i ms)` ASSUME_TAC THENL
   [MATCH_MP_TAC FLAT_MAKE_VALID_EL THEN EXISTS_TAC `gs:int32 list` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_make_valid]) THEN
  SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes32 (word_add make (word (4 * i)))) (s0:x86state) =
      EL i (ms:int32 list) /\
    read (memory :> bytes32 (word_add rows (word (4 * flat_i (EL i ms))))) s0 =
      EL (flat_i (EL i ms)) (rs:int32 list) /\
    read (memory :> bytes32 (word_add fields
      (word (4 * flat_offset rs (EL i ms))))) s0 =
      flat_field fs rs (EL i ms)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN
    ASM_MESON_TAC[FLAT_READ; flat_make_valid; flat_offset; flat_field;
                  WORDLIST_FROM_MEMORY_32];
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `nonoverlapping ((scratch:int64),4 * i)
      (word_add scratch (word (4 * i)),4)`
  ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (1--5) THEN
  SUBGOAL_THEN
   `read RBX s5 = word (flat_i (EL i ms)) /\
    read RAX s5 = word (flat_j (EL i ms))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[flat_i; flat_j; GSYM word_zx] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;
    DISCARD_MATCHING_ASSUMPTIONS [`read RBX s = x`; `read RAX s = x`] THEN
    STRIP_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `flat_i (EL i ms) < LENGTH (rs:int32 list) /\ (x:bool)`)
           (concl th)
    then STRIP_ASSUME_TAC th else failwith "not the bounds") THEN
  VAL_INT64_TAC `flat_i (EL i (ms:int32 list))` THEN
  VAL_INT64_TAC `flat_offset rs (EL i (ms:int32 list))` THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (6--7) THEN
  SUBGOAL_THEN `read RBP s7 = word (flat_offset rs (EL i ms))` MP_TAC THENL
   [ASM_REWRITE_TAC[flat_offset; GSYM word_zx] THEN FLAT_ZX_TAC;
    DISCARD_MATCHING_ASSUMPTIONS [`read RBP s = x`] THEN STRIP_TAC] THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (8--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0] THEN
  VAL_INT64_TAC `i + 1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `wordlist_of_num (i + 1)
      (read (memory :> bytes (scratch,4 * (i + 1))) s11) =
    flat_prefix (i + 1) (flat_selected fs rs ms)`
  ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[WORDLIST_FROM_MEMORY_32; ADD1]
      (ISPECL [`scratch:int64`; `i:num`; `flat_selected fs rs ms`;
               `s11:x86state`; `s11:x86state`] FLAT_WORDLIST_PREFIX_32)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[flat_selected; LENGTH_MAP; EL_MAP; WORD_ZX_ZX;
                   DIMINDEX_32; DIMINDEX_64; ARITH_LE; ARITH_LT];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[];;

let FLAT_FIRE_MAKE_NONZERO = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list)
    (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
    pc stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
    init_r15.
    flat_valid fs rs gs ms /\ flat_guards_hold fs rs gs /\ 0 < LENGTH ms /\
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
      (\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                    stackpointer returnaddress init_rbp init_rbx init_r12
                    init_r13 init_r14 init_r15 s)
      (\s. flat_make_done pc dest scratch (flat_selected fs rs ms) ds
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RAX; RBX; RBP; R10] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(scratch,4 * LENGTH ms)])`,
  REWRITE_TAC[SOME_FLAGS; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
              flat_mid; flat_make_done; flat_saved; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ENSURES_WHILE_PAUP_TAC `0` `LENGTH(ms:int32 list)` `pc + 0x7d` `pc + 0xa4`
   `\i s. flat_make_inv fields rows make dest scratch fs rs ms ds
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 i s /\
          (read ZF s <=> i = LENGTH ms)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[flat_make_inv; flat_saved; flat_prefix;
                WORDLIST_FROM_MEMORY_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC FLAT_FIRE_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_SIMP_TAC[BITVAL_CLAUSES; ARITH_RULE `0 < n ==> ~(n = 0)`;
                 WORDLIST_FROM_MEMORY_CLAUSES];
    FLAT_MAKE_BODY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[flat_make_inv; flat_saved; WORDLIST_FROM_MEMORY_32] THEN
    X86_SIM_TAC FLAT_FIRE_EXEC [1];
    ASM_REWRITE_TAC[flat_make_inv; flat_make_done; flat_saved; FLAT_PREFIX_ALL;
                    flat_selected; LENGTH_MAP; WORDLIST_FROM_MEMORY_32] THEN
    X86_SIM_TAC FLAT_FIRE_EXEC [1] THEN
    ASM_REWRITE_TAC[flat_make_done; flat_saved; FLAT_PREFIX_MAP;
                    FLAT_PREFIX_ALL]]);;


let FLAT_FIRE_MAKE_ZERO = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list)
    (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
    pc stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
    init_r15.
    flat_valid fs rs gs ms /\ flat_guards_hold fs rs gs /\ ms = [] /\
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
      (\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                    stackpointer returnaddress init_rbp init_rbx init_r12
                    init_r13 init_r14 init_r15 s)
      (\s. flat_make_done pc dest scratch (flat_selected fs rs ms) ds
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RAX; RBX; RBP; R10] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(scratch,4 * LENGTH ms)])`,
  REWRITE_TAC[SOME_FLAGS; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
              flat_mid; flat_make_done; flat_saved; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ASM_REWRITE_TAC[flat_selected; MAP; WORDLIST_FROM_MEMORY_CLAUSES;
                  wordlist_of_num] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[BITVAL_CLAUSES; VAL_WORD_0; WORDLIST_FROM_MEMORY_CLAUSES;
               wordlist_of_num] THEN
  REWRITE_TAC[LENGTH; VAL_WORD_0; WORDLIST_FROM_MEMORY_CLAUSES]);;


let flat_dest_inv = new_definition
 `flat_dest_inv dest scratch (os:int32 list)
                stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                init_r14 init_r15 i s <=>
    read R9 s = word (LENGTH os) /\
    read R12 s = dest /\ read R13 s = scratch /\ read R10 s = word i /\
    (wordlist_from_memory(scratch,LENGTH os) s : int32 list) = os /\
    (wordlist_from_memory(dest,i) s : int32 list) = flat_prefix i os /\
    flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
               init_r14 init_r15 s`;;

let flat_dest_done = new_definition
 `flat_dest_done pc dest scratch (os:int32 list)
                 stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                 init_r14 init_r15 s <=>
    bytes_loaded s (word pc) flat_fire_mc /\
    read RIP s = word (pc + 0xbf) /\
    (wordlist_from_memory(dest,LENGTH os) s : int32 list) = os /\
    (wordlist_from_memory(scratch,LENGTH os) s : int32 list) = os /\
    flat_saved stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
               init_r14 init_r15 s`;;

let FLAT_DEST_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[flat_dest_inv; flat_saved; WORDLIST_FROM_MEMORY_32] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes32 (word_add scratch (word (4 * i)))) (s0:x86state) =
      EL i (os:int32 list)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[FLAT_READ; WORDLIST_FROM_MEMORY_32]; ALL_TAC] THEN
  SUBGOAL_THEN
   `nonoverlapping ((dest:int64),4 * i) (word_add dest (word (4 * i)),4)`
  ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0] THEN
  VAL_INT64_TAC `i + 1` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `wordlist_of_num (i + 1) (read (memory :> bytes (dest,4 * (i + 1))) s4) =
    flat_prefix (i + 1) (os:int32 list)`
  ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[WORDLIST_FROM_MEMORY_32; ADD1]
      (ISPECL [`dest:int64`; `i:num`; `os:int32 list`;
               `s4:x86state`; `s4:x86state`] FLAT_WORDLIST_PREFIX_32)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH_LE; ARITH_LT];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[];;

let FLAT_FIRE_DEST_NONZERO = prove
 (`!dest scratch (os:int32 list) (ds:int32 list) pc stackpointer returnaddress
    init_rbp init_rbx init_r12 init_r13 init_r14 init_r15.
    0 < LENGTH os /\ LENGTH ds = LENGTH os /\ LENGTH os < 2 EXP 58 /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc); (word_sub stackpointer (word 48),56)]
      [(dest,4 * LENGTH os); (scratch,4 * LENGTH os)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub stackpointer (word 48),56) /\
    nonoverlapping (scratch,4 * LENGTH os) (dest,4 * LENGTH os)
    ==> ensures x86
      (\s. flat_make_done pc dest scratch os ds
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (\s. flat_dest_done pc dest scratch os
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RAX; R10] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH os)])`,
  REWRITE_TAC[SOME_FLAGS; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
              flat_make_done; flat_dest_done; flat_saved; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `LENGTH(os:int32 list)` THEN
  ENSURES_WHILE_PAUP_TAC `0` `LENGTH(os:int32 list)` `pc + 0xae` `pc + 0xbd`
   `\i s. flat_dest_inv dest scratch os
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 i s /\
          (read ZF s <=> i = LENGTH os)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[flat_dest_inv; flat_saved; flat_prefix;
                WORDLIST_FROM_MEMORY_CLAUSES; WORDLIST_FROM_MEMORY_32] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC FLAT_FIRE_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`;
                 WORDLIST_FROM_MEMORY_CLAUSES];
    FLAT_DEST_BODY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[flat_dest_inv; flat_saved; WORDLIST_FROM_MEMORY_32] THEN
    X86_SIM_TAC FLAT_FIRE_EXEC [1];
    ASM_REWRITE_TAC[flat_dest_inv; flat_dest_done; flat_saved; FLAT_PREFIX_ALL;
                    WORDLIST_FROM_MEMORY_32] THEN
    X86_SIM_TAC FLAT_FIRE_EXEC [1] THEN
    ASM_REWRITE_TAC[flat_dest_done; flat_saved; FLAT_PREFIX_ALL]]);;

let FLAT_FIRE_DEST_ZERO = prove
 (`!dest scratch (os:int32 list) (ds:int32 list) pc stackpointer returnaddress
    init_rbp init_rbx init_r12 init_r13 init_r14 init_r15.
    os = [] /\ LENGTH ds = LENGTH os /\ LENGTH os < 2 EXP 58 /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc); (word_sub stackpointer (word 48),56)]
      [(dest,4 * LENGTH os); (scratch,4 * LENGTH os)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub stackpointer (word 48),56) /\
    nonoverlapping (scratch,4 * LENGTH os) (dest,4 * LENGTH os)
    ==> ensures x86
      (\s. flat_make_done pc dest scratch os ds
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (\s. flat_dest_done pc dest scratch os
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RAX; R10] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH os)])`,
  REWRITE_TAC[SOME_FLAGS; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
              flat_make_done; flat_dest_done; flat_saved; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `LENGTH(os:int32 list)` THEN
  ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES; WORDLIST_FROM_MEMORY_32;
                  wordlist_of_num] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_0; WORDLIST_FROM_MEMORY_CLAUSES; wordlist_of_num] THEN
  REWRITE_TAC[LENGTH; VAL_WORD_0; WORDLIST_FROM_MEMORY_CLAUSES] THEN
  SUBGOAL_THEN `LENGTH (ds:int32 list) = 0` MP_TAC THENL
   [ASM_SIMP_TAC[LENGTH]; REWRITE_TAC[LENGTH_EQ_NIL]]);;


let flat_return = new_definition
 `flat_return dest scratch (ds:int32 list) (zs:int32 list) returnvalue
              stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
              init_r14 init_r15 s <=>
    read RIP s = returnaddress /\
    read RSP s = word_add stackpointer (word 8) /\
    C_RETURN s = word returnvalue /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15 /\
    (wordlist_from_memory(dest,LENGTH ds) s : int32 list) = ds /\
    (wordlist_from_memory(scratch,LENGTH zs) s : int32 list) = zs`;;

let FLAT_FIRE_ACCEPT_RETURN = prove
 (`!dest scratch (os:int32 list) pc stackpointer returnaddress init_rbp init_rbx
    init_r12 init_r13 init_r14 init_r15.
    ensures x86
      (\s. flat_dest_done pc dest scratch os
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (\s. flat_return dest scratch os os 1
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R12; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; flat_dest_done; flat_return; flat_saved;
              WORDLIST_FROM_MEMORY_32; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (1--2) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 48)) (word 8):int64 = word_sub x (word 40)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 40)) (word 8):int64 = word_sub x (word 32)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [5] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 32)) (word 8):int64 = word_sub x (word 24)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [6] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 24)) (word 8):int64 = word_sub x (word 16)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [7] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 16)) (word 8):int64 = word_sub x (word 8)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [8] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 8)) (word 8):int64 = x`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [9] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let FLAT_FIRE_REFUSE_RETURN = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list)
    (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
    pc stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
    init_r15.
    LENGTH ds = LENGTH ms /\ LENGTH zs = LENGTH ms /\
    ~flat_guards_hold fs rs gs
    ==> ensures x86
      (\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                    stackpointer returnaddress init_rbp init_rbx init_r12
                    init_r13 init_r14 init_r15 s)
      (\s. flat_return dest scratch ds zs 0
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R12; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; flat_mid; flat_return; flat_saved;
              WORDLIST_FROM_MEMORY_32; fst FLAT_FIRE_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ASM_SIMP_TAC[BITVAL_CLAUSES] THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC (1--3) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 48)) (word 8):int64 = word_sub x (word 40)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [5] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 40)) (word 8):int64 = word_sub x (word 32)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [6] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 32)) (word 8):int64 = word_sub x (word 24)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [7] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 24)) (word 8):int64 = word_sub x (word 16)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [8] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 16)) (word 8):int64 = word_sub x (word 8)`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [9] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 8)) (word 8):int64 = x`]) THEN
  X86_STEPS_TAC FLAT_FIRE_EXEC [10] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;


let FLAT_MAKE_FRAME_SUBSUMED = prove
 (`(MAYCHANGE [RIP; RAX; RBX; RBP; R10] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(scratch,4 * LENGTH (ms:int32 list))])
   subsumed
   (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
               memory :> bytes(scratch,4 * LENGTH ms);
               memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC);;

let FLAT_DEST_FRAME_SUBSUMED = prove
 (`(MAYCHANGE [RIP; RAX; R10] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(dest,4 * LENGTH (ms:int32 list))])
   subsumed
   (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
               memory :> bytes(scratch,4 * LENGTH ms);
               memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC);;

let FLAT_RETURN_FRAME_SUBSUMED = prove
 (`(MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R12; R13; R14; R15] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events])
   subsumed
   (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(dest,4 * LENGTH (ms:int32 list));
               memory :> bytes(scratch,4 * LENGTH ms);
               memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REWRITE_TAC[ETA_AX] THEN SUBSUMED_MAYCHANGE_TAC);;

let FLAT_FULL_FRAME_IDEMPOT = prove
 (`(MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(dest,4 * LENGTH (ms:int32 list));
               memory :> bytes(scratch,4 * LENGTH ms);
               memory :> bytes(word_sub stackpointer (word 48),48)]) ,,
   (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
               memory :> bytes(scratch,4 * LENGTH ms);
               memory :> bytes(word_sub stackpointer (word 48),48)]) =
   (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
    MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
               memory :> bytes(scratch,4 * LENGTH ms);
               memory :> bytes(word_sub stackpointer (word 48),48)])`,
  MAYCHANGE_IDEMPOT_TAC);;


let FLAT_FIRE_GUARDS_NONZERO_WIDE =
  GEN_ALL(REWRITE_RULE[SOME_FLAGS] FLAT_FIRE_GUARDS_NONZERO);;
let FLAT_FIRE_GUARDS_ZERO_WIDE =
  GEN_ALL(REWRITE_RULE[SOME_FLAGS] FLAT_FIRE_GUARDS_ZERO);;
let FLAT_FIRE_MAKE_NONZERO_WIDE =
  let br = REWRITE_RULE[SOME_FLAGS] (SPEC_ALL FLAT_FIRE_MAKE_NONZERO) in
  GEN_ALL(DISCH (lhand(concl br))
    (MATCH_MP ENSURES_FRAME_SUBSUMED
      (CONJ FLAT_MAKE_FRAME_SUBSUMED (UNDISCH br))));;
let FLAT_FIRE_MAKE_ZERO_WIDE =
  let br = REWRITE_RULE[SOME_FLAGS] (SPEC_ALL FLAT_FIRE_MAKE_ZERO) in
  GEN_ALL(DISCH (lhand(concl br))
    (MATCH_MP ENSURES_FRAME_SUBSUMED
      (CONJ FLAT_MAKE_FRAME_SUBSUMED (UNDISCH br))));;
let FLAT_FIRE_ACCEPT_RETURN_WIDE =
  GEN_ALL(MATCH_MP ENSURES_FRAME_SUBSUMED
    (CONJ FLAT_RETURN_FRAME_SUBSUMED
      (REWRITE_RULE[SOME_FLAGS] (SPEC_ALL FLAT_FIRE_ACCEPT_RETURN))));;
let FLAT_FIRE_REFUSE_RETURN_WIDE =
  let br = REWRITE_RULE[SOME_FLAGS] (SPEC_ALL FLAT_FIRE_REFUSE_RETURN) in
  GEN_ALL(DISCH (lhand(concl br))
    (MATCH_MP ENSURES_FRAME_SUBSUMED
      (CONJ FLAT_RETURN_FRAME_SUBSUMED (UNDISCH br))));;


let FLAT_FIRE_GUARDS_ANY = prove
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
      (\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                    stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
                    init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
                  memory :> bytes(scratch,4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `gs = ([]:int32 list)` THENL
   [MATCH_MP_TAC FLAT_FIRE_GUARDS_ZERO_WIDE THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC FLAT_FIRE_GUARDS_NONZERO_WIDE THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM LENGTH_EQ_NIL]) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]);;

let FLAT_FIRE_MAKE_ANY = prove
 (`!fields rows guards make dest scratch (fs:int32 list) (rs:int32 list)
    (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
    pc stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
    init_r15.
    flat_valid fs rs gs ms /\ flat_guards_hold fs rs gs /\
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
      (\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                    stackpointer returnaddress init_rbp init_rbx init_r12
                    init_r13 init_r14 init_r15 s)
      (\s. flat_make_done pc dest scratch (flat_selected fs rs ms) ds
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH ms);
                  memory :> bytes(scratch,4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `ms = ([]:int32 list)` THENL
   [MATCH_MP_TAC FLAT_FIRE_MAKE_ZERO_WIDE THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC FLAT_FIRE_MAKE_NONZERO_WIDE THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM LENGTH_EQ_NIL]) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]);;

let FLAT_FIRE_DEST_ANY = prove
 (`!dest scratch (os:int32 list) (ds:int32 list) pc stackpointer returnaddress
    init_rbp init_rbx init_r12 init_r13 init_r14 init_r15.
    LENGTH ds = LENGTH os /\ LENGTH os < 2 EXP 58 /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc); (word_sub stackpointer (word 48),56)]
      [(dest,4 * LENGTH os); (scratch,4 * LENGTH os)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub stackpointer (word 48),56) /\
    nonoverlapping (scratch,4 * LENGTH os) (dest,4 * LENGTH os)
    ==> ensures x86
      (\s. flat_make_done pc dest scratch os ds
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (\s. flat_dest_done pc dest scratch os
                        stackpointer returnaddress init_rbp init_rbx init_r12
                        init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R10; R11; R12; R13; R14; R15] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH os);
                  memory :> bytes(scratch,4 * LENGTH os);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `os = ([]:int32 list)` THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `(MAYCHANGE [RIP; RAX; R10] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH (os:int32 list))])` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS] FLAT_FIRE_DEST_ZERO) THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `(MAYCHANGE [RIP; RAX; R10] ,,
       MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dest,4 * LENGTH (os:int32 list))])` THEN
    CONJ_TAC THENL
     [SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS] FLAT_FIRE_DEST_NONZERO) THEN
      REPEAT CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[GSYM LENGTH_EQ_NIL]) THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]]);;

let FLAT_FIRE_MAKE_ANY_MAP =
  GEN_ALL(REWRITE_RULE[flat_selected; LENGTH_MAP] (SPEC_ALL FLAT_FIRE_MAKE_ANY));;
let FLAT_FIRE_DEST_ANY_MAP =
  GEN_ALL(REWRITE_RULE[LENGTH_MAP]
    (SPECL [`dest:int64`; `scratch:int64`;
            `MAP (flat_field fs rs) (ms:int32 list)`] FLAT_FIRE_DEST_ANY));;


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
  ASM_CASES_TAC `flat_guards_hold fs rs gs` THENL
   [ASM_REWRITE_TAC[flat_selected; BITVAL_CLAUSES] THEN
    SUBGOAL_THEN
     `ALLPAIRS nonoverlapping
        [(word pc,LENGTH flat_fire_mc);
         (word_sub (stackpointer:int64) (word 48),56)]
        [((dest:int64),4 * LENGTH (ms:int32 list));
         ((scratch:int64),4 * LENGTH ms)] /\
      nonoverlapping (scratch,4 * LENGTH ms) (dest,4 * LENGTH ms)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES]) THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC `(\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                              stackpointer returnaddress init_rbp init_rbx init_r12
                              init_r13 init_r14 init_r15 s)` THEN
    CONJ_TAC THENL [MATCH_ACCEPT_TAC FLAT_FULL_FRAME_IDEMPOT; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FLAT_FIRE_GUARDS_ANY THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
      EXISTS_TAC `(\s. flat_make_done pc dest scratch (MAP (flat_field fs rs) ms) ds
                                    stackpointer returnaddress init_rbp init_rbx
                                    init_r12 init_r13 init_r14 init_r15 s)` THEN
      CONJ_TAC THENL [MATCH_ACCEPT_TAC FLAT_FULL_FRAME_IDEMPOT; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FLAT_FIRE_MAKE_ANY_MAP THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
        EXISTS_TAC `(\s. flat_dest_done pc dest scratch (MAP (flat_field fs rs) ms)
                                      stackpointer returnaddress init_rbp init_rbx
                                      init_r12 init_r13 init_r14 init_r15 s)` THEN
        CONJ_TAC THENL [MATCH_ACCEPT_TAC FLAT_FULL_FRAME_IDEMPOT; ALL_TAC] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC FLAT_FIRE_DEST_ANY_MAP THEN ASM_REWRITE_TAC[];
          MATCH_ACCEPT_TAC
           (SPECL [`pc:num`; `MAP (flat_field fs rs) (ms:int32 list)`;
                   `returnaddress:int64`; `init_rbp:int64`; `init_rbx:int64`;
                   `init_r12:int64`; `init_r13:int64`; `init_r14:int64`;
                   `init_r15:int64`; `dest:int64`; `scratch:int64`;
                   `ms:int32 list`; `stackpointer:int64`]
            FLAT_FIRE_ACCEPT_RETURN_WIDE)]]];
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC `(\s. flat_mid pc fields rows guards make dest scratch fs rs gs ms ds zs
                              stackpointer returnaddress init_rbp init_rbx init_r12
                              init_r13 init_r14 init_r15 s)` THEN
    CONJ_TAC THENL [MATCH_ACCEPT_TAC FLAT_FULL_FRAME_IDEMPOT; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FLAT_FIRE_GUARDS_ANY THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC
       (SPECL [`pc:num`; `fields:int64`; `rows:int64`; `guards:int64`;
               `make:int64`; `fs:int32 list`; `rs:int32 list`; `gs:int32 list`;
               `ds:int32 list`; `zs:int32 list`; `returnaddress:int64`;
               `init_rbp:int64`; `init_rbx:int64`; `init_r12:int64`;
               `init_r13:int64`; `init_r14:int64`; `init_r15:int64`;
               `dest:int64`; `scratch:int64`; `ms:int32 list`;
               `stackpointer:int64`] FLAT_FIRE_REFUSE_RETURN_WIDE) THEN
      ASM_REWRITE_TAC[]]]);;
