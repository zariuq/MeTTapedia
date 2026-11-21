(* ========================================================================= *)
(* The compiled leaf of Micromath's substitute1 rule, proved on the x86-64    *)
(* model of s2n-bignum. The bytes are those of mm_sub1_leaf.o, which the     *)
(* compiler emits from the theory and Cesta exports; the gate checks that    *)
(* the linked program carries them unchanged.                                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(* The runner binds mm_sub1_leaf_object to the path of mm_sub1_leaf.o; the byte
   list below is checked against that object.                                *)

let mm_sub1_leaf_mc =
  define_assert_from_elf "mm_sub1_leaf_mc" mm_sub1_leaf_object
[
  0xf3; 0x0f; 0x1e; 0xfa;                   (* endbr64 *)
  0x55;                                     (* push %rbp *)
  0x48; 0x8d; 0x47; 0x10;                   (* lea 0x10(%rdi),%rax *)
  0x53;                                     (* push %rbx *)
  0x4c; 0x8b; 0x17;                         (* mov (%rdi),%r10 *)
  0x48; 0x89; 0xd3;                         (* mov %rdx,%rbx *)
  0x48; 0x89; 0xca;                         (* mov %rcx,%rdx *)
  0x4c; 0x8b; 0x5f; 0x08;                   (* mov 0x8(%rdi),%r11 *)
  0x48; 0x89; 0xf7;                         (* mov %rsi,%rdi *)
  0x48; 0xc1; 0xe7; 0x05;                   (* shl $0x5,%rdi *)
  0x4c; 0x01; 0xd7;                         (* add %r10,%rdi *)
  0x4c; 0x39; 0xde;                         (* cmp %r11,%rsi *)
  0x48; 0x89; 0xde;                         (* mov %rbx,%rsi *)
  0x48; 0x0f; 0x43; 0xf8;                   (* cmovae %rax,%rdi *)
  0x48; 0xc1; 0xe6; 0x05;                   (* shl $0x5,%rsi *)
  0x4c; 0x01; 0xd6;                         (* add %r10,%rsi *)
  0x4c; 0x39; 0xdb;                         (* cmp %r11,%rbx *)
  0x48; 0x0f; 0x43; 0xf0;                   (* cmovae %rax,%rsi *)
  0x48; 0xc1; 0xe1; 0x05;                   (* shl $0x5,%rcx *)
  0x4c; 0x01; 0xd1;                         (* add %r10,%rcx *)
  0x4c; 0x39; 0xda;                         (* cmp %r11,%rdx *)
  0x4c; 0x89; 0xc2;                         (* mov %r8,%rdx *)
  0x48; 0x0f; 0x43; 0xc8;                   (* cmovae %rax,%rcx *)
  0x48; 0xc1; 0xe2; 0x05;                   (* shl $0x5,%rdx *)
  0x48; 0x8b; 0x5e; 0x18;                   (* mov 0x18(%rsi),%rbx *)
  0x4c; 0x01; 0xd2;                         (* add %r10,%rdx *)
  0x4d; 0x39; 0xd8;                         (* cmp %r11,%r8 *)
  0x4c; 0x8b; 0x46; 0x10;                   (* mov 0x10(%rsi),%r8 *)
  0x48; 0x0f; 0x42; 0xc2;                   (* cmovb %rdx,%rax *)
  0x48; 0x8b; 0x57; 0x18;                   (* mov 0x18(%rdi),%rdx *)
  0x48; 0x39; 0x51; 0x08;                   (* cmp %rdx,0x8(%rcx) *)
  0x0f; 0x95; 0xc2;                         (* setne %dl *)
  0x4c; 0x39; 0x41; 0x10;                   (* cmp %r8,0x10(%rcx) *)
  0x40; 0x0f; 0x95; 0xc5;                   (* setne %bpl *)
  0x09; 0xea;                               (* or %ebp,%edx *)
  0x48; 0x8b; 0x6f; 0x10;                   (* mov 0x10(%rdi),%rbp *)
  0x48; 0x39; 0x6e; 0x08;                   (* cmp %rbp,0x8(%rsi) *)
  0x40; 0x0f; 0x95; 0xc5;                   (* setne %bpl *)
  0x09; 0xea;                               (* or %ebp,%edx *)
  0x48; 0x39; 0x59; 0x18;                   (* cmp %rbx,0x18(%rcx) *)
  0x40; 0x0f; 0x95; 0xc5;                   (* setne %bpl *)
  0x09; 0xea;                               (* or %ebp,%edx *)
  0x48; 0x8b; 0x2f;                         (* mov (%rdi),%rbp *)
  0x48; 0x39; 0x68; 0x08;                   (* cmp %rbp,0x8(%rax) *)
  0x40; 0x0f; 0x95; 0xc5;                   (* setne %bpl *)
  0x09; 0xea;                               (* or %ebp,%edx *)
  0x4c; 0x39; 0x40; 0x10;                   (* cmp %r8,0x10(%rax) *)
  0x41; 0x0f; 0x95; 0xc0;                   (* setne %r8b *)
  0x44; 0x08; 0xc2;                         (* or %r8b,%dl *)
  0x75; 0x3f;                               (* jne e6 <mm_sub1_leaf+0xe6> *)
  0x48; 0x39; 0x58; 0x18;                   (* cmp %rbx,0x18(%rax) *)
  0x75; 0x39;                               (* jne e6 <mm_sub1_leaf+0xe6> *)
  0xba; 0x02; 0x00; 0x00; 0x00;             (* mov $0x2,%edx *)
  0x4d; 0x39; 0xd9;                         (* cmp %r11,%r9 *)
  0x73; 0x29;                               (* jae e0 <mm_sub1_leaf+0xe0> *)
  0x4c; 0x8b; 0x00;                         (* mov (%rax),%r8 *)
  0x48; 0x8b; 0x7f; 0x08;                   (* mov 0x8(%rdi),%rdi *)
  0x49; 0xc1; 0xe1; 0x05;                   (* shl $0x5,%r9 *)
  0x48; 0x8b; 0x01;                         (* mov (%rcx),%rax *)
  0x48; 0x8b; 0x16;                         (* mov (%rsi),%rdx *)
  0x4f; 0x89; 0x04; 0x0a;                   (* mov %r8,(%r10,%r9,1) *)
  0x4b; 0x89; 0x7c; 0x0a; 0x08;             (* mov %rdi,0x8(%r10,%r9,1) *)
  0x4b; 0x89; 0x44; 0x0a; 0x18;             (* mov %rax,0x18(%r10,%r9,1) *)
  0x4b; 0x89; 0x54; 0x0a; 0x10;             (* mov %rdx,0x10(%r10,%r9,1) *)
  0xba; 0x01; 0x00; 0x00; 0x00;             (* mov $0x1,%edx *)
  0x48; 0x89; 0xd0;                         (* mov %rdx,%rax *)
  0x5b;                                     (* pop %rbx *)
  0x5d;                                     (* pop %rbp *)
  0xc3;                                     (* ret *)
  0x31; 0xd2;                               (* xor %edx,%edx *)
  0x5b;                                     (* pop %rbx *)
  0x5d;                                     (* pop %rbp *)
  0x48; 0x89; 0xd0;                         (* mov %rdx,%rax *)
  0xc3                                      (* ret *)
];;

let MM_SUB1_LEAF_EXEC = X86_MK_EXEC_RULE mm_sub1_leaf_mc;;

(* The body premise k is read from: its slot when inside the table, otherwise
   the table's unset body, stored at offset 16 of the table record.          *)
let mm_ref = new_definition
 `mm_ref (t:int64) (sl:int64) n (k:int64) =
    if val k < n then word_add sl (word (32 * val k)) else word_add t (word 16)`;;

(* ------------------------------------------------------------------------- *)
(* Rewriting lemmas the simulation needs.                                     *)
(* ------------------------------------------------------------------------- *)

(* The selected premise address, as the code computes it, is mm_ref.        *)
let MM_REF_SELECT = prove
 (`!t sl n (k:int64).
     n < 2 EXP 64
     ==> (if val (word n:int64) <= val k then word_add t (word 16)
          else word_add (word_shl k 5) sl) = mm_ref t sl n k /\
         (if val k < val (word n:int64) then word_add (word_shl k 5) sl
          else word_add t (word 16)) = mm_ref t sl n k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[mm_ref; VAL_WORD_EQ; DIMINDEX_64; GSYM NOT_LT] THEN
  REWRITE_TAC[word_shl] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

(* A byte read of a wider register.                                          *)
let MM_BYTE_OF_MOD = prove
 (`!x:N word. (word (val x MOD 256):byte) = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[word_zx] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM WORD_MOD_SIZE] THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV);;

let MM_SHL5 = prove
 (`!x:int64. word_shl x 5 = word (32 * val x)`,
  REWRITE_TAC[word_shl] THEN CONV_TAC WORD_RULE);;

(* The stack pointer through the two pops and the return.                    *)
let MM_STACK1 = prove
 (`!sp:int64. word_add (word_sub (word_sub sp (word 8)) (word 8)) (word 8) =
              word_sub sp (word 8)`,
  CONV_TAC WORD_RULE);;

let MM_STACK2 = prove
 (`!sp:int64. word_add (word_sub sp (word 8)) (word 8) = sp`,
  CONV_TAC WORD_RULE);;

(* The two saved registers as offsets from the bottom of the frame.         *)
let MM_STACK3 = prove
 (`word_sub (word_sub stackpointer (word 8)) (word 8):int64 =
   word_sub stackpointer (word 16)`,
  CONV_TAC WORD_RULE);;

let MM_STACK4 = prove
 (`word_sub stackpointer (word 8):int64 =
   word_add (word_sub stackpointer (word 16)) (word 8)`,
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Tactics shared by the two theorems.                                        *)
(* ------------------------------------------------------------------------- *)

(* The premise addresses are kept as equations mm_ref ... = a_i, so that the
   simulator's own rewriting turns a selected address into its name.        *)
let MM_FLIP_REFS_TAC =
  RULE_ASSUM_TAC (fun th ->
    let c = concl th in
    if is_eq c && is_var(lhs c) && mem (fst(dest_var(lhs c))) ["a0";"a1";"a2";"a3"]
    then GSYM th else th);;

(* After a select, the register holds the premise's name.                   *)
let MM_RENAME_TAC =
  let pat = `read (r:(x86state,int64)component) (s:x86state)` in
  fun g ->
    let ths = MATCH_MP MM_REF_SELECT (ASSUME `n < 2 EXP 64`) ::
              map ASSUME [`mm_ref t sl n k0 = a0`; `mm_ref t sl n k1 = a1`;
                          `mm_ref t sl n k2 = a2`; `mm_ref t sl n k3 = a3`] in
    RULE_ASSUM_TAC (fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] pat) (lhs c) then REWRITE_RULE ths th else th) g;;

let MM_POP_TAC n =
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC [n] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MM_STACK1; MM_STACK2]);;

let MM_FRAME_TAC =
  RULE_ASSUM_TAC (fun th -> if maychange_term (concl th)
    then REWRITE_RULE[MM_STACK4] (REWRITE_RULE[MM_STACK3] th) else th) THEN
  MONOTONE_MAYCHANGE_TAC;;

let MM_G6 = `(f2:int64) = y0 /\ (x2:int64) = x1 /\ (f1:int64) = x0 /\
             (y2:int64) = y1 /\ (f3:int64) = o0 /\ (x3:int64) = x1`;;
let MM_ZF6 = mk_iff(`read ZF s49`, MM_G6);;
let MM_G7 = `(f1:int64) = x0 /\ (f2:int64) = y0 /\ (x2:int64) = x1 /\ (y2:int64) = y1 /\
             (f3:int64) = o0 /\ (x3:int64) = x1 /\ (y3:int64) = y1`;;

(* Entry to the first branch: the premises selected, the first six guards
   computed into ZF.                                                         *)
let MM_PREFIX_TAC =
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; fst MM_SUB1_LEAF_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MM_FLIP_REFS_TAC THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
            (dest_list `[RBX; RBP]`) THEN
  SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP 58` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC (1--18) THEN MM_RENAME_TAC THEN
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC (19--23) THEN MM_RENAME_TAC THEN
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC (24--29) THEN MM_RENAME_TAC THEN
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC (30--49) THEN
  SUBGOAL_THEN MM_ZF6 MP_TAC THENL
   [ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; MM_BYTE_OF_MOD] THEN
    MAP_EVERY ASM_CASES_TAC
      [`f2:int64 = y0`; `x2:int64 = x1`; `f1:int64 = x0`; `y2:int64 = y1`;
       `f3:int64 = o0`; `x3:int64 = x1`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST;
    DISCARD_MATCHING_ASSUMPTIONS [`read ZF s <=> y`] THEN DISCH_TAC];;

(* The refusing exit at offset 0xe6: xor edx,edx; pop rbx; pop rbp;
   mov rax,rdx; ret.                                                         *)
let MM_RET0_TAC n0 =
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC [n0] THEN
  MM_POP_TAC (n0+1) THEN MM_POP_TAC (n0+2) THEN
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC [n0+3] THEN MM_POP_TAC (n0+4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN MM_FRAME_TAC;;

(* The refusing paths: a first-six guard fails (jump at state 50), or the
   seventh does (jump at state 52).                                          *)
let MM_REFUSE6_TAC =
  SUBGOAL_THEN `~read ZF s49` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME MM_ZF6] THEN ASM_REWRITE_TAC[];
    DISCARD_MATCHING_ASSUMPTIONS [`read ZF s <=> y`]] THEN
  SUBGOAL_THEN (mk_neg MM_G7) ASSUME_TAC THENL
   [UNDISCH_TAC (mk_neg MM_G6) THEN CONV_TAC TAUT; ALL_TAC] THEN
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC [50] THEN MM_RET0_TAC 51;;

let MM_PASS6_TAC =
  SUBGOAL_THEN `read ZF s49` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME MM_ZF6] THEN ASM_REWRITE_TAC[];
    DISCARD_MATCHING_ASSUMPTIONS [`read ZF s <=> y`]] THEN
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC (50--51) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_EQ_0; WORD_SUB_EQ_0]);;

let MM_REFUSE7_TAC =
  SUBGOAL_THEN `~read ZF s51` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; DISCARD_MATCHING_ASSUMPTIONS [`read ZF s <=> y`]] THEN
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC [52] THEN MM_RET0_TAC 53;;

(* All seven guards hold: through the destination check at state 55.        *)
let MM_PASS7_TAC =
  SUBGOAL_THEN `read ZF s51` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; DISCARD_MATCHING_ASSUMPTIONS [`read ZF s <=> y`]] THEN
  X86_STEPS_TAC MM_SUB1_LEAF_EXEC (52--54) THEN
  SUBGOAL_THEN `val (word n:int64) = n` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The destination inside the table: on a firing the slot is written.        *)
(* ------------------------------------------------------------------------- *)

let MM_SUB1_LEAF_INSIDE = prove
 (`!t sl n k0 k1 k2 k3 dest a0 a1 a2 a3
    o0 f0 x0 y0 o1 f1 x1 y1 o2 f2 x2 y2 o3 f3 x3 y3 pc stackpointer returnaddress.
     n < 2 EXP 58 /\ val dest < n /\
     a0 = mm_ref t sl n k0 /\ a1 = mm_ref t sl n k1 /\
     a2 = mm_ref t sl n k2 /\ a3 = mm_ref t sl n k3 /\
     ALLPAIRS nonoverlapping
       [(word_sub stackpointer (word 16),24)]
       [(word pc,LENGTH mm_sub1_leaf_mc); (t,16); (a0,32); (a1,32); (a2,32); (a3,32);
        (word_add sl (word (32 * val dest)),32)] /\
     nonoverlapping (word pc,LENGTH mm_sub1_leaf_mc) (word_add sl (word (32 * val dest)),32)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mm_sub1_leaf_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [t; k0; k1; k2; k3; dest] s /\
               read (memory :> bytes64 t) s = sl /\
               read (memory :> bytes64 (word_add t (word 8))) s = word n /\
               read (memory :> bytes64 a0) s = o0 /\
               read (memory :> bytes64 (word_add a0 (word 8))) s = f0 /\
               read (memory :> bytes64 (word_add a0 (word 16))) s = x0 /\
               read (memory :> bytes64 (word_add a0 (word 24))) s = y0 /\
               read (memory :> bytes64 a1) s = o1 /\
               read (memory :> bytes64 (word_add a1 (word 8))) s = f1 /\
               read (memory :> bytes64 (word_add a1 (word 16))) s = x1 /\
               read (memory :> bytes64 (word_add a1 (word 24))) s = y1 /\
               read (memory :> bytes64 a2) s = o2 /\
               read (memory :> bytes64 (word_add a2 (word 8))) s = f2 /\
               read (memory :> bytes64 (word_add a2 (word 16))) s = x2 /\
               read (memory :> bytes64 (word_add a2 (word 24))) s = y2 /\
               read (memory :> bytes64 a3) s = o3 /\
               read (memory :> bytes64 (word_add a3 (word 8))) s = f3 /\
               read (memory :> bytes64 (word_add a3 (word 16))) s = x3 /\
               read (memory :> bytes64 (word_add a3 (word 24))) s = y3)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = (if f1 = x0 /\ f2 = y0 /\ x2 = x1 /\ y2 = y1 /\ f3 = o0 /\ x3 = x1 /\ y3 = y1 then word 1 else word 0) /\
               (f1 = x0 /\ f2 = y0 /\ x2 = x1 /\ y2 = y1 /\ f3 = o0 /\ x3 = x1 /\ y3 = y1
                ==> read (memory :> bytes64 (word_add sl (word (32 * val dest)))) s = o3 /\
                    read (memory :> bytes64 (word_add sl (word (32 * val dest + 8)))) s = f0 /\
                    read (memory :> bytes64 (word_add sl (word (32 * val dest + 16)))) s = o1 /\
                    read (memory :> bytes64 (word_add sl (word (32 * val dest + 24)))) s = o2))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_add sl (word (32 * val dest)),32);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MM_PREFIX_TAC THEN ASM_CASES_TAC MM_G6 THENL
   [MM_PASS6_TAC THEN ASM_CASES_TAC `(y3:int64) = y1` THENL
     [MM_PASS7_TAC THEN
      X86_STEPS_TAC MM_SUB1_LEAF_EXEC (55--58) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MM_SHL5]) THEN
      X86_STEPS_TAC MM_SUB1_LEAF_EXEC (59--66) THEN
      MM_POP_TAC 67 THEN MM_POP_TAC 68 THEN MM_POP_TAC 69 THEN
      SUBGOAL_THEN `val (word (32 * val (dest:int64)):int64) = 32 * val dest`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; MULT_CLAUSES])) THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `val (dest:int64) < n` THEN UNDISCH_TAC `n < 2 EXP 58` THEN ARITH_TAC;
        ALL_TAC] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN MM_FRAME_TAC;
      MM_REFUSE7_TAC];
    MM_REFUSE6_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The destination past the table: nothing but the stack frame is written.   *)
(* ------------------------------------------------------------------------- *)

let MM_SUB1_LEAF_OUTSIDE = prove
 (`!t sl n k0 k1 k2 k3 dest a0 a1 a2 a3
    o0 f0 x0 y0 o1 f1 x1 y1 o2 f2 x2 y2 o3 f3 x3 y3 pc stackpointer returnaddress.
     n < 2 EXP 58 /\ n <= val dest /\
     a0 = mm_ref t sl n k0 /\ a1 = mm_ref t sl n k1 /\
     a2 = mm_ref t sl n k2 /\ a3 = mm_ref t sl n k3 /\
     ALLPAIRS nonoverlapping
       [(word_sub stackpointer (word 16),24)]
       [(word pc,LENGTH mm_sub1_leaf_mc); (t,16); (a0,32); (a1,32); (a2,32); (a3,32)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mm_sub1_leaf_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [t; k0; k1; k2; k3; dest] s /\
               read (memory :> bytes64 t) s = sl /\
               read (memory :> bytes64 (word_add t (word 8))) s = word n /\
               read (memory :> bytes64 a0) s = o0 /\
               read (memory :> bytes64 (word_add a0 (word 8))) s = f0 /\
               read (memory :> bytes64 (word_add a0 (word 16))) s = x0 /\
               read (memory :> bytes64 (word_add a0 (word 24))) s = y0 /\
               read (memory :> bytes64 a1) s = o1 /\
               read (memory :> bytes64 (word_add a1 (word 8))) s = f1 /\
               read (memory :> bytes64 (word_add a1 (word 16))) s = x1 /\
               read (memory :> bytes64 (word_add a1 (word 24))) s = y1 /\
               read (memory :> bytes64 a2) s = o2 /\
               read (memory :> bytes64 (word_add a2 (word 8))) s = f2 /\
               read (memory :> bytes64 (word_add a2 (word 16))) s = x2 /\
               read (memory :> bytes64 (word_add a2 (word 24))) s = y2 /\
               read (memory :> bytes64 a3) s = o3 /\
               read (memory :> bytes64 (word_add a3 (word 8))) s = f3 /\
               read (memory :> bytes64 (word_add a3 (word 16))) s = x3 /\
               read (memory :> bytes64 (word_add a3 (word 24))) s = y3)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = (if f1 = x0 /\ f2 = y0 /\ x2 = x1 /\ y2 = y1 /\ f3 = o0 /\ x3 = x1 /\ y3 = y1 then word 2 else word 0))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MM_PREFIX_TAC THEN ASM_CASES_TAC MM_G6 THENL
   [MM_PASS6_TAC THEN ASM_CASES_TAC `(y3:int64) = y1` THENL
     [MM_PASS7_TAC THEN
      SUBGOAL_THEN `~(val (dest:int64) < n)` ASSUME_TAC THENL
       [UNDISCH_TAC `n <= val (dest:int64)` THEN ARITH_TAC; ALL_TAC] THEN
      X86_STEPS_TAC MM_SUB1_LEAF_EXEC [55] THEN
      X86_STEPS_TAC MM_SUB1_LEAF_EXEC [56] THEN
      MM_POP_TAC 57 THEN MM_POP_TAC 58 THEN MM_POP_TAC 59 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN MM_FRAME_TAC;
      MM_REFUSE7_TAC];
    MM_REFUSE6_TAC]);;
