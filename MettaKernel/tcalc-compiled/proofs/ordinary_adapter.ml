(* Ordinary-row packing adapter, proved from its linked x86-64 bytes. *)

let ordinary_flat_mc = define_from_elf "ordinary_flat_mc" ordinary_flat_object;;

let ORDINARY_FLAT_EXEC = X86_MK_EXEC_RULE ordinary_flat_mc;;

let ORDINARY_READ64 = prove
 (`!(ps:int64 list) (a:int64) (s:x86state) i.
      i < LENGTH ps /\ wordlist_from_memory(a,LENGTH ps) s = ps
      ==> read (memory :> bytes64 (word_add a (word (8 * i)))) s = EL i ps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `LENGTH(ps:int64 list)`; `i:num`; `s:x86state`]
                (INST_TYPE [`:8`,`:N`] EL_WORDLIST_FROM_MEMORY)) THEN
  ASM_REWRITE_TAC[BYTES64_WBYTES; DIMINDEX_8; EQ_SYM_EQ]);;

let ORDINARY_WORDLIST_FROM_MEMORY_64 = prove
 (`!a n s. wordlist_from_memory(a,n) s : int64 list =
           wordlist_of_num n (read (memory :> bytes(a,8 * n)) s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `s:x86state`]
                (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY)) THEN
  REWRITE_TAC[DIMINDEX_8]);;

let ORDINARY_FIRST_NULL = prove
 (`!ptrs:int64 list. ~(ALL (\(p:int64). ~(p = word 0)) ptrs)
      ==> ?k. k < LENGTH ptrs /\
              (!i. i < k ==> ~(EL i ptrs = word 0)) /\ EL k ptrs = word 0`,
  GEN_TAC THEN REWRITE_TAC[NOT_ALL; GSYM EX_MEM; MEM_EXISTS_EL] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:int64` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?k. k < LENGTH(ptrs:int64 list) /\ EL k ptrs = word 0`
   (fun h -> MP_TAC(ONCE_REWRITE_RULE[num_WOP] h)) THENL
   [EXISTS_TAC `n:num` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let ORDINARY_ORTHOGONAL_BYTES = prove
 (`!(a:int64) k b j.
      nonoverlapping (a,k) (b,j)
      ==> orthogonal_components (memory :> bytes(a,k)) (memory :> bytes(b,j))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN
  CONJ_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV;
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; GSYM nonoverlapping] THEN
    ASM_REWRITE_TAC[]]);;

let ORDINARY_ORTHOGONAL_BYTES64 = prove
 (`!(a:int64) k b.
      nonoverlapping (a,k) (b,8)
      ==> orthogonal_components (memory :> bytes(a,k)) (memory :> bytes64 b)`,
  REWRITE_TAC[bytes64; COMPONENT_COMPOSE_ASSOC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_RIGHT THEN
  MATCH_MP_TAC ORDINARY_ORTHOGONAL_BYTES THEN ASM_REWRITE_TAC[]);;

let ORDINARY_SINGLE_ROW_UPDATE = prove
 (`!(a:int64) (rs:int32 list) (s:x86state) (t:x86state).
    LENGTH rs = 1 /\
    (wordlist_from_memory(a,0) s : int32 list) = flat_prefix 0 rs /\
    (wordlist_from_memory(a,0) t : int32 list) = wordlist_from_memory(a,0) s /\
    read (memory :> bytes32 (word_add a (word (4 * 0)))) t = EL 0 rs
    ==> wordlist_from_memory(a,LENGTH rs) t = rs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `0`; `rs:int32 list`; `s:x86state`; `t:x86state`]
                FLAT_WORDLIST_PREFIX_32) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[ADD1; ADD_CLAUSES] THEN ASM_MESON_TAC[FLAT_PREFIX_ALL]]);;

let ORDINARY_ORTHOGONAL_COMPONENTS_SYM = prove
 (`!c:(x86state,A)component d:(x86state,B)component.
      orthogonal_components c d ==> orthogonal_components d c`,
  REWRITE_TAC[orthogonal_components] THEN MESON_TAC[]);;

let ORDINARY_READ_OVER_WRITE_ORTHOGONAL_TAC =
  let tac_orth = (MATCH_MP_TAC o prove)
   (`orthogonal_components (c:(x86state,A)component) (d:(x86state,B)component) /\
     read c (s':x86state) = read c s
     ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]) in
  let rec tac g =
   (REFL_TAC ORELSE
    (tac_orth THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC ORELSE
      (MATCH_MP_TAC ORDINARY_ORTHOGONAL_COMPONENTS_SYM THEN
       FIRST_ASSUM ACCEPT_TAC) ORELSE ORTHOGONAL_COMPONENTS_TAC ORELSE
      (MATCH_MP_TAC ORDINARY_ORTHOGONAL_BYTES THEN NONOVERLAPPING_TAC); tac])) g in
  tac;;

let ordinary_adapter_call = new_definition
 `ordinary_adapter_call pc premises guards make workspace
      (fs:int32 list) (rs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) nc stackpointer
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read RIP s = word (pc + 0x1f8) /\
    read RDI s = workspace /\ read RSI s = word_add workspace (word 512) /\
    read RDX s = guards /\ read RCX s = word (LENGTH gs) /\
    read R8 s = make /\ read R9 s = word (LENGTH ms) /\
    read R12 s = premises /\ read R14 s = word (LENGTH ms) /\
    read RBP s = word (LENGTH gs) /\ read RBX s = word nc /\
    read R13 s = init_r13 /\ read R15 s = init_r15 /\
    read RSP s = word_sub stackpointer (word 56) /\
    read (memory :> bytes64
      (word_add (word_sub stackpointer (word 64)) (word 8))) s =
      word_add workspace (word 612) /\
    read (memory :> bytes64
      (word_add (word_sub stackpointer (word 64)) (word 16))) s =
      word_add workspace (word 740) /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) s = init_r14 /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s = init_r12 /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s = init_rbp /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s = init_rbx /\
    wordlist_from_memory(workspace,LENGTH fs) s = fs /\
    wordlist_from_memory(word_add workspace (word 512),LENGTH rs) s = rs /\
    wordlist_from_memory(guards,LENGTH gs) s = gs /\
    wordlist_from_memory(make,LENGTH ms) s = ms /\
    wordlist_from_memory(word_add workspace (word 612),LENGTH ms) s = ds /\
    wordlist_from_memory(word_add workspace (word 740),LENGTH ms) s = zs`;;

let ordinary_adapter_leaf_state = new_definition
 `ordinary_adapter_leaf_state pc premises guards make workspace
      (fs:int32 list) (rs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) nc stackpointer returnvalue
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read RIP s = word (pc + 0x1fd) /\
    read RSP s = word_sub stackpointer (word 56) /\
    C_RETURN s = word returnvalue /\
    read RDI s = workspace /\ read RSI s = word_add workspace (word 512) /\
    read RDX s = guards /\ read RCX s = word (LENGTH gs) /\
    read R8 s = make /\ read R9 s = word (LENGTH ms) /\
    read R12 s = premises /\ read R14 s = word (LENGTH ms) /\
    read RBP s = word (LENGTH gs) /\ read RBX s = word nc /\
    read R13 s = init_r13 /\ read R15 s = init_r15 /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) s = init_r14 /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s = init_r12 /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s = init_rbp /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s = init_rbx /\
    wordlist_from_memory(workspace,LENGTH fs) s = fs /\
    wordlist_from_memory(word_add workspace (word 512),LENGTH rs) s = rs /\
    wordlist_from_memory(word_add workspace (word 612),LENGTH ds) s = ds /\
    wordlist_from_memory(word_add workspace (word 740),LENGTH zs) s = zs`;;

let ordinary_adapter_return = new_definition
 `ordinary_adapter_return workspace (fs:int32 list) (rs:int32 list)
      (ds:int32 list) (zs:int32 list) returnvalue stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    read RIP s = returnaddress /\
    read RSP s = word_add stackpointer (word 8) /\
    C_RETURN s = word returnvalue /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15 /\
    wordlist_from_memory(workspace,LENGTH fs) s = fs /\
    wordlist_from_memory(word_add workspace (word 512),LENGTH rs) s = rs /\
    wordlist_from_memory(word_add workspace (word 612),LENGTH ds) s = ds /\
    wordlist_from_memory(word_add workspace (word 740),LENGTH zs) s = zs`;;

let ordinary_adapter_status_return = new_definition
 `ordinary_adapter_status_return returnvalue stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    read RIP s = returnaddress /\
    read RSP s = word_add stackpointer (word 8) /\
    C_RETURN s = word returnvalue /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15`;;

let ordinary_adapter_shape_valid = new_definition
 `ordinary_adapter_shape_valid (call:int64) (premises:int64) (constants:int64)
      (guards:int64) (make:int64) (workspace:int64)
      (ptrs:int64 list) (cs:int32 list) (gs:int32 list) (ms:int32 list) <=>
    ~(call = word 0) /\ ~(workspace = word 0) /\
    LENGTH ptrs <= 24 /\ LENGTH cs <= 32 /\
    LENGTH gs <= 32 /\ LENGTH ms <= 32 /\
    (LENGTH ptrs = 0 \/ ~(premises = word 0)) /\
    (LENGTH cs = 0 \/ ~(constants = word 0)) /\
    (LENGTH gs = 0 \/ ~(guards = word 0)) /\
    (LENGTH ms = 0 \/ ~(make = word 0))`;;

let ordinary_machine_valid = new_definition
 `ordinary_machine_valid (call:int64) (premises:int64) (constants:int64)
      (guards:int64) (make:int64) (workspace:int64)
      (ptrs:int64 list) (cs:int32 list) (gs:int32 list) (ms:int32 list) <=>
    ~(call = word 0) /\ ~(workspace = word 0) /\
    LENGTH ptrs <= 24 /\ LENGTH cs <= 32 /\
    LENGTH gs <= 32 /\ LENGTH ms <= 32 /\
    (LENGTH ptrs = 0 \/ ~(premises = word 0)) /\
    (LENGTH cs = 0 \/ ~(constants = word 0)) /\
    (LENGTH gs = 0 \/ ~(guards = word 0)) /\
    (LENGTH ms = 0 \/ ~(make = word 0)) /\
    ALL (\(p:int64). ~(p = word 0)) ptrs`;;

let ordinary_adapter_entry = new_definition
 `ordinary_adapter_entry pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read RIP s = word (pc + 0xe0) /\
    read RDI s = call /\
    read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15 /\
    read (memory :> bytes64 call) s = premises /\
    read (memory :> bytes64 (word_add call (word 8))) s = constants /\
    read (memory :> bytes64 (word_add call (word 16))) s = guards /\
    read (memory :> bytes64 (word_add call (word 24))) s = make /\
    read (memory :> bytes64 (word_add call (word 32))) s = workspace /\
    read (memory :> bytes64 (word_add call (word 40))) s = word (LENGTH ptrs) /\
    read (memory :> bytes64 (word_add call (word 48))) s = word (LENGTH cs) /\
    read (memory :> bytes64 (word_add call (word 56))) s = word (LENGTH gs) /\
    read (memory :> bytes64 (word_add call (word 64))) s = word (LENGTH ms) /\
    LENGTH ps = LENGTH ptrs /\
    wordlist_from_memory(premises,LENGTH ptrs) s = ptrs /\
    (!i. i < LENGTH ps
         ==> wordlist_from_memory(EL i ptrs,4) s = EL i ps) /\
    wordlist_from_memory(constants,LENGTH cs) s = cs /\
    wordlist_from_memory(guards,LENGTH gs) s = gs /\
    wordlist_from_memory(make,LENGTH ms) s = ms /\
    wordlist_from_memory(word_add workspace (word 612),LENGTH ms) s = ds /\
    wordlist_from_memory(word_add workspace (word 740),LENGTH ms) s = zs`;;

let ordinary_adapter_sources = new_definition
 `ordinary_adapter_sources call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) s <=>
    read (memory :> bytes64 call) s = premises /\
    read (memory :> bytes64 (word_add call (word 8))) s = constants /\
    read (memory :> bytes64 (word_add call (word 16))) s = guards /\
    read (memory :> bytes64 (word_add call (word 24))) s = make /\
    read (memory :> bytes64 (word_add call (word 32))) s = workspace /\
    read (memory :> bytes64 (word_add call (word 40))) s = word (LENGTH ptrs) /\
    read (memory :> bytes64 (word_add call (word 48))) s = word (LENGTH cs) /\
    read (memory :> bytes64 (word_add call (word 56))) s = word (LENGTH gs) /\
    read (memory :> bytes64 (word_add call (word 64))) s = word (LENGTH ms) /\
    wordlist_from_memory(premises,LENGTH ptrs) s = ptrs /\
    (!i. i < LENGTH ps
         ==> wordlist_from_memory(EL i ptrs,4) s = EL i ps) /\
    wordlist_from_memory(constants,LENGTH cs) s = cs /\
    wordlist_from_memory(guards,LENGTH gs) s = gs /\
    wordlist_from_memory(make,LENGTH ms) s = ms`;;

let ordinary_pack_valid = new_definition
 `ordinary_pack_valid (ptrs:int64 list) (ps:(int32 list) list)
      (cs:int32 list) (fs:int32 list) (rs:int32 list) <=>
    LENGTH ps = LENGTH ptrs /\ ALL (\p. LENGTH p = 4) ps /\
    LENGTH fs = 4 * LENGTH ps + LENGTH cs /\
    LENGTH rs = LENGTH ps + 1 /\
    (!i j. i < LENGTH ps /\ j < 4
           ==> EL (4 * i + j) fs = EL j (EL i ps)) /\
    (!j. j < LENGTH cs ==> EL (4 * LENGTH ps + j) fs = EL j cs) /\
    (!i. i <= LENGTH ps ==> EL i rs = word (4 * i))`;;

let ordinary_adapter_exclusions = new_definition
 `ordinary_adapter_exclusions pc call premises constants guards make workspace
      (ptrs:int64 list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (fs:int32 list) (rs:int32 list) stackpointer <=>
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc);
       (word_sub (word_sub stackpointer (word 64)) (word 48),56)]
      [(workspace,4 * LENGTH fs);
       (word_add workspace (word 512),4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
       (word_add workspace (word 612),4 * LENGTH ms);
       (word_add workspace (word 740),4 * LENGTH ms)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub (word_sub stackpointer (word 64)) (word 48),56) /\
    ALL (nonoverlapping (word_add workspace (word 740),4 * LENGTH ms))
      [(workspace,4 * LENGTH fs);
       (word_add workspace (word 512),4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
       (word_add workspace (word 612),4 * LENGTH ms)] /\
    ALL (nonoverlapping (word_add workspace (word 612),4 * LENGTH ms))
      [(workspace,4 * LENGTH fs);
       (word_add workspace (word 512),4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms)] /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH ordinary_flat_mc);
       (word_sub stackpointer (word 112),112)]
      [(workspace,868); (guards,4 * LENGTH gs); (make,4 * LENGTH ms)] /\
    nonoverlapping (guards,4 * LENGTH gs) (make,4 * LENGTH ms) /\
    nonoverlapping (word pc,LENGTH ordinary_flat_mc)
      (word_sub stackpointer (word 112),112) /\
    ALL (nonoverlapping (word pc,LENGTH ordinary_flat_mc))
      [(word_add workspace (word 612),4 * LENGTH ms);
       (word_add workspace (word 740),4 * LENGTH ms);
       (word_sub stackpointer (word 112),56)] /\
    ALL (\q. ALL (nonoverlapping q)
              [(word pc,LENGTH ordinary_flat_mc);
               (word_sub stackpointer (word 112),112); (workspace,868)])
      [(call,72); (premises,8 * LENGTH ptrs); (constants,4 * LENGTH cs)] /\
    ALL (\p. ALL (nonoverlapping (p,16))
              [(word pc,LENGTH ordinary_flat_mc);
               (word_sub stackpointer (word 112),112); (workspace,868)]) ptrs`;;

let ordinary_adapter_frame = new_definition
 `ordinary_adapter_frame workspace (fs:int32 list) (rs:int32 list)
      (ms:int32 list) stackpointer =
    (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; RCX; RDX; RDI; RSI;
                R8; R9; R10; R11; R12; R13; R14; R15] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(workspace,4 * LENGTH fs);
                memory :> bytes(word_add workspace (word 512),4 * LENGTH rs);
                memory :> bytes(word_add workspace (word 612),4 * LENGTH ms);
                memory :> bytes(word_add workspace (word 740),4 * LENGTH ms);
                memory :> bytes(word_sub stackpointer (word 112),112)])`;;

let ORDINARY_ADAPTER_FRAME_IDEMPOTENT = prove
 (`!workspace (fs:int32 list) (rs:int32 list) (ms:int32 list) stackpointer.
      ordinary_adapter_frame workspace fs rs ms stackpointer ,,
      ordinary_adapter_frame workspace fs rs ms stackpointer =
      ordinary_adapter_frame workspace fs rs ms stackpointer`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN
  MAYCHANGE_IDEMPOT_TAC);;

let ORDINARY_ADAPTER_TRANS = prove
 (`!workspace (fs:int32 list) (rs:int32 list) (ms:int32 list) stackpointer
      P Q R.
    ensures x86 P Q (ordinary_adapter_frame workspace fs rs ms stackpointer) /\
    ensures x86 Q R (ordinary_adapter_frame workspace fs rs ms stackpointer)
    ==> ensures x86 P R (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `Q:x86state->bool` THEN
  REWRITE_TAC[ORDINARY_ADAPTER_FRAME_IDEMPOTENT] THEN ASM_REWRITE_TAC[]);;

let ordinary_pack_saved = new_definition
 `ordinary_pack_saved call constants guards make workspace nconst
      nguards arity stackpointer returnaddress init_rbp init_rbx init_r12
      init_r13 init_r14 init_r15 s <=>
    read RDI s = workspace /\ read RSI s = call /\
    read RBX s = word nconst /\ read RBP s = word nguards /\
    read R14 s = word arity /\ read R13 s = init_r13 /\ read R15 s = init_r15 /\
    read RSP s = word_sub stackpointer (word 40) /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    read (memory :> bytes64 (word_sub stackpointer (word 8))) s = init_r14 /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s = init_r12 /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s = init_rbp /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s = init_rbx /\
    read (memory :> bytes64 (word_add call (word 8))) s = constants /\
    read (memory :> bytes64 (word_add call (word 16))) s = guards /\
    read (memory :> bytes64 (word_add call (word 24))) s = make`;;

let ordinary_pack_data = new_definition
 `ordinary_pack_data call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 s <=>
    ordinary_pack_saved call constants guards make workspace (LENGTH cs)
      (LENGTH gs) (LENGTH ms) stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 s /\
    read R12 s = (if LENGTH ptrs = 0 then init_r12 else premises) /\
    ordinary_adapter_sources call premises constants guards make workspace ptrs ps
      cs gs ms s /\
    wordlist_from_memory(premises,LENGTH ptrs) s = ptrs /\
    (!i. i < LENGTH ps
         ==> wordlist_from_memory(EL i ptrs,4) s = EL i ps) /\
    wordlist_from_memory(constants,LENGTH cs) s = cs /\
    wordlist_from_memory(guards,LENGTH gs) s = gs /\
    wordlist_from_memory(make,LENGTH ms) s = ms /\
    wordlist_from_memory(word_add workspace (word 612),LENGTH ms) s = ds /\
    wordlist_from_memory(word_add workspace (word 740),LENGTH ms) s = zs`;;

let ordinary_pack_inv = new_definition
 `ordinary_pack_inv pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      (fs:int32 list) (rs:int32 list) stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 i s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read R9 s = word (LENGTH ptrs) /\ read R8 s = word i /\
    ordinary_pack_data call premises constants guards make workspace ptrs ps cs
      gs ms ds zs stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 s /\
    wordlist_from_memory(workspace,4 * i) s = flat_prefix (4 * i) fs /\
    wordlist_from_memory(word_add workspace (word 512),i) s = flat_prefix i rs`;;

let ordinary_copy_inv = new_definition
 `ordinary_copy_inv pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      (fs:int32 list) (rs:int32 list) stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 i j s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read R9 s = word (LENGTH ptrs) /\ read R8 s = word i /\
    read R10 s = word (4 * i) /\ read R11 s = EL i ptrs /\
    read RAX s = word j /\
    ordinary_pack_data call premises constants guards make workspace ptrs ps cs
      gs ms ds zs stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 s /\
    wordlist_from_memory(workspace,4 * i + j) s = flat_prefix (4 * i + j) fs /\
    wordlist_from_memory(word_add workspace (word 512),i + 1) s =
      flat_prefix (i + 1) rs`;;

let ordinary_pack_done = new_definition
 `ordinary_pack_done pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      (fs:int32 list) (rs:int32 list) stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 i s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read RIP s = word (pc + 0x26d) /\
    read R9 s = word (LENGTH ptrs) /\ read R8 s = word i /\
    ordinary_pack_data call premises constants guards make workspace ptrs ps cs
      gs ms ds zs stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 s /\
    wordlist_from_memory(workspace,4 * i) s = flat_prefix (4 * i) fs /\
    wordlist_from_memory(word_add workspace (word 512),i) s = flat_prefix i rs /\
    (read ZF s <=> i = LENGTH ptrs)`;;

let ordinary_scan_inv = new_definition
 `ordinary_scan_inv pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 i s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read R9 s = word (LENGTH ptrs) /\
    read RAX s = word_add premises (word (8 * i)) /\
    read RDX s = word_add premises (word (8 * LENGTH ptrs)) /\
    ordinary_pack_data call premises constants guards make workspace ptrs ps cs
      gs ms ds zs stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 s`;;

let ordinary_scan_start = new_definition
 `ordinary_scan_start pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 s <=>
    read RIP s = word (pc + 0x18d) /\
    ordinary_scan_inv pc call premises constants guards make workspace ptrs ps cs
      gs ms ds zs stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 0 s`;;

let ordinary_pack_start = new_definition
 `ordinary_pack_start pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      (fs:int32 list) (rs:int32 list) stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    read RIP s = word (pc + 0x23e) /\
    ordinary_pack_inv pc call premises constants guards make workspace ptrs ps cs
      gs ms ds zs fs rs stackpointer returnaddress init_rbp init_rbx init_r12
      init_r13 init_r14 init_r15 0 s`;;

let ordinary_pack_finish = new_definition
 `ordinary_pack_finish pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      (fs:int32 list) (rs:int32 list) stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    read RIP s = word (pc + 0x27a) /\
    read R9 s = word (LENGTH ptrs) /\
    read RAX s = word (4 * LENGTH ptrs) /\
    ordinary_pack_data call premises constants guards make workspace ptrs ps cs
      gs ms ds zs stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 s /\
    wordlist_from_memory(workspace,4 * LENGTH ptrs) s =
      flat_prefix (4 * LENGTH ptrs) fs /\
    wordlist_from_memory(word_add workspace (word 512),LENGTH ptrs) s =
      flat_prefix (LENGTH ptrs) rs`;;

let ordinary_const_inv = new_definition
 `ordinary_const_inv pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      (fs:int32 list) (rs:int32 list) stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 j s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read R9 s = word (LENGTH ptrs) /\ read R8 s = constants /\
    read RCX s = word_add workspace (word (4 * LENGTH ptrs)) /\
    read RAX s = word j /\
    ordinary_pack_data call premises constants guards make workspace ptrs ps cs
      gs ms ds zs stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 s /\
    wordlist_from_memory(workspace,4 * LENGTH ptrs + j) s =
      flat_prefix (4 * LENGTH ptrs + j) fs /\
    wordlist_from_memory(word_add workspace (word 512),LENGTH ptrs + 1) s =
      flat_prefix (LENGTH ptrs + 1) rs`;;

let ordinary_const_entry = new_definition
 `ordinary_const_entry pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      (fs:int32 list) (rs:int32 list) stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read RIP s = word (pc + 0x28b) /\
    read R9 s = word (LENGTH ptrs) /\
    read RAX s = word (4 * LENGTH ptrs) /\
    ordinary_pack_data call premises constants guards make workspace ptrs ps cs
      gs ms ds zs stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 s /\
    wordlist_from_memory(workspace,4 * LENGTH ptrs) s =
      flat_prefix (4 * LENGTH ptrs) fs /\
    wordlist_from_memory(word_add workspace (word 512),LENGTH rs) s = rs`;;

let ordinary_adapter_prepare = new_definition
 `ordinary_adapter_prepare pc call premises constants guards make workspace
      (ptrs:int64 list) (ps:(int32 list) list) (cs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list)
      (fs:int32 list) (rs:int32 list) stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read RIP s = word (pc + 0x1d3) /\
    ordinary_pack_data call premises constants guards make workspace ptrs ps cs
      gs ms ds zs stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 s /\
    wordlist_from_memory(workspace,LENGTH fs) s = fs /\
    wordlist_from_memory(word_add workspace (word 512),LENGTH rs) s = rs`;;

let ORDINARY_ADAPTER_LEAF = prove
 (`!pc premises guards make workspace (fs:int32 list) (rs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list) nc
      stackpointer init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    flat_valid fs rs gs ms /\
    LENGTH ds = LENGTH ms /\ LENGTH zs = LENGTH ms /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc);
       (word_sub (word_sub stackpointer (word 64)) (word 48),56)]
      [(workspace,4 * LENGTH fs);
       (word_add workspace (word 512),4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
       (word_add workspace (word 612),4 * LENGTH ms);
       (word_add workspace (word 740),4 * LENGTH ms)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub (word_sub stackpointer (word 64)) (word 48),56) /\
    ALL (nonoverlapping (word_add workspace (word 740),4 * LENGTH ms))
      [(workspace,4 * LENGTH fs);
       (word_add workspace (word 512),4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
       (word_add workspace (word 612),4 * LENGTH ms)] /\
    ALL (nonoverlapping (word_add workspace (word 612),4 * LENGTH ms))
      [(workspace,4 * LENGTH fs);
       (word_add workspace (word 512),4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms)] /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH ordinary_flat_mc);
       (word_sub stackpointer (word 112),112)]
      [(workspace,868); (guards,4 * LENGTH gs); (make,4 * LENGTH ms)] /\
    nonoverlapping (guards,4 * LENGTH gs) (make,4 * LENGTH ms) /\
    nonoverlapping (word pc,LENGTH ordinary_flat_mc)
      (word_sub stackpointer (word 112),112) /\
    ALL (nonoverlapping (word pc,LENGTH ordinary_flat_mc))
      [(word_add workspace (word 612),4 * LENGTH ms);
       (word_add workspace (word 740),4 * LENGTH ms);
       (word_sub stackpointer (word 112),56)]
    ==> ensures x86
      (\s. ordinary_adapter_call pc premises guards make workspace fs rs gs ms
             ds zs nc stackpointer init_rbp init_rbx init_r12 init_r13 init_r14
             init_r15 s)
      (\s. ordinary_adapter_leaf_state pc premises guards make workspace fs rs gs ms
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else ds)
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else zs)
             nc stackpointer (bitval (flat_guards_hold fs rs gs))
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; RCX; RDX; R10; R11;
                  R12; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(word_add workspace (word 612),4 * LENGTH ms);
                  memory :> bytes(word_add workspace (word 740),4 * LENGTH ms);
                  memory :> bytes(word_sub stackpointer (word 112),48)] ,,
       MAYCHANGE [memory :> bytes64(word_sub stackpointer (word 64))])`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
              ordinary_adapter_call; ordinary_adapter_leaf_state;
              WORDLIST_FROM_MEMORY_32; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPUTE_LENGTH_RULE flat_fire_mc;
                              COMPUTE_LENGTH_RULE ordinary_flat_mc]) THEN
  VAL_INT64_TAC `LENGTH(fs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(rs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64) (pc,211)
      (val (workspace:int64),4 * LENGTH (fs:int32 list)) /\
    nonoverlapping_modulo (2 EXP 64) (pc,211)
      (val (word_add workspace (word 512)),4 * LENGTH (rs:int32 list)) /\
    nonoverlapping_modulo (2 EXP 64) (pc,211)
      (val (guards:int64),4 * LENGTH (gs:int32 list)) /\
    nonoverlapping_modulo (2 EXP 64) (pc,211)
      (val (make:int64),4 * LENGTH (ms:int32 list)) /\
    nonoverlapping_modulo (2 EXP 64) (pc,211)
      (val (word_add workspace (word 612)),4 * LENGTH (ms:int32 list)) /\
    nonoverlapping_modulo (2 EXP 64) (pc,211)
      (val (word_add workspace (word 740)),4 * LENGTH (ms:int32 list)) /\
    nonoverlapping_modulo (2 EXP 64) (pc,211)
      (val (word_sub (word_sub (stackpointer:int64) (word 64)) (word 48)),56)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPUTE_LENGTH_RULE flat_fire_mc] THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC ORDINARY_FLAT_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_sub x (word 56)) (word 8):int64 =
               word_sub x (word 64)`]) THEN
  X86_SUBROUTINE_SIM_TAC
    (ordinary_flat_mc,ORDINARY_FLAT_EXEC,0,flat_fire_mc,FLAT_FIRE_CORRECT)
    [`workspace:int64`; `word_add workspace (word 512):int64`; `guards:int64`;
     `make:int64`; `word_add workspace (word 612):int64`;
     `word_add workspace (word 740):int64`; `fs:int32 list`; `rs:int32 list`;
     `gs:int32 list`; `ms:int32 list`; `ds:int32 list`; `zs:int32 list`;
     `pc:num`; `word_sub stackpointer (word 64):int64`;
     `word (pc + 0x1fd):int64`; `word (LENGTH (gs:int32 list)):int64`;
     `word nc:int64`; `premises:int64`; `init_r13:int64`;
     `word (LENGTH (ms:int32 list)):int64`; `init_r15:int64`] 2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_return; C_RETURN;
                              WORDLIST_FROM_MEMORY_32]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_sub x (word 64)) (word 48):int64 =
               word_sub x (word 112)`]) THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_32] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `orthogonal_components
      (memory :> bytes(word_add workspace (word 512),4 * LENGTH (rs:int32 list)))
      (memory :> bytes(word_add workspace (word 612),4 * LENGTH (ms:int32 list))) /\
    orthogonal_components
      (memory :> bytes(word_add workspace (word 512),4 * LENGTH rs))
      (memory :> bytes(word_add workspace (word 740),4 * LENGTH (ms:int32 list))) /\
    orthogonal_components
      (memory :> bytes(word_add workspace (word 512),4 * LENGTH rs))
      (memory :> bytes(word_sub stackpointer (word 112),48)) /\
    orthogonal_components
      (memory :> bytes(word_add workspace (word 512),4 * LENGTH rs))
      (memory :> bytes64(word_sub stackpointer (word 64)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ORTHOGONAL_BYTES THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN FIRST_X_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC ORDINARY_ORTHOGONAL_BYTES THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN FIRST_X_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC ORDINARY_ORTHOGONAL_BYTES THEN
      MATCH_MP_TAC(ISPECL
       [`word_add workspace (word 512):int64`; `4 * LENGTH (rs:int32 list)`;
        `word_sub stackpointer (word 112):int64`; `56`;
        `word_add workspace (word 512):int64`; `4 * LENGTH (rs:int32 list)`;
        `word_sub stackpointer (word 112):int64`; `48`]
       NONOVERLAPPING_SUBREGIONS) THEN
      REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
        REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN FIRST_X_ASSUM ACCEPT_TAC;
        REWRITE_TAC[CONTAINED] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[CONTAINED] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      MATCH_MP_TAC ORDINARY_ORTHOGONAL_BYTES64 THEN
      MATCH_MP_TAC(ISPECL
       [`word_add workspace (word 512):int64`; `4 * LENGTH (rs:int32 list)`;
        `word_sub stackpointer (word 112):int64`; `56`;
        `word_add workspace (word 512):int64`; `4 * LENGTH (rs:int32 list)`;
        `word_sub stackpointer (word 64):int64`; `8`]
       NONOVERLAPPING_SUBREGIONS) THEN
      REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
        REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN FIRST_X_ASSUM ACCEPT_TAC;
        REWRITE_TAC[CONTAINED] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN
         `word_sub stackpointer (word 64):int64 =
          word_add (word_sub stackpointer (word 112)) (word 48)`
        SUBST1_TAC THENL [WORD_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[CONTAINED] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC `48 + i` THEN CONJ_TAC THENL
         [ASM_ARITH_TAC;
          REWRITE_TAC[WORD_ADD_ASSOC; GSYM WORD_ADD]]]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes64 (word_sub stackpointer (word 8))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 8))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 16))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 16))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 24))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 24))) s0 /\
    read (memory :> bytes64 (word_sub stackpointer (word 32))) s2 =
      read (memory :> bytes64 (word_sub stackpointer (word 32))) s0 /\
    read (memory :> bytes (workspace,4 * LENGTH (fs:int32 list))) s2 =
      read (memory :> bytes (workspace,4 * LENGTH fs)) s0 /\
    read (memory :> bytes
      (word_add workspace (word 512),4 * LENGTH (rs:int32 list))) s2 =
      read (memory :> bytes
        (word_add workspace (word 512),4 * LENGTH rs)) s0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (maychange_term o concl)) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    (ORDINARY_READ_OVER_WRITE_ORTHOGONAL_TAC ORELSE FAIL_TAC "PRESERVE");
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    WORD_RULE `word_sub (word_sub x (word 64)) (word 48):int64 =
               word_sub x (word 112)`]) THEN
  (ENSURES_FINAL_STATE_TAC ORELSE FAIL_TAC "FINAL") THEN ASM_REWRITE_TAC[
    WORD_RULE `word_add (word_sub x (word 64)) (word 8):int64 =
               word_sub x (word 56)`] THEN
  (MONOTONE_MAYCHANGE_TAC ORELSE FAIL_TAC "FRAME"));;

let ORDINARY_ADAPTER_EPILOGUE = prove
 (`!pc premises guards make workspace (fs:int32 list) (rs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list) nc
      returnvalue stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15.
    ensures x86
      (\s. ordinary_adapter_leaf_state pc premises guards make workspace fs rs gs ms
             ds zs nc stackpointer returnvalue init_rbp init_rbx init_r12 init_r13
             init_r14 init_r15 s /\
           read (memory :> bytes64 stackpointer) s = returnaddress)
      (\s. ordinary_adapter_return workspace fs rs ds zs returnvalue stackpointer
             returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RDX; RCX; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[C_RETURN; ordinary_adapter_leaf_state; ordinary_adapter_return;
              WORDLIST_FROM_MEMORY_32; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[
    WORD_RULE `word_add (word_sub x (word 56)) (word 16):int64 =
               word_sub x (word 40)`;
    WORD_RULE `word_add (word_sub x (word 40)) (word 8):int64 =
               word_sub x (word 32)`]);;

let ORDINARY_ADAPTER_AFTER_LEAF = prove
 (`!pc premises guards make workspace (fs:int32 list) (rs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list) nc
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    flat_valid fs rs gs ms /\
    LENGTH ds = LENGTH ms /\ LENGTH zs = LENGTH ms /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH flat_fire_mc);
       (word_sub (word_sub stackpointer (word 64)) (word 48),56)]
      [(workspace,4 * LENGTH fs);
       (word_add workspace (word 512),4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
       (word_add workspace (word 612),4 * LENGTH ms);
       (word_add workspace (word 740),4 * LENGTH ms)] /\
    nonoverlapping (word pc,LENGTH flat_fire_mc)
      (word_sub (word_sub stackpointer (word 64)) (word 48),56) /\
    ALL (nonoverlapping (word_add workspace (word 740),4 * LENGTH ms))
      [(workspace,4 * LENGTH fs);
       (word_add workspace (word 512),4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms);
       (word_add workspace (word 612),4 * LENGTH ms)] /\
    ALL (nonoverlapping (word_add workspace (word 612),4 * LENGTH ms))
      [(workspace,4 * LENGTH fs);
       (word_add workspace (word 512),4 * LENGTH rs);
       (guards,4 * LENGTH gs); (make,4 * LENGTH ms)] /\
    ALLPAIRS nonoverlapping
      [(word pc,LENGTH ordinary_flat_mc);
       (word_sub stackpointer (word 112),112)]
      [(workspace,868); (guards,4 * LENGTH gs); (make,4 * LENGTH ms)] /\
    nonoverlapping (guards,4 * LENGTH gs) (make,4 * LENGTH ms) /\
    nonoverlapping (word pc,LENGTH ordinary_flat_mc)
      (word_sub stackpointer (word 112),112) /\
    ALL (nonoverlapping (word pc,LENGTH ordinary_flat_mc))
      [(word_add workspace (word 612),4 * LENGTH ms);
       (word_add workspace (word 740),4 * LENGTH ms);
       (word_sub stackpointer (word 112),56)]
    ==> ensures x86
      (\s. ordinary_adapter_call pc premises guards make workspace fs rs gs ms
             ds zs nc stackpointer init_rbp init_rbx init_r12 init_r13 init_r14
             init_r15 s /\
           read (memory :> bytes64 stackpointer) s = returnaddress)
      (\s. ordinary_adapter_return workspace fs rs
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else ds)
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else zs)
             (bitval (flat_guards_hold fs rs gs)) stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      ((MAYCHANGE [RIP; RSP; RAX; RBX; RBP; RCX; RDX; R10; R11;
                   R12; R13; R14; R15] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes(word_add workspace (word 612),4 * LENGTH ms);
                   memory :> bytes(word_add workspace (word 740),4 * LENGTH ms);
                   memory :> bytes(word_sub stackpointer (word 112),48)] ,,
        MAYCHANGE [memory :> bytes64(word_sub stackpointer (word 64))]) ,,
       MAYCHANGE [RIP; RSP; RDX; RCX; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS THEN
  EXISTS_TAC `\s. ordinary_adapter_leaf_state pc premises guards make workspace
      fs rs gs ms
      (if flat_guards_hold fs rs gs then flat_selected fs rs ms else ds)
      (if flat_guards_hold fs rs gs then flat_selected fs rs ms else zs)
      nc stackpointer (bitval (flat_guards_hold fs rs gs)) init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 s /\
    read (memory :> bytes64 stackpointer) s = returnaddress` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
      REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
    (ORDINARY_READ_OVER_WRITE_ORTHOGONAL_TAC ORELSE FAIL_TAC "PRESERVE");
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS] ORDINARY_ADAPTER_LEAF) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS] ORDINARY_ADAPTER_EPILOGUE)]);;

let ORDINARY_ADAPTER_AFTER_LEAF_SOURCES = prove
 (`!pc call currentpremises premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (fs:int32 list) (rs:int32 list)
      (gs:int32 list) (ms:int32 list) (ds:int32 list) (zs:int32 list) nc
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    flat_valid fs rs gs ms /\
    LENGTH ds = LENGTH ms /\ LENGTH zs = LENGTH ms /\ LENGTH ps = LENGTH ptrs /\
    LENGTH ms <= 32 /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_call pc currentpremises guards make workspace fs rs gs ms
             ds zs nc stackpointer init_rbp init_rbx init_r12 init_r13 init_r14
             init_r15 s /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (\s. ordinary_adapter_return workspace fs rs
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else ds)
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else zs)
             (bitval (flat_guards_hold fs rs gs)) stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      ((MAYCHANGE [RIP; RSP; RAX; RBX; RBP; RCX; RDX; R10; R11;
                   R12; R13; R14; R15] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes(word_add workspace (word 612),4 * LENGTH ms);
                   memory :> bytes(word_add workspace (word 740),4 * LENGTH ms);
                   memory :> bytes(word_sub stackpointer (word 112),48)] ,,
        MAYCHANGE [memory :> bytes64(word_sub stackpointer (word 64))]) ,,
       MAYCHANGE [RIP; RSP; RDX; RCX; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[SOME_FLAGS; ordinary_adapter_exclusions; ordinary_adapter_sources;
              WORDLIST_FROM_MEMORY_32; ORDINARY_WORDLIST_FROM_MEMORY_64] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    (ORDINARY_READ_OVER_WRITE_ORTHOGONAL_TAC ORELSE FAIL_TAC "SOURCE_PRESERVE");
    MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS] ORDINARY_ADAPTER_AFTER_LEAF) THEN
    ASM_REWRITE_TAC[]]);;

let ORDINARY_ADAPTER_PREPARE = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    ensures x86
      (\s. ordinary_adapter_prepare pc call premises constants guards make
             workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_call pc
             (if LENGTH ptrs = 0 then init_r12 else premises) guards make workspace
             fs rs gs ms ds zs (LENGTH cs) stackpointer init_rbp init_rbx init_r12
             init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RCX; RDX; RSI; R8; R9] ,,
       MAYCHANGE [memory :> bytes64(word_sub stackpointer (word 56));
                  memory :> bytes64(word_sub stackpointer (word 48))])`,
  REWRITE_TAC[ordinary_adapter_prepare; ordinary_adapter_call; ordinary_pack_data;
              ordinary_pack_saved; ordinary_adapter_sources; C_RETURN;
              fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[
    WORD_RULE `word_sub (word_sub (word_sub x (word 40)) (word 8)) (word 8):int64 =
               word_sub x (word 56)`;
    WORD_RULE `word_sub (word_sub x (word 40)) (word 8):int64 =
               word_sub x (word 48)`] THEN
  MONOTONE_MAYCHANGE_TAC);;

let ORDINARY_ADAPTER_PREPARE_SOURCES = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_prepare pc call premises constants guards make
             workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_call pc
             (if LENGTH ptrs = 0 then init_r12 else premises) guards make workspace
             fs rs gs ms ds zs (LENGTH cs) stackpointer init_rbp init_rbx init_r12
             init_r13 init_r14 init_r15 s /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REWRITE_TAC[ordinary_adapter_exclusions; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC `\s. ordinary_adapter_prepare pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    ordinary_adapter_sources call premises constants guards make workspace ptrs ps
      cs gs ms s` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ordinary_adapter_prepare; ordinary_pack_data] THEN MESON_TAC[];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN CONJ_TAC THENL
     [REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC;
      MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN CONJ_TAC THENL
       [REWRITE_TAC[ordinary_adapter_sources; WORDLIST_FROM_MEMORY_32;
                    ORDINARY_WORDLIST_FROM_MEMORY_64] THEN
        REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
        REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
        PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        (ORDINARY_READ_OVER_WRITE_ORTHOGONAL_TAC ORELSE
         FAIL_TAC "PREPARE_SOURCE_PRESERVE");
        MATCH_MP_TAC ORDINARY_ADAPTER_PREPARE]]]);;

let ORDINARY_ADAPTER_STATUS_SOURCES = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 P C.
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer /\
    (!s. ordinary_adapter_entry pc call premises constants guards make workspace
           ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
           init_r12 init_r13 init_r14 init_r15 s ==> P s) /\
    C subsumed (ordinary_adapter_frame workspace fs rs ms stackpointer) /\
    ensures x86 P
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s) C
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC `\s. ordinary_adapter_entry pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 s /\
    ordinary_adapter_sources call premises constants guards make workspace ptrs ps
      cs gs ms s` THEN CONJ_TAC THENL
   [REWRITE_TAC[ordinary_adapter_entry] THEN MESON_TAC[];
    MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[ordinary_adapter_exclusions; ALLPAIRS; ALL;
                                  NONOVERLAPPING_CLAUSES]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM NONOVERLAPPING_CLAUSES]) THEN
      REWRITE_TAC[ordinary_adapter_sources; WORDLIST_FROM_MEMORY_32;
                  ORDINARY_WORDLIST_FROM_MEMORY_64] THEN
      REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
      REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      (ORDINARY_READ_OVER_WRITE_ORTHOGONAL_TAC ORELSE
       FAIL_TAC "STATUS_SOURCE_PRESERVE");
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `P:x86state->bool` THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN ASM_REWRITE_TAC[]]]]);;

let ordinary_adapter_early = new_definition
 `ordinary_adapter_early pc call workspace nkeep stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s <=>
    bytes_loaded s (word pc) ordinary_flat_mc /\
    read RIP s = word (pc + 0xe0) /\ read RDI s = call /\
    read RSP s = stackpointer /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    read RBP s = init_rbp /\ read RBX s = init_rbx /\
    read R12 s = init_r12 /\ read R13 s = init_r13 /\
    read R14 s = init_r14 /\ read R15 s = init_r15 /\
    read (memory :> bytes64 (word_add call (word 32))) s = workspace /\
    read (memory :> bytes64 (word_add call (word 40))) s = word nkeep`;;

let ORDINARY_ADAPTER_EARLY_UNSUPPORTED = prove
 (`!pc call workspace nkeep stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15.
    nkeep < 2 EXP 64 /\
    (call = word 0 \/
     ~(call = word 0) /\ workspace = word 0 \/
     ~(call = word 0) /\ ~(workspace = word 0) /\ nkeep > 24)
    ==> ensures x86
      (\s. ordinary_adapter_early pc call workspace nkeep stackpointer
             returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RAX; RDI; RSI; R9] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; ordinary_adapter_early;
              ordinary_adapter_status_return; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN VAL_INT64_TAC `nkeep:num` THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let ordinary_adapter_counts_entry = new_definition
 `ordinary_adapter_counts_entry pc call workspace nkeep nconst nguards arity
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 s <=>
    ordinary_adapter_early pc call workspace nkeep stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
    read (memory :> bytes64 (word_add call (word 48))) s = word nconst /\
    read (memory :> bytes64 (word_add call (word 56))) s = word nguards /\
    read (memory :> bytes64 (word_add call (word 64))) s = word arity`;;

let ORDINARY_ADAPTER_BAD_COUNTS = prove
 (`!pc call workspace nkeep nconst nguards arity stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15.
    nkeep < 2 EXP 64 /\ nconst < 2 EXP 64 /\
    nguards < 2 EXP 64 /\ arity < 2 EXP 64 /\
    ~(call = word 0) /\ ~(workspace = word 0) /\ nkeep <= 24 /\
    (nconst > 32 \/
     ~(nconst > 32) /\ nguards > 32 \/
     ~(nconst > 32) /\ ~(nguards > 32) /\ arity > 32)
    ==> ensures x86
      (\s. ordinary_adapter_counts_entry pc call workspace nkeep nconst nguards
             arity stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
             init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; ordinary_adapter_counts_entry;
              ordinary_adapter_early; ordinary_adapter_status_return;
              fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `nkeep:num` THEN VAL_INT64_TAC `nconst:num` THEN
  VAL_INT64_TAC `nguards:num` THEN VAL_INT64_TAC `arity:num` THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--27) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--31) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let ordinary_adapter_pointer_entry = new_definition
 `ordinary_adapter_pointer_entry pc call premises constants guards make workspace
      nkeep nconst nguards arity stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 s <=>
    ordinary_adapter_counts_entry pc call workspace nkeep nconst nguards arity
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 s /\
    read (memory :> bytes64 call) s = premises /\
    read (memory :> bytes64 (word_add call (word 8))) s = constants /\
    read (memory :> bytes64 (word_add call (word 16))) s = guards /\
    read (memory :> bytes64 (word_add call (word 24))) s = make`;;

let ORDINARY_ADAPTER_NULL_PREMISES = prove
 (`!pc call premises constants guards make workspace nkeep nconst nguards arity
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    ~(call = word 0) /\ ~(workspace = word 0) /\
    nkeep <= 24 /\ nconst <= 32 /\ nguards <= 32 /\ arity <= 32 /\
    nkeep > 0 /\ premises = word 0
    ==> ensures x86
      (\s. ordinary_adapter_pointer_entry pc call premises constants guards make
             workspace nkeep nconst nguards arity stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; ordinary_adapter_pointer_entry;
              ordinary_adapter_counts_entry; ordinary_adapter_early;
              ordinary_adapter_status_return; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `nkeep:num` THEN VAL_INT64_TAC `nconst:num` THEN
  VAL_INT64_TAC `nguards:num` THEN VAL_INT64_TAC `arity:num` THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let ORDINARY_ADAPTER_NULL_CONSTANTS = prove
 (`!pc call premises constants guards make workspace nkeep nconst nguards arity
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    ~(call = word 0) /\ ~(workspace = word 0) /\
    nkeep <= 24 /\ nconst <= 32 /\ nguards <= 32 /\ arity <= 32 /\
    (nkeep = 0 \/ ~(premises = word 0)) /\
    nconst > 0 /\ constants = word 0
    ==> ensures x86
      (\s. ordinary_adapter_pointer_entry pc call premises constants guards make
             workspace nkeep nconst nguards arity stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; ordinary_adapter_pointer_entry;
              ordinary_adapter_counts_entry; ordinary_adapter_early;
              ordinary_adapter_status_return; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `nkeep:num` THEN VAL_INT64_TAC `nconst:num` THEN
  VAL_INT64_TAC `nguards:num` THEN VAL_INT64_TAC `arity:num` THEN
  ASM_CASES_TAC `nkeep = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--38) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let ORDINARY_ADAPTER_NULL_GUARDS = prove
 (`!pc call premises constants guards make workspace nkeep nconst nguards arity
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    ~(call = word 0) /\ ~(workspace = word 0) /\
    nkeep <= 24 /\ nconst <= 32 /\ nguards <= 32 /\ arity <= 32 /\
    (nkeep = 0 \/ ~(premises = word 0)) /\
    (nconst = 0 \/ ~(constants = word 0)) /\
    nguards > 0 /\ guards = word 0
    ==> ensures x86
      (\s. ordinary_adapter_pointer_entry pc call premises constants guards make
             workspace nkeep nconst nguards arity stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; ordinary_adapter_pointer_entry;
              ordinary_adapter_counts_entry; ordinary_adapter_early;
              ordinary_adapter_status_return; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `nkeep:num` THEN VAL_INT64_TAC `nconst:num` THEN
  VAL_INT64_TAC `nguards:num` THEN VAL_INT64_TAC `arity:num` THEN
  ASM_CASES_TAC `nkeep = 0` THEN ASM_CASES_TAC `nconst = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--39) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--40) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--39) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let ORDINARY_ADAPTER_NULL_MAKE = prove
 (`!pc call premises constants guards make workspace nkeep nconst nguards arity
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    ~(call = word 0) /\ ~(workspace = word 0) /\
    nkeep <= 24 /\ nconst <= 32 /\ nguards <= 32 /\ arity <= 32 /\
    (nkeep = 0 \/ ~(premises = word 0)) /\
    (nconst = 0 \/ ~(constants = word 0)) /\
    (nguards = 0 \/ ~(guards = word 0)) /\
    arity > 0 /\ make = word 0
    ==> ensures x86
      (\s. ordinary_adapter_pointer_entry pc call premises constants guards make
             workspace nkeep nconst nguards arity stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; ordinary_adapter_pointer_entry;
              ordinary_adapter_counts_entry; ordinary_adapter_early;
              ordinary_adapter_status_return; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  VAL_INT64_TAC `nkeep:num` THEN VAL_INT64_TAC `nconst:num` THEN
  VAL_INT64_TAC `nguards:num` THEN VAL_INT64_TAC `arity:num` THEN
  ASM_CASES_TAC `nkeep = 0` THEN ASM_CASES_TAC `nconst = 0` THEN
  ASM_CASES_TAC `nguards = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--42) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--42) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--44) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--42) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--43) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--43) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--45) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let ORDINARY_ADAPTER_SCAN = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    0 < LENGTH ptrs /\ LENGTH ptrs < 2 EXP 64 /\
    ALL (\(p:int64). ~(p = word 0)) ptrs
    ==> ensures x86
      (\s. ordinary_scan_start pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_pack_start pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RAX] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; ordinary_scan_start; ordinary_scan_inv;
              ordinary_pack_start; ordinary_pack_inv; ordinary_pack_data;
              ordinary_pack_saved; ordinary_adapter_sources; flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES;
              fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN VAL_INT64_TAC `LENGTH(ptrs:int64 list)` THEN
  ENSURES_WHILE_UP2_TAC `LENGTH(ptrs:int64 list)` `pc + 0x18d` `pc + 0x23b`
   `\i s. ordinary_scan_inv pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 i s` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[ordinary_scan_inv] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `~(EL i (ptrs:int64 list) = word 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ALL_EL]; ALL_TAC] THEN
    SUBGOAL_THEN
     `read (memory :> bytes64 (word_add premises (word (8 * i)))) s0 =
        EL i (ptrs:int64 list)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ORDINARY_READ64 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [WORD_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `i + 1 < LENGTH(ptrs:int64 list) <=> ~(i + 1 = LENGTH ptrs)`
     (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    REWRITE_TAC[ordinary_scan_inv] THEN X86_SIM_TAC ORDINARY_FLAT_EXEC [1] THEN
    ASM_REWRITE_TAC[ordinary_pack_start; ordinary_pack_inv; flat_prefix;
                    WORDLIST_FROM_MEMORY_CLAUSES]]);;

let ORDINARY_ADAPTER_SCAN_NULL = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 k.
    k < LENGTH ptrs /\ LENGTH ptrs < 2 EXP 64 /\
    (!i. i < k ==> ~(EL i ptrs = word 0)) /\ EL k ptrs = word 0
    ==> ensures x86
      (\s. ordinary_scan_start pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[C_RETURN; SOME_FLAGS; ordinary_scan_start; ordinary_scan_inv;
              ordinary_adapter_status_return; ordinary_pack_data;
              ordinary_pack_saved; ordinary_adapter_sources;
              fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN VAL_INT64_TAC `LENGTH(ptrs:int64 list)` THEN
  ENSURES_WHILE_UP2_TAC `k + 1` `pc + 0x18d` `val returnaddress`
   `\i s. if i <= k
          then ordinary_scan_inv pc call premises constants guards make workspace
                 ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp
                 init_rbx init_r12 init_r13 init_r14 init_r15 i s
          else ordinary_adapter_status_return 2 stackpointer returnaddress
                 init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_CASES_TAC `i = k:num` THENL
     [SUBST1_TAC(ASSUME `i = k:num`) THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(k + 1 <= k)`; ordinary_scan_inv] THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read (memory :> bytes64 (word_add premises (word (8 * k)))) s0 =
          EL k (ptrs:int64 list)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC ORDINARY_READ64 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--9) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_RULE
        `word_add (word_sub x (word 40)) (word 8):int64 = word_sub x (word 32)`];
      SUBGOAL_THEN `i < k:num` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> i + 1 <= k`;
                   ARITH_RULE `i < k ==> i + 1 < k + 1`; ordinary_scan_inv] THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `~(EL i (ptrs:int64 list) = word 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `read (memory :> bytes64 (word_add premises (word (8 * i)))) s0 =
          EL i (ptrs:int64 list)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC ORDINARY_READ64 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN WORD_ARITH_TAC];
    ASM_REWRITE_TAC[ARITH_RULE `~(k + 1 <= k)`] THEN
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let ORDINARY_ADAPTER_PACK = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    0 < LENGTH ptrs /\ LENGTH ptrs <= 24 /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_pack_start pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_pack_finish pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R10; R11] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(workspace,4 * LENGTH fs);
                  memory :> bytes(word_add workspace (word 512),4 * LENGTH rs)])`,
  REWRITE_TAC[SOME_FLAGS; ordinary_adapter_exclusions; ordinary_pack_valid;
              ordinary_pack_start; ordinary_pack_finish; ordinary_pack_data;
              ordinary_pack_saved; ordinary_adapter_sources; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPUTE_LENGTH_RULE flat_fire_mc;
                              COMPUTE_LENGTH_RULE ordinary_flat_mc]) THEN
  VAL_INT64_TAC `LENGTH(ptrs:int64 list)` THEN
  VAL_INT64_TAC `LENGTH(fs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(rs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ENSURES_WHILE_UP2_TAC `LENGTH(ptrs:int64 list)` `pc + 0x23e` `pc + 0x272`
   `\i s. ordinary_pack_inv pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 i s` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[ordinary_pack_inv; ordinary_pack_start; flat_prefix;
                WORDLIST_FROM_MEMORY_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[ordinary_pack_inv] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "a0" THEN
    SUBGOAL_THEN `i + 1 < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `EL i (rs:int32 list) = word (4 * i)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `read (memory :> bytes64 (word_add premises (word (8 * i)))) a0 =
        EL i (ptrs:int64 list)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ORDINARY_READ64 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add workspace (word 512),4 * i)
        (word_add (word_add workspace (word 512)) (word (4 * i)),4)`
    ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
    X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--4) THEN
    ENSURES_WHILE_UP2_TAC `4` `pc + 0x254` `pc + 0x269`
     `\j s. ordinary_copy_inv pc call premises constants guards make workspace
               ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
               init_rbx init_r12 init_r13 init_r14 init_r15 i j s` THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[ordinary_copy_inv; flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES;
                  ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "b0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(REWRITE_RULE[ADD1]
       (ISPECL [`word_add workspace (word 512):int64`; `i:num`;
                `rs:int32 list`; `a0:x86state`; `b0:x86state`]
               FLAT_WORDLIST_PREFIX_32)) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[];
          REWRITE_TAC[WORDLIST_FROM_MEMORY_32] THEN
          READ_OVER_WRITE_ORTHOGONAL_TAC;
          ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST];
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      REWRITE_TAC[ordinary_copy_inv] THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "c0" THEN
      SUBGOAL_THEN `j + 1 < 2 EXP 64` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `wordlist_from_memory(EL i (ptrs:int64 list),4) c0 = EL i ps`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `j < LENGTH(EL i (ps:(int32 list) list))` ASSUME_TAC THENL
       [ASM_MESON_TAC[ALL_EL]; ALL_TAC] THEN
      SUBGOAL_THEN
       `read (memory :> bytes32
          (word_add (EL i ptrs) (word (4 * j)))) c0 = EL j (EL i ps)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `EL (4 * i + j) (fs:int32 list) = EL j (EL i ps)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `nonoverlapping (workspace,4 * (4 * i + j))
          (word_add workspace (word (4 * (4 * i + j))),4)`
      ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
      X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `wordlist_from_memory(workspace,4 * i + (j + 1)) c5 =
          flat_prefix (4 * i + (j + 1)) (fs:int32 list)`
      ASSUME_TAC THENL
       [MP_TAC(REWRITE_RULE[ADD1; ARITH_RULE `4 * i + SUC j = 4 * i + j + 1`]
         (ISPECL [`workspace:int64`; `4 * i + j`; `fs:int32 list`;
                  `c0:x86state`; `c5:x86state`] FLAT_WORDLIST_PREFIX_32)) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [ASM_ARITH_TAC;
            ASM_REWRITE_TAC[];
            REWRITE_TAC[WORDLIST_FROM_MEMORY_32] THEN
            READ_OVER_WRITE_ORTHOGONAL_TAC;
            ASM_REWRITE_TAC[]];
          ASM_REWRITE_TAC[ARITH_RULE `4 * i + SUC j = 4 * i + (j + 1)`]];
        ASM_REWRITE_TAC[ARITH_RULE `4 * i + (j + 1) = 4 * i + j + 1`] THEN
        CONJ_TAC THENL [ALL_TAC; WORD_ARITH_TAC] THEN
        SUBGOAL_THEN `j + 1 < 4 <=> ~(j + 1 = 4)`
         (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC];
      REWRITE_TAC[ordinary_copy_inv; ordinary_pack_inv] THEN
      ENSURES_INIT_TAC "d0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `4 * i + 4 = 4 * (i + 1)`] THEN
      CONJ_TAC THENL [ALL_TAC; WORD_ARITH_TAC] THEN
      SUBGOAL_THEN
       `i + 1 < LENGTH(ptrs:int64 list) <=> ~(i + 1 = LENGTH ptrs)`
       (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC];
    REWRITE_TAC[ordinary_pack_inv; ordinary_pack_finish] THEN
    X86_SIM_TAC ORDINARY_FLAT_EXEC [1] THEN ASM_REWRITE_TAC[] THEN
    FLAT_ZX_TAC]);;

let ORDINARY_ADAPTER_PACK_FINISH = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    LENGTH ptrs <= 24 /\ LENGTH cs <= 32 /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_pack_finish pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_call pc (if LENGTH ptrs = 0 then init_r12 else premises)
             guards make workspace fs rs gs ms ds zs
             (LENGTH cs) stackpointer init_rbp init_rbx init_r12 init_r13 init_r14
             init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; R8; R9] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(workspace,4 * LENGTH fs);
                  memory :> bytes(word_add workspace (word 512),4 * LENGTH rs);
                  memory :> bytes(word_sub stackpointer (word 56),16)])`,
  REWRITE_TAC[SOME_FLAGS; ordinary_adapter_exclusions; ordinary_pack_valid;
              ordinary_pack_finish; ordinary_adapter_call; ordinary_pack_data;
              ordinary_pack_saved; ordinary_adapter_sources; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; C_RETURN; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPUTE_LENGTH_RULE flat_fire_mc;
                              COMPUTE_LENGTH_RULE ordinary_flat_mc]) THEN
  VAL_INT64_TAC `LENGTH(ptrs:int64 list)` THEN
  VAL_INT64_TAC `LENGTH(cs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(fs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(rs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  REWRITE_TAC[ordinary_pack_inv] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `EL (LENGTH ptrs) (rs:int32 list) = word (4 * LENGTH ptrs)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `nonoverlapping (word_add workspace (word 512),4 * LENGTH ptrs)
      (word_add (word_add workspace (word 512)) (word (4 * LENGTH ptrs)),4)`
  ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_STEPS_TAC ORDINARY_FLAT_EXEC [1] THEN
  SUBGOAL_THEN
   `wordlist_from_memory(word_add workspace (word 512),LENGTH ptrs + 1) s1 =
      (rs:int32 list)`
  ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[ADD1]
     (ISPECL [`word_add workspace (word 512):int64`; `LENGTH(ptrs:int64 list)`;
              `rs:int32 list`; `s0:x86state`; `s1:x86state`]
             FLAT_WORDLIST_PREFIX_32)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[];
        REWRITE_TAC[WORDLIST_FROM_MEMORY_32] THEN READ_OVER_WRITE_ORTHOGONAL_TAC;
        ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST];
      ASM_REWRITE_TAC[FLAT_PREFIX_ALL]];
    ALL_TAC] THEN
  X86_STEPS_TAC ORDINARY_FLAT_EXEC [2] THEN
  ASM_CASES_TAC `LENGTH(cs:int32 list) = 0` THENL
   [X86_STEPS_TAC ORDINARY_FLAT_EXEC [3] THEN
    X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[FLAT_PREFIX_ALL];
    SUBGOAL_THEN `0 < LENGTH(cs:int32 list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    X86_STEPS_TAC ORDINARY_FLAT_EXEC (3--6) THEN
    ENSURES_WHILE_UP2_TAC `LENGTH(cs:int32 list)` `pc + 0x2a0` `pc + 0x2b0`
     `\j s. ordinary_const_inv pc call premises constants guards make workspace
               ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
               init_rbx init_r12 init_r13 init_r14 init_r15 j s` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[ordinary_const_inv; ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "a0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      REWRITE_TAC[ordinary_const_inv] THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "b0" THEN
      SUBGOAL_THEN `j + 1 < 2 EXP 64` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `read (memory :> bytes32 (word_add constants (word (4 * j)))) b0 =
          EL j (cs:int32 list)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `EL (4 * LENGTH ptrs + j) (fs:int32 list) = EL j cs` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `nonoverlapping (workspace,4 * (4 * LENGTH ptrs + j))
          (word_add workspace (word (4 * (4 * LENGTH ptrs + j))),4)`
      ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
      X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `wordlist_from_memory(workspace,4 * LENGTH ptrs + (j + 1)) b5 =
          flat_prefix (4 * LENGTH ptrs + (j + 1)) (fs:int32 list)`
      ASSUME_TAC THENL
       [MP_TAC(REWRITE_RULE[ADD1;
          ARITH_RULE `4 * n + SUC j = 4 * n + j + 1`]
         (ISPECL [`workspace:int64`; `4 * LENGTH(ptrs:int64 list) + j`;
                  `fs:int32 list`; `b0:x86state`; `b5:x86state`]
                 FLAT_WORDLIST_PREFIX_32)) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [ASM_ARITH_TAC;
            ASM_REWRITE_TAC[];
            REWRITE_TAC[WORDLIST_FROM_MEMORY_32] THEN
            READ_OVER_WRITE_ORTHOGONAL_TAC;
            ASM_REWRITE_TAC[]];
          ASM_REWRITE_TAC[ARITH_RULE `4 * n + SUC j = 4 * n + (j + 1)`]];
        ASM_REWRITE_TAC[ARITH_RULE `4 * n + (j + 1) = 4 * n + j + 1`] THEN
        CONJ_TAC THENL [ALL_TAC; WORD_ARITH_TAC] THEN
        SUBGOAL_THEN `j + 1 < LENGTH(cs:int32 list) <=> ~(j + 1 = LENGTH cs)`
         (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC];
      REWRITE_TAC[ordinary_const_inv] THEN
      ENSURES_INIT_TAC "c0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[FLAT_PREFIX_ALL]]]);;

let ORDINARY_ADAPTER_PACK_FINISH_SOURCES = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    LENGTH ptrs <= 24 /\ LENGTH cs <= 32 /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_pack_finish pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_call pc
             (if LENGTH ptrs = 0 then init_r12 else premises) guards make workspace
             fs rs gs ms ds zs (LENGTH cs) stackpointer init_rbp init_rbx init_r12
             init_r13 init_r14 init_r15 s /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC `\s. ordinary_pack_finish pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    ordinary_adapter_sources call premises constants guards make workspace ptrs ps
      cs gs ms s` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ordinary_pack_finish; ordinary_pack_inv; ordinary_pack_data] THEN
    MESON_TAC[];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN CONJ_TAC THENL
   [REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC;
    MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN CONJ_TAC THENL
     [REWRITE_TAC[ordinary_adapter_sources; WORDLIST_FROM_MEMORY_32;
                  ORDINARY_WORDLIST_FROM_MEMORY_64] THEN
      REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
      REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      (ORDINARY_READ_OVER_WRITE_ORTHOGONAL_TAC ORELSE
       FAIL_TAC "PACK_SOURCE_PRESERVE");
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS] ORDINARY_ADAPTER_PACK_FINISH) THEN
      ASM_REWRITE_TAC[]]]]);;

let ORDINARY_ADAPTER_CONSTANTS = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    0 < LENGTH cs /\ LENGTH ptrs <= 24 /\ LENGTH cs <= 32 /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_const_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_prepare pc call premises constants guards make
             workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RAX; RCX; RDX; R8] ,, MAYCHANGE SOME_FLAGS ,,
       MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(workspace,4 * LENGTH fs)])`,
  REWRITE_TAC[SOME_FLAGS; ordinary_adapter_exclusions; ordinary_pack_valid;
              ordinary_const_entry; ordinary_adapter_prepare; ordinary_pack_data;
              ordinary_pack_saved; ordinary_adapter_sources; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPUTE_LENGTH_RULE flat_fire_mc;
                              COMPUTE_LENGTH_RULE ordinary_flat_mc]) THEN
  VAL_INT64_TAC `LENGTH(ptrs:int64 list)` THEN
  VAL_INT64_TAC `LENGTH(cs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(fs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(rs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--4) THEN
  ENSURES_WHILE_UP2_TAC `LENGTH(cs:int32 list)` `pc + 0x2a0` `pc + 0x2b0`
   `\j s. ordinary_const_inv pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 j s` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[ordinary_const_inv; ADD_CLAUSES] THEN
    ENSURES_INIT_TAC "a0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
    REWRITE_TAC[ordinary_const_inv] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "b0" THEN
    SUBGOAL_THEN `j + 1 < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `read (memory :> bytes32 (word_add constants (word (4 * j)))) b0 =
        EL j (cs:int32 list)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FLAT_READ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `EL (4 * LENGTH ptrs + j) (fs:int32 list) = EL j cs` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `nonoverlapping (workspace,4 * (4 * LENGTH ptrs + j))
        (word_add workspace (word (4 * (4 * LENGTH ptrs + j))),4)`
    ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
    X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `wordlist_from_memory(workspace,4 * LENGTH ptrs + (j + 1)) b5 =
        flat_prefix (4 * LENGTH ptrs + (j + 1)) (fs:int32 list)`
    ASSUME_TAC THENL
     [MP_TAC(REWRITE_RULE[ADD1;
        ARITH_RULE `4 * n + SUC j = 4 * n + j + 1`]
       (ISPECL [`workspace:int64`; `4 * LENGTH(ptrs:int64 list) + j`;
                `fs:int32 list`; `b0:x86state`; `b5:x86state`]
               FLAT_WORDLIST_PREFIX_32)) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[];
          REWRITE_TAC[WORDLIST_FROM_MEMORY_32] THEN
          READ_OVER_WRITE_ORTHOGONAL_TAC;
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[ARITH_RULE `4 * n + SUC j = 4 * n + (j + 1)`]];
      ASM_REWRITE_TAC[ARITH_RULE `4 * n + (j + 1) = 4 * n + j + 1`] THEN
      CONJ_TAC THENL [ALL_TAC; WORD_ARITH_TAC] THEN
      SUBGOAL_THEN `j + 1 < LENGTH(cs:int32 list) <=> ~(j + 1 = LENGTH cs)`
       (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC];
    REWRITE_TAC[ordinary_const_inv] THEN
    ENSURES_INIT_TAC "c0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[FLAT_PREFIX_ALL]]);;

let ORDINARY_ADAPTER_ZERO_PACK = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    LENGTH ptrs = 0 /\ (0 < LENGTH gs \/ 0 < LENGTH ms) /\
    ordinary_machine_valid call premises constants guards make workspace ptrs cs gs ms /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_pack_finish pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS; ordinary_machine_valid;
              ordinary_pack_valid; ordinary_adapter_exclusions;
              ordinary_adapter_entry; ordinary_pack_finish; ordinary_pack_data;
              ordinary_pack_saved; ordinary_adapter_sources; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPUTE_LENGTH_RULE flat_fire_mc;
                              COMPUTE_LENGTH_RULE ordinary_flat_mc]) THEN
  VAL_INT64_TAC `LENGTH(ptrs:int64 list)` THEN
  VAL_INT64_TAC `LENGTH(cs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(fs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(rs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ASM_CASES_TAC `LENGTH(cs:int32 list) = 0` THEN
  ASM_CASES_TAC `LENGTH(gs:int32 list) = 0` THEN
  ASM_CASES_TAC `LENGTH(ms:int32 list) = 0` THENL
   [ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--38) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--42) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES];
    ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--42) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--42) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--44) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES]]);;

let ORDINARY_ADAPTER_ZERO_CONSTANTS = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    LENGTH ptrs = 0 /\ 0 < LENGTH cs /\ LENGTH gs = 0 /\ LENGTH ms = 0 /\
    ordinary_machine_valid call premises constants guards make workspace ptrs cs gs ms /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_const_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS; ordinary_machine_valid;
              ordinary_pack_valid; ordinary_adapter_exclusions;
              ordinary_adapter_entry; ordinary_const_entry; ordinary_pack_data;
              ordinary_pack_saved; ordinary_adapter_sources; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPUTE_LENGTH_RULE flat_fire_mc;
                              COMPUTE_LENGTH_RULE ordinary_flat_mc]) THEN
  VAL_INT64_TAC `LENGTH(ptrs:int64 list)` THEN
  VAL_INT64_TAC `LENGTH(cs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(fs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(rs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--40) THEN
  SUBGOAL_THEN
   `wordlist_from_memory(word_add workspace (word 512),LENGTH rs) s40 =
      (rs:int32 list)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ORDINARY_SINGLE_ROW_UPDATE THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES];
      REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES];
      ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES]);;

let ORDINARY_ADAPTER_ZERO_PREPARE = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    LENGTH ptrs = 0 /\ LENGTH cs = 0 /\ LENGTH gs = 0 /\
    ordinary_machine_valid call premises constants guards make workspace ptrs cs gs ms /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_prepare pc call premises constants guards make
             workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS; ordinary_machine_valid;
              ordinary_pack_valid; ordinary_adapter_exclusions;
              ordinary_adapter_entry; ordinary_adapter_prepare; ordinary_pack_data;
              ordinary_pack_saved; ordinary_adapter_sources; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPUTE_LENGTH_RULE flat_fire_mc;
                              COMPUTE_LENGTH_RULE ordinary_flat_mc]) THEN
  SUBGOAL_THEN `(fs:int32 list) = []` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  VAL_INT64_TAC `LENGTH(ptrs:int64 list)` THEN
  VAL_INT64_TAC `LENGTH(cs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(fs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(rs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ASM_CASES_TAC `LENGTH(ms:int32 list) = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--35) THEN
    SUBGOAL_THEN
     `wordlist_from_memory(word_add workspace (word 512),LENGTH rs) s35 =
        (rs:int32 list)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ORDINARY_SINGLE_ROW_UPDATE THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES];
        REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES];
        ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST];
      ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--38) THEN
    SUBGOAL_THEN
     `wordlist_from_memory(word_add workspace (word 512),LENGTH rs) s38 =
        (rs:int32 list)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ORDINARY_SINGLE_ROW_UPDATE THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[flat_prefix; WORDLIST_FROM_MEMORY_CLAUSES];
        REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES];
        ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST];
      ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES]]);;

let ORDINARY_ADAPTER_VALID_NONZERO = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    0 < LENGTH ptrs /\
    ordinary_adapter_shape_valid call premises constants guards make workspace ptrs cs gs ms /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_scan_start pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RDI; RSI; R9; RBX; RBP; R12; R14] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(word_sub stackpointer (word 40),40)])`,
  REWRITE_TAC[SOME_FLAGS; ordinary_adapter_shape_valid; ordinary_adapter_exclusions;
              ordinary_adapter_entry; ordinary_scan_start; ordinary_scan_inv;
              ordinary_pack_data; ordinary_pack_saved; ordinary_adapter_sources;
              ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES; fst ORDINARY_FLAT_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPUTE_LENGTH_RULE flat_fire_mc;
                              COMPUTE_LENGTH_RULE ordinary_flat_mc]) THEN
  VAL_INT64_TAC `LENGTH(ptrs:int64 list)` THEN
  VAL_INT64_TAC `LENGTH(cs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(gs:int32 list)` THEN
  VAL_INT64_TAC `LENGTH(ms:int32 list)` THEN
  ASM_CASES_TAC `LENGTH(cs:int32 list) = 0` THEN
  ASM_CASES_TAC `LENGTH(gs:int32 list) = 0` THEN
  ASM_CASES_TAC `LENGTH(ms:int32 list) = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--38) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--40) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--42) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--46) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--43) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--44) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--46) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC ORDINARY_FLAT_EXEC (1--48) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let ORDINARY_ADAPTER_SCAN_NULL_ENTRY = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15 k.
    0 < LENGTH ptrs /\
    ordinary_adapter_shape_valid call premises constants guards make workspace ptrs cs gs ms /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer /\
    k < LENGTH ptrs /\ (!i. i < k ==> ~(EL i ptrs = word 0)) /\
    EL k ptrs = word 0
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC `\s. ordinary_adapter_entry pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
      init_r12 init_r13 init_r14 init_r15 s /\
    ordinary_adapter_sources call premises constants guards make workspace ptrs ps
      cs gs ms s` THEN CONJ_TAC THENL
   [REWRITE_TAC[ordinary_adapter_entry] THEN MESON_TAC[];
    MATCH_MP_TAC ENSURES_FRAME_INVARIANT THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[ordinary_adapter_exclusions; ALLPAIRS; ALL;
                                  NONOVERLAPPING_CLAUSES]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM NONOVERLAPPING_CLAUSES]) THEN
      REWRITE_TAC[ordinary_adapter_sources; WORDLIST_FROM_MEMORY_32;
                  ORDINARY_WORDLIST_FROM_MEMORY_64] THEN
      REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
      REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      (ORDINARY_READ_OVER_WRITE_ORTHOGONAL_TAC ORELSE
       FAIL_TAC "NULL_SOURCE_PRESERVE");
      MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
      EXISTS_TAC `\s. ordinary_scan_start pc call premises constants guards make
        workspace ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp
        init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
       [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN CONJ_TAC THENL
         [REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN
          MONOTONE_MAYCHANGE_TAC;
          MATCH_MP_TAC ORDINARY_ADAPTER_VALID_NONZERO THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN CONJ_TAC THENL
         [REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN
          MONOTONE_MAYCHANGE_TAC;
          MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS] ORDINARY_ADAPTER_SCAN_NULL) THEN
          ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]]]);;

let ORDINARY_ADAPTER_VALID_NONZERO_CALL = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    0 < LENGTH ptrs /\
    ordinary_machine_valid call premises constants guards make workspace ptrs cs gs ms /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_call pc premises guards make workspace fs rs gs ms ds zs
             (LENGTH cs) stackpointer init_rbp init_rbx init_r12 init_r13 init_r14
             init_r15 s /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ordinary_adapter_shape_valid call premises constants guards make
    workspace ptrs cs gs ms` ASSUME_TAC THENL
   [ASM_MESON_TAC[ordinary_machine_valid; ordinary_adapter_shape_valid]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ordinary_machine_valid; ordinary_adapter_shape_valid;
                              ordinary_pack_valid]) THEN
  MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
  EXISTS_TAC `\s. ordinary_scan_start pc call premises constants guards make
    workspace ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
    init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN CONJ_TAC THENL
     [REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC;
      MATCH_MP_TAC ORDINARY_ADAPTER_VALID_NONZERO THEN
      ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_adapter_shape_valid]];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC `\s. ordinary_pack_start pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN CONJ_TAC THENL
       [REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN
        MONOTONE_MAYCHANGE_TAC;
        MATCH_MP_TAC ORDINARY_ADAPTER_SCAN THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC];
      MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
      EXISTS_TAC `\s. ordinary_pack_finish pc call premises constants guards make
        workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
        init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
       [MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN CONJ_TAC THENL
         [REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN
          MONOTONE_MAYCHANGE_TAC;
          MATCH_MP_TAC ORDINARY_ADAPTER_PACK THEN
          ASM_REWRITE_TAC[ordinary_pack_valid] THEN ASM_ARITH_TAC];
        MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS]
          ORDINARY_ADAPTER_PACK_FINISH_SOURCES) THEN
        ASM_REWRITE_TAC[ordinary_pack_valid] THEN ASM_ARITH_TAC]]]);;

let ORDINARY_ADAPTER_ZERO_CALL = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    LENGTH ptrs = 0 /\
    ordinary_machine_valid call premises constants guards make workspace ptrs cs gs ms /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_call pc
             (if LENGTH ptrs = 0 then init_r12 else premises) guards make workspace
             fs rs gs ms ds zs (LENGTH cs) stackpointer init_rbp init_rbx init_r12
             init_r13 init_r14 init_r15 s /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ordinary_machine_valid; ordinary_pack_valid]) THEN
  ASM_CASES_TAC `LENGTH(cs:int32 list) = 0` THEN
  ASM_CASES_TAC `LENGTH(gs:int32 list) = 0` THEN
  ASM_CASES_TAC `LENGTH(ms:int32 list) = 0` THENL
   [MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC `\s. ordinary_adapter_prepare pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_ZERO_PREPARE THEN
      ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_pack_valid];
      MATCH_MP_TAC ORDINARY_ADAPTER_PREPARE_SOURCES THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC `\s. ordinary_adapter_prepare pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_ZERO_PREPARE THEN
      ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_pack_valid];
      MATCH_MP_TAC ORDINARY_ADAPTER_PREPARE_SOURCES THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC `\s. ordinary_pack_finish pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_ZERO_PACK THEN
      ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_pack_valid] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS]
        ORDINARY_ADAPTER_PACK_FINISH_SOURCES) THEN
      ASM_REWRITE_TAC[ordinary_pack_valid] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC `\s. ordinary_pack_finish pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_ZERO_PACK THEN
      ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_pack_valid] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS]
        ORDINARY_ADAPTER_PACK_FINISH_SOURCES) THEN
      ASM_REWRITE_TAC[ordinary_pack_valid] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC `\s. ordinary_adapter_prepare pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
      EXISTS_TAC `\s. ordinary_const_entry pc call premises constants guards make
        workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
        init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
       [MATCH_MP_TAC ORDINARY_ADAPTER_ZERO_CONSTANTS THEN
        ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_pack_valid] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN CONJ_TAC THENL
         [REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN
          MONOTONE_MAYCHANGE_TAC;
          MATCH_MP_TAC ORDINARY_ADAPTER_CONSTANTS THEN
          ASM_REWRITE_TAC[ordinary_pack_valid] THEN ASM_ARITH_TAC]];
      MATCH_MP_TAC ORDINARY_ADAPTER_PREPARE_SOURCES THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC `\s. ordinary_pack_finish pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_ZERO_PACK THEN
      ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_pack_valid] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS]
        ORDINARY_ADAPTER_PACK_FINISH_SOURCES) THEN
      ASM_REWRITE_TAC[ordinary_pack_valid] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC `\s. ordinary_pack_finish pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_ZERO_PACK THEN
      ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_pack_valid] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS]
        ORDINARY_ADAPTER_PACK_FINISH_SOURCES) THEN
      ASM_REWRITE_TAC[ordinary_pack_valid] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
    EXISTS_TAC `\s. ordinary_pack_finish pc call premises constants guards make
      workspace ptrs ps cs gs ms ds zs fs rs stackpointer returnaddress init_rbp
      init_rbx init_r12 init_r13 init_r14 init_r15 s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ORDINARY_ADAPTER_ZERO_PACK THEN
      ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_pack_valid] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS]
        ORDINARY_ADAPTER_PACK_FINISH_SOURCES) THEN
      ASM_REWRITE_TAC[ordinary_pack_valid] THEN ASM_ARITH_TAC]]);;

let ORDINARY_ADAPTER_VALID_CALL = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    ordinary_machine_valid call premises constants guards make workspace ptrs cs gs ms /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_call pc
             (if LENGTH ptrs = 0 then init_r12 else premises) guards make workspace
             fs rs gs ms ds zs (LENGTH cs) stackpointer init_rbp init_rbx init_r12
             init_r13 init_r14 init_r15 s /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH(ptrs:int64 list) = 0` THENL
   [MATCH_MP_TAC ORDINARY_ADAPTER_ZERO_CALL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `0 < LENGTH(ptrs:int64 list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ORDINARY_ADAPTER_VALID_NONZERO_CALL THEN
    ASM_REWRITE_TAC[]]);;

let ORDINARY_ADAPTER_VALID_AFTER_LEAF = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    flat_valid fs rs gs ms /\
    LENGTH ds = LENGTH ms /\ LENGTH zs = LENGTH ms /\
    ordinary_machine_valid call premises constants guards make workspace ptrs cs gs ms /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_return workspace fs rs
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else ds)
             (if flat_guards_hold fs rs gs then flat_selected fs rs ms else zs)
             (bitval (flat_guards_hold fs rs gs)) stackpointer returnaddress
             init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ORDINARY_ADAPTER_TRANS THEN
  EXISTS_TAC `\s. ordinary_adapter_call pc
      (if LENGTH ptrs = 0 then init_r12 else premises) guards make workspace fs rs
      gs ms ds zs (LENGTH cs) stackpointer init_rbp init_rbx init_r12 init_r13
      init_r14 init_r15 s /\
    read (memory :> bytes64 stackpointer) s = returnaddress /\
    ordinary_adapter_sources call premises constants guards make workspace ptrs ps
      cs gs ms s` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ORDINARY_ADAPTER_VALID_CALL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN CONJ_TAC THENL
     [REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC;
      MATCH_MP_TAC (REWRITE_RULE[SOME_FLAGS]
        ORDINARY_ADAPTER_AFTER_LEAF_SOURCES) THEN
      ASM_REWRITE_TAC[ordinary_machine_valid; ordinary_pack_valid] THEN
      ASM_ARITH_TAC]]);;

let ORDINARY_ADAPTER_STATUS_TAC p c defs th =
  MATCH_MP_TAC ORDINARY_ADAPTER_STATUS_SOURCES THEN
  EXISTS_TAC p THEN EXISTS_TAC c THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC(ordinary_adapter_entry::defs) THEN MESON_TAC[];
    REWRITE_TAC[ordinary_adapter_frame; SOME_FLAGS] THEN
    MONOTONE_MAYCHANGE_TAC;
    MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];;

let ORDINARY_ADAPTER_UNSUPPORTED = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    ~(ordinary_machine_valid call premises constants guards make workspace ptrs
        cs gs ms) /\
    LENGTH ptrs < 2 EXP 64 /\ LENGTH cs < 2 EXP 64 /\
    LENGTH gs < 2 EXP 64 /\ LENGTH ms < 2 EXP 64 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. ordinary_adapter_status_return 2 stackpointer returnaddress init_rbp
             init_rbx init_r12 init_r13 init_r14 init_r15 s /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ordinary_machine_valid]) THEN
  ASM_CASES_TAC `call = word 0` THENL
   [ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_early pc call workspace (LENGTH ptrs) stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RAX; RDI; RSI; R9] ,, MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_early] ORDINARY_ADAPTER_EARLY_UNSUPPORTED; ALL_TAC] THEN
  ASM_CASES_TAC `workspace = word 0` THENL
   [ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_early pc call workspace (LENGTH ptrs) stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RAX; RDI; RSI; R9] ,, MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_early] ORDINARY_ADAPTER_EARLY_UNSUPPORTED; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(ptrs:int64 list) <= 24` THENL
   [ALL_TAC;
    ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_early pc call workspace (LENGTH ptrs) stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RAX; RDI; RSI; R9] ,, MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_early] ORDINARY_ADAPTER_EARLY_UNSUPPORTED] THEN
  ASM_CASES_TAC `LENGTH(cs:int32 list) <= 32` THENL
   [ALL_TAC;
    ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_counts_entry pc call workspace (LENGTH ptrs) (LENGTH cs)
         (LENGTH gs) (LENGTH ms) stackpointer returnaddress init_rbp init_rbx
         init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
        MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_counts_entry] ORDINARY_ADAPTER_BAD_COUNTS] THEN
  ASM_CASES_TAC `LENGTH(gs:int32 list) <= 32` THENL
   [ALL_TAC;
    ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_counts_entry pc call workspace (LENGTH ptrs) (LENGTH cs)
         (LENGTH gs) (LENGTH ms) stackpointer returnaddress init_rbp init_rbx
         init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
        MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_counts_entry] ORDINARY_ADAPTER_BAD_COUNTS] THEN
  ASM_CASES_TAC `LENGTH(ms:int32 list) <= 32` THENL
   [ALL_TAC;
    ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_counts_entry pc call workspace (LENGTH ptrs) (LENGTH cs)
         (LENGTH gs) (LENGTH ms) stackpointer returnaddress init_rbp init_rbx
         init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
        MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_counts_entry] ORDINARY_ADAPTER_BAD_COUNTS] THEN
  ASM_CASES_TAC `LENGTH(ptrs:int64 list) = 0 \/ ~(premises = word 0)` THENL
   [ALL_TAC;
    ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_pointer_entry pc call premises constants guards make
         workspace (LENGTH ptrs) (LENGTH cs) (LENGTH gs) (LENGTH ms) stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
        MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_pointer_entry] ORDINARY_ADAPTER_NULL_PREMISES] THEN
  ASM_CASES_TAC `LENGTH(cs:int32 list) = 0 \/ ~(constants = word 0)` THENL
   [ALL_TAC;
    ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_pointer_entry pc call premises constants guards make
         workspace (LENGTH ptrs) (LENGTH cs) (LENGTH gs) (LENGTH ms) stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
        MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_pointer_entry] ORDINARY_ADAPTER_NULL_CONSTANTS] THEN
  ASM_CASES_TAC `LENGTH(gs:int32 list) = 0 \/ ~(guards = word 0)` THENL
   [ALL_TAC;
    ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_pointer_entry pc call premises constants guards make
         workspace (LENGTH ptrs) (LENGTH cs) (LENGTH gs) (LENGTH ms) stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
        MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_pointer_entry] ORDINARY_ADAPTER_NULL_GUARDS] THEN
  ASM_CASES_TAC `LENGTH(ms:int32 list) = 0 \/ ~(make = word 0)` THENL
   [ALL_TAC;
    ORDINARY_ADAPTER_STATUS_TAC
      `\s. ordinary_adapter_pointer_entry pc call premises constants guards make
         workspace (LENGTH ptrs) (LENGTH cs) (LENGTH gs) (LENGTH ms) stackpointer
         returnaddress init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s`
      `(MAYCHANGE [RIP; RSP; RAX; RDI; RSI; RCX; R9; RBX; RBP; R12; R14] ,,
        MAYCHANGE SOME_FLAGS)`
      [ordinary_adapter_pointer_entry] ORDINARY_ADAPTER_NULL_MAKE] THEN
  ASM_CASES_TAC `ALL (\(p:int64). ~(p = word 0)) ptrs` THENL
   [ASM_MESON_TAC[ordinary_machine_valid]; ALL_TAC] THEN
  MP_TAC(SPEC `ptrs:int64 list` ORDINARY_FIRST_NULL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC ORDINARY_ADAPTER_SCAN_NULL_ENTRY THEN
  EXISTS_TAC `k:num` THEN
  ASM_REWRITE_TAC[ordinary_adapter_shape_valid] THEN ASM_ARITH_TAC);;

let ORDINARY_ADAPTER_MACHINE_CORRECT = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (cs:int32 list) (gs:int32 list) (ms:int32 list)
      (ds:int32 list) (zs:int32 list) (fs:int32 list) (rs:int32 list)
      stackpointer returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
      init_r15.
    LENGTH ptrs < 2 EXP 64 /\ LENGTH cs < 2 EXP 64 /\
    LENGTH gs < 2 EXP 64 /\ LENGTH ms < 2 EXP 64 /\
    ordinary_pack_valid ptrs ps cs fs rs /\
    LENGTH fs < 2 EXP 58 /\ LENGTH rs < 2 EXP 58 /\
    LENGTH gs < 2 EXP 58 /\ LENGTH ms < 2 EXP 58 /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs gs ms fs rs stackpointer /\
    (ordinary_machine_valid call premises constants guards make workspace ptrs
       cs gs ms
     ==> flat_valid fs rs gs ms /\
         LENGTH ds = LENGTH ms /\ LENGTH zs = LENGTH ms)
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs gs ms ds zs stackpointer returnaddress init_rbp init_rbx
             init_r12 init_r13 init_r14 init_r15 s)
      (\s. (if ordinary_machine_valid call premises constants guards make workspace
                 ptrs cs gs ms
            then ordinary_adapter_return workspace fs rs
                   (if flat_guards_hold fs rs gs then flat_selected fs rs ms else ds)
                   (if flat_guards_hold fs rs gs then flat_selected fs rs ms else zs)
                   (bitval (flat_guards_hold fs rs gs)) stackpointer returnaddress
                   init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s
            else ordinary_adapter_status_return 2 stackpointer returnaddress init_rbp
                   init_rbx init_r12 init_r13 init_r14 init_r15 s) /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs gs ms s)
      (ordinary_adapter_frame workspace fs rs ms stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `ordinary_machine_valid call premises constants guards make
    workspace ptrs cs gs ms` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC ORDINARY_ADAPTER_VALID_AFTER_LEAF THEN ASM_MESON_TAC[];
    MATCH_MP_TAC ORDINARY_ADAPTER_UNSUPPORTED THEN ASM_REWRITE_TAC[]]);;

let ORDINARY_PACK_VALID_SPEC = prove
 (`!ptrs ps ars cs.
    LENGTH ps = LENGTH ptrs /\ ordinary_row_valid ps ars
    ==> ordinary_pack_valid ptrs ps cs (ordinary_fields ps cs) (ordinary_rows ps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ordinary_pack_valid; ORDINARY_FIELDS_LENGTH;
              ORDINARY_ROWS_LENGTH] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[ordinary_row_valid];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ORDINARY_PREMISE_FIELDS_EL THEN
    EXISTS_TAC `ars:num list` THEN ASM_MESON_TAC[ordinary_row_valid];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ORDINARY_CONSTANT_FIELDS_EL THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ORDINARY_ROWS_EL THEN
    ASM_REWRITE_TAC[]]);;

let ORDINARY_ADAPTER_MC_CORRECT = prove
 (`!pc call premises constants guards make workspace (ptrs:int64 list)
      (ps:(int32 list) list) (ars:num list) (cs:int32 list)
      (ogs:(num#num#num#num) list) (oms:(num#num) list)
      (ds:int32 list) (zs:int32 list) stackpointer returnaddress
      init_rbp init_rbx init_r12 init_r13 init_r14 init_r15.
    ordinary_valid ps ars cs ogs oms /\
    LENGTH ps = LENGTH ptrs /\
    LENGTH ds = LENGTH oms /\ LENGTH zs = LENGTH oms /\
    ordinary_adapter_exclusions pc call premises constants guards make workspace
      ptrs cs (ordinary_pack_guards ogs) (ordinary_pack_makes oms)
      (ordinary_fields ps cs) (ordinary_rows ps) stackpointer
    ==> ensures x86
      (\s. ordinary_adapter_entry pc call premises constants guards make workspace
             ptrs ps cs (ordinary_pack_guards ogs) (ordinary_pack_makes oms) ds zs
             stackpointer returnaddress init_rbp init_rbx init_r12 init_r13
             init_r14 init_r15 s)
      (\s. (if ordinary_machine_valid call premises constants guards make workspace
                 ptrs cs (ordinary_pack_guards ogs) (ordinary_pack_makes oms)
            then ordinary_adapter_return workspace (ordinary_fields ps cs)
                   (ordinary_rows ps)
                   (if ordinary_guards_hold ps cs ogs
                    then ordinary_selected ps cs oms else ds)
                   (if ordinary_guards_hold ps cs ogs
                    then ordinary_selected ps cs oms else zs)
                   (bitval (ordinary_guards_hold ps cs ogs)) stackpointer
                   returnaddress init_rbp init_rbx init_r12 init_r13 init_r14
                   init_r15 s
            else ordinary_adapter_status_return 2 stackpointer returnaddress init_rbp
                   init_rbx init_r12 init_r13 init_r14 init_r15 s) /\
           ordinary_adapter_sources call premises constants guards make workspace
             ptrs ps cs (ordinary_pack_guards ogs) (ordinary_pack_makes oms) s /\
           (ordinary_machine_valid call premises constants guards make workspace
                ptrs cs (ordinary_pack_guards ogs) (ordinary_pack_makes oms)
            ==> ordinary_fire_spec ps cs ogs oms =
                if ordinary_guards_hold ps cs ogs
                then SOME(wordlist_from_memory
                    (word_add workspace (word 612),
                     LENGTH(ordinary_pack_makes oms)) s)
                else NONE))
      (ordinary_adapter_frame workspace (ordinary_fields ps cs) (ordinary_rows ps)
        (ordinary_pack_makes oms) stackpointer)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(ps:(int32 list) list) <= 24 /\ LENGTH(cs:int32 list) <= 32 /\
    LENGTH(ogs:(num#num#num#num) list) <= 32 /\
    LENGTH(oms:(num#num) list) <= 32` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ordinary_valid]; ALL_TAC] THEN
  SUBGOAL_THEN `ordinary_pack_valid ptrs ps cs (ordinary_fields ps cs)
    (ordinary_rows ps)` ASSUME_TAC THENL
   [MATCH_MP_TAC ORDINARY_PACK_VALID_SPEC THEN EXISTS_TAC `ars:num list` THEN
    ASM_MESON_TAC[ordinary_valid]; ALL_TAC] THEN
  SUBGOAL_THEN `flat_guards_hold (ordinary_fields ps cs) (ordinary_rows ps)
    (ordinary_pack_guards ogs) = ordinary_guards_hold ps cs ogs` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_PACKED_GUARDS_HOLD]; ALL_TAC] THEN
  SUBGOAL_THEN `flat_selected (ordinary_fields ps cs) (ordinary_rows ps)
    (ordinary_pack_makes oms) = ordinary_selected ps cs oms` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORDINARY_PACKED_SELECTED]; ALL_TAC] THEN
  ENSURES_POSTCONDITION_TAC
   `\s. (if ordinary_machine_valid call premises constants guards make workspace
              ptrs cs (ordinary_pack_guards ogs) (ordinary_pack_makes oms)
         then ordinary_adapter_return workspace (ordinary_fields ps cs)
                (ordinary_rows ps)
                (if flat_guards_hold (ordinary_fields ps cs) (ordinary_rows ps)
                     (ordinary_pack_guards ogs)
                 then flat_selected (ordinary_fields ps cs) (ordinary_rows ps)
                      (ordinary_pack_makes oms) else ds)
                (if flat_guards_hold (ordinary_fields ps cs) (ordinary_rows ps)
                     (ordinary_pack_guards ogs)
                 then flat_selected (ordinary_fields ps cs) (ordinary_rows ps)
                      (ordinary_pack_makes oms) else zs)
                (bitval (flat_guards_hold (ordinary_fields ps cs) (ordinary_rows ps)
                  (ordinary_pack_guards ogs))) stackpointer returnaddress
                init_rbp init_rbx init_r12 init_r13 init_r14 init_r15 s
         else ordinary_adapter_status_return 2 stackpointer returnaddress init_rbp
                init_rbx init_r12 init_r13 init_r14 init_r15 s) /\
        ordinary_adapter_sources call premises constants guards make workspace
          ptrs ps cs (ordinary_pack_guards ogs) (ordinary_pack_makes oms) s` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC ORDINARY_ADAPTER_MACHINE_CORRECT THEN
    ASM_REWRITE_TAC[ordinary_pack_guards; ordinary_pack_makes; LENGTH_MAP;
                    ORDINARY_FIELDS_LENGTH; ORDINARY_ROWS_LENGTH] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC;
      ASM_REWRITE_TAC[GSYM ordinary_pack_guards; GSYM ordinary_pack_makes];
      DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC ORDINARY_PACKED_VALID THEN EXISTS_TAC `ars:num list` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[ordinary_pack_makes; LENGTH_MAP]]]] THEN
  GEN_TAC THEN
  ASM_CASES_TAC `ordinary_machine_valid call premises constants guards make
    workspace ptrs cs (ordinary_pack_guards ogs) (ordinary_pack_makes oms)` THEN
  ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ordinary_adapter_return]) THEN
    ASM_CASES_TAC `ordinary_guards_hold ps cs ogs` THEN
    ASM_REWRITE_TAC[ordinary_fire_spec];
    ASM_REWRITE_TAC[]]);;





