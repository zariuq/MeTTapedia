(* Packed 32-bit row descriptors and their mathematical firing contract.
   No instruction image, processor state or object file is required. *)

needs "Library/words.ml";;
needs "Library/bitmatch.ml";;
needs "common/overlap.ml";;
needs "common/for_hollight.ml";;
needs "common/words2.ml";;
needs "common/misc.ml";;

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

