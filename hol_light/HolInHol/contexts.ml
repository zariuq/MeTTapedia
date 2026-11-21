(* ========================================================================= *)
(* Contexts: valid updates and extensions preserve theory well-formedness,  *)
(* and well-formedness and provability are monotone under extension         *)
(* (Candle's updates_theory_ok, extends_theory_ok, term_ok_extend,           *)
(* extends_sub, extends_proves).                                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Inclusion of association lists, read through first-match lookup.        *)
(* ------------------------------------------------------------------------- *)

let hsubmap = new_definition
 `hsubmap (l1:(A#B)list) l2 <=>
    !k v. hlookup l1 k = SOME v ==> hlookup l2 k = SOME v`;;

let HSUBMAP_REFL = prove
 (`!l:(A#B)list. hsubmap l l`,
  REWRITE_TAC[hsubmap]);;

let HSUBMAP_TRANS = prove
 (`!l1 l2 l3:(A#B)list. hsubmap l1 l2 /\ hsubmap l2 l3 ==> hsubmap l1 l3`,
  REWRITE_TAC[hsubmap] THEN MESON_TAC[]);;

let HLOOKUP_APPEND = prove
 (`!l1 l2 (k:A).
        hlookup (APPEND l1 l2) k =
        if hlookup l1 k = (NONE:B option) then hlookup l2 k else hlookup l1 k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; hlookup] THEN
  SPEC_TAC(`h:A#B`,`p:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[hlookup] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let HLOOKUP_NONE = prove
 (`!l (k:A). hlookup l k = (NONE:B option) <=> ~MEM k (MAP FST l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[hlookup; MAP; MEM] THEN
  SPEC_TAC(`h:A#B`,`p:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[hlookup; FST] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let HLOOKUP_MEM = prove
 (`!l (k:A) (v:B). hlookup l k = SOME v ==> MEM (k,v) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[hlookup; MEM; option_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`p:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[hlookup; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[]);;

let HLOOKUP_DISTINCT_MEM = prove
 (`!l (k:A) (v:B). HALL_DISTINCT (MAP FST l) /\ MEM (k,v) l
                   ==> hlookup l k = SOME v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  SPEC_TAC(`h:A#B`,`p:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[hlookup; MAP; HALL_DISTINCT; PAIR_EQ; FST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `~MEM (k:A) (MAP FST (t:(A#B)list))` THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[FST];
    ASM_MESON_TAC[]]);;

let HSUBMAP_APPEND = prove
 (`!l1 l2:(A#B)list.
        hsubmap l2 (APPEND l1 l2) <=>
        !k v. hlookup l2 k = SOME v
              ==> hlookup l1 k = NONE \/ hlookup l1 k = SOME v`,
  REWRITE_TAC[hsubmap; HLOOKUP_APPEND] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`k:A`; `v:B`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`k:A`; `v:B`]) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let HSUBMAP_APPEND_FRESH = prove
 (`!l1 l2:(A#B)list.
        (!k. MEM k (MAP FST l1) ==> hlookup l2 k = NONE)
        ==> hsubmap l2 (APPEND l1 l2)`,
  REWRITE_TAC[HSUBMAP_APPEND] THEN
  MESON_TAC[HLOOKUP_NONE; option_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* Well-formedness is monotone in the signature.                           *)
(* ------------------------------------------------------------------------- *)

let HTYPE_OK_MONO = prove
 (`!tys1 tys2 ty. hsubmap tys1 tys2 /\ htype_ok tys1 ty ==> htype_ok tys2 ty`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC HOLTYPE_INDUCT THEN REWRITE_TAC[HTYPE_OK] THEN
  MAP_EVERY X_GEN_TAC [`s:string`; `tys:holtype list`] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[hsubmap]; ASM_MESON_TAC[]]);;

let HTERM_OK_MONO = prove
 (`!sig1 sig2 tm.
        hsubmap (FST sig1) (FST sig2) /\ hsubmap (SND sig1) (SND sig2) /\
        hterm_ok sig1 tm
        ==> hterm_ok sig2 tm`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC holterm_INDUCT THEN
  REWRITE_TAC[hterm_ok] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HTYPE_OK_MONO];
    REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `ty0:holtype` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ty0:holtype` THEN ASM_MESON_TAC[HTYPE_OK_MONO; hsubmap];
    MESON_TAC[];
    ASM_MESON_TAC[HTYPE_OK_MONO]]);;

let HIS_STD_SIG_MONO = prove
 (`!sig1 sig2.
        hsubmap (FST sig1) (FST sig2) /\ hsubmap (SND sig1) (SND sig2) /\
        his_std_sig sig1
        ==> his_std_sig sig2`,
  REWRITE_TAC[his_std_sig; hsubmap] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Valid updates and extensions keep every old lookup and every old axiom. *)
(* ------------------------------------------------------------------------- *)

let HTYPE_LIST_CONS = prove
 (`!upd ctxt. htype_list (CONS upd ctxt) =
              APPEND (htypes_of_upd upd) (htype_list ctxt)`,
  REWRITE_TAC[htype_list; MAP; hflat]);;

let HCONST_LIST_CONS = prove
 (`!upd ctxt. hconst_list (CONS upd ctxt) =
              APPEND (hconsts_of_upd upd) (hconst_list ctxt)`,
  REWRITE_TAC[hconst_list; MAP; hflat]);;

let HAXIOM_LIST_CONS = prove
 (`!upd ctxt. haxiom_list (CONS upd ctxt) =
              APPEND (haxioms_of_upd upd) (haxiom_list ctxt)`,
  REWRITE_TAC[haxiom_list; MAP; hflat]);;

let MAP_FST_PAIR_MAP = prove
 (`!(f:B->C) (l:(A#B)list). MAP FST (MAP (\(s,t). (s,f t)) l) = MAP FST l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  SPEC_TAC(`h:A#B`,`p:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[FST]);;

let HUPDATES_SUBMAP = prove
 (`!upd ctxt.
        upd hupdates ctxt
        ==> hsubmap (htype_list ctxt) (htype_list (CONS upd ctxt)) /\
            hsubmap (hconst_list ctxt) (hconst_list (CONS upd ctxt))`,
  MATCH_MP_TAC hupdates_INDUCT THEN
  REWRITE_TAC[HTYPE_LIST_CONS; HCONST_LIST_CONS] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC HSUBMAP_APPEND_FRESH THEN
  REWRITE_TAC[htypes_of_upd; hconsts_of_upd; LET_DEF; LET_END_DEF;
              MAP; MEM; FST; MAP_FST_PAIR_MAP] THEN
  ASM_MESON_TAC[]);;

let HUPDATES_AXIOMS = prove
 (`!upd ctxt p. p IN SND (hthyof ctxt) ==> p IN SND (hthyof (CONS upd ctxt))`,
  REWRITE_TAC[hthyof; IN_SET_OF_LIST; HAXIOM_LIST_CONS; MEM_APPEND] THEN
  MESON_TAC[]);;

let HEXTENDS_SUBMAP = prove
 (`!c2 c1. c2 hextends c1
           ==> hsubmap (htype_list c1) (htype_list c2) /\
               hsubmap (hconst_list c1) (hconst_list c2) /\
               (!p. p IN SND (hthyof c1) ==> p IN SND (hthyof c2))`,
  MATCH_MP_TAC hextends_INDUCT THEN REWRITE_TAC[HSUBMAP_REFL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HUPDATES_SUBMAP) THEN
  ASM_MESON_TAC[HSUBMAP_TRANS; HUPDATES_AXIOMS]);;

(* ------------------------------------------------------------------------- *)
(* The string order is a strict total order (by character code, as OCaml   *)
(* compares strings), and HSTRING_SORT lists the distinct members of a     *)
(* list in strictly increasing order.                                      *)
(* ------------------------------------------------------------------------- *)

let HBIT_SPLIT = prove
 (`!a b m n k. m < k /\ n < k
               ==> ((if a then k else 0) + m = (if b then k else 0) + n <=>
                    (a <=> b) /\ m = n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`a:bool`; `b:bool`] THEN REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let HBITS_BOUND = prove
 (`(!a7. (if a7 then 1 else 0) < 2) /\
   (!a6 a7. (if a6 then 2 else 0) + (if a7 then 1 else 0) < 4) /\
   (!a5 a6 a7. (if a5 then 4 else 0) + (if a6 then 2 else 0) +
               (if a7 then 1 else 0) < 8) /\
   (!a4 a5 a6 a7. (if a4 then 8 else 0) + (if a5 then 4 else 0) +
                  (if a6 then 2 else 0) + (if a7 then 1 else 0) < 16) /\
   (!a3 a4 a5 a6 a7. (if a3 then 16 else 0) + (if a4 then 8 else 0) +
                     (if a5 then 4 else 0) + (if a6 then 2 else 0) +
                     (if a7 then 1 else 0) < 32) /\
   (!a2 a3 a4 a5 a6 a7. (if a2 then 32 else 0) + (if a3 then 16 else 0) +
                        (if a4 then 8 else 0) + (if a5 then 4 else 0) +
                        (if a6 then 2 else 0) + (if a7 then 1 else 0) < 64) /\
   (!a1 a2 a3 a4 a5 a6 a7.
        (if a1 then 64 else 0) + (if a2 then 32 else 0) +
        (if a3 then 16 else 0) + (if a4 then 8 else 0) +
        (if a5 then 4 else 0) + (if a6 then 2 else 0) +
        (if a7 then 1 else 0) < 128)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

let HCHAR_CODE_INJ = prove
 (`!c d. hchar_code c = hchar_code d <=> c = d`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  STRUCT_CASES_TAC(SPEC `c:char` (cases "char")) THEN
  STRUCT_CASES_TAC(SPEC `d:char` (cases "char")) THEN
  REWRITE_TAC[hchar_code; injectivity "char"] THEN
  SIMP_TAC[HBIT_SPLIT; HBITS_BOUND] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ] THEN
  CONV_TAC TAUT);;

let HSTRING_LT_IRREFL = prove
 (`!s. ~hstring_lt s s`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[hstring_lt; LT_REFL]);;

let HSTRING_LT_TRANS = prove
 (`!s1 s2 s3. hstring_lt s1 s2 /\ hstring_lt s2 s3 ==> hstring_lt s1 s3`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `s2:char list` THEN X_GEN_TAC `s3:char list` THEN
  STRUCT_CASES_TAC(ISPEC `s2:char list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `s3:char list` list_CASES) THEN
  REWRITE_TAC[hstring_lt; NOT_CONS_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LT_TRANS]);;

let HSTRING_LT_TOTAL = prove
 (`!s1 s2. hstring_lt s1 s2 \/ s1 = s2 \/ hstring_lt s2 s1`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `s2:char list` THEN
  STRUCT_CASES_TAC(ISPEC `s2:char list` list_CASES) THEN
  REWRITE_TAC[hstring_lt; NOT_CONS_NIL; CONS_11] THEN
  DISJ_CASES_TAC(SPECL [`hchar_code h`; `hchar_code h'`] LT_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th))) THEN
  REWRITE_TAC[HCHAR_CODE_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[LT_REFL]);;

let hstring_sorted = define
 `(hstring_sorted [] <=> T) /\
  (hstring_sorted (CONS h t) <=> ALL (hstring_lt h) t /\ hstring_sorted t)`;;

let HSTRING_SORTED_APPEND = prove
 (`!l1 l2. hstring_sorted (APPEND l1 l2) <=>
           hstring_sorted l1 /\ hstring_sorted l2 /\
           (!a b. MEM a l1 /\ MEM b l2 ==> hstring_lt a b)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; hstring_sorted; MEM; ALL_APPEND] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

let HSTRING_SORTED_FILTER = prove
 (`!P l. hstring_sorted l ==> hstring_sorted (FILTER P l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; hstring_sorted] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[hstring_sorted] THEN
  UNDISCH_TAC `ALL (hstring_lt h) t` THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN MESON_TAC[]);;

let MEM_HINORDER_INSERT = prove
 (`!x xs y. MEM y (HINORDER_INSERT x xs) <=> y = x \/ MEM y xs`,
  REWRITE_TAC[HINORDER_INSERT; MEM_APPEND; MEM_FILTER; MEM] THEN
  MESON_TAC[HSTRING_LT_TOTAL]);;

let HSTRING_SORT_MEM = prove
 (`!l x. MEM x (HSTRING_SORT l) <=> MEM x l`,
  REWRITE_TAC[HSTRING_SORT] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; MEM; MEM_HINORDER_INSERT]);;

let HSTRING_SORT_SORTED = prove
 (`!l. hstring_sorted (HSTRING_SORT l)`,
  REWRITE_TAC[HSTRING_SORT] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST; hstring_sorted] THEN
  ABBREV_TAC `xs = ITLIST HINORDER_INSERT t []` THEN
  REWRITE_TAC[HINORDER_INSERT; HSTRING_SORTED_APPEND; APPEND] THEN
  ASM_SIMP_TAC[HSTRING_SORTED_FILTER; hstring_sorted] THEN
  REWRITE_TAC[MEM; MEM_FILTER; GSYM ALL_MEM] THEN
  MESON_TAC[HSTRING_LT_TRANS]);;

let HSTRING_SORTED_DISTINCT = prove
 (`!l. hstring_sorted l ==> HALL_DISTINCT l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[hstring_sorted; HALL_DISTINCT] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[HSTRING_LT_IRREFL]);;

let HSTRING_SORTED_UNIQUE = prove
 (`!l1 l2. hstring_sorted l1 /\ hstring_sorted l2 /\
           (!x. MEM x l1 <=> MEM x l2)
           ==> l1 = l2`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:string list` list_CASES) THEN
  REWRITE_TAC[hstring_sorted; MEM; NOT_CONS_NIL; CONS_11; GSYM ALL_MEM] THENL
   [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(h:char list) = h'` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[HSTRING_LT_IRREFL; HSTRING_LT_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[HSTRING_LT_IRREFL]);;

let HALL_DISTINCT_CARD = prove
 (`!l:A list. HALL_DISTINCT l ==> CARD (set_of_list l) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[HALL_DISTINCT; set_of_list; CARD_CLAUSES; LENGTH;
           FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  ASM_SIMP_TAC[]);;

let HSTRING_SORT_LENGTH = prove
 (`!l. HALL_DISTINCT l ==> LENGTH (HSTRING_SORT l) = LENGTH l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `HSTRING_SORT l` HALL_DISTINCT_CARD) THEN
  SIMP_TAC[HSTRING_SORTED_DISTINCT; HSTRING_SORT_SORTED] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `set_of_list (HSTRING_SORT l) = set_of_list l` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; HSTRING_SORT_MEM];
    ASM_SIMP_TAC[HALL_DISTINCT_CARD]]);;

let HSTRING_SORT_UNIQUE = prove
 (`!l params. hstring_sorted params /\ (!v. MEM v params <=> MEM v l)
              ==> HSTRING_SORT l = params`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HSTRING_SORTED_UNIQUE THEN
  ASM_REWRITE_TAC[HSTRING_SORT_SORTED; HSTRING_SORT_MEM]);;

(* ------------------------------------------------------------------------- *)
(* Type-variable lists have no repetitions.                                *)
(* ------------------------------------------------------------------------- *)

let HALL_DISTINCT_HLIST_UNION = prove
 (`!xs ys:A list. HALL_DISTINCT ys ==> HALL_DISTINCT (HLIST_UNION xs ys)`,
  REWRITE_TAC[HLIST_UNION] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ITLIST; HLIST_INSERT] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[HALL_DISTINCT]);;

let HTYVARS_DISTINCT = prove
 (`!ty. HALL_DISTINCT (htyvars ty)`,
  MATCH_MP_TAC HOLTYPE_INDUCT THEN
  REWRITE_TAC[HTYVARS; HALL_DISTINCT; MEM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`tys:holtype list`,`l:holtype list`) THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[ITLIST; HALL_DISTINCT;
                                   HALL_DISTINCT_HLIST_UNION]);;

let HTVARS_DISTINCT = prove
 (`!t. HALL_DISTINCT (htvars t)`,
  MATCH_MP_TAC holterm_INDUCT THEN
  SIMP_TAC[htvars; HTYVARS_DISTINCT; HALL_DISTINCT_HLIST_UNION]);;

(* ------------------------------------------------------------------------- *)
(* Theory well-formedness is preserved by an update whose new constants are*)
(* well-typed and whose new axioms are well-formed booleans, provided the  *)
(* update keeps every old lookup.                                          *)
(* ------------------------------------------------------------------------- *)

let HUPDATE_THEORY_OK = prove
 (`!upd ctxt.
        htheory_ok (hthyof ctxt) /\
        hsubmap (htype_list ctxt) (htype_list (CONS upd ctxt)) /\
        hsubmap (hconst_list ctxt) (hconst_list (CONS upd ctxt)) /\
        (!name ty. hlookup (hconsts_of_upd upd) name = SOME ty
                   ==> htype_ok (htype_list (CONS upd ctxt)) ty) /\
        (!p. MEM p (haxioms_of_upd upd)
             ==> hterm_ok (hsigof (CONS upd ctxt)) p /\ p hhas_type HBool)
        ==> htheory_ok (hthyof (CONS upd ctxt))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[htheory_ok; hthyof; hsigof; FST; SND] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[HCONST_LIST_CONS; HLOOKUP_APPEND] THEN
    MAP_EVERY X_GEN_TAC [`name:string`; `ty:holtype`] THEN
    COND_CASES_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC HTYPE_OK_MONO THEN EXISTS_TAC `htype_list ctxt` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`name:string`; `ty:holtype`] o
        check (fun th -> is_forall (concl th) &&
                         can (find_term ((=) `hconst_list ctxt`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`name:string`; `ty:holtype`] o
        check (fun th -> is_forall (concl th) &&
                         can (find_term ((=) `hconsts_of_upd upd`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    RULE_ASSUM_TAC(REWRITE_RULE[IN_SET_OF_LIST]) THEN
    REWRITE_TAC[IN_SET_OF_LIST; HAXIOM_LIST_CONS; MEM_APPEND] THEN
    X_GEN_TAC `p:holterm` THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[];
      CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
      MATCH_MP_TAC HTERM_OK_MONO THEN
      EXISTS_TAC `(htype_list ctxt,hconst_list ctxt)` THEN
      ASM_SIMP_TAC[FST; SND]];
    MATCH_MP_TAC HIS_STD_SIG_MONO THEN
    EXISTS_TAC `(htype_list ctxt,hconst_list ctxt)` THEN
    ASM_REWRITE_TAC[FST; SND]]);;

let MEM_HCONSTSPEC_ILIST = prove
 (`!eqs:(string#holterm)list s' s.
        MEM (s',s) (MAP (\(s,t). TmConst s (htypeof t),TmVar s (htypeof t)) eqs) <=>
        ?n t. MEM (n,t) eqs /\ s' = TmConst n (htypeof t) /\
              s = TmVar n (htypeof t)`,
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let MEM_HCONSTS_OF_CONSTSPEC = prove
 (`!eqs:(string#holterm)list n ty.
        MEM (n,ty) (MAP (\(s,t). (s,htypeof t)) eqs) <=>
        ?t. MEM (n,t) eqs /\ ty = htypeof t`,
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let HTERM_OK_COMB_TYPED = prove
 (`!sig s t rty. hterm_ok sig s /\ hterm_ok sig t /\
                 htypeof s = HFun (htypeof t) rty
                 ==> hterm_ok sig (TmComb s t) /\ htypeof (TmComb s t) = rty`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[hterm_ok; htypeof; HCODOMAIN_HFUN; HWELLTYPED_CLAUSES] THEN
  ASM_MESON_TAC[HTERM_OK_WELLTYPED]);;

let HTERM_OK_EQUATION_BOOL = prove
 (`!sig s t. his_std_sig sig /\ hterm_ok sig s /\ hterm_ok sig t /\
             htypeof t = htypeof s
             ==> hterm_ok sig (s =:= t) /\ (s =:= t) hhas_type HBool`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[HTERM_OK_EQUATION; HEQUATION_HAS_TYPE_BOOL] THEN
  ASM_MESON_TAC[HTERM_OK_WELLTYPED]);;

let HCONSTSPEC_THEORY_OK = prove
 (`!ctxt eqs prop.
        htheory_ok (hthyof ctxt) /\
        hproves (hthyof ctxt) (MAP (\(s,t). TmVar s (htypeof t) =:= t) eqs) prop /\
        HALL_DISTINCT (MAP FST eqs) /\
        hsubmap (hconst_list ctxt) (hconst_list (CONS (HConstSpec eqs prop) ctxt))
        ==> htheory_ok (hthyof (CONS (HConstSpec eqs prop) ctxt))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HUPDATE_THEORY_OK THEN
  ASM_REWRITE_TAC[HTYPE_LIST_CONS; htypes_of_upd; APPEND; HSUBMAP_REFL] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HPROVES_TERM_OK) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HTHEORY_OK_STD_SIG) THEN
  SUBGOAL_THEN `!n t. MEM (n,t) (eqs:(string#holterm)list)
                      ==> hterm_ok (FST (hthyof ctxt)) t /\
                          htype_ok (htype_list ctxt) (htypeof t)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `ALL (\p. hterm_ok (FST (hthyof ctxt)) p /\ p hhas_type HBool)
                     (MAP (\(s,t). TmVar s (htypeof t) =:= t)
                          (eqs:(string#holterm)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    DISCH_THEN(MP_TAC o SPEC `TmVar n (htypeof t) =:= t`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[HTERM_OK_EQUATION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`FST (hthyof ctxt)`; `t:holterm`] HTERM_OK_TYPE_OK) THEN
    ASM_REWRITE_TAC[hthyof; hsigof; FST];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[hconsts_of_upd] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HLOOKUP_MEM) THEN
    REWRITE_TAC[MEM_HCONSTS_OF_CONSTSPEC] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; APPEND; MEM;
              LET_DEF; LET_END_DEF] THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!n t. MEM (n,t) (eqs:(string#holterm)list)
          ==> hlookup (hconst_list (CONS (HConstSpec eqs prop) ctxt)) n =
              SOME (htypeof t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[HCONST_LIST_CONS; hconsts_of_upd; HLOOKUP_APPEND] THEN
    SUBGOAL_THEN `hlookup (MAP (\(s,t). s,htypeof t) (eqs:(string#holterm)list))
                          (n:string) = SOME (htypeof t)`
     (fun th -> REWRITE_TAC[th; option_DISTINCT]) THEN
    MATCH_MP_TAC HLOOKUP_DISTINCT_MEM THEN
    ASM_REWRITE_TAC[MAP_FST_PAIR_MAP; MEM_HCONSTS_OF_CONSTSPEC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HTERM_OK_VSUBST THEN CONJ_TAC THENL
     [MATCH_MP_TAC HTERM_OK_MONO THEN EXISTS_TAC `FST (hthyof ctxt)` THEN
      ASM_REWRITE_TAC[hsigof; hthyof; FST; SND; HTYPE_LIST_CONS; htypes_of_upd;
                      APPEND; HSUBMAP_REFL];
      REWRITE_TAC[MEM_HCONSTSPEC_ILIST] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[holterm_INJ] THEN
      MAP_EVERY EXISTS_TAC [`n:string`; `htypeof t`] THEN
      REWRITE_TAC[HHAS_TYPE_CLAUSES; hterm_ok] THEN
      EXISTS_TAC `htypeof t` THEN
      ASM_SIMP_TAC[hsigof; SND; FST] THEN CONJ_TAC THENL
       [REWRITE_TAC[HTYPE_LIST_CONS; htypes_of_upd; APPEND] THEN ASM_MESON_TAC[];
        MESON_TAC[HTYPE_SUBST_NIL]]];
    MATCH_MP_TAC HVSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[MEM_HCONSTSPEC_ILIST] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[holterm_INJ; HHAS_TYPE_CLAUSES] THEN
    MESON_TAC[]]);;

let HTYPEDEFN_THEORY_OK = prove
 (`!ctxt name pred abs_name rep_name witness.
        htheory_ok (hthyof ctxt) /\
        hproves (hthyof ctxt) [] (TmComb pred witness) /\
        ~(abs_name = rep_name) /\
        hsubmap (htype_list ctxt)
                (htype_list (CONS (HTypeDefn name pred abs_name rep_name) ctxt)) /\
        hsubmap (hconst_list ctxt)
                (hconst_list (CONS (HTypeDefn name pred abs_name rep_name) ctxt))
        ==> htheory_ok (hthyof (CONS (HTypeDefn name pred abs_name rep_name) ctxt))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HUPDATE_THEORY_OK THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HPROVES_TERM_OK) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HTHEORY_OK_STD_SIG) THEN
  UNDISCH_TAC `TmComb pred witness hhas_type HBool` THEN
  REWRITE_TAC[HHAS_TYPE_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `rty:holtype` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `hterm_ok (FST (hthyof ctxt)) (TmComb pred witness)` THEN
  REWRITE_TAC[hterm_ok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `htypeof pred = HFun rty HBool /\ htypeof witness = rty`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[HWELLTYPED_LEMMA]; ALL_TAC] THEN
  SUBGOAL_THEN `htype_ok (htype_list ctxt) rty` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`FST (hthyof ctxt)`; `pred:holterm`] HTERM_OK_TYPE_OK) THEN
    ASM_REWRITE_TAC[HFun; HTYPE_OK; ALL; hthyof; hsigof; FST] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ntys = htype_list (CONS (HTypeDefn name pred abs_name rep_name) ctxt)` THEN
  ABBREV_TAC `ncs = hconst_list (CONS (HTypeDefn name pred abs_name rep_name) ctxt)` THEN
  ABBREV_TAC `aty = TyApp name (MAP TyVar (HSTRING_SORT (htvars pred)))` THEN
  SUBGOAL_THEN `htype_ok ntys aty /\ htype_ok ntys rty /\
                hlookup ntys "fun" = SOME 2 /\ hlookup ntys "bool" = SOME 0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `his_std_sig (FST (hthyof ctxt))` THEN
    REWRITE_TAC[his_std_sig; hthyof; hsigof; FST] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "ntys" THEN EXPAND_TAC "aty" THEN
      REWRITE_TAC[HTYPE_OK; HTYPE_LIST_CONS; htypes_of_upd; APPEND; hlookup;
                  LENGTH_MAP] THEN
      SIMP_TAC[HSTRING_SORT_LENGTH; HTVARS_DISTINCT] THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[HTYPE_OK];
      MATCH_MP_TAC HTYPE_OK_MONO THEN EXISTS_TAC `htype_list ctxt` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `hsubmap (htype_list ctxt) ntys` THEN
      REWRITE_TAC[hsubmap] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `hsubmap (htype_list ctxt) ntys` THEN
      REWRITE_TAC[hsubmap] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `his_std_sig (ntys,ncs)` ASSUME_TAC THENL
   [MATCH_MP_TAC HIS_STD_SIG_MONO THEN
    EXISTS_TAC `(htype_list ctxt,hconst_list ctxt)` THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    UNDISCH_TAC `his_std_sig (FST (hthyof ctxt))` THEN
    REWRITE_TAC[hthyof; hsigof; FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `hconsts_of_upd (HTypeDefn name pred abs_name rep_name) =
                [abs_name,HFun rty aty; rep_name,HFun aty rty]`
  ASSUME_TAC THENL
   [REWRITE_TAC[hconsts_of_upd; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[HDOMAIN_HFUN];
    ALL_TAC] THEN
  SUBGOAL_THEN `hlookup (ncs:(string#holtype)list) abs_name =
                SOME (HFun rty aty) /\
                hlookup ncs rep_name = SOME (HFun aty rty)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ncs" THEN REWRITE_TAC[HCONST_LIST_CONS] THEN
    ASM_REWRITE_TAC[APPEND; hlookup];
    ALL_TAC] THEN
  SUBGOAL_THEN `htype_ok ntys (HFun rty aty) /\ htype_ok ntys (HFun aty rty)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HFun; HTYPE_OK; ALL; LENGTH; ARITH_RULE `SUC(SUC 0) = 2`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hterm_ok (ntys,ncs) (TmConst abs_name (HFun rty aty)) /\
    hterm_ok (ntys,ncs) (TmConst rep_name (HFun aty rty)) /\
    hterm_ok (ntys,ncs) (TmVar "a" aty) /\
    hterm_ok (ntys,ncs) (TmVar "r" rty) /\
    hterm_ok (ntys,ncs) pred`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[hterm_ok; FST; SND] THEN
    ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
    REPEAT CONJ_TAC THENL
     [MESON_TAC[HTYPE_SUBST_NIL]; MESON_TAC[HTYPE_SUBST_NIL]; ALL_TAC] THEN
    MATCH_MP_TAC HTERM_OK_MONO THEN EXISTS_TAC `FST (hthyof ctxt)` THEN
    ASM_REWRITE_TAC[hthyof; hsigof; FST; SND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[hlookup] THEN REPEAT GEN_TAC THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; LET_DEF;
              LET_END_DEF; APPEND; MEM] THEN
  ASM_REWRITE_TAC[HDOMAIN_HFUN] THEN
  REWRITE_TAC[hsigof] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A = TmConst abs_name (HFun rty aty)` THEN
  ABBREV_TAC `R = TmConst rep_name (HFun aty rty)` THEN
  ABBREV_TAC `a = TmVar "a" aty` THEN
  ABBREV_TAC `r = TmVar "r" rty` THEN
  SUBGOAL_THEN `htypeof A = HFun rty aty /\ htypeof R = HFun aty rty /\
                htypeof a = aty /\ htypeof r = rty`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "R"; "a"; "r"] THEN REWRITE_TAC[htypeof];
    ALL_TAC] THEN
  SUBGOAL_THEN `hterm_ok (ntys,ncs) (TmComb R a) /\ htypeof (TmComb R a) = rty`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HTERM_OK_COMB_TYPED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hterm_ok (ntys,ncs) (TmComb A (TmComb R a)) /\
                htypeof (TmComb A (TmComb R a)) = aty`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HTERM_OK_COMB_TYPED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hterm_ok (ntys,ncs) (TmComb A r) /\ htypeof (TmComb A r) = aty`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HTERM_OK_COMB_TYPED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hterm_ok (ntys,ncs) (TmComb R (TmComb A r)) /\
                htypeof (TmComb R (TmComb A r)) = rty`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HTERM_OK_COMB_TYPED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hterm_ok (ntys,ncs) (TmComb pred r) /\
                htypeof (TmComb pred r) = HBool`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HTERM_OK_COMB_TYPED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hterm_ok (ntys,ncs) (TmComb R (TmComb A r) =:= r) /\
                (TmComb R (TmComb A r) =:= r) hhas_type HBool`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HTERM_OK_EQUATION_BOOL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC HTERM_OK_EQUATION_BOOL THEN
  ASM_REWRITE_TAC[HTYPEOF_EQUATION]);;

(* ------------------------------------------------------------------------- *)
(* Valid updates and extensions preserve theory well-formedness.           *)
(* ------------------------------------------------------------------------- *)

let HUPDATES_THEORY_OK = prove
 (`!upd ctxt. upd hupdates ctxt /\ htheory_ok (hthyof ctxt)
              ==> htheory_ok (hthyof (CONS upd ctxt))`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC hupdates_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC HUPDATE_THEORY_OK THEN
    ASM_REWRITE_TAC[HTYPE_LIST_CONS; HCONST_LIST_CONS; htypes_of_upd;
                    hconsts_of_upd; haxioms_of_upd; haxexts_of_upd;
                    hconexts_of_upd; APPEND; HSUBMAP_REFL; hlookup;
                    option_DISTINCT; MEM] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[hsigof]) THEN
    ASM_REWRITE_TAC[hsigof; HTYPE_LIST_CONS; HCONST_LIST_CONS; htypes_of_upd;
                    hconsts_of_upd; APPEND];
    MATCH_MP_TAC HUPDATE_THEORY_OK THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HTYPE_LIST_CONS; HCONST_LIST_CONS; htypes_of_upd; hconsts_of_upd;
                haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; MEM] THEN
    REWRITE_TAC[APPEND; HSUBMAP_REFL] THEN
    REWRITE_TAC[MEM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`[name:string,ty:holtype]`; `hconst_list ctxt`]
                    HSUBMAP_APPEND_FRESH) THEN
      REWRITE_TAC[APPEND; MAP; MEM; FST] THEN ASM_MESON_TAC[];
      REWRITE_TAC[hlookup] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[option_INJ; option_DISTINCT] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC HCONSTSPEC_THEORY_OK THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HCONST_LIST_CONS] THEN MATCH_MP_TAC HSUBMAP_APPEND_FRESH THEN
    ASM_REWRITE_TAC[hconsts_of_upd; MAP_FST_PAIR_MAP];
    MATCH_MP_TAC HUPDATE_THEORY_OK THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HTYPE_LIST_CONS; HCONST_LIST_CONS; htypes_of_upd; hconsts_of_upd;
                haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; MEM; hlookup;
                option_DISTINCT] THEN
    REWRITE_TAC[APPEND; HSUBMAP_REFL] THEN
    MP_TAC(ISPECL [`[name:string,arity:num]`; `htype_list ctxt`]
                  HSUBMAP_APPEND_FRESH) THEN
    REWRITE_TAC[APPEND; MAP; MEM; FST] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC HTYPEDEFN_THEORY_OK THEN EXISTS_TAC `witness:holterm` THEN
    ASM_REWRITE_TAC[HTYPE_LIST_CONS; HCONST_LIST_CONS] THEN
    CONJ_TAC THEN MATCH_MP_TAC HSUBMAP_APPEND_FRESH THEN
    REWRITE_TAC[htypes_of_upd; hconsts_of_upd; LET_DEF; LET_END_DEF; MAP;
                MEM; FST] THEN
    ASM_MESON_TAC[]]);;

let HEXTENDS_THEORY_OK = prove
 (`!c1 c2. c2 hextends c1 /\ htheory_ok (hthyof c1) ==> htheory_ok (hthyof c2)`,
  SUBGOAL_THEN `!c2 c1. c2 hextends c1
                        ==> htheory_ok (hthyof c1) ==> htheory_ok (hthyof c2)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC hextends_INDUCT THEN MESON_TAC[HUPDATES_THEORY_OK]);;

(* ------------------------------------------------------------------------- *)
(* Provability is monotone in the theory, hence under extension.           *)
(* ------------------------------------------------------------------------- *)

let HPROVES_MONO = prove
 (`!thy1 h c. hproves thy1 h c
              ==> !thy2. hsubmap (FST(FST thy1)) (FST(FST thy2)) /\
                         hsubmap (SND(FST thy1)) (SND(FST thy2)) /\
                         (!p. p IN SND thy1 ==> p IN SND thy2) /\
                         htheory_ok thy2
                         ==> hproves thy2 h c`,
  MATCH_MP_TAC hproves_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN X_GEN_TAC `thy2:hthy` THEN STRIP_TAC THENL
   [MATCH_MP_TAC HPROVES_ABS THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[HTYPE_OK_MONO];
    MATCH_MP_TAC HPROVES_ASSUME THEN ASM_MESON_TAC[HTERM_OK_MONO];
    MATCH_MP_TAC HPROVES_BETA THEN ASM_MESON_TAC[HTERM_OK_MONO; HTYPE_OK_MONO];
    MATCH_MP_TAC HPROVES_DEDUCT_ANTISYM THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC HPROVES_EQ_MP THEN
    MAP_EVERY EXISTS_TAC [`p:holterm`; `p':holterm`] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC HPROVES_INST THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[HTERM_OK_MONO];
    MATCH_MP_TAC HPROVES_INST_TYPE THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `ALL (htype_ok (FST (FST (thy:hthy))))
                     (MAP FST (tyin:(holtype#holtype)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[HTYPE_OK_MONO];
    MATCH_MP_TAC HPROVES_MK_COMB THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC HPROVES_REFL THEN ASM_MESON_TAC[HTERM_OK_MONO];
    MATCH_MP_TAC HPROVES_AXIOM THEN ASM_MESON_TAC[]]);;

let HTHYOF_SIG = prove
 (`!ctxt. FST (FST (hthyof ctxt)) = htype_list ctxt /\
          SND (FST (hthyof ctxt)) = hconst_list ctxt /\
          FST (hthyof ctxt) = hsigof ctxt`,
  REWRITE_TAC[hthyof; hsigof]);;

let HUPDATES_PROVES = prove
 (`!upd ctxt h c. upd hupdates ctxt /\ hproves (hthyof ctxt) h c
                  ==> hproves (hthyof (CONS upd ctxt)) h c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HPROVES_MONO) THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HUPDATES_SUBMAP) THEN
  ASM_REWRITE_TAC[HTHYOF_SIG; HUPDATES_AXIOMS] THEN
  MATCH_MP_TAC HUPDATES_THEORY_OK THEN ASM_MESON_TAC[HPROVES_THEORY_OK]);;

let HEXTENDS_PROVES = prove
 (`!c1 c2 h c. c2 hextends c1 /\ hproves (hthyof c1) h c
               ==> hproves (hthyof c2) h c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HPROVES_MONO) THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HEXTENDS_SUBMAP) THEN
  ASM_REWRITE_TAC[HTHYOF_SIG] THEN
  MATCH_MP_TAC HEXTENDS_THEORY_OK THEN ASM_MESON_TAC[HPROVES_THEORY_OK]);;

let HEXTENDS_TYPE_OK = prove
 (`!c1 c2 ty. c2 hextends c1 /\ htype_ok (FST (hsigof c1)) ty
              ==> htype_ok (FST (hsigof c2)) ty`,
  REWRITE_TAC[hsigof] THEN MESON_TAC[HEXTENDS_SUBMAP; HTYPE_OK_MONO]);;

let HEXTENDS_TERM_OK = prove
 (`!c1 c2 t. c2 hextends c1 /\ hterm_ok (hsigof c1) t
             ==> hterm_ok (hsigof c2) t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HTERM_OK_MONO THEN
  EXISTS_TAC `hsigof c1` THEN ASM_REWRITE_TAC[hsigof] THEN
  ASM_MESON_TAC[HEXTENDS_SUBMAP]);;

let HEXTENDS_LOOKUP = prove
 (`!c1 c2. c2 hextends c1
           ==> (!k a. hlookup (FST (hsigof c1)) k = SOME a
                      ==> hlookup (FST (hsigof c2)) k = SOME a) /\
               (!k ty. hlookup (SND (hsigof c1)) k = SOME ty
                       ==> hlookup (SND (hsigof c2)) k = SOME ty)`,
  REWRITE_TAC[hsigof; GSYM hsubmap] THEN MESON_TAC[HEXTENDS_SUBMAP]);;
