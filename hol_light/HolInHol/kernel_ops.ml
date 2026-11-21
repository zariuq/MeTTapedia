(* ========================================================================= *)
(* HOL Light's theory operations (fusion.ml) as valid updates: new_type,    *)
(* new_constant, new_axiom, new_basic_definition and                         *)
(* new_basic_type_definition, each with fusion.ml's checks as hypotheses;    *)
(* every theorem the operation returns is provable in the extended theory.   *)
(* Negative controls for the freshness checks follow.                        *)
(* ========================================================================= *)

let HUPDATES_NEWAXIOM = el 0 (CONJUNCTS hupdates_RULES);;

let HUPDATES_NEWCONST = el 1 (CONJUNCTS hupdates_RULES);;

let HUPDATES_CONSTSPEC = el 2 (CONJUNCTS hupdates_RULES);;

let HUPDATES_NEWTYPE = el 3 (CONJUNCTS hupdates_RULES);;

let HUPDATES_TYPEDEFN = el 4 (CONJUNCTS hupdates_RULES);;

(* ------------------------------------------------------------------------- *)
(* new_type and new_constant. HOL Light checks only that the name is not   *)
(* yet declared; the type given to new_constant is well-formed because     *)
(* HOL Light types are built by mk_type, which checks arities.             *)
(* ------------------------------------------------------------------------- *)

let HOL_NEW_TYPE = prove
 (`!ctxt name arity.
        hlookup (htype_list ctxt) name = NONE
        ==> HNewType name arity hupdates ctxt`,
  REWRITE_TAC[HUPDATES_NEWTYPE]);;

let HOL_NEW_CONSTANT = prove
 (`!ctxt name ty.
        hlookup (hconst_list ctxt) name = NONE /\ htype_ok (htype_list ctxt) ty
        ==> HNewConst name ty hupdates ctxt`,
  REWRITE_TAC[HUPDATES_NEWCONST]);;

let HAXIOM_OF_UPDATE = prove
 (`!upd ctxt p. MEM p (haxioms_of_upd upd)
                ==> p IN SND (hthyof (CONS upd ctxt))`,
  REWRITE_TAC[hthyof; IN_SET_OF_LIST; HAXIOM_LIST_CONS; MEM_APPEND] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* new_axiom. HOL Light checks that the term is a proposition; the term is *)
(* well-formed in the signature because HOL Light terms are built by       *)
(* mk_var, mk_const, mk_comb and mk_abs.                                   *)
(* ------------------------------------------------------------------------- *)

let HOL_NEW_AXIOM = prove
 (`!ctxt tm.
        htheory_ok (hthyof ctxt) /\ hterm_ok (hsigof ctxt) tm /\
        tm hhas_type HBool
        ==> HNewAxiom tm hupdates ctxt /\
            hproves (hthyof (CONS (HNewAxiom tm) ctxt)) [] tm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `HNewAxiom tm hupdates ctxt` ASSUME_TAC THENL
   [MATCH_MP_TAC HUPDATES_NEWAXIOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HPROVES_AXIOM THEN
  ASM_SIMP_TAC[HUPDATES_THEORY_OK] THEN MATCH_MP_TAC HAXIOM_OF_UPDATE THEN
  REWRITE_TAC[haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; APPEND; MEM]);;

(* ------------------------------------------------------------------------- *)
(* new_basic_definition `c = r`: the constant name is fresh, r is closed,  *)
(* and every type variable of r occurs in the type of c. The matching      *)
(* update is a constant specification with the single equation c = r.      *)
(* ------------------------------------------------------------------------- *)

let HOL_NEW_BASIC_DEFINITION = prove
 (`!ctxt c ty r.
        htheory_ok (hthyof ctxt) /\
        hterm_ok (hsigof ctxt) (TmVar c ty =:= r) /\
        hlookup (hconst_list ctxt) c = NONE /\
        HCLOSED r /\
        (!v. MEM v (htvars r) ==> MEM v (htyvars ty))
        ==> HConstSpec [c,r] (TmVar c ty =:= r) hupdates ctxt /\
            hproves (hthyof (CONS (HConstSpec [c,r] (TmVar c ty =:= r)) ctxt)) []
                    (TmConst c ty =:= r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HTHEORY_OK_STD_SIG) THEN
  UNDISCH_TAC `hterm_ok (hsigof ctxt) (TmVar c ty =:= r)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HTHYOF_SIG]) THEN
  ASM_SIMP_TAC[HTERM_OK_EQUATION; htypeof] THEN STRIP_TAC THEN
  SUBGOAL_THEN `HConstSpec [c,r] (TmVar c ty =:= r) hupdates ctxt` ASSUME_TAC THENL
   [MATCH_MP_TAC HUPDATES_CONSTSPEC THEN
    ASM_REWRITE_TAC[MAP; ALL; MEM; HALL_DISTINCT; FST; SND] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HPROVES_ASSUME THEN
      ASM_REWRITE_TAC[HTHYOF_SIG; HEQUATION_HAS_TYPE_BOOL; htypeof;
                      HWELLTYPED_CLAUSES] THEN
      ASM_SIMP_TAC[HTERM_OK_EQUATION; htypeof] THEN
      ASM_MESON_TAC[HTERM_OK_WELLTYPED];
      REWRITE_TAC[hequation; HEqual; HVFREE_IN; holterm_DISTINCT; holterm_INJ;
                  PAIR_EQ] THEN
      UNDISCH_TAC `HCLOSED r` THEN REWRITE_TAC[HCLOSED] THEN MESON_TAC[];
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HPROVES_AXIOM THEN
  ASM_SIMP_TAC[HUPDATES_THEORY_OK] THEN MATCH_MP_TAC HAXIOM_OF_UPDATE THEN
  REWRITE_TAC[haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; APPEND; MEM;
              LET_DEF; LET_END_DEF; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `HVSUBST [TmConst c ty,TmVar c ty] r = r` ASSUME_TAC THENL
   [MATCH_MP_TAC HVSUBST_TRIVIAL THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
    UNDISCH_TAC `HCLOSED r` THEN REWRITE_TAC[HCLOSED] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[hequation; HVSUBST; HEqual; htypeof; HREV_ASSOCD]);;

(* ------------------------------------------------------------------------- *)
(* new_basic_type_definition from |- P x: the type name and the two        *)
(* constant names are fresh and distinct, P is closed, and the new type    *)
(* is applied to the type variables of P sorted by name, as fusion.ml      *)
(* sorts them with (<=). HOL Light returns the two theorems below.         *)
(* ------------------------------------------------------------------------- *)

let HOL_NEW_BASIC_TYPE_DEFINITION = prove
 (`!ctxt tyname absname repname P x params.
        htheory_ok (hthyof ctxt) /\
        hproves (hthyof ctxt) [] (TmComb P x) /\
        HCLOSED P /\
        hlookup (htype_list ctxt) tyname = NONE /\
        hlookup (hconst_list ctxt) absname = NONE /\
        hlookup (hconst_list ctxt) repname = NONE /\
        ~(absname = repname) /\
        hstring_sorted params /\ (!v. MEM v params <=> MEM v (htvars P))
        ==> HTypeDefn tyname P absname repname hupdates ctxt /\
            hproves (hthyof (CONS (HTypeDefn tyname P absname repname) ctxt)) []
             (TmComb (TmConst absname
                        (HFun (htypeof x) (TyApp tyname (MAP TyVar params))))
                     (TmComb (TmConst repname
                               (HFun (TyApp tyname (MAP TyVar params)) (htypeof x)))
                             (TmVar "a" (TyApp tyname (MAP TyVar params)))) =:=
              TmVar "a" (TyApp tyname (MAP TyVar params))) /\
            hproves (hthyof (CONS (HTypeDefn tyname P absname repname) ctxt)) []
             (TmComb P (TmVar "r" (htypeof x)) =:=
              (TmComb (TmConst repname
                        (HFun (TyApp tyname (MAP TyVar params)) (htypeof x)))
                      (TmComb (TmConst absname
                                (HFun (htypeof x) (TyApp tyname (MAP TyVar params))))
                              (TmVar "r" (htypeof x))) =:=
               TmVar "r" (htypeof x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `HTypeDefn tyname P absname repname hupdates ctxt` ASSUME_TAC THENL
   [MATCH_MP_TAC HUPDATES_TYPEDEFN THEN EXISTS_TAC `x:holterm` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `HSTRING_SORT (htvars P) = params` ASSUME_TAC THENL
   [MATCH_MP_TAC HSTRING_SORT_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hdomain (htypeof P) = htypeof x` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HPROVES_TERM_OK) THEN
    REWRITE_TAC[HHAS_TYPE_CLAUSES] THEN
    DISCH_THEN(X_CHOOSE_THEN `dty:holtype` STRIP_ASSUME_TAC o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP HWELLTYPED_LEMMA) THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP HWELLTYPED_LEMMA) THEN
    REWRITE_TAC[HDOMAIN_HFUN];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC HPROVES_AXIOM THEN
  ASM_SIMP_TAC[HUPDATES_THEORY_OK] THEN MATCH_MP_TAC HAXIOM_OF_UPDATE THEN
  REWRITE_TAC[haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; APPEND; MEM;
              LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Derived rules used by the negative controls.                            *)
(* ------------------------------------------------------------------------- *)

let HPROVES_HYPS_UNION_NIL = prove
 (`!thy h c. hproves thy (HTERM_UNION h []) c /\
             ALL (\p. hterm_ok (FST thy) p /\ p hhas_type HBool) h
             ==> hproves thy h c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HPROVES_ACONV THEN
  MAP_EVERY EXISTS_TAC [`HTERM_UNION h []`; `c:holterm`] THEN
  ASM_REWRITE_TAC[HACONV_REFL] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `x:holterm` THEN
    REWRITE_TAC[HACONV_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HTERM_UNION_NONEW) THEN REWRITE_TAC[MEM];
    ASM_MESON_TAC[HPROVES_TERM_OK; hwelltyped]]);;

let HPROVES_AP_TERM = prove
 (`!thy h f l r.
        hproves thy h (l =:= r) /\ hterm_ok (FST thy) f /\ hwelltyped (TmComb f l)
        ==> hproves thy h (TmComb f l =:= TmComb f r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`thy:hthy`; `[]:holterm list`; `h:holterm list`;
                `f:holterm`; `f:holterm`; `l:holterm`; `r:holterm`]
               HPROVES_MK_COMB) THEN
  REWRITE_TAC[HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HPROVES_REFL THEN
  ASM_MESON_TAC[HPROVES_THEORY_OK]);;

let HPROVES_AP_THM = prove
 (`!thy h f g x.
        hproves thy h (f =:= g) /\ hterm_ok (FST thy) x /\ hwelltyped (TmComb f x)
        ==> hproves thy h (TmComb f x =:= TmComb g x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HPROVES_HYPS_UNION_NIL THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[HPROVES_TERM_OK]] THEN
  MATCH_MP_TAC HPROVES_MK_COMB THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HPROVES_REFL THEN ASM_MESON_TAC[HPROVES_THEORY_OK]);;

let HPROVES_SYM = prove
 (`!thy h l r. hproves thy h (l =:= r) ==> hproves thy h (r =:= l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HPROVES_TERM_OK) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HTHEORY_OK_STD_SIG) THEN
  SUBGOAL_THEN `hterm_ok (FST(thy:hthy)) (HEqual (htypeof l))` ASSUME_TAC THENL
   [UNDISCH_TAC `hterm_ok (FST(thy:hthy)) (l =:= r)` THEN
    REWRITE_TAC[hequation; hterm_ok] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hterm_ok (FST(thy:hthy)) l /\ hterm_ok (FST thy) r /\
                htypeof r = htypeof l`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `hterm_ok (FST(thy:hthy)) (l =:= r)` THEN
    ASM_SIMP_TAC[HTERM_OK_EQUATION];
    ALL_TAC] THEN
  SUBGOAL_THEN `hwelltyped l /\ hwelltyped r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HTERM_OK_WELLTYPED]; ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy h (TmComb (HEqual (htypeof l)) l =:=
                              TmComb (HEqual (htypeof l)) r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_AP_TERM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HWELLTYPED_CLAUSES; HEqual; htypeof] THEN
    ASM_REWRITE_TAC[GSYM HEqual; HFUN_INJ] THEN
    REWRITE_TAC[HEqual; HFun] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy [] (l =:= l)` ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_REFL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy h ((l =:= l) =:= (r =:= l))` ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_HYPS_UNION_NIL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(l =:= l) = TmComb (TmComb (HEqual (htypeof l)) l) l /\
                  (r =:= l) = TmComb (TmComb (HEqual (htypeof l)) r) l`
     (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[hequation]; ALL_TAC] THEN
    MATCH_MP_TAC HPROVES_MK_COMB THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HWELLTYPED_CLAUSES; HEqual; htypeof; HCODOMAIN_HFUN] THEN
    ASM_REWRITE_TAC[HFUN_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HPROVES_HYPS_UNION_NIL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HPROVES_EQ_MP THEN
  MAP_EVERY EXISTS_TAC [`l =:= l`; `l =:= l`] THEN
  ASM_REWRITE_TAC[HACONV_REFL]);;

let HPROVES_TRANS_EQ = prove
 (`!thy h1 h2 l m r. hproves thy h1 (l =:= m) /\ hproves thy h2 (m =:= r)
                     ==> hproves thy (HTERM_UNION h1 h2) (l =:= r)`,
  MESON_TAC[HPROVES_TRANS; HACONV_REFL]);;

let HTYPE_OK_STD = prove
 (`!sig. his_std_sig sig
         ==> htype_ok (FST sig) HBool /\
             (!a b. htype_ok (FST sig) (HFun a b) <=>
                    htype_ok (FST sig) a /\ htype_ok (FST sig) b)`,
  SIMP_TAC[his_std_sig; HFun; HBool; HTYPE_OK; ALL; LENGTH;
           ARITH_RULE `SUC(SUC 0) = 2`]);;

let HTERM_OK_ABS_VAR = prove
 (`!sig x ty t. hterm_ok sig (TmAbs (TmVar x ty) t) <=>
                htype_ok (FST sig) ty /\ hterm_ok sig t`,
  REWRITE_TAC[hterm_ok; holterm_INJ] THEN MESON_TAC[]);;

let HPROVES_INST1 = prove
 (`!thy h c t v ty.
        hproves thy h c /\ t hhas_type ty /\ hterm_ok (FST thy) t
        ==> hproves thy (MAP (HVSUBST [t,TmVar v ty]) h)
                        (HVSUBST [t,TmVar v ty] c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HPROVES_INST THEN
  ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`v:string`; `ty:holtype`] THEN ASM_REWRITE_TAC[]);;

let HVSUBST_EQUATION = prove
 (`!ilist s t.
        (!s' s0. MEM (s',s0) ilist ==> ?x ty. s0 = TmVar x ty /\ s' hhas_type ty) /\
        hwelltyped s
        ==> HVSUBST ilist (s =:= t) = HVSUBST ilist s =:= HVSUBST ilist t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hequation; HVSUBST; HEqual] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM HEqual] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(GSYM HWELLTYPED_LEMMA) THEN
  MATCH_MP_TAC HVSUBST_HAS_TYPE THEN ASM_REWRITE_TAC[GSYM HWELLTYPED]);;

let HVSUBST_EQUATION1 = prove
 (`!t v ty s u. t hhas_type ty /\ hwelltyped s
                ==> HVSUBST [t,TmVar v ty] (s =:= u) =
                    HVSUBST [t,TmVar v ty] s =:= HVSUBST [t,TmVar v ty] u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HVSUBST_EQUATION THEN
  ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`v:string`; `ty:holtype`] THEN ASM_REWRITE_TAC[]);;

let HWELLTYPED_TAC =
  REWRITE_TAC[HWELLTYPED_CLAUSES; htypeof; HCODOMAIN_HFUN; HFUN_INJ;
              holterm_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM;
              UNWIND_THM1; EXISTS_REFL; EXISTS_REFL_SYM];;

let HHAS_TYPE_TAC =
  REWRITE_TAC[HHAS_TYPE_CLAUSES; HFUN_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM;
              UNWIND_THM1; UNWIND_THM2; EXISTS_REFL; EXISTS_REFL_SYM];;

let HVSUBST_CONV =
  let rw = REWRITE_CONV[HVSUBST; HREV_ASSOCD; FILTER; EX; MAP; LET_DEF;
                        LET_END_DEF; HVSUBST_NIL; holterm_INJ; PAIR_EQ;
                        HVFREE_IN; holterm_DISTINCT] in
  REPEATC(CHANGED_CONV(rw THENC TRY_CONV(DEPTH_CONV GEN_BETA_CONV) THENC
                       TRY_CONV(ONCE_DEPTH_CONV STRING_EQ_CONV)));;

let HVSUBST_DEFINING_EQUATION = prove
 (`!c ty r. HCLOSED r
            ==> HVSUBST [TmConst c ty,TmVar c ty] (TmVar c ty =:= r) =
                TmConst c ty =:= r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `HVSUBST [TmConst c ty,TmVar c ty] r = r` ASSUME_TAC THENL
   [MATCH_MP_TAC HVSUBST_TRIVIAL THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
    ASM_MESON_TAC[HCLOSED];
    ASM_REWRITE_TAC[hequation; HVSUBST; HEqual; htypeof; HREV_ASSOCD]]);;

(* ------------------------------------------------------------------------- *)
(* Negative control for the freshness of a defined constant: defining c     *)
(* twice (c = \x y. x, then c = \x y. y) meets every other condition of the  *)
(* definition rule, the resulting theory is well-formed, and it proves       *)
(* x = y for distinct boolean variables, which MODEL_DISTINCT_EQ_INVALID     *)
(* shows is false in the standard model.                                     *)
(* ------------------------------------------------------------------------- *)

let HNEG_CONST_REDEFINITION = prove
 (`(HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hupdates hcore_ctxt /\
   hlookup (hconst_list (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)) "c" = SOME (HFun HBool (HFun HBool HBool)) /\
   hproves (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)) [TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))) /\
   HCLOSED (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))) /\ htvars (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))) = [] /\
   (!x ty. HVFREE_IN (TmVar x ty) (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))
           ==> MEM (x,ty) ["c",htypeof (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))]) /\
   HALL_DISTINCT ["c"] /\
   htheory_ok (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))) (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt))) /\
   hproves (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))) (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt))) [] ((TmVar "x" HBool) =:= (TmVar "y" HBool))`,
  MP_TAC(MATCH_MP HTHEORY_OK_STD_SIG HCORE_THEORY_OK) THEN
  REWRITE_TAC[HTHYOF_SIG] THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP HTYPE_OK_STD (ASSUME `his_std_sig (hsigof hcore_ctxt)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `HCLOSED (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))) /\ HCLOSED (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))) /\ htvars (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))) = [] /\ htvars (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))) = []`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[HCLOSED; HVFREE_IN; htvars; HTYVARS; HBool; ITLIST; HFun] THEN
    REWRITE_TAC[holterm_INJ; HLIST_UNION; ITLIST] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `htypeof (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))) = (HFun HBool (HFun HBool HBool)) /\ htypeof (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))) = (HFun HBool (HFun HBool HBool))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[htypeof]; ALL_TAC] THEN
  SUBGOAL_THEN `hterm_ok (hsigof hcore_ctxt) (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[HTERM_OK_EQUATION; hterm_ok; HTERM_OK_ABS_VAR; htypeof];
    ALL_TAC] THEN
  SUBGOAL_THEN `hlookup (hconst_list hcore_ctxt) "c" = NONE` ASSUME_TAC THENL
   [REWRITE_TAC[HCORE_CONST_LIST; hlookup] THEN
    CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`hcore_ctxt`; `"c"`; `(HFun HBool (HFun HBool HBool))`; `(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))`] HOL_NEW_BASIC_DEFINITION) THEN
  ASM_REWRITE_TAC[HCORE_THEORY_OK; MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `htheory_ok (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt))` ASSUME_TAC THENL
   [MATCH_MP_TAC HUPDATES_THEORY_OK THEN ASM_REWRITE_TAC[HCORE_THEORY_OK];
    ALL_TAC] THEN
  SUBGOAL_THEN `hconst_list (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt) = CONS ("c",(HFun HBool (HFun HBool HBool))) (hconst_list hcore_ctxt)`
  ASSUME_TAC THENL
   [REWRITE_TAC[HCONST_LIST_CONS; hconsts_of_upd; MAP; APPEND] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hlookup (hconst_list (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)) "c" = SOME (HFun HBool (HFun HBool HBool))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[hlookup]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `his_std_sig (FST (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)))` ASSUME_TAC THENL
   [MATCH_MP_TAC HTHEORY_OK_STD_SIG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP HTYPE_OK_STD (ASSUME `his_std_sig (FST (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)))`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `hproves (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)) [TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))]
                        (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_ASSUME THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[HEQUATION_HAS_TYPE_BOOL; HWELLTYPED_CLAUSES; htypeof;
                  holterm_INJ] THEN MESON_TAC[];
      ASM_SIMP_TAC[HTERM_OK_EQUATION; hterm_ok; HTERM_OK_ABS_VAR; htypeof]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[hequation; HEqual; HVFREE_IN; holterm_DISTINCT; holterm_INJ;
                MEM; PAIR_EQ] THEN
    UNDISCH_TAC `HCLOSED (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))` THEN REWRITE_TAC[HCLOSED] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HALL_DISTINCT; MEM] THEN
  SUBGOAL_THEN `hsubmap (hconst_list (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)) (hconst_list (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))) (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `hconst_list (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))) (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)) = APPEND ["c",(HFun HBool (HFun HBool HBool))] (hconst_list (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [HCONST_LIST_CONS] THEN
      REWRITE_TAC[hconsts_of_upd; MAP] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[HSUBMAP_APPEND] THEN
    MAP_EVERY X_GEN_TAC [`k:string`; `v:holtype`] THEN
    ASM_CASES_TAC `k = "c"` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      ASM_REWRITE_TAC[hlookup; option_INJ] THEN MESON_TAC[];
      SUBGOAL_THEN `~("c" = k)` (fun th -> REWRITE_TAC[th; hlookup]) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `htheory_ok (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))) (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)))` ASSUME_TAC THENL
   [MATCH_MP_TAC HCONSTSPEC_THEORY_OK THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAP; HALL_DISTINCT; MEM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `hproves (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))) (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt))) [] (TmConst "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt)`; `[]:holterm list`;
                   `TmConst "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))`] HPROVES_MONO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[HTHYOF_SIG; HUPDATES_AXIOMS] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[HTYPE_LIST_CONS; htypes_of_upd; APPEND; HSUBMAP_REFL];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `hproves (hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))) (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt))) [] (TmConst "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_AXIOM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAXIOM_OF_UPDATE THEN
    REWRITE_TAC[haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; APPEND;
                MEM; MAP; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[HVSUBST_DEFINING_EQUATION];
    ALL_TAC] THEN
  ABBREV_TAC `thy = hthyof (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))) (CONS (HConstSpec ["c",(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))] (TmVar "c" (HFun HBool (HFun HBool HBool)) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))))) hcore_ctxt))` THEN
  SUBGOAL_THEN `his_std_sig (FST(thy:hthy))` ASSUME_TAC THENL
   [MATCH_MP_TAC HTHEORY_OK_STD_SIG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP HTYPE_OK_STD (ASSUME `his_std_sig (FST(thy:hthy))`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `hterm_ok (FST(thy:hthy)) (TmVar "x" HBool) /\ hterm_ok (FST thy) (TmVar "y" HBool)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[hterm_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy [] ((TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))) =:= (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`; `(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)))`;
                   `TmConst "c" (HFun HBool (HFun HBool HBool))`; `(TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)))`] HPROVES_TRANS_EQ) THEN
    REWRITE_TAC[HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HPROVES_SYM THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy [] (TmComb (TmComb (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))) (TmVar "x" HBool)) (TmVar "y" HBool) =:=
                                TmComb (TmComb (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))) (TmVar "x" HBool)) (TmVar "y" HBool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_AP_THM THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HPROVES_AP_THM THEN ASM_REWRITE_TAC[] THEN
      HWELLTYPED_TAC;
      HWELLTYPED_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy [] (TmComb (TmComb (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))) (TmVar "x" HBool)) (TmVar "y" HBool) =:= (TmVar "x" HBool)) /\
                hproves thy [] (TmComb (TmComb (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))) (TmVar "x" HBool)) (TmVar "y" HBool) =:= (TmVar "y" HBool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`]
                  HPROVES_TRANS_EQ) THEN
    REWRITE_TAC[HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THENL
     [EXISTS_TAC `TmComb (TmAbs (TmVar "y" HBool) (TmVar "x" HBool)) (TmVar "y" HBool)`;
      EXISTS_TAC `TmComb (TmAbs (TmVar "y" HBool) (TmVar "y" HBool)) (TmVar "y" HBool)`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC HPROVES_AP_THM THEN ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC HPROVES_BETA THEN
         ASM_REWRITE_TAC[HTERM_OK_ABS_VAR; hterm_ok];
         HWELLTYPED_TAC];
       MATCH_MP_TAC HPROVES_BETA THEN ASM_REWRITE_TAC[hterm_ok]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`; `(TmVar "x" HBool)`;
                 `TmComb (TmComb (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))) (TmVar "x" HBool)) (TmVar "y" HBool)`; `(TmVar "y" HBool)`] HPROVES_TRANS_EQ) THEN
  REWRITE_TAC[HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`; `(TmVar "x" HBool)`;
                 `TmComb (TmComb (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "x" HBool))) (TmVar "x" HBool)) (TmVar "y" HBool)`; `TmComb (TmComb (TmAbs (TmVar "x" HBool) (TmAbs (TmVar "y" HBool) (TmVar "y" HBool))) (TmVar "x" HBool)) (TmVar "y" HBool)`]
                HPROVES_TRANS_EQ) THEN
  REWRITE_TAC[HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HPROVES_SYM THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Negative control for the freshness of a defined type: redefining bool as  *)
(* the subtype {r | r} of bool (abstraction absb, representation repb) meets *)
(* every other condition of the type definition rule, the resulting theory   *)
(* is well-formed, and it proves x = y for distinct boolean variables.       *)
(* ------------------------------------------------------------------------- *)

let HNEG_TYPE_REDEFINITION = prove
 (`hlookup (htype_list hcore_ctxt) "bool" = SOME 0 /\
   hproves (hthyof hcore_ctxt) [] (TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool))) /\
   HCLOSED (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) /\
   hlookup (hconst_list hcore_ctxt) "absb" = NONE /\
   hlookup (hconst_list hcore_ctxt) "repb" = NONE /\
   ~("absb" = "repb") /\
   htheory_ok (hthyof (CONS (HTypeDefn "bool" (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) "absb" "repb") hcore_ctxt)) /\
   hproves (hthyof (CONS (HTypeDefn "bool" (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) "absb" "repb") hcore_ctxt)) [] ((TmVar "x" HBool) =:= (TmVar "y" HBool))`,
  MP_TAC(MATCH_MP HTHEORY_OK_STD_SIG HCORE_THEORY_OK) THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP HTYPE_OK_STD (ASSUME `his_std_sig (FST (hthyof hcore_ctxt))`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `hlookup (htype_list hcore_ctxt) "bool" = SOME 0 /\
                hlookup (hconst_list hcore_ctxt) "absb" = NONE /\
                hlookup (hconst_list hcore_ctxt) "repb" = NONE /\
                ~("absb" = "repb") /\ HCLOSED (TmAbs (TmVar "r" HBool) (TmVar "r" HBool))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[HCORE_TYPE_LIST; HCORE_CONST_LIST; hlookup; HCLOSED; HVFREE_IN;
                holterm_INJ] THEN
    CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `hterm_ok (FST (hthyof hcore_ctxt)) (TmVar "r" HBool) /\
                hterm_ok (FST (hthyof hcore_ctxt)) ((TmVar "r" HBool) =:= (TmVar "r" HBool)) /\
                ((TmVar "r" HBool) =:= (TmVar "r" HBool)) hhas_type HBool`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[hterm_ok; HTERM_OK_EQUATION; HEQUATION_HAS_TYPE_BOOL;
                 HWELLTYPED_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `hproves (hthyof hcore_ctxt) [] (TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `hproves (hthyof hcore_ctxt) [] (TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool)) =:= ((TmVar "r" HBool) =:= (TmVar "r" HBool)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`hthyof hcore_ctxt`; `[]:holterm list`;
                     `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmVar "r" HBool) =:= (TmVar "r" HBool)`; `((TmVar "r" HBool) =:= (TmVar "r" HBool))`; `"r"`; `HBool`]
                    HPROVES_INST1) THEN
      ASM_REWRITE_TAC[MAP] THEN ANTS_TAC THENL
       [MATCH_MP_TAC HPROVES_BETA THEN ASM_REWRITE_TAC[HCORE_THEORY_OK];
        ALL_TAC] THEN
      SUBGOAL_THEN `HVSUBST [((TmVar "r" HBool) =:= (TmVar "r" HBool)),(TmVar "r" HBool)] (TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmVar "r" HBool) =:= (TmVar "r" HBool)) =
                    TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool)) =:= ((TmVar "r" HBool) =:= (TmVar "r" HBool))`
       (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(SPECL [`((TmVar "r" HBool) =:= (TmVar "r" HBool))`; `"r"`; `HBool`; `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmVar "r" HBool)`; `(TmVar "r" HBool)`]
                   HVSUBST_EQUATION1) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN HWELLTYPED_TAC;
        DISCH_THEN SUBST1_TAC THEN CONV_TAC(LAND_CONV HVSUBST_CONV) THEN
        REFL_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hthyof hcore_ctxt`; `[]:holterm list`; `[]:holterm list`;
                   `((TmVar "r" HBool) =:= (TmVar "r" HBool))`; `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool))`; `((TmVar "r" HBool) =:= (TmVar "r" HBool))`] HPROVES_EQ_MP) THEN
    REWRITE_TAC[HTERM_UNION; HACONV_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HPROVES_SYM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HPROVES_REFL THEN ASM_REWRITE_TAC[HCORE_THEORY_OK]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `htheory_ok (hthyof (CONS (HTypeDefn "bool" (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) "absb" "repb") hcore_ctxt))` ASSUME_TAC THENL
   [MATCH_MP_TAC HTYPEDEFN_THEORY_OK THEN EXISTS_TAC `((TmVar "r" HBool) =:= (TmVar "r" HBool))` THEN
    ASM_REWRITE_TAC[HCORE_THEORY_OK] THEN
    REWRITE_TAC[HTYPE_LIST_CONS; HCONST_LIST_CONS] THEN CONJ_TAC THENL
     [REWRITE_TAC[htypes_of_upd; htvars; HTYVARS; HBool; ITLIST; HLIST_UNION;
                  LENGTH] THEN
      REWRITE_TAC[HSUBMAP_APPEND; hlookup] THEN
      MAP_EVERY X_GEN_TAC [`k:string`; `v:num`] THEN
      ASM_CASES_TAC `k = "bool"` THENL
       [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
        MESON_TAC[];
        SUBGOAL_THEN `~("bool" = k)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_MESON_TAC[]];
      MATCH_MP_TAC HSUBMAP_APPEND_FRESH THEN
      REWRITE_TAC[hconsts_of_upd; LET_DEF; LET_END_DEF; MAP; MEM; FST] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `thy = hthyof (CONS (HTypeDefn "bool" (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) "absb" "repb") hcore_ctxt)` THEN
  SUBGOAL_THEN `hproves thy [] (TmComb (TmConst "absb" (HFun HBool HBool)) (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)) =:= (TmVar "a" HBool)) /\
                hproves thy [] (TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmVar "r" HBool) =:=
                                (TmComb (TmConst "repb" (HFun HBool HBool)) (TmComb (TmConst "absb" (HFun HBool HBool)) (TmVar "r" HBool)) =:= (TmVar "r" HBool)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "thy" THEN CONJ_TAC THEN MATCH_MP_TAC HPROVES_AXIOM THEN
    (CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC HAXIOM_OF_UPDATE THEN
    REWRITE_TAC[haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; APPEND; MEM;
                LET_DEF; LET_END_DEF; htvars; HTYVARS; HBool; ITLIST;
                HLIST_UNION; HSTRING_SORT; MAP; htypeof; HDOMAIN_HFUN] THEN
    REWRITE_TAC[GSYM HBool];
    ALL_TAC] THEN
  SUBGOAL_THEN `his_std_sig (FST(thy:hthy))` ASSUME_TAC THENL
   [MATCH_MP_TAC HTHEORY_OK_STD_SIG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP HTYPE_OK_STD (ASSUME `his_std_sig (FST(thy:hthy))`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `hterm_ok (FST(thy:hthy)) (TmConst "absb" (HFun HBool HBool)) /\ hterm_ok (FST thy) (TmConst "repb" (HFun HBool HBool)) /\
                hterm_ok (FST thy) (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)) /\
                hterm_ok (FST thy) (TmVar "r" HBool) /\ hterm_ok (FST thy) (TmVar "x" HBool) /\
                hterm_ok (FST thy) (TmVar "y" HBool) /\ hterm_ok (FST thy) (TmVar "a" HBool)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP HPROVES_TERM_OK o check (fun th ->
      can (find_term ((=) `(TmVar "a" HBool)`)) (concl th))) THEN
    ASM_SIMP_TAC[HTERM_OK_EQUATION] THEN REWRITE_TAC[hterm_ok] THEN
    SIMP_TAC[] THEN ASM_REWRITE_TAC[hterm_ok];
    ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy [] (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`;
                   `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool))`; `TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`;
                   `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool))`] HPROVES_EQ_MP) THEN
    REWRITE_TAC[HTERM_UNION; HACONV_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmVar "r" HBool) =:= (TmVar "r" HBool)`;
                     `TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`; `"r"`; `HBool`] HPROVES_INST1) THEN
      ASM_REWRITE_TAC[MAP] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC HPROVES_BETA THEN ASM_REWRITE_TAC[];
          HHAS_TYPE_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `HVSUBST [TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool),(TmVar "r" HBool)] (TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmVar "r" HBool) =:= (TmVar "r" HBool)) =
                    TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)) =:= TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`
       (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(SPECL [`TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`; `"r"`; `HBool`; `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmVar "r" HBool)`; `(TmVar "r" HBool)`]
                   HVSUBST_EQUATION1) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [HHAS_TYPE_TAC; HWELLTYPED_TAC];
        DISCH_THEN SUBST1_TAC THEN CONV_TAC(LAND_CONV HVSUBST_CONV) THEN
        REFL_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`;
                   `TmComb (TmConst "repb" (HFun HBool HBool)) (TmComb (TmConst "absb" (HFun HBool HBool)) (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool))) =:=
                    TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`;
                   `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool))`;
                   `TmComb (TmConst "repb" (HFun HBool HBool)) (TmComb (TmConst "absb" (HFun HBool HBool)) (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool))) =:=
                    TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`] HPROVES_EQ_MP) THEN
    REWRITE_TAC[HTERM_UNION; HACONV_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HPROVES_SYM THEN
      MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`;
                     `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmVar "r" HBool) =:= (TmComb (TmConst "repb" (HFun HBool HBool)) (TmComb (TmConst "absb" (HFun HBool HBool)) (TmVar "r" HBool)) =:= (TmVar "r" HBool))`;
                     `TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`; `"r"`; `HBool`] HPROVES_INST1) THEN
      ASM_REWRITE_TAC[MAP] THEN ANTS_TAC THENL
       [HHAS_TYPE_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      MP_TAC(SPECL [`TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`; `"r"`; `HBool`; `TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool)) (TmVar "r" HBool)`;
                    `TmComb (TmConst "repb" (HFun HBool HBool)) (TmComb (TmConst "absb" (HFun HBool HBool)) (TmVar "r" HBool)) =:= (TmVar "r" HBool)`]
                   HVSUBST_EQUATION1) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [HHAS_TYPE_TAC; HWELLTYPED_TAC];
        DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(SPECL [`TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`; `"r"`; `HBool`;
                    `TmComb (TmConst "repb" (HFun HBool HBool)) (TmComb (TmConst "absb" (HFun HBool HBool)) (TmVar "r" HBool))`; `(TmVar "r" HBool)`]
                   HVSUBST_EQUATION1) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [HHAS_TYPE_TAC; HWELLTYPED_TAC];
        DISCH_THEN SUBST1_TAC] THEN
      CONV_TAC(LAND_CONV HVSUBST_CONV) THEN REFL_TAC;
      MATCH_MP_TAC HPROVES_AP_TERM THEN ASM_REWRITE_TAC[] THEN HWELLTYPED_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy [] ((TmVar "a" HBool) =:= TmComb (TmConst "absb" (HFun HBool HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`; `(TmVar "a" HBool)`;
                   `TmComb (TmConst "absb" (HFun HBool HBool)) (TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool))`; `TmComb (TmConst "absb" (HFun HBool HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool))`]
                  HPROVES_TRANS_EQ) THEN
    REWRITE_TAC[HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HPROVES_SYM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HPROVES_AP_TERM THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; HWELLTYPED_TAC] THEN
      MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`;
                     `TmComb (TmConst "repb" (HFun HBool HBool)) (TmVar "a" HBool)`; `((TmVar "r" HBool) =:= (TmVar "r" HBool))`] HPROVES_DEDUCT_ANTISYM) THEN
      REWRITE_TAC[FILTER; HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HPROVES_REFL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy [] ((TmVar "x" HBool) =:= TmComb (TmConst "absb" (HFun HBool HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool))) /\
                hproves thy [] ((TmVar "y" HBool) =:= TmComb (TmConst "absb" (HFun HBool HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`;
                     `(TmVar "a" HBool) =:= TmComb (TmConst "absb" (HFun HBool HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool))`; `(TmVar "x" HBool)`; `"a"`; `HBool`]
                    HPROVES_INST1);
      MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`;
                     `(TmVar "a" HBool) =:= TmComb (TmConst "absb" (HFun HBool HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool))`; `(TmVar "y" HBool)`; `"a"`; `HBool`]
                    HPROVES_INST1)] THEN
    (ASM_REWRITE_TAC[MAP; HHAS_TYPE_CLAUSES] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    W(fun (asl,w) ->
      let v = fst(dest_pair(hd(dest_list(lhand(lhand w))))) in
      MP_TAC(SPECL [v; `"a"`; `HBool`; `(TmVar "a" HBool)`; `TmComb (TmConst "absb" (HFun HBool HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool))`]
                   HVSUBST_EQUATION1)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [HHAS_TYPE_TAC; HWELLTYPED_TAC]; DISCH_THEN SUBST1_TAC] THEN
    BINOP_TAC THENL
     [REWRITE_TAC[HVSUBST; HREV_ASSOCD];
      MATCH_MP_TAC HVSUBST_TRIVIAL THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
      REPEAT GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      REWRITE_TAC[hequation; HEqual; HVFREE_IN; holterm_INJ;
                  holterm_DISTINCT] THEN
      CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`; `(TmVar "x" HBool)`;
                 `TmComb (TmConst "absb" (HFun HBool HBool)) ((TmVar "r" HBool) =:= (TmVar "r" HBool))`; `(TmVar "y" HBool)`] HPROVES_TRANS_EQ) THEN
  REWRITE_TAC[HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HPROVES_SYM THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Negative controls for the freshness of declared names: redeclaring a      *)
(* constant or a type, or reusing a constant name in a type definition,     *)
(* loses a theorem of the earlier context, so provability is no longer      *)
(* monotone (HEXTENDS_PROVES needs these guards).                            *)
(* ------------------------------------------------------------------------- *)

let HCORE_STD_FACTS = prove
 (`his_std_sig (hsigof hcore_ctxt) /\ htype_ok (htype_list hcore_ctxt) HBool`,
  MP_TAC(MATCH_MP HTHEORY_OK_STD_SIG HCORE_THEORY_OK) THEN
  REWRITE_TAC[HTHYOF_SIG] THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP HTYPE_OK_STD (ASSUME `his_std_sig (hsigof hcore_ctxt)`)) THEN
  SIMP_TAC[hsigof]);;

let HNEG_NEWCONST_REDECLARATION = prove
 (`HNewConst "c" HBool hupdates hcore_ctxt /\
   hproves (hthyof (CONS (HNewConst "c" HBool) hcore_ctxt)) []
           (TmConst "c" HBool =:= TmConst "c" HBool) /\
   hlookup (hconst_list (CONS (HNewConst "c" HBool) hcore_ctxt)) "c" = SOME HBool /\
   htype_ok (htype_list (CONS (HNewConst "c" HBool) hcore_ctxt)) (HFun HBool HBool) /\
   ~hproves (hthyof (CONS (HNewConst "c" (HFun HBool HBool))
                          (CONS (HNewConst "c" HBool) hcore_ctxt))) []
            (TmConst "c" HBool =:= TmConst "c" HBool)`,
  SUBGOAL_THEN `HNewConst "c" HBool hupdates hcore_ctxt` ASSUME_TAC THENL
   [MATCH_MP_TAC HOL_NEW_CONSTANT THEN REWRITE_TAC[HCORE_STD_FACTS] THEN
    REWRITE_TAC[HCORE_CONST_LIST; hlookup] THEN
    CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[HCONST_LIST_CONS; HTYPE_LIST_CONS; hconsts_of_upd;
                  htypes_of_upd; APPEND; hlookup] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_REFL THEN
    ASM_SIMP_TAC[HUPDATES_THEORY_OK; HCORE_THEORY_OK] THEN
    REWRITE_TAC[HTHYOF_SIG; hsigof; hterm_ok; HCONST_LIST_CONS; HTYPE_LIST_CONS;
                hconsts_of_upd; htypes_of_upd; APPEND; hlookup; option_INJ;
                UNWIND_THM1; HCORE_STD_FACTS] THEN
    MESON_TAC[HTYPE_SUBST_NIL];
    MP_TAC(MATCH_MP HTYPE_OK_STD (CONJUNCT1 HCORE_STD_FACTS)) THEN
    SIMP_TAC[hsigof; HCORE_STD_FACTS];
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP HPROVES_TERM_OK) THEN
    REWRITE_TAC[hequation; hterm_ok; HTHYOF_SIG; hsigof; HCONST_LIST_CONS;
                hconsts_of_upd; APPEND; hlookup; option_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[HTYPE_SUBST_HFUN; HFUN_NOT_BOOL]]);;

let HNEG_NEWTYPE_REDECLARATION = prove
 (`HNewType "t" 0 hupdates hcore_ctxt /\
   hproves (hthyof (CONS (HNewType "t" 0) hcore_ctxt)) []
           (TmVar "v" (TyApp "t" []) =:= TmVar "v" (TyApp "t" [])) /\
   hlookup (htype_list (CONS (HNewType "t" 0) hcore_ctxt)) "t" = SOME 0 /\
   ~hproves (hthyof (CONS (HNewType "t" 1) (CONS (HNewType "t" 0) hcore_ctxt))) []
            (TmVar "v" (TyApp "t" []) =:= TmVar "v" (TyApp "t" []))`,
  SUBGOAL_THEN `HNewType "t" 0 hupdates hcore_ctxt` ASSUME_TAC THENL
   [MATCH_MP_TAC HOL_NEW_TYPE THEN
    REWRITE_TAC[HCORE_TYPE_LIST; hlookup] THEN
    CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[HTYPE_LIST_CONS; htypes_of_upd; APPEND; hlookup] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_REFL THEN
    ASM_SIMP_TAC[HUPDATES_THEORY_OK; HCORE_THEORY_OK] THEN
    REWRITE_TAC[HTHYOF_SIG; hsigof; hterm_ok; HTYPE_LIST_CONS; htypes_of_upd;
                APPEND; HTYPE_OK; hlookup; LENGTH; ALL];
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP HPROVES_TERM_OK) THEN
    REWRITE_TAC[hequation; hterm_ok; HTHYOF_SIG; hsigof; HTYPE_LIST_CONS;
                htypes_of_upd; APPEND; HTYPE_OK; hlookup; LENGTH; option_INJ] THEN
    ARITH_TAC]);;

let HNEG_TYPEDEF_CONST_REUSE = prove
 (`hproves (hthyof (CONS (HNewConst "c" HBool) hcore_ctxt)) []
     (TmComb (TmAbs (TmVar "r" HBool) (TmVar "r" HBool =:= TmVar "r" HBool))
             (TmVar "r" HBool)) /\
   HCLOSED (TmAbs (TmVar "r" HBool) (TmVar "r" HBool =:= TmVar "r" HBool)) /\
   hlookup (htype_list (CONS (HNewConst "c" HBool) hcore_ctxt)) "t" = NONE /\
   hlookup (hconst_list (CONS (HNewConst "c" HBool) hcore_ctxt)) "repc" = NONE /\
   ~("c" = "repc") /\
   hlookup (hconst_list (CONS (HNewConst "c" HBool) hcore_ctxt)) "c" = SOME HBool /\
   hproves (hthyof (CONS (HNewConst "c" HBool) hcore_ctxt)) []
           (TmConst "c" HBool =:= TmConst "c" HBool) /\
   ~hproves (hthyof (CONS (HTypeDefn "t"
                (TmAbs (TmVar "r" HBool) (TmVar "r" HBool =:= TmVar "r" HBool))
                "c" "repc") (CONS (HNewConst "c" HBool) hcore_ctxt))) []
            (TmConst "c" HBool =:= TmConst "c" HBool)`,
  MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2 HNEG_NEWCONST_REDECLARATION))) THEN
  MP_TAC(CONJUNCT1(CONJUNCT2 HNEG_NEWCONST_REDECLARATION)) THEN
  MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 HNEG_NEWCONST_REDECLARATION))) THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `htheory_ok (hthyof (CONS (HNewConst "c" HBool) hcore_ctxt))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HUPDATES_THEORY_OK THEN
    REWRITE_TAC[HNEG_NEWCONST_REDECLARATION; HCORE_THEORY_OK];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ABBREV_TAC `thy = hthyof (CONS (HNewConst "c" HBool) hcore_ctxt)` THEN
    SUBGOAL_THEN `his_std_sig (FST(thy:hthy))` ASSUME_TAC THENL
     [MATCH_MP_TAC HTHEORY_OK_STD_SIG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(MATCH_MP HTYPE_OK_STD (ASSUME `his_std_sig (FST(thy:hthy))`)) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`thy:hthy`; `[]:holterm list`; `[]:holterm list`;
                   `TmVar "r" HBool =:= TmVar "r" HBool`;
                   `TmComb (TmAbs (TmVar "r" HBool)
                              (TmVar "r" HBool =:= TmVar "r" HBool))
                           (TmVar "r" HBool)`;
                   `TmVar "r" HBool =:= TmVar "r" HBool`] HPROVES_EQ_MP) THEN
    REWRITE_TAC[HTERM_UNION; HACONV_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HPROVES_SYM THEN MATCH_MP_TAC HPROVES_BETA THEN
      ASM_SIMP_TAC[hterm_ok; HTERM_OK_EQUATION; htypeof];
      MATCH_MP_TAC HPROVES_REFL THEN ASM_REWRITE_TAC[hterm_ok]];
    REWRITE_TAC[HCLOSED; HVFREE_IN; hequation; HEqual; holterm_INJ;
                holterm_DISTINCT] THEN MESON_TAC[];
    REWRITE_TAC[HTYPE_LIST_CONS; htypes_of_upd; APPEND; HCORE_TYPE_LIST;
                hlookup] THEN
    CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];
    REWRITE_TAC[HCONST_LIST_CONS; hconsts_of_upd; APPEND; HCORE_CONST_LIST;
                hlookup] THEN
    CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[];
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP HPROVES_TERM_OK) THEN
    REWRITE_TAC[hequation; hterm_ok; HTHYOF_SIG; hsigof; HCONST_LIST_CONS;
                hconsts_of_upd; LET_DEF; LET_END_DEF; APPEND; hlookup;
                option_INJ; UNWIND_THM1] THEN
    REWRITE_TAC[HTYPE_SUBST_HFUN; HFUN_NOT_BOOL]]);;
