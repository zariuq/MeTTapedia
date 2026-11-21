(* ========================================================================= *)
(* Cross-check of the port against Model: the core context (types bool, ind  *)
(* and fun; constants = and @), the translation of Model's types and terms,  *)
(* the embedding of Model's provability into the port's, its converse, the   *)
(* transfer of Model's soundness theorem, and negative controls.             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The core context: the initial context with the type ind and the choice   *)
(* constant @ : (A->bool)->A.                                                *)
(* ------------------------------------------------------------------------- *)

let hcore_ctxt = new_definition
 `hcore_ctxt =
    CONS (HNewConst "@" (HFun (HFun (TyVar "A") HBool) (TyVar "A")))
         (CONS (HNewType "ind" 0) hinit_ctxt)`;;

let HCORE_EXTENDS_INIT = prove
 (`hcore_ctxt hextends hinit_ctxt`,
  REWRITE_TAC[hcore_ctxt] THEN
  REPEAT(MATCH_MP_TAC(CONJUNCT2 hextends_RULES) THEN CONJ_TAC) THEN
  REWRITE_TAC[hextends_RULES] THEN REWRITE_TAC[hinit_ctxt] THENL
   [MATCH_MP_TAC(el 3 (CONJUNCTS hupdates_RULES));
    MATCH_MP_TAC(el 1 (CONJUNCTS hupdates_RULES))] THEN
  CONV_TAC HCONTEXT_CONV);;

let HCORE_THEORY_OK = prove
 (`htheory_ok (hthyof hcore_ctxt)`,
  REWRITE_TAC[hcore_ctxt; hinit_ctxt] THEN CONV_TAC HCONTEXT_CONV THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC HCONTEXT_CONV);;

(* ------------------------------------------------------------------------- *)
(* Translation of Model's types and terms.                                   *)
(* ------------------------------------------------------------------------- *)

let htrty = new_recursive_definition type_RECURSION
 `(htrty (Tyvar s) = TyVar s) /\
  (htrty Bool = HBool) /\
  (htrty Ind = TyApp "ind" []) /\
  (htrty (Fun a b) = HFun (htrty a) (htrty b))`;;

let htrtm = new_recursive_definition term_RECURSION
 `(htrtm (Var x ty) = TmVar x (htrty ty)) /\
  (htrtm (Equal ty) = TmConst "=" (htrty (Fun ty (Fun ty Bool)))) /\
  (htrtm (Select ty) = TmConst "@" (htrty (Fun (Fun ty Bool) ty))) /\
  (htrtm (Comb s t) = TmComb (htrtm s) (htrtm t)) /\
  (htrtm (Abs x ty t) = TmAbs (TmVar x (htrty ty)) (htrtm t))`;;

let HTRTY_INJ = prove
 (`!a b. htrty a = htrty b <=> a = b`,
  MATCH_MP_TAC type_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN TRY GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `b:type` (cases "type")) THEN
  ASM_REWRITE_TAC[htrty; HFun; HBool; holtype_INJ; holtype_DISTINCT;
                  type_INJ; type_DISTINCT; CONS_11; NOT_CONS_NIL] THEN
  CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[]);;

let HTRTM_INJ = prove
 (`!s t. htrtm s = htrtm t <=> s = t`,
  MATCH_MP_TAC term_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN TRY GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `t:term` (cases "term")) THEN
  ASM_REWRITE_TAC[htrtm; holterm_INJ; holterm_DISTINCT; term_INJ;
                  term_DISTINCT; HTRTY_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC[type_INJ; CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Typing, well-formedness, alpha-equivalence and free variables.          *)
(* ------------------------------------------------------------------------- *)

let HTRTM_HAS_TYPE = prove
 (`!tm ty. tm has_type ty ==> htrtm tm hhas_type htrty ty`,
  MATCH_MP_TAC has_type_INDUCT THEN REWRITE_TAC[htrtm; htrty] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HHAS_TYPE_VAR; HHAS_TYPE_CONST] THEN
  TRY(MATCH_MP_TAC HHAS_TYPE_ABS THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MATCH_MP_TAC HHAS_TYPE_COMB THEN EXISTS_TAC `htrty dty` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htrty]) THEN ASM_REWRITE_TAC[]);;

let HTRTM_TYPEOF = prove
 (`!tm. welltyped tm ==> htypeof (htrtm tm) = htrty (typeof tm)`,
  MESON_TAC[HTRTM_HAS_TYPE; HWELLTYPED_LEMMA; WELLTYPED]);;

let HTRTY_HFUN = prove
 (`!ty a b. htrty ty = HFun a b <=>
            ?ty1 ty2. ty = Fun ty1 ty2 /\ htrty ty1 = a /\ htrty ty2 = b`,
  MATCH_MP_TAC type_INDUCT THEN
  REWRITE_TAC[htrty; HFun; HBool; holtype_INJ; holtype_DISTINCT; type_INJ;
              type_DISTINCT; CONS_11; NOT_CONS_NIL] THEN
  CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[] THEN
  MESON_TAC[]);;

let HTRTM_WELLTYPED = prove
 (`!tm. hwelltyped (htrtm tm) <=> welltyped tm`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[htrtm; HWELLTYPED_CLAUSES; WELLTYPED_CLAUSES; holterm_INJ] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:term`; `t:term`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `welltyped s` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `welltyped t` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[HTRTM_TYPEOF; HTRTY_HFUN] THEN MESON_TAC[HTRTY_INJ];
    MESON_TAC[]]);;

let HTRTY_OK = prove
 (`!ty. htype_ok (htype_list hcore_ctxt) (htrty ty)`,
  MATCH_MP_TAC type_INDUCT THEN
  REWRITE_TAC[htrty; hcore_ctxt; hinit_ctxt] THEN CONV_TAC HCONTEXT_CONV THEN
  SIMP_TAC[]);;

let HTRTM_TERM_OK = prove
 (`!tm. welltyped tm ==> hterm_ok (hsigof hcore_ctxt) (htrtm tm)`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[htrtm; hterm_ok; WELLTYPED_CLAUSES] THEN
  REWRITE_TAC[hsigof; FST; SND; HTRTY_OK] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `a:type` THEN REWRITE_TAC[hcore_ctxt; hinit_ctxt] THEN
    CONV_TAC HCONTEXT_CONV THEN REWRITE_TAC[UNWIND_THM1] THEN
    EXISTS_TAC `[htrty a,TyVar "A"]` THEN
    REWRITE_TAC[htrty; HFun; HBool; HTYPE_SUBST; MAP; HREV_ASSOCD];
    X_GEN_TAC `a:type` THEN REWRITE_TAC[hcore_ctxt; hinit_ctxt] THEN
    CONV_TAC HCONTEXT_CONV THEN REWRITE_TAC[UNWIND_THM1] THEN
    EXISTS_TAC `[htrty a,TyVar "A"]` THEN
    REWRITE_TAC[htrty; HFun; HBool; HTYPE_SUBST; MAP; HREV_ASSOCD];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM htrtm; HTRTM_WELLTYPED; WELLTYPED_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`a0:string`; `htrty a1`] THEN
    ASM_SIMP_TAC[HTRTY_OK]]);;

let HTRTM_ALPHAVARS = prove
 (`!env s t. ALPHAVARS env (s,t) <=>
             HALPHAVARS (MAP (\(a,b). (htrtm a,htrtm b)) env) (htrtm s,htrtm t)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALPHAVARS; HALPHAVARS; MAP; HTRTM_INJ] THEN
  SPEC_TAC(`h:term#term`,`p:term#term`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ; HTRTM_INJ]);;

let HTRTM_RACONV = prove
 (`!s t env. RACONV env (s,t) <=>
             HRACONV (MAP (\(a,b). (htrtm a,htrtm b)) env) (htrtm s,htrtm t)`,
  MATCH_MP_TAC term_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN TRY GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `t:term` (cases "term")) THEN
  ASM_REWRITE_TAC[RACONV; HRACONV; htrtm; HTRTM_ALPHAVARS; HTRTY_INJ;
                  htypeof] THEN
  CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC[htrty; type_INJ; HFun; HBool; holtype_INJ; CONS_11] THEN
  REWRITE_TAC[GSYM HFun; GSYM HBool; HTRTY_INJ; GSYM htrty] THEN
  REWRITE_TAC[MAP] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[htrtm] THEN MESON_TAC[]);;

let HTRTM_ACONV = prove
 (`!s t. ACONV s t <=> HACONV (htrtm s) (htrtm t)`,
  REWRITE_TAC[ACONV; HACONV; HTRTM_RACONV; MAP]);;

let HTRTM_VFREE_IN = prove
 (`!t v. VFREE_IN v t <=> HVFREE_IN (htrtm v) (htrtm t)`,
  MATCH_MP_TAC term_INDUCT THEN
  ASM_REWRITE_TAC[VFREE_IN; HVFREE_IN; htrtm] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM htrtm; HTRTM_INJ]);;

let HTRTM_FILTER = prove
 (`!c l. MAP htrtm (FILTER ((~) o ACONV c) l) =
         FILTER ((~) o HACONV (htrtm c)) (MAP htrtm l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; MAP; o_THM] THEN
  REWRITE_TAC[HTRTM_ACONV] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]);;

let HTRTM_EQUATION = prove
 (`!s t. welltyped s ==> htrtm (s === t) = htrtm s =:= htrtm t`,
  SIMP_TAC[equation; hequation; htrtm; HEqual; HTRTM_TYPEOF; htrty]);;

let HTRTM_TERM_UNION = prove
 (`!l1 l2. MAP htrtm (TERM_UNION l1 l2) =
           HTERM_UNION (MAP htrtm l1) (MAP htrtm l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TERM_UNION; HTERM_UNION; MAP] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN GEN_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  SUBGOAL_THEN `EX (HACONV (htrtm h)) (MAP htrtm (TERM_UNION t l2)) <=>
                EX (ACONV h) (TERM_UNION t l2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EX_MAP; o_DEF; GSYM HTRTM_ACONV] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MAP]);;

(* ------------------------------------------------------------------------- *)
(* Substitution and type instantiation agree up to alpha-equivalence.      *)
(* ------------------------------------------------------------------------- *)

let htrilist = new_definition
 `htrilist ilist = MAP (\(a,b). (htrtm a,htrtm b)) ilist`;;

let htrtyin = new_definition
 `htrtyin tyin = MAP (\(a,b). (htrty a,htrty b)) tyin`;;

let HTRTM_EQ_VAR = prove
 (`!p x ty. htrtm p = TmVar x (htrty ty) <=> p = Var x ty`,
  REWRITE_TAC[GSYM(CONJUNCT1 htrtm); HTRTM_INJ]);;

let HTRTY_EQ_TYVAR = prove
 (`!p v. htrty p = TyVar v <=> p = Tyvar v`,
  REWRITE_TAC[GSYM(CONJUNCT1 htrty); HTRTY_INJ]);;

let HTRTM_REV_ASSOCD = prove
 (`!ilist x ty.
        htrtm (REV_ASSOCD (Var x ty) ilist (Var x ty)) =
        HREV_ASSOCD (TmVar x (htrty ty)) (htrilist ilist) (TmVar x (htrty ty))`,
  REWRITE_TAC[htrilist] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REV_ASSOCD; HREV_ASSOCD; MAP; htrtm] THEN
  SPEC_TAC(`h:term#term`,`p:term#term`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[REV_ASSOCD; HREV_ASSOCD; HTRTM_EQ_VAR] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let HTRTY_TYPE_SUBST = prove
 (`!tyin ty. htrty (TYPE_SUBST tyin ty) = HTYPE_SUBST (htrtyin tyin) (htrty ty)`,
  GEN_TAC THEN MATCH_MP_TAC type_INDUCT THEN
  REWRITE_TAC[TYPE_SUBST; htrty; HTYPE_SUBST_HFUN; HTYPE_SUBST_HBOOL] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[HTYPE_SUBST; htrtyin] THEN
    SPEC_TAC(`tyin:(type#type)list`,`l:(type#type)list`) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REV_ASSOCD; HREV_ASSOCD; MAP; htrty] THEN
    SPEC_TAC(`h:type#type`,`p:type#type`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[REV_ASSOCD; HREV_ASSOCD; HTRTY_EQ_TYVAR] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[HTYPE_SUBST; MAP];
    SIMP_TAC[]]);;

let HTRILIST_FILTER = prove
 (`!ilist x ty.
        htrilist (FILTER (\(s',s). ~(s = Var x ty)) ilist) =
        FILTER (\(s',s). ~(s = TmVar x (htrty ty))) (htrilist ilist)`,
  REWRITE_TAC[htrilist] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FILTER; MAP] THEN
  SPEC_TAC(`h:term#term`,`p:term#term`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[HTRTM_EQ_VAR] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let HTRTM_VFREE_IN_VAR = prove
 (`!t y yty. HVFREE_IN (TmVar y yty) (htrtm t) <=>
             ?ty. yty = htrty ty /\ VFREE_IN (Var y ty) t`,
  MATCH_MP_TAC term_INDUCT THEN
  ASM_REWRITE_TAC[htrtm; HVFREE_IN; VFREE_IN; holterm_INJ; holterm_DISTINCT;
                  term_INJ; term_DISTINCT] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MESON_TAC[];
    REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[HTRTY_INJ]]);;

let REV_ASSOCD_MEM_MODEL = prove
 (`!l:(B#A)list x d. MEM (REV_ASSOCD x l d,x) l \/ REV_ASSOCD x l d = d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD; MEM] THEN
  SPEC_TAC(`h:B#A`,`p:B#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[REV_ASSOCD; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let REV_ASSOCD_WELLTYPED_MODEL = prove
 (`!ilist x ty.
        (!s s'. MEM (s',s) ilist ==> ?x ty. s = Var x ty /\ s' has_type ty)
        ==> welltyped (REV_ASSOCD (Var x ty) ilist (Var x ty))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ilist:(term#term)list`; `Var x ty`; `Var x ty`]
                REV_ASSOCD_MEM_MODEL) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[WELLTYPED_CLAUSES] THEN
  ASM_MESON_TAC[welltyped]);;

let HTRTM_VSUBST_DB = prove
 (`!t. welltyped t
       ==> !ilist. (!s s'. MEM (s',s) ilist ==> ?x ty. s = Var x ty /\ s' has_type ty)
                   ==> hdb (htrtm (VSUBST ilist t)) =
                       hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) (htrilist ilist))
                                 (hdb (htrtm t))`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[VSUBST; htrtm; hdb; hdbVSUBST; WELLTYPED_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[HTRTM_REV_ASSOCD; HREV_ASSOCD_MAP_HDB];
    REPEAT STRIP_TAC THEN REWRITE_TAC[hdbterm_INJ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:string`; `bty:type`; `tm:term`] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN ASSUME_TAC(MP th (ASSUME `welltyped tm`))) THEN
  X_GEN_TAC `ilist:(term#term)list` THEN DISCH_TAC THEN
  REWRITE_TAC[hdest_var; htypeof; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = Var b bty)) (ilist:(term#term)list)` THEN
  SUBGOAL_THEN `!s s'. MEM (s',s) ilist' ==> ?x ty. s = Var x ty /\ s' has_type ty`
  ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MEM_FILTER] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `MAP (\(x,y). (hdb x,hdb y)) (htrilist ilist') =
    FILTER (\(x,y). ~(y = hdbVar b (htrty bty)))
           (MAP (\(x,y). (hdb x,hdb y)) (htrilist ilist))`
  ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[HTRILIST_FILTER; MAP_HDB_FILTER_NEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) (htrilist ilist'))
              (hbind (b,htrty bty) 0 (hdb (htrtm tm))) =
    hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) (htrilist ilist))
              (hbind (b,htrty bty) 0 (hdb (htrtm tm)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HDBVSUBST_FREES THEN ASM_REWRITE_TAC[HDBVFREE_IN_BIND] THEN
    REWRITE_TAC[HREV_ASSOCD_FILTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hwelltyped (htrtm tm)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HTRTM_WELLTYPED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z y yty. hdbVFREE_IN (hdbVar z (htrty bty))
                (hdb (HREV_ASSOCD (TmVar y (htrty yty)) (htrilist ilist')
                                  (TmVar y (htrty yty)))) <=>
              VFREE_IN (Var z bty) (REV_ASSOCD (Var y yty) ilist' (Var y yty))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM HTRTM_REV_ASSOCD] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) HDBVFREE_IN_VAR (lhand w))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[HTRTM_WELLTYPED] THEN
      MATCH_MP_TAC REV_ASSOCD_WELLTYPED_MODEL THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[HTRTM_VFREE_IN; htrtm];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[htrtm; hdb; hdest_var; htypeof; hdbterm_INJ] THENL
   [ABBREV_TAC `zn = VARIANT (VSUBST ilist' tm) b bty` THEN
  SUBGOAL_THEN
   `hdb (htrtm (VSUBST (CONS (Var zn bty,Var b bty) ilist') tm)) =
    hdbVSUBST (MAP (\(x,y). (hdb x,hdb y))
                   (htrilist (CONS (Var zn bty,Var b bty) ilist')))
              (hdb (htrtm tm))`
  SUBST1_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
    ASM_MESON_TAC[has_type_RULES];
    ALL_TAC] THEN
  REWRITE_TAC[htrilist; MAP] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[htrtm; hdb; GSYM htrilist] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) (htrilist ilist'))
                        (hbind (b,htrty bty) 0 (hdb (htrtm tm)))` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC HBIND_DBVSUBST_CONS THEN
  REWRITE_TAC[HDBVFREE_IN_DBVSUBST; HDBVFREE_IN_BIND; HREV_ASSOCD_MAP_HDB] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `hdbVFREE_IN (hdbVar y ty) (hdb (htrtm tm))` THEN
  ASM_SIMP_TAC[HDBVFREE_IN_VAR; HTRTM_VFREE_IN_VAR] THEN
  DISCH_THEN(X_CHOOSE_THEN `yty:type` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `hdbVFREE_IN (hdbVar zn (htrty bty))
                 (hdb (HREV_ASSOCD (TmVar y (htrty yty)) (htrilist ilist')
                                   (TmVar y (htrty yty))))` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`VSUBST ilist' tm`; `b:string`; `bty:type`] VARIANT) THEN
  ASM_REWRITE_TAC[VFREE_IN_VSUBST] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hdb (htrtm (VSUBST ilist' tm)) =
                hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) (htrilist ilist'))
                          (hdb (htrtm tm))`
  SUBST1_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) (htrilist ilist'))
                        (hbind (b,htrty bty) 0 (hdb (htrtm tm)))` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC HBIND_DBVSUBST THEN
  REWRITE_TAC[htrilist; GSYM MAP_o; MEM_MAP; EXISTS_PAIR_THM; o_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN CONJ_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     is_var (lhs (concl th)) && not(type_of(lhs(concl th)) = `:(term#term)list`)))) THEN
    FIRST_X_ASSUM(MP_TAC o SYM o check (fun th -> is_eq (concl th) &&
     can (find_term (fun t -> t = `hdb`)) (concl th))) THEN
  REWRITE_TAC[HDB_VAR; HTRTM_EQ_VAR] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `MEM (p1:term,Var b bty) ilist'` THEN EXPAND_TAC "ilist'" THEN
  REWRITE_TAC[MEM_FILTER] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:hdbterm` THEN REWRITE_TAC[PAIR_EQ; MAP_o; GSYM htrilist] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     is_var (lhs (concl th)) && not(type_of(lhs(concl th)) = `:(term#term)list`)))) THEN
  SUBGOAL_THEN `?y yty. p2 = Var y yty` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htrtm; hdb]) THEN REWRITE_TAC[htrtm; hdb] THEN
  REWRITE_TAC[HREV_ASSOCD_MAP_HDB] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `hdbVFREE_IN (hdbVar y (htrty yty)) (hdb (htrtm tm))` THEN
  ASM_SIMP_TAC[HDBVFREE_IN_VAR; HTRTM_VFREE_IN_VAR; HTRTY_INJ] THEN
  REWRITE_TAC[UNWIND_THM1] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ilist':(term#term)list`; `Var y yty`; `Var y yty`]
                REV_ASSOCD_MEM_MODEL) THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `~EX (\(s',s). VFREE_IN (Var b bty) s' /\ VFREE_IN s tm)
                     (ilist':(term#term)list)` THEN
    REWRITE_TAC[NOT_EX; GSYM ALL_MEM] THEN
    DISCH_THEN(MP_TAC o SPEC `(REV_ASSOCD (Var y yty) ilist' (Var y yty),
                               Var y yty)`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[VFREE_IN; term_INJ] THEN
    UNDISCH_TAC `MEM (p1:term,Var y yty) ilist'` THEN EXPAND_TAC "ilist'" THEN
    REWRITE_TAC[MEM_FILTER] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[term_INJ] THEN MESON_TAC[]]);;

let HTRILIST_COND = prove
 (`!ilist. (!s s'. MEM (s',s) ilist ==> ?x ty. s = Var x ty /\ s' has_type ty)
           ==> (!s s'. MEM (s',s) (htrilist ilist)
                       ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty) /\
               (!k v. MEM (v,k) (htrilist ilist)
                      ==> hwelltyped v /\ ?x ty. k = TmVar x ty)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[htrilist; MEM_MAP; EXISTS_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `a:term` (X_CHOOSE_THEN `b:term`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:term`; `a:term`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[htrtm] THEN
  ASM_MESON_TAC[HTRTM_HAS_TYPE; HTRTM_WELLTYPED; welltyped]);;

let HTRTM_VSUBST = prove
 (`!t ilist.
        welltyped t /\
        (!s s'. MEM (s',s) ilist ==> ?x ty. s = Var x ty /\ s' has_type ty)
        ==> HACONV (htrtm (VSUBST ilist t)) (HVSUBST (htrilist ilist) (htrtm t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HTRILIST_COND) THEN
  SUBGOAL_THEN `hwelltyped (htrtm t)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HTRTM_WELLTYPED]; ALL_TAC] THEN
  SUBGOAL_THEN `hwelltyped (htrtm (VSUBST ilist t)) /\
                hwelltyped (HVSUBST (htrilist ilist) (htrtm t))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[HTRTM_WELLTYPED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HVSUBST_WELLTYPED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HACONV_DB] THEN
  MP_TAC(SPEC `t:term` HTRTM_VSUBST_DB) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `ilist:(term#term)list`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(SPEC `htrtm t` HVSUBST_DBVSUBST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MODEL_INST_CORE_CASES = prove
 (`!tm env tyin.
        welltyped tm /\
        (!s s'. MEM (s,s') env
                ==> ?x ty. s = Var x ty /\ s' = Var x (TYPE_SUBST tyin ty))
        ==> (?x ty. INST_CORE env tyin tm = Clash(Var x (TYPE_SUBST tyin ty)) /\
                    VFREE_IN (Var x ty) tm /\
                    ~(REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) =
                      Var x ty)) \/
            (!x ty. VFREE_IN (Var x ty) tm
                    ==> REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) =
                        Var x ty) /\
            (?tm'. INST_CORE env tyin tm = Result tm' /\
                   tm' has_type (TYPE_SUBST tyin (typeof tm)) /\
                   (!u uty. VFREE_IN (Var u uty) tm' <=>
                            ?oty. VFREE_IN (Var u oty) tm /\
                                  uty = TYPE_SUBST tyin oty))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sizeof tm`; `tm:term`; `env:(term#term)list`;
                `tyin:(type#type)list`] SEMANTICS_INST_CORE) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MODEL_SIZEOF_INDUCT = prove
 (`!P. (!tm. (!tm'. sizeof tm' < sizeof tm ==> P tm') ==> P tm) ==> !tm. P tm`,
  GEN_TAC THEN MP_TAC(ISPEC `sizeof` WF_MEASURE) THEN
  REWRITE_TAC[WF_IND; MEASURE] THEN MESON_TAC[]);;

let HTRTYIN_TYPE_SUBST = prove
 (`!tyin ty. HTYPE_SUBST (htrtyin tyin) (htrty ty) = htrty (TYPE_SUBST tyin ty)`,
  REWRITE_TAC[HTRTY_TYPE_SUBST]);;

let MRESULT_CASES = prove
 (`!r. ~IS_CLASH r <=> ?t. r = Result t`,
  MATCH_MP_TAC result_INDUCT THEN
  REWRITE_TAC[IS_CLASH; result_INJ; result_DISTINCT] THEN MESON_TAC[]);;
let MRESULT_CASES2 = prove
 (`!r. IS_RESULT r <=> ?t. r = Result t`,
  MATCH_MP_TAC result_INDUCT THEN
  REWRITE_TAC[IS_RESULT; result_INJ; result_DISTINCT] THEN MESON_TAC[]);;

let INST_CORE_ABS = el 4 (CONJUNCTS INST_CORE);;

let HTRTM_INST_CORE_DB = prove
 (`!tm env tyin tmi.
      welltyped tm /\
      (!s s'. MEM (s,s') env
              ==> ?x ty. s = Var x ty /\ s' = Var x (TYPE_SUBST tyin ty)) /\
      INST_CORE env tyin tm = Result tmi
      ==> hdb (htrtm tmi) = hdbINST (htrtyin tyin) (hdb (htrtm tm))`,
  MATCH_MP_TAC MODEL_SIZEOF_INDUCT THEN GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `tm:term` (cases "term")) THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`env:(term#term)list`; `tyin:(type#type)list`;
                       `tmi:term`] THENL
   [REWRITE_TAC[INST_CORE; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[result_INJ; result_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[htrtm; hdb; hdbINST; HTRTY_TYPE_SUBST];
    REWRITE_TAC[INST_CORE; result_INJ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[htrtm; hdb; hdbINST; GSYM HTRTY_TYPE_SUBST; TYPE_SUBST];
    REWRITE_TAC[INST_CORE; result_INJ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[htrtm; hdb; hdbINST; GSYM HTRTY_TYPE_SUBST; TYPE_SUBST];
    REWRITE_TAC[WELLTYPED_CLAUSES; INST_CORE; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN STRIP_TAC THENL
   [UNDISCH_TAC `IS_CLASH (INST_CORE env tyin a0)` THEN
    ASM_REWRITE_TAC[IS_CLASH];
    UNDISCH_TAC `IS_CLASH (INST_CORE env tyin a1)` THEN
    ASM_REWRITE_TAC[IS_CLASH];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MRESULT_CASES; result_INJ]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `?t. INST_CORE env tyin a0 = Result t` THEN
  DISCH_THEN(X_CHOOSE_TAC `r0:term`) THEN
  UNDISCH_TAC `?t. INST_CORE env tyin a1 = Result t` THEN
  DISCH_THEN(X_CHOOSE_TAC `r1:term`) THEN
  ASM_REWRITE_TAC[RESULT; htrtm; hdb; hdbINST; hdbterm_INJ] THEN
  CONJ_TAC THENL
   [USE_THEN "ih" (MP_TAC o SPEC `a0:term`);
    USE_THEN "ih" (MP_TAC o SPEC `a1:term`)] THEN
  REWRITE_TAC[sizeof; ARITH_RULE `s < 1 + s + t /\ t < 1 + s + t`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[WELLTYPED_CLAUSES] THEN STRIP_TAC THEN
  UNDISCH_TAC `INST_CORE env tyin (Abs a0 a1 a2) = Result tmi` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [INST_CORE_ABS] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[htrtm; hdb; hdest_var; htypeof; hdbINST] THEN
  USE_THEN "ih" (MP_TAC o SPEC `a2:term`) THEN
  REWRITE_TAC[sizeof; ARITH_RULE `t < 2 + t`] THEN
  DISCH_THEN(LABEL_TAC "iht") THEN
  COND_CASES_TAC THENL [ALL_TAC; COND_CASES_TAC] THENL
     [REWRITE_TAC[result_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `IS_RESULT (INST_CORE (CONS (Var a0 a1,Var a0 (TYPE_SUBST tyin a1))
                                          env) tyin a2)` THEN
  REWRITE_TAC[MRESULT_CASES2] THEN DISCH_THEN(X_CHOOSE_TAC `r1:term`) THEN
  ASM_REWRITE_TAC[RESULT; htrtm; hdb; hdest_var; htypeof; hdbterm_INJ] THEN
  REWRITE_TAC[HTRTY_TYPE_SUBST] THEN
  SUBGOAL_THEN `hdb (htrtm r1) = hdbINST (htrtyin tyin) (hdb (htrtm a2))`
  SUBST1_TAC THENL
   [USE_THEN "iht" MATCH_MP_TAC THEN
    EXISTS_TAC `CONS (Var a0 a1,Var a0 (TYPE_SUBST tyin a1)) env` THEN
    ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC HDBINST_BIND THEN
  X_GEN_TAC `ty':holtype` THEN
  SUBGOAL_THEN `hwelltyped (htrtm a2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HTRTM_WELLTYPED]; ALL_TAC] THEN
  ASM_SIMP_TAC[HDBVFREE_IN_VAR; HTRTM_VFREE_IN_VAR] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `oty:type` STRIP_ASSUME_TAC)
    MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[GSYM HTRTY_TYPE_SUBST; HTRTY_INJ] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a2:term`; `CONS (Var a0 a1,Var a0 (TYPE_SUBST tyin a1)) env`;
                `tyin:(type#type)list`] MODEL_INST_CORE_CASES) THEN
  ASM_REWRITE_TAC[result_DISTINCT; result_INJ] THEN
  ANTS_TAC THENL [REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`a0:string`; `oty:type`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[REV_ASSOCD; term_INJ] THEN MESON_TAC[];
      DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
     can (find_term (fun t -> t = `IS_RESULT`)) (concl th))) THEN
  ASM_REWRITE_TAC[IS_RESULT];
      MP_TAC(SPECL [`a2:term`; `[]:(term#term)list`; `tyin:(type#type)list`]
               MODEL_INST_CORE_CASES) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:term` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[RESULT] THEN
  ABBREV_TAC `z = VARIANT t0 a0 (TYPE_SUBST tyin a1)` THEN
  SUBGOAL_THEN `!oty. VFREE_IN (Var z oty) a2
                      ==> ~(TYPE_SUBST tyin oty = TYPE_SUBST tyin a1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t0:term`; `a0:string`; `TYPE_SUBST tyin a1`] VARIANT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t' = VSUBST [Var z a1,Var a0 a1] a2` THEN
  SUBGOAL_THEN `sizeof t' = sizeof a2 /\ welltyped t'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SIZEOF_VSUBST THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
      MESON_TAC[];
      MATCH_MP_TAC VSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      MESON_TAC[has_type_RULES]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k kty. VFREE_IN (Var k kty) t' <=>
            VFREE_IN (Var a0 a1) a2 /\ k = z /\ kty = a1 \/
            VFREE_IN (Var k kty) a2 /\ ~(k = a0 /\ kty = a1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN REWRITE_TAC[VFREE_IN_VSUBST] THEN
    REWRITE_TAC[REV_ASSOCD] THEN
    REWRITE_TAC[COND_RAND; VFREE_IN; term_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [INST_CORE_ABS] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      COND_CASES_TAC THENL [ALL_TAC; COND_CASES_TAC] THENL
   [REWRITE_TAC[result_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[MRESULT_CASES2] o check (fun th ->
      can (find_term (fun t -> t = `IS_RESULT`)) (concl th) &&
      not (is_neg (concl th)))) THEN
    DISCH_THEN(X_CHOOSE_TAC `r2:term`) THEN
    ASM_REWRITE_TAC[RESULT; htrtm; hdb; hdest_var; htypeof; hdbterm_INJ] THEN
    REWRITE_TAC[HTRTY_TYPE_SUBST] THEN
    SUBGOAL_THEN `hdb (htrtm r2) = hdbINST (htrtyin tyin) (hdb (htrtm t'))`
    SUBST1_TAC THENL
     [USE_THEN "ih" (MP_TAC o SPEC `t':term`) THEN
      REWRITE_TAC[sizeof; ASSUME `sizeof t' = sizeof a2`;
                  ARITH_RULE `t < 2 + t`] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `CONS (Var z a1,Var z (TYPE_SUBST tyin a1)) env` THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `hwelltyped (htrtm a2) /\ hwelltyped (htrtm t')`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[HTRTM_WELLTYPED]; ALL_TAC] THEN
    SUBGOAL_THEN `hdb (htrtm t') =
                  hdbVSUBST [hdbVar z (htrty a1),hdbVar a0 (htrty a1)]
                            (hdb (htrtm a2))`
    ASSUME_TAC THENL
     [EXPAND_TAC "t'" THEN MP_TAC(SPEC `a2:term` HTRTM_VSUBST_DB) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `[Var z a1,Var a0 a1]`) THEN
      REWRITE_TAC[MEM; PAIR_EQ; htrilist; MAP] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[htrtm; hdb] THEN
      ANTS_TAC THENL [MESON_TAC[has_type_RULES]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `hbind (a0,htrty a1) 0 (hdb (htrtm a2)) =
                  hbind (z,htrty a1) 0 (hdb (htrtm t'))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`hdb (htrtm a2)`; `z:string`; `htrty a1`; `a0:string`;
                     `htrty a1`; `0`; `[]:(hdbterm#hdbterm)list`]
                    HBIND_DBVSUBST_CONS) THEN
      REWRITE_TAC[HDBVSUBST_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[HDBVFREE_IN_BIND] THEN
      ASM_SIMP_TAC[HDBVFREE_IN_VAR; HTRTM_VFREE_IN_VAR; HTRTY_INJ] THEN
      REWRITE_TAC[UNWIND_THM1] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC HDBINST_BIND THEN
    X_GEN_TAC `ty':holtype` THEN
    ASM_SIMP_TAC[HDBVFREE_IN_VAR; HTRTM_VFREE_IN_VAR] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `oty:type` STRIP_ASSUME_TAC)
      MP_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[GSYM HTRTY_TYPE_SUBST; HTRTY_INJ] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`t':term`; `CONS (Var z a1,Var z (TYPE_SUBST tyin a1)) env`;
                  `tyin:(type#type)list`] MODEL_INST_CORE_CASES) THEN
    ASM_REWRITE_TAC[result_DISTINCT; result_INJ] THEN
    ANTS_TAC THENL [REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`z:string`; `oty:type`] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[REV_ASSOCD; term_INJ] THEN MESON_TAC[];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
       can (find_term (fun t -> t = `IS_RESULT`)) (concl th))) THEN
    ASM_REWRITE_TAC[IS_RESULT];
    DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(SPECL [`t':term`; `CONS (Var z a1,Var z (TYPE_SUBST tyin a1)) env`;
                  `tyin:(type#type)list`] MODEL_INST_CORE_CASES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:string` (X_CHOOSE_THEN `ty:type`
        STRIP_ASSUME_TAC)) THEN
      UNDISCH_TAC `CLASH (INST_CORE (CONS (Var z a1,Var z (TYPE_SUBST tyin a1))
                                        env) tyin t') =
                   Var z (TYPE_SUBST tyin a1)` THEN
      ASM_REWRITE_TAC[CLASH; term_INJ] THEN STRIP_TAC THEN
  UNDISCH_TAC `x:string = z` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~(REV_ASSOCD (Var z (TYPE_SUBST tyin ty))
                    (CONS (Var z a1,Var z (TYPE_SUBST tyin a1)) env)
                    (Var z ty) = Var z ty)` THEN
  ASM_REWRITE_TAC[REV_ASSOCD; term_INJ] THEN DISCH_TAC THEN
  UNDISCH_TAC `VFREE_IN (Var z ty) t'` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[];
      STRIP_TAC THEN
  UNDISCH_TAC `~IS_RESULT (INST_CORE (CONS (Var z a1,Var z (TYPE_SUBST tyin a1))
                                           env) tyin t')` THEN
  ASM_REWRITE_TAC[IS_RESULT]]]]]);;

let HTRTM_INST = prove
 (`!t tyin. welltyped t
            ==> HACONV (htrtm (INST tyin t)) (HINST (htrtyin tyin) (htrtm t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t:term`; `[]:(term#term)list`; `tyin:(type#type)list`]
               MODEL_INST_CORE_CASES) THEN
  ASM_REWRITE_TAC[MEM; REV_ASSOCD] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:term` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `INST tyin t = t1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[INST_DEF; RESULT]; ALL_TAC] THEN
  SUBGOAL_THEN `hwelltyped (htrtm t1) /\ hwelltyped (HINST (htrtyin tyin) (htrtm t))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[HTRTM_WELLTYPED] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[welltyped];
      MATCH_MP_TAC HINST_WELLTYPED THEN ASM_REWRITE_TAC[HTRTM_WELLTYPED]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HACONV_DB; HINST_DBINST; HTRTM_WELLTYPED] THEN
  MATCH_MP_TAC HTRTM_INST_CORE_DB THEN
  MAP_EVERY EXISTS_TAC [`[]:(term#term)list`] THEN
  ASM_REWRITE_TAC[MEM]);;

(* ------------------------------------------------------------------------- *)
(* Model provability embeds into the port.                                 *)
(* ------------------------------------------------------------------------- *)

let proves_SINDUCT = derive_strong_induction(prove_RULES,proves_INDUCT);;
let MODEL_PROVES_BOOL = prove
 (`!asl p. asl |- p ==> p has_type Bool /\ ALL (\a. a has_type Bool) asl`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP HOL_IS_SOUND) THEN
  SIMP_TAC[sequent; ALL]);;
let HCORE_FST = prove
 (`FST (hthyof hcore_ctxt) = hsigof hcore_ctxt /\
   FST (FST (hthyof hcore_ctxt)) = htype_list hcore_ctxt`,
  REWRITE_TAC[hthyof; hsigof]);;
let HTRTM_BOOL_OK = prove
 (`!a. a has_type Bool
       ==> hterm_ok (FST (hthyof hcore_ctxt)) (htrtm a) /\
           htrtm a hhas_type HBool`,
  REWRITE_TAC[HCORE_FST] THEN
  MESON_TAC[HTRTM_TERM_OK; HTRTM_HAS_TYPE; htrty; welltyped]);;

let HTRTYIN_OK = prove
 (`!tyin. ALL (htype_ok (FST (FST (hthyof hcore_ctxt)))) (MAP FST (htrtyin tyin))`,
  REWRITE_TAC[HCORE_FST; htrtyin; GSYM ALL_MEM; MEM_MAP; EXISTS_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[HTRTY_OK]);;
let ALL_HTRTM_BOOL_OK = prove
 (`!l. ALL (\a. a has_type Bool) l
       ==> ALL (\p. hterm_ok (FST (hthyof hcore_ctxt)) p /\ p hhas_type HBool)
               (MAP htrtm l)`,
  REWRITE_TAC[ALL_MAP] THEN GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
  SIMP_TAC[o_THM; HTRTM_BOOL_OK]);;

let HOL_EMBEDS = prove
 (`!asl p. asl |- p
           ==> hproves (hthyof hcore_ctxt) (MAP htrtm asl) (htrtm p)`,
  MATCH_MP_TAC proves_SINDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MAP; HTRTM_EQUATION] THEN
  MATCH_MP_TAC HPROVES_REFL THEN
  ASM_SIMP_TAC[HCORE_THEORY_OK; HCORE_FST; HTRTM_TERM_OK];
    REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`asl1:term list`; `l === m1`] MODEL_PROVES_BOOL) THEN
  MP_TAC(SPECL [`asl2:term list`; `m2 === r`] MODEL_PROVES_BOOL) THEN
  ASM_REWRITE_TAC[EQUATION_HAS_TYPE_BOOL] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[HTRTM_TERM_UNION; HTRTM_EQUATION] THEN
  MATCH_MP_TAC HPROVES_TRANS THEN
  MAP_EVERY EXISTS_TAC [`htrtm m1`; `htrtm m2`] THEN
  ASM_SIMP_TAC[GSYM HTRTM_ACONV; GSYM HTRTM_EQUATION];
    REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`asl1:term list`; `l1 === r1`] MODEL_PROVES_BOOL) THEN
  MP_TAC(SPECL [`asl2:term list`; `l2 === r2`] MODEL_PROVES_BOOL) THEN
  ASM_REWRITE_TAC[EQUATION_HAS_TYPE_BOOL] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[HTRTM_TERM_UNION; HTRTM_EQUATION] THEN
  REWRITE_TAC[htrtm] THEN MATCH_MP_TAC HPROVES_MK_COMB THEN
  ASM_SIMP_TAC[GSYM HTRTM_EQUATION; GSYM htrtm; HTRTM_WELLTYPED];
    REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`asl:term list`; `l === r`] MODEL_PROVES_BOOL) THEN
  ASM_REWRITE_TAC[EQUATION_HAS_TYPE_BOOL] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (Abs x ty l)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WELLTYPED_CLAUSES]; ALL_TAC] THEN
  ASM_SIMP_TAC[HTRTM_EQUATION] THEN REWRITE_TAC[htrtm] THEN
  MATCH_MP_TAC HPROVES_ABS THEN
  ASM_SIMP_TAC[GSYM HTRTM_EQUATION; HCORE_FST; HTRTY_OK] THEN
  UNDISCH_TAC `~EX (VFREE_IN (Var x ty)) asl` THEN
  REWRITE_TAC[EX_MAP; o_DEF; GSYM(CONJUNCT1 htrtm); GSYM HTRTM_VFREE_IN] THEN
  REWRITE_TAC[ETA_AX];
    REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped (Comb (Abs x ty t) (Var x ty))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WELLTYPED_CLAUSES; typeof] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HTRTM_EQUATION; MAP] THEN REWRITE_TAC[htrtm] THEN
  MATCH_MP_TAC HPROVES_BETA THEN
  ASM_SIMP_TAC[HCORE_THEORY_OK; HCORE_FST; HTRTY_OK; HTRTM_TERM_OK];
    REPEAT STRIP_TAC THEN REWRITE_TAC[MAP] THEN MATCH_MP_TAC HPROVES_ASSUME THEN
  ASM_SIMP_TAC[HCORE_THEORY_OK; HTRTM_BOOL_OK];
    REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`asl1:term list`; `p === q`] MODEL_PROVES_BOOL) THEN
  ASM_REWRITE_TAC[EQUATION_HAS_TYPE_BOOL] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[HTRTM_TERM_UNION] THEN MATCH_MP_TAC HPROVES_EQ_MP THEN
  MAP_EVERY EXISTS_TAC [`htrtm p`; `htrtm p'`] THEN
  ASM_SIMP_TAC[GSYM HTRTM_EQUATION; GSYM HTRTM_ACONV];
    REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`asl1:term list`; `c1:term`] MODEL_PROVES_BOOL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `welltyped c1` ASSUME_TAC THENL
   [ASM_MESON_TAC[welltyped]; ALL_TAC] THEN
  ASM_SIMP_TAC[HTRTM_TERM_UNION; HTRTM_FILTER; HTRTM_EQUATION] THEN
  MATCH_MP_TAC HPROVES_DEDUCT_ANTISYM THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MAP (INST tyin) asl |- INST tyin p` ASSUME_TAC THENL
   [MATCH_MP_TAC(el 8 (CONJUNCTS prove_RULES)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`asl:term list`; `p:term`] MODEL_PROVES_BOOL) THEN
  MP_TAC(SPECL [`MAP (INST tyin) asl`; `INST tyin p`] MODEL_PROVES_BOOL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`hthyof hcore_ctxt`; `htrtyin tyin`; `MAP htrtm asl`;
                `htrtm p`] HPROVES_INST_TYPE) THEN
  ASM_REWRITE_TAC[HTRTYIN_OK] THEN DISCH_TAC THEN
  MATCH_MP_TAC HPROVES_ACONV THEN
  MAP_EVERY EXISTS_TAC [`MAP (HINST (htrtyin tyin)) (MAP htrtm asl)`;
                        `HINST (htrtyin tyin) (htrtm p)`] THEN
  ASM_SIMP_TAC[ALL_HTRTM_BOOL_OK] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MEM_MAP] THEN X_GEN_TAC `y:holterm` THEN STRIP_TAC THEN
      EXISTS_TAC `htrtm (INST tyin x)` THEN CONJ_TAC THENL
   [EXISTS_TAC `INST tyin x` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `x:term` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HACONV_SYM THEN MATCH_MP_TAC HTRTM_INST THEN
  UNDISCH_TAC `ALL (\a. a has_type Bool) asl` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[welltyped];
      MATCH_MP_TAC HACONV_SYM THEN MATCH_MP_TAC HTRTM_INST THEN
  ASM_MESON_TAC[welltyped];
      REWRITE_TAC[HTRTM_WELLTYPED] THEN ASM_MESON_TAC[welltyped]];
    REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MAP (VSUBST ilist) asl |- VSUBST ilist p` ASSUME_TAC THENL
   [MATCH_MP_TAC(el 9 (CONJUNCTS prove_RULES)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`asl:term list`; `p:term`] MODEL_PROVES_BOOL) THEN
  MP_TAC(SPECL [`MAP (VSUBST ilist) asl`; `VSUBST ilist p`] MODEL_PROVES_BOOL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HTRILIST_COND) THEN
  MP_TAC(SPECL [`hthyof hcore_ctxt`; `htrilist ilist`; `MAP htrtm asl`;
                `htrtm p`] HPROVES_INST) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:holterm`; `s':holterm`] o
      check (fun th -> can (find_term (fun t -> t = `hhas_type`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:string`; `ty:holtype`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `MEM (s':holterm,s) (htrilist ilist)` THEN
    REWRITE_TAC[htrilist; MEM_MAP; EXISTS_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[HCORE_FST] THEN
    MATCH_MP_TAC HTRTM_TERM_OK THEN ASM_MESON_TAC[welltyped];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HPROVES_ACONV THEN
  MAP_EVERY EXISTS_TAC [`MAP (HVSUBST (htrilist ilist)) (MAP htrtm asl)`;
                        `HVSUBST (htrilist ilist) (htrtm p)`] THEN
  ASM_SIMP_TAC[ALL_HTRTM_BOOL_OK] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MEM_MAP] THEN X_GEN_TAC `y:holterm` THEN STRIP_TAC THEN
    EXISTS_TAC `htrtm (VSUBST ilist x)` THEN CONJ_TAC THENL
     [EXISTS_TAC `VSUBST ilist x` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `x:term` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HACONV_SYM THEN MATCH_MP_TAC HTRTM_VSUBST THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\a. a has_type Bool) asl` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[welltyped];
    MATCH_MP_TAC HACONV_SYM THEN MATCH_MP_TAC HTRTM_VSUBST THEN
    ASM_MESON_TAC[welltyped];
    REWRITE_TAC[HTRTM_WELLTYPED] THEN ASM_MESON_TAC[welltyped]]]);;

(* ------------------------------------------------------------------------- *)
(* Back-translation of the port's types and terms into Model's. It is a    *)
(* total function that inverts htrty and htrtm on the well-formed types and*)
(* terms of the core context.                                              *)
(* ------------------------------------------------------------------------- *)

let hbtrty_app = new_definition
 `hbtrty_app s l = if s = "fun" then Fun (HD l) (HD (TL l))
                   else if s = "ind" then Ind else Bool`;;

let HBTRTY_DEF = new_recursive_definition holtype_RECURSION
 `(hbtrty (TyVar v) = Tyvar v) /\
  (hbtrty (TyApp s tys) = hbtrty_app s (hbtrty_list tys)) /\
  (hbtrty_list [] = []) /\
  (hbtrty_list (CONS ty tys) = CONS (hbtrty ty) (hbtrty_list tys))`;;

let HBTRTY_LIST = prove
 (`!tys. hbtrty_list tys = MAP hbtrty tys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[HBTRTY_DEF; MAP]);;

let HBTRTY = prove
 (`(!v. hbtrty (TyVar v) = Tyvar v) /\
   (!s tys. hbtrty (TyApp s tys) = hbtrty_app s (MAP hbtrty tys))`,
  REWRITE_TAC[HBTRTY_DEF; HBTRTY_LIST]);;

let hbtrtm = new_recursive_definition holterm_RECURSION
 `(hbtrtm (TmVar x ty) = Var x (hbtrty ty)) /\
  (hbtrtm (TmConst c ty) = if c = "=" then Equal (hbtrty (hdomain ty))
                           else Select (hbtrty (hcodomain ty))) /\
  (hbtrtm (TmComb s t) = Comb (hbtrtm s) (hbtrtm t)) /\
  (hbtrtm (TmAbs v t) =
     Abs (FST(hdest_var v)) (hbtrty (SND(hdest_var v))) (hbtrtm t))`;;

let HBTRTY_HTRTY = prove
 (`!ty. hbtrty (htrty ty) = ty`,
  MATCH_MP_TAC type_INDUCT THEN
  REWRITE_TAC[htrty; HBTRTY; HFun; HBool; MAP; hbtrty_app; HD; TL] THEN
  CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[] THEN
  SIMP_TAC[]);;

let HBTRTM_HTRTM = prove
 (`!t. hbtrtm (htrtm t) = t`,
  MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[htrtm; hbtrtm; htrty; HDOMAIN_HFUN; HCODOMAIN_HFUN;
              HBTRTY_HTRTY; hdest_var; FST; SND] THEN
  CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC[HDOMAIN_HFUN; HCODOMAIN_HFUN; HBTRTY_HTRTY] THEN
  SIMP_TAC[]);;

let HCORE_TYPE_LIST = prove
 (`htype_list hcore_ctxt = ["ind",0; "bool",0; "fun",2]`,
  REWRITE_TAC[hcore_ctxt; hinit_ctxt; htype_list; MAP; hflat; htypes_of_upd;
              APPEND]);;

let HCORE_CONST_LIST = prove
 (`hconst_list hcore_ctxt =
     ["@",HFun (HFun (TyVar "A") HBool) (TyVar "A");
      "=",HFun (TyVar "A") (HFun (TyVar "A") HBool)]`,
  REWRITE_TAC[hcore_ctxt; hinit_ctxt; hconst_list; MAP; hflat; hconsts_of_upd;
              APPEND]);;

let HLENGTH_EQ_0 = prove
 (`!l:A list. 0 = LENGTH l <=> l = []`,
  MESON_TAC[LENGTH_EQ_NIL]);;

let HLENGTH_EQ_2 = prove
 (`!l:A list. 2 = LENGTH l <=> ?a b. l = [a;b]`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH; NOT_CONS_NIL] THEN
  SPEC_TAC(`t:A list`,`m:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH; CONS_11; NOT_CONS_NIL] THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC(SUC n) <=> n = 0`; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let HTRTY_HBTRTY = prove
 (`!ty. htype_ok (htype_list hcore_ctxt) ty ==> htrty (hbtrty ty) = ty`,
  MATCH_MP_TAC HOLTYPE_INDUCT THEN
  REWRITE_TAC[HBTRTY; htrty; HTYPE_OK; HCORE_TYPE_LIST; hlookup] THEN
  X_GEN_TAC `s:string` THEN X_GEN_TAC `tys:holtype list` THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `s = "ind"` THENL
   [ASM_REWRITE_TAC[option_INJ; HLENGTH_EQ_0] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MAP; hbtrty_app; htrty] THEN
    CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[htrty];
    ALL_TAC] THEN
  ASM_CASES_TAC `s = "bool"` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN
    REWRITE_TAC[option_INJ; HLENGTH_EQ_0] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MAP; hbtrty_app; htrty; HBool] THEN
    CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[htrty; HBool];
    ALL_TAC] THEN
  ASM_CASES_TAC `s = "fun"` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN
    REWRITE_TAC[option_INJ; HLENGTH_EQ_2] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:holtype`
      (X_CHOOSE_THEN `b:holtype` ASSUME_TAC)) ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `tys:holtype list`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
    ASM_REWRITE_TAC[MAP; hbtrty_app; HD; TL; htrty; HFun] THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~("ind" = s) /\ ~("bool" = s) /\ ~("fun" = s)`
      (fun th -> REWRITE_TAC[th; option_DISTINCT]) THEN
    ASM_MESON_TAC[]]);;

let HTRTM_HBTRTM = prove
 (`!t. hterm_ok (hsigof hcore_ctxt) t ==> htrtm (hbtrtm t) = t`,
  MATCH_MP_TAC holterm_INDUCT THEN
  REWRITE_TAC[hterm_ok; hbtrtm; htrtm; hsigof; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[HTRTY_HBTRTY];
    MAP_EVERY X_GEN_TAC [`c:string`; `ty:holtype`] THEN
    REWRITE_TAC[HCORE_CONST_LIST; hlookup] THEN
    ASM_CASES_TAC `c = "="` THEN ASM_REWRITE_TAC[] THENL
     [CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN
      REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `i:(holtype#holtype)list` SUBST_ALL_TAC)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[HTYPE_SUBST_HFUN; HTYPE_SUBST_HBOOL]) THEN
      REWRITE_TAC[HTYPE_SUBST_HFUN; HTYPE_SUBST_HBOOL; HDOMAIN_HFUN; htrtm;
                  htrty];
      ASM_CASES_TAC `c = "@"` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
        REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `i:(holtype#holtype)list` SUBST_ALL_TAC)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[HTYPE_SUBST_HFUN; HTYPE_SUBST_HBOOL]) THEN
        REWRITE_TAC[HTYPE_SUBST_HFUN; HTYPE_SUBST_HBOOL; HCODOMAIN_HFUN; htrtm;
                    htrty];
        SUBGOAL_THEN `~("@" = c)` (fun th -> REWRITE_TAC[th; option_DISTINCT]) THEN
        ASM_MESON_TAC[]]] THEN
    SUBGOAL_THEN `htrty (hbtrty (HTYPE_SUBST i (TyVar "A"))) =
                  HTYPE_SUBST i (TyVar "A")`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC HTRTY_HBTRTY THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `htype_ok`)) (concl th))) THEN
    REWRITE_TAC[HFun; HTYPE_OK; ALL] THEN SIMP_TAC[];
    SIMP_TAC[];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[hdest_var; FST; SND; holterm_INJ] THEN
    ASM_SIMP_TAC[HTRTY_HBTRTY]]);;

(* ------------------------------------------------------------------------- *)
(* Model's deductive system is closed under alpha-equivalence and           *)
(* weakening (the same construction as for the port).                       *)
(* ------------------------------------------------------------------------- *)

let MPROVES_REFL = el 0 (CONJUNCTS prove_RULES);;
let MPROVES_TRANS = el 1 (CONJUNCTS prove_RULES);;
let MPROVES_MK_COMB = el 2 (CONJUNCTS prove_RULES);;
let MPROVES_ABS = el 3 (CONJUNCTS prove_RULES);;
let MPROVES_BETA = el 4 (CONJUNCTS prove_RULES);;
let MPROVES_ASSUME = el 5 (CONJUNCTS prove_RULES);;
let MPROVES_EQ_MP = el 6 (CONJUNCTS prove_RULES);;
let MPROVES_DEDUCT_ANTISYM = el 7 (CONJUNCTS prove_RULES);;
let MPROVES_INST_TYPE = el 8 (CONJUNCTS prove_RULES);;
let MPROVES_INST = el 9 (CONJUNCTS prove_RULES);;

let MACONV_SYM = prove
 (`!s t. ACONV s t ==> ACONV t s`,
  MESON_TAC[HTRTM_ACONV; HACONV_SYM]);;

let MACONV_TRANS = prove
 (`!s t u. ACONV s t /\ ACONV t u ==> ACONV s u`,
  MESON_TAC[HTRTM_ACONV; HACONV_TRANS]);;

let MACONV_VAR = prove
 (`!t x ty. ACONV t (Var x ty) <=> t = Var x ty`,
  REWRITE_TAC[HTRTM_ACONV; htrtm; HACONV_VAR; HTRTM_EQ_VAR]);;

let MTERM_UNION_SUBSUMED = prove
 (`!l1 l2. (!x. MEM x l1 ==> ?y. MEM y l2 /\ ACONV x y)
           ==> TERM_UNION l1 l2 = l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[TERM_UNION; MEM] THEN
  REPEAT STRIP_TAC THEN LET_TAC THEN
  SUBGOAL_THEN `subun:term list = l2` SUBST1_TAC THENL
   [EXPAND_TAC "subun" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM EX_MEM] THEN ASM_MESON_TAC[]);;

let MREV_ASSOCD_NOT_MEM = prove
 (`!l:(B#A)list a d. ~(?x. MEM (x,a) l) ==> REV_ASSOCD a l d = d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[REV_ASSOCD] THEN
  SPEC_TAC(`h:B#A`,`p:B#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[REV_ASSOCD; MEM; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let MVSUBST_TRIVIAL = prove
 (`!tm ilist. (!s' s. MEM (s',s) ilist ==> ~VFREE_IN s tm)
              ==> VSUBST ilist tm = tm`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[VSUBST; VFREE_IN] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MREV_ASSOCD_NOT_MEM THEN
    DISCH_THEN(X_CHOOSE_TAC `y:term`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:term`; `Var x ty`]) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[term_INJ] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:string`; `ty:type`; `t:term`] THEN DISCH_TAC THEN
    X_GEN_TAC `ilist:(term#term)list` THEN DISCH_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN
     `!s' s. MEM (s',s) (FILTER (\(s',s). ~(s = Var x ty))
                                (ilist:(term#term)list))
             ==> ~VFREE_IN s t`
    ASSUME_TAC THENL
     [REWRITE_TAC[MEM_FILTER] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~EX (\(s',s). VFREE_IN (Var x ty) s' /\ VFREE_IN s t)
                      (FILTER (\(s',s). ~(s = Var x ty))
                              (ilist:(term#term)list))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[NOT_EX; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let MVFREE_IN_ITLIST_COMB = prove
 (`!l b v. VFREE_IN v (ITLIST Comb l b) <=> VFREE_IN v b \/ EX (VFREE_IN v) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; EX; VFREE_IN] THEN
  MESON_TAC[]);;

let MPROVES_ADD_FRONT = prove
 (`!rest r q. rest |- r /\ q has_type Bool ==> ?r'. CONS q rest |- r'`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `z = VARIANT (Comb (Comb q r) (ITLIST Comb rest q)) "x" Bool` THEN
  MP_TAC(ISPECL [`Comb (Comb q r) (ITLIST Comb rest q)`; `"x"`; `Bool`]
                VARIANT) THEN
  ASM_REWRITE_TAC[VFREE_IN; MVFREE_IN_ITLIST_COMB; DE_MORGAN_THM] THEN
  REWRITE_TAC[NOT_EX; GSYM ALL_MEM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `[Var z Bool] |- Var z Bool` ASSUME_TAC THENL
   [MATCH_MP_TAC MPROVES_ASSUME THEN REWRITE_TAC[has_type_RULES]; ALL_TAC] THEN
  MP_TAC(SPECL [`[Var z Bool]`; `rest:term list`; `Var z Bool`; `r:term`]
               MPROVES_DEDUCT_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `TERM_UNION (FILTER ((~) o ACONV r) [Var z Bool])
               (FILTER ((~) o ACONV (Var z Bool)) rest) =
    CONS (Var z Bool) rest`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!y. MEM y rest ==> ~ACONV (Var z Bool) y` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP MACONV_SYM) THEN
      REWRITE_TAC[MACONV_VAR] THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[VFREE_IN];
      ALL_TAC] THEN
    SUBGOAL_THEN `FILTER ((~) o ACONV (Var z Bool)) rest = rest`
    SUBST1_TAC THENL
     [UNDISCH_TAC `!y. MEM y rest ==> ~ACONV (Var z Bool) y` THEN
      SPEC_TAC(`rest:term list`,`l:term list`) THEN
      LIST_INDUCT_TAC THEN ASM_SIMP_TAC[FILTER; MEM; o_THM];
      ALL_TAC] THEN
    REWRITE_TAC[FILTER; o_THM] THEN
    SUBGOAL_THEN `~ACONV r (Var z Bool)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[MACONV_VAR] THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[VFREE_IN];
      ALL_TAC] THEN
    REWRITE_TAC[TERM_UNION; LET_DEF; LET_END_DEF; GSYM EX_MEM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`[q:term,Var z Bool]`; `CONS (Var z Bool) rest`;
                `Var z Bool === r`] MPROVES_INST) THEN
  ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MAP; VSUBST; REV_ASSOCD] THEN
  SUBGOAL_THEN `MAP (VSUBST [q:term,Var z Bool]) rest = rest` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `MAP (\x:term. x) rest` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[MAP_ID]] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MVSUBST_TRIVIAL THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
    ASM_MESON_TAC[];
    MESON_TAC[]]);;

let MPROVES_EXISTS_HYPS = prove
 (`!h. ALL (\p. p has_type Bool) h ==> ?r. h |- r`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THENL
   [EXISTS_TAC `Var "x" Bool === Var "x" Bool` THEN
    MATCH_MP_TAC MPROVES_REFL THEN REWRITE_TAC[WELLTYPED_CLAUSES];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `r:term`) THEN
    MATCH_MP_TAC MPROVES_ADD_FRONT THEN EXISTS_TAC `r:term` THEN
    ASM_REWRITE_TAC[]]);;

let MPROVES_ACONV = prove
 (`!asl p asl' p'.
        asl |- p /\ (!x. MEM x asl ==> ?y. MEM y asl' /\ ACONV x y) /\
        ALL (\a. a has_type Bool) asl' /\ ACONV p p' /\ welltyped p'
        ==> asl' |- p'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `asl':term list` MPROVES_EXISTS_HYPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `r:term`) THEN
  MP_TAC(SPECL [`asl':term list`; `asl:term list`; `r:term`; `p:term`]
               MPROVES_DEDUCT_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`TERM_UNION (FILTER ((~) o ACONV p) asl')
                            (FILTER ((~) o ACONV r) asl)`;
                `asl':term list`; `r:term`; `p:term`; `r:term`]
               MPROVES_EQ_MP) THEN
  ASM_REWRITE_TAC[ACONV_REFL] THEN
  SUBGOAL_THEN
   `TERM_UNION (TERM_UNION (FILTER ((~) o ACONV p) asl')
                           (FILTER ((~) o ACONV r) asl)) asl' = asl'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MTERM_UNION_SUBSUMED THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP TERM_UNION_NONEW) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MEM_FILTER]) THEN ASM_MESON_TAC[ACONV_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`[]:term list`; `asl':term list`; `p':term`; `p':term`;
                `p:term`] MPROVES_EQ_MP) THEN
  ASM_REWRITE_TAC[TERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MPROVES_REFL THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MACONV_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Well-formed terms of the core context are translations of Model terms;  *)
(* substitution and type instantiation agree up to alpha-equivalence.      *)
(* ------------------------------------------------------------------------- *)

let HTRTM_HAS_TYPE_EQ = prove
 (`!tm ty. htrtm tm hhas_type htrty ty <=> tm has_type ty`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[HTRTM_HAS_TYPE] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `welltyped tm` ASSUME_TAC THENL
   [ASM_MESON_TAC[HTRTM_WELLTYPED; hwelltyped]; ALL_TAC] THEN
  SUBGOAL_THEN `typeof tm = ty` (fun th -> ASM_MESON_TAC[th; WELLTYPED]) THEN
  REWRITE_TAC[GSYM HTRTY_INJ] THEN
  ASM_MESON_TAC[HTRTM_HAS_TYPE; WELLTYPED; HHAS_TYPE_FUNCTIONAL]);;

let HBTRTM_HTRTM_LIST = prove
 (`!l. MAP hbtrtm (MAP htrtm l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; HBTRTM_HTRTM]);;

let HCORE_TYPE_IMAGE = prove
 (`!ty. htype_ok (FST (FST (hthyof hcore_ctxt))) ty ==> ?ty0. ty = htrty ty0`,
  REWRITE_TAC[HCORE_FST] THEN MESON_TAC[HTRTY_HBTRTY]);;

let HCORE_TERM_IMAGE = prove
 (`!t. hterm_ok (FST (hthyof hcore_ctxt)) t
       ==> ?t0. welltyped t0 /\ t = htrtm t0`,
  REWRITE_TAC[HCORE_FST] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `hbtrtm t` THEN ASM_SIMP_TAC[HTRTM_HBTRTM] THEN
  ASM_MESON_TAC[HTRTM_WELLTYPED; HTRTM_HBTRTM; HTERM_OK_WELLTYPED]);;

let HCORE_BOOL_IMAGE = prove
 (`!t. hterm_ok (FST (hthyof hcore_ctxt)) t /\ t hhas_type HBool
       ==> ?t0. t0 has_type Bool /\ t = htrtm t0`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t0:term` STRIP_ASSUME_TAC o
                MATCH_MP HCORE_TERM_IMAGE) THEN
  EXISTS_TAC `t0:term` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM HTRTM_HAS_TYPE_EQ] THEN
  REWRITE_TAC[htrty] THEN ASM_MESON_TAC[]);;

let HCORE_LIST_IMAGE = prove
 (`!l. ALL (\p. hterm_ok (FST (hthyof hcore_ctxt)) p /\ p hhas_type HBool) l
       ==> ?l0. ALL (\a. a has_type Bool) l0 /\ l = MAP htrtm l0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THENL
   [EXISTS_TAC `[]:term list` THEN REWRITE_TAC[ALL; MAP]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:term list` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `h:holterm` HCORE_BOOL_IMAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:term` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (a0:term) l0` THEN ASM_REWRITE_TAC[ALL; MAP]);;

let HCORE_SEQUENT_IMAGE = prove
 (`!h c. hproves (hthyof hcore_ctxt) h c
         ==> ?h0 c0. ALL (\a. a has_type Bool) h0 /\ c0 has_type Bool /\
                     h = MAP htrtm h0 /\ c = htrtm c0`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP HPROVES_TERM_OK) THEN
  MP_TAC(SPEC `h:holterm list` HCORE_LIST_IMAGE) THEN
  MP_TAC(SPEC `c:holterm` HCORE_BOOL_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let HTRTM_EX_VFREE_IN = prove
 (`!x ty l. EX (HVFREE_IN (TmVar x (htrty ty))) (MAP htrtm l) <=>
            EX (VFREE_IN (Var x ty)) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[EX; MAP; HTRTM_VFREE_IN; htrtm]);;

let HTRTM_COMB = el 3 (CONJUNCTS htrtm);;
let HTRTM_ABS = el 4 (CONJUNCTS htrtm);;
let HTRTM_VAR = el 0 (CONJUNCTS htrtm);;

let HTRTY_HBTRTY_TYVAR = prove
 (`!b v. htrty (hbtrty b) = TyVar v <=> b = TyVar v`,
  MATCH_MP_TAC HOLTYPE_INDUCT THEN
  REWRITE_TAC[HBTRTY; htrty; holtype_DISTINCT; hbtrty_app] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[htrty; HFun; HBool; holtype_DISTINCT]);;

let HTYPE_SUBST_HTRTYIN = prove
 (`!tyin. ALL (htype_ok (htype_list hcore_ctxt)) (MAP FST tyin)
          ==> !ty. HTYPE_SUBST (htrtyin (MAP (\(a,b). (hbtrty a,hbtrty b)) tyin))
                               ty =
                   HTYPE_SUBST tyin ty`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HOLTYPE_INDUCT THEN
  REWRITE_TAC[HTYPE_SUBST] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:string` THEN
    UNDISCH_TAC `ALL (htype_ok (htype_list hcore_ctxt))
                     (MAP FST (tyin:(holtype#holtype)list))` THEN
    SPEC_TAC(`tyin:(holtype#holtype)list`,`l:(holtype#holtype)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[htrtyin; MAP; HREV_ASSOCD; ALL] THEN
    SPEC_TAC(`h:holtype#holtype`,`p:holtype#holtype`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
    MAP_EVERY X_GEN_TAC [`a:holtype`; `b:holtype`] THEN STRIP_TAC THEN
    REWRITE_TAC[HREV_ASSOCD; HTRTY_HBTRTY_TYVAR] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[HTRTY_HBTRTY] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[htrtyin];
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
    ASM_REWRITE_TAC[]]);;

let HDBINST_CONG = prove
 (`!i i' t. (!ty. HTYPE_SUBST i ty = HTYPE_SUBST i' ty)
            ==> hdbINST i t = hdbINST i' t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`t:hdbterm`,`t:hdbterm`) THEN
  MATCH_MP_TAC hdbterm_INDUCT THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[hdbINST]);;

let HINST_ACONV_CONG = prove
 (`!i i' t. hwelltyped t /\ (!ty. HTYPE_SUBST i ty = HTYPE_SUBST i' ty)
            ==> HACONV (HINST i t) (HINST i' t)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[HACONV_DB; HINST_WELLTYPED; HINST_DBINST] THEN
  MATCH_MP_TAC HDBINST_CONG THEN ASM_REWRITE_TAC[]);;

let HCORE_REFLECT_ACONV = prove
 (`!asl p h c.
        asl |- p /\ hproves (hthyof hcore_ctxt) h c /\
        (!a. MEM a asl ==> ?b. MEM b h /\ HACONV (htrtm a) b) /\
        HACONV (htrtm p) c
        ==> MAP hbtrtm h |- hbtrtm c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:holterm list`; `c:holterm`] HCORE_SEQUENT_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:term list` (X_CHOOSE_THEN `c0:term`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN SUBST_ALL_TAC))))) THEN
  REWRITE_TAC[HBTRTM_HTRTM; HBTRTM_HTRTM_LIST] THEN
  MATCH_MP_TAC MPROVES_ACONV THEN
  MAP_EVERY EXISTS_TAC [`asl:term list`; `p:term`] THEN
  ASM_REWRITE_TAC[HTRTM_ACONV] THEN CONJ_TAC THENL
   [X_GEN_TAC `a:term` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:term`) THEN ASM_REWRITE_TAC[MEM_MAP] THEN
    MESON_TAC[];
    ASM_MESON_TAC[welltyped]]);;

let HBTRTM_EQ_IMAGE = prove
 (`!s t. welltyped s ==> hbtrtm (htrtm s =:= htrtm t) = s === t`,
  SIMP_TAC[GSYM HTRTM_EQUATION; HBTRTM_HTRTM]);;

let HCORE_OK_EQUATION =
  MATCH_MP HTERM_OK_EQUATION (MATCH_MP HTHEORY_OK_STD_SIG HCORE_THEORY_OK);;

let HTRILIST_IMAGE = prove
 (`!ilist. (!s s'. MEM (s',s) ilist
                   ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty /\
                              hterm_ok (FST (hthyof hcore_ctxt)) s')
           ==> htrilist (MAP (\(a,b). (hbtrtm a,hbtrtm b)) ilist) = ilist /\
               (!s s'. MEM (s',s) (MAP (\(a,b). (hbtrtm a,hbtrtm b)) ilist)
                       ==> ?x ty. s = Var x ty /\ s' has_type ty)`,
  REWRITE_TAC[htrilist] THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN
  SPEC_TAC(`h:holterm#holterm`,`p:holterm#holterm`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:holterm`; `b:holterm`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:holterm`; `a:holterm`]) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:string` (X_CHOOSE_THEN `ty:holtype`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `a0:term` STRIP_ASSUME_TAC o
              MATCH_MP HCORE_TERM_IMAGE) THEN
  SUBGOAL_THEN `htype_ok (htype_list hcore_ctxt) ty` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`FST (hthyof hcore_ctxt)`; `a:holterm`] HTERM_OK_TYPE_OK) THEN
    ASM_REWRITE_TAC[MATCH_MP HTHEORY_OK_STD_SIG HCORE_THEORY_OK; HCORE_FST] THEN
    ASM_MESON_TAC[HWELLTYPED_LEMMA];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_SIMP_TAC[HBTRTM_HTRTM; hbtrtm; htrtm; HTRTY_HBTRTY; PAIR_EQ] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  EXISTS_TAC `x:string` THEN EXISTS_TAC `hbtrty ty` THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM HTRTM_HAS_TYPE_EQ] THEN
  ASM_SIMP_TAC[HTRTY_HBTRTY] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The converse: provability in the port's core context reflects into      *)
(* Model, so the port's core provability is exactly the image of Model's,  *)
(* and Model's soundness theorem transfers.                                *)
(* ------------------------------------------------------------------------- *)

let hproves_SINDUCT = derive_strong_induction(hproves_RULES,hproves_INDUCT);;

let HPROVES_OK_TAC (asl,w as g) =
  let ths = filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                  "hproves"
                              with Failure _ -> false) (map snd asl) in
  MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP HPROVES_TERM_OK th)) ths g;;

let hok_tm = `hterm_ok (FST (hthyof hcore_ctxt))`;;

let TERM_IMAGE_TAC v v0 =
  MP_TAC(MATCH_MP HCORE_TERM_IMAGE (ASSUME (mk_comb(hok_tm,v)))) THEN
  DISCH_THEN(X_CHOOSE_THEN v0 (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC));;

let BOOL_IMAGE_TAC v v0 =
  MP_TAC(MATCH_MP HCORE_BOOL_IMAGE
    (CONJ (ASSUME (mk_comb(hok_tm,v)))
          (ASSUME (mk_comb(mk_comb(`(hhas_type)`,v),`HBool`))))) THEN
  DISCH_THEN(X_CHOOSE_THEN v0 (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC));;

let LIST_IMAGE_TAC v v0 =
  MP_TAC(MATCH_MP HCORE_LIST_IMAGE (ASSUME (mk_comb(
    `ALL (\p. hterm_ok (FST (hthyof hcore_ctxt)) p /\ p hhas_type HBool)`,v)))) THEN
  DISCH_THEN(X_CHOOSE_THEN v0 (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC));;

let TYPE_IMAGE_TAC v v0 =
  MP_TAC(MATCH_MP HCORE_TYPE_IMAGE (ASSUME (mk_comb(
    `htype_ok (FST (FST (hthyof hcore_ctxt)))`,v)))) THEN
  DISCH_THEN(X_CHOOSE_THEN v0 SUBST_ALL_TAC);;

let MPROVES_TO_GOAL_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "|-"
    with Failure _ -> false)));;

let SPLIT_CONJ_ASSUM_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then CONJUNCTS_THEN ASSUME_TAC th
    else failwith "SPLIT_CONJ_ASSUM_TAC"));;
let HOL_REFLECTS = prove
 (`!h c. hproves (hthyof hcore_ctxt) h c ==> MAP hbtrtm h |- hbtrtm c`,
  SUBGOAL_THEN
   `!thy h c. hproves thy h c
              ==> thy = hthyof hcore_ctxt ==> MAP hbtrtm h |- hbtrtm c`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC hproves_SINDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN HPROVES_OK_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HCORE_OK_EQUATION]) THENL
   [SPLIT_CONJ_ASSUM_TAC THEN
    TYPE_IMAGE_TAC `ty:holtype` `ty0:type` THEN
    TERM_IMAGE_TAC `l:holterm` `l0:term` THEN
    TERM_IMAGE_TAC `r:holterm` `r0:term` THEN
    LIST_IMAGE_TAC `h:holterm list` `h0:term list` THEN
    MPROVES_TO_GOAL_TAC THEN
    ASM_SIMP_TAC[HBTRTM_EQ_IMAGE; HBTRTM_HTRTM_LIST; GSYM HTRTM_ABS;
                 WELLTYPED_CLAUSES] THEN
    DISCH_TAC THEN MATCH_MP_TAC MPROVES_ABS THEN
    ASM_REWRITE_TAC[GSYM HTRTM_EX_VFREE_IN];
    BOOL_IMAGE_TAC `p:holterm` `p0:term` THEN
    REWRITE_TAC[MAP; HBTRTM_HTRTM] THEN MATCH_MP_TAC MPROVES_ASSUME THEN
    ASM_REWRITE_TAC[];
    TYPE_IMAGE_TAC `ty:holtype` `ty0:type` THEN
    TERM_IMAGE_TAC `t:holterm` `t0:term` THEN
    REWRITE_TAC[GSYM HTRTM_ABS] THEN REWRITE_TAC[GSYM HTRTM_VAR] THEN
    REWRITE_TAC[GSYM HTRTM_COMB] THEN
    SUBGOAL_THEN `welltyped (Comb (Abs x ty0 t0) (Var x ty0))` ASSUME_TAC THENL
     [REWRITE_TAC[WELLTYPED_CLAUSES; typeof; type_INJ] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[HBTRTM_EQ_IMAGE; MAP] THEN MATCH_MP_TAC MPROVES_BETA THEN
    ASM_REWRITE_TAC[];
    BOOL_IMAGE_TAC `c1:holterm` `c10:term` THEN
    BOOL_IMAGE_TAC `c2:holterm` `c20:term` THEN
    LIST_IMAGE_TAC `h1:holterm list` `h10:term list` THEN
    LIST_IMAGE_TAC `h2:holterm list` `h20:term list` THEN
    MPROVES_TO_GOAL_TAC THEN
    SUBGOAL_THEN `welltyped c10` ASSUME_TAC THENL
     [ASM_MESON_TAC[welltyped]; ALL_TAC] THEN
    ASM_SIMP_TAC[HBTRTM_EQ_IMAGE; HBTRTM_HTRTM; HBTRTM_HTRTM_LIST;
                 GSYM HTRTM_FILTER; GSYM HTRTM_TERM_UNION] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MPROVES_DEDUCT_ANTISYM THEN
    ASM_REWRITE_TAC[];
    SPLIT_CONJ_ASSUM_TAC THEN
    TERM_IMAGE_TAC `p:holterm` `p0:term` THEN
    TERM_IMAGE_TAC `q:holterm` `q0:term` THEN
    BOOL_IMAGE_TAC `p':holterm` `p0':term` THEN
    LIST_IMAGE_TAC `h1:holterm list` `h10:term list` THEN
    LIST_IMAGE_TAC `h2:holterm list` `h20:term list` THEN
    MPROVES_TO_GOAL_TAC THEN
    ASM_SIMP_TAC[HBTRTM_EQ_IMAGE; HBTRTM_HTRTM; HBTRTM_HTRTM_LIST;
                 GSYM HTRTM_TERM_UNION] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MPROVES_EQ_MP THEN
    MAP_EVERY EXISTS_TAC [`p0:term`; `p0':term`] THEN
    ASM_REWRITE_TAC[HTRTM_ACONV];
    MATCH_MP_TAC HCORE_REFLECT_ACONV THEN
    MAP_EVERY EXISTS_TAC
     [`MAP (VSUBST (MAP (\(a,b). (hbtrtm a,hbtrtm b)) ilist)) (MAP hbtrtm h)`;
      `VSUBST (MAP (\(a,b). (hbtrtm a,hbtrtm b)) ilist) (hbtrtm c)`] THEN
    MP_TAC(SPEC `ilist:(holterm#holterm)list` HTRILIST_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `ilist0 = MAP (\(a,b). (hbtrtm a,hbtrtm b))
                             (ilist:(holterm#holterm)list)` THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MPROVES_INST THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC HPROVES_INST THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      BOOL_IMAGE_TAC `c:holterm` `c0:term` THEN
      LIST_IMAGE_TAC `h:holterm list` `h0:term list` THEN
      REWRITE_TAC[HBTRTM_HTRTM_LIST] THEN REWRITE_TAC[MEM_MAP] THEN
      X_GEN_TAC `a:term` THEN
      DISCH_THEN(X_CHOOSE_THEN `y:term`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      EXISTS_TAC `HVSUBST ilist (htrtm y)` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `htrtm y` THEN REWRITE_TAC[] THEN EXISTS_TAC `y:term` THEN
        REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `htrilist ilist0 = ilist`)) THEN
      MATCH_MP_TAC HTRTM_VSUBST THEN CONJ_TAC THENL
       [ASM_MESON_TAC[ALL_MEM; welltyped]; FIRST_ASSUM ACCEPT_TAC];
      BOOL_IMAGE_TAC `c:holterm` `c0:term` THEN
      REWRITE_TAC[HBTRTM_HTRTM] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `htrilist ilist0 = ilist`)) THEN
      MATCH_MP_TAC HTRTM_VSUBST THEN CONJ_TAC THENL
       [ASM_MESON_TAC[welltyped]; FIRST_ASSUM ACCEPT_TAC]];
    MATCH_MP_TAC HCORE_REFLECT_ACONV THEN
    MAP_EVERY EXISTS_TAC
     [`MAP (INST (MAP (\(a,b). (hbtrty a,hbtrty b)) tyin)) (MAP hbtrtm h)`;
      `INST (MAP (\(a,b). (hbtrty a,hbtrty b)) tyin) (hbtrtm c)`] THEN
    MP_TAC(SPEC `tyin:(holtype#holtype)list` HTYPE_SUBST_HTRTYIN) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[HCORE_FST]; ALL_TAC] THEN
    ABBREV_TAC `tyin0 = MAP (\(a,b). (hbtrty a,hbtrty b))
                            (tyin:(holtype#holtype)list)` THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MPROVES_INST_TYPE THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC HPROVES_INST_TYPE THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      BOOL_IMAGE_TAC `c:holterm` `c0:term` THEN
      LIST_IMAGE_TAC `h:holterm list` `h0:term list` THEN
      REWRITE_TAC[HBTRTM_HTRTM_LIST] THEN REWRITE_TAC[MEM_MAP] THEN
      X_GEN_TAC `a:term` THEN
      DISCH_THEN(X_CHOOSE_THEN `y:term`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      EXISTS_TAC `HINST tyin (htrtm y)` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `htrtm y` THEN REWRITE_TAC[] THEN EXISTS_TAC `y:term` THEN
        REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC HACONV_TRANS THEN
      EXISTS_TAC `HINST (htrtyin tyin0) (htrtm y)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC HTRTM_INST THEN ASM_MESON_TAC[ALL_MEM; welltyped];
        MATCH_MP_TAC HINST_ACONV_CONG THEN CONJ_TAC THENL
         [REWRITE_TAC[HTRTM_WELLTYPED] THEN ASM_MESON_TAC[ALL_MEM; welltyped];
          FIRST_ASSUM ACCEPT_TAC]];
      BOOL_IMAGE_TAC `c:holterm` `c0:term` THEN
      REWRITE_TAC[HBTRTM_HTRTM] THEN
      MATCH_MP_TAC HACONV_TRANS THEN
      EXISTS_TAC `HINST (htrtyin tyin0) (htrtm c0)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC HTRTM_INST THEN ASM_MESON_TAC[welltyped];
        MATCH_MP_TAC HINST_ACONV_CONG THEN CONJ_TAC THENL
         [REWRITE_TAC[HTRTM_WELLTYPED] THEN ASM_MESON_TAC[welltyped];
          FIRST_ASSUM ACCEPT_TAC]]];
    SPLIT_CONJ_ASSUM_TAC THEN
    TERM_IMAGE_TAC `l1:holterm` `l10:term` THEN
    TERM_IMAGE_TAC `r1:holterm` `r10:term` THEN
    TERM_IMAGE_TAC `l2:holterm` `l20:term` THEN
    TERM_IMAGE_TAC `r2:holterm` `r20:term` THEN
    LIST_IMAGE_TAC `h1:holterm list` `h10:term list` THEN
    LIST_IMAGE_TAC `h2:holterm list` `h20:term list` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM HTRTM_COMB; HTRTM_WELLTYPED]) THEN
    MPROVES_TO_GOAL_TAC THEN
    ASM_SIMP_TAC[HBTRTM_EQ_IMAGE; HBTRTM_HTRTM_LIST; GSYM HTRTM_TERM_UNION;
                 GSYM HTRTM_COMB] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MPROVES_MK_COMB THEN ASM_REWRITE_TAC[];
    TERM_IMAGE_TAC `t:holterm` `t0:term` THEN
    ASM_SIMP_TAC[HBTRTM_EQ_IMAGE; MAP] THEN MATCH_MP_TAC MPROVES_REFL THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(c:holterm) IN SND (hthyof hcore_ctxt)` THEN
    REWRITE_TAC[hcore_ctxt; hinit_ctxt] THEN CONV_TAC HCONTEXT_CONV])
;;

let HCORE_SOUND = prove
 (`!h c. hproves (hthyof hcore_ctxt) h c ==> MAP hbtrtm h |= hbtrtm c`,
  MESON_TAC[HOL_REFLECTS; HOL_IS_SOUND]);;

let HCORE_PROVES = prove
 (`!h c. hproves (hthyof hcore_ctxt) h c <=>
         ?asl p. asl |- p /\ h = MAP htrtm asl /\ c = htrtm p`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`MAP hbtrtm h`; `hbtrtm c`] THEN
    ASM_SIMP_TAC[HOL_REFLECTS] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HCORE_SEQUENT_IMAGE) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[HBTRTM_HTRTM; HBTRTM_HTRTM_LIST];
    STRIP_TAC THEN ASM_SIMP_TAC[HOL_EMBEDS]]);;

(* ------------------------------------------------------------------------- *)
(* A model-theoretic negative control: x = y for distinct boolean          *)
(* variables is not provable in the core context.                          *)
(* ------------------------------------------------------------------------- *)

let MODEL_DISTINCT_EQ_INVALID = prove
 (`~([] |= Var "x" Bool === Var "y" Bool)`,
  SIMP_TAC[EQUATION_HAS_TYPE_BOOL; WELLTYPED_CLAUSES; typeof;
           sequent; ALL; SEMANTICS_EQUATION; has_type_RULES; semantics;
           BOOLEAN_EQ_TRUE] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  EXISTS_TAC `(("x",Bool) |-> False) ((("y",Bool) |-> True)
                (\(x,ty). @a. a <: typeset (\x. boolset) ty))` THEN
  EXISTS_TAC `\x:string. boolset` THEN
  REWRITE_TAC[NOT_IMP; type_valuation; VALMOD; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN
  REWRITE_TAC[TRUE_NE_FALSE; GSYM TRUE_NE_FALSE] THEN
  CONJ_TAC THENL [MESON_TAC[IN_BOOL]; ALL_TAC] THEN
  REWRITE_TAC[term_valuation] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[VALMOD; PAIR_EQ] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[typeset; IN_BOOL]) THEN
  CONV_TAC SELECT_CONV THEN MATCH_MP_TAC TYPESET_INHABITED THEN
  REWRITE_TAC[type_valuation] THEN MESON_TAC[IN_BOOL]);;

let HCORE_DISTINCT_EQ_UNPROVABLE = prove
 (`~hproves (hthyof hcore_ctxt) [] (TmVar "x" HBool =:= TmVar "y" HBool)`,
  DISCH_THEN(MP_TAC o MATCH_MP HCORE_SOUND) THEN
  SUBGOAL_THEN `TmVar "x" HBool =:= TmVar "y" HBool =
                htrtm (Var "x" Bool === Var "y" Bool)`
  SUBST1_TAC THENL
   [SIMP_TAC[HTRTM_EQUATION; WELLTYPED_CLAUSES; htrtm; htrty]; ALL_TAC] THEN
  REWRITE_TAC[MAP; HBTRTM_HTRTM; MODEL_DISTINCT_EQ_INVALID]);;

let HCORE_CONSISTENT = prove
 (`?p. p hhas_type HBool /\ ~hproves (hthyof hcore_ctxt) [] p`,
  EXISTS_TAC `TmVar "x" HBool =:= TmVar "y" HBool` THEN
  REWRITE_TAC[HCORE_DISTINCT_EQ_UNPROVABLE; HEQUATION_HAS_TYPE_BOOL] THEN
  REWRITE_TAC[HWELLTYPED_CLAUSES; htypeof]);;

(* ------------------------------------------------------------------------- *)
(* The inference system with EQ_MP weakened by dropping its alpha-          *)
(* equivalence side condition proves x = y for distinct boolean variables   *)
(* in the core context, so that side condition is needed.                    *)
(* ------------------------------------------------------------------------- *)

let hproves_weak_RULES,hproves_weak_INDUCT,hproves_weak_CASES =
 new_inductive_definition
 `(!thy h x ty l r.
      ~(EX (HVFREE_IN (TmVar x ty)) h) /\ htype_ok (FST(FST thy)) ty /\
      hproves_weak thy h (l =:= r)
      ==> hproves_weak thy h (TmAbs (TmVar x ty) l =:= TmAbs (TmVar x ty) r)) /\
  (!thy p.
      htheory_ok thy /\ p hhas_type HBool /\ hterm_ok (FST thy) p
      ==> hproves_weak thy [p] p) /\
  (!thy x ty t.
      htheory_ok thy /\ htype_ok (FST(FST thy)) ty /\ hterm_ok (FST thy) t
      ==> hproves_weak thy []
            (TmComb (TmAbs (TmVar x ty) t) (TmVar x ty) =:= t)) /\
  (!thy h1 h2 c1 c2.
      hproves_weak thy h1 c1 /\ hproves_weak thy h2 c2
      ==> hproves_weak thy (HTERM_UNION (FILTER ((~) o HACONV c2) h1)
                                        (FILTER ((~) o HACONV c1) h2))
                           (c1 =:= c2)) /\
  (!thy h1 h2 p q p'.
      hproves_weak thy h1 (p =:= q) /\ hproves_weak thy h2 p'
      ==> hproves_weak thy (HTERM_UNION h1 h2) q) /\
  (!thy ilist h c.
      (!s s'. MEM (s',s) ilist
              ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty /\
                         hterm_ok (FST thy) s') /\
      hproves_weak thy h c
      ==> hproves_weak thy (MAP (HVSUBST ilist) h) (HVSUBST ilist c)) /\
  (!thy tyin h c.
      ALL (htype_ok (FST(FST thy))) (MAP FST tyin) /\ hproves_weak thy h c
      ==> hproves_weak thy (MAP (HINST tyin) h) (HINST tyin c)) /\
  (!thy h1 h2 l1 r1 l2 r2.
      hproves_weak thy h1 (l1 =:= r1) /\ hproves_weak thy h2 (l2 =:= r2) /\
      hwelltyped (TmComb l1 l2)
      ==> hproves_weak thy (HTERM_UNION h1 h2) (TmComb l1 l2 =:= TmComb r1 r2)) /\
  (!thy t.
      htheory_ok thy /\ hterm_ok (FST thy) t
      ==> hproves_weak thy [] (t =:= t)) /\
  (!thy c.
      htheory_ok thy /\ c IN SND thy
      ==> hproves_weak thy [] c)`;;

let HPROVES_IMP_WEAK = prove
 (`!thy h c. hproves thy h c ==> hproves_weak thy h c`,
  MATCH_MP_TAC hproves_INDUCT THEN MESON_TAC[hproves_weak_RULES]);;

let HBOOLVAR_TERM_OK = prove
 (`!x. hterm_ok (FST (hthyof hcore_ctxt)) (TmVar x HBool)`,
  REWRITE_TAC[hterm_ok; HCORE_FST] THEN
  REWRITE_TAC[hcore_ctxt; hinit_ctxt] THEN CONV_TAC HCONTEXT_CONV);;

let HPROVES_WEAK_DISTINCT_EQ = prove
 (`hproves_weak (hthyof hcore_ctxt) [] (TmVar "x" HBool =:= TmVar "y" HBool)`,
  SUBGOAL_THEN
   `hterm_ok (FST (hthyof hcore_ctxt)) (TmVar "x" HBool =:= TmVar "y" HBool) /\
    hterm_ok (FST (hthyof hcore_ctxt)) (TmVar "x" HBool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP HTHEORY_OK_STD_SIG HCORE_THEORY_OK) THEN
    SIMP_TAC[HTERM_OK_EQUATION; HBOOLVAR_TERM_OK; htypeof];
    ALL_TAC] THEN
  MP_TAC(SPECL [`hthyof hcore_ctxt`; `[]:holterm list`; `[]:holterm list`;
                `TmVar "x" HBool =:= TmVar "y" HBool`;
                `TmVar "x" HBool =:= TmVar "y" HBool`;
                `TmVar "x" HBool =:= TmVar "x" HBool`]
               (el 4 (CONJUNCTS hproves_weak_RULES))) THEN
  REWRITE_TAC[HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC(el 8 (CONJUNCTS hproves_weak_RULES)) THEN
  ASM_REWRITE_TAC[HCORE_THEORY_OK]);;

let HPROVES_WEAK_SIDE_CONDITION_FAILS = prove
 (`~HACONV (TmVar "x" HBool =:= TmVar "y" HBool)
           (TmVar "x" HBool =:= TmVar "x" HBool)`,
  REWRITE_TAC[HACONV_EQUATION; HACONV_VAR; holterm_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV STRING_EQ_CONV) THEN REWRITE_TAC[]);;

let HEQ_MP_ALPHA_CONDITION_NEEDED = prove
 (`hproves_weak (hthyof hcore_ctxt) [] (TmVar "x" HBool =:= TmVar "y" HBool) /\
   ~hproves (hthyof hcore_ctxt) [] (TmVar "x" HBool =:= TmVar "y" HBool)`,
  REWRITE_TAC[HPROVES_WEAK_DISTINCT_EQ; HCORE_DISTINCT_EQ_UNPROVABLE]);;
