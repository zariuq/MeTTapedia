(* ========================================================================= *)
(* De Bruijn terms, following the de Bruijn section of Candle's             *)
(* holSyntaxExtra: substitution and type instantiation commute with the      *)
(* translation into de Bruijn form, and alpha-equivalence of well-typed      *)
(* terms is equality of their de Bruijn forms.                               *)
(* ========================================================================= *)

let hdbterm_INDUCT,hdbterm_RECURSION = define_type
 "hdbterm = hdbVar string holtype
          | hdbBound num
          | hdbConst string holtype
          | hdbComb hdbterm hdbterm
          | hdbAbs holtype hdbterm";;

let hdbterm_DISTINCT = distinctness "hdbterm";;

let hdbterm_INJ = injectivity "hdbterm";;

(* ------------------------------------------------------------------------- *)
(* Binding a variable (a name and a type) as bound index n.                  *)
(* ------------------------------------------------------------------------- *)

let hbind = define
 `(hbind v n (hdbVar x ty) = if v = (x,ty) then hdbBound n else hdbVar x ty) /\
  (hbind v n (hdbBound m) = hdbBound m) /\
  (hbind v n (hdbConst x ty) = hdbConst x ty) /\
  (hbind v n (hdbComb t1 t2) = hdbComb (hbind v n t1) (hbind v n t2)) /\
  (hbind v n (hdbAbs ty tm) = hdbAbs ty (hbind v (n + 1) tm))`;;

(* ------------------------------------------------------------------------- *)
(* Translation into de Bruijn form.                                          *)
(* ------------------------------------------------------------------------- *)

let hdb = define
 `(hdb (TmVar x ty) = hdbVar x ty) /\
  (hdb (TmConst x ty) = hdbConst x ty) /\
  (hdb (TmComb t1 t2) = hdbComb (hdb t1) (hdb t2)) /\
  (hdb (TmAbs v tm) = hdbAbs (htypeof v) (hbind (hdest_var v) 0 (hdb tm)))`;;

(* ------------------------------------------------------------------------- *)
(* Substitution and free variables on de Bruijn terms.                       *)
(* ------------------------------------------------------------------------- *)

let hdbVSUBST = define
 `(hdbVSUBST ilist (hdbVar x ty) =
     HREV_ASSOCD (hdbVar x ty) ilist (hdbVar x ty)) /\
  (hdbVSUBST ilist (hdbBound m) = hdbBound m) /\
  (hdbVSUBST ilist (hdbConst x ty) = hdbConst x ty) /\
  (hdbVSUBST ilist (hdbComb t1 t2) =
     hdbComb (hdbVSUBST ilist t1) (hdbVSUBST ilist t2)) /\
  (hdbVSUBST ilist (hdbAbs ty t) = hdbAbs ty (hdbVSUBST ilist t))`;;

let hdbVFREE_IN = define
 `(hdbVFREE_IN v (hdbVar x ty) <=> hdbVar x ty = v) /\
  (hdbVFREE_IN v (hdbBound n) <=> F) /\
  (hdbVFREE_IN v (hdbConst x ty) <=> hdbConst x ty = v) /\
  (hdbVFREE_IN v (hdbComb t1 t2) <=> hdbVFREE_IN v t1 \/ hdbVFREE_IN v t2) /\
  (hdbVFREE_IN v (hdbAbs ty t) <=> hdbVFREE_IN v t)`;;

(* ------------------------------------------------------------------------- *)
(* Type instantiation on de Bruijn terms.                                    *)
(* ------------------------------------------------------------------------- *)

let hdbINST = define
 `(hdbINST tyin (hdbVar x ty) = hdbVar x (HTYPE_SUBST tyin ty)) /\
  (hdbINST tyin (hdbBound n) = hdbBound n) /\
  (hdbINST tyin (hdbConst x ty) = hdbConst x (HTYPE_SUBST tyin ty)) /\
  (hdbINST tyin (hdbComb t1 t2) =
     hdbComb (hdbINST tyin t1) (hdbINST tyin t2)) /\
  (hdbINST tyin (hdbAbs ty t) = hdbAbs (HTYPE_SUBST tyin ty) (hdbINST tyin t))`;;

(* ------------------------------------------------------------------------- *)
(* Basic properties of binding and substitution.                             *)
(* ------------------------------------------------------------------------- *)

let HBIND_NOT_FREE = prove
 (`!t n x ty. ~hdbVFREE_IN (hdbVar x ty) t ==> hbind (x,ty) n t = t`,
  MATCH_MP_TAC hdbterm_INDUCT THEN
  REWRITE_TAC[hbind; hdbVFREE_IN; DE_MORGAN_THM; hdbterm_INJ; PAIR_EQ] THEN
  SIMP_TAC[] THEN MESON_TAC[]);;

let HDBVFREE_IN_BIND = prove
 (`!tm y n x ty. hdbVFREE_IN y (hbind (x,ty) n tm) <=>
                 ~(y = hdbVar x ty) /\ hdbVFREE_IN y tm`,
  MATCH_MP_TAC hdbterm_INDUCT THEN REWRITE_TAC[hbind; hdbVFREE_IN] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[hdbVFREE_IN; hdbterm_DISTINCT] THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST1_TAC) THEN MESON_TAC[];
      EQ_TAC THEN SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[hdbterm_INJ] THEN ASM_MESON_TAC[]];
    REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[hdbterm_DISTINCT];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let HDBVSUBST_FREES = prove
 (`!tm ls ls'. (!k. hdbVFREE_IN k tm ==> HREV_ASSOCD k ls k = HREV_ASSOCD k ls' k)
               ==> hdbVSUBST ls tm = hdbVSUBST ls' tm`,
  MATCH_MP_TAC hdbterm_INDUCT THEN REWRITE_TAC[hdbVSUBST; hdbVFREE_IN] THEN
  SIMP_TAC[hdbterm_INJ] THEN MESON_TAC[]);;

let HDBVSUBST_NIL = prove
 (`!tm. hdbVSUBST [] tm = tm`,
  MATCH_MP_TAC hdbterm_INDUCT THEN ASM_SIMP_TAC[hdbVSUBST; HREV_ASSOCD]);;

let HREV_ASSOCD_NOT_MEM_SND = prove
 (`!l:(B#A)list a d. ~MEM a (MAP SND l) ==> HREV_ASSOCD a l d = d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HREV_ASSOCD_NOT_MEM THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
  MESON_TAC[SND]);;

let HBIND_DBVSUBST = prove
 (`!tm x ty n ls.
        ~MEM (hdbVar x ty) (MAP SND ls) /\
        (!k. hdbVFREE_IN k tm /\ MEM k (MAP SND ls)
             ==> ~hdbVFREE_IN (hdbVar x ty) (HREV_ASSOCD k ls k))
        ==> hbind (x,ty) n (hdbVSUBST ls tm) = hdbVSUBST ls (hbind (x,ty) n tm)`,
  MATCH_MP_TAC hdbterm_INDUCT THEN
  REWRITE_TAC[hbind; hdbVSUBST; hdbVFREE_IN] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:string`; `b:holtype`; `x:string`; `ty:holtype`;
                         `n:num`; `ls:(hdbterm#hdbterm)list`] THEN
    STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o GSYM) THEN
      ASM_SIMP_TAC[HREV_ASSOCD_NOT_MEM_SND; hbind; hdbVSUBST];
      REWRITE_TAC[hdbVSUBST] THEN MATCH_MP_TAC HBIND_NOT_FREE THEN
      ASM_CASES_TAC `MEM (hdbVar a b) (MAP SND (ls:(hdbterm#hdbterm)list))` THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[HREV_ASSOCD_NOT_MEM_SND; hdbVFREE_IN; hdbterm_INJ] THEN
        ASM_MESON_TAC[]]];
    SIMP_TAC[hdbterm_INJ] THEN MESON_TAC[];
    SIMP_TAC[hdbterm_INJ] THEN MESON_TAC[]]);;

let HBIND_DBVSUBST_CONS = prove
 (`!tm z zty x xty n ls.
        ~hdbVFREE_IN (hdbVar z zty) (hdbVSUBST ls (hbind (x,xty) n tm))
        ==> hbind (z,zty) n
              (hdbVSUBST (CONS (hdbVar z zty,hdbVar x xty) ls) tm) =
            hdbVSUBST ls (hbind (x,xty) n tm)`,
  MATCH_MP_TAC hdbterm_INDUCT THEN
  REWRITE_TAC[hbind; hdbVSUBST; hdbVFREE_IN; HREV_ASSOCD] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[hdbterm_INJ; PAIR_EQ] THEN
    ASM_CASES_TAC `x:string = a0 /\ xty:holtype = a1` THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      REWRITE_TAC[hbind; hdbVSUBST];
      REWRITE_TAC[hdbVSUBST] THEN MESON_TAC[HBIND_NOT_FREE]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    BINOP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let HDBVFREE_IN_DBVSUBST = prove
 (`!tm u uty ilist.
        hdbVFREE_IN (hdbVar u uty) (hdbVSUBST ilist tm) <=>
        ?y ty. hdbVFREE_IN (hdbVar y ty) tm /\
               hdbVFREE_IN (hdbVar u uty)
                 (HREV_ASSOCD (hdbVar y ty) ilist (hdbVar y ty))`,
  MATCH_MP_TAC hdbterm_INDUCT THEN
  REWRITE_TAC[hdbVSUBST; hdbVFREE_IN; hdbterm_DISTINCT] THEN
  REPEAT CONJ_TAC THEN TRY(REWRITE_TAC[hdbterm_INJ] THEN MESON_TAC[] THEN NO_TAC) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let HDB_VAR = prove
 (`!t x ty. hdb t = hdbVar x ty <=> t = TmVar x ty`,
  MATCH_MP_TAC holterm_INDUCT THEN
  REWRITE_TAC[hdb; hdbterm_INJ; hdbterm_DISTINCT; holterm_INJ;
              holterm_DISTINCT]);;

let HDB_CONST = prove
 (`!t x ty. hdb t = hdbConst x ty <=> t = TmConst x ty`,
  MATCH_MP_TAC holterm_INDUCT THEN
  REWRITE_TAC[hdb; hdbterm_INJ; hdbterm_DISTINCT; holterm_INJ;
              holterm_DISTINCT]);;

let HDBVFREE_IN_VFREE_IN = prove
 (`!tm. hwelltyped tm ==> !v. hdbVFREE_IN (hdb v) (hdb tm) <=> HVFREE_IN v tm`,
  MATCH_MP_TAC HWELLTYPED_INDUCT THEN
  REWRITE_TAC[hdb; hdbVFREE_IN; HVFREE_IN; hdest_var; htypeof] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[HDB_VAR];
    MESON_TAC[HDB_CONST];
    SIMP_TAC[];
    SIMP_TAC[HDBVFREE_IN_BIND; HDB_VAR] THEN MESON_TAC[]]);;

let HDBVFREE_IN_VAR = prove
 (`!tm x ty. hwelltyped tm
             ==> (hdbVFREE_IN (hdbVar x ty) (hdb tm) <=> HVFREE_IN (TmVar x ty) tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `tm:holterm` HDBVFREE_IN_VFREE_IN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `TmVar x ty`) THEN REWRITE_TAC[hdb]);;

(* ------------------------------------------------------------------------- *)
(* Substitution commutes with the translation into de Bruijn form.           *)
(* ------------------------------------------------------------------------- *)

let MAP_HDB_FILTER_NEQ = prove
 (`!ls z ty.
        MAP (\(x,y). (hdb x,hdb y)) (FILTER (\(s',s). ~(s = TmVar z ty)) ls) =
        FILTER (\(x,y). ~(y = hdbVar z ty)) (MAP (\(x,y). (hdb x,hdb y)) ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FILTER] THEN
  SPEC_TAC(`h:holterm#holterm`,`p:holterm#holterm`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[HDB_VAR] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let HREV_ASSOCD_MAP_HDB = prove
 (`!ls k ky.
        HREV_ASSOCD (hdbVar k ky) (MAP (\(x,y). (hdb x,hdb y)) ls) (hdbVar k ky) =
        hdb (HREV_ASSOCD (TmVar k ky) ls (TmVar k ky))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; HREV_ASSOCD; hdb] THEN
  SPEC_TAC(`h:holterm#holterm`,`p:holterm#holterm`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[HREV_ASSOCD; HDB_VAR] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let HREV_ASSOCD_WELLTYPED = prove
 (`!ilist x ty.
        (!k v. MEM (v,k) ilist ==> hwelltyped v)
        ==> hwelltyped (HREV_ASSOCD (TmVar x ty) ilist (TmVar x ty))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ilist:(holterm#holterm)list`; `TmVar x ty`; `TmVar x ty`]
                HREV_ASSOCD_MEM) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[HWELLTYPED_CLAUSES] THEN ASM_MESON_TAC[]);;

let HVSUBST_DBVSUBST = prove
 (`!tm. hwelltyped tm
        ==> !ilist. (!k v. MEM (v,k) ilist
                           ==> hwelltyped v /\ ?x ty. k = TmVar x ty)
                    ==> hdb (HVSUBST ilist tm) =
                        hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist) (hdb tm)`,
  MATCH_MP_TAC HWELLTYPED_INDUCT THEN REWRITE_TAC[HVSUBST; hdb; hdbVSUBST] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[HREV_ASSOCD_MAP_HDB];
    REPEAT STRIP_TAC THEN REWRITE_TAC[hdbterm_INJ] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:string`; `bty:holtype`; `tm:holterm`] THEN
  STRIP_TAC THEN X_GEN_TAC `ilist:(holterm#holterm)list` THEN DISCH_TAC THEN
  REWRITE_TAC[hdest_var; htypeof; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = TmVar b bty))
                              (ilist:(holterm#holterm)list)` THEN
  SUBGOAL_THEN
   `!k v. MEM (v,k) ilist' ==> hwelltyped v /\ ?x ty. k = TmVar x ty`
  ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MEM_FILTER] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `MAP (\(x,y). (hdb x,hdb y)) ilist' =
    FILTER (\(x,y). ~(y = hdbVar b bty)) (MAP (\(x,y). (hdb x,hdb y)) ilist)`
  ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[MAP_HDB_FILTER_NEQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist') (hbind (b,bty) 0 (hdb tm)) =
    hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist) (hbind (b,bty) 0 (hdb tm))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HDBVSUBST_FREES THEN ASM_REWRITE_TAC[HDBVFREE_IN_BIND] THEN
    REWRITE_TAC[HREV_ASSOCD_FILTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[hdb; hdest_var; htypeof; hdbterm_INJ] THENL
   [ABBREV_TAC `zn = HVARIANT (HVSUBST ilist' tm) b bty` THEN
    SUBGOAL_THEN
     `hdb (HVSUBST (CONS (TmVar zn bty,TmVar b bty) ilist') tm) =
      hdbVSUBST (MAP (\(x,y). (hdb x,hdb y))
                     (CONS (TmVar zn bty,TmVar b bty) ilist')) (hdb tm)`
    SUBST1_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
      ASM_MESON_TAC[HWELLTYPED_CLAUSES];
      ALL_TAC] THEN
    REWRITE_TAC[MAP] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[hdb] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist')
                          (hbind (b,bty) 0 (hdb tm))` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC HBIND_DBVSUBST_CONS THEN
    REWRITE_TAC[HDBVFREE_IN_DBVSUBST; HDBVFREE_IN_BIND; HREV_ASSOCD_MAP_HDB] THEN
    ASM_SIMP_TAC[HDBVFREE_IN_VAR] THEN
    SUBGOAL_THEN
     `!y yty. hdbVFREE_IN (hdbVar zn bty)
                (hdb (HREV_ASSOCD (TmVar y yty) ilist' (TmVar y yty))) <=>
              HVFREE_IN (TmVar zn bty)
                (HREV_ASSOCD (TmVar y yty) ilist' (TmVar y yty))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC HDBVFREE_IN_VAR THEN
      MATCH_MP_TAC HREV_ASSOCD_WELLTYPED THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`HVSUBST ilist' tm`; `b:string`; `bty:holtype`]
                  HVARIANT_THM) THEN
    ASM_SIMP_TAC[HVFREE_IN_VSUBST] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hdb (HVSUBST ilist' tm) =
                hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist') (hdb tm)`
  SUBST1_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist')
                        (hbind (b,bty) 0 (hdb tm))` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC HBIND_DBVSUBST THEN
  REWRITE_TAC[GSYM MAP_o; MEM_MAP; EXISTS_PAIR_THM; o_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`p1:hdbterm`; `p2:hdbterm`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q1:holterm`
      (X_CHOOSE_THEN `q2:holterm` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    UNDISCH_TAC `MEM (q1:holterm,q2:holterm) ilist'` THEN
    EXPAND_TAC "ilist'" THEN
    REWRITE_TAC[MEM_FILTER] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_MESON_TAC[HDB_VAR];
    ALL_TAC] THEN
  X_GEN_TAC `k:hdbterm` THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:hdbterm` (X_CHOOSE_THEN `p2:hdbterm`
    (CONJUNCTS_THEN2 MP_TAC (SUBST_ALL_TAC o SYM)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:holterm` (X_CHOOSE_THEN `s:holterm`
    (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (K ALL_TAC) SUBST_ALL_TAC)))) THEN
  SUBGOAL_THEN `?y yty. s = TmVar y yty` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[hdb]) THEN REWRITE_TAC[hdb] THEN
  REWRITE_TAC[HREV_ASSOCD_MAP_HDB] THEN
  SUBGOAL_THEN `hwelltyped (HREV_ASSOCD (TmVar y yty) ilist' (TmVar y yty))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HREV_ASSOCD_WELLTYPED THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[HDBVFREE_IN_VAR] THEN
  UNDISCH_TAC `hdbVFREE_IN (hdbVar y yty) (hdb tm)` THEN
  ASM_SIMP_TAC[HDBVFREE_IN_VAR] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ilist':(holterm#holterm)list`; `TmVar y yty`; `TmVar y yty`]
                HREV_ASSOCD_MEM) THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `~EX (\(s',s). HVFREE_IN (TmVar b bty) s' /\ HVFREE_IN s tm)
                     (ilist':(holterm#holterm)list)` THEN
    REWRITE_TAC[NOT_EX; GSYM ALL_MEM] THEN
    DISCH_THEN(MP_TAC o SPEC `(HREV_ASSOCD (TmVar y yty) ilist' (TmVar y yty),
                               TmVar y yty)`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[HVFREE_IN; holterm_INJ] THEN
    UNDISCH_TAC `MEM (v:holterm,TmVar y yty) ilist'` THEN
    EXPAND_TAC "ilist'" THEN
    REWRITE_TAC[MEM_FILTER] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[holterm_INJ] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Type instantiation commutes with the translation into de Bruijn form.    *)
(* ------------------------------------------------------------------------- *)

let HDBINST_BIND = prove
 (`!tm x ty n ls.
      (!ty'. hdbVFREE_IN (hdbVar x ty') tm /\
             HTYPE_SUBST ls ty' = HTYPE_SUBST ls ty ==> ty' = ty)
      ==> hdbINST ls (hbind (x,ty) n tm) =
          hbind (x,HTYPE_SUBST ls ty) n (hdbINST ls tm)`,
  MATCH_MP_TAC hdbterm_INDUCT THEN REWRITE_TAC[hbind; hdbINST; hdbVFREE_IN] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[hdbterm_INJ; PAIR_EQ] THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:string = a0` THEN ASM_REWRITE_TAC[hdbINST] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_CASES_TAC `ty:holtype = a1` THEN ASM_REWRITE_TAC[hdbINST] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[hdbINST] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN REWRITE_TAC[hdbterm_INJ] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN REWRITE_TAC[hdbterm_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let HRESULT_CASES = prove
 (`!r. ~HIS_CLASH r <=> ?t. r = HResult t`,
  MATCH_MP_TAC hresult_INDUCT THEN
  REWRITE_TAC[HIS_CLASH; hresult_INJ; hresult_DISTINCT] THEN MESON_TAC[]);;

let HRESULT_CASES2 = prove
 (`!r. HIS_RESULT r <=> ?t. r = HResult t`,
  MATCH_MP_TAC hresult_INDUCT THEN
  REWRITE_TAC[HIS_RESULT; hresult_INJ; hresult_DISTINCT] THEN MESON_TAC[]);;

let HINST_CORE_DBINST = prove
 (`!tm env tyin tmi.
      hwelltyped tm /\
      (!s s'. MEM (s,s') env
              ==> ?x ty. s = TmVar x ty /\ s' = TmVar x (HTYPE_SUBST tyin ty)) /\
      HINST_CORE env tyin tm = HResult tmi
      ==> hdb tmi = hdbINST tyin (hdb tm)`,
  MATCH_MP_TAC HSIZEOF_INDUCT THEN GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `tm:holterm` (cases "holterm")) THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`env:(holterm#holterm)list`;
                       `tyin:(holtype#holtype)list`; `tmi:holterm`] THENL
   [REWRITE_TAC[HINST_CORE; LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
    REWRITE_TAC[hresult_INJ; hresult_DISTINCT] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[hdb; hdbINST];
    REWRITE_TAC[HINST_CORE; hresult_INJ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[hdb; hdbINST];
    REWRITE_TAC[HWELLTYPED_CLAUSES; HINST_CORE; LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN STRIP_TAC THENL
     [UNDISCH_TAC `HIS_CLASH (HINST_CORE env tyin a0)` THEN
      ASM_REWRITE_TAC[HIS_CLASH];
      UNDISCH_TAC `HIS_CLASH (HINST_CORE env tyin a1)` THEN
      ASM_REWRITE_TAC[HIS_CLASH];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HRESULT_CASES; hresult_INJ]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `?t. HINST_CORE env tyin a0 = HResult t` THEN
    DISCH_THEN(X_CHOOSE_TAC `r0:holterm`) THEN
    UNDISCH_TAC `?t. HINST_CORE env tyin a1 = HResult t` THEN
    DISCH_THEN(X_CHOOSE_TAC `r1:holterm`) THEN
    ASM_REWRITE_TAC[HRESULT; hdb; hdbINST; hdbterm_INJ] THEN
    CONJ_TAC THENL
     [USE_THEN "ih" (MP_TAC o SPEC `a0:holterm`);
      USE_THEN "ih" (MP_TAC o SPEC `a1:holterm`)] THEN
    REWRITE_TAC[hsizeof; ARITH_RULE `s < 1 + s + t /\ t < 1 + s + t`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HWELLTYPED_CLAUSES] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = `a0:holterm`)) THEN
  UNDISCH_TAC `HINST_CORE env tyin (TmAbs (TmVar n ty) a1) = HResult tmi` THEN
  REWRITE_TAC[HINST_CORE; hdest_var; FST; SND; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[hdb; hdest_var; htypeof; hdbINST] THEN
  USE_THEN "ih" (MP_TAC o SPEC `a1:holterm`) THEN
  REWRITE_TAC[hsizeof; ARITH_RULE `t < 2 + t`] THEN
  DISCH_THEN(LABEL_TAC "iht") THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[hresult_INJ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `HIS_RESULT (HINST_CORE (CONS (TmVar n ty,
                   TmVar n (HTYPE_SUBST tyin ty)) env) tyin a1)` THEN
    REWRITE_TAC[HRESULT_CASES2] THEN DISCH_THEN(X_CHOOSE_TAC `r1:holterm`) THEN
    ASM_REWRITE_TAC[HRESULT; hdb; hdest_var; htypeof; hdbterm_INJ] THEN
    SUBGOAL_THEN `hdb r1 = hdbINST tyin (hdb a1)` SUBST1_TAC THENL
     [USE_THEN "iht" MATCH_MP_TAC THEN
      EXISTS_TAC `CONS (TmVar n ty,TmVar n (HTYPE_SUBST tyin ty)) env` THEN
      ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC HDBINST_BIND THEN
    X_GEN_TAC `ty':holtype` THEN ASM_SIMP_TAC[HDBVFREE_IN_VAR] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`a1:holterm`;
                  `CONS (TmVar n ty,TmVar n (HTYPE_SUBST tyin ty)) env`;
                  `tyin:(holtype#holtype)list`] HINST_CORE_HAS_TYPE) THEN
    ASM_REWRITE_TAC[hresult_DISTINCT; hresult_INJ] THEN
    ANTS_TAC THENL [REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`n:string`; `ty':holtype`] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[HREV_ASSOCD; holterm_INJ] THEN MESON_TAC[];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
       can (find_term (fun t -> t = `HIS_RESULT`)) (concl th))) THEN
    ASM_REWRITE_TAC[HIS_RESULT];
    ALL_TAC;
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
       can (find_term (fun t -> t = `HIS_RESULT`)) (concl th))) THEN
    ASM_REWRITE_TAC[HIS_RESULT]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`a1:holterm`; `[]:(holterm#holterm)list`;
                `tyin:(holtype#holtype)list`] HINST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; HREV_ASSOCD] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:holterm` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[HRESULT] THEN
  ABBREV_TAC `z = HVARIANT t0 n (HTYPE_SUBST tyin ty)` THEN
  SUBGOAL_THEN `~HVFREE_IN (TmVar z ty) a1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t0:holterm`; `n:string`; `HTYPE_SUBST tyin ty`]
                  HVARIANT_THM) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t' = HVSUBST [TmVar z ty,TmVar n ty] a1` THEN
  SUBGOAL_THEN `hsizeof t' = hsizeof a1 /\ hwelltyped t'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC HSIZEOF_VSUBST THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
      MESON_TAC[];
      MATCH_MP_TAC HVSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      MESON_TAC[HHAS_TYPE_VAR]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
     can (find_term (fun t -> t = `HIS_RESULT`)) (concl th) &&
     not (is_neg (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HRESULT_CASES2] THEN DISCH_THEN(X_CHOOSE_TAC `r2:holterm`) THEN
  ASM_REWRITE_TAC[HRESULT; hdb; hdest_var; htypeof; hdbterm_INJ] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     rand (concl th) = `HResult r2`)) THEN
  ASM_REWRITE_TAC[HRESULT] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[HRESULT] THEN
  SUBGOAL_THEN `hdb r2 = hdbINST tyin (hdb t')` SUBST1_TAC THENL
   [USE_THEN "ih" (MP_TAC o SPEC `t':holterm`) THEN
    REWRITE_TAC[hsizeof; ASSUME `hsizeof t' = hsizeof a1`;
                ARITH_RULE `t < 2 + t`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `CONS (TmVar z ty,TmVar z (HTYPE_SUBST tyin ty)) env` THEN
    ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hdb t' = hdbVSUBST [hdbVar z ty,hdbVar n ty] (hdb a1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN MP_TAC(SPEC `a1:holterm` HVSUBST_DBVSUBST) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `[TmVar z ty,TmVar n ty]`) THEN
    REWRITE_TAC[MEM; PAIR_EQ; MAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[hdb] THEN
    ANTS_TAC THENL [MESON_TAC[HWELLTYPED_CLAUSES]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hbind (n,ty) 0 (hdb a1) = hbind (z,ty) 0 (hdb t')`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`hdb a1`; `z:string`; `ty:holtype`; `n:string`;
                   `ty:holtype`; `0`; `[]:(hdbterm#hdbterm)list`]
                  HBIND_DBVSUBST_CONS) THEN
    REWRITE_TAC[HDBVSUBST_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[HDBVFREE_IN_BIND] THEN ASM_SIMP_TAC[HDBVFREE_IN_VAR];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC HDBINST_BIND THEN
  X_GEN_TAC `ty':holtype` THEN ASM_SIMP_TAC[HDBVFREE_IN_VAR] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t':holterm`;
                `CONS (TmVar z ty,TmVar z (HTYPE_SUBST tyin ty)) env`;
                `tyin:(holtype#holtype)list`] HINST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[hresult_DISTINCT; hresult_INJ] THEN
  ANTS_TAC THENL [REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:string`; `ty':holtype`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[HREV_ASSOCD; holterm_INJ] THEN MESON_TAC[]);;

let HINST_DBINST = prove
 (`!tm tyin. hwelltyped tm ==> hdb (HINST tyin tm) = hdbINST tyin (hdb tm)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HINST_CORE_DBINST THEN
  MAP_EVERY EXISTS_TAC [`[]:(holterm#holterm)list`] THEN
  ASM_SIMP_TAC[MEM; HINST_THM]);;

(* ------------------------------------------------------------------------- *)
(* Translation relative to a list of enclosing binders.                      *)
(* ------------------------------------------------------------------------- *)

let hdbvar = define
 `(hdbvar [] n x ty = hdbVar x ty) /\
  (hdbvar (CONS v vs) n x ty =
     if v = (x,ty) then hdbBound n else hdbvar vs (n + 1) x ty)`;;

let hdbterm_env = define
 `(hdbterm_env env (TmVar s ty) = hdbvar env 0 s ty) /\
  (hdbterm_env env (TmConst s ty) = hdbConst s ty) /\
  (hdbterm_env env (TmComb t1 t2) =
     hdbComb (hdbterm_env env t1) (hdbterm_env env t2)) /\
  (hdbterm_env env (TmAbs v t) =
     hdbAbs (htypeof v) (hdbterm_env (CONS (hdest_var v) env) t))`;;

let hbind_list_aux = define
 `(hbind_list_aux n [] tm = tm) /\
  (hbind_list_aux n (CONS v vs) tm = hbind_list_aux (n + 1) vs (hbind v n tm))`;;

let HBIND_LIST_AUX_CLAUSES = prove
 (`(!env m n. hbind_list_aux m env (hdbBound n) = hdbBound n) /\
   (!env m x ty. hbind_list_aux m env (hdbConst x ty) = hdbConst x ty) /\
   (!env m t1 t2. hbind_list_aux m env (hdbComb t1 t2) =
                  hdbComb (hbind_list_aux m env t1) (hbind_list_aux m env t2)) /\
   (!env m ty tm. hbind_list_aux m env (hdbAbs ty tm) =
                  hdbAbs ty (hbind_list_aux (m + 1) env tm))`,
  REPEAT CONJ_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[hbind_list_aux; hbind]);;

let HBIND_LIST_AUX_VAR = prove
 (`!env m x ty. hbind_list_aux m env (hdbVar x ty) = hdbvar env m x ty`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[hbind_list_aux; hdbvar; hbind] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[HBIND_LIST_AUX_CLAUSES]);;

let HDBTERM_ENV_BIND = prove
 (`!tm env. hdbterm_env env tm = hbind_list_aux 0 env (hdb tm)`,
  MATCH_MP_TAC holterm_INDUCT THEN
  REWRITE_TAC[hdbterm_env; hdb; HBIND_LIST_AUX_CLAUSES; HBIND_LIST_AUX_VAR;
              hbind_list_aux; ADD_CLAUSES] THEN
  SIMP_TAC[hbind_list_aux; ARITH]);;

let HDBTERM_ENV_DB = prove
 (`!tm. hdbterm_env [] tm = hdb tm`,
  REWRITE_TAC[HDBTERM_ENV_BIND; hbind_list_aux]);;

let HDBVAR_CASES = prove
 (`!env n x ty. hdbvar env n x ty = hdbVar x ty \/
                ?k. n <= k /\ hdbvar env n x ty = hdbBound k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[hdbvar] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[hdbterm_DISTINCT] THENL
   [MESON_TAC[LE_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `x:string`; `ty:holtype`]) THEN
  MESON_TAC[ARITH_RULE `n + 1 <= k ==> n <= k`]);;

(* ------------------------------------------------------------------------- *)
(* Alpha-equivalence of well-typed terms is equality of de Bruijn forms.    *)
(* ------------------------------------------------------------------------- *)

let HALPHAVARS_HDBVAR = prove
 (`!env n x1 ty1 x2 ty2.
        (!a b. MEM (a,b) env ==> (?x ty. a = TmVar x ty) /\
                                 (?x ty. b = TmVar x ty)) /\
        HALPHAVARS env (TmVar x1 ty1,TmVar x2 ty2)
        ==> hdbvar (MAP (hdest_var o FST) env) n x1 ty1 =
            hdbvar (MAP (hdest_var o SND) env) n x2 ty2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HALPHAVARS; MAP; hdbvar; MEM] THENL
   [SIMP_TAC[holterm_INJ]; ALL_TAC] THEN
  SPEC_TAC(`h:holterm#holterm`,`p:holterm#holterm`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:holterm`; `b:holterm`] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[o_THM; FST; SND; PAIR_EQ] THEN STRIP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq (concl th) && is_var (rhs (concl th))))) THEN
    REWRITE_TAC[hdest_var];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?xa ya. a = TmVar xa ya) /\ (?xb yb. b = TmVar xb yb)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. MEM (a,b) t ==> (?x ty. a = TmVar x ty) /\
                                      (?x ty. b = TmVar x ty)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
         is_var (lhs (concl th))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[holterm_INJ]) THEN
  ASM_REWRITE_TAC[hdest_var; PAIR_EQ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let HRACONV_DBTERM = prove
 (`!env tp. HRACONV env tp
            ==> hwelltyped (FST tp) /\ hwelltyped (SND tp) /\
                (!a b. MEM (a,b) env ==> (?x ty. a = TmVar x ty) /\
                                         (?x ty. b = TmVar x ty))
                ==> hdbterm_env (MAP (hdest_var o FST) env) (FST tp) =
                    hdbterm_env (MAP (hdest_var o SND) env) (SND tp)`,
  MATCH_MP_TAC HRACONV_INDUCT THEN
  REWRITE_TAC[FST; SND; hdbterm_env; HWELLTYPED_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[HALPHAVARS_HDBVAR];
    REPEAT STRIP_TAC THEN REWRITE_TAC[hdbterm_INJ] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[MAP; o_THM; FST; SND] THEN DISCH_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n1:string` (X_CHOOSE_THEN
      `ty1:holtype` STRIP_ASSUME_TAC)) MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n2:string` (X_CHOOSE_THEN
      `ty2:holtype` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
           is_var (lhs (concl th)) && type_of (lhs (concl th)) = `:holterm`))) THEN
    ASM_REWRITE_TAC[hdbterm_INJ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]]);;

let HDBVAR_ALPHAVARS = prove
 (`!env1 env2 n x1 ty1 x2 ty2.
        LENGTH env1 = LENGTH env2 /\
        hdbvar env1 n x1 ty1 = hdbvar env2 n x2 ty2
        ==> HALPHAVARS (ZIP (MAP (\(x,ty). TmVar x ty) env1)
                            (MAP (\(x,ty). TmVar x ty) env2))
                       (TmVar x1 ty1,TmVar x2 ty2)`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; NOT_SUC; MAP; ZIP; hdbvar; HALPHAVARS; hdbterm_INJ] THEN
    SIMP_TAC[holterm_INJ];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; GSYM NOT_SUC; SUC_INJ] THEN
  SPEC_TAC(`h:string#holtype`,`p:string#holtype`) THEN
  SPEC_TAC(`h':string#holtype`,`q:string#holtype`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:string`; `c1:holtype`; `a1:string`; `d1:holtype`] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP; ZIP; hdbvar; HALPHAVARS; PAIR_EQ; holterm_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[holterm_INJ] THEN
  ASM_CASES_TAC `a1:string = x1 /\ d1:holtype = ty1` THEN
  ASM_CASES_TAC `b1:string = x2 /\ c1:holtype = ty2` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`t':(string#holtype)list`; `n + 1`; `x2:string`;
                  `ty2:holtype`] HDBVAR_CASES) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `hdbBound n`)) THEN
    REWRITE_TAC[hdbterm_DISTINCT; GSYM hdbterm_DISTINCT; hdbterm_INJ] THEN
    MESON_TAC[ARITH_RULE `~(n + 1 <= n)`];
    MP_TAC(SPECL [`t:(string#holtype)list`; `n + 1`; `x1:string`;
                  `ty1:holtype`] HDBVAR_CASES) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `hdbBound n`)) THEN
    REWRITE_TAC[hdbterm_DISTINCT; GSYM hdbterm_DISTINCT; hdbterm_INJ] THEN
    MESON_TAC[ARITH_RULE `~(n + 1 <= n)`];
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n + 1` THEN
    ASM_REWRITE_TAC[]]);;

let HDBVAR_NOT = prove
 (`!env n x ty c d s t ty' u.
        ~(hdbvar env n x ty = hdbConst c d) /\
        ~(hdbvar env n x ty = hdbComb s t) /\
        ~(hdbvar env n x ty = hdbAbs ty' u)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`env:(string#holtype)list`; `n:num`; `x:string`; `ty:holtype`]
               HDBVAR_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[hdbterm_DISTINCT; GSYM hdbterm_DISTINCT]);;

let HDBTERM_RACONV = prove
 (`!t1 env1 t2 env2.
        hwelltyped t1 /\ hwelltyped t2 /\
        hdbterm_env env1 t1 = hdbterm_env env2 t2 /\ LENGTH env1 = LENGTH env2
        ==> HRACONV (ZIP (MAP (\(x,ty). TmVar x ty) env1)
                         (MAP (\(x,ty). TmVar x ty) env2)) (t1,t2)`,
  MATCH_MP_TAC holterm_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC; REPEAT GEN_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC] THEN
  STRUCT_CASES_TAC(SPEC `t2:holterm` (cases "holterm")) THEN
  REWRITE_TAC[hdbterm_env; HRACONV; hdbterm_DISTINCT; GSYM hdbterm_DISTINCT;
              hdbterm_INJ; HDBVAR_NOT; GSYM HDBVAR_NOT] THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HDBVAR_ALPHAVARS THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
    SIMP_TAC[];
    REWRITE_TAC[HWELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    USE_THEN "ih" (CONJUNCTS_THEN ASSUME_TAC) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[HWELLTYPED_CLAUSES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hdbterm_env (CONS (hdest_var a0) env1) a1 =
                 hdbterm_env (CONS (hdest_var a0') env2) a1'` THEN
    ASM_REWRITE_TAC[hdest_var] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `CONS (TmVar n ty,TmVar n' ty')
           (ZIP (MAP (\(x,ty). TmVar x ty) env1)
                (MAP (\(x,ty). TmVar x ty) env2)) =
      ZIP (MAP (\(x,ty). TmVar x ty) (CONS (n,ty) env1))
          (MAP (\(x,ty). TmVar x ty) (CONS (n',ty') env2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[MAP; ZIP] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "ih" (MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[LENGTH]]);;

let HACONV_DB = prove
 (`!t1 t2. hwelltyped t1 /\ hwelltyped t2
           ==> (HACONV t1 t2 <=> hdb t1 = hdb t2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HACONV; GSYM HDBTERM_ENV_DB] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`[]:(holterm#holterm)list`; `(t1:holterm,t2:holterm)`]
                 HRACONV_DBTERM) THEN
    ASM_REWRITE_TAC[MEM; MAP; FST; SND];
    DISCH_TAC THEN
    MP_TAC(SPECL [`t1:holterm`; `[]:(string#holtype)list`; `t2:holterm`;
                  `[]:(string#holtype)list`] HDBTERM_RACONV) THEN
    ASM_REWRITE_TAC[MAP; ZIP; LENGTH]]);;

(* ------------------------------------------------------------------------- *)
(* Hence substitution and instantiation respect alpha-equivalence.          *)
(* ------------------------------------------------------------------------- *)

let HACONV_VSUBST = prove
 (`!t1 t2 ilist.
      hwelltyped t1 /\ hwelltyped t2 /\
      (!s s'. MEM (s',s) ilist ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty) /\
      HACONV t1 t2
      ==> HACONV (HVSUBST ilist t1) (HVSUBST ilist t2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k v. MEM (v,k) ilist ==> hwelltyped v /\ ?x ty. k = TmVar x ty`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:holterm`; `v:holterm`]) THEN
    ASM_REWRITE_TAC[hwelltyped] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hwelltyped (HVSUBST ilist t1) /\ hwelltyped (HVSUBST ilist t2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HVSUBST_WELLTYPED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HACONV_DB] THEN
  SUBGOAL_THEN
   `!t. hwelltyped t
        ==> hdb (HVSUBST ilist t) =
            hdbVSUBST (MAP (\(x,y). (hdb x,hdb y)) ilist) (hdb t)`
  (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN MP_TAC(SPEC `t:holterm` HVSUBST_DBVSUBST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  AP_TERM_TAC THEN ASM_MESON_TAC[HACONV_DB]);;

let HACONV_INST = prove
 (`!t1 t2 tyin. hwelltyped t1 /\ hwelltyped t2 /\ HACONV t1 t2
                ==> HACONV (HINST tyin t1) (HINST tyin t2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[HACONV_DB; HINST_WELLTYPED; HINST_DBINST] THEN
  ASM_MESON_TAC[HACONV_DB]);;
