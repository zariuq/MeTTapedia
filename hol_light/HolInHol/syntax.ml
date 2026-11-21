(* ========================================================================= *)
(* HOL syntax with type operators and constants, signatures, theories and    *)
(* the inference system, following Candle's holSyntax.                       *)
(*                                                                           *)
(* Names carry an h/H prefix (types holtype and holterm) so that this file   *)
(* can be loaded in the same session as Model/syntax.ml.                     *)
(*                                                                           *)
(* Hypotheses are lists read as sets up to alpha-equivalence, as in          *)
(* Model/syntax.ml: union deduplicates up to HACONV, DEDUCT_ANTISYM filters, *)
(* INST and INST_TYPE map.                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Association lists.                                                        *)
(* ------------------------------------------------------------------------- *)

let HREV_ASSOCD = define
 `(HREV_ASSOCD (a:B) [] (d:A) = d) /\
  (HREV_ASSOCD a (CONS (x,y) t) d = if y = a then x else HREV_ASSOCD a t d)`;;

let HREV_ASSOCD_FILTER = prove
 (`!l:(B#A)list a b P.
        HREV_ASSOCD a (FILTER (\(y,x). P x) l) b =
            if P a then HREV_ASSOCD a l b else b`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HREV_ASSOCD; FILTER; COND_ID] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`h:B#A`,`p:B#A`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `x:A`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(P:A->bool) x` THEN ASM_REWRITE_TAC[HREV_ASSOCD] THEN
  ASM_MESON_TAC[]);;

let HREV_ASSOCD_MEM = prove
 (`!l:(B#A)list x d. MEM (HREV_ASSOCD x l d,x) l \/ HREV_ASSOCD x l d = d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HREV_ASSOCD; MEM] THEN
  SPEC_TAC(`h:B#A`,`p:B#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[HREV_ASSOCD; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* First-match lookup, as finite maps built from association lists.          *)

let hlookup = define
 `(hlookup [] (k:A) = (NONE:B option)) /\
  (hlookup (CONS (k',v) t) k = if k' = k then SOME v else hlookup t k)`;;

(* ------------------------------------------------------------------------- *)
(* List union without duplicates, as LIST_INSERT and LIST_UNION.             *)
(* ------------------------------------------------------------------------- *)

let HLIST_INSERT = new_definition
 `HLIST_INSERT (x:A) xs = if MEM x xs then xs else CONS x xs`;;

let HLIST_UNION = new_definition
 `HLIST_UNION (xs:A list) ys = ITLIST HLIST_INSERT xs ys`;;

let MEM_HLIST_UNION = prove
 (`!xs ys (x:A). MEM x (HLIST_UNION xs ys) <=> MEM x xs \/ MEM x ys`,
  REWRITE_TAC[HLIST_UNION] THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; MEM; HLIST_INSERT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Types.                                                                    *)
(* ------------------------------------------------------------------------- *)

let holtype_INDUCT,holtype_RECURSION = define_type
  "holtype = TyVar string | TyApp string (holtype list)";;

let holtype_DISTINCT = distinctness "holtype";;

let holtype_INJ = injectivity "holtype";;

let HOLTYPE_INDUCT = prove
 (`!P. (!v. P (TyVar v)) /\ (!s tys. ALL P tys ==> P (TyApp s tys))
       ==> !ty. P ty`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`P:holtype->bool`; `ALL (P:holtype->bool)`] holtype_INDUCT) THEN
  ASM_SIMP_TAC[ALL]);;

let HFun = new_definition
 `HFun s t = TyApp "fun" [s;t]`;;

let HBool = new_definition
 `HBool = TyApp "bool" []`;;

let HFUN_INJ = prove
 (`!s t s' t'. HFun s t = HFun s' t' <=> s = s' /\ t = t'`,
  REWRITE_TAC[HFun; holtype_INJ; CONS_11]);;

let HFUN_NOT_BOOL = prove
 (`!s t. ~(HFun s t = HBool) /\ ~(HBool = HFun s t)`,
  REWRITE_TAC[HFun; HBool; holtype_INJ; NOT_CONS_NIL]);;

let hdomain = define
 `(hdomain (TyVar v) = TyVar v) /\
  (hdomain (TyApp n []) = TyApp n []) /\
  (hdomain (TyApp n (CONS x xs)) = x)`;;

let hcodomain = define
 `(hcodomain (TyVar v) = TyVar v) /\
  (hcodomain (TyApp n []) = TyApp n []) /\
  (hcodomain (TyApp n [y]) = TyApp n [y]) /\
  (hcodomain (TyApp n (CONS y (CONS x xs))) = x)`;;

let HDOMAIN_HFUN = prove
 (`!s t. hdomain (HFun s t) = s`,
  REWRITE_TAC[HFun; hdomain]);;

let HCODOMAIN_HFUN = prove
 (`!s t. hcodomain (HFun s t) = t`,
  REWRITE_TAC[HFun; hcodomain]);;

(* ------------------------------------------------------------------------- *)
(* Terms. An abstraction binds a term, which is well-formed only when it is  *)
(* a variable.                                                               *)
(* ------------------------------------------------------------------------- *)

let holterm_INDUCT,holterm_RECURSION = define_type
  "holterm = TmVar string holtype
           | TmConst string holtype
           | TmComb holterm holterm
           | TmAbs holterm holterm";;

let holterm_DISTINCT = distinctness "holterm";;

let holterm_INJ = injectivity "holterm";;

let HEqual = new_definition
 `HEqual ty = TmConst "=" (HFun ty (HFun ty HBool))`;;

let hdest_var = define
 `hdest_var (TmVar x ty) = (x,ty)`;;

(* ------------------------------------------------------------------------- *)
(* Typing.                                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("hhas_type",(12,"right"));;

let hhas_type_RULES,hhas_type_INDUCT,hhas_type_CASES = new_inductive_definition
 `(!n ty. (TmVar n ty) hhas_type ty) /\
  (!n ty. (TmConst n ty) hhas_type ty) /\
  (!s t dty rty. s hhas_type (HFun dty rty) /\ t hhas_type dty
                 ==> (TmComb s t) hhas_type rty) /\
  (!n dty t rty. t hhas_type rty
                 ==> (TmAbs (TmVar n dty) t) hhas_type (HFun dty rty))`;;

let hwelltyped = new_definition
 `hwelltyped tm <=> ?ty. tm hhas_type ty`;;

let htypeof = define
 `(htypeof (TmVar n ty) = ty) /\
  (htypeof (TmConst n ty) = ty) /\
  (htypeof (TmComb s t) = hcodomain (htypeof s)) /\
  (htypeof (TmAbs v t) = HFun (htypeof v) (htypeof t))`;;

let HWELLTYPED_LEMMA = prove
 (`!tm ty. tm hhas_type ty ==> htypeof tm = ty`,
  MATCH_MP_TAC hhas_type_INDUCT THEN
  SIMP_TAC[htypeof; HCODOMAIN_HFUN]);;

let HWELLTYPED = prove
 (`!tm. hwelltyped tm <=> tm hhas_type (htypeof tm)`,
  REWRITE_TAC[hwelltyped] THEN MESON_TAC[HWELLTYPED_LEMMA]);;

let HHAS_TYPE_FUNCTIONAL = prove
 (`!tm ty1 ty2. tm hhas_type ty1 /\ tm hhas_type ty2 ==> ty1 = ty2`,
  MESON_TAC[HWELLTYPED_LEMMA]);;

let HHAS_TYPE_CLAUSES = prove
 (`(!n ty rty. TmVar n ty hhas_type rty <=> rty = ty) /\
   (!n ty rty. TmConst n ty hhas_type rty <=> rty = ty) /\
   (!s t rty. TmComb s t hhas_type rty <=>
              ?dty. s hhas_type (HFun dty rty) /\ t hhas_type dty) /\
   (!v t ty. TmAbs v t hhas_type ty <=>
             ?n dty rty. v = TmVar n dty /\ ty = HFun dty rty /\
                         t hhas_type rty)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [hhas_type_CASES] THEN
  REWRITE_TAC[holterm_INJ; holterm_DISTINCT] THEN MESON_TAC[]);;

let HWELLTYPED_CLAUSES = prove
 (`(!n ty. hwelltyped(TmVar n ty)) /\
   (!n ty. hwelltyped(TmConst n ty)) /\
   (!s t. hwelltyped (TmComb s t) <=>
            hwelltyped s /\ hwelltyped t /\
            ?rty. htypeof s = HFun (htypeof t) rty) /\
   (!v t. hwelltyped (TmAbs v t) <=>
            ?n ty. v = TmVar n ty /\ hwelltyped t)`,
  REWRITE_TAC[hwelltyped; HHAS_TYPE_CLAUSES] THEN REPEAT STRIP_TAC THENL
   [MESON_TAC[]; MESON_TAC[];
    MESON_TAC[HWELLTYPED; HWELLTYPED_LEMMA; hwelltyped];
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Equations.                                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("=:=",(18,"right"));;

let hequation = new_definition
 `(s =:= t) = TmComb (TmComb (HEqual(htypeof s)) s) t`;;

let HEQUATION_HAS_TYPE_BOOL = prove
 (`!s t. (s =:= t) hhas_type HBool
         <=> hwelltyped s /\ hwelltyped t /\ htypeof s = htypeof t`,
  REWRITE_TAC[hequation; HEqual; HHAS_TYPE_CLAUSES; HFUN_INJ] THEN
  MESON_TAC[HWELLTYPED; HWELLTYPED_LEMMA; hwelltyped]);;

let HWELLTYPED_EQUATION = prove
 (`!s t. hwelltyped (s =:= t) <=> (s =:= t) hhas_type HBool`,
  REWRITE_TAC[HEQUATION_HAS_TYPE_BOOL] THEN
  REWRITE_TAC[hequation; HEqual; HWELLTYPED_CLAUSES; htypeof;
              HCODOMAIN_HFUN; HFUN_INJ] THEN
  MESON_TAC[]);;

let HTYPEOF_EQUATION = prove
 (`!s t. htypeof (s =:= t) = HBool`,
  REWRITE_TAC[hequation; HEqual; htypeof; HCODOMAIN_HFUN]);;

let HEQUATION_INJ = prove
 (`!s t s' t'. (s =:= t) = (s' =:= t') <=> s = s' /\ t = t'`,
  REWRITE_TAC[hequation; holterm_INJ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Alpha-equivalence, relative to a list of pairs of bound variables.        *)
(* ------------------------------------------------------------------------- *)

let HALPHAVARS = define
 `(HALPHAVARS [] (tmp:holterm#holterm) <=> FST tmp = SND tmp) /\
  (HALPHAVARS (CONS tp oenv) tmp <=>
        tmp = tp \/
        ~(FST tp = FST tmp) /\ ~(SND tp = SND tmp) /\ HALPHAVARS oenv tmp)`;;

let HRACONV_RULES,HRACONV_INDUCT,HRACONV_CASES = new_inductive_definition
 `(!env x1 ty1 x2 ty2.
       HALPHAVARS env (TmVar x1 ty1,TmVar x2 ty2)
       ==> HRACONV env (TmVar x1 ty1,TmVar x2 ty2)) /\
  (!env x ty. HRACONV env (TmConst x ty,TmConst x ty)) /\
  (!env s1 t1 s2 t2.
       HRACONV env (s1,s2) /\ HRACONV env (t1,t2)
       ==> HRACONV env (TmComb s1 t1,TmComb s2 t2)) /\
  (!env v1 t1 v2 t2.
       htypeof v1 = htypeof v2 /\ HRACONV (CONS (v1,v2) env) (t1,t2)
       ==> HRACONV env (TmAbs v1 t1,TmAbs v2 t2))`;;

let HACONV = new_definition
 `HACONV t1 t2 <=> HRACONV [] (t1,t2)`;;

let HRACONV = prove
 (`(HRACONV env (TmVar x1 ty1,TmVar x2 ty2) <=>
        HALPHAVARS env (TmVar x1 ty1,TmVar x2 ty2)) /\
   (HRACONV env (TmVar x1 ty1,TmConst x2 ty2) <=> F) /\
   (HRACONV env (TmVar x1 ty1,TmComb l2 r2) <=> F) /\
   (HRACONV env (TmVar x1 ty1,TmAbs v2 t2) <=> F) /\
   (HRACONV env (TmConst x1 ty1,TmVar x2 ty2) <=> F) /\
   (HRACONV env (TmConst x1 ty1,TmConst x2 ty2) <=> x1 = x2 /\ ty1 = ty2) /\
   (HRACONV env (TmConst x1 ty1,TmComb l2 r2) <=> F) /\
   (HRACONV env (TmConst x1 ty1,TmAbs v2 t2) <=> F) /\
   (HRACONV env (TmComb l1 r1,TmVar x2 ty2) <=> F) /\
   (HRACONV env (TmComb l1 r1,TmConst x2 ty2) <=> F) /\
   (HRACONV env (TmComb l1 r1,TmComb l2 r2) <=>
        HRACONV env (l1,l2) /\ HRACONV env (r1,r2)) /\
   (HRACONV env (TmComb l1 r1,TmAbs v2 t2) <=> F) /\
   (HRACONV env (TmAbs v1 t1,TmVar x2 ty2) <=> F) /\
   (HRACONV env (TmAbs v1 t1,TmConst x2 ty2) <=> F) /\
   (HRACONV env (TmAbs v1 t1,TmComb l2 r2) <=> F) /\
   (HRACONV env (TmAbs v1 t1,TmAbs v2 t2) <=>
        htypeof v1 = htypeof v2 /\ HRACONV (CONS (v1,v2) env) (t1,t2))`,
  REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [HRACONV_CASES] THEN
  REWRITE_TAC[holterm_INJ; holterm_DISTINCT; PAIR_EQ] THEN MESON_TAC[]);;

let HALPHAVARS_MEM = prove
 (`!env tp. HALPHAVARS env tp ==> MEM tp env \/ FST tp = SND tp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HALPHAVARS; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tp:holterm#holterm`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let HALPHAVARS_REFL = prove
 (`!env t. ALL (\(s,t). s = t) env ==> HALPHAVARS env (t,t)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; HALPHAVARS] THEN
  SPEC_TAC(`h:holterm#holterm`,`p:holterm#holterm`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[PAIR_EQ]);;

let HRACONV_REFL = prove
 (`!t env. ALL (\(s,t). s = t) env ==> HRACONV env (t,t)`,
  MATCH_MP_TAC holterm_INDUCT THEN
  REWRITE_TAC[HRACONV] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[HALPHAVARS_REFL];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[]]);;

let HACONV_REFL = prove
 (`!t. HACONV t t`,
  REWRITE_TAC[HACONV] THEN SIMP_TAC[HRACONV_REFL; ALL]);;

let HALPHAVARS_SYM = prove
 (`!env a b. HALPHAVARS env (a,b)
             ==> HALPHAVARS (MAP (\(x,y). (y,x)) env) (b,a)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HALPHAVARS; MAP] THEN
  SPEC_TAC(`h:holterm#holterm`,`p:holterm#holterm`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ; HALPHAVARS] THEN ASM_MESON_TAC[]);;

let HRACONV_SYM = prove
 (`!env tp. HRACONV env tp
            ==> HRACONV (MAP (\(x,y). (y,x)) env) (SND tp,FST tp)`,
  MATCH_MP_TAC HRACONV_INDUCT THEN REWRITE_TAC[HRACONV; MAP] THEN
  SIMP_TAC[HALPHAVARS_SYM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC[]);;

let HACONV_SYM = prove
 (`!t1 t2. HACONV t1 t2 ==> HACONV t2 t1`,
  REWRITE_TAC[HACONV] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HRACONV_SYM) THEN REWRITE_TAC[MAP]);;

let HALPHAVARS_TRANS = prove
 (`!env vs a b c.
        LENGTH vs = LENGTH env /\
        HALPHAVARS env (a,b) /\
        HALPHAVARS (ZIP (MAP SND env) vs) (b,c)
        ==> HALPHAVARS (ZIP (MAP FST env) vs) (a,c)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; ZIP_DEF; HALPHAVARS] THEN MESON_TAC[];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  SPEC_TAC(`h:holterm#holterm`,`p:holterm#holterm`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; MAP; ZIP; HALPHAVARS; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':holterm list`;`a:holterm`;`b:holterm`;`c:holterm`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let HRACONV_TRANS = prove
 (`!env tp. HRACONV env tp
            ==> !vs t. LENGTH vs = LENGTH env /\
                       HRACONV (ZIP (MAP SND env) vs) (SND tp,t)
                       ==> HRACONV (ZIP (MAP FST env) vs) (FST tp,t)`,
  MATCH_MP_TAC HRACONV_INDUCT THEN REWRITE_TAC[FST; SND] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_TAC THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(SPEC `t:holterm` (cases "holterm")) THEN
    REWRITE_TAC[HRACONV] THEN STRIP_TAC THEN
    MATCH_MP_TAC HALPHAVARS_TRANS THEN
    EXISTS_TAC `TmVar x2 ty2` THEN ASM_REWRITE_TAC[];
    STRUCT_CASES_TAC(SPEC `t:holterm` (cases "holterm")) THEN
    REWRITE_TAC[HRACONV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(SPEC `t:holterm` (cases "holterm")) THEN
    REWRITE_TAC[HRACONV] THEN STRIP_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(SPEC `t:holterm` (cases "holterm")) THEN
    REWRITE_TAC[HRACONV] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (a0:holterm) vs`; `a1:holterm`]) THEN
    ASM_REWRITE_TAC[LENGTH; MAP; ZIP]]);;
let HACONV_TRANS = prove
 (`!t1 t2 t3. HACONV t1 t2 /\ HACONV t2 t3 ==> HACONV t1 t3`,
  REWRITE_TAC[HACONV] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`[]:(holterm#holterm)list`; `(t1:holterm,t2:holterm)`]
               HRACONV_TRANS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`[]:holterm list`; `t3:holterm`]) THEN
  ASM_REWRITE_TAC[LENGTH; MAP; ZIP]);;

let HRACONV_TYPE = prove
 (`!env p. HRACONV env p
           ==> ALL (\(x,y). htypeof x = htypeof y) env
               ==> htypeof (FST p) = htypeof (SND p)`,
  MATCH_MP_TAC HRACONV_INDUCT THEN REWRITE_TAC[htypeof; FST; SND] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP HALPHAVARS_MEM) THENL
     [UNDISCH_TAC `ALL (\(x,y). htypeof x = htypeof y) env` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN
      DISCH_THEN(MP_TAC o SPEC `(TmVar x1 ty1,TmVar x2 ty2)`) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[htypeof];
      FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
      REWRITE_TAC[FST; SND; holterm_INJ] THEN SIMP_TAC[]];
    AP_TERM_TAC THEN ASM_MESON_TAC[];
    BINOP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ALL] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[]]);;
let HACONV_TYPE = prove
 (`!s t. HACONV s t ==> htypeof s = htypeof t`,
  REWRITE_TAC[HACONV] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HRACONV_TYPE) THEN REWRITE_TAC[ALL]);;

(* ------------------------------------------------------------------------- *)
(* Free variables (and constants).                                           *)
(* ------------------------------------------------------------------------- *)

let HVFREE_IN = define
 `(HVFREE_IN v (TmVar x ty) <=> TmVar x ty = v) /\
  (HVFREE_IN v (TmConst x ty) <=> TmConst x ty = v) /\
  (HVFREE_IN v (TmComb s t) <=> HVFREE_IN v s \/ HVFREE_IN v t) /\
  (HVFREE_IN v (TmAbs w t) <=> ~(w = v) /\ HVFREE_IN v t)`;;

let HCLOSED = new_definition
 `HCLOSED tm <=> !x ty. ~(HVFREE_IN (TmVar x ty) tm)`;;

let HVFREE_IN_RACONV = prove
 (`!env p. HRACONV env p
           ==> !x ty. HVFREE_IN (TmVar x ty) (FST p) /\
                      ~(?y. MEM (TmVar x ty,y) env) <=>
                      HVFREE_IN (TmVar x ty) (SND p) /\
                      ~(?y. MEM (y,TmVar x ty) env)`,
  MATCH_MP_TAC HRACONV_INDUCT THEN REWRITE_TAC[HVFREE_IN; holterm_DISTINCT] THEN
  REWRITE_TAC[PAIR_EQ; holterm_INJ; MEM] THEN CONJ_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[HALPHAVARS] THEN
  REWRITE_TAC[MEM; FORALL_PAIR_THM; holterm_INJ; PAIR_EQ] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MESON_TAC[]);;

let HVFREE_IN_ACONV = prove
 (`!s t x ty. HACONV s t
              ==> (HVFREE_IN (TmVar x ty) s <=> HVFREE_IN (TmVar x ty) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HACONV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HVFREE_IN_RACONV) THEN
  SIMP_TAC[MEM; FST; SND]);;

(* ------------------------------------------------------------------------- *)
(* Variants: append primes to the name until it is not free, as fusion.ml.   *)
(* ------------------------------------------------------------------------- *)

let HVFREE_IN_FINITE = prove
 (`!t. FINITE {x | HVFREE_IN x t}`,
  MATCH_MP_TAC holterm_INDUCT THEN REWRITE_TAC[HVFREE_IN] THEN
  REWRITE_TAC[SET_RULE `{x:holterm | a = x} = {a}`;
              SET_RULE `{x:holterm | P x \/ Q x} = {x | P x} UNION {x | Q x}`;
              SET_RULE `{x:holterm | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  SIMP_TAC[FINITE_INSERT; FINITE_RULES; FINITE_UNION; FINITE_INTER]);;

let HVFREE_IN_FINITE_ALT = prove
 (`!t ty. FINITE {x | HVFREE_IN (TmVar x ty) t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\v. FST(hdest_var v)) {x | HVFREE_IN x t}` THEN
  SIMP_TAC[HVFREE_IN_FINITE; FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:string` THEN DISCH_TAC THEN
  EXISTS_TAC `TmVar x ty` THEN ASM_REWRITE_TAC[hdest_var]);;

let HVARIANT_EXISTS = prove
 (`!t x ty. ?n. ~HVFREE_IN (TmVar (APPEND x (REPLICATE n (HD "'"))) ty) t`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`LENGTH:string->num`; `{x | HVFREE_IN (TmVar x ty) t}`]
                FINITE_IMAGE) THEN
  REWRITE_TAC[HVFREE_IN_FINITE_ALT; num_FINITE; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN EXISTS_TAC `SUC a` THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    SPEC `LENGTH(APPEND x (REPLICATE (SUC a) (HD "'")))`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [EXISTS_TAC `APPEND x (REPLICATE (SUC a) (HD "'"))` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LENGTH_APPEND; LENGTH_REPLICATE] THEN ARITH_TAC]);;

let HVARIANT_PRIMES = new_definition
 `HVARIANT_PRIMES t x ty =
    minimal n. ~HVFREE_IN (TmVar (APPEND x (REPLICATE n (HD "'"))) ty) t`;;

let HVARIANT = new_definition
 `HVARIANT t x ty = APPEND x (REPLICATE (HVARIANT_PRIMES t x ty) (HD "'"))`;;

let HVARIANT_PRIMES_THM = prove
 (`!t x ty.
        ~HVFREE_IN (TmVar (APPEND x (REPLICATE (HVARIANT_PRIMES t x ty)
                                               (HD "'"))) ty) t /\
        !m. m < HVARIANT_PRIMES t x ty
            ==> HVFREE_IN (TmVar (APPEND x (REPLICATE m (HD "'"))) ty) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HVARIANT_PRIMES] THEN
  MP_TAC(SPECL [`t:holterm`; `x:string`; `ty:holtype`] HVARIANT_EXISTS) THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN MESON_TAC[]);;

let HVARIANT_THM = prove
 (`!t x ty. ~HVFREE_IN (TmVar (HVARIANT t x ty) ty) t`,
  REWRITE_TAC[HVARIANT; HVARIANT_PRIMES_THM]);;

(* ------------------------------------------------------------------------- *)
(* Union of hypothesis lists, deduplicating up to alpha-equivalence.         *)
(* ------------------------------------------------------------------------- *)

let HTERM_UNION = define
 `(HTERM_UNION [] l2 = l2) /\
  (HTERM_UNION (CONS h t) l2 =
        let subun = HTERM_UNION t l2 in
        if EX (HACONV h) subun then subun else CONS h subun)`;;

let HTERM_UNION_NONEW = prove
 (`!l1 l2 x. MEM x (HTERM_UNION l1 l2) ==> MEM x l1 \/ MEM x l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HTERM_UNION; MEM] THEN
  LET_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let HTERM_UNION_THM = prove
 (`!l1 l2 x. MEM x l1 \/ MEM x l2
             ==> ?y. MEM y (HTERM_UNION l1 l2) /\ HACONV x y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HTERM_UNION; MEM; GSYM EX_MEM] THENL
   [MESON_TAC[HACONV_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN LET_TAC THEN COND_CASES_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[HACONV_REFL]);;

let HTERM_UNION_SUBSUMED = prove
 (`!l1 l2. (!x. MEM x l1 ==> ?y. MEM y l2 /\ HACONV x y)
           ==> HTERM_UNION l1 l2 = l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HTERM_UNION; MEM] THEN
  REPEAT STRIP_TAC THEN LET_TAC THEN
  SUBGOAL_THEN `subun:holterm list = l2` SUBST1_TAC THENL
   [EXPAND_TAC "subun" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM EX_MEM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Type substitution. The recursion through the argument list is defined by  *)
(* an auxiliary function on lists of types.                                  *)
(* ------------------------------------------------------------------------- *)

let HTYPE_SUBST_DEF = new_recursive_definition holtype_RECURSION
 `(HTYPE_SUBST i (TyVar v) = HREV_ASSOCD (TyVar v) i (TyVar v)) /\
  (HTYPE_SUBST i (TyApp s tys) = TyApp s (HTYPE_SUBST_LIST i tys)) /\
  (HTYPE_SUBST_LIST i [] = []) /\
  (HTYPE_SUBST_LIST i (CONS ty tys) =
     CONS (HTYPE_SUBST i ty) (HTYPE_SUBST_LIST i tys))`;;

let HTYPE_SUBST_LIST = prove
 (`!i tys. HTYPE_SUBST_LIST i tys = MAP (HTYPE_SUBST i) tys`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[HTYPE_SUBST_DEF; MAP]);;

let HTYPE_SUBST = prove
 (`(!i v. HTYPE_SUBST i (TyVar v) = HREV_ASSOCD (TyVar v) i (TyVar v)) /\
   (!i s tys. HTYPE_SUBST i (TyApp s tys) = TyApp s (MAP (HTYPE_SUBST i) tys))`,
  REWRITE_TAC[HTYPE_SUBST_DEF; HTYPE_SUBST_LIST]);;

let HTYPE_SUBST_HFUN = prove
 (`!i s t. HTYPE_SUBST i (HFun s t) = HFun (HTYPE_SUBST i s) (HTYPE_SUBST i t)`,
  REWRITE_TAC[HFun; HTYPE_SUBST; MAP]);;

let HTYPE_SUBST_HBOOL = prove
 (`!i. HTYPE_SUBST i HBool = HBool`,
  REWRITE_TAC[HBool; HTYPE_SUBST; MAP]);;

let HTYPE_SUBST_NIL = prove
 (`!ty. HTYPE_SUBST [] ty = ty`,
  MATCH_MP_TAC HOLTYPE_INDUCT THEN REWRITE_TAC[HTYPE_SUBST; HREV_ASSOCD] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`tys:holtype list`,`l:holtype list`) THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; ALL]);;

(* ------------------------------------------------------------------------- *)
(* Term substitution, renaming a bound variable when it would capture.       *)
(* ------------------------------------------------------------------------- *)

let HVSUBST = define
 `(HVSUBST ilist (TmVar x ty) = HREV_ASSOCD (TmVar x ty) ilist (TmVar x ty)) /\
  (HVSUBST ilist (TmConst x ty) = TmConst x ty) /\
  (HVSUBST ilist (TmComb s t) = TmComb (HVSUBST ilist s) (HVSUBST ilist t)) /\
  (HVSUBST ilist (TmAbs v t) =
        let ilist' = FILTER (\(s',s). ~(s = v)) ilist in
        let t' = HVSUBST ilist' t in
        if EX (\(s',s). HVFREE_IN v s' /\ HVFREE_IN s t) ilist'
        then let z = TmVar (HVARIANT t' (FST(hdest_var v)) (SND(hdest_var v)))
                           (SND(hdest_var v)) in
             let ilist'' = CONS (z,v) ilist' in
             TmAbs z (HVSUBST ilist'' t)
        else TmAbs v t')`;;

let hsizeof = define
 `(hsizeof (TmVar x ty) = 1) /\
  (hsizeof (TmConst x ty) = 1) /\
  (hsizeof (TmComb s t) = 1 + hsizeof s + hsizeof t) /\
  (hsizeof (TmAbs v t) = 2 + hsizeof t)`;;

(* ------------------------------------------------------------------------- *)
(* Induction over well-typed terms, and properties of substitution.          *)
(* ------------------------------------------------------------------------- *)

let HWELLTYPED_INDUCT = prove
 (`!P. (!x ty. P (TmVar x ty)) /\
       (!x ty. P (TmConst x ty)) /\
       (!s t. hwelltyped s /\ hwelltyped t /\
              (?rty. htypeof s = HFun (htypeof t) rty) /\ P s /\ P t
              ==> P (TmComb s t)) /\
       (!x ty t. hwelltyped t /\ P t ==> P (TmAbs (TmVar x ty) t))
       ==> !tm. hwelltyped tm ==> P tm`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC holterm_INDUCT THEN
  ASM_REWRITE_TAC[HWELLTYPED_CLAUSES] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[]);;

let HHAS_TYPE_VAR = el 0 (CONJUNCTS hhas_type_RULES);;
let HHAS_TYPE_CONST = el 1 (CONJUNCTS hhas_type_RULES);;
let HHAS_TYPE_COMB = el 2 (CONJUNCTS hhas_type_RULES);;
let HHAS_TYPE_ABS = el 3 (CONJUNCTS hhas_type_RULES);;

let HVSUBST_HAS_TYPE = prove
 (`!tm ty ilist.
        tm hhas_type ty /\
        (!s s'. MEM (s',s) ilist ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty)
        ==> (HVSUBST ilist tm) hhas_type ty`,
  MATCH_MP_TAC holterm_INDUCT THEN REWRITE_TAC[HVSUBST] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:string`; `xty:holtype`; `ty:holtype`;
                         `ilist:(holterm#holterm)list`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`ilist:(holterm#holterm)list`; `TmVar x xty`;
                   `TmVar x xty`] HREV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    DISCH_THEN(MP_TAC o SPECL [`TmVar x xty`;
      `HREV_ASSOCD (TmVar x xty) ilist (TmVar x xty)`]) THEN
    ASM_REWRITE_TAC[holterm_INJ] THEN
    UNDISCH_TAC `TmVar x xty hhas_type ty` THEN
    REWRITE_TAC[HHAS_TYPE_CLAUSES] THEN MESON_TAC[];
    SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:holterm`; `t:holterm`] THEN STRIP_TAC THEN
    REWRITE_TAC[HHAS_TYPE_CLAUSES] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:holterm`; `t:holterm`] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MAP_EVERY X_GEN_TAC [`fty:holtype`; `ilist:(holterm#holterm)list`] THEN
  REWRITE_TAC[HHAS_TYPE_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:string` (X_CHOOSE_THEN
    `dty:holtype` (X_CHOOSE_THEN `rty:holtype` STRIP_ASSUME_TAC)))
    ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[hdest_var; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN MATCH_MP_TAC HHAS_TYPE_ABS THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MEM; MEM_FILTER; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_MESON_TAC[hhas_type_RULES]);;

let HVSUBST_WELLTYPED = prove
 (`!tm ilist.
        hwelltyped tm /\
        (!s s'. MEM (s',s) ilist ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty)
        ==> hwelltyped (HVSUBST ilist tm)`,
  MESON_TAC[HVSUBST_HAS_TYPE; hwelltyped]);;

let HVSUBST_NIL = prove
 (`!tm. HVSUBST [] tm = tm`,
  MATCH_MP_TAC holterm_INDUCT THEN
  ASM_SIMP_TAC[HVSUBST; HREV_ASSOCD; FILTER; EX; LET_DEF; LET_END_DEF]);;

let HSIZEOF_VSUBST = prove
 (`!t ilist. (!s' s. MEM (s',s) ilist ==> ?x ty. s' = TmVar x ty)
             ==> hsizeof (HVSUBST ilist t) = hsizeof t`,
  MATCH_MP_TAC holterm_INDUCT THEN REWRITE_TAC[HVSUBST; hsizeof] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:string`; `ty:holtype`] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[HREV_ASSOCD; hsizeof] THEN
    SPEC_TAC(`h:holterm#holterm`,`p:holterm#holterm`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; MEM; PAIR_EQ; HREV_ASSOCD] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[hsizeof];
    ALL_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:holterm`; `t:holterm`] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  X_GEN_TAC `ilist:(holterm#holterm)list` THEN DISCH_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[hsizeof; EQ_ADD_LCANCEL] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[MEM; MEM_FILTER; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[]);;

let HVFREE_IN_COND = prove
 (`!v b s t. HVFREE_IN v (if b then s else t) <=>
             (if b then HVFREE_IN v s else HVFREE_IN v t)`,
  MESON_TAC[]);;

let HVFREE_IN_VSUBST = prove
 (`!tm. hwelltyped tm
        ==> !u uty ilist.
              HVFREE_IN (TmVar u uty) (HVSUBST ilist tm) <=>
              ?y ty. HVFREE_IN (TmVar y ty) tm /\
                     HVFREE_IN (TmVar u uty)
                               (HREV_ASSOCD (TmVar y ty) ilist (TmVar y ty))`,
  MATCH_MP_TAC HWELLTYPED_INDUCT THEN
  REWRITE_TAC[HVFREE_IN; HVSUBST; holterm_DISTINCT] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[holterm_INJ];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:string`; `ty:holtype`; `t:holterm`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC
   [`u:string`; `uty:holtype`; `ilist:(holterm#holterm)list`] THEN
  REWRITE_TAC[hdest_var; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `ilist' = FILTER (\(s',s). ~(s = TmVar x ty))
                              (ilist:(holterm#holterm)list)` THEN
  SUBGOAL_THEN
   `!y yty. HREV_ASSOCD (TmVar y yty) ilist' (TmVar y yty) =
            if TmVar y yty = TmVar x ty then TmVar y yty
            else HREV_ASSOCD (TmVar y yty) ilist (TmVar y yty)`
  ASSUME_TAC THENL
   [EXPAND_TAC "ilist'" THEN REWRITE_TAC[HREV_ASSOCD_FILTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[HVFREE_IN; HREV_ASSOCD] THENL
   [MP_TAC(ISPECL [`HVSUBST ilist' t`; `x:string`; `ty:holtype`]
                  HVARIANT_THM) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[HVFREE_IN_COND; HVFREE_IN] THEN
    REWRITE_TAC[COND_EXPAND; holterm_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  EXPAND_TAC "ilist'" THEN
  REWRITE_TAC[NOT_EX; GSYM ALL_MEM; MEM_FILTER; FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN DISCH_TAC THEN
  REWRITE_TAC[HVFREE_IN_COND; HVFREE_IN] THEN REWRITE_TAC[COND_EXPAND] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:string`
   (X_CHOOSE_THEN `yty:holtype` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`ilist:(holterm#holterm)list`; `TmVar y yty`; `TmVar y yty`]
                HREV_ASSOCD_MEM) THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[];
    UNDISCH_TAC `HVFREE_IN (TmVar u uty)
                  (HREV_ASSOCD (TmVar y yty) ilist (TmVar y yty))` THEN
    ASM_REWRITE_TAC[HVFREE_IN] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Results of type instantiation: a clash or a term.                        *)
(* ------------------------------------------------------------------------- *)

let hresult_INDUCT,hresult_RECURSION = define_type
 "hresult = HClash holterm | HResult holterm";;

let hresult_INJ = injectivity "hresult";;

let hresult_DISTINCT = distinctness "hresult";;

let HIS_RESULT = define
 `(HIS_RESULT(HClash t) = F) /\
  (HIS_RESULT(HResult t) = T)`;;

let HIS_CLASH = define
 `(HIS_CLASH(HClash t) = T) /\
  (HIS_CLASH(HResult t) = F)`;;

let HRESULT = define
 `HRESULT(HResult t) = t`;;

let HCLASH = define
 `HCLASH(HClash t) = t`;;

(* ------------------------------------------------------------------------- *)
(* Type instantiation in terms. A clash reports a free variable that would   *)
(* be captured; the abstraction case then renames its bound variable.        *)
(* ------------------------------------------------------------------------- *)

let HINST_CORE_EXISTS = prove
 (`?HINST_CORE.
  (!env tyin x ty.
        HINST_CORE env tyin (TmVar x ty) =
          let tm = TmVar x ty in
          let tm' = TmVar x (HTYPE_SUBST tyin ty) in
          if HREV_ASSOCD tm' env tm = tm then HResult tm' else HClash tm') /\
  (!env tyin x ty.
        HINST_CORE env tyin (TmConst x ty) =
          HResult(TmConst x (HTYPE_SUBST tyin ty))) /\
  (!env tyin s t.
        HINST_CORE env tyin (TmComb s t) =
            let sres = HINST_CORE env tyin s in
            if HIS_CLASH sres then sres else
            let tres = HINST_CORE env tyin t in
            if HIS_CLASH tres then tres else
            let s' = HRESULT sres and t' = HRESULT tres in
            HResult (TmComb s' t')) /\
  (!env tyin v t.
        HINST_CORE env tyin (TmAbs v t) =
            let x = FST(hdest_var v) and ty = SND(hdest_var v) in
            let ty' = HTYPE_SUBST tyin ty in
            let v' = TmVar x ty' in
            let env' = CONS (v,v') env in
            let tres = HINST_CORE env' tyin t in
            if HIS_RESULT tres then HResult(TmAbs v' (HRESULT tres)) else
            let w = HCLASH tres in
            if ~(w = v') then tres else
            let x' = HVARIANT (HRESULT(HINST_CORE [] tyin t)) x ty' in
            let t' = HVSUBST [TmVar x' ty,TmVar x ty] t in
            let ty'' = HTYPE_SUBST tyin ty in
            let env'' = CONS (TmVar x' ty,TmVar x' ty'') env in
            let tres' = HINST_CORE env'' tyin t' in
            if HIS_RESULT tres'
            then HResult(TmAbs (TmVar x' ty'') (HRESULT tres'))
            else tres')`,
  W(fun (asl,w) -> MATCH_MP_TAC(DISCH_ALL
   (pure_prove_recursive_function_exists w))) THEN
  EXISTS_TAC `MEASURE(\(env:(holterm#holterm)list,tyin:(holtype#holtype)list,t).
                        hsizeof t)` THEN
  REWRITE_TAC[WF_MEASURE; MEASURE_LE; MEASURE] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  SIMP_TAC[MEM; PAIR_EQ; holterm_INJ; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM;
           GSYM EXISTS_REFL; HSIZEOF_VSUBST; LE_REFL; hsizeof] THEN
  REPEAT STRIP_TAC THEN ARITH_TAC);;

let HINST_CORE = new_specification ["HINST_CORE"] HINST_CORE_EXISTS;;

let HINST_DEF = new_definition
 `HINST tyin tm = HRESULT(HINST_CORE [] tyin tm)`;;

(* ------------------------------------------------------------------------- *)
(* Typing and free variables of type instantiation.                          *)
(* ------------------------------------------------------------------------- *)

let HSIZEOF_INDUCT = prove
 (`!P. (!tm. (!tm'. hsizeof tm' < hsizeof tm ==> P tm') ==> P tm)
       ==> !tm. P tm`,
  GEN_TAC THEN MP_TAC(ISPEC `hsizeof` WF_MEASURE) THEN
  REWRITE_TAC[WF_IND; MEASURE] THEN MESON_TAC[]);;

let HINST_CORE_HAS_TYPE = prove
 (`!tm env tyin.
      hwelltyped tm /\
      (!s s'. MEM (s,s') env
              ==> ?x ty. s = TmVar x ty /\ s' = TmVar x (HTYPE_SUBST tyin ty))
      ==> (?x ty. HINST_CORE env tyin tm =
                  HClash(TmVar x (HTYPE_SUBST tyin ty)) /\
                  HVFREE_IN (TmVar x ty) tm /\
                  ~(HREV_ASSOCD (TmVar x (HTYPE_SUBST tyin ty)) env
                                (TmVar x ty) = TmVar x ty)) \/
          (!x ty. HVFREE_IN (TmVar x ty) tm
                  ==> HREV_ASSOCD (TmVar x (HTYPE_SUBST tyin ty)) env
                                  (TmVar x ty) = TmVar x ty) /\
          (?tm'. HINST_CORE env tyin tm = HResult tm' /\
                 tm' hhas_type (HTYPE_SUBST tyin (htypeof tm)) /\
                 (!u uty. HVFREE_IN (TmVar u uty) tm' <=>
                          ?oty. HVFREE_IN (TmVar u oty) tm /\
                                uty = HTYPE_SUBST tyin oty))`,
  MATCH_MP_TAC HSIZEOF_INDUCT THEN GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `tm:holterm` (cases "holterm")) THEN
  DISCH_THEN(LABEL_TAC "ih") THENL
   [MAP_EVERY X_GEN_TAC
     [`env:(holterm#holterm)list`; `tyin:(holtype#holtype)list`] THEN
    STRIP_TAC THEN
    REWRITE_TAC[HINST_CORE; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[hresult_DISTINCT; hresult_INJ; UNWIND_THM1; HVFREE_IN;
                    holterm_INJ; htypeof; HHAS_TYPE_VAR] THENL
     [REPEAT STRIP_TAC THEN ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[HINST_CORE; hresult_DISTINCT; hresult_INJ; UNWIND_THM1;
                HVFREE_IN; holterm_DISTINCT; htypeof; HHAS_TYPE_CONST];
    MAP_EVERY X_GEN_TAC
     [`env:(holterm#holterm)list`; `tyin:(holtype#holtype)list`] THEN
    REWRITE_TAC[HWELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    USE_THEN "ih" (MP_TAC o SPEC `a1:holterm`) THEN
    USE_THEN "ih" (MP_TAC o SPEC `a0:holterm`) THEN
    REWRITE_TAC[hsizeof; ARITH_RULE `s < 1 + s + t /\ t < 1 + s + t`] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`env:(holterm#holterm)list`; `tyin:(holtype#holtype)list`]) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HINST_CORE; LET_DEF; LET_END_DEF] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:string`
       (X_CHOOSE_THEN `ty:holtype` STRIP_ASSUME_TAC)) THEN
      DISCH_THEN(K ALL_TAC) THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:string`; `ty:holtype`] THEN
      ASM_REWRITE_TAC[HIS_CLASH; HVFREE_IN];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `s':holterm` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`env:(holterm#holterm)list`; `tyin:(holtype#holtype)list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:string`
       (X_CHOOSE_THEN `ty:holtype` STRIP_ASSUME_TAC)) THEN
      DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:string`; `ty:holtype`] THEN
      ASM_REWRITE_TAC[HIS_CLASH; HVFREE_IN];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `t':holterm` STRIP_ASSUME_TAC)) THEN
    DISJ2_TAC THEN
    ASM_REWRITE_TAC[HIS_CLASH; HRESULT; hresult_INJ; UNWIND_THM1; HVFREE_IN] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HHAS_TYPE_COMB THEN
      EXISTS_TAC `HTYPE_SUBST tyin (htypeof a1)` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[HTYPE_SUBST_HFUN]) THEN
      ASM_REWRITE_TAC[htypeof; HCODOMAIN_HFUN];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`env:(holterm#holterm)list`; `tyin:(holtype#holtype)list`] THEN
  REWRITE_TAC[HWELLTYPED_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:string` (X_CHOOSE_THEN
    `ty:holtype` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) ASSUME_TAC) THEN
  USE_THEN "ih" (MP_TAC o SPEC `a1:holterm`) THEN
  REWRITE_TAC[hsizeof; ARITH_RULE `t < 2 + t`] THEN
  DISCH_THEN(LABEL_TAC "iht") THEN
  USE_THEN "iht" (MP_TAC o SPECL
    [`CONS (TmVar x ty,TmVar x (HTYPE_SUBST tyin ty)) env`;
     `tyin:(holtype#holtype)list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[HINST_CORE; hdest_var; FST; SND; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_THEN `x0:string` (X_CHOOSE_THEN `ty0:holtype`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[HIS_RESULT; HRESULT; HCLASH; hresult_DISTINCT;
                    hresult_INJ; UNWIND_THM1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HREV_ASSOCD]) THEN COND_CASES_TAC THENL
     [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`x0:string`; `ty0:holtype`] THEN
      REWRITE_TAC[HVFREE_IN] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ASSUME_TAC o GSYM o check (is_neg o concl)) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[holterm_INJ]; ALL_TAC] THEN
      UNDISCH_TAC
       `~((if TmVar x (HTYPE_SUBST tyin ty) = TmVar x0 (HTYPE_SUBST tyin ty0)
           then TmVar x ty
           else HREV_ASSOCD (TmVar x0 (HTYPE_SUBST tyin ty0)) env
                            (TmVar x0 ty0)) = TmVar x0 ty0)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [holterm_INJ] o
                  check (is_eq o concl)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    USE_THEN "iht" (MP_TAC o SPECL
      [`[]:(holterm#holterm)list`; `tyin:(holtype#holtype)list`]) THEN
    REWRITE_TAC[MEM; HREV_ASSOCD; ASSUME `hwelltyped a1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:holterm` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[HRESULT] THEN
    ABBREV_TAC `z = HVARIANT t0 x (HTYPE_SUBST tyin ty)` THEN
    SUBGOAL_THEN
     `!oty. HVFREE_IN (TmVar z oty) a1
            ==> ~(HTYPE_SUBST tyin oty = HTYPE_SUBST tyin ty)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t0:holterm`; `x:string`; `HTYPE_SUBST tyin ty`]
                    HVARIANT_THM) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `t' = HVSUBST [TmVar z ty,TmVar x ty] a1` THEN
    SUBGOAL_THEN `hsizeof t' = hsizeof a1 /\ hwelltyped t' /\
                  htypeof t' = htypeof a1`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t'" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC HSIZEOF_VSUBST THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
        MESON_TAC[];
        MATCH_MP_TAC HVSUBST_WELLTYPED THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
        MESON_TAC[HHAS_TYPE_VAR];
        MATCH_MP_TAC HWELLTYPED_LEMMA THEN MATCH_MP_TAC HVSUBST_HAS_TYPE THEN
        ASM_REWRITE_TAC[GSYM HWELLTYPED; MEM; PAIR_EQ] THEN
        MESON_TAC[HHAS_TYPE_VAR]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!k kty. HVFREE_IN (TmVar k kty) t' <=>
              HVFREE_IN (TmVar x ty) a1 /\ k = z /\ kty = ty \/
              HVFREE_IN (TmVar k kty) a1 /\ ~(k = x /\ kty = ty)`
    ASSUME_TAC THENL
     [EXPAND_TAC "t'" THEN ASM_SIMP_TAC[HVFREE_IN_VSUBST] THEN
      REWRITE_TAC[HREV_ASSOCD; HVFREE_IN_COND; HVFREE_IN; holterm_INJ] THEN
      REWRITE_TAC[COND_EXPAND] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `hsizeof t' < hsizeof (TmAbs (TmVar x ty) a1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[hsizeof] THEN ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ih" (MP_TAC o SPECL
      [`CONS (TmVar z ty,TmVar z (HTYPE_SUBST tyin ty)) env`;
       `tyin:(holtype#holtype)list`] o
      C MP (ASSUME `hsizeof t' < hsizeof (TmAbs (TmVar x ty) a1)`) o
      SPEC `t':holterm`) THEN
    REWRITE_TAC[ASSUME `hwelltyped t'`] THEN
    ANTS_TAC THENL [REWRITE_TAC[MEM; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[HREV_ASSOCD] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(X_CHOOSE_THEN `x1:string` (X_CHOOSE_THEN `ty1:holtype`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[HIS_RESULT; hresult_DISTINCT; hresult_INJ] THEN
      MAP_EVERY EXISTS_TAC [`x1:string`; `ty1:holtype`] THEN
      REWRITE_TAC[HVFREE_IN] THEN
      UNDISCH_TAC `HVFREE_IN (TmVar x1 ty1) t'` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `~((if TmVar z (HTYPE_SUBST tyin ty) = TmVar x1 (HTYPE_SUBST tyin ty1)
           then TmVar z ty
           else HREV_ASSOCD (TmVar x1 (HTYPE_SUBST tyin ty1)) env
                            (TmVar x1 ty1)) = TmVar x1 ty1)` THEN
      REWRITE_TAC[holterm_INJ] THEN
      ASM_CASES_TAC `z:string = x1` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
        ASM_CASES_TAC `HTYPE_SUBST tyin ty = HTYPE_SUBST tyin ty1` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `t2:holterm` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[HIS_RESULT; HRESULT; hresult_DISTINCT; hresult_INJ;
                    UNWIND_THM1] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[HVFREE_IN; holterm_INJ] THEN
      MAP_EVERY X_GEN_TAC [`y:string`; `yty:holtype`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:string`; `yty:holtype`] o
        check (fun th -> is_forall(concl th) &&
               can (find_term (fun t -> t = `z:string`)) (concl th) &&
               can (find_term (fun t -> t = `env:(holterm#holterm)list`))
                   (concl th))) THEN
      ASM_REWRITE_TAC[holterm_INJ] THEN
      ASM_CASES_TAC `z:string = y` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
      ASM_CASES_TAC `HTYPE_SUBST tyin ty = HTYPE_SUBST tyin yty` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[htypeof; HTYPE_SUBST_HFUN] THEN
      MATCH_MP_TAC HHAS_TYPE_ABS THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[HVFREE_IN; holterm_INJ] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `t1:holterm` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HREV_ASSOCD; holterm_INJ]) THEN
  ASM_REWRITE_TAC[HIS_RESULT; HRESULT; hresult_DISTINCT; hresult_INJ;
                  UNWIND_THM1] THEN
  SUBGOAL_THEN `!y yty. HVFREE_IN (TmVar y yty) a1 /\ x = y /\
                        HTYPE_SUBST tyin ty = HTYPE_SUBST tyin yty ==> ty = yty`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:string`; `yty:holtype`] o
      check (fun th -> is_forall(concl th) &&
             can (find_term (fun t -> t = `env:(holterm#holterm)list`))
                 (concl th) &&
             not (can (find_term (fun t -> t = `hwelltyped a1`)) (concl th)))) THEN
    ASM_REWRITE_TAC[holterm_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[HVFREE_IN; holterm_INJ] THEN
    MAP_EVERY X_GEN_TAC [`y:string`; `yty:holtype`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:string`; `yty:holtype`] o
      check (fun th -> is_forall(concl th) &&
             can (find_term (fun t -> t = `env:(holterm#holterm)list`))
                 (concl th) &&
             not (can (find_term (fun t -> t = `hwelltyped a1`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[htypeof; HTYPE_SUBST_HFUN] THEN MATCH_MP_TAC HHAS_TYPE_ABS THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[HVFREE_IN; holterm_INJ] THEN ASM_MESON_TAC[]]);;

let HINST_CORE_NIL_IS_RESULT = prove
 (`!tyin tm. hwelltyped tm ==> HIS_RESULT (HINST_CORE [] tyin tm)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tm:holterm`; `[]:(holterm#holterm)list`; `tyin:(holtype#holtype)list`]
               HINST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; HREV_ASSOCD] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[HIS_RESULT]);;

let HINST_THM = prove
 (`!tyin tm.
        hwelltyped tm
        ==> HINST_CORE [] tyin tm = HResult (HINST tyin tm) /\
            (HINST tyin tm) hhas_type (HTYPE_SUBST tyin (htypeof tm)) /\
            (!u uty. HVFREE_IN (TmVar u uty) (HINST tyin tm) <=>
                     ?oty. HVFREE_IN (TmVar u oty) tm /\
                           uty = HTYPE_SUBST tyin oty)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tm:holterm`; `[]:(holterm#holterm)list`; `tyin:(holtype#holtype)list`]
               HINST_CORE_HAS_TYPE) THEN
  ASM_REWRITE_TAC[MEM; HREV_ASSOCD; HINST_DEF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[HRESULT]);;

let HINST_HAS_TYPE = prove
 (`!tm ty tyin. tm hhas_type ty ==> (HINST tyin tm) hhas_type (HTYPE_SUBST tyin ty)`,
  MESON_TAC[HINST_THM; hwelltyped; HWELLTYPED_LEMMA]);;

let HINST_WELLTYPED = prove
 (`!tm tyin. hwelltyped tm ==> hwelltyped (HINST tyin tm)`,
  MESON_TAC[HINST_THM; hwelltyped]);;

let HVFREE_IN_INST = prove
 (`!tm tyin u uty.
        hwelltyped tm
        ==> (HVFREE_IN (TmVar u uty) (HINST tyin tm) <=>
             ?oty. HVFREE_IN (TmVar u oty) tm /\ uty = HTYPE_SUBST tyin oty)`,
  MESON_TAC[HINST_THM]);;

(* ------------------------------------------------------------------------- *)
(* Type variables of types and terms.                                        *)
(* ------------------------------------------------------------------------- *)

let HTYVARS_DEF = new_recursive_definition holtype_RECURSION
 `(htyvars (TyVar v) = [v]) /\
  (htyvars (TyApp s tys) = htyvars_list tys) /\
  (htyvars_list [] = []) /\
  (htyvars_list (CONS ty tys) = HLIST_UNION (htyvars ty) (htyvars_list tys))`;;

let HTYVARS = prove
 (`(!v. htyvars (TyVar v) = [v]) /\
   (!s tys. htyvars (TyApp s tys) =
            ITLIST (\x y. HLIST_UNION (htyvars x) y) tys [])`,
  REWRITE_TAC[HTYVARS_DEF] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[HTYVARS_DEF; ITLIST]);;

let htvars = define
 `(htvars (TmVar n ty) = htyvars ty) /\
  (htvars (TmConst n ty) = htyvars ty) /\
  (htvars (TmComb s t) = HLIST_UNION (htvars s) (htvars t)) /\
  (htvars (TmAbs v t) = HLIST_UNION (htvars v) (htvars t))`;;

(* ------------------------------------------------------------------------- *)
(* Signatures: type operators with arities and constants with types, as      *)
(* association lists read by first match. A theory adds a set of axioms.     *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("hsig",`:(string#num)list#(string#holtype)list`);;

new_type_abbrev("hthy",`:hsig#(holterm->bool)`);;

let HTYPE_OK_DEF = new_recursive_definition holtype_RECURSION
 `(htype_ok tysig (TyVar v) <=> T) /\
  (htype_ok tysig (TyApp name args) <=>
     hlookup tysig name = SOME (LENGTH args) /\ htype_ok_list tysig args) /\
  (htype_ok_list tysig [] <=> T) /\
  (htype_ok_list tysig (CONS ty tys) <=>
     htype_ok tysig ty /\ htype_ok_list tysig tys)`;;

let HTYPE_OK = prove
 (`(!tysig v. htype_ok tysig (TyVar v) <=> T) /\
   (!tysig name args.
       htype_ok tysig (TyApp name args) <=>
       hlookup tysig name = SOME (LENGTH args) /\ ALL (htype_ok tysig) args)`,
  REWRITE_TAC[HTYPE_OK_DEF] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC(`args:holtype list`,`l:holtype list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[HTYPE_OK_DEF; ALL]);;

let hterm_ok = new_recursive_definition holterm_RECURSION
 `(hterm_ok (sig:hsig) (TmVar x ty) <=> htype_ok (FST sig) ty) /\
  (hterm_ok sig (TmConst name ty) <=>
     ?ty0. hlookup (SND sig) name = SOME ty0 /\
           htype_ok (FST sig) ty /\
           ?i. ty = HTYPE_SUBST i ty0) /\
  (hterm_ok sig (TmComb tm1 tm2) <=>
     hterm_ok sig tm1 /\ hterm_ok sig tm2 /\ hwelltyped (TmComb tm1 tm2)) /\
  (hterm_ok sig (TmAbs v tm) <=>
     ?x ty. v = TmVar x ty /\ htype_ok (FST sig) ty /\ hterm_ok sig tm)`;;

let his_std_sig = new_definition
 `his_std_sig (sig:hsig) <=>
    hlookup (FST sig) "fun" = SOME 2 /\
    hlookup (FST sig) "bool" = SOME 0 /\
    hlookup (SND sig) "=" = SOME (HFun (TyVar "A") (HFun (TyVar "A") HBool))`;;

let htheory_ok = new_definition
 `htheory_ok (thy:hthy) <=>
    (!name ty. hlookup (SND(FST thy)) name = SOME ty
               ==> htype_ok (FST(FST thy)) ty) /\
    (!p. p IN SND thy ==> hterm_ok (FST thy) p /\ p hhas_type HBool) /\
    his_std_sig (FST thy)`;;

(* ------------------------------------------------------------------------- *)
(* Sequents provable in a theory.                                            *)
(* ------------------------------------------------------------------------- *)

let hproves_RULES,hproves_INDUCT,hproves_CASES = new_inductive_definition
 `(!thy h x ty l r.
      ~(EX (HVFREE_IN (TmVar x ty)) h) /\ htype_ok (FST(FST thy)) ty /\
      hproves thy h (l =:= r)
      ==> hproves thy h (TmAbs (TmVar x ty) l =:= TmAbs (TmVar x ty) r)) /\
  (!thy p.
      htheory_ok thy /\ p hhas_type HBool /\ hterm_ok (FST thy) p
      ==> hproves thy [p] p) /\
  (!thy x ty t.
      htheory_ok thy /\ htype_ok (FST(FST thy)) ty /\ hterm_ok (FST thy) t
      ==> hproves thy [] (TmComb (TmAbs (TmVar x ty) t) (TmVar x ty) =:= t)) /\
  (!thy h1 h2 c1 c2.
      hproves thy h1 c1 /\ hproves thy h2 c2
      ==> hproves thy (HTERM_UNION (FILTER ((~) o HACONV c2) h1)
                                   (FILTER ((~) o HACONV c1) h2))
                      (c1 =:= c2)) /\
  (!thy h1 h2 p q p'.
      hproves thy h1 (p =:= q) /\ hproves thy h2 p' /\ HACONV p p'
      ==> hproves thy (HTERM_UNION h1 h2) q) /\
  (!thy ilist h c.
      (!s s'. MEM (s',s) ilist
              ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty /\
                         hterm_ok (FST thy) s') /\
      hproves thy h c
      ==> hproves thy (MAP (HVSUBST ilist) h) (HVSUBST ilist c)) /\
  (!thy tyin h c.
      ALL (htype_ok (FST(FST thy))) (MAP FST tyin) /\ hproves thy h c
      ==> hproves thy (MAP (HINST tyin) h) (HINST tyin c)) /\
  (!thy h1 h2 l1 r1 l2 r2.
      hproves thy h1 (l1 =:= r1) /\ hproves thy h2 (l2 =:= r2) /\
      hwelltyped (TmComb l1 l2)
      ==> hproves thy (HTERM_UNION h1 h2) (TmComb l1 l2 =:= TmComb r1 r2)) /\
  (!thy t.
      htheory_ok thy /\ hterm_ok (FST thy) t
      ==> hproves thy [] (t =:= t)) /\
  (!thy c.
      htheory_ok thy /\ c IN SND thy
      ==> hproves thy [] c)`;;

let HPROVES_ABS = el 0 (CONJUNCTS hproves_RULES);;
let HPROVES_ASSUME = el 1 (CONJUNCTS hproves_RULES);;
let HPROVES_BETA = el 2 (CONJUNCTS hproves_RULES);;
let HPROVES_DEDUCT_ANTISYM = el 3 (CONJUNCTS hproves_RULES);;
let HPROVES_EQ_MP = el 4 (CONJUNCTS hproves_RULES);;
let HPROVES_INST = el 5 (CONJUNCTS hproves_RULES);;
let HPROVES_INST_TYPE = el 6 (CONJUNCTS hproves_RULES);;
let HPROVES_MK_COMB = el 7 (CONJUNCTS hproves_RULES);;
let HPROVES_REFL = el 8 (CONJUNCTS hproves_RULES);;
let HPROVES_AXIOM = el 9 (CONJUNCTS hproves_RULES);;

(* ------------------------------------------------------------------------- *)
(* Well-formed types and terms: substitution, instantiation, alpha.          *)
(* ------------------------------------------------------------------------- *)

let HTYPE_SUBST_COMPOSE = prove
 (`!tyin1 ty tyin2.
        HTYPE_SUBST tyin2 (HTYPE_SUBST tyin1 ty) =
        HTYPE_SUBST (APPEND (MAP (\(a,b). (HTYPE_SUBST tyin2 a,b)) tyin1)
                            tyin2) ty`,
  GEN_TAC THEN MATCH_MP_TAC HOLTYPE_INDUCT THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[HTYPE_SUBST] THEN
    SPEC_TAC(`tyin1:(holtype#holtype)list`,`l:(holtype#holtype)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; APPEND; HREV_ASSOCD; HTYPE_SUBST] THEN
    POP_ASSUM MP_TAC THEN SPEC_TAC(`h:holtype#holtype`,`p:holtype#holtype`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[HREV_ASSOCD] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[HTYPE_SUBST; holtype_INJ; GSYM MAP_o] THEN
    MATCH_MP_TAC MAP_EQ THEN POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
    SIMP_TAC[o_THM]]);;

let HTYPE_OK_TYPE_SUBST = prove
 (`!s tyin ty.
        htype_ok s ty /\ ALL (htype_ok s) (MAP FST tyin)
        ==> htype_ok s (HTYPE_SUBST tyin ty)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC HOLTYPE_INDUCT THEN
  REWRITE_TAC[HTYPE_SUBST; HTYPE_OK; LENGTH_MAP; ALL_MAP] THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`tyin:(holtype#holtype)list`; `TyVar v`; `TyVar v`]
                  HREV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[HTYPE_OK] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM]) THEN
    DISCH_THEN(MP_TAC o SPEC `(HREV_ASSOCD (TyVar v) tyin (TyVar v),TyVar v)`) THEN
    ASM_REWRITE_TAC[o_THM];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `ALL (htype_ok s) tys` THEN
    UNDISCH_TAC `ALL (\ty. htype_ok s ty /\ ALL (htype_ok s o FST) tyin
                           ==> htype_ok s (HTYPE_SUBST tyin ty)) tys` THEN
    REWRITE_TAC[IMP_IMP; AND_ALL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
    ASM_SIMP_TAC[o_THM]]);;

let HTERM_OK_WELLTYPED = prove
 (`!sig t. hterm_ok sig t ==> hwelltyped t`,
  GEN_TAC THEN MATCH_MP_TAC holterm_INDUCT THEN
  REWRITE_TAC[hterm_ok; HWELLTYPED_CLAUSES] THEN MESON_TAC[]);;

let HTERM_OK_TYPE_OK = prove
 (`!sig t. his_std_sig sig /\ hterm_ok sig t ==> htype_ok (FST sig) (htypeof t)`,
  GEN_TAC THEN MATCH_MP_TAC holterm_INDUCT THEN
  REWRITE_TAC[hterm_ok; htypeof; his_std_sig] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MESON_TAC[];
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `hwelltyped (TmComb a0 a1)` THEN
    REWRITE_TAC[HWELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    SUBGOAL_THEN `htype_ok (FST(sig:hsig)) (htypeof a0)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[HFun; HTYPE_OK; ALL; hcodomain] THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[htypeof; HFun; HTYPE_OK; ALL] THEN
    ASM_SIMP_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]]);;

let EXISTS_REFL_SYM = prove
 (`!a:A. ?x. a = x`,
  MESON_TAC[]);;

let HTERM_OK_EQUATION = prove
 (`!sig s t.
        his_std_sig sig
        ==> (hterm_ok sig (s =:= t) <=>
             hterm_ok sig s /\ hterm_ok sig t /\ htypeof t = htypeof s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[hequation; hterm_ok; HEqual; HWELLTYPED_CLAUSES; htypeof;
              HCODOMAIN_HFUN; HFUN_INJ] THEN
  REWRITE_TAC[EXISTS_REFL_SYM; RIGHT_EXISTS_AND_THM] THEN
  ASM_CASES_TAC `hterm_ok sig s` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `hterm_ok sig t` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `hwelltyped s /\ hwelltyped t /\
                htype_ok (FST(sig:hsig)) (htypeof s)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HTERM_OK_WELLTYPED; HTERM_OK_TYPE_OK]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `his_std_sig sig` THEN REWRITE_TAC[his_std_sig] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[option_INJ; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[HFun; HBool; HTYPE_OK; ALL; LENGTH; ARITH] THEN
  SUBGOAL_THEN
   `?i. TyApp "fun" [htypeof s; TyApp "fun" [htypeof s; TyApp "bool" []]] =
        HTYPE_SUBST i (TyApp "fun" [TyVar "A";
                                    TyApp "fun" [TyVar "A"; TyApp "bool" []]])`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXISTS_TAC `[htypeof s,TyVar "A"]` THEN
    REWRITE_TAC[HTYPE_SUBST; MAP; HREV_ASSOCD];
    MESON_TAC[]]);;

let HTERM_OK_VFREE_IN = prove
 (`!sig t x. HVFREE_IN x t /\ hterm_ok sig t ==> hterm_ok sig x`,
  GEN_TAC THEN MATCH_MP_TAC holterm_INDUCT THEN
  REWRITE_TAC[HVFREE_IN; hterm_ok] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[hterm_ok];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[hterm_ok];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let HTERM_OK_VSUBST = prove
 (`!sig tm ilist.
        hterm_ok sig tm /\
        (!s s'. MEM (s',s) ilist
                ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty /\ hterm_ok sig s')
        ==> hterm_ok sig (HVSUBST ilist tm)`,
  GEN_TAC THEN MATCH_MP_TAC holterm_INDUCT THEN REWRITE_TAC[HVSUBST] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:string`; `ty:holtype`; `ilist:(holterm#holterm)list`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`ilist:(holterm#holterm)list`; `TmVar x ty`; `TmVar x ty`]
                  HREV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:holterm`; `t:holterm`] THEN STRIP_TAC THEN
    X_GEN_TAC `ilist:(holterm#holterm)list` THEN
    REWRITE_TAC[hterm_ok] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `hwelltyped (TmComb s t)` THEN
    REWRITE_TAC[HWELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!u. hwelltyped u ==> HVSUBST ilist u hhas_type htypeof u`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HVSUBST_HAS_TYPE THEN
      ASM_REWRITE_TAC[GSYM HWELLTYPED] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[hwelltyped]; ASM_MESON_TAC[hwelltyped]; ALL_TAC] THEN
    EXISTS_TAC `rty:holtype` THEN
    ASM_MESON_TAC[HWELLTYPED_LEMMA];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:holterm`; `t:holterm`] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  X_GEN_TAC `ilist:(holterm#holterm)list` THEN
  REWRITE_TAC[hterm_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:string` (X_CHOOSE_THEN
    `ty:holtype` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[hdest_var; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[hterm_ok; holterm_INJ] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; GSYM CONJ_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MEM; MEM_FILTER; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_MESON_TAC[HHAS_TYPE_VAR; hterm_ok]);;

let HNOT_IS_RESULT = prove
 (`!r. ~(HIS_RESULT r) <=> HIS_CLASH r`,
  MATCH_MP_TAC hresult_INDUCT THEN REWRITE_TAC[HIS_RESULT; HIS_CLASH]);;

let HTERM_OK_INST_CORE = prove
 (`!sig tyin tm env.
        hterm_ok sig tm /\ ALL (htype_ok (FST sig)) (MAP FST tyin) /\
        (!s s'. MEM (s,s') env
                ==> ?x ty. s = TmVar x ty /\ s' = TmVar x (HTYPE_SUBST tyin ty)) /\
        HIS_RESULT (HINST_CORE env tyin tm)
        ==> hterm_ok sig (HRESULT (HINST_CORE env tyin tm))`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC HSIZEOF_INDUCT THEN GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `tm:holterm` (cases "holterm")) THEN
  DISCH_THEN(LABEL_TAC "ih") THEN X_GEN_TAC `env:(holterm#holterm)list` THENL
   [REWRITE_TAC[HINST_CORE; LET_DEF; LET_END_DEF; hterm_ok] THEN
    COND_CASES_TAC THEN REWRITE_TAC[HIS_RESULT; HRESULT; hterm_ok] THEN
    MESON_TAC[HTYPE_OK_TYPE_SUBST];
    REWRITE_TAC[HINST_CORE; HRESULT; hterm_ok] THEN STRIP_TAC THEN
    EXISTS_TAC `ty0:holtype` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HTYPE_OK_TYPE_SUBST]; ALL_TAC] THEN
    REWRITE_TAC[HTYPE_SUBST_COMPOSE] THEN MESON_TAC[];
    REWRITE_TAC[hterm_ok] THEN STRIP_TAC THEN
    UNDISCH_TAC `HIS_RESULT (HINST_CORE env tyin (TmComb a0 a1))` THEN
    REWRITE_TAC[HINST_CORE; LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM HNOT_IS_RESULT]) THEN
    ASM_REWRITE_TAC[HIS_RESULT; HRESULT; hterm_ok] THEN
    SUBGOAL_THEN
     `!tm. hwelltyped tm /\ HIS_RESULT (HINST_CORE env tyin tm)
           ==> (HRESULT (HINST_CORE env tyin tm)) hhas_type
               (HTYPE_SUBST tyin (htypeof tm))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`tm:holterm`; `env:(holterm#holterm)list`;
                    `tyin:(holtype#holtype)list`] HINST_CORE_HAS_TYPE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [UNDISCH_TAC `HIS_RESULT (HINST_CORE env tyin tm)` THEN
        ASM_REWRITE_TAC[HIS_RESULT];
        ASM_REWRITE_TAC[HRESULT]];
      ALL_TAC] THEN
    UNDISCH_TAC `hwelltyped (TmComb a0 a1)` THEN
    REWRITE_TAC[HWELLTYPED_CLAUSES] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `HRESULT (HINST_CORE env tyin a0) hhas_type
        HFun (HTYPE_SUBST tyin (htypeof a1)) (HTYPE_SUBST tyin rty) /\
      HRESULT (HINST_CORE env tyin a1) hhas_type
        HTYPE_SUBST tyin (htypeof a1)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM HTYPE_SUBST_HFUN] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "ih" (MP_TAC o SPEC `a0:holterm`) THEN
      REWRITE_TAC[hsizeof; ARITH_RULE `s < 1 + s + t`] THEN
      DISCH_THEN(MP_TAC o SPEC `env:(holterm#holterm)list`) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "ih" (MP_TAC o SPEC `a1:holterm`) THEN
      REWRITE_TAC[hsizeof; ARITH_RULE `t < 1 + s + t`] THEN
      DISCH_THEN(MP_TAC o SPEC `env:(holterm#holterm)list`) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[hwelltyped];
      ASM_MESON_TAC[hwelltyped];
      EXISTS_TAC `HTYPE_SUBST tyin rty` THEN
      ASM_MESON_TAC[HWELLTYPED_LEMMA]];
    ALL_TAC] THEN
  REWRITE_TAC[hterm_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:string` (X_CHOOSE_THEN
   `ty:holtype` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `HIS_RESULT (HINST_CORE env tyin (TmAbs (TmVar x ty) a1))` THEN
  REWRITE_TAC[HINST_CORE; hdest_var; FST; SND; LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[HIS_RESULT; HRESULT] THEN
  REWRITE_TAC[hterm_ok; holterm_INJ; RIGHT_EXISTS_AND_THM; UNWIND_THM1;
              GSYM CONJ_ASSOC] THEN
  ASM_SIMP_TAC[HTYPE_OK_TYPE_SUBST] THENL
   [USE_THEN "ih" (MP_TAC o SPEC `a1:holterm`) THEN
    REWRITE_TAC[hsizeof; ARITH_RULE `t < 2 + t`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z = HVARIANT (HRESULT (HINST_CORE [] tyin a1)) x
                           (HTYPE_SUBST tyin ty)` THEN
  ABBREV_TAC `t' = HVSUBST [TmVar z ty,TmVar x ty] a1` THEN
  SUBGOAL_THEN `hsizeof t' = hsizeof a1 /\ hterm_ok sig t'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC HSIZEOF_VSUBST THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
      MESON_TAC[];
      MATCH_MP_TAC HTERM_OK_VSUBST THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
      ASM_MESON_TAC[HHAS_TYPE_VAR; hterm_ok]];
    ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPEC `t':holterm`) THEN
  REWRITE_TAC[hsizeof; ASSUME `hsizeof t' = hsizeof a1`;
              ARITH_RULE `t < 2 + t`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

let HTERM_OK_INST = prove
 (`!sig tyin tm.
        hterm_ok sig tm /\ ALL (htype_ok (FST sig)) (MAP FST tyin)
        ==> hterm_ok sig (HINST tyin tm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HINST_DEF] THEN
  MATCH_MP_TAC HTERM_OK_INST_CORE THEN
  ASM_MESON_TAC[MEM; HTERM_OK_WELLTYPED; HINST_CORE_NIL_IS_RESULT]);;

let HTERM_OK_RACONV = prove
 (`!env tp. HRACONV env tp
            ==> !sig. ALL (\(s,s'). hwelltyped s /\ hwelltyped s' /\
                                    htypeof s = htypeof s' /\
                                    htype_ok (FST sig) (htypeof s)) env /\
                      hterm_ok sig (FST tp) /\ hwelltyped (SND tp)
                      ==> hterm_ok sig (SND tp)`,
  MATCH_MP_TAC HRACONV_INDUCT THEN REWRITE_TAC[FST; SND; hterm_ok] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP HALPHAVARS_MEM) THENL
     [UNDISCH_TAC `ALL (\(s,s'). hwelltyped s /\ hwelltyped s' /\
                                 htypeof s = htypeof s' /\
                                 htype_ok (FST(sig:hsig)) (htypeof s)) env` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN
      DISCH_THEN(MP_TAC o SPEC `(TmVar x1 ty1,TmVar x2 ty2)`) THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[htypeof] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
      REWRITE_TAC[FST; SND; holterm_INJ] THEN ASM_MESON_TAC[]];
    MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `hwelltyped (TmComb s2 t2)` THEN
    REWRITE_TAC[HWELLTYPED_CLAUSES] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `hwelltyped (TmAbs v2 t2)` THEN
    REWRITE_TAC[HWELLTYPED_CLAUSES] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:string` (X_CHOOSE_THEN `nty:holtype`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`n:string`; `nty:holtype`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `nty:holtype = ty` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `htypeof v1 = htypeof v2` THEN
      ASM_REWRITE_TAC[htypeof] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ALL] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_REWRITE_TAC[HWELLTYPED_CLAUSES; htypeof]]);;

let HTERM_OK_ACONV = prove
 (`!sig t1 t2. HACONV t1 t2 /\ hterm_ok sig t1 /\ hwelltyped t2
               ==> hterm_ok sig t2`,
  REWRITE_TAC[HACONV] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sig:hsig` o MATCH_MP HTERM_OK_RACONV) THEN
  ASM_REWRITE_TAC[ALL; FST; SND]);;

let HPROVES_THEORY_OK = prove
 (`!thy h c. hproves thy h c ==> htheory_ok thy`,
  MATCH_MP_TAC hproves_INDUCT THEN SIMP_TAC[]);;

let HTHEORY_OK_STD_SIG = prove
 (`!thy. htheory_ok thy ==> his_std_sig (FST thy)`,
  SIMP_TAC[htheory_ok]);;

(* ------------------------------------------------------------------------- *)
(* Every hypothesis and conclusion of a provable sequent is a well-formed   *)
(* term of type bool.                                                        *)
(* ------------------------------------------------------------------------- *)

let ALL_HTERM_UNION = prove
 (`!P l1 l2. ALL P l1 /\ ALL P l2 ==> ALL P (HTERM_UNION l1 l2)`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[HTERM_UNION_NONEW]);;

let ALL_FILTER_IMP = prove
 (`!P Q l:A list. ALL P l ==> ALL P (FILTER Q l)`,
  REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN MESON_TAC[]);;

let HPROVES_TERM_OK = prove
 (`!thy h c. hproves thy h c
             ==> htheory_ok thy /\ hterm_ok (FST thy) c /\ c hhas_type HBool /\
                 ALL (\p. hterm_ok (FST thy) p /\ p hhas_type HBool) h`,
  MATCH_MP_TAC hproves_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HTHEORY_OK_STD_SIG) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HEQUATION_HAS_TYPE_BOOL]) THEN
  FIRST_ASSUM(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP HTERM_OK_EQUATION th])) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[HTERM_OK_EQUATION; HEQUATION_HAS_TYPE_BOOL] THENL
   [REWRITE_TAC[hterm_ok; HWELLTYPED_CLAUSES; htypeof; holterm_INJ] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[ALL];
    REWRITE_TAC[hterm_ok; HWELLTYPED_CLAUSES; htypeof; HCODOMAIN_HFUN; ALL;
                holterm_INJ] THEN
    ASM_MESON_TAC[HTERM_OK_WELLTYPED];
    SUBGOAL_THEN `htypeof c1 = HBool /\ htypeof c2 = HBool` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[HWELLTYPED_LEMMA]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[hwelltyped]; ALL_TAC] THEN
    MATCH_MP_TAC ALL_HTERM_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC ALL_FILTER_IMP THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [SUBGOAL_THEN `htypeof q = HBool` (fun th -> ASM_MESON_TAC[th; HWELLTYPED]) THEN
      ASM_MESON_TAC[HACONV_TYPE; HWELLTYPED_LEMMA];
      MATCH_MP_TAC ALL_HTERM_UNION THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `!s s'. MEM (s',s) ilist ==> ?x ty. s = TmVar x ty /\ s' hhas_type ty`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[HTERM_OK_VSUBST; HVSUBST_HAS_TYPE] THEN
    REWRITE_TAC[ALL_MAP] THEN
    UNDISCH_TAC `ALL (\p. hterm_ok (FST(thy:hthy)) p /\ p hhas_type HBool) h` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
    ASM_SIMP_TAC[o_THM; HTERM_OK_VSUBST; HVSUBST_HAS_TYPE];
    SUBGOAL_THEN `!t. t hhas_type HBool ==> HINST tyin t hhas_type HBool`
    ASSUME_TAC THENL [MESON_TAC[HINST_HAS_TYPE; HTYPE_SUBST_HBOOL]; ALL_TAC] THEN
    ASM_SIMP_TAC[HTERM_OK_INST] THEN
    REWRITE_TAC[ALL_MAP] THEN
    UNDISCH_TAC `ALL (\p. hterm_ok (FST(thy:hthy)) p /\ p hhas_type HBool) h` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
    ASM_SIMP_TAC[o_THM; HTERM_OK_INST];
    UNDISCH_TAC `hwelltyped (TmComb l1 l2)` THEN
    REWRITE_TAC[hterm_ok; HWELLTYPED_CLAUSES; htypeof] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC ALL_HTERM_UNION THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[HTERM_OK_WELLTYPED; ALL];
    REWRITE_TAC[ALL] THEN ASM_MESON_TAC[htheory_ok]]);;

(* ------------------------------------------------------------------------- *)
(* Admissible weakening and closure under alpha-equivalence.                 *)
(* ------------------------------------------------------------------------- *)

let HACONV_VAR = prove
 (`!t x ty. HACONV t (TmVar x ty) <=> t = TmVar x ty`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[HACONV_REFL] THEN
  STRUCT_CASES_TAC(SPEC `t:holterm` (cases "holterm")) THEN
  REWRITE_TAC[HACONV; HRACONV; HALPHAVARS]);;

let HREV_ASSOCD_NOT_MEM = prove
 (`!l:(B#A)list a d. ~(?x. MEM (x,a) l) ==> HREV_ASSOCD a l d = d`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HREV_ASSOCD] THEN
  SPEC_TAC(`h:B#A`,`p:B#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[HREV_ASSOCD; MEM; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let HVSUBST_TRIVIAL = prove
 (`!tm ilist. (!s' s. MEM (s',s) ilist ==> ~HVFREE_IN s tm)
              ==> HVSUBST ilist tm = tm`,
  MATCH_MP_TAC holterm_INDUCT THEN REWRITE_TAC[HVSUBST; HVFREE_IN] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HREV_ASSOCD_NOT_MEM THEN
    DISCH_THEN(X_CHOOSE_TAC `y:holterm`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:holterm`; `TmVar a0 a1`]) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[holterm_INJ] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`v:holterm`; `t:holterm`] THEN STRIP_TAC THEN
    X_GEN_TAC `ilist:(holterm#holterm)list` THEN DISCH_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN
     `!s' s. MEM (s',s) (FILTER (\(s',s). ~(s = v))
                                  (ilist:(holterm#holterm)list))
             ==> ~HVFREE_IN s t`
    ASSUME_TAC THENL
     [REWRITE_TAC[MEM_FILTER] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~EX (\(s',s). HVFREE_IN v s' /\ HVFREE_IN s t)
                      (FILTER (\(s',s). ~(s = v))
                              (ilist:(holterm#holterm)list))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[NOT_EX; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let HVFREE_IN_ITLIST_COMB = prove
 (`!l b v. HVFREE_IN v (ITLIST TmComb l b) <=> HVFREE_IN v b \/ EX (HVFREE_IN v) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; EX; HVFREE_IN] THEN
  MESON_TAC[]);;

let HPROVES_ADD_FRONT = prove
 (`!thy rest r q.
        hproves thy rest r /\ q hhas_type HBool /\ hterm_ok (FST thy) q
        ==> ?r'. hproves thy (CONS q rest) r'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HPROVES_THEORY_OK) THEN
  ABBREV_TAC
   `z = HVARIANT (TmComb (TmComb q r) (ITLIST TmComb rest q)) "x" HBool` THEN
  MP_TAC(ISPECL [`TmComb (TmComb q r) (ITLIST TmComb rest q)`; `"x"`; `HBool`]
                HVARIANT_THM) THEN
  ASM_REWRITE_TAC[HVFREE_IN; HVFREE_IN_ITLIST_COMB; DE_MORGAN_THM] THEN
  REWRITE_TAC[NOT_EX; GSYM ALL_MEM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `hproves thy [TmVar z HBool] (TmVar z HBool)` ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_ASSUME THEN ASM_REWRITE_TAC[HHAS_TYPE_VAR; hterm_ok] THEN
    UNDISCH_TAC `htheory_ok thy` THEN
    SIMP_TAC[htheory_ok; his_std_sig; HBool; HTYPE_OK; LENGTH; ALL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`thy:hthy`; `[TmVar z HBool]`; `rest:holterm list`;
                `TmVar z HBool`; `r:holterm`] HPROVES_DEDUCT_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `HTERM_UNION (FILTER ((~) o HACONV r) [TmVar z HBool])
                (FILTER ((~) o HACONV (TmVar z HBool)) rest) =
    CONS (TmVar z HBool) rest`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!y. MEM y rest ==> ~HACONV (TmVar z HBool) y` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP HACONV_SYM) THEN
      REWRITE_TAC[HACONV_VAR] THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[HVFREE_IN];
      ALL_TAC] THEN
    SUBGOAL_THEN `FILTER ((~) o HACONV (TmVar z HBool)) rest = rest`
    SUBST1_TAC THENL
     [UNDISCH_TAC `!y. MEM y rest ==> ~HACONV (TmVar z HBool) y` THEN
      SPEC_TAC(`rest:holterm list`,`l:holterm list`) THEN
      LIST_INDUCT_TAC THEN ASM_SIMP_TAC[FILTER; MEM; o_THM];
      ALL_TAC] THEN
    REWRITE_TAC[FILTER; o_THM] THEN
    SUBGOAL_THEN `~HACONV r (TmVar z HBool)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[HACONV_VAR] THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[HVFREE_IN];
      ALL_TAC] THEN
    REWRITE_TAC[HTERM_UNION; LET_DEF; LET_END_DEF; GSYM EX_MEM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`thy:hthy`; `[q:holterm,TmVar z HBool]`;
                `CONS (TmVar z HBool) rest`; `TmVar z HBool =:= r`]
               HPROVES_INST) THEN
  ASM_REWRITE_TAC[MEM; PAIR_EQ] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MAP; HVSUBST; HREV_ASSOCD] THEN
  SUBGOAL_THEN `MAP (HVSUBST [q:holterm,TmVar z HBool]) rest = rest` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `MAP (\x:holterm. x) rest` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[MAP_ID]] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HVSUBST_TRIVIAL THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
    ASM_MESON_TAC[];
    MESON_TAC[]]);;

let HPROVES_EXISTS_HYPS = prove
 (`!thy h. htheory_ok thy /\
           ALL (\p. hterm_ok (FST thy) p /\ p hhas_type HBool) h
           ==> ?r. hproves thy h r`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THENL
   [STRIP_TAC THEN EXISTS_TAC `TmVar "x" HBool =:= TmVar "x" HBool` THEN
    MATCH_MP_TAC HPROVES_REFL THEN ASM_REWRITE_TAC[hterm_ok] THEN
    UNDISCH_TAC `htheory_ok thy` THEN
    SIMP_TAC[htheory_ok; his_std_sig; HBool; HTYPE_OK; LENGTH; ALL];
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `r:holterm`) THEN
    MATCH_MP_TAC HPROVES_ADD_FRONT THEN EXISTS_TAC `r:holterm` THEN
    ASM_REWRITE_TAC[]]);;

let HPROVES_ACONV = prove
 (`!thy h c h' c'.
        hproves thy h c /\
        (!x. MEM x h ==> ?y. MEM y h' /\ HACONV x y) /\
        ALL (\p. hterm_ok (FST thy) p /\ p hhas_type HBool) h' /\
        HACONV c c' /\ hwelltyped c'
        ==> hproves thy h' c'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HPROVES_TERM_OK) THEN
  MP_TAC(SPECL [`thy:hthy`; `h':holterm list`] HPROVES_EXISTS_HYPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `r:holterm`) THEN
  MP_TAC(SPECL [`thy:hthy`; `h':holterm list`; `h:holterm list`;
                `r:holterm`; `c:holterm`] HPROVES_DEDUCT_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`thy:hthy`;
                `HTERM_UNION (FILTER ((~) o HACONV c) h')
                             (FILTER ((~) o HACONV r) h)`;
                `h':holterm list`; `r:holterm`; `c:holterm`; `r:holterm`]
               HPROVES_EQ_MP) THEN
  ASM_REWRITE_TAC[HACONV_REFL] THEN
  SUBGOAL_THEN
   `HTERM_UNION (HTERM_UNION (FILTER ((~) o HACONV c) h')
                             (FILTER ((~) o HACONV r) h)) h' = h'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HTERM_UNION_SUBSUMED THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP HTERM_UNION_NONEW) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MEM_FILTER]) THEN ASM_MESON_TAC[HACONV_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`thy:hthy`; `[]:holterm list`; `h':holterm list`;
                `c':holterm`; `c':holterm`; `c:holterm`] HPROVES_EQ_MP) THEN
  ASM_REWRITE_TAC[HTERM_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HPROVES_REFL THEN ASM_MESON_TAC[HTERM_OK_ACONV];
    ASM_MESON_TAC[HACONV_SYM]]);;

let HPROVES_WEAKEN = prove
 (`!thy h c h'.
        hproves thy h c /\ (!x. MEM x h ==> MEM x h') /\
        ALL (\p. hterm_ok (FST thy) p /\ p hhas_type HBool) h'
        ==> hproves thy h' c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HPROVES_ACONV THEN
  MAP_EVERY EXISTS_TAC [`h:holterm list`; `c:holterm`] THEN
  ASM_REWRITE_TAC[HACONV_REFL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HACONV_REFL]; ALL_TAC] THEN
  ASM_MESON_TAC[HPROVES_TERM_OK; hwelltyped]);;

(* ------------------------------------------------------------------------- *)
(* A derived rule: transitivity of equality up to alpha-equivalence.       *)
(* ------------------------------------------------------------------------- *)

let HACONV_EQUATION = prove
 (`!l m l' m'. HACONV (l =:= m) (l' =:= m') <=> HACONV l l' /\ HACONV m m'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HACONV; hequation; HEqual; HRACONV] THEN
  REWRITE_TAC[GSYM HACONV] THEN MESON_TAC[HACONV_TYPE]);;

let HPROVES_TRANS = prove
 (`!thy h1 h2 l m1 m2 r.
        hproves thy h1 (l =:= m1) /\ hproves thy h2 (m2 =:= r) /\
        HACONV m1 m2
        ==> hproves thy (HTERM_UNION h1 h2) (l =:= r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`thy:hthy`; `h1:holterm list`; `l =:= m1`] HPROVES_TERM_OK) THEN
  MP_TAC(ISPECL [`thy:hthy`; `h2:holterm list`; `m2 =:= r`] HPROVES_TERM_OK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HTHEORY_OK_STD_SIG) THEN
  SUBGOAL_THEN `hterm_ok (FST(thy:hthy)) l /\ hterm_ok (FST thy) m1 /\
                htypeof m1 = htypeof l /\
                hterm_ok (FST thy) m2 /\ hterm_ok (FST thy) r /\
                htypeof r = htypeof m2`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP HTERM_OK_EQUATION
       (ASSUME `his_std_sig (FST(thy:hthy))`)]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `htypeof m2 = htypeof l` ASSUME_TAC THENL
   [ASM_MESON_TAC[HACONV_TYPE]; ALL_TAC] THEN
  SUBGOAL_THEN `hproves thy [] (TmComb (HEqual (htypeof l)) l =:=
                                TmComb (HEqual (htypeof l)) l)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HPROVES_REFL THEN ASM_REWRITE_TAC[hterm_ok; HEqual] THEN
    REWRITE_TAC[HWELLTYPED_CLAUSES; htypeof; HFUN_INJ] THEN
    REWRITE_TAC[EXISTS_REFL_SYM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[HTERM_OK_WELLTYPED]] THEN
    UNDISCH_TAC `his_std_sig (FST(thy:hthy))` THEN REWRITE_TAC[his_std_sig] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN CONJ_TAC THENL
     [REWRITE_TAC[HFun; HBool; HTYPE_OK; ALL; LENGTH; ARITH] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`FST(thy:hthy)`; `l:holterm`] HTERM_OK_TYPE_OK) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[his_std_sig] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `[htypeof l,TyVar "A"]` THEN
      REWRITE_TAC[HTYPE_SUBST_HFUN; HTYPE_SUBST_HBOOL; HTYPE_SUBST;
                  HREV_ASSOCD]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`thy:hthy`; `[]:holterm list`; `h2:holterm list`;
                `TmComb (HEqual (htypeof l)) l`; `TmComb (HEqual (htypeof l)) l`;
                `m2:holterm`; `r:holterm`] HPROVES_MK_COMB) THEN
  ASM_REWRITE_TAC[HTERM_UNION] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HWELLTYPED_CLAUSES; HEqual; htypeof; HFUN_INJ;
                HCODOMAIN_HFUN] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hwelltyped l /\ hwelltyped m2` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[HTERM_OK_WELLTYPED]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. TmComb (TmComb (HEqual (htypeof l)) l) a = (l =:= a)`
   (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[hequation]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`thy:hthy`; `h2:holterm list`; `h1:holterm list`;
                `l =:= m2`; `l =:= r`; `l =:= m1`] HPROVES_EQ_MP) THEN
  ASM_REWRITE_TAC[HACONV_EQUATION; HACONV_REFL] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HACONV_SYM]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HPROVES_ACONV THEN
  MAP_EVERY EXISTS_TAC [`HTERM_UNION h2 h1`; `l =:= r`] THEN
  ASM_REWRITE_TAC[HACONV_REFL] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP HTERM_UNION_NONEW) THEN
    MATCH_MP_TAC HTERM_UNION_THM THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ALL_HTERM_UNION THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[HWELLTYPED_EQUATION; HEQUATION_HAS_TYPE_BOOL] THEN
    SUBGOAL_THEN `hwelltyped l /\ hwelltyped r` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[HTERM_OK_WELLTYPED]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;
