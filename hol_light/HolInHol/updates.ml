(* ========================================================================= *)
(* Theory contexts: sequences of updates (new types, new constants, axioms,  *)
(* constant specifications and type definitions), following Candle's         *)
(* holSyntax. A context determines a signature and a set of axioms.          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Strings ordered lexicographically by character code (as OCaml compares   *)
(* strings); ASCII's first argument is the most significant bit.             *)
(* ------------------------------------------------------------------------- *)

let hchar_code = define
 `hchar_code (ASCII a0 a1 a2 a3 a4 a5 a6 a7) =
    (if a0 then 128 else 0) + (if a1 then 64 else 0) +
    (if a2 then 32 else 0) + (if a3 then 16 else 0) +
    (if a4 then 8 else 0) + (if a5 then 4 else 0) +
    (if a6 then 2 else 0) + (if a7 then 1 else 0)`;;

let hstring_lt = define
 `(hstring_lt [] s <=> ~(s = [])) /\
  (hstring_lt (CONS c s) [] <=> F) /\
  (hstring_lt (CONS c1 s1) (CONS c2 s2) <=>
     hchar_code c1 < hchar_code c2 \/ c1 = c2 /\ hstring_lt s1 s2)`;;

let HINORDER_INSERT = new_definition
 `HINORDER_INSERT x xs =
    APPEND (FILTER (\y. hstring_lt y x) xs)
           (APPEND [x] (FILTER (\y. hstring_lt x y) xs))`;;

let HSTRING_SORT = new_definition
 `HSTRING_SORT xs = ITLIST HINORDER_INSERT xs []`;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary list functions.                                                 *)
(* ------------------------------------------------------------------------- *)

let hflat = define
 `(hflat [] = []:A list) /\
  (hflat (CONS h t) = APPEND h (hflat t))`;;

let HALL_DISTINCT = define
 `(HALL_DISTINCT [] <=> T) /\
  (HALL_DISTINCT (CONS (h:A) t) <=> ~MEM h t /\ HALL_DISTINCT t)`;;

(* ------------------------------------------------------------------------- *)
(* Updates.                                                                  *)
(*   HConstSpec eqs prop: constants by specification, with witnesses eqs.    *)
(*   HTypeDefn name pred abs_name rep_name: a new type operator from a       *)
(*   predicate, with its abstraction and representation constants.           *)
(*   HNewType name arity, HNewConst name type, HNewAxiom prop.               *)
(* ------------------------------------------------------------------------- *)

let hupdate_INDUCT,hupdate_RECURSION = define_type
 "hupdate = HConstSpec ((string#holterm)list) holterm
          | HTypeDefn string holterm string string
          | HNewType string num
          | HNewConst string holtype
          | HNewAxiom holterm";;

let hupdate_DISTINCT = distinctness "hupdate";;

let hupdate_INJ = injectivity "hupdate";;

(* ------------------------------------------------------------------------- *)
(* The types and constants introduced by an update.                          *)
(* ------------------------------------------------------------------------- *)

let htypes_of_upd = define
 `(htypes_of_upd (HConstSpec eqs prop) = []) /\
  (htypes_of_upd (HTypeDefn name pred abs_name rep_name) =
     [name,LENGTH (htvars pred)]) /\
  (htypes_of_upd (HNewType name arity) = [name,arity]) /\
  (htypes_of_upd (HNewConst name ty) = []) /\
  (htypes_of_upd (HNewAxiom prop) = [])`;;

let hconsts_of_upd = define
 `(hconsts_of_upd (HConstSpec eqs prop) =
     MAP (\(s,t). (s,htypeof t)) eqs) /\
  (hconsts_of_upd (HTypeDefn name pred abs_name rep_name) =
     let rep_type = hdomain (htypeof pred) in
     let abs_type = TyApp name (MAP TyVar (HSTRING_SORT (htvars pred))) in
     [abs_name,HFun rep_type abs_type; rep_name,HFun abs_type rep_type]) /\
  (hconsts_of_upd (HNewType name arity) = []) /\
  (hconsts_of_upd (HNewConst name ty) = [name,ty]) /\
  (hconsts_of_upd (HNewAxiom prop) = [])`;;

let htype_list = new_definition
 `htype_list ctxt = hflat (MAP htypes_of_upd ctxt)`;;

let hconst_list = new_definition
 `hconst_list ctxt = hflat (MAP hconsts_of_upd ctxt)`;;

let hsigof = new_definition
 `hsigof ctxt = (htype_list ctxt,hconst_list ctxt)`;;

(* ------------------------------------------------------------------------- *)
(* Axioms: axiomatic extensions and conservative extensions.                 *)
(* ------------------------------------------------------------------------- *)

let haxexts_of_upd = define
 `(haxexts_of_upd (HNewAxiom prop) = [prop]) /\
  (haxexts_of_upd (HConstSpec eqs prop) = []) /\
  (haxexts_of_upd (HTypeDefn name pred abs_name rep_name) = []) /\
  (haxexts_of_upd (HNewType name arity) = []) /\
  (haxexts_of_upd (HNewConst name ty) = [])`;;

let hconexts_of_upd = define
 `(hconexts_of_upd (HConstSpec eqs prop) =
     let ilist = MAP (\(s,t). let ty = htypeof t in (TmConst s ty,TmVar s ty))
                     eqs in
     [HVSUBST ilist prop]) /\
  (hconexts_of_upd (HTypeDefn name pred abs_name rep_name) =
     let abs_type = TyApp name (MAP TyVar (HSTRING_SORT (htvars pred))) in
     let rep_type = hdomain (htypeof pred) in
     let absc = TmConst abs_name (HFun rep_type abs_type) in
     let repc = TmConst rep_name (HFun abs_type rep_type) in
     let a = TmVar "a" abs_type in
     let r = TmVar "r" rep_type in
     [TmComb absc (TmComb repc a) =:= a;
      TmComb pred r =:= (TmComb repc (TmComb absc r) =:= r)]) /\
  (hconexts_of_upd (HNewType name arity) = []) /\
  (hconexts_of_upd (HNewConst name ty) = []) /\
  (hconexts_of_upd (HNewAxiom prop) = [])`;;

let haxioms_of_upd = new_definition
 `haxioms_of_upd upd = APPEND (haxexts_of_upd upd) (hconexts_of_upd upd)`;;

let haxiom_list = new_definition
 `haxiom_list ctxt = hflat (MAP haxioms_of_upd ctxt)`;;

(* The theory of a context: its signature and its axioms.                     *)

let hthyof = new_definition
 `hthyof ctxt = (hsigof ctxt,set_of_list (haxiom_list ctxt))`;;

(* ------------------------------------------------------------------------- *)
(* The principles for extending a context.                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("hupdates",(12,"right"));;

let hupdates_RULES,hupdates_INDUCT,hupdates_CASES = new_inductive_definition
 `(!ctxt prop.
      prop hhas_type HBool /\ hterm_ok (hsigof ctxt) prop
      ==> (HNewAxiom prop) hupdates ctxt) /\
  (!ctxt name ty.
      hlookup (hconst_list ctxt) name = NONE /\
      htype_ok (htype_list ctxt) ty
      ==> (HNewConst name ty) hupdates ctxt) /\
  (!ctxt eqs prop.
      hproves (hthyof ctxt) (MAP (\(s,t). TmVar s (htypeof t) =:= t) eqs) prop /\
      ALL (\t. HCLOSED t /\
               (!v. MEM v (htvars t) ==> MEM v (htyvars (htypeof t))))
          (MAP SND eqs) /\
      (!x ty. HVFREE_IN (TmVar x ty) prop
              ==> MEM (x,ty) (MAP (\(s,t). (s,htypeof t)) eqs)) /\
      (!s. MEM s (MAP FST eqs) ==> hlookup (hconst_list ctxt) s = NONE) /\
      HALL_DISTINCT (MAP FST eqs)
      ==> (HConstSpec eqs prop) hupdates ctxt) /\
  (!ctxt name arity.
      hlookup (htype_list ctxt) name = NONE
      ==> (HNewType name arity) hupdates ctxt) /\
  (!ctxt name pred abs_name rep_name witness.
      hproves (hthyof ctxt) [] (TmComb pred witness) /\
      HCLOSED pred /\
      hlookup (htype_list ctxt) name = NONE /\
      hlookup (hconst_list ctxt) abs_name = NONE /\
      hlookup (hconst_list ctxt) rep_name = NONE /\
      ~(abs_name = rep_name)
      ==> (HTypeDefn name pred abs_name rep_name) hupdates ctxt)`;;

(* Reflexive-transitive closure of extension by one valid update.            *)

parse_as_infix("hextends",(12,"right"));;

let hextends_RULES,hextends_INDUCT,hextends_CASES = new_inductive_definition
 `(!ctxt. ctxt hextends ctxt) /\
  (!ctxt1 ctxt2 upd.
      ctxt2 hextends ctxt1 /\ upd hupdates ctxt2
      ==> (CONS upd ctxt2) hextends ctxt1)`;;

(* ------------------------------------------------------------------------- *)
(* The initial context: the type operators bool and fun, and equality.       *)
(* ------------------------------------------------------------------------- *)

let hinit_ctxt = new_definition
 `hinit_ctxt = [HNewConst "=" (HFun (TyVar "A") (HFun (TyVar "A") HBool));
                HNewType "bool" 0;
                HNewType "fun" 2]`;;

(* ------------------------------------------------------------------------- *)
(* Basic facts.                                                              *)
(* ------------------------------------------------------------------------- *)

let HEXTENDS_TRANS = prove
 (`!c1 c2 c3. c1 hextends c2 /\ c2 hextends c3 ==> c1 hextends c3`,
  SUBGOAL_THEN `!c1 c2. c1 hextends c2 ==> !c3. c2 hextends c3 ==> c1 hextends c3`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC hextends_INDUCT THEN MESON_TAC[hextends_RULES]);;

let HCONTEXT_CONV =
  let rw = REWRITE_CONV[htheory_ok; hthyof; hsigof; htype_list; hconst_list;
                        haxiom_list; MAP; hflat; htypes_of_upd; hconsts_of_upd;
                        haxioms_of_upd; haxexts_of_upd; hconexts_of_upd; APPEND;
                        set_of_list; NOT_IN_EMPTY; his_std_sig; hlookup;
                        FST; SND; HFun; HBool; HTYPE_OK; ALL; LENGTH; ARITH;
                        option_INJ; option_DISTINCT] in
  REPEATC(CHANGED_CONV(rw THENC TRY_CONV(ONCE_DEPTH_CONV STRING_EQ_CONV)));;

let HINIT_THEORY_OK = prove
 (`htheory_ok (hthyof hinit_ctxt)`,
  REWRITE_TAC[hinit_ctxt] THEN CONV_TAC HCONTEXT_CONV THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC HCONTEXT_CONV);;
