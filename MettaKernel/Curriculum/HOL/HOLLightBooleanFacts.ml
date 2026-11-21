(* Derived Boolean proof input for the retained HOL Light source exporter. *)

let BOOL_DATA_RECURSION = prove
 (`!e0 e1:A. ?fn:bool->A. fn F = e0 /\ fn T = e1`,
  MATCH_ACCEPT_TAC bool_RECURSION);;

let BOOL_DATA_INDUCTION = prove
 (`!P:bool->bool. P F /\ P T ==> !b:bool. P b`,
  MATCH_ACCEPT_TAC bool_INDUCT);;

let BOOL_DATA_DISTINCT = prove
 (`~(F = T)`, REWRITE_TAC[]);;

let BOOL_DATA_CASES = prove
 (`!b:bool. b = F \/ b = T`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let BOOL_DATA_FINITE = prove
 (`!f:bool->bool.
     (!x y:bool. f x = f y ==> x = y) ==>
     !x:bool. ?y:bool. f y = x`,
  MESON_TAC[BOOL_CASES_AX]);;
