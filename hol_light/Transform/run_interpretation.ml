(* Closed source formulas consumed by the finite-run interpretation. These
   theorems retain the loaded list and run constants and their type instances. *)

let TC_RUN_LIST_SEPARATION = prove
 (`!(h:E) t. ~(CONS h t = [])`,
  MATCH_ACCEPT_TAC NOT_CONS_NIL);;

let TC_RUN_LIST_INJECTIVITY = prove
 (`!(h1:E) h2 t1 t2.
     (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\ (t1 = t2)`,
  MATCH_ACCEPT_TAC CONS_11);;

let TC_RUN_LIST_INDUCTION = prove
 (`!P:E list->bool. P [] /\ (!h t. P t ==> P (CONS h t)) ==> !l. P l`,
  MATCH_ACCEPT_TAC list_INDUCT);;

let TC_RUN_PATH_NIL = prove
 (`!(step:S->E->S->bool) s t. tc_path step [] s t <=> s = t`,
  REWRITE_TAC[tc_path]);;

let TC_RUN_PATH_CONS = prove
 (`!(step:S->E->S->bool) event events s t.
     tc_path step (CONS event events) s t <=>
       ?u. step s event u /\ tc_path step events u t`,
  REWRITE_TAC[tc_path]);;

let TC_RUN_PULLBACK_NIL = prove
 (`!(back:E->V->V) value. tc_pullback back [] value = value`,
  REWRITE_TAC[tc_pullback]);;

let TC_RUN_PULLBACK_CONS = prove
 (`!(back:E->V->V) event events value.
     tc_pullback back (CONS event events) value =
       back event (tc_pullback back events value)`,
  REWRITE_TAC[tc_pullback]);;
