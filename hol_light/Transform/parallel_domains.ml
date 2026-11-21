(* The event carrier retains complete proposed firing/preparation data.
   Its domain checks preparation and permission at every computed prefix.
   Computing the prepared target alone never grants permission. Explicit
   projections recover the existing admitted-event presentation. *)

let tc_prepared_word_target = new_recursive_definition list_RECURSION
 `(tc_prepared_word_target (result:S->E->S) [] s = s) /\
  (tc_prepared_word_target result (CONS event events) s =
     tc_prepared_word_target result events (result s event))`;;

let tc_prepared_word_domain = new_recursive_definition list_RECURSION
 `(tc_prepared_word_domain (preparation:S->E->bool) result allow [] s <=> T) /\
  (tc_prepared_word_domain preparation result allow (CONS event events) s <=>
     preparation s event /\ allow s event /\
     tc_prepared_word_domain preparation result allow events (result s event))`;;

let TC_PREPARED_WORD_TARGET_APPEND = prove
 (`!(result:S->E->S) first second s.
     tc_prepared_word_target result (APPEND first second) s =
       tc_prepared_word_target result second (tc_prepared_word_target result first s)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; tc_prepared_word_target]);;

let TC_PREPARED_WORD_DOMAIN_APPEND = prove
 (`!(preparation:S->E->bool) result allow first second s.
     tc_prepared_word_domain preparation result allow (APPEND first second) s <=>
       tc_prepared_word_domain preparation result allow first s /\
       tc_prepared_word_domain preparation result allow second (tc_prepared_word_target result first s)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`s:S`,`s:S`) THEN SPEC_TAC(`second:E list`,`second:E list`) THEN
  SPEC_TAC(`first:E list`,`first:E list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; tc_prepared_word_domain; tc_prepared_word_target; CONJ_ASSOC]);;

let TC_PREPARED_WORD_PATH_IFF = prove
 (`!(preparation:S->E->bool) result allow events s t.
     tc_path (\source event target. preparation source event /\ allow source event /\
       target = result source event) events s t <=>
       tc_prepared_word_domain preparation result allow events s /\
       t = tc_prepared_word_target result events s`,
  REPEAT GEN_TAC THEN SPEC_TAC(`t:S`,`t:S`) THEN SPEC_TAC(`s:S`,`s:S`) THEN
  SPEC_TAC(`events:E list`,`events:E list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[tc_path; tc_prepared_word_domain; tc_prepared_word_target] THEN MESON_TAC[]);;

let TC_PREPARED_WORD_ADMISSION_IFF = prove
 (`!(preparation:S->F->P->bool) result allow (firing:E->F) (witness:E->P) events s t.
     tc_path (\source event target.
       tc_admitted_event preparation result allow source (firing event) (witness event) target) events s t <=>
     tc_prepared_word_domain (\source event. preparation source (firing event) (witness event))
       (\source event. result source (firing event) (witness event))
       (\source event. allow source (firing event) (witness event)) events s /\
     t = tc_prepared_word_target (\source event. result source (firing event) (witness event)) events s`,
  REPEAT GEN_TAC THEN SPEC_TAC(`t:S`,`t:S`) THEN SPEC_TAC(`s:S`,`s:S`) THEN
  SPEC_TAC(`events:E list`,`events:E list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[tc_path; tc_admitted_event; tc_prepared_event;
    tc_prepared_word_domain; tc_prepared_word_target] THEN MESON_TAC[]);;

let TC_PREPARED_WORD_DEFINED_IFF = prove
 (`!(preparation:S->E->bool) result allow events s.
     (?t. tc_path (\source event target. preparation source event /\ allow source event /\
       target = result source event) events s t) <=>
       tc_prepared_word_domain preparation result allow events s`,
  REWRITE_TAC[TC_PREPARED_WORD_PATH_IFF] THEN MESON_TAC[]);;

let TC_PREPARED_WORD_PERMISSION = prove
 (`!(preparation:S->E->bool) result allow event events s.
     tc_prepared_word_domain preparation result allow (CONS event events) s ==>
       preparation s event /\ allow s event`,
  REWRITE_TAC[tc_prepared_word_domain] THEN MESON_TAC[]);;

let TC_PREPARED_WORD_REFUSED_TARGET_REMAINS = prove
 (`~tc_prepared_word_domain (\s:bool event:bool. T)
       (\s:bool event:bool. ~s) (\s:bool event:bool. F) [F] F /\
    tc_prepared_word_target (\s:bool event:bool. ~s) [F] F = T`,
  REWRITE_TAC[tc_prepared_word_domain; tc_prepared_word_target]);;

let TC_PREPARED_WORD_ORDER_RETAINED = prove
 (`tc_prepared_word_domain (\s:bool event:bool. T)
      (\s:bool event:bool. if event then ~s else F) (\s:bool event:bool. T) [F;T] F /\
    tc_prepared_word_domain (\s:bool event:bool. T)
      (\s:bool event:bool. if event then ~s else F) (\s:bool event:bool. T) [T;F] F /\
    ~(tc_prepared_word_target (\s:bool event:bool. if event then ~s else F) [F;T] F =
      tc_prepared_word_target (\s:bool event:bool. if event then ~s else F) [T;F] F)`,
  REWRITE_TAC[tc_prepared_word_domain; tc_prepared_word_target]);;

let TC_PREPARED_WORD_EQUAL_ENDPOINTS_DISTINCT = prove
 (`tc_path (\s event t. tc_admitted_event (\s:bool f:bool p:bool. T)
       (\s:bool f:bool p:bool. s) (\s:bool f:bool p:bool. T) s event F t) [F] F F /\
    tc_path (\s event t. tc_admitted_event (\s:bool f:bool p:bool. T)
       (\s:bool f:bool p:bool. s) (\s:bool f:bool p:bool. T) s event F t) [T] F F /\
    ~([F] = [T])`,
  REWRITE_TAC[TC_PREPARED_WORD_ADMISSION_IFF; tc_prepared_word_domain; tc_prepared_word_target; CONS_11]);;
