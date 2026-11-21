(* Preparation and permission are separate. The preparation relation retains
   the particular witness; a supplied permission profile selects events.
   No witness existence, guard policy or evaluator is implicit. *)

let tc_prepared_event = new_definition
 `tc_prepared_event (preparation:S->F->P->bool) (result:S->F->P->S) s f p t <=>
    preparation s f p /\ t = result s f p`;;

let tc_admitted_event = new_definition
 `tc_admitted_event (preparation:S->F->P->bool) (result:S->F->P->S) allow s f p t <=>
    tc_prepared_event preparation result s f p t /\ allow s f p`;;

(* A constructor for the solution/guard specialization, not a general default. *)
let tc_solution_preparation = new_definition
 `tc_solution_preparation (ready:S->F->bool) (solution:S->F->V->bool)
       (witness:S->F->P->bool) s f p <=>
    ready s f /\ (?v. solution s f v) /\ witness s f p`;;

let tc_guard_profile = new_definition
 `tc_guard_profile (solution:S->F->V->bool) (holds:S->F->P->V->bool) s f p <=>
    !v. solution s f v ==> holds s f p v`;;

(* Inclusion is required only where the first profile admits a preparation. *)
let tc_profile_inclusion = new_definition
 `tc_profile_inclusion (preparation:S->F->P->bool) first second <=>
    !s f p. preparation s f p /\ first s f p ==> second s f p`;;

let TC_ADMITTED_EVENT_PREPARED = prove
 (`!(preparation:S->F->P->bool) result allow s f p t.
     tc_admitted_event preparation result allow s f p t ==>
     tc_prepared_event preparation result s f p t`,
  REWRITE_TAC[tc_admitted_event] THEN MESON_TAC[]);;

let TC_ADMITTED_EVENT_PERMISSION = prove
 (`!(preparation:S->F->P->bool) result allow s f p t.
     tc_admitted_event preparation result allow s f p t ==> allow s f p`,
  REWRITE_TAC[tc_admitted_event] THEN MESON_TAC[]);;

let TC_ADMITTED_EVENT_FIXED_RESULT = prove
 (`!(preparation:S->F->P->bool) result allow s f p t u.
     tc_admitted_event preparation result allow s f p t /\
     tc_admitted_event preparation result allow s f p u ==> t = u`,
  REWRITE_TAC[tc_admitted_event; tc_prepared_event] THEN MESON_TAC[]);;

let TC_PROFILE_INCLUSION_REFL = prove
 (`!(preparation:S->F->P->bool) allow. tc_profile_inclusion preparation allow allow`,
  REWRITE_TAC[tc_profile_inclusion] THEN MESON_TAC[]);;

let TC_PROFILE_INCLUSION_TRANS = prove
 (`!(preparation:S->F->P->bool) first second third.
     tc_profile_inclusion preparation first second /\
     tc_profile_inclusion preparation second third ==>
     tc_profile_inclusion preparation first third`,
  REWRITE_TAC[tc_profile_inclusion] THEN MESON_TAC[]);;

let TC_PROFILE_INCLUSION_EVENT = prove
 (`!(preparation:S->F->P->bool) result first second s f p t.
     tc_profile_inclusion preparation first second /\
     tc_admitted_event preparation result first s f p t ==>
     tc_admitted_event preparation result second s f p t`,
  REWRITE_TAC[tc_profile_inclusion; tc_admitted_event; tc_prepared_event] THEN MESON_TAC[]);;

let TC_SOLUTION_PREPARATION_EXISTS = prove
 (`!(ready:S->F->bool) (solution:S->F->V->bool) (witness:S->F->P->bool) s f.
     (?p. tc_solution_preparation ready solution witness s f p) <=>
     ready s f /\ (?v. solution s f v) /\ (?p. witness s f p)`,
  REWRITE_TAC[tc_solution_preparation] THEN MESON_TAC[]);;

let TC_GUARD_PROFILE_SPECIALIZATION = prove
 (`!(ready:S->F->bool) (solution:S->F->V->bool) (witness:S->F->P->bool)
       result (holds:S->F->P->V->bool) s f p t.
     tc_admitted_event (tc_solution_preparation ready solution witness) result
       (tc_guard_profile solution holds) s f p t <=>
     tc_admits (ready s f) (solution s f) (holds s f p) /\
       witness s f p /\ t = result s f p`,
  REWRITE_TAC[tc_admitted_event; tc_prepared_event; tc_solution_preparation;
    tc_guard_profile; tc_admits; tc_preparable] THEN MESON_TAC[]);;

let TC_EMPTY_PREPARATION_NO_EVENT = prove
 (`!(result:S->F->P->S) allow s f p t.
     ~tc_admitted_event (\s:S f:F p:P. F) result allow s f p t`,
  REWRITE_TAC[tc_admitted_event; tc_prepared_event]);;

let TC_REFUSAL_RETAINS_PREPARATION = prove
 (`tc_prepared_event (\s:bool f:bool p:bool. p) (\s:bool f:bool p:bool. ~s) F F T T /\
   ~tc_admitted_event (\s:bool f:bool p:bool. p) (\s:bool f:bool p:bool. ~s)
     (\s:bool f:bool p:bool. F) F F T T`,
  REWRITE_TAC[tc_prepared_event; tc_admitted_event]);;

let TC_ADMITTED_PREPARATIONS_RETAIN_IDENTITY = prove
 (`tc_admitted_event (\s:bool f:bool p:bool. T) (\s:bool f:bool p:bool. F)
     (\s:bool f:bool p:bool. T) F F F F /\
   tc_admitted_event (\s:bool f:bool p:bool. T) (\s:bool f:bool p:bool. F)
     (\s:bool f:bool p:bool. T) F F T F /\ ~(F = T)`,
  REWRITE_TAC[tc_admitted_event; tc_prepared_event]);;

let TC_PREPARATIONS_CAN_CHANGE_RESULT = prove
 (`tc_admitted_event (\s:bool f:bool p:bool. T) (\s:bool f:bool p:bool. p)
     (\s:bool f:bool p:bool. T) F F F F /\
   tc_admitted_event (\s:bool f:bool p:bool. T) (\s:bool f:bool p:bool. p)
     (\s:bool f:bool p:bool. T) F F T T`,
  REWRITE_TAC[tc_admitted_event; tc_prepared_event]);;

let TC_PERMISSION_PROTECTS_INVARIANT = prove
 (`!s f p t:bool.
     tc_admitted_event (\s:bool f:bool p:bool. T) (\s:bool f:bool p:bool. p)
       (\s:bool f:bool p:bool. ~p) s f p t ==> ~t`,
  REWRITE_TAC[tc_admitted_event; tc_prepared_event] THEN MESON_TAC[]);;

let TC_RELAXED_PERMISSION_CAN_BREAK_INVARIANT = prove
 (`~tc_admitted_event (\s:bool f:bool p:bool. T) (\s:bool f:bool p:bool. p)
       (\s:bool f:bool p:bool. ~p) F F T T /\
   tc_admitted_event (\s:bool f:bool p:bool. T) (\s:bool f:bool p:bool. p)
       (\s:bool f:bool p:bool. T) F F T T /\ ~(~T)`,
  REWRITE_TAC[tc_admitted_event; tc_prepared_event]);;
