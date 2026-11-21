(* Coexistence is total on configurations. Equation predicates retain
   membership, while occurrence predicates retain identity. Neither operation
   asserts consistent knowledge, separate ownership or stable admission. *)

let tc_parallel_store = new_definition
 `tc_parallel_store (left:T->T->bool) right x y <=> left x y \/ right x y`;;

let tc_parallel_present = new_definition
 `tc_parallel_present (left:O->bool) right occ <=> left occ \/ right occ`;;

let TC_PAR_STORE_ASSOC = prove
 (`!(left:T->T->bool) middle right.
     tc_parallel_store (tc_parallel_store left middle) right =
       tc_parallel_store left (tc_parallel_store middle right)`,
  REWRITE_TAC[FUN_EQ_THM; tc_parallel_store] THEN MESON_TAC[]);;

let TC_PAR_STORE_UNIT = prove
 (`!(store:T->T->bool).
     tc_parallel_store (\x y. F) store = store /\
     tc_parallel_store store (\x y. F) = store`,
  REWRITE_TAC[FUN_EQ_THM; tc_parallel_store]);;

let TC_PAR_STORE_COMM = prove
 (`!(left:T->T->bool) right.
     tc_parallel_store left right = tc_parallel_store right left`,
  REWRITE_TAC[FUN_EQ_THM; tc_parallel_store] THEN MESON_TAC[]);;

let TC_PAR_PRESENT_ASSOC = prove
 (`!(left:O->bool) middle right.
     tc_parallel_present (tc_parallel_present left middle) right =
       tc_parallel_present left (tc_parallel_present middle right)`,
  REWRITE_TAC[FUN_EQ_THM; tc_parallel_present] THEN MESON_TAC[]);;

let TC_PAR_PRESENT_UNIT = prove
 (`!(present:O->bool).
     tc_parallel_present (\occ. F) present = present /\
     tc_parallel_present present (\occ. F) = present`,
  REWRITE_TAC[FUN_EQ_THM; tc_parallel_present]);;

let TC_PAR_PRESENT_COMM = prove
 (`!(left:O->bool) right.
     tc_parallel_present left right = tc_parallel_present right left`,
  REWRITE_TAC[FUN_EQ_THM; tc_parallel_present] THEN MESON_TAC[]);;

let TC_PAR_MODELS = prove
 (`!(hom:A->A->H->bool) (eq:A->T->T->bool) act a b sigma left right.
     tc_models hom eq act a b sigma (tc_parallel_store left right) <=>
       tc_models hom eq act a b sigma left /\ tc_models hom eq act a b sigma right`,
  REWRITE_TAC[tc_models; tc_parallel_store] THEN MESON_TAC[]);;

let TC_PAR_SOLVABLE_EXACT = prove
 (`!(hom:A->A->H->bool) (eq:A->T->T->bool) act a left right.
     tc_solvable hom eq act a (tc_parallel_store left right) <=>
       ?b sigma. tc_models hom eq act a b sigma left /\ tc_models hom eq act a b sigma right`,
  REWRITE_TAC[tc_solvable; TC_PAR_MODELS]);;

let TC_PAR_MAP_STORE = prove
 (`!(act:H->T->T) map left right.
     tc_map_store act map (tc_parallel_store left right) =
       tc_parallel_store (tc_map_store act map left) (tc_map_store act map right)`,
  REWRITE_TAC[FUN_EQ_THM; tc_map_store; tc_parallel_store] THEN MESON_TAC[]);;

(* Given local resource enablement, only a collision with a newly made
   occurrence can destroy that enablement under a larger inventory. Guards
   remain a separate admission obligation. *)
let TC_PAR_ENABLED_EXACT = prove
 (`!(present:O->bool) context taken read made.
     tc_enabled present taken read made ==>
       (tc_enabled (tc_parallel_present present context) taken read made <=>
          !occ. made occ ==> ~context occ)`,
  REWRITE_TAC[tc_enabled; tc_parallel_present] THEN MESON_TAC[]);;

let TC_PAR_FIRE_FRAME = prove
 (`!(present:O->bool) context taken made.
     (!occ. taken occ ==> ~context occ) ==>
       tc_fire (tc_parallel_present present context) taken made =
         tc_parallel_present (tc_fire present taken made) context`,
  REWRITE_TAC[FUN_EQ_THM; tc_parallel_present; tc_fire] THEN MESON_TAC[]);;

let TC_PAR_OCCURRENCE_ALIAS = prove
 (`!(present:O->bool). tc_parallel_present present present = present`,
  REWRITE_TAC[FUN_EQ_THM; tc_parallel_present]);;

(* Both readers use the same occurrence identity, without manufacturing a
   second occurrence or consuming the shared one. *)
let TC_PAR_SHARED_READ = prove
 (`tc_enabled (tc_parallel_present (\occ:bool. occ) (\occ:bool. occ))
      (\occ. F) (\occ. occ) (\occ. F) /\
    tc_fire (tc_parallel_present (\occ:bool. occ) (\occ:bool. occ))
      (\occ. F) (\occ. F) T`,
  REWRITE_TAC[tc_enabled; tc_parallel_present; tc_fire]);;

let TC_PAR_CONTEXT_ALLOCATION_COLLISION = prove
 (`tc_enabled (\occ:bool. F) (\occ. F) (\occ. F) (\occ. occ) /\
    ~tc_enabled (tc_parallel_present (\occ:bool. F) (\occ. occ))
       (\occ. F) (\occ. F) (\occ. occ)`,
  REWRITE_TAC[tc_enabled; tc_parallel_present] THEN MESON_TAC[]);;

let TC_PAR_TAKE_DESTROYS_CONTEXT = prove
 (`~(tc_fire (tc_parallel_present (\occ:bool. occ) (\occ. occ))
       (\occ. occ) (\occ. F) =
     tc_parallel_present (tc_fire (\occ:bool. occ) (\occ. occ) (\occ. F)) (\occ. occ))`,
  REWRITE_TAC[FUN_EQ_THM; tc_parallel_present; tc_fire] THEN MESON_TAC[]);;
