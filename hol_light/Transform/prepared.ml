(* A prepared effect connects complete before/information/after data.
   Its structural contract is independent of guard admission. It can be
   indexed by any firing and preparation witness; no canonical witness or
   unique result is required. *)

let tc_prepared_effect = new_definition
 `tc_prepared_effect (terms:A->T->bool) (hom:A->A->H->bool) act
      a m b extension settle old information next
      (present:O->bool) taken (read:O->bool) made after <=>
    tc_store terms a old /\ tc_store terms m information /\
    hom a m extension /\ hom m b settle /\
    (!x y. old x y ==> information (act extension x) (act extension y)) /\
    (!x y. next x y <=> tc_map_store act settle information x y) /\
    (!occ. after occ <=> tc_fire present taken made occ)`;;

let tc_admitted_effect = new_definition
 `tc_admitted_effect (terms:A->T->bool) (hom:A->A->H->bool) eq act
      a m b extension settle old information next
      (present:O->bool) taken read made after shapes holds <=>
    tc_prepared_effect terms hom act a m b extension settle old information next
      present taken read made after /\
    shapes /\ tc_enabled present taken read made /\
    tc_solvable hom eq act m information /\ tc_entails hom eq act m information holds`;;

let TC_PREPARED_RESULT_TYPED = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next (present:O->bool) taken read made after.
     tc_frames objects terms hom eq act identity comp /\
     tc_prepared_effect terms hom act a m b extension settle old information next
       present taken read made after ==> tc_store terms b next`,
  REWRITE_TAC[tc_prepared_effect; tc_store; tc_map_store] THEN
  MESON_TAC[TC_FRAME_ACT_TYPED]);;

let TC_PREPARED_INFO_BACK = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next (present:O->bool) taken read made after c tau.
     tc_frames objects terms hom eq act identity comp /\
     tc_prepared_effect terms hom act a m b extension settle old information next
       present taken read made after /\ tc_models hom eq act b c tau next
     ==> tc_models hom eq act m c (comp tau settle) information`,
  REWRITE_TAC[tc_prepared_effect; tc_models; tc_map_store; tc_store] THEN
  MESON_TAC[TC_FRAME_COMP; TC_FRAME_ACT_COMP]);;

let TC_PREPARED_KNOWLEDGE_BACK = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next (present:O->bool) taken read made after c sigma.
     tc_frames objects terms hom eq act identity comp /\
     tc_prepared_effect terms hom act a m b extension settle old information next
       present taken read made after /\ tc_models hom eq act m c sigma information
     ==> tc_models hom eq act a c (comp sigma extension) old`,
  REWRITE_TAC[tc_prepared_effect; tc_models; tc_store] THEN
  MESON_TAC[TC_FRAME_COMP; TC_FRAME_ACT_COMP]);;

let TC_MODELS_ACTION_AGREEMENT = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T) a b f g store.
     tc_store terms a store /\ hom a b f /\ hom a b g /\
     (!t. terms a t ==> act f t = act g t)
     ==> (tc_models hom eq act a b f store <=> tc_models hom eq act a b g store)`,
  REWRITE_TAC[tc_store; tc_models] THEN MESON_TAC[]);;

let TC_PREPARED_MODELS_ALONG = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next (present:O->bool) taken read made after c tau.
     tc_frames objects terms hom eq act identity comp /\
     tc_prepared_effect terms hom act a m b extension settle old information next
       present taken read made after /\ tc_models hom eq act b c tau next
     ==> tc_models hom eq act a c (comp tau (comp settle extension)) old`,
  REWRITE_TAC[tc_prepared_effect; tc_models; tc_map_store; tc_store] THEN
  MESON_TAC[TC_FRAME_COMP; TC_FRAME_ACT_TYPED; TC_FRAME_ACT_COMP]);;

let TC_ADMITTED_START_SOLVABLE = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next (present:O->bool) taken read made after shapes holds.
     tc_frames objects terms hom eq act identity comp /\
     tc_admitted_effect terms hom eq act a m b extension settle old information next
       present taken read made after shapes holds ==> tc_solvable hom eq act a old`,
  REWRITE_TAC[tc_admitted_effect; tc_solvable] THEN
  MESON_TAC[TC_PREPARED_KNOWLEDGE_BACK]);;

let TC_ADMITTED_READ_SURVIVES = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T)
       a m b extension settle old information next (present:O->bool) taken read made after shapes holds occ.
     tc_admitted_effect terms hom eq act a m b extension settle old information next
       present taken read made after shapes holds /\ read occ ==> after occ`,
  REWRITE_TAC[tc_admitted_effect; tc_prepared_effect] THEN MESON_TAC[TC_READ_SURVIVES]);;

let TC_ADMITTED_TAKE_REMOVED = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T)
       a m b extension settle old information next (present:O->bool) taken read made after shapes holds occ.
     tc_admitted_effect terms hom eq act a m b extension settle old information next
       present taken read made after shapes holds /\ taken occ ==> ~after occ`,
  REWRITE_TAC[tc_admitted_effect; tc_prepared_effect] THEN MESON_TAC[TC_TAKE_REMOVED]);;

let TC_PREPARED_MAKE_PRESENT = prove
 (`!(terms:A->T->bool) hom (act:H->T->T)
       a m b extension settle old information next (present:O->bool) taken read made after occ.
     tc_prepared_effect terms hom act a m b extension settle old information next
       present taken read made after /\ made occ ==> after occ`,
  REWRITE_TAC[tc_prepared_effect] THEN MESON_TAC[TC_MAKE_PRESENT]);;

let TC_PREPARATION_IGNORES_GUARD = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T)
       a m b extension settle old information next (present:O->bool) taken read made after shapes guard other.
     tc_admitted_effect terms hom eq act a m b extension settle old information next
       present taken read made after shapes guard /\ tc_entails hom eq act m information other
     ==> tc_admitted_effect terms hom eq act a m b extension settle old information next
       present taken read made after shapes other`,
  REWRITE_TAC[tc_admitted_effect] THEN MESON_TAC[]);;

(* A real occurrence is consumed and another is produced, while settlement
   commits every Boolean term to false. Coverage is deliberately absent. *)
let TC_CONSUMING_COMMIT_ADMITTED = prove
 (`tc_admitted_effect (\a:bool t:bool. T) (\a:bool b:bool h:bool->bool. T)
      (\a:bool x:bool y:bool. x = y) (\h:bool->bool t:bool. h t)
      F F F (\t:bool. t) (\t:bool. F)
      (\x:bool y:bool. F) (\x:bool y:bool. F) (\x:bool y:bool. F)
      (\occ:bool. ~occ) (\occ:bool. ~occ) (\occ:bool. F)
      (\occ:bool. occ) (\occ:bool. occ) T (\b:bool h:bool->bool. T)`,
  REWRITE_TAC[tc_admitted_effect; tc_prepared_effect; tc_store; tc_map_store;
    tc_solvable; tc_entails; tc_models; tc_enabled; tc_fire] THEN MESON_TAC[]);;

let TC_WRONG_OCCURRENCE_RESULT_REJECTED = prove
 (`!terms hom (act:H->T->T) a m b extension settle old information next.
     ~tc_prepared_effect (terms:A->T->bool) hom act a m b extension settle old information next
       (\occ:bool. ~occ) (\occ:bool. ~occ) (\occ:bool. F)
       (\occ:bool. occ) (\occ:bool. ~occ)`,
  REWRITE_TAC[tc_prepared_effect; tc_fire] THEN MESON_TAC[]);;
