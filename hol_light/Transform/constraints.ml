(* Disequations constrain the terms actually named by a context. Settlement
   need not reflect every possible distinction. The local condition is the
   existing tc_separates predicate, not a second notion of separation. *)

let tc_constraint_context = new_definition
 `tc_constraint_context (objects:A->bool) (terms:A->T->bool) eq (act:H->T->T)
       identity a apart <=>
    objects a /\ tc_store terms a apart /\ tc_separates eq act a (identity a) apart`;;

let TC_SEPARATES_UNION = prove
 (`!(eq:A->T->T->bool) (act:H->T->T) b sigma one two.
     tc_separates eq act b sigma (\x y. one x y \/ two x y) <=>
     tc_separates eq act b sigma one /\ tc_separates eq act b sigma two`,
  REWRITE_TAC[tc_separates] THEN MESON_TAC[]);;

let TC_SEPARATES_WEAKEN = prove
 (`!(eq:A->T->T->bool) (act:H->T->T) b sigma small big.
     (!x y. small x y ==> big x y) /\ tc_separates eq act b sigma big
     ==> tc_separates eq act b sigma small`,
  REWRITE_TAC[tc_separates] THEN MESON_TAC[]);;

let TC_SEPARATES_EMPTY = prove
 (`!(eq:A->T->T->bool) (act:H->T->T) b sigma.
     tc_separates eq act b sigma (\x y. F)`,
  REWRITE_TAC[tc_separates]);;

let TC_SEPARATES_ACTION_AGREEMENT = prove
 (`!(terms:A->T->bool) (eq:A->T->T->bool) (act:H->T->T) a b f g apart.
     tc_store terms a apart /\ (!t. terms a t ==> act f t = act g t) ==>
     (tc_separates eq act b f apart <=> tc_separates eq act b g apart)`,
  REWRITE_TAC[tc_store; tc_separates] THEN MESON_TAC[]);;

let TC_SEPARATES_ASSOC = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b c d f g h apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\
     hom a b f /\ hom b c g /\ hom c d h ==>
     (tc_separates eq act d (comp h (comp g f)) apart <=>
      tc_separates eq act d (comp (comp h g) f) apart)`,
  REWRITE_TAC[tc_separates; tc_store] THEN MESON_TAC[TC_FRAME_ACT_ASSOC]);;

let TC_SEPARATES_COMP_ID = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\
     objects a /\ hom a b f ==>
     (tc_separates eq act b (comp f (identity a)) apart <=> tc_separates eq act b f apart)`,
  REWRITE_TAC[tc_separates; tc_store] THEN
  MESON_TAC[TC_FRAME_ID; TC_FRAME_ACT_ID; TC_FRAME_ACT_COMP]);;

let TC_ACT_LEFT_UNIT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f t.
     tc_frames objects terms hom eq act identity comp /\ hom a b f /\ terms a t
     ==> act (comp (identity b) f) t = act f t`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_SEPARATES_ID_COMP = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\ hom a b f ==>
     (tc_separates eq act b (comp (identity b) f) apart <=> tc_separates eq act b f apart)`,
  REWRITE_TAC[tc_separates; tc_store] THEN MESON_TAC[TC_ACT_LEFT_UNIT]);;

let TC_SEPARATES_MAP_TYPED = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b c f g apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\
     hom a b f /\ hom b c g ==>
     (tc_separates eq act c g (tc_map_store act f apart) <=>
      tc_separates eq act c (comp g f) apart)`,
  REWRITE_TAC[tc_separates; tc_map_store; tc_store] THEN
  MESON_TAC[TC_FRAME_ACT_COMP]);;

let TC_SEPARATES_IDENTITY = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart ==>
     (tc_separates eq act a (identity a) apart <=> !x y. apart x y ==> ~eq a x y)`,
  REWRITE_TAC[tc_separates; tc_store] THEN MESON_TAC[TC_FRAME_ACT_ID]);;

let TC_LOCAL_PRESERVATION_EXACT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\ hom a b f ==>
     (tc_constraint_context objects terms eq act identity b (tc_map_store act f apart) <=>
      tc_separates eq act b f apart)`,
  REWRITE_TAC[tc_constraint_context; tc_store; tc_map_store; tc_separates] THEN
  MESON_TAC[TC_FRAME_OBJECTS; TC_FRAME_ACT_TYPED; TC_FRAME_ACT_ID]);;

let TC_LOCAL_PRESERVATION_SOURCE_VALID = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\ hom a b f /\
     tc_separates eq act b f apart ==>
     tc_constraint_context objects terms eq act identity a apart`,
  REWRITE_TAC[tc_constraint_context; tc_store; tc_separates] THEN
  MESON_TAC[TC_FRAME_OBJECTS; TC_FRAME_ACT_ID; TC_FRAME_PRESERVES]);;

let TC_GLOBAL_REFLECTION_SUFFICES = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f apart.
     tc_frames objects terms hom eq act identity comp /\
     tc_constraint_context objects terms eq act identity a apart /\
     tc_faithful terms eq act a b f ==> tc_separates eq act b f apart`,
  REWRITE_TAC[tc_constraint_context; tc_faithful; tc_store; tc_separates] THEN
  MESON_TAC[TC_FRAME_ACT_ID]);;

(* Global reflection is precisely the uniform requirement over every valid
   inequality context. One firing carrying one context needs only its instance. *)
let TC_REFLECTION_IFF_ALL_CONTEXTS = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f.
     tc_frames objects terms hom eq act identity comp /\ hom a b f ==>
     (tc_faithful terms eq act a b f <=>
      !apart. tc_constraint_context objects terms eq act identity a apart
        ==> tc_separates eq act b f apart)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[TC_GLOBAL_REFLECTION_SUFFICES];
    DISCH_TAC THEN REWRITE_TAC[tc_faithful] THEN
    MAP_EVERY X_GEN_TAC [`x:T`; `y:T`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(eq:A->T->T->bool) a x y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `tc_constraint_context objects (terms:A->T->bool) eq (act:H->T->T) identity a
        (\p:T q:T. p = x /\ q = y)` ASSUME_TAC THENL
      [REWRITE_TAC[tc_constraint_context; tc_store; tc_separates] THEN
       ASM_MESON_TAC[TC_FRAME_OBJECTS; TC_FRAME_ACT_ID]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\p:T q:T. p = x /\ q = y`) THEN
    ASM_REWRITE_TAC[tc_separates] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:T`; `y:T`]) THEN ASM_REWRITE_TAC[]]);;

let TC_LOCAL_PRESERVATION_COMPOSE = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b c f g apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\
     hom a b f /\ hom b c g /\ tc_separates eq act c g (tc_map_store act f apart)
     ==> tc_separates eq act c (comp g f) apart`,
  MESON_TAC[TC_SEPARATES_MAP_TYPED]);;

(* A morphism between declared constraint contexts preserves their future
   solution discipline. It is not required to be globally injective. *)
let tc_constraint_arrow = new_definition
 `tc_constraint_arrow (hom:A->A->H->bool) (eq:A->T->T->bool) act comp
       a apart b later f <=>
    hom a b f /\
    (!c g. hom b c g /\ tc_separates eq act c g later
       ==> tc_separates eq act c (comp g f) apart)`;;

let TC_CONSTRAINT_ARROW_MAP = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\ hom a b f
     ==> tc_constraint_arrow hom eq act comp a apart b (tc_map_store act f apart) f`,
  REWRITE_TAC[tc_constraint_arrow] THEN MESON_TAC[TC_SEPARATES_MAP_TYPED]);;

let TC_CONSTRAINT_ARROW_STRENGTHEN = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f apart later.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\ hom a b f /\
     (!x y. apart x y ==> later (act f x) (act f y))
     ==> tc_constraint_arrow hom eq act comp a apart b later f`,
  REWRITE_TAC[tc_constraint_arrow; tc_separates; tc_store] THEN
  MESON_TAC[TC_FRAME_ACT_COMP]);;

let TC_CONSTRAINT_ARROW_ID = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a apart.
     tc_frames objects terms hom eq act identity comp /\ objects a /\ tc_store terms a apart
     ==> tc_constraint_arrow hom eq act comp a apart a apart (identity a)`,
  REWRITE_TAC[tc_constraint_arrow] THEN MESON_TAC[TC_FRAME_ID; TC_SEPARATES_COMP_ID]);;

let TC_CONSTRAINT_ARROW_COMPOSE = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b c f g one two three.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a one /\
     tc_constraint_arrow hom eq act comp a one b two f /\
     tc_constraint_arrow hom eq act comp b two c three g
     ==> tc_constraint_arrow hom eq act comp a one c three (comp g f)`,
  REWRITE_TAC[tc_constraint_arrow] THEN MESON_TAC[TC_FRAME_COMP; TC_SEPARATES_ASSOC]);;

let TC_CONSTRAINT_ARROW_SEPARATES = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f apart later.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\
     tc_constraint_context objects terms eq act identity b later /\
     tc_constraint_arrow hom eq act comp a apart b later f
     ==> tc_separates eq act b f apart`,
  REWRITE_TAC[tc_constraint_context; tc_constraint_arrow] THEN
  MESON_TAC[TC_FRAME_ID; TC_SEPARATES_ID_COMP]);;

(* Admission quantifies over solutions separating the declared inequalities.
   The settlement check is a structural obligation on this prepared effect. *)
let tc_local_admitted_effect = new_definition
 `tc_local_admitted_effect (terms:A->T->bool) (hom:A->A->H->bool) eq act
       a m b extension settle old information next apart
       (present:O->bool) taken read made after shapes holds <=>
    tc_prepared_effect terms hom act a m b extension settle old information next
      present taken read made after /\
    tc_store terms m apart /\ tc_separates eq act b settle apart /\
    shapes /\ tc_enabled present taken read made /\
    (?c sigma. tc_solution hom eq act m information apart c sigma) /\
    (!c sigma. tc_solution hom eq act m information apart c sigma ==> holds c sigma)`;;

let TC_LOCAL_RESULT_CONTEXT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next apart (present:O->bool) taken read made after shapes holds.
     tc_frames objects terms hom eq act identity comp /\
     tc_local_admitted_effect terms hom eq act a m b extension settle old information next apart
       present taken read made after shapes holds
     ==> tc_constraint_context objects terms eq act identity b (tc_map_store act settle apart)`,
  REWRITE_TAC[tc_local_admitted_effect; tc_prepared_effect] THEN
  MESON_TAC[TC_LOCAL_PRESERVATION_EXACT]);;

let TC_LOCAL_CURRENT_CONTEXT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next apart (present:O->bool) taken read made after shapes holds.
     tc_frames objects terms hom eq act identity comp /\
     tc_local_admitted_effect terms hom eq act a m b extension settle old information next apart
       present taken read made after shapes holds
     ==> tc_constraint_context objects terms eq act identity m apart`,
  REWRITE_TAC[tc_local_admitted_effect; tc_prepared_effect] THEN
  MESON_TAC[TC_LOCAL_PRESERVATION_SOURCE_VALID]);;

let TC_LOCAL_NO_CONSTRAINTS = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T)
       a m b extension settle old information next (present:O->bool) taken read made after shapes holds.
     tc_local_admitted_effect terms hom eq act a m b extension settle old information next (\x y. F)
       present taken read made after shapes holds <=>
     tc_admitted_effect terms hom eq act a m b extension settle old information next
       present taken read made after shapes holds`,
  REWRITE_TAC[tc_local_admitted_effect; tc_admitted_effect; tc_store; tc_solution;
    tc_separates; tc_solvable; tc_entails]);;

let TC_LOCAL_COLLAPSE_REFUSED = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T)
       a m b extension settle old information next apart (present:O->bool) taken read made after shapes holds x y.
     apart x y /\ eq b (act settle x) (act settle y) ==>
     ~tc_local_admitted_effect terms hom eq act a m b extension settle old information next apart
       present taken read made after shapes holds`,
  REWRITE_TAC[tc_local_admitted_effect; tc_separates] THEN MESON_TAC[]);;

let TC_LOCAL_SOLUTION_BACK = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next apart (present:O->bool) taken read made after shapes holds c tau.
     tc_frames objects terms hom eq act identity comp /\
     tc_local_admitted_effect terms hom eq act a m b extension settle old information next apart
       present taken read made after shapes holds /\
     tc_solution hom eq act b next (tc_map_store act settle apart) c tau
     ==> tc_solution hom eq act m information apart c (comp tau settle)`,
  REWRITE_TAC[tc_local_admitted_effect; tc_solution] THEN
  MESON_TAC[TC_PREPARED_INFO_BACK; TC_SEPARATES_MAP_TYPED; tc_prepared_effect; tc_models]);;
