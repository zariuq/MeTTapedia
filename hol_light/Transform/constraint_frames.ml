(* A constraint-indexed frame is a base frame together with its declared
   inequalities. The construction below is a real instance of tc_frames;
   future substitutions must respect the declared target context. *)

let TC_FRAME_EQ_REFL = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a x.
     tc_frames objects terms hom eq act identity comp /\ terms a x ==> eq a x x`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_FRAME_EQ_SYM = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a x y.
     tc_frames objects terms hom eq act identity comp /\ terms a x /\ terms a y /\ eq a x y
     ==> eq a y x`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_FRAME_EQ_TRANS = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a x y z.
     tc_frames objects terms hom eq act identity comp /\ terms a x /\ terms a y /\ terms a z /\
     eq a x y /\ eq a y z ==> eq a x z`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let tc_context_terms = new_definition
 `tc_context_terms (objects:A->bool) (terms:A->T->bool) eq (act:H->T->T) identity
       (point:A#(T->T->bool)) t <=>
    tc_constraint_context objects terms eq act identity (FST point) (SND point) /\
    terms (FST point) t`;;

let tc_context_hom = new_definition
 `tc_context_hom (objects:A->bool) (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       (source:A#(T->T->bool)) (target:A#(T->T->bool)) f <=>
    tc_constraint_context objects terms eq act identity (FST source) (SND source) /\
    tc_constraint_context objects terms eq act identity (FST target) (SND target) /\
    tc_constraint_arrow hom eq act comp (FST source) (SND source) (FST target) (SND target) f`;;

let TC_CONSTRAINT_FRAME_LIFT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp.
     tc_frames objects terms hom eq act identity comp ==>
     tc_frames
       (\point. tc_constraint_context objects terms eq act identity (FST point) (SND point))
       (tc_context_terms objects terms eq act identity)
       (tc_context_hom objects terms hom eq act identity comp)
       (\point x y. eq (FST point) x y) act (\point. identity (FST point)) comp`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[tc_frames; tc_context_terms; tc_context_hom] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MESON_TAC[];
    ASM_MESON_TAC[TC_CONSTRAINT_ARROW_ID; tc_constraint_context];
    ASM_MESON_TAC[TC_CONSTRAINT_ARROW_COMPOSE; tc_constraint_context];
    ASM_MESON_TAC[TC_FRAME_ACT_TYPED; tc_constraint_arrow];
    ASM_MESON_TAC[TC_FRAME_ACT_ID];
    ASM_MESON_TAC[TC_FRAME_ACT_COMP; tc_constraint_arrow];
    ASM_MESON_TAC[TC_FRAME_EQ_REFL];
    ASM_MESON_TAC[TC_FRAME_EQ_SYM];
    ASM_MESON_TAC[TC_FRAME_EQ_TRANS];
    ASM_MESON_TAC[TC_FRAME_PRESERVES; tc_constraint_arrow]]);;

let TC_LOCAL_CONTEXT_HOM_EXACT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b f apart.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a apart /\ hom a b f ==>
     (tc_context_hom objects terms hom eq act identity comp
        (a,apart) (b,tc_map_store act f apart) f <=> tc_separates eq act b f apart)`,
  REWRITE_TAC[tc_context_hom; FST; SND] THEN
  MESON_TAC[TC_LOCAL_PRESERVATION_EXACT; TC_LOCAL_PRESERVATION_SOURCE_VALID;
    TC_CONSTRAINT_ARROW_MAP]);;

let TC_CONTEXT_MODEL_CANONICAL = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a apart b f store.
     tc_frames objects terms hom eq act identity comp /\
     tc_constraint_context objects terms eq act identity a apart ==>
     (tc_models (tc_context_hom objects terms hom eq act identity comp)
        (\point x y. eq (FST point) x y) act (a,apart) (b,tc_map_store act f apart) f store <=>
      tc_solution hom eq act a store apart b f)`,
  REWRITE_TAC[tc_solution; tc_models; FST] THEN
  MESON_TAC[TC_LOCAL_CONTEXT_HOM_EXACT; tc_context_hom; tc_constraint_arrow; tc_constraint_context; FST; SND]);;

let TC_CONTEXT_MODEL_BASE = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a apart b later f store.
     tc_frames objects terms hom eq act identity comp /\
     tc_models (tc_context_hom objects terms hom eq act identity comp)
       (\point x y. eq (FST point) x y) act (a,apart) (b,later) f store ==>
     tc_solution hom eq act a store apart b f`,
  REWRITE_TAC[tc_solution; tc_models; tc_context_hom; FST; SND] THEN
  MESON_TAC[TC_CONSTRAINT_ARROW_SEPARATES; tc_constraint_context; tc_constraint_arrow]);;

let TC_CONSTRAINT_SOLVABLE_EXACT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a apart store.
     tc_frames objects terms hom eq act identity comp /\
     tc_constraint_context objects terms eq act identity a apart ==>
     (tc_solvable (tc_context_hom objects terms hom eq act identity comp)
        (\point x y. eq (FST point) x y) act (a,apart) store <=>
      ?b f. tc_solution hom eq act a store apart b f)`,
  REWRITE_TAC[tc_solvable; EXISTS_PAIR_THM] THEN
  MESON_TAC[TC_CONTEXT_MODEL_BASE; TC_CONTEXT_MODEL_CANONICAL]);;

let TC_CONSTRAINT_ENTAILS_EXACT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a apart store holds.
     tc_frames objects terms hom eq act identity comp /\
     tc_constraint_context objects terms eq act identity a apart ==>
     (tc_entails (tc_context_hom objects terms hom eq act identity comp)
        (\point x y. eq (FST point) x y) act (a,apart) store (\point f. holds (FST point) f) <=>
      !b f. tc_solution hom eq act a store apart b f ==> holds b f)`,
  REWRITE_TAC[tc_entails; FORALL_PAIR_THM; FST; SND] THEN
  MESON_TAC[TC_CONTEXT_MODEL_BASE; TC_CONTEXT_MODEL_CANONICAL]);;

let TC_CONTEXT_STORE_TYPED = prove
 (`!objects (terms:A->T->bool) eq (act:H->T->T) identity a apart store.
     tc_constraint_context objects terms eq act identity a apart /\ tc_store terms a store
     ==> tc_store (tc_context_terms objects terms eq act identity) (a,apart) store`,
  REWRITE_TAC[tc_store; tc_context_terms; FST; SND] THEN MESON_TAC[]);;

let TC_CARRIED_CONTEXT_HOM = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a apart b later f.
     tc_frames objects terms hom eq act identity comp /\
     tc_constraint_context objects terms eq act identity a apart /\
     tc_constraint_context objects terms eq act identity b later /\ hom a b f /\
     (!x y. apart x y ==> later (act f x) (act f y))
     ==> tc_context_hom objects terms hom eq act identity comp (a,apart) (b,later) f`,
  REWRITE_TAC[tc_context_hom; FST; SND] THEN
  MESON_TAC[TC_CONSTRAINT_ARROW_STRENGTHEN; tc_constraint_context]);;

(* Lift the whole prepared effect. Only the inequalities actually carried
   or told at the intermediate frame have to survive its settlement. *)
let TC_LOCAL_PREPARED_EFFECT_LIFT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next beforeApart currentApart
       (present:O->bool) taken read made after.
     tc_frames objects terms hom eq act identity comp /\
     tc_prepared_effect terms hom act a m b extension settle old information next
       present taken read made after /\
     tc_constraint_context objects terms eq act identity a beforeApart /\
     tc_store terms m currentApart /\
     (!x y. beforeApart x y ==> currentApart (act extension x) (act extension y)) /\
     tc_separates eq act b settle currentApart ==>
     tc_prepared_effect (tc_context_terms objects terms eq act identity)
       (tc_context_hom objects terms hom eq act identity comp) act
       (a,beforeApart) (m,currentApart) (b,tc_map_store act settle currentApart)
       extension settle old information next present taken read made after`,
  REWRITE_TAC[tc_prepared_effect] THEN
  MESON_TAC[TC_CONTEXT_STORE_TYPED; TC_CARRIED_CONTEXT_HOM;
    TC_LOCAL_CONTEXT_HOM_EXACT; TC_LOCAL_PRESERVATION_SOURCE_VALID]);;

let TC_LOCAL_ADMISSION_LIFT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next beforeApart currentApart
       (present:O->bool) taken read made after shapes holds.
     tc_frames objects terms hom eq act identity comp /\
     tc_constraint_context objects terms eq act identity a beforeApart /\
     (!x y. beforeApart x y ==> currentApart (act extension x) (act extension y)) /\
     tc_local_admitted_effect terms hom eq act a m b extension settle old information next currentApart
       present taken read made after shapes holds ==>
     tc_admitted_effect (tc_context_terms objects terms eq act identity)
       (tc_context_hom objects terms hom eq act identity comp)
       (\point x y. eq (FST point) x y) act
       (a,beforeApart) (m,currentApart) (b,tc_map_store act settle currentApart)
       extension settle old information next present taken read made after shapes
       (\point f. holds (FST point) f)`,
  REWRITE_TAC[tc_admitted_effect] THEN
  MESON_TAC[TC_LOCAL_PREPARED_EFFECT_LIFT; TC_CONSTRAINT_SOLVABLE_EXACT;
    TC_CONSTRAINT_ENTAILS_EXACT; TC_LOCAL_CURRENT_CONTEXT; tc_local_admitted_effect]);;

let TC_CONTEXT_PREPARED_BASE = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next beforeApart currentApart afterApart
       (present:O->bool) taken read made after.
     tc_prepared_effect (tc_context_terms objects terms eq act identity)
       (tc_context_hom objects terms hom eq act identity comp) act
       (a,beforeApart) (m,currentApart) (b,afterApart)
       extension settle old information next present taken read made after ==>
     tc_prepared_effect terms hom act a m b extension settle old information next
       present taken read made after /\
     tc_constraint_context objects terms eq act identity m currentApart /\
     tc_constraint_context objects terms eq act identity b afterApart`,
  REWRITE_TAC[tc_prepared_effect; tc_context_terms; tc_context_hom;
    tc_constraint_arrow; tc_store; FST; SND] THEN MESON_TAC[]);;

let TC_LOCAL_ADMISSION_REFLECT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next beforeApart currentApart
       (present:O->bool) taken read made after shapes holds.
     tc_frames objects terms hom eq act identity comp /\
     tc_admitted_effect (tc_context_terms objects terms eq act identity)
       (tc_context_hom objects terms hom eq act identity comp)
       (\point x y. eq (FST point) x y) act
       (a,beforeApart) (m,currentApart) (b,tc_map_store act settle currentApart)
       extension settle old information next present taken read made after shapes
       (\point f. holds (FST point) f) ==>
     tc_local_admitted_effect terms hom eq act a m b extension settle old information next currentApart
       present taken read made after shapes holds`,
  REWRITE_TAC[tc_admitted_effect; tc_local_admitted_effect] THEN
  MESON_TAC[TC_CONTEXT_PREPARED_BASE; TC_CONSTRAINT_SOLVABLE_EXACT;
    TC_CONSTRAINT_ENTAILS_EXACT; TC_LOCAL_PRESERVATION_EXACT; tc_constraint_context; tc_prepared_effect]);;

let TC_LOCAL_ADMISSION_EXACT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next beforeApart currentApart
       (present:O->bool) taken read made after shapes holds.
     tc_frames objects terms hom eq act identity comp /\
     tc_constraint_context objects terms eq act identity a beforeApart /\
     (!x y. beforeApart x y ==> currentApart (act extension x) (act extension y)) ==>
     (tc_local_admitted_effect terms hom eq act a m b extension settle old information next currentApart
        present taken read made after shapes holds <=>
      tc_admitted_effect (tc_context_terms objects terms eq act identity)
        (tc_context_hom objects terms hom eq act identity comp)
        (\point x y. eq (FST point) x y) act
        (a,beforeApart) (m,currentApart) (b,tc_map_store act settle currentApart)
        extension settle old information next present taken read made after shapes
        (\point f. holds (FST point) f))`,
  MESON_TAC[TC_LOCAL_ADMISSION_LIFT; TC_LOCAL_ADMISSION_REFLECT]);;
