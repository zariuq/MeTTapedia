(* Semantic knowledge refinement, independently of admission. The literal
   prepared-effect presentation is a stronger profile of this contract. *)

let tc_semantic_effect = new_definition
 `tc_semantic_effect (terms:A->T->bool) (hom:A->A->H->bool) eq act comp
      a m b extension settle old information next
      (present:O->bool) taken (read:O->bool) made after <=>
    tc_store terms a old /\ tc_store terms m information /\ tc_store terms b next /\
    hom a m extension /\ hom m b settle /\
    (!c sigma. tc_models hom eq act m c sigma information ==>
       tc_models hom eq act a c (comp sigma extension) old) /\
    (!c sigma. tc_models hom eq act b c sigma next ==>
       tc_models hom eq act m c (comp sigma settle) information) /\
    (!occ. after occ <=> tc_fire present taken made occ)`;;

let tc_exact_knowledge = new_definition
 `tc_exact_knowledge (hom:A->A->H->bool) (eq:A->T->T->bool)
      (act:H->T->T) (comp:H->H->H) m b (settle:H) information next <=>
    !c sigma. hom b c sigma /\
      tc_models hom eq act m c (comp sigma settle) information ==>
      tc_models hom eq act b c sigma next`;;

let TC_PREPARED_IS_SEMANTIC = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next (present:O->bool) taken read made after.
     tc_frames objects terms hom eq act identity comp /\
     tc_prepared_effect terms hom act a m b extension settle old information next
       present taken read made after ==>
     tc_semantic_effect terms hom eq act comp a m b extension settle old information next
       present taken read made after`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tc_semantic_effect] THEN
  ASM_MESON_TAC[tc_prepared_effect; TC_PREPARED_RESULT_TYPED;
    TC_PREPARED_KNOWLEDGE_BACK; TC_PREPARED_INFO_BACK]);;

let TC_PREPARED_KNOWLEDGE_EXACT = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next (present:O->bool) taken read made after.
     tc_frames objects terms hom eq act identity comp /\
     tc_prepared_effect terms hom act a m b extension settle old information next
       present taken read made after ==>
     tc_exact_knowledge hom eq act comp m b settle information next`,
  REWRITE_TAC[tc_exact_knowledge; tc_prepared_effect; tc_models;
    tc_store; tc_map_store] THEN MESON_TAC[TC_FRAME_ACT_COMP]);;

let TC_ACTION_COMPOSE_ASSOC = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b c extension settle tau t.
     tc_frames objects terms hom eq act identity comp /\
     hom a m extension /\ hom m b settle /\ hom b c tau /\ terms a t ==>
     act (comp (comp tau settle) extension) t =
       act (comp tau (comp settle extension)) t`,
  MESON_TAC[TC_FRAME_COMP; TC_FRAME_ACT_COMP; TC_FRAME_ACT_TYPED]);;

let TC_MODELS_COMPOSE_ASSOC = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b c extension settle tau old.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a old /\
     hom a m extension /\ hom m b settle /\ hom b c tau ==>
     (tc_models hom eq act a c (comp (comp tau settle) extension) old <=>
      tc_models hom eq act a c (comp tau (comp settle extension)) old)`,
  REWRITE_TAC[tc_models; tc_store] THEN
  MESON_TAC[TC_FRAME_COMP; TC_ACTION_COMPOSE_ASSOC]);;

let TC_SEMANTIC_MODELS_ALONG = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       a m b extension settle old information next (present:O->bool) taken read made after c tau.
     tc_frames objects terms hom eq act identity comp /\
     tc_semantic_effect terms hom eq act comp a m b extension settle old information next
       present taken read made after /\ tc_models hom eq act b c tau next ==>
     tc_models hom eq act a c (comp tau (comp settle extension)) old`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `tc_models (hom:A->A->H->bool) eq (act:H->T->T) a c
      ((comp:H->H->H) (comp tau settle) extension) old` ASSUME_TAC THENL
   [ASM_MESON_TAC[tc_semantic_effect];
    ASM_MESON_TAC[TC_MODELS_COMPOSE_ASSOC; tc_semantic_effect; tc_models]]);;

let TC_SEMANTIC_EXACT_MODELS = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T) comp
       a m b extension settle old information next (present:O->bool) taken read made after c tau.
     tc_semantic_effect terms hom eq act comp a m b extension settle old information next
       present taken read made after /\
     tc_exact_knowledge hom eq act comp m b settle information next /\ hom b c tau ==>
     (tc_models hom eq act b c tau next <=>
      tc_models hom eq act m c (comp tau settle) information)`,
  REWRITE_TAC[tc_semantic_effect; tc_exact_knowledge] THEN MESON_TAC[]);;

(* This result is strictly stronger than the empty information and is
   consistent: a constant substitution satisfies its new equation. *)
let TC_STRICT_REFINEMENT_NOT_EXACT = prove
 (`(~tc_exact_knowledge (\a:bool b:bool h:bool->bool. T)
       (\a:bool x:bool y:bool. x = y) (\h:bool->bool t:bool. h t)
       (\g:bool->bool f:bool->bool t:bool. g(f t)) F F (\t:bool. t)
       (\x:bool y:bool. F) (\x:bool y:bool. x = T /\ y = F)) /\
    tc_solvable (\a:bool b:bool h:bool->bool. T)
       (\a:bool x:bool y:bool. x = y) (\h:bool->bool t:bool. h t)
       F (\x:bool y:bool. x = T /\ y = F)`,
  REWRITE_TAC[tc_exact_knowledge; tc_solvable; tc_models] THEN BETA_TAC THEN
  CONJ_TAC THENL
   [DISCH_THEN (MP_TAC o SPEC `\x:bool. x`) THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    EXISTS_TAC `\x:bool. F` THEN REWRITE_TAC[]]);;
