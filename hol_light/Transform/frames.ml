(* Indexed frames with explicit valid-object, term and morphism predicates.
   The axioms below form a predicate on supplied operations, not new HOL axioms.
   Raw morphisms need only act associatively; their representations need not
   satisfy category equations as HOL equality. *)

let tc_frames = new_definition
 `tc_frames (objects:A->bool) (terms:A->T->bool) (hom:A->A->H->bool)
            eq (act:H->T->T) identity comp <=>
    (!a t. terms a t ==> objects a) /\
    (!a b f. hom a b f ==> objects a /\ objects b) /\
    (!a. objects a ==> hom a a (identity a)) /\
    (!a b c f g. hom a b f /\ hom b c g ==> hom a c (comp g f)) /\
    (!a b f t. hom a b f /\ terms a t ==> terms b (act f t)) /\
    (!a t. terms a t ==> act (identity a) t = t) /\
    (!a b c f g t. hom a b f /\ hom b c g /\ terms a t
       ==> act (comp g f) t = act g (act f t)) /\
    (!a t. terms a t ==> eq a t t) /\
    (!a x y. terms a x /\ terms a y /\ eq a x y ==> eq a y x) /\
    (!a x y z. terms a x /\ terms a y /\ terms a z /\ eq a x y /\ eq a y z
       ==> eq a x z) /\
    (!a b f x y. hom a b f /\ terms a x /\ terms a y /\ eq a x y
       ==> eq b (act f x) (act f y))`;;

let tc_store = new_definition
 `tc_store (terms:A->T->bool) a store <=>
    !x y. store x y ==> terms a x /\ terms a y`;;

let TC_FRAME_OBJECTS = prove
 (`!(objects:A->bool) (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b (f:H).
     tc_frames objects terms hom eq act identity comp /\ hom a b f
     ==> objects a /\ objects b`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_FRAME_ID = prove
 (`!(objects:A->bool) (terms:A->T->bool) hom eq (act:H->T->T) identity comp (a:A).
     tc_frames objects terms hom eq act identity comp /\ objects a
     ==> hom a a (identity a)`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_FRAME_COMP = prove
 (`!(objects:A->bool) (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b c (f:H) g.
     tc_frames objects terms hom eq act identity comp /\ hom a b f /\ hom b c g
     ==> hom a c (comp g f)`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_FRAME_ACT_TYPED = prove
 (`!(objects:A->bool) (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b (f:H) (t:T).
     tc_frames objects terms hom eq act identity comp /\ hom a b f /\ terms a t
     ==> terms b (act f t)`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_FRAME_ACT_ID = prove
 (`!(objects:A->bool) (terms:A->T->bool) hom eq (act:H->T->T) identity comp a (t:T).
     tc_frames objects terms hom eq act identity comp /\ terms a t
     ==> act (identity a) t = t`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_FRAME_ACT_COMP = prove
 (`!(objects:A->bool) (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b c (f:H) g (t:T).
     tc_frames objects terms hom eq act identity comp /\
     hom a b f /\ hom b c g /\ terms a t
     ==> act (comp g f) t = act g (act f t)`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_FRAME_PRESERVES = prove
 (`!(objects:A->bool) (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b (f:H) (x:T) y.
     tc_frames objects terms hom eq act identity comp /\
     hom a b f /\ terms a x /\ terms a y /\ eq a x y
     ==> eq b (act f x) (act f y)`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_STORE_MAP_TYPED = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b e store.
     tc_frames objects terms hom eq act identity comp /\
     tc_store terms a store /\ hom a b e
     ==> tc_store terms b (tc_map_store act e store)`,
  REWRITE_TAC[tc_store; tc_map_store] THEN MESON_TAC[TC_FRAME_ACT_TYPED]);;

let TC_MODELS_MAP_TYPED = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a m b e tau store.
     tc_frames objects terms hom eq act identity comp /\
     tc_store terms a store /\ hom a m e /\ hom m b tau ==>
     (tc_models hom eq act m b tau (tc_map_store act e store) <=>
      tc_models hom eq act a b (comp tau e) store)`,
  REWRITE_TAC[tc_models; tc_map_store; tc_store] THEN
  MESON_TAC[TC_FRAME_COMP; TC_FRAME_ACT_COMP]);;

let TC_MODELS_POSTCOMPOSE = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b c f g store.
     tc_frames objects terms hom eq act identity comp /\ tc_store terms a store /\
     tc_models hom eq act a b f store /\ hom b c g
     ==> tc_models hom eq act a c (comp g f) store`,
  REWRITE_TAC[tc_models; tc_store] THEN
  MESON_TAC[TC_FRAME_COMP; TC_FRAME_ACT_TYPED; TC_FRAME_ACT_COMP; TC_FRAME_PRESERVES]);;

let TC_FRAME_ACT_ASSOC = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp a b c d f g h t.
     tc_frames objects terms hom eq act identity comp /\
     hom a b f /\ hom b c g /\ hom c d h /\ terms a t ==>
     act (comp h (comp g f)) t = act (comp (comp h g) f) t`,
  MESON_TAC[TC_FRAME_COMP; TC_FRAME_ACT_TYPED; TC_FRAME_ACT_COMP]);;

(* A valid frame can have no terms. Enlarging it may introduce terms. *)
let TC_EMPTY_FIBRE_FRAME = prove
 (`tc_frames (\a:bool. T) (\a:bool t:bool. a)
       (\a:bool b:bool h:bool. a ==> b)
       (\a:bool x:bool y:bool. x = y) (\h:bool t:bool. t)
       (\a:bool. F) (\g:bool f:bool. F)`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;

let TC_NO_PHANTOM_MORPHISM = prove
 (`!objects (terms:A->T->bool) hom eq act identity comp a b (f:H).
     tc_frames objects terms hom eq act identity comp /\ ~objects b
     ==> ~hom a b f`,
  MESON_TAC[TC_FRAME_OBJECTS]);;

(* Distinct morphism representations can have identical action. Requiring
   representation-level identity/composition laws would reject this model. *)
let TC_ACTION_WITHOUT_RAW_CATEGORY = prove
 (`tc_frames (\a:bool. T) (\a:bool t:bool. T)
       (\a:bool b:bool h:bool. T)
       (\a:bool x:bool y:bool. x = y) (\h:bool t:bool. t)
       (\a:bool. F) (\g:bool f:bool. F) /\
    ~((\g:bool f:bool. F) ((\a:bool. F) F) T = T)`,
  REWRITE_TAC[tc_frames] THEN MESON_TAC[]);;
