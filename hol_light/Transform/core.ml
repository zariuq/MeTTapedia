(* Transform's relational admission and settlement core.
   Object frames, terms and morphisms have explicit domain predicates. This
   permits empty fibres in HOL's inhabited carrier types. Equation stores are
   predicates on term pairs; their finite-list presentations are separate.
   No solver or decidability assumption is part of these definitions. *)

let tc_enabled = new_definition
 `tc_enabled (present:O->bool) taken read made <=>
    (!occ. taken occ ==> present occ) /\
    (!occ. read occ ==> present occ) /\
    (!occ. ~(taken occ /\ read occ)) /\
    (!occ. made occ ==> ~present occ)`;;

let tc_fire = new_definition
 `tc_fire (present:O->bool) taken made occ <=>
    (present occ /\ ~taken occ) \/ made occ`;;

let tc_models = new_definition
 `tc_models (hom:A->A->H->bool) (eq:A->T->T->bool)
            (act:H->T->T) a b sigma (store:T->T->bool) <=>
    hom a b sigma /\ (!x y. store x y ==> eq b (act sigma x) (act sigma y))`;;

let tc_solvable = new_definition
 `tc_solvable (hom:A->A->H->bool) (eq:A->T->T->bool) act a store <=>
    ?b sigma. tc_models hom eq act a b sigma store`;;

let tc_entails = new_definition
 `tc_entails (hom:A->A->H->bool) (eq:A->T->T->bool) act a store holds <=>
    !b sigma. tc_models hom eq act a b sigma store ==> holds b sigma`;;

let tc_map_store = new_definition
 `tc_map_store (act:H->T->T) e (store:T->T->bool) u v <=>
    ?x y. store x y /\ u = act e x /\ v = act e y`;;

let tc_separates = new_definition
 `tc_separates (eq:A->T->T->bool) (act:H->T->T) b sigma apart <=>
    !x y. apart x y ==> ~eq b (act sigma x) (act sigma y)`;;

let tc_solution = new_definition
 `tc_solution (hom:A->A->H->bool) (eq:A->T->T->bool) act a store apart b sigma <=>
    tc_models hom eq act a b sigma store /\ tc_separates eq act b sigma apart`;;

(* A solution variable may itself encode a later frame and its morphism. *)
let tc_preparable = new_definition
 `tc_preparable ready (solution:S->bool) <=> ready /\ (?s. solution s)`;;

let tc_admits = new_definition
 `tc_admits ready (solution:S->bool) holds <=>
    tc_preparable ready solution /\ (!s. solution s ==> holds s)`;;

let tc_faithful = new_definition
 `tc_faithful (terms:A->T->bool) eq (act:H->T->T) b c j <=>
    !x y. terms b x /\ terms b y /\ eq c (act j x) (act j y)
          ==> eq b x y`;;

(* The common answer frame c may be larger than the original answer frame b.
   Restricting c=b would exclude legitimate fresh-helper settlements. *)
let tc_covers = new_definition
 `tc_covers (terms:A->T->bool) (hom:A->A->H->bool) eq act a r e store settled <=>
    !b sigma. tc_models hom eq act a b sigma store ==>
      ?c j tau. hom b c j /\ tc_faithful terms eq act b c j /\
        tc_models hom eq act r c tau settled /\
        (!t. terms a t ==> eq c (act j (act sigma t)) (act tau (act e t)))`;;

let tc_same_target_covers = new_definition
 `tc_same_target_covers (terms:A->T->bool) (hom:A->A->H->bool) eq act a r e store settled <=>
    !b sigma. tc_models hom eq act a b sigma store ==>
      ?tau. tc_models hom eq act r b tau settled /\
        (!t. terms a t ==> eq b (act sigma t) (act tau (act e t)))`;;

(* The branch index is retained; an individual committing branch need not
   cover the full source family. Each branch must still be sound. *)
let tc_covering_family = new_definition
 `tc_covering_family (source:S->bool) (branch:B->R->bool) recovery <=>
    (!i r. branch i r ==> ?s. recovery s i r) /\
    (!i r s. branch i r /\ recovery s i r ==> source s) /\
    (!s. source s ==> ?i r. branch i r /\ recovery s i r)`;;

let tc_prepares = new_definition
 `tc_prepares (ready:F->bool) (solution:F->S->bool) (preparation:F->P->bool) <=>
    !f. tc_preparable (ready f) (solution f) ==> ?p. preparation f p`;;

let tc_move = new_definition
 `tc_move ready (solution:F->S->bool) holds preparation (result:F->P->W) f w <=>
    tc_admits (ready f) (solution f) (holds f) /\
    (?p. preparation f p /\ w = result f p)`;;

(* Soundness constrains what a result may claim. Coverage is a separate,
   optional property; neither evaluation policy nor a trace is required. *)
let tc_sound = new_definition
 `tc_sound (before:S->bool) (after:R->bool) back <=>
    !r. after r ==> before (back r)`;;

let TC_SOUND_COMPOSE = prove
 (`!before middle after (back:R->S) (earlier:Q->R).
     tc_sound before middle back /\ tc_sound middle after earlier
     ==> tc_sound before after (\r. back (earlier r))`,
  REWRITE_TAC[tc_sound] THEN MESON_TAC[]);;

let TC_COMMIT_IS_SOUND = prove
 (`tc_sound (\s:bool. T) (\s:bool. ~s) (\s. s)`,
  REWRITE_TAC[tc_sound]);;

let TC_READ_SURVIVES = prove
 (`!present taken read made (occ:O).
     tc_enabled present taken read made /\ read occ
     ==> tc_fire present taken made occ`,
  REWRITE_TAC[tc_enabled; tc_fire] THEN MESON_TAC[]);;

let TC_TAKE_REMOVED = prove
 (`!present taken read made (occ:O).
     tc_enabled present taken read made /\ taken occ
     ==> ~tc_fire present taken made occ`,
  REWRITE_TAC[tc_enabled; tc_fire] THEN MESON_TAC[]);;

let TC_MAKE_PRESENT = prove
 (`!present taken made (occ:O). made occ ==> tc_fire present taken made occ`,
  REWRITE_TAC[tc_fire] THEN MESON_TAC[]);;

let TC_READ_TAKE_CONFLICT = prove
 (`!present taken read made (occ:O).
     taken occ /\ read occ ==> ~tc_enabled present taken read made`,
  REWRITE_TAC[tc_enabled] THEN MESON_TAC[]);;

let TC_POSITIVE_FRAME = prove
 (`!present taken read made (extra:O->bool).
     tc_enabled present taken read made /\ (!occ. extra occ ==> ~made occ)
     ==> tc_enabled (\occ. present occ \/ extra occ) taken read made`,
  REWRITE_TAC[tc_enabled] THEN MESON_TAC[]);;

let TC_FIRE_FRAME = prove
 (`!present taken made (extra:O->bool).
     (!occ. extra occ ==> ~taken occ) ==>
     !occ. tc_fire (\occ. present occ \/ extra occ) taken made occ <=>
         tc_fire present taken made occ \/ extra occ`,
  REWRITE_TAC[tc_fire] THEN MESON_TAC[]);;

let TC_MODELS_CONJUNCTION = prove
 (`!(hom:A->A->H->bool) eq act a b sigma one two.
     tc_models hom eq act a b sigma (\x:T y. one x y \/ two x y) <=>
     tc_models hom eq act a b sigma one /\ tc_models hom eq act a b sigma two`,
  REWRITE_TAC[tc_models] THEN MESON_TAC[]);;

let TC_MODELS_TRANSPORT = prove
 (`!(hom:A->A->H->bool) eq (act:H->T->T) comp a r b e tau store.
     hom a r e /\ hom r b tau /\ hom a b (comp tau e) /\
     (!t. act (comp tau e) t = act tau (act e t)) ==>
     (tc_models hom eq act r b tau (tc_map_store act e store) <=>
      tc_models hom eq act a b (comp tau e) store)`,
  REWRITE_TAC[tc_models; tc_map_store] THEN MESON_TAC[]);;

let TC_SETTLEMENT_SOUND = prove
 (`!(hom:A->A->H->bool) eq (act:H->T->T) comp a r b e store.
     hom a r e /\
     (!tau. hom r b tau ==> hom a b (comp tau e)) /\
     (!tau t. hom r b tau ==> act (comp tau e) t = act tau (act e t)) ==>
     tc_sound (\sigma. tc_models hom eq act a b sigma store)
       (\tau. tc_models hom eq act r b tau (tc_map_store act e store))
       (\tau. comp tau e)`,
  REWRITE_TAC[tc_sound; tc_models; tc_map_store] THEN MESON_TAC[]);;

let TC_ADMISSION_CHARACTERIZATION = prove
 (`!ready (solution:S->bool) holds.
     tc_admits ready solution holds <=>
     ready /\ (?s. solution s) /\ (!s. solution s ==> holds s)`,
  REWRITE_TAC[tc_admits; tc_preparable] THEN MESON_TAC[]);;

let TC_EMPTY_IS_NOT_ADMITTED = prove
 (`!ready (holds:S->bool). ~tc_admits ready (\s:S. F) holds`,
  REWRITE_TAC[tc_admits; tc_preparable]);;

let TC_RESTRICTED_GUARD = prove
 (`!ready (solution:S->bool) restriction.
     ready /\ (?s. solution s /\ restriction s) ==>
     tc_admits ready (\s. solution s /\ restriction s) restriction`,
  REWRITE_TAC[tc_admits; tc_preparable] THEN MESON_TAC[]);;

let TC_RESTRICTION_PREPARES = prove
 (`!ready (solution:S->bool) restriction.
     tc_preparable ready (\s. solution s /\ restriction s)
     ==> tc_preparable ready solution`,
  REWRITE_TAC[tc_preparable] THEN MESON_TAC[]);;

let TC_GUARD_RESTRICTION_CONTROL = prove
 (`~tc_admits T (\s:bool. T) (\s. s) /\
    tc_admits T (\s:bool. s) (\s. s) /\
    tc_preparable T (\s:bool. T)`,
  REWRITE_TAC[tc_admits; tc_preparable] THEN MESON_TAC[]);;

let TC_PREPARED_ADMISSION_HAS_RESULT = prove
 (`!ready (solution:F->S->bool) holds preparation (result:F->P->W) f.
     tc_prepares ready solution preparation ==>
     (tc_admits (ready f) (solution f) (holds f) <=>
      ?w. tc_move ready solution holds preparation result f w)`,
  REWRITE_TAC[tc_prepares; tc_move; tc_admits] THEN MESON_TAC[]);;

let TC_FAITHFUL_IDENTITY = prove
 (`!(terms:A->T->bool) eq (act:H->T->T) b i.
     (!t. terms b t ==> act i t = t) ==> tc_faithful terms eq act b b i`,
  REWRITE_TAC[tc_faithful] THEN MESON_TAC[]);;

let TC_FAITHFUL_COMPOSE = prove
 (`!(terms:A->T->bool) eq (act:H->T->T) comp a b c j k.
     tc_faithful terms eq act a b j /\ tc_faithful terms eq act b c k /\
     (!t. terms a t ==> terms b (act j t)) /\
     (!t. terms a t ==> act (comp k j) t = act k (act j t)) ==>
     tc_faithful terms eq act a c (comp k j)`,
  REWRITE_TAC[tc_faithful] THEN MESON_TAC[]);;

let TC_SAME_TARGET_IMPLIES_COVERS = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T) identity a r e store settled.
     tc_same_target_covers terms hom eq act a r e store settled /\
     (!b. hom b b (identity b)) /\ (!b t. act (identity b) t = t)
     ==> tc_covers terms hom eq act a r e store settled`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tc_covers] THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `sigma:H`] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tc_same_target_covers]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:A`; `sigma:H`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:H` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`b:A`; `identity(b:A):H`; `tau:H`] THEN
  ASM_REWRITE_TAC[tc_faithful] THEN MESON_TAC[]);;

let TC_COVERAGE_PRESERVES_SOLVABILITY = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T) a r e store settled.
     tc_covers terms hom eq act a r e store settled /\
     tc_solvable hom eq act a store ==> tc_solvable hom eq act r settled`,
  REWRITE_TAC[tc_covers; tc_solvable] THEN MESON_TAC[]);;

let TC_FAMILY_WITNESS = prove
 (`!source (branch:B->R->bool) recovery.
     tc_covering_family source branch recovery /\ (?s:S. source s)
     ==> ?i r. branch i r`,
  REWRITE_TAC[tc_covering_family] THEN MESON_TAC[]);;

let TC_FAMILY_NO_INVENTION = prove
 (`!(source:S->bool) (branch:B->R->bool) recovery s i r.
     tc_covering_family source branch recovery /\ branch i r /\ recovery s i r
     ==> source s`,
  REWRITE_TAC[tc_covering_family] THEN MESON_TAC[]);;

let TC_TWO_BRANCHES_COVER = prove
 (`tc_covering_family (\s:bool. T) (\i:bool r:bool. r = i)
                     (\s:bool i:bool r:bool. s = r)`,
  REWRITE_TAC[tc_covering_family] THEN MESON_TAC[]);;

let TC_ONE_BRANCH_LOSES_ANSWER = prove
 (`~tc_covering_family (\s:bool. T) (\i:bool r:bool. ~i /\ ~r)
                      (\s:bool i:bool r:bool. s = r)`,
  REWRITE_TAC[tc_covering_family] THEN MESON_TAC[]);;

let TC_UNRELATED_BRANCH_REJECTED = prove
 (`~tc_covering_family (\s:bool. ~s) (\i:bool r:bool. r = i)
                      (\s:bool i:bool r:bool. ~i /\ s = r)`,
  REWRITE_TAC[tc_covering_family] THEN MESON_TAC[]);;

let TC_CAPACITY_IS_NOT_REFUTATION = prove
 (`!ready (solution:S->bool) holds capacity.
     tc_admits ready solution holds /\ ~capacity ==> ?s. solution s`,
  REWRITE_TAC[tc_admits; tc_preparable] THEN MESON_TAC[]);;

let TC_IDENTITY_COVERS = prove
 (`!(terms:A->T->bool) hom eq (act:H->T->T) identity a store.
     (!b. hom b b (identity b)) /\ (!b t. act (identity b) t = t) /\
     (!b t. eq b t t) ==>
     tc_covers terms hom eq act a a (identity a) store store`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[tc_covers] THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `sigma:H`] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`b:A`; `identity(b:A):H`; `sigma:H`] THEN
  ASM_REWRITE_TAC[tc_faithful] THEN MESON_TAC[]);;

let TC_FALSE_SETTLEMENT_NOT_COVERING = prove
 (`~tc_covers (\a:bool t:bool. T) (\a:bool b:bool h:bool->bool. T)
       (\a:bool x:bool y:bool. x = y) (\h:bool->bool t:bool. h t)
       F F (\t:bool. F) (\x:bool y:bool. F) (\x:bool y:bool. F)`,
  REWRITE_TAC[tc_covers] THEN
  DISCH_THEN(MP_TAC o SPECL [`F`; `\t:bool. t`]) THEN
  REWRITE_TAC[tc_models; tc_faithful] THEN MESON_TAC[]);;

let TC_FALSE_SETTLEMENT_STAYS_SOLVABLE = prove
 (`tc_solvable (\a:bool b:bool h:bool->bool. T)
       (\a:bool x:bool y:bool. x = y) (\h:bool->bool t:bool. h t)
       F (\x:bool y:bool. F)`,
  REWRITE_TAC[tc_solvable; tc_models]);;

let TC_FRESH_TARGET_COVERS = prove
 (`tc_covers (\a:bool t:bool. a) (\a:bool b:bool h:bool. a ==> b)
       (\a:bool x:bool y:bool. x = y) (\h:bool t:bool. t)
       F T F (\x:bool y:bool. F) (\x:bool y:bool. F)`,
  REWRITE_TAC[tc_covers; tc_models; tc_faithful] THEN
  MESON_TAC[]);;

let TC_FRESH_TARGET_NOT_SAME_TARGET = prove
 (`~tc_same_target_covers (\a:bool t:bool. a)
       (\a:bool b:bool h:bool. a ==> b)
       (\a:bool x:bool y:bool. x = y) (\h:bool t:bool. t)
       F T F (\x:bool y:bool. F) (\x:bool y:bool. F)`,
  REWRITE_TAC[tc_same_target_covers; tc_models] THEN MESON_TAC[]);;

(* Authoritative theorem inventory for the replay gate. *)
let transform_core_theorems = [
 "TC_SOUND_COMPOSE",TC_SOUND_COMPOSE;
 "TC_COMMIT_IS_SOUND",TC_COMMIT_IS_SOUND;
 "TC_READ_SURVIVES",TC_READ_SURVIVES;
 "TC_TAKE_REMOVED",TC_TAKE_REMOVED;
 "TC_MAKE_PRESENT",TC_MAKE_PRESENT;
 "TC_READ_TAKE_CONFLICT",TC_READ_TAKE_CONFLICT;
 "TC_POSITIVE_FRAME",TC_POSITIVE_FRAME;
 "TC_FIRE_FRAME",TC_FIRE_FRAME;
 "TC_MODELS_CONJUNCTION",TC_MODELS_CONJUNCTION;
 "TC_MODELS_TRANSPORT",TC_MODELS_TRANSPORT;
 "TC_SETTLEMENT_SOUND",TC_SETTLEMENT_SOUND;
 "TC_ADMISSION_CHARACTERIZATION",TC_ADMISSION_CHARACTERIZATION;
 "TC_EMPTY_IS_NOT_ADMITTED",TC_EMPTY_IS_NOT_ADMITTED;
 "TC_RESTRICTED_GUARD",TC_RESTRICTED_GUARD;
 "TC_RESTRICTION_PREPARES",TC_RESTRICTION_PREPARES;
 "TC_GUARD_RESTRICTION_CONTROL",TC_GUARD_RESTRICTION_CONTROL;
 "TC_PREPARED_ADMISSION_HAS_RESULT",TC_PREPARED_ADMISSION_HAS_RESULT;
 "TC_FAITHFUL_IDENTITY",TC_FAITHFUL_IDENTITY;
 "TC_FAITHFUL_COMPOSE",TC_FAITHFUL_COMPOSE;
 "TC_SAME_TARGET_IMPLIES_COVERS",TC_SAME_TARGET_IMPLIES_COVERS;
 "TC_COVERAGE_PRESERVES_SOLVABILITY",TC_COVERAGE_PRESERVES_SOLVABILITY;
 "TC_FAMILY_WITNESS",TC_FAMILY_WITNESS;
 "TC_FAMILY_NO_INVENTION",TC_FAMILY_NO_INVENTION;
 "TC_TWO_BRANCHES_COVER",TC_TWO_BRANCHES_COVER;
 "TC_ONE_BRANCH_LOSES_ANSWER",TC_ONE_BRANCH_LOSES_ANSWER;
 "TC_UNRELATED_BRANCH_REJECTED",TC_UNRELATED_BRANCH_REJECTED;
 "TC_CAPACITY_IS_NOT_REFUTATION",TC_CAPACITY_IS_NOT_REFUTATION;
 "TC_IDENTITY_COVERS",TC_IDENTITY_COVERS;
 "TC_FALSE_SETTLEMENT_NOT_COVERING",TC_FALSE_SETTLEMENT_NOT_COVERING;
 "TC_FALSE_SETTLEMENT_STAYS_SOLVABLE",TC_FALSE_SETTLEMENT_STAYS_SOLVABLE;
 "TC_FRESH_TARGET_COVERS",TC_FRESH_TARGET_COVERS;
 "TC_FRESH_TARGET_NOT_SAME_TARGET",TC_FRESH_TARGET_NOT_SAME_TARGET
];;
