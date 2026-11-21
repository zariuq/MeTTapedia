(* A nontrivial finite-world model: terms are Boolean observations of two
   bits; substitutions are arbitrary maps of worlds. Commitment resets only
   the first bit. All controls use the same model and the same settlement. *)

let tc_world_eq = new_definition
 `tc_world_eq (a:bool) (p:(bool#bool)->bool) q <=> p = q`;;
let tc_world_act = new_definition
 `tc_world_act (h:(bool#bool)->(bool#bool)) (p:(bool#bool)->bool) world = p (h world)`;;
let tc_world_id = new_definition
 `tc_world_id (a:bool) (world:bool#bool) = world`;;
let tc_world_comp = new_definition
 `tc_world_comp (g:(bool#bool)->(bool#bool)) (f:(bool#bool)->(bool#bool)) world = f (g world)`;;
let tc_reset_first = new_definition
 `tc_reset_first (world:bool#bool) = (F,SND world)`;;
let tc_reset_second = new_definition
 `tc_reset_second (world:bool#bool) = (FST world,F)`;;
let tc_y_apart_true = new_definition
 `tc_y_apart_true (p:(bool#bool)->bool) (q:(bool#bool)->bool) <=> p = SND /\ q = (\world. T)`;;
let tc_x_apart_false = new_definition
 `tc_x_apart_false (p:(bool#bool)->bool) (q:(bool#bool)->bool) <=> p = FST /\ q = (\world. F)`;;
let tc_xy_apart = new_definition
 `tc_xy_apart (p:(bool#bool)->bool) (q:(bool#bool)->bool) <=> p = FST /\ q = SND`;;

let TC_WORLD_FRAME = prove
 (`tc_frames (\a:bool. T) (\a:bool p:(bool#bool)->bool. T)
       (\a:bool b:bool h:(bool#bool)->(bool#bool). T)
       tc_world_eq tc_world_act tc_world_id tc_world_comp`,
  REWRITE_TAC[tc_frames; tc_world_eq; tc_world_act; tc_world_id; tc_world_comp; FUN_EQ_THM]
  THEN MESON_TAC[]);;

let TC_WORLD_Y_CONTEXT = prove
 (`tc_constraint_context (\a:bool. T) (\a:bool p:(bool#bool)->bool. T)
       tc_world_eq tc_world_act tc_world_id F tc_y_apart_true`,
  REWRITE_TAC[tc_constraint_context; tc_store; tc_separates;
    tc_y_apart_true; tc_world_eq; tc_world_act; tc_world_id] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(F,F)`) THEN REWRITE_TAC[tc_world_act; tc_world_id; SND]);;

let TC_WORLD_X_CONTEXT = prove
 (`tc_constraint_context (\a:bool. T) (\a:bool p:(bool#bool)->bool. T)
       tc_world_eq tc_world_act tc_world_id F tc_x_apart_false`,
  REWRITE_TAC[tc_constraint_context; tc_store; tc_separates;
    tc_x_apart_false; tc_world_eq; tc_world_act; tc_world_id] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(T,F)`) THEN REWRITE_TAC[tc_world_act; tc_world_id; FST]);;

let TC_RESET_NOT_GLOBALLY_REFLECTING = prove
 (`~tc_faithful (\a:bool p:(bool#bool)->bool. T) tc_world_eq tc_world_act F F tc_reset_first`,
  REWRITE_TAC[tc_faithful; tc_world_eq; tc_world_act; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`FST:(bool#bool)->bool`; `\world:bool#bool. F`] THEN
  REWRITE_TAC[tc_world_act; tc_reset_first; FST; FUN_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(T,F)`) THEN REWRITE_TAC[FST]);;

let TC_RESET_PRESERVES_Y = prove
 (`tc_separates tc_world_eq tc_world_act F tc_reset_first tc_y_apart_true`,
  REWRITE_TAC[tc_separates; tc_y_apart_true; tc_world_eq; tc_world_act] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[tc_reset_first; SND; FUN_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(F,F)`) THEN REWRITE_TAC[tc_world_act; tc_reset_first; SND]);;

let TC_RESET_COLLAPSES_X = prove
 (`~tc_separates tc_world_eq tc_world_act F tc_reset_first tc_x_apart_false`,
  REWRITE_TAC[tc_separates; tc_x_apart_false; tc_world_eq; tc_world_act; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`FST:(bool#bool)->bool`; `\world:bool#bool. F`] THEN
  REWRITE_TAC[tc_world_act; tc_reset_first; FST; FUN_EQ_THM]);;

let TC_WORLD_Y_SOLVABLE = prove
 (`?b f. tc_solution (\a:bool b:bool h:(bool#bool)->(bool#bool). T)
       tc_world_eq tc_world_act F (\p:(bool#bool)->bool q. F) tc_y_apart_true b f`,
  MAP_EVERY EXISTS_TAC [`F`; `tc_world_id F`] THEN
  REWRITE_TAC[tc_solution; tc_models] THEN
  MESON_TAC[TC_WORLD_Y_CONTEXT; tc_constraint_context]);;

let TC_WORLD_X_SOLVABLE = prove
 (`?b f. tc_solution (\a:bool b:bool h:(bool#bool)->(bool#bool). T)
       tc_world_eq tc_world_act F (\p:(bool#bool)->bool q. F) tc_x_apart_false b f`,
  MAP_EVERY EXISTS_TAC [`F`; `tc_world_id F`] THEN
  REWRITE_TAC[tc_solution; tc_models] THEN
  MESON_TAC[TC_WORLD_X_CONTEXT; tc_constraint_context]);;

(* Consumes one occurrence, makes another, and commits X while preserving Y's
   declared inequality. It is admitted by the local construction. *)
let TC_LOCAL_COMMIT_Y_ADMITTED = prove
 (`tc_local_admitted_effect (\a:bool p:(bool#bool)->bool. T)
       (\a:bool b:bool h:(bool#bool)->(bool#bool). T) tc_world_eq tc_world_act
       F F F (tc_world_id F) tc_reset_first
       (\p:(bool#bool)->bool q. F) (\p:(bool#bool)->bool q. F) (\p:(bool#bool)->bool q. F)
       tc_y_apart_true (\occ:bool. ~occ) (\occ:bool. ~occ) (\occ:bool. F)
       (\occ:bool. occ) (\occ:bool. occ) T (\b:bool h:(bool#bool)->(bool#bool). T)`,
  REWRITE_TAC[tc_local_admitted_effect; tc_prepared_effect; tc_store; tc_map_store;
    tc_enabled; tc_fire; TC_RESET_PRESERVES_Y; TC_WORLD_Y_SOLVABLE] THEN MESON_TAC[]);;

let TC_LOCAL_COMMIT_X_REFUSED = prove
 (`~tc_local_admitted_effect (\a:bool p:(bool#bool)->bool. T)
       (\a:bool b:bool h:(bool#bool)->(bool#bool). T) tc_world_eq tc_world_act
       F F F (tc_world_id F) tc_reset_first
       (\p:(bool#bool)->bool q. F) (\p:(bool#bool)->bool q. F) (\p:(bool#bool)->bool q. F)
       tc_x_apart_false (\occ:bool. ~occ) (\occ:bool. ~occ) (\occ:bool. F)
       (\occ:bool. occ) (\occ:bool. occ) T (\b:bool h:(bool#bool)->(bool#bool). T)`,
  REWRITE_TAC[tc_local_admitted_effect; TC_RESET_COLLAPSES_X]);;

(* The same prepared effect is admitted when the guard is asked over the
   separating solutions. Asking over all base solutions would refuse it. *)
let TC_LOCAL_RESTRICTED_GUARD_ADMITTED = prove
 (`tc_local_admitted_effect (\a:bool p:(bool#bool)->bool. T)
       (\a:bool b:bool h:(bool#bool)->(bool#bool). T) tc_world_eq tc_world_act
       F F F (tc_world_id F) (tc_world_id F)
       (\p:(bool#bool)->bool q. F) (\p:(bool#bool)->bool q. F) (\p:(bool#bool)->bool q. F)
       tc_x_apart_false (\occ:bool. ~occ) (\occ:bool. ~occ) (\occ:bool. F)
       (\occ:bool. occ) (\occ:bool. occ) T
       (\b h. tc_separates tc_world_eq tc_world_act b h tc_x_apart_false)`,
  REWRITE_TAC[tc_local_admitted_effect; tc_prepared_effect; tc_store; tc_map_store;
    tc_enabled; tc_fire; TC_WORLD_X_SOLVABLE] THEN
  MESON_TAC[TC_WORLD_X_CONTEXT; tc_constraint_context; tc_solution]);;

let TC_UNRESTRICTED_GUARD_REFUSED = prove
 (`~tc_admitted_effect (\a:bool p:(bool#bool)->bool. T)
       (\a:bool b:bool h:(bool#bool)->(bool#bool). T) tc_world_eq tc_world_act
       F F F (tc_world_id F) (tc_world_id F)
       (\p:(bool#bool)->bool q. F) (\p:(bool#bool)->bool q. F) (\p:(bool#bool)->bool q. F)
       (\occ:bool. ~occ) (\occ:bool. ~occ) (\occ:bool. F)
       (\occ:bool. occ) (\occ:bool. occ) T
       (\b h. tc_separates tc_world_eq tc_world_act b h tc_x_apart_false)`,
  REWRITE_TAC[tc_admitted_effect; tc_entails; tc_models] THEN MESON_TAC[TC_RESET_COLLAPSES_X]);;

let TC_LOCAL_STRICTLY_GENERALIZES_REFLECTION = prove
 (`tc_separates tc_world_eq tc_world_act F tc_reset_first tc_y_apart_true /\
    ~tc_faithful (\a:bool p:(bool#bool)->bool. T) tc_world_eq tc_world_act F F tc_reset_first /\
    ~tc_separates tc_world_eq tc_world_act F tc_reset_first tc_x_apart_false`,
  MESON_TAC[TC_RESET_PRESERVES_Y; TC_RESET_NOT_GLOBALLY_REFLECTING; TC_RESET_COLLAPSES_X]);;

(* Separate compatibility at the old context is insufficient for scheduling
   both commits. Composition checks the second against the transported context. *)
let TC_RESETS_SEPARATELY_COMPATIBLE = prove
 (`tc_separates tc_world_eq tc_world_act F tc_reset_first tc_xy_apart /\
   tc_separates tc_world_eq tc_world_act F tc_reset_second tc_xy_apart`,
  REWRITE_TAC[tc_separates; tc_xy_apart; tc_world_eq] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(T,T)`) THEN
  REWRITE_TAC[tc_world_act; tc_reset_first; tc_reset_second; FST; SND]);;

let TC_RESETS_JOINTLY_CONFLICT = prove
 (`~tc_separates tc_world_eq tc_world_act F
       (tc_world_comp tc_reset_second tc_reset_first) tc_xy_apart`,
  REWRITE_TAC[tc_separates; tc_xy_apart; tc_world_eq; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`FST:(bool#bool)->bool`; `SND:(bool#bool)->bool`] THEN
  REWRITE_TAC[FUN_EQ_THM; tc_world_act; tc_world_comp; tc_reset_first; tc_reset_second; FST; SND]);;
