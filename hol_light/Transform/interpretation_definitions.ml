(* Export the actual defining equations used by the Lean interpretation.
   These names retain declarations; they are not additional correctness claims.
   The full semantic and admission theorem bundle is checked separately. *)

let TC_INTERPRET_IDENTITY = prove
 (concl I_DEF, ACCEPT_TAC I_DEF);;

let TC_INTERPRET_FIRE = prove
 (concl tc_fire, ACCEPT_TAC tc_fire);;
let TC_INTERPRET_MODELS = prove
 (concl tc_models, ACCEPT_TAC tc_models);;
let TC_INTERPRET_SOLVABLE = prove
 (concl tc_solvable, ACCEPT_TAC tc_solvable);;
let TC_INTERPRET_MAP_STORE = prove
 (concl tc_map_store, ACCEPT_TAC tc_map_store);;
let TC_INTERPRET_FRAMES = prove
 (concl tc_frames, ACCEPT_TAC tc_frames);;
let TC_INTERPRET_STORE = prove
 (concl tc_store, ACCEPT_TAC tc_store);;
let TC_INTERPRET_PREPARED_EFFECT = prove
 (concl tc_prepared_effect, ACCEPT_TAC tc_prepared_effect);;
let TC_INTERPRET_SEMANTIC_EFFECT = prove
 (concl tc_semantic_effect, ACCEPT_TAC tc_semantic_effect);;
let TC_INTERPRET_EXACT_KNOWLEDGE = prove
 (concl tc_exact_knowledge, ACCEPT_TAC tc_exact_knowledge);;
let TC_INTERPRET_PREPARED_EVENT = prove
 (concl tc_prepared_event, ACCEPT_TAC tc_prepared_event);;
let TC_INTERPRET_ADMITTED_EVENT = prove
 (concl tc_admitted_event, ACCEPT_TAC tc_admitted_event);;
let TC_INTERPRET_SOLUTION_PREPARATION = prove
 (concl tc_solution_preparation, ACCEPT_TAC tc_solution_preparation);;
let TC_INTERPRET_GUARD_PROFILE = prove
 (concl tc_guard_profile, ACCEPT_TAC tc_guard_profile);;
let TC_INTERPRET_PROFILE_INCLUSION = prove
 (concl tc_profile_inclusion, ACCEPT_TAC tc_profile_inclusion);;
