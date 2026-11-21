(* A preparation witness can be part of a firing's data. This re-indexes
   executions; it does not choose one witness or erase its identity. *)

let tc_witness_step = new_definition
 `tc_witness_step (ready:S->F->bool) (solution:S->F->V->bool) holds
       (preparation:S->F->P->bool) (result:S->F->P->S) s (event:F#P) t <=>
    tc_admits (ready s (FST event)) (solution s (FST event)) (holds s (FST event)) /\
    preparation s (FST event) (SND event) /\ t = result s (FST event) (SND event)`;;

let TC_WITNESS_MOVE_EXACT = prove
 (`!(ready:S->F->bool) (solution:S->F->V->bool) holds preparation (result:S->F->P->S) s f t.
     tc_move (ready s) (solution s) (holds s) (preparation s) (result s) f t <=>
     ?p. tc_witness_step ready solution holds preparation result s (f,p) t`,
  REWRITE_TAC[tc_move; tc_witness_step; FST; SND] THEN MESON_TAC[]);;

let TC_WITNESS_FIXED_EVENT_DETERMINISTIC = prove
 (`!(ready:S->F->bool) (solution:S->F->V->bool) holds preparation (result:S->F->P->S) s event t u.
     tc_witness_step ready solution holds preparation result s event t /\
     tc_witness_step ready solution holds preparation result s event u ==> t = u`,
  REWRITE_TAC[tc_witness_step] THEN MESON_TAC[]);;

let TC_WITNESS_LABEL_SIMULATION = prove
 (`!(ready:S->F->bool) (solution:S->F->V->bool) holds preparation (result:S->F->P->S).
     tc_simulates (tc_witness_step ready solution holds preparation result)
       (\s f t. tc_move (ready s) (solution s) (holds s) (preparation s) (result s) f t)
       (\s:S. s) (FST:F#P->F)`,
  REWRITE_TAC[tc_simulates; tc_witness_step; tc_move] THEN MESON_TAC[]);;

let TC_WITNESS_PATH_ERASURE = prove
 (`!(ready:S->F->bool) (solution:S->F->V->bool) holds preparation (result:S->F->P->S) events s t.
     tc_path (tc_witness_step ready solution holds preparation result) events s t ==>
     tc_path (\s f t. tc_move (ready s) (solution s) (holds s) (preparation s) (result s) f t)
       (MAP FST events) s t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (BETA_RULE (ISPECL
    [`tc_witness_step (ready:S->F->bool) (solution:S->F->V->bool) holds
        (preparation:S->F->P->bool) result`;
     `\s:S f:F t:S. tc_move (ready s) ((solution:S->F->V->bool) s) (holds s)
        ((preparation:S->F->P->bool) s) (result s) f t`;
     `\s:S. s`; `FST:F#P->F`] TC_PATH_SIMULATION)) THEN
  ANTS_TAC THENL
   [MATCH_ACCEPT_TAC (ISPECL
      [`ready:S->F->bool`; `solution:S->F->V->bool`; `holds:S->F->V->bool`;
       `preparation:S->F->P->bool`; `result:S->F->P->S`] TC_WITNESS_LABEL_SIMULATION);
    DISCH_THEN(MP_TAC o SPECL [`events:(F#P)list`; `s:S`; `t:S`]) THEN
    ASM_REWRITE_TAC[]]);;

(* General label refinement: every coarse edge has an actual fine witness.
   This is stronger than a forward-only simulation. *)
let TC_PATH_LABEL_REFINEMENT = prove
 (`!(coarse:S->E->S->bool) (fine:S->F->S->bool) label.
     (!s event t. coarse s event t <=> ?witness. label witness = event /\ fine s witness t) ==>
     !events s t. tc_path coarse events s t ==>
       ?witnesses. MAP label witnesses = events /\ tc_path fine witnesses s t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[tc_path] THEN DISCH_TAC THEN
    EXISTS_TAC `[]:F list` THEN ASM_REWRITE_TAC[MAP; tc_path];
    MAP_EVERY X_GEN_TAC [`event:E`; `events:E list`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`start:S`; `finish:S`] THEN REWRITE_TAC[tc_path] THEN
    DISCH_THEN(X_CHOOSE_THEN `middle:S` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?witness:F. (label:F->E) witness = event /\
        (fine:S->F->S->bool) start witness middle`
      (X_CHOOSE_THEN `witness:F` STRIP_ASSUME_TAC) THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?witnesses:F list. MAP (label:F->E) witnesses = events /\
        tc_path (fine:S->F->S->bool) witnesses middle finish`
      (X_CHOOSE_THEN `witnesses:F list` STRIP_ASSUME_TAC) THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `CONS (witness:F) witnesses` THEN ASM_REWRITE_TAC[MAP; tc_path] THEN
    ASM_MESON_TAC[]]);;

let TC_WITNESS_PATH_REFINEMENT = prove
 (`!(ready:S->F->bool) (solution:S->F->V->bool) holds preparation (result:S->F->P->S).
     !events s t.
     tc_path (\s f t. tc_move (ready s) (solution s) (holds s) (preparation s) (result s) f t) events s t ==>
     ?witnesses. MAP FST witnesses = events /\
       tc_path (tc_witness_step ready solution holds preparation result) witnesses s t`,
  MAP_EVERY X_GEN_TAC
    [`ready:S->F->bool`; `solution:S->F->V->bool`; `holds:S->F->V->bool`;
     `preparation:S->F->P->bool`; `result:S->F->P->S`] THEN
  MATCH_MP_TAC (BETA_RULE (ISPECL
    [`\s:S f:F t:S. tc_move (ready s) ((solution:S->F->V->bool) s) (holds s)
        ((preparation:S->F->P->bool) s) (result s) f t`;
     `tc_witness_step (ready:S->F->bool) (solution:S->F->V->bool) holds
        (preparation:S->F->P->bool) result`;
     `FST:F#P->F`] TC_PATH_LABEL_REFINEMENT)) THEN
  REWRITE_TAC[EXISTS_PAIR_THM; FST; SND; TC_WITNESS_MOVE_EXACT] THEN MESON_TAC[]);;

(* After the declared relabelling, the full transition relations agree at
   every state, not only on completed answers. This ordinary LTS statement
   does not count parallel edges or probability mass. *)
let TC_WITNESS_PUBLIC_BISIMULATION = prove
 (`!(ready:S->F->bool) (solution:S->F->V->bool) holds preparation (result:S->F->P->S).
     tc_bisimulation
       (\s f t. tc_move (ready s) (solution s) (holds s) (preparation s) (result s) f t)
       (\s f t. ?p. tc_witness_step ready solution holds preparation result s (f,p) t)
       (\s:S t:S. s = t)`,
  REWRITE_TAC[tc_bisimulation; TC_WITNESS_MOVE_EXACT] THEN MESON_TAC[]);;

(* Exact observation descent, restricted to valid witnesses. The choice in
   this mathematical factorization is not an execution/scheduling policy. *)
let TC_WITNESS_OBSERVER_DESCENT = prove
 (`!(valid:F->P->bool) (observe:F#P->Q).
     (?erased:F->Q. !f p. valid f p ==> observe (f,p) = erased f) <=>
     (!f p q. valid f p /\ valid f q ==> observe (f,p) = observe (f,q))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[];
    DISCH_TAC THEN EXISTS_TAC `\f:F. (observe:F#P->Q) (f,(@p:P. valid f p))` THEN
    BETA_TAC THEN ASM_MESON_TAC[SELECT_AX]]);;

let TC_TWO_PREPARATIONS_SAME_RESULT = prove
 (`tc_witness_step (\s:bool f:bool. T) (\s:bool f:bool v:bool. T)
       (\s:bool f:bool v:bool. T) (\s:bool f:bool p:bool. T)
       (\s:bool f:bool p:bool. F) F (F,F) F /\
    tc_witness_step (\s:bool f:bool. T) (\s:bool f:bool v:bool. T)
       (\s:bool f:bool v:bool. T) (\s:bool f:bool p:bool. T)
       (\s:bool f:bool p:bool. F) F (F,T) F /\
    ~((F,F) = (F,T))`,
  REWRITE_TAC[tc_witness_step; tc_admits; tc_preparable; FST; SND; PAIR_EQ]);;

let TC_WITNESS_OBSERVER_CANNOT_FORGET = prove
 (`~(?erased:bool->bool. !f p. (SND:bool#bool->bool) (f,p) = erased f)`,
  REWRITE_TAC[SND] THEN MESON_TAC[]);;

let TC_ANSWER_OBSERVER_CAN_FORGET = prove
 (`?erased:bool->bool. !f p. (\event:bool#bool. F) (f,p) = erased f`,
  EXISTS_TAC `\f:bool. F` THEN REWRITE_TAC[]);;
