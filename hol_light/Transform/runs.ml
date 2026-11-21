(* Finite labelled paths retain their event word. The event carrier may hold
   full firing/preparation data. A label-only specialization does not thereby
   claim history-preserving bisimilarity or reconstruction of hidden states. *)

let tc_path = new_recursive_definition list_RECURSION
 `(tc_path (step:S->E->S->bool) [] s t <=> s = t) /\
  (tc_path step (CONS event events) s t <=>
     ?u. step s event u /\ tc_path step events u t)`;;

let tc_pullback = new_recursive_definition list_RECURSION
 `(tc_pullback (back:E->V->V) [] value = value) /\
  (tc_pullback back (CONS event events) value =
     back event (tc_pullback back events value))`;;

let tc_observes = new_definition
 `tc_observes (step:S->E->S->bool) (observe:S->Q) events s answer <=>
    ?t. tc_path step events s t /\ answer = observe t`;;

let tc_simulates = new_definition
 `tc_simulates (step:S->E->S->bool) (target:U->L->U->bool) encode label <=>
    !s event t. step s event t ==> target (encode s) (label event) (encode t)`;;

let tc_bisimulation = new_definition
 `tc_bisimulation (step:S->E->S->bool) (target:U->E->U->bool) relation <=>
    (!s u event t. relation s u /\ step s event t ==>
       ?v. target u event v /\ relation t v) /\
    (!s u event v. relation s u /\ target u event v ==>
       ?t. step s event t /\ relation t v)`;;

let TC_PATH_APPEND = prove
 (`!(step:S->E->S->bool) first second s t.
     tc_path step (APPEND first second) s t <=>
     ?u. tc_path step first s u /\ tc_path step second u t`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; tc_path] THEN MESON_TAC[]);;

let TC_PATH_SINGLETON = prove
 (`!(step:S->E->S->bool) event s t. tc_path step [event] s t <=> step s event t`,
  REWRITE_TAC[tc_path] THEN MESON_TAC[]);;

let TC_PULLBACK_APPEND = prove
 (`!(back:E->V->V) first second value.
     tc_pullback back (APPEND first second) value =
     tc_pullback back first (tc_pullback back second value)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; tc_pullback]);;

let TC_PATH_SOLUTIONS_BACK = prove
 (`!(step:S->E->S->bool) (valid:S->V->bool) back.
     (!s event t value. step s event t /\ valid t value ==> valid s (back event value))
     ==> !events s t value. tc_path step events s t /\ valid t value
           ==> valid s (tc_pullback back events value)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[tc_path; tc_pullback] THEN ASM_MESON_TAC[]);;

(* An actual interpretation of every event as a prepared transform effect
   licenses the path theorem. Pullbacks retain the settlement/extension of
   each event; no equality law on raw morphism composition is assumed. *)
let TC_PREPARED_PATH_MODELS_START = prove
 (`!objects (terms:A->T->bool) hom eq (act:H->T->T) identity comp
       (step:S->E->S->bool) frame knowledge (present:S->O->bool)
       target extension settle information taken read made c.
     tc_frames objects terms hom eq act identity comp /\
     (!s event t. step s event t ==>
       tc_prepared_effect terms hom act (frame s) (target event) (frame t)
         (extension event) (settle event) (knowledge s) (information event) (knowledge t)
         (present s) (taken event) (read event) (made event) (present t)) ==>
     !events s t tau. tc_path step events s t /\
       tc_models hom eq act (frame t) c tau (knowledge t) ==>
       tc_models hom eq act (frame s) c
         (tc_pullback (\event sigma. comp sigma (comp (settle event) (extension event))) events tau)
         (knowledge s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (BETA_RULE (ISPECL
    [`step:S->E->S->bool`;
     `\s:S sigma:H. tc_models (hom:A->A->H->bool) eq (act:H->T->T)
        (frame s) c sigma (knowledge s)`;
     `\event:E sigma:H. (comp:H->H->H) sigma (comp (settle event) (extension event))`]
    TC_PATH_SOLUTIONS_BACK)) THEN
  BETA_TAC THEN ASM_MESON_TAC[TC_PREPARED_MODELS_ALONG]);;

let TC_PATH_INVARIANT = prove
 (`!(step:S->E->S->bool) invariant.
     (!s event t. step s event t /\ invariant s ==> invariant t)
     ==> !events s t. tc_path step events s t /\ invariant s ==> invariant t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[tc_path] THEN ASM_MESON_TAC[]);;

let TC_PATH_SIMULATION = prove
 (`!(step:S->E->S->bool) (target:U->L->U->bool) encode label.
     tc_simulates step target encode label ==>
     !events s t. tc_path step events s t ==>
       tc_path target (MAP label events) (encode s) (encode t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tc_simulates] THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[tc_path; MAP] THEN ASM_MESON_TAC[]);;

let TC_BISIMULATION_SYMMETRIC = prove
 (`!(step:S->E->S->bool) (target:U->E->U->bool) relation.
     tc_bisimulation step target relation ==>
     tc_bisimulation target step (\u s. relation s u)`,
  REWRITE_TAC[tc_bisimulation] THEN MESON_TAC[]);;

let TC_PATH_BISIMULATION = prove
 (`!(step:S->E->S->bool) (target:U->E->U->bool) relation.
     tc_bisimulation step target relation ==>
     !events s u t. relation s u /\ tc_path step events s t ==>
       ?v. tc_path target events u v /\ relation t v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tc_bisimulation] THEN STRIP_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[tc_path] THEN ASM_MESON_TAC[]);;

let TC_PATH_BISIMULATION_BACK = prove
 (`!(step:S->E->S->bool) (target:U->E->U->bool) relation.
     tc_bisimulation step target relation ==>
     !events s u v. relation s u /\ tc_path target events u v ==>
       ?t. tc_path step events s t /\ relation t v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tc_bisimulation] THEN STRIP_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[tc_path] THEN ASM_MESON_TAC[]);;

let TC_BISIMULATION_OBSERVATIONS = prove
 (`!(step:S->E->S->bool) (target:U->E->U->bool) relation (left:S->Q) right.
     tc_bisimulation step target relation /\
     (!s u. relation s u ==> left s = right u) ==>
     !events s u answer. relation s u ==>
       (tc_observes step left events s answer <=> tc_observes target right events u answer)`,
  REWRITE_TAC[tc_observes] THEN
  MESON_TAC[TC_PATH_BISIMULATION; TC_PATH_BISIMULATION_BACK]);;

let TC_PATH_SWAP = prove
 (`!(step:S->E->S->bool) first second.
     (!s u t. step s first u /\ step u second t ==>
       ?v. step s second v /\ step v first t) ==>
     !rest s t. tc_path step (CONS first (CONS second rest)) s t ==>
       tc_path step (CONS second (CONS first rest)) s t`,
  REWRITE_TAC[tc_path] THEN MESON_TAC[]);;

(* This is a footprint diamond, not a license to commute arbitrary guards. *)
let TC_POSITIVE_FOOTPRINT_DIAMOND = prove
 (`!(present:O->bool) take1 read1 make1 take2 read2 make2.
     tc_enabled present take1 read1 make1 /\ tc_enabled present take2 read2 make2 /\
     (!occ. take1 occ ==> ~take2 occ /\ ~read2 occ) /\
     (!occ. take2 occ ==> ~read1 occ) /\ (!occ. make1 occ ==> ~make2 occ) ==>
     tc_enabled (tc_fire present take1 make1) take2 read2 make2 /\
     tc_enabled (tc_fire present take2 make2) take1 read1 make1 /\
     (!occ. tc_fire (tc_fire present take1 make1) take2 make2 occ <=>
            tc_fire (tc_fire present take2 make2) take1 make1 occ)`,
  REWRITE_TAC[tc_enabled; tc_fire] THEN MESON_TAC[]);;

let tc_absent = new_definition
 `tc_absent (present:O->bool) region <=> !occ. ~(present occ /\ region occ)`;;

let TC_ABSENCE_NOT_FRAMED = prove
 (`tc_absent (\occ:bool. F) (\occ:bool. T) /\
    ~tc_absent (\occ:bool. ~occ) (\occ:bool. T)`,
  REWRITE_TAC[tc_absent] THEN MESON_TAC[]);;

(* The label selects identity or negation. Words compose in execution order. *)
let TC_NONTRIVIAL_TWO_EVENT_PATH = prove
 (`tc_path (\s:bool event:bool t:bool. t = (if event then ~s else s))
       [F;T] F T /\
    ~tc_path (\s:bool event:bool t:bool. t = (if event then ~s else s))
       [F;T] F F`,
  REWRITE_TAC[tc_path] THEN MESON_TAC[]);;

let TC_FORWARD_SIMULATION_NOT_REFLECTION = prove
 (`tc_simulates (\s:bool event:bool t:bool. F)
       (\s:bool event:bool t:bool. T) (\s:bool. s) (\e:bool. e) /\
    tc_path (\s:bool event:bool t:bool. T) [F] F T /\
    ~tc_path (\s:bool event:bool t:bool. F) [F] F T`,
  REWRITE_TAC[tc_simulates; tc_path] THEN MESON_TAC[]);;

let TC_OBSERVER_CAN_FORGET_ENDPOINT = prove
 (`tc_observes (\s:bool event:bool t:bool. T) (\s:bool. F) [F] F F /\
    tc_path (\s:bool event:bool t:bool. T) [F] F F /\
    tc_path (\s:bool event:bool t:bool. T) [F] F T`,
  REWRITE_TAC[tc_observes; tc_path] THEN MESON_TAC[]);;
