(* Forward recording is the continuation instance of the loaded pullback.
   The event word is retained. Records may have state-indexed validity fibres;
   the update law is required only on actual events with valid input records.
   No initial valid record or inhabitant of every valid fibre is assumed. *)

let TC_RECORD_CONTINUATION = prove
 (`!(update:E->R->R) events (continuation:R->R) record.
     tc_pullback (\event next prior. next (update event prior)) events continuation record =
       continuation (tc_pullback (\event next prior. next (update event prior)) events I record)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[tc_pullback; I_THM];
    REPEAT GEN_TAC THEN REWRITE_TAC[tc_pullback] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let TC_RECORD_NIL = prove
 (`!(update:E->R->R) record.
     tc_pullback (\event next prior. next (update event prior)) [] I record = record`,
  REWRITE_TAC[tc_pullback; I_THM]);;

let TC_RECORD_CONS = prove
 (`!(update:E->R->R) event events record.
     tc_pullback (\event next prior. next (update event prior)) (CONS event events) I record =
       tc_pullback (\event next prior. next (update event prior)) events I (update event record)`,
  REWRITE_TAC[tc_pullback]);;

let TC_RECORD_APPEND = prove
 (`!(update:E->R->R) first second record.
     tc_pullback (\event next prior. next (update event prior)) (APPEND first second) I record =
       tc_pullback (\event next prior. next (update event prior)) second I
         (tc_pullback (\event next prior. next (update event prior)) first I record)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TC_PULLBACK_APPEND] THEN
  MATCH_ACCEPT_TAC TC_RECORD_CONTINUATION);;

let TC_RECORD_VALID_FIBRES = prove
 (`!(step:S->E->S->bool) (valid:S->R->bool) (update:E->R->R).
     (!s event t record. step s event t /\ valid s record ==> valid t (update event record)) ==>
     !events s t record. tc_path step events s t /\ valid s record ==>
       valid t (tc_pullback (\event next prior. next (update event prior)) events I record)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[tc_path; TC_RECORD_NIL; TC_RECORD_CONS] THEN ASM_MESON_TAC[]);;

let TC_RECORD_ERASURE = prove
 (`!(step:S->E->S->bool) (update:E->R->R) events s t record.
     tc_path step events s t <=>
       ?final. tc_path step events s t /\
         final = tc_pullback (\event next prior. next (update event prior)) events I record`,
  MESON_TAC[]);;

let TC_RECORD_UNIQUE = prove
 (`!(step:S->E->S->bool) (update:E->R->R) events s t record.
     tc_path step events s t ==>
       ?!final. tc_path step events s t /\
         final = tc_pullback (\event next prior. next (update event prior)) events I record`,
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN MESON_TAC[]);;

(* Distinct ordered words produce different records even when the world
   projection deliberately forgets their labels. *)
let TC_RECORD_ORDER_RETAINED = prove
 (`~(tc_pullback (\event next prior:bool. next event) [F;T] I F =
      tc_pullback (\event next prior:bool. next event) [T;F] I F)`,
  REWRITE_TAC[tc_pullback; I_THM]);;

let TC_RECORD_NO_VALID_INITIAL = prove
 (`!s:bool. ~(?record:bool. (\state record. F) s record)`,
  REWRITE_TAC[]);;
