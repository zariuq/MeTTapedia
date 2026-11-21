(* Guarded transport proofs assembled from the original derived HOL rules. *)

let guarded_transport_primitives () =
  let laws =
    `(!x:A. G x ==> H (f x) /\ g (f x) = x) /\
     (!x:B. H x ==> G (g x) /\ f (g x) = x)` in
  let assumed = ASSUME laws in
  laws,CONJUNCT1 assumed,CONJUNCT2 assumed;;

let guarded_transport_close laws th =
  GENL [`G:A->bool`; `H:B->bool`; `f:A->B`; `g:B->A`; `P:B->bool`]
    (DISCH laws th);;

let GUARDED_FORALL_TRANSPORT =
  let laws,left,right = guarded_transport_primitives () in
  let source = `!x:A. G x ==> (P:B->bool) (f x)`
  and target = `!x:B. H x ==> P x` in
  let valid_y = ASSUME `(H:B->bool) y` in
  let facts_y = MP (SPEC `y:B` right) valid_y in
  let observed_y = MP (SPEC `g (y:B):A` (ASSUME source)) (CONJUNCT1 facts_y) in
  let at_y = EQ_MP (AP_TERM `P:B->bool` (CONJUNCT2 facts_y)) observed_y in
  let target_at_y = GEN `y:B` (DISCH `(H:B->bool) y` at_y) in
  let target_at_x = EQ_MP (ALPHA (concl target_at_y) target) target_at_y in
  let forwards = DISCH source target_at_x in
  let valid_x = ASSUME `(G:A->bool) x` in
  let facts_x = MP (SPEC `x:A` left) valid_x in
  let at_fx = MP (SPEC `f (x:A):B` (ASSUME target)) (CONJUNCT1 facts_x) in
  let backwards = DISCH target (GEN `x:A` (DISCH `(G:A->bool) x` at_fx)) in
  guarded_transport_close laws (IMP_ANTISYM_RULE forwards backwards);;

let GUARDED_EXISTS_TRANSPORT =
  let laws,left,right = guarded_transport_primitives () in
  let source = `?x:A. G x /\ (P:B->bool) (f x)`
  and target = `?x:B. H x /\ P x` in
  let source_body = ASSUME `G (x:A) /\ (P:B->bool) (f x)` in
  let source_facts = MP (SPEC `x:A` left) (CONJUNCT1 source_body) in
  let at_fx = CONJ (CONJUNCT1 source_facts) (CONJUNCT2 source_body) in
  let target_exists = EXISTS (target,`f (x:A):B`) at_fx in
  let forwards = DISCH source (CHOOSE (`x:A`,ASSUME source) target_exists) in
  let target_body = ASSUME `H (y:B) /\ P y` in
  let target_facts = MP (SPEC `y:B` right) (CONJUNCT1 target_body) in
  let observed_source = EQ_MP (SYM (AP_TERM `P:B->bool` (CONJUNCT2 target_facts)))
    (CONJUNCT2 target_body) in
  let at_gy = CONJ (CONJUNCT1 target_facts) observed_source in
  let source_exists = EXISTS (source,`g (y:B):A`) at_gy in
  let backwards = DISCH target (CHOOSE (`y:B`,ASSUME target) source_exists) in
  guarded_transport_close laws (IMP_ANTISYM_RULE forwards backwards);;
