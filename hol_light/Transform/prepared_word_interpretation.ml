(* Actual recursion equations for exact source readback. These roots retain
   the loaded operators and list constructors. The complete-word correctness
   and refusal controls are proved separately in parallel_domains.ml. *)

let TC_PREPARED_WORD_TARGET_NIL = prove
 (`!(result:S->E->S) s. tc_prepared_word_target result [] s = s`,
  REWRITE_TAC[tc_prepared_word_target]);;

let TC_PREPARED_WORD_TARGET_CONS = prove
 (`!(result:S->E->S) event events s.
     tc_prepared_word_target result (CONS event events) s =
       tc_prepared_word_target result events (result s event)`,
  REWRITE_TAC[tc_prepared_word_target]);;

let TC_PREPARED_WORD_DOMAIN_NIL = prove
 (`!(preparation:S->E->bool) result allow s.
     tc_prepared_word_domain preparation result allow [] s`,
  REWRITE_TAC[tc_prepared_word_domain]);;

let TC_PREPARED_WORD_DOMAIN_CONS = prove
 (`!(preparation:S->E->bool) result allow event events s.
     tc_prepared_word_domain preparation result allow (CONS event events) s <=>
       preparation s event /\ allow s event /\
       tc_prepared_word_domain preparation result allow events (result s event)`,
  REWRITE_TAC[tc_prepared_word_domain]);;
