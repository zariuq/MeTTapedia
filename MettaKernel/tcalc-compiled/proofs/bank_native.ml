(* Accepted artifact and workspace contracts. No unfinished adapter is loaded. *)

needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/flat_fire.ml";;
needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/bank_math.ml";;
needs "../../cesta/adapters/hol/pilot/span_words.ml";;
needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/flat_workspace.ml";;
needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/flat_trace_workspace.ml";;
needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/flat_trace_wide.ml";;
needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/flat_fire_wide.ml";;
needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/mm_sub1_leaf.ml";;

let bank_native_theorems =
 ["FLAT_FIRE_CORRECT",FLAT_FIRE_CORRECT;
  "FLAT_FIRE_TRACED_CORRECT",FLAT_FIRE_TRACED_CORRECT;
  "FLAT_FIRE_FULL_WORKSPACE_CORRECT",FLAT_FIRE_FULL_WORKSPACE_CORRECT;
  "FLAT_FIRE_TRACED_FULL_WORKSPACE_CORRECT",FLAT_FIRE_TRACED_FULL_WORKSPACE_CORRECT;
  "WORDLIST_FROM_MEMORY_SPLIT_32",WORDLIST_FROM_MEMORY_SPLIT_32;
  "WORDLIST_FULL_SPLICE_32",WORDLIST_FULL_SPLICE_32;
  "FLAT_TRACE_APPEND_FULL",FLAT_TRACE_APPEND_FULL;
  "FLAT_TRACE_WIDEN_FULL",FLAT_TRACE_WIDEN_FULL;
  "FLAT_TRACE_COMPOSE_FULL",FLAT_TRACE_COMPOSE_FULL;
  "MM_SUB1_LEAF_INSIDE",MM_SUB1_LEAF_INSIDE;
  "MM_SUB1_LEAF_OUTSIDE",MM_SUB1_LEAF_OUTSIDE];;
