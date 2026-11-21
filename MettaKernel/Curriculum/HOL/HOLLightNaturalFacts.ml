(* Derived arithmetic proof input for the retained source exporter. *)

let NAT_CARRIER_INFINITY = prove
 (`?s:num->num.
      (!m n:num. s m = s n ==> m = n) /\
      (?m:num. !n:num. ~(s n = m))`,
  EXISTS_TAC `SUC` THEN CONJ_TAC THENL
   [MESON_TAC[SUC_INJ]; EXISTS_TAC `0` THEN REWRITE_TAC[NOT_SUC]]);;

let dump_natural_fact_closure prefix =
  dump_structured_proof_closures prefix
   ["num_RECURSION", num_RECURSION;
    "num_INDUCTION", num_INDUCTION;
    "NOT_SUC", NOT_SUC;
    "SUC_INJ", SUC_INJ;
    "NAT_CARRIER_INFINITY", NAT_CARRIER_INFINITY];;
