(* HOL06 - the LCF kernel: theorems built by PRIMITIVE inference rules, no tactics.
   This is the trusted core a MeTTa-hosted HOL kernel must mirror. *)
open HolKernel Parse boolLib bossLib;
val _ = new_theory "HOL06_lcf_kernel";

(* REFL : |- t = t *)
Theorem refl_ex = REFL “x:num”;
(* ASSUME + DISCH : |- p ==> p *)
Theorem imp_id_kernel = DISCH “p:bool” (ASSUME “p:bool”);
(* BETA_CONV : |- (\x. x) y = y *)
Theorem beta_ex = BETA_CONV “(\x:num. x) y”;

val _ = export_theory();
