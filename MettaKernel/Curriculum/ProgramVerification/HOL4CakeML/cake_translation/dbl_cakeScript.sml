(* CakeML translation of the verified `dbl` function: HOL4 proves a verified
   CakeML implementation is produced by the translator. *)
open preamble basis ml_translatorLib;
val _ = new_theory "dbl_cake";
val _ = translation_extends "basisProg";

Definition dbl_def:
  dbl (n:num) = n + n
End

(* the translator emits CakeML for dbl together with a correctness certificate *)
val res = translate dbl_def;

val _ = export_theory();
