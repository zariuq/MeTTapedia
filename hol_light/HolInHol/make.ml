(* ========================================================================= *)
(* Load Model (HOL in HOL Light, with Harrison's soundness proof) and the    *)
(* port of Candle's HOL syntax and inference system. Run HOL Light with this *)
(* directory as the working directory and load this file with loadt.         *)
(* ========================================================================= *)

loadt "Model/make.ml";;

loadt "syntax.ml";;
loadt "dbterm.ml";;
loadt "updates.ml";;
loadt "embedding.ml";;
loadt "contexts.ml";;
loadt "kernel_ops.ml";;
