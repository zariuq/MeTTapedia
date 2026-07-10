(* Real HOL Light calibration for the equality-kernel side.

   Source anchors:
   - fusion.ml exposes the primitive theorem operations.
   - bool.ml defines DISCH from equality-kernel primitives and IMP_DEF.

   This file is run inside HOL Light after hol.ml has loaded. *)

let assert_true label ok =
  if ok then () else failwith ("HOLLightSelfImpSmoke: " ^ label);;

let p = `p:bool`;;

let self_imp = DISCH p (ASSUME p);;
assert_true "SELF_IMP conclusion" (aconv (concl self_imp) (mk_imp(p,p)));;
assert_true "SELF_IMP closed" (hyp self_imp = []);;

let bool_refl = REFL p;;
assert_true "REFL conclusion" (aconv (concl bool_refl) `p <=> p`);;
assert_true "REFL closed" (hyp bool_refl = []);;

print_string "HOL_LIGHT_SELF_IMP_SMOKE_OK\n";;

#quit;;
