(* From a hypothesis about two functions, derive equality under an abstraction
   and specialize the domain. No axioms or definitions enter the proof. *)
let BINDER_PUBLICATION =
  let a = mk_vartype "A" and b = bool_ty in
  let predicate_type = mk_fun_ty a b in
  new_constant ("cross_pred",predicate_type);
  let f = mk_const ("cross_pred",[]) and g = mk_var ("g",predicate_type)
  and x = mk_var ("x",a) in
  let at_x = MK_COMB (ASSUME (mk_eq (f,g)), REFL x) in
  INST_TYPE [b,a] (ABS x at_x);;
