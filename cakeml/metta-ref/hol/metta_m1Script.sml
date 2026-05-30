Theory metta_m1
Ancestors
  integer
Libs
  preamble

Datatype:
  atom = Sym num
       | Var num
       | IntLit int
       | StrLit num
       | Expr (atom list)
End

Datatype:
  binding = Bind num atom
End

Definition error_atom_def:
  error_atom subject reason = Expr [Sym 0; subject; reason]
End

Definition is_error_def:
  is_error atom ⇔
    case atom of
    | Expr (Sym 0 :: rest) => T
    | _ => F
End

Definition visible_results_def:
  visible_results [] = [] ∧
  visible_results (x :: xs) =
    if x = Sym 1 then visible_results xs else x :: visible_results xs
End

Definition lookup_bind_def:
  lookup_bind v [] = NONE ∧
  lookup_bind v (Bind w a :: rest) =
    if v = w then SOME a else lookup_bind v rest
End

Definition apply_subst_def:
  apply_subst bs (Sym n) = Sym n ∧
  apply_subst bs (Var v) =
    (case lookup_bind v bs of
     | NONE => Var v
     | SOME a => a) ∧
  apply_subst bs (IntLit i) = IntLit i ∧
  apply_subst bs (StrLit s) = StrLit s ∧
  apply_subst bs (Expr xs) = Expr (MAP (apply_subst bs) xs)
End

Definition bind_var_def:
  bind_var v a bs =
    case lookup_bind v bs of
    | NONE => SOME (Bind v a :: bs)
    | SOME old => if old = a then SOME bs else NONE
End

Definition atom_depth_def:
  atom_depth (Sym n) = 1 ∧
  atom_depth (Var v) = 1 ∧
  atom_depth (IntLit i) = 1 ∧
  atom_depth (StrLit s) = 1 ∧
  atom_depth (Expr xs) = SUC (atom_list_depth xs) ∧
  atom_list_depth [] = 0 ∧
  atom_list_depth (x :: xs) = SUC (atom_depth x + atom_list_depth xs)
End

Theorem atom_depth_pos:
  ∀a. 0 < atom_depth a
Proof
  Induct \\ rw[atom_depth_def]
QED

Theorem atom_depth_mem_lt:
  ∀xs a. MEM a xs ⇒ atom_depth a < atom_depth (Expr xs)
Proof
  Induct \\ rw[atom_depth_def] >-
    (imp_res_tac atom_depth_pos \\ DECIDE_TAC) \\
  res_tac \\ fs[atom_depth_def] \\
  imp_res_tac atom_depth_pos \\ DECIDE_TAC
QED

Definition match_atom_def:
  match_atom (Var v) a bs = bind_var v a bs ∧
  match_atom (Sym x) (Sym y) bs = (if x = y then SOME bs else NONE) ∧
  match_atom (IntLit x) (IntLit y) bs = (if x = y then SOME bs else NONE) ∧
  match_atom (StrLit x) (StrLit y) bs = (if x = y then SOME bs else NONE) ∧
  match_atom (Expr ps) (Expr qs) bs = match_list ps qs bs ∧
  match_atom _ _ bs = NONE ∧
  match_list [] [] bs = SOME bs ∧
  match_list (p :: ps) (q :: qs) bs =
    (case match_atom p q bs of
     | SOME bs2 => match_list ps qs bs2
     | NONE => NONE) ∧
  match_list _ _ bs = NONE
Termination
  WF_REL_TAC
    ‘measure (λx.
       case x of
       | INL (p,q,bs) => atom_depth p + atom_depth q
       | INR (ps,qs,bs) => atom_list_depth ps + atom_list_depth qs)’ \\
  rw[atom_depth_def] \\ DECIDE_TAC
End

Definition match_space_def:
  match_space [] pattern templ = [] ∧
  match_space (entry :: rest) pattern templ =
    case match_atom pattern entry [] of
    | SOME bs => apply_subst bs templ :: match_space rest pattern templ
    | NONE => match_space rest pattern templ
End

Definition equality_step_def:
  equality_step space atom out ⇔
    ∃lhs rhs bs.
      MEM (Expr [Sym 2; lhs; rhs]) space ∧
      match_atom lhs atom [] = SOME bs ∧
      out = apply_subst bs rhs
End

Theorem equality_step_cons:
  ∀space atom out extra.
    equality_step space atom out ⇒
    equality_step (extra :: space) atom out
Proof
  rw[equality_step_def] \\ metis_tac[]
QED

Definition eval_equalities_def:
  eval_equalities [] atom = [] ∧
  eval_equalities (Expr [Sym 2; lhs; rhs] :: rest) atom =
    (case match_atom lhs atom [] of
     | SOME bs => apply_subst bs rhs :: eval_equalities rest atom
     | NONE => eval_equalities rest atom) ∧
  eval_equalities (_ :: rest) atom = eval_equalities rest atom
End

Definition eval_fuel_def:
  eval_fuel 0 space atom = [error_atom atom (Sym 3)] ∧
  eval_fuel (SUC fuel) space atom =
    let rs = eval_equalities space atom in
      if rs = [] then [atom] else rs
End

Definition eval_m1_def:
  eval_m1 0 space atom = [error_atom atom (Sym 3)] ∧
  eval_m1 (SUC fuel) space atom =
    case atom of
    | Expr [Sym 4; Sym 5; pattern; templ] => match_space space pattern templ
    | _ =>
        let rs = eval_equalities space atom in
          if rs = [] then [atom] else rs
End

Datatype:
  builtin_result = BuiltinResult (atom list)
                 | NoBuiltin
End

Definition builtin_eval_def:
  builtin_eval atom =
    case atom of
    | Expr [Sym 6; Var v; value; body] =>
        BuiltinResult [apply_subst [Bind v value] body]
    | Expr [Sym 6; pat; value; body] =>
        BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 7; Sym 8; t; e] => BuiltinResult [t]
    | Expr [Sym 7; Sym 9; t; e] => BuiltinResult [e]
    | Expr [Sym 7; c; t; e] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 11; IntLit x; IntLit y] =>
        BuiltinResult [IntLit (int_add x y)]
    | Expr [Sym 11; a; b] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 12; IntLit x; IntLit y] =>
        BuiltinResult [if int_lt x y then Sym 8 else Sym 9]
    | Expr [Sym 12; a; b] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 13; lhs; rhs; then_atom; else_atom] =>
        (case match_atom lhs rhs [] of
         | SOME bs => BuiltinResult [apply_subst bs then_atom]
         | NONE => BuiltinResult [else_atom])
    | Expr [Sym 14; Expr (x :: xs)] => BuiltinResult [Expr [x; Expr xs]]
    | Expr [Sym 14; a] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 15; head; Expr xs] => BuiltinResult [Expr (head :: xs)]
    | Expr [Sym 15; head; tail] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 16; Expr xs] => BuiltinResult [Expr (visible_results xs)]
    | Expr [Sym 16; a] => BuiltinResult [Expr (visible_results [a])]
    | Expr [Sym 17; Expr xs] => BuiltinResult (visible_results xs)
    | Expr [Sym 17; a] => BuiltinResult [a]
    | _ => NoBuiltin
End

Definition builtin_step_def:
  builtin_step atom out ⇔
    ∃outs. builtin_eval atom = BuiltinResult outs ∧ MEM out outs
End

Definition eval_m1_ext_def:
  eval_m1_ext 0 space atom = [error_atom atom (Sym 3)] ∧
  eval_m1_ext (SUC fuel) space atom =
    case atom of
    | Expr [Sym 4; Sym 5; pattern; templ] => match_space space pattern templ
    | _ =>
        case builtin_eval atom of
        | BuiltinResult outs => outs
        | NoBuiltin =>
            let rs = eval_equalities space atom in
              if rs = [] then [atom] else rs
End

Definition return_payloads_rest_def:
  return_payloads_rest original [] = [] ∧
  return_payloads_rest original (Expr [Sym 19; value] :: rest) =
    value :: return_payloads_rest original rest ∧
  return_payloads_rest original (_ :: rest) =
    error_atom original (Sym 22) :: return_payloads_rest original rest
End

Definition return_payloads_def:
  return_payloads original [] = [error_atom original (Sym 22)] ∧
  return_payloads original (Expr [Sym 19; value] :: rest) =
    value :: return_payloads_rest original rest ∧
  return_payloads original (_ :: rest) = [error_atom original (Sym 22)]
End

Definition eval_m1_rec_def:
  eval_m1_rec 0 space atom = [error_atom atom (Sym 3)] ∧
  eval_m1_rec (SUC fuel) space atom =
    (case atom of
    | Expr [Sym 18; body] =>
        return_payloads atom (eval_m1_rec fuel space body)
    | Expr [Sym 19; value] => [atom]
    | Expr [Sym 20; body] =>
        let rs = eval_m1_rec fuel space body in
          if rs = [body] then [Sym 23] else rs
    | Expr [Sym 21; nested; Var v; templ] =>
        eval_m1_rec_chain fuel space v (eval_m1_rec fuel space nested) templ
    | Expr [Sym 21; nested; bad_var; templ] =>
        [error_atom atom (Sym 10)]
    | _ => eval_m1_ext (SUC fuel) space atom) ∧
  eval_m1_rec_chain fuel space v [] templ = [] ∧
  eval_m1_rec_chain fuel space v (x :: xs) templ =
    eval_m1_rec fuel space (apply_subst [Bind v x] templ) ++
    eval_m1_rec_chain fuel space v xs templ
Termination
  WF_REL_TAC
    ‘inv_image ($< LEX $<)
       (λx. case x of
        | INL (fuel,space,atom) => (fuel,0)
        | INR (fuel,space,v,vals,templ) => (fuel,SUC (LENGTH vals)))’ \\
  rw[] \\ DECIDE_TAC
End

Theorem atom_eq_dec:
  ∀a b : atom. a = b ∨ a ≠ b
Proof
  rw[]
QED

Theorem is_error_error_atom:
  ∀subject reason. is_error (error_atom subject reason)
Proof
  rw[is_error_def, error_atom_def]
QED

Theorem visible_results_no_empty:
  ∀xs. ¬MEM (Sym 1) (visible_results xs)
Proof
  Induct \\ rw[visible_results_def]
QED

Theorem visible_results_member:
  ∀x xs. MEM x (visible_results xs) ⇒ MEM x xs
Proof
  Induct_on ‘xs’ \\ rw[visible_results_def] \\
  Cases_on ‘h = Sym 1’ \\ fs[visible_results_def]
QED

Theorem lookup_bind_hit:
  ∀v a rest. lookup_bind v (Bind v a :: rest) = SOME a
Proof
  rw[lookup_bind_def]
QED

Theorem lookup_bind_miss_cons:
  ∀v w a rest.
    v ≠ w ⇒ lookup_bind v (Bind w a :: rest) = lookup_bind v rest
Proof
  rw[lookup_bind_def]
QED

Theorem lookup_bind_none_not_mem:
  ∀v bs.
    lookup_bind v bs = NONE ⇒
    ¬∃a. MEM (Bind v a) bs
Proof
  Induct_on ‘bs’ \\ rw[lookup_bind_def] \\ Cases_on ‘h’ \\ gvs[lookup_bind_def]
QED

Theorem apply_subst_empty_var:
  ∀v. apply_subst [] (Var v) = Var v
Proof
  rw[apply_subst_def, lookup_bind_def]
QED

Theorem apply_subst_var_hit:
  ∀v a. apply_subst [Bind v a] (Var v) = a
Proof
  rw[apply_subst_def, lookup_bind_def]
QED

Theorem apply_subst_var_miss:
  ∀v w a.
    v ≠ w ⇒ apply_subst [Bind w a] (Var v) = Var v
Proof
  rw[apply_subst_def, lookup_bind_def]
QED

Theorem bind_var_empty_sound:
  ∀v a bs.
    bind_var v a [] = SOME bs ⇒ apply_subst bs (Var v) = a
Proof
  gvs[bind_var_def, lookup_bind_def, apply_subst_def]
QED

Theorem match_var_empty_sound:
  ∀v a bs.
    match_atom (Var v) a [] = SOME bs ⇒ apply_subst bs (Var v) = a
Proof
  EVAL_TAC \\ gvs[lookup_bind_def]
QED

Theorem match_sym_self:
  ∀n bs. match_atom (Sym n) (Sym n) bs = SOME bs
Proof
  EVAL_TAC \\ rw[]
QED

Theorem match_repeated_var_positive:
  ∀v a.
    match_list [Var v; Var v] [a; a] [] = SOME [Bind v a]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem match_repeated_var_negative:
  ∀v a b.
    a ≠ b ⇒ match_list [Var v; Var v] [a; b] [] = NONE
Proof
  rw[] \\ EVAL_TAC \\ rw[]
QED

Theorem match_nested_var_sound:
  ∀f g v a.
    match_atom
      (Expr [Sym f; Expr [Sym g; Var v]])
      (Expr [Sym f; Expr [Sym g; a]])
      [] = SOME [Bind v a] ∧
    apply_subst [Bind v a]
      (Expr [Sym f; Expr [Sym g; Var v]]) =
      Expr [Sym f; Expr [Sym g; a]]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem match_space_member_sound:
  ∀space pattern templ out.
    MEM out (match_space space pattern templ) ⇒
    ∃entry bs.
      MEM entry space ∧
      match_atom pattern entry [] = SOME bs ∧
      out = apply_subst bs templ
Proof
  Induct_on ‘space’ \\ rw[match_space_def] \\
  Cases_on ‘match_atom pattern h []’ \\ gvs[match_space_def] \\ metis_tac[]
QED

Theorem eval_equalities_sound:
  ∀space atom out.
    MEM out (eval_equalities space atom) ⇒
    equality_step space atom out
Proof
  ho_match_mp_tac eval_equalities_ind \\
  rw[eval_equalities_def, equality_step_def] \\
  every_case_tac \\ gvs[equality_step_def] \\
  metis_tac[equality_step_cons]
QED

Theorem eval_fuel_sound:
  ∀fuel space atom out.
    MEM out (eval_fuel fuel space atom) ⇒
    out = atom ∨ out = error_atom atom (Sym 3) ∨
    MEM out (eval_equalities space atom)
Proof
  Cases \\ rw[eval_fuel_def] \\
  Cases_on ‘eval_equalities space atom = []’ \\ gvs[]
QED

Theorem eval_fuel_equality_step_sound:
  ∀fuel space atom out.
    MEM out (eval_fuel fuel space atom) ∧
    out ≠ atom ∧
    out ≠ error_atom atom (Sym 3) ⇒
    equality_step space atom out
Proof
  metis_tac[eval_fuel_sound, eval_equalities_sound]
QED

Theorem eval_fuel_identity_rule:
  ∀fuel f v a.
    eval_fuel (SUC fuel)
      [Expr [Sym 2; Expr [Sym f; Var v]; Var v]]
      (Expr [Sym f; a]) = [a]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_sound:
  ∀fuel space atom out.
    MEM out (eval_m1 fuel space atom) ⇒
    out = atom ∨ out = error_atom atom (Sym 3) ∨
    MEM out (eval_equalities space atom) ∨
    ∃pattern templ.
      atom = Expr [Sym 4; Sym 5; pattern; templ] ∧
      MEM out (match_space space pattern templ)
Proof
  Cases \\ rw[eval_m1_def] \\
  every_case_tac \\ gvs[] \\ metis_tac[]
QED

Theorem eval_m1_step_sound:
  ∀fuel space atom out.
    MEM out (eval_m1 fuel space atom) ⇒
    out = atom ∨ out = error_atom atom (Sym 3) ∨
    equality_step space atom out ∨
    ∃pattern templ.
      atom = Expr [Sym 4; Sym 5; pattern; templ] ∧
      MEM out (match_space space pattern templ)
Proof
  metis_tac[eval_m1_sound, eval_equalities_sound]
QED

Theorem eval_m1_match_member_sound:
  ∀fuel space pattern templ out.
    MEM out (eval_m1 (SUC fuel) space (Expr [Sym 4; Sym 5; pattern; templ])) ⇒
    ∃entry bs.
      MEM entry space ∧
      match_atom pattern entry [] = SOME bs ∧
      out = apply_subst bs templ
Proof
  rw[eval_m1_def] \\ metis_tac[match_space_member_sound]
QED

Theorem eval_m1_match_example:
  ∀fuel p a.
    eval_m1 (SUC fuel)
      [Expr [Sym p; a]]
      (Expr [Sym 4; Sym 5; Expr [Sym p; Var 0]; Var 0]) = [a]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_sound:
  ∀fuel space atom out.
    MEM out (eval_m1_ext fuel space atom) ⇒
    out = atom ∨ out = error_atom atom (Sym 3) ∨
    equality_step space atom out ∨
    builtin_step atom out ∨
    ∃pattern templ.
      atom = Expr [Sym 4; Sym 5; pattern; templ] ∧
      MEM out (match_space space pattern templ)
Proof
  Cases \\ rw[eval_m1_ext_def] \\
  every_case_tac \\ gvs[builtin_step_def] \\
  metis_tac[eval_equalities_sound]
QED

Theorem eval_m1_ext_let_var_example:
  ∀fuel v value body.
    eval_m1_ext (SUC fuel) []
      (Expr [Sym 6; Var v; value; body]) =
    [apply_subst [Bind v value] body]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_if_true_example:
  ∀fuel t e.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 7; Sym 8; t; e]) = [t]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_if_false_example:
  ∀fuel t e.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 7; Sym 9; t; e]) = [e]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_add_example:
  ∀fuel x y.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 11; IntLit x; IntLit y]) =
    [IntLit (int_add x y)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_lt_true_example:
  ∀fuel x y.
    int_lt x y ⇒
    eval_m1_ext (SUC fuel) [] (Expr [Sym 12; IntLit x; IntLit y]) =
    [Sym 8]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_add_bad_arg_example:
  ∀fuel a.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 11; Sym a; IntLit 0]) =
    [error_atom (Expr [Sym 11; Sym a; IntLit 0]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_unify_success_example:
  ∀fuel a good bad.
    eval_m1_ext (SUC fuel) []
      (Expr [Sym 13; Sym a; Sym a; Sym good; bad]) = [Sym good]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_unify_failure_example:
  ∀fuel a b good bad.
    a ≠ b ⇒
    eval_m1_ext (SUC fuel) []
      (Expr [Sym 13; Sym a; Sym b; good; bad]) = [bad]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_decons_example:
  ∀fuel a b.
    eval_m1_ext (SUC fuel) []
      (Expr [Sym 14; Expr [a; b]]) = [Expr [a; Expr [b]]]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_cons_example:
  ∀fuel a b.
    eval_m1_ext (SUC fuel) []
      (Expr [Sym 15; a; Expr [b]]) = [Expr [a; b]]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_collapse_visible_example:
  ∀fuel.
    eval_m1_ext (SUC fuel) []
      (Expr [Sym 16; Expr [Sym 20; Sym 1; Sym 21]]) =
    [Expr [Sym 20; Sym 21]]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_superpose_visible_example:
  ∀fuel.
    eval_m1_ext (SUC fuel) []
      (Expr [Sym 17; Expr [Sym 20; Sym 1; Sym 21]]) =
    [Sym 20; Sym 21]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem return_payloads_two_example:
  ∀original a b.
    return_payloads original
      [Expr [Sym 19; a]; Expr [Sym 19; b]] = [a; b]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_function_return_example:
  ∀fuel a.
    eval_m1_rec (SUC (SUC fuel)) []
      (Expr [Sym 18; Expr [Sym 19; a]]) = [a]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_function_no_return_example:
  ∀fuel n.
    eval_m1_rec (SUC (SUC fuel)) []
      (Expr [Sym 18; Sym n]) =
    [error_atom (Expr [Sym 18; Sym n]) (Sym 22)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_eval_not_reducible_example:
  ∀fuel n.
    eval_m1_rec (SUC (SUC fuel)) []
      (Expr [Sym 20; Sym n]) = [Sym 23]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_chain_after_eval_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC (SUC fuel)))
      [Expr [Sym 2; Expr [Sym 24; Var 0]; Var 0]]
      (Expr [Sym 21;
             Expr [Sym 20; Expr [Sym 24; Sym 25]];
             Var 1;
             Expr [Sym 26; Var 1; Sym 27]]) =
    [Expr [Sym 26; Sym 25; Sym 27]]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_chain_bad_var_example:
  ∀fuel nested templ.
    eval_m1_rec (SUC fuel) []
      (Expr [Sym 21; nested; Sym 0; templ]) =
    [error_atom (Expr [Sym 21; nested; Sym 0; templ]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED
