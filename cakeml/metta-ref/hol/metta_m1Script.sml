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
  exported_atom = ESym num
                | EVar num
                | EInt int
                | EStr num
                | EExpr (exported_atom list)
End

Definition export_atom_def:
  export_atom (Sym n) = ESym n ∧
  export_atom (Var v) = EVar v ∧
  export_atom (IntLit i) = EInt i ∧
  export_atom (StrLit s) = EStr s ∧
  export_atom (Expr xs) = EExpr (export_atom_list xs) ∧
  export_atom_list [] = [] ∧
  export_atom_list (x :: xs) = export_atom x :: export_atom_list xs
End

Definition import_exported_atom_def:
  import_exported_atom (ESym n) = Sym n ∧
  import_exported_atom (EVar v) = Var v ∧
  import_exported_atom (EInt i) = IntLit i ∧
  import_exported_atom (EStr s) = StrLit s ∧
  import_exported_atom (EExpr xs) = Expr (import_exported_atom_list xs) ∧
  import_exported_atom_list [] = [] ∧
  import_exported_atom_list (x :: xs) =
    import_exported_atom x :: import_exported_atom_list xs
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

Theorem import_export_atom:
  ∀a. import_exported_atom (export_atom a) = a
Proof
  completeInduct_on ‘atom_depth a’ \\
  rw[] \\
  Cases_on ‘a’ \\ gvs[export_atom_def, import_exported_atom_def] \\
  Induct_on ‘l’ \\ rw[export_atom_def, import_exported_atom_def] \\
  first_x_assum irule \\
  fs[atom_depth_def] \\
  imp_res_tac atom_depth_pos \\
  DECIDE_TAC
QED

Theorem import_export_atom_list:
  ∀xs. import_exported_atom_list (export_atom_list xs) = xs
Proof
  Induct \\ rw[export_atom_def, import_exported_atom_def, import_export_atom]
QED

Theorem import_export_atom_map:
  ∀xs. MAP import_exported_atom (MAP export_atom xs) = xs
Proof
  Induct \\ rw[import_export_atom]
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

Datatype:
  host_impl = HostML | HostNative | HostOther
End

Datatype:
  host_call_profile = HostCall atom atom num int
End

Datatype:
  host_byte_call_profile = HostByteCall atom atom num int int
End

Definition host_impl_def:
  host_impl (Sym 28) = HostML ∧
  host_impl (Sym 29) = HostNative ∧
  host_impl _ = HostOther
End

Definition host_inc_profile_def:
  host_inc_profile tag name args ⇔
    (host_impl tag = HostML ∨ host_impl tag = HostNative) ∧
    name = Sym 30 ∧ ∃arg. args = [arg]
End

Definition host_call_table_def:
  host_call_table =
    [HostCall (Sym 28) (Sym 30) 1 7;
     HostCall (Sym 29) (Sym 30) 1 19]
End

Definition host_byte_call_table_def:
  host_byte_call_table =
    [HostByteCall (Sym 28) (Sym 30) 1 7 1;
     HostByteCall (Sym 28) (Sym 59) 1 7 2;
     HostByteCall (Sym 28) (Sym 60) 1 7 3;
     HostByteCall (Sym 29) (Sym 30) 1 19 1;
     HostByteCall (Sym 29) (Sym 59) 1 19 2;
     HostByteCall (Sym 29) (Sym 60) 1 19 3]
End

Definition host_call_table_lookup_def:
  host_call_table_lookup [] tag name arity = NONE ∧
  host_call_table_lookup
    (HostCall entry_tag entry_name entry_arity conf_len :: rest)
    tag name arity =
    (if entry_tag = tag ∧ entry_name = name ∧ entry_arity = arity
     then SOME conf_len
     else host_call_table_lookup rest tag name arity)
End

Definition host_byte_call_table_lookup_def:
  host_byte_call_table_lookup [] tag name arity = NONE ∧
  host_byte_call_table_lookup
    (HostByteCall entry_tag entry_name entry_arity conf_len opcode :: rest)
    tag name arity =
    (if entry_tag = tag ∧ entry_name = name ∧ entry_arity = arity
     then SOME (conf_len, opcode)
     else host_byte_call_table_lookup rest tag name arity)
End

Definition host_byte_conf_len_def:
  host_byte_conf_len (Sym 28) = SOME 7 ∧
  host_byte_conf_len (Sym 29) = SOME 19 ∧
  host_byte_conf_len _ = NONE
End

Definition host_byte_profile_def:
  host_byte_profile tag name (arity:num) (conf:int) (opcode:int) ⇔
    arity = 1 ∧
    host_byte_conf_len tag = SOME conf ∧
    ((name = Sym 30 ∧ opcode = 1) ∨
     (name = Sym 59 ∧ opcode = 2) ∨
     (name = Sym 60 ∧ opcode = 3))
End

Definition host_eval_profile_def:
  host_eval_profile tag name (arity:num) ⇔
    arity = 1 ∧ (tag = Sym 28 ∨ tag = Sym 29) ∧ name = Sym 30
End

Definition host_byte_only_profile_def:
  host_byte_only_profile tag name arity conf opcode ⇔
    host_byte_profile tag name arity conf opcode ∧
    ¬host_eval_profile tag name arity
End

Definition host_byte_success_def:
  host_byte_success opcode arg0 arg1 conf =
    if opcode = 1 then [0; arg0 + 1; arg1 + conf; 7]
    else if opcode = 2 then [0; arg0 - 1; arg1 + conf; 8]
    else if opcode = 3 then [0; arg0; arg1 + conf; 9]
    else [3; arg0; arg1; 255]
End

Definition host_byte_response_def:
  host_byte_response tag bytes =
    case (host_byte_conf_len tag, bytes) of
    | (SOME conf_len, [opcode; arg0; arg1; marker]) =>
        host_byte_success opcode arg0 arg1 conf_len
    | (NONE, [opcode; arg0; arg1; marker]) => [2; arg0; arg1; 254]
    | _ => bytes
End

Definition host_call_byte_boundary_def:
  host_call_byte_boundary tag x meta response out ⇔
    host_inc_profile tag (Sym 30) [IntLit x] ∧
    response = host_byte_response tag [1; x; meta; 0] ∧
    out = IntLit (int_add x 1)
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
    | Expr [Sym 31; Sym 8; Sym 8] => BuiltinResult [Sym 8]
    | Expr [Sym 31; Sym 8; Sym 9] => BuiltinResult [Sym 9]
    | Expr [Sym 31; Sym 9; Sym 8] => BuiltinResult [Sym 9]
    | Expr [Sym 31; Sym 9; Sym 9] => BuiltinResult [Sym 9]
    | Expr [Sym 31; a; b] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 32; Sym 8; Sym 8] => BuiltinResult [Sym 8]
    | Expr [Sym 32; Sym 8; Sym 9] => BuiltinResult [Sym 8]
    | Expr [Sym 32; Sym 9; Sym 8] => BuiltinResult [Sym 8]
    | Expr [Sym 32; Sym 9; Sym 9] => BuiltinResult [Sym 9]
    | Expr [Sym 32; a; b] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 33; Sym 8] => BuiltinResult [Sym 9]
    | Expr [Sym 33; Sym 9] => BuiltinResult [Sym 8]
    | Expr [Sym 33; a] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 45; IntLit x; IntLit y] =>
        BuiltinResult [IntLit (int_mul x y)]
    | Expr [Sym 45; a; b] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 46; IntLit x; IntLit y] =>
        BuiltinResult [IntLit (x - y)]
    | Expr [Sym 46; a; b] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr [Sym 47; a; b] =>
        BuiltinResult [if a = b then Sym 8 else Sym 9]
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
    | Expr [Sym 28; Sym 30; IntLit x] =>
        BuiltinResult [IntLit (int_add x 1)]
    | Expr [Sym 28; Sym 30; bad] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr (Sym 28 :: name :: args) => BuiltinResult [Sym 23]
    | Expr [Sym 29; Sym 30; IntLit x] =>
        BuiltinResult [IntLit (int_add x 1)]
    | Expr [Sym 29; Sym 30; bad] => BuiltinResult [error_atom atom (Sym 10)]
    | Expr (Sym 29 :: name :: args) => BuiltinResult [Sym 23]
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

Definition return_payload_of_def:
  return_payload_of (Expr [Sym 19; value]) = SOME value ∧
  return_payload_of _ = NONE
End

Definition return_payloads_rest_def:
  return_payloads_rest original [] = [] ∧
  return_payloads_rest original (atom :: rest) =
    (case return_payload_of atom of
     | SOME value => value
     | NONE => error_atom original (Sym 22)) ::
    return_payloads_rest original rest
End

Definition return_payloads_def:
  return_payloads original [] = [error_atom original (Sym 22)] ∧
  return_payloads original (atom :: rest) =
    case return_payload_of atom of
    | SOME value => value :: return_payloads_rest original rest
    | NONE => [error_atom original (Sym 22)]
End

Definition rec_add_right_def:
  rec_add_right original x [] = [] ∧
  rec_add_right original (IntLit x) (IntLit y :: ys) =
    IntLit (int_add x y) :: rec_add_right original (IntLit x) ys ∧
  rec_add_right original x (_ :: ys) =
    error_atom original (Sym 10) :: rec_add_right original x ys
End

Definition rec_add_values_def:
  rec_add_values original [] ys = [] ∧
  rec_add_values original (x :: xs) ys =
    rec_add_right original x ys ++ rec_add_values original xs ys
End

Definition rec_mul_right_def:
  rec_mul_right original x [] = [] ∧
  rec_mul_right original (IntLit x) (IntLit y :: ys) =
    IntLit (int_mul x y) :: rec_mul_right original (IntLit x) ys ∧
  rec_mul_right original x (_ :: ys) =
    error_atom original (Sym 10) :: rec_mul_right original x ys
End

Definition rec_mul_values_def:
  rec_mul_values original [] ys = [] ∧
  rec_mul_values original (x :: xs) ys =
    rec_mul_right original x ys ++ rec_mul_values original xs ys
End

Definition rec_sub_right_def:
  rec_sub_right original x [] = [] ∧
  rec_sub_right original (IntLit x) (IntLit y :: ys) =
    IntLit (x - y) :: rec_sub_right original (IntLit x) ys ∧
  rec_sub_right original x (_ :: ys) =
    error_atom original (Sym 10) :: rec_sub_right original x ys
End

Definition rec_sub_values_def:
  rec_sub_values original [] ys = [] ∧
  rec_sub_values original (x :: xs) ys =
    rec_sub_right original x ys ++ rec_sub_values original xs ys
End

Definition rec_lt_right_def:
  rec_lt_right original x [] = [] ∧
  rec_lt_right original (IntLit x) (IntLit y :: ys) =
    (if int_lt x y then Sym 8 else Sym 9) ::
      rec_lt_right original (IntLit x) ys ∧
  rec_lt_right original x (_ :: ys) =
    error_atom original (Sym 10) :: rec_lt_right original x ys
End

Definition rec_lt_values_def:
  rec_lt_values original [] ys = [] ∧
  rec_lt_values original (x :: xs) ys =
    rec_lt_right original x ys ++ rec_lt_values original xs ys
End

Definition bool_and_result_def:
  bool_and_result original x y =
    case x of
    | Sym 8 =>
        (case y of
         | Sym 8 => Sym 8
         | Sym 9 => Sym 9
         | _ => error_atom original (Sym 10))
    | Sym 9 =>
        (case y of
         | Sym 8 => Sym 9
         | Sym 9 => Sym 9
         | _ => error_atom original (Sym 10))
    | _ => error_atom original (Sym 10)
End

Definition bool_or_result_def:
  bool_or_result original x y =
    case x of
    | Sym 8 =>
        (case y of
         | Sym 8 => Sym 8
         | Sym 9 => Sym 8
         | _ => error_atom original (Sym 10))
    | Sym 9 =>
        (case y of
         | Sym 8 => Sym 8
         | Sym 9 => Sym 9
         | _ => error_atom original (Sym 10))
    | _ => error_atom original (Sym 10)
End

Definition bool_not_result_def:
  bool_not_result original x =
    case x of
    | Sym 8 => Sym 9
    | Sym 9 => Sym 8
    | _ => error_atom original (Sym 10)
End

Definition rec_and_right_def:
  rec_and_right original x [] = [] ∧
  rec_and_right original x (y :: ys) =
    bool_and_result original x y :: rec_and_right original x ys
End

Definition rec_and_values_def:
  rec_and_values original [] ys = [] ∧
  rec_and_values original (x :: xs) ys =
    rec_and_right original x ys ++ rec_and_values original xs ys
End

Definition rec_or_right_def:
  rec_or_right original x [] = [] ∧
  rec_or_right original x (y :: ys) =
    bool_or_result original x y :: rec_or_right original x ys
End

Definition rec_or_values_def:
  rec_or_values original [] ys = [] ∧
  rec_or_values original (x :: xs) ys =
    rec_or_right original x ys ++ rec_or_values original xs ys
End

Definition rec_not_values_def:
  rec_not_values original [] = [] ∧
  rec_not_values original (x :: xs) =
    bool_not_result original x :: rec_not_values original xs
End

Definition rec_eq_right_def:
  rec_eq_right original x [] = [] ∧
  rec_eq_right original x (y :: ys) =
    (if x = y then Sym 8 else Sym 9) :: rec_eq_right original x ys
End

Definition rec_eq_values_def:
  rec_eq_values original [] ys = [] ∧
  rec_eq_values original (x :: xs) ys =
    rec_eq_right original x ys ++ rec_eq_values original xs ys
End

Definition default_types_def:
  default_types (IntLit i) = [Sym 40] ∧
  default_types (StrLit s) = [Sym 42] ∧
  default_types (Sym n) = [Sym 39] ∧
  default_types (Var v) = [Sym 43] ∧
  default_types (Expr xs) = [Sym 41]
End

Definition hol_type_lookup_def:
  hol_type_lookup [] atom = default_types atom ∧
  hol_type_lookup (Expr [Sym 34; a; typ] :: rest) atom =
    (if a = atom then typ :: hol_type_lookup rest atom
     else hol_type_lookup rest atom) ∧
  hol_type_lookup (_ :: rest) atom = hol_type_lookup rest atom
End

Definition hol_declared_type_lookup_def:
  hol_declared_type_lookup [] atom = [] ∧
  hol_declared_type_lookup (Expr [Sym 34; a; typ] :: rest) atom =
    (if a = atom then typ :: hol_declared_type_lookup rest atom
     else hol_declared_type_lookup rest atom) ∧
  hol_declared_type_lookup (_ :: rest) atom =
    hol_declared_type_lookup rest atom
End

Definition hol_declared_or_default_type_lookup_def:
  hol_declared_or_default_type_lookup space atom =
    case hol_declared_type_lookup space atom of
    | [] => default_types atom
    | types => types
End

Definition hol_type_matches_def:
  hol_type_matches expected actual ⇔
    expected = actual ∨ expected = Sym 39 ∨ actual = Sym 39 ∨
    expected = Sym 44 ∨ actual = Sym 44
End

Definition hol_any_type_match_def:
  hol_any_type_match expected [] = F ∧
  hol_any_type_match expected (actual :: rest) =
    (hol_type_matches expected actual ∨ hol_any_type_match expected rest)
End

Definition hol_typed_add_bad_def:
  hol_typed_add_bad space atom ⇔
    case atom of
    | Expr [Sym 38; a; b] =>
        MEM (Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]])
            space ∧
        ¬(hol_any_type_match (Sym 36)
             (hol_declared_or_default_type_lookup space a) ∧
          hol_any_type_match (Sym 36)
             (hol_declared_or_default_type_lookup space b))
    | _ => F
End

Definition evalc_values_def:
  evalc_values space original expected [] = [] ∧
  evalc_values space original expected (value :: rest) =
    (if hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value)
     then value
     else error_atom original (Sym 10)) ::
    evalc_values space original expected rest
End

Definition dependent_vec_cons_type_def:
  dependent_vec_cons_type space elem tail =
    case hol_declared_or_default_type_lookup space tail of
    | Expr [Sym 49; elem_type; n] :: rest =>
        (case hol_declared_or_default_type_lookup space elem of
         | actual :: actual_rest =>
             if hol_type_matches elem_type actual
             then Expr [Sym 49; elem_type; Expr [Sym 51; n]]
             else Sym 10
         | [] => Sym 10)
    | _ => Sym 10
End

Definition branch_pair_def:
  branch_pair (Expr [pattern; body]) = SOME (pattern, body) ∧
  branch_pair _ = NONE
End

Definition eval_case_one_with_def:
  eval_case_one_with ev value [] = [] ∧
  eval_case_one_with ev value (branch :: rest) =
    (case branch_pair branch of
     | SOME (pattern, body) =>
         (case match_atom pattern value [] of
          | SOME bs => ev (apply_subst bs body)
          | NONE => eval_case_one_with ev value rest)
     | NONE => eval_case_one_with ev value rest)
End

Definition eval_case_values_with_def:
  eval_case_values_with ev [] branches = [] ∧
  eval_case_values_with ev (value :: rest) branches =
    eval_case_one_with ev value branches ++
    eval_case_values_with ev rest branches
End

Definition eval_switch_one_with_def:
  eval_switch_one_with ev value [] = [] ∧
  eval_switch_one_with ev value (branch :: rest) =
    (case branch_pair branch of
     | SOME (pattern, body) =>
         (case match_atom pattern value [] of
          | SOME bs => ev (apply_subst bs body)
          | NONE => eval_switch_one_with ev value rest)
     | NONE => eval_switch_one_with ev value rest)
End

Definition eval_switch_values_with_def:
  eval_switch_values_with ev [] branches = [] ∧
  eval_switch_values_with ev (value :: rest) branches =
    eval_switch_one_with ev value branches ++
    eval_switch_values_with ev rest branches
End

Definition let_binding_pair_def:
  let_binding_pair (Expr [Var v; value]) = SOME (v, value) ∧
  let_binding_pair _ = NONE
End

Definition subst_binding_pair_def:
  subst_binding_pair v value (Expr [Var w; rhs]) =
    Expr [Var w; apply_subst [Bind v value] rhs] ∧
  subst_binding_pair v value other = other
End

Definition subst_binding_pairs_def:
  subst_binding_pairs v value [] = [] ∧
  subst_binding_pairs v value (pair :: rest) =
    subst_binding_pair v value pair :: subst_binding_pairs v value rest
End

Definition eval_let_star_with_def:
  eval_let_star_with 0 ev bindings body original =
    [error_atom original (Sym 3)] ∧
  eval_let_star_with (SUC fuel) ev [] body original = ev body ∧
  eval_let_star_with (SUC fuel) ev (binding :: rest) body original =
    (case let_binding_pair binding of
     | SOME (v, value) =>
         FLAT
           (MAP
             (λevaluated.
                eval_let_star_with fuel ev
                  (subst_binding_pairs v evaluated rest)
                  (apply_subst [Bind v evaluated] body) original)
             (ev value))
     | NONE => [error_atom original (Sym 10)])
Termination
  WF_REL_TAC ‘measure (λ(fuel,ev,bindings,body,original). fuel)’ \\
  rw[]
End

Definition let_star_provenance_def:
  let_star_provenance 0 ev bindings body original out =
    (out = error_atom original (Sym 3)) ∧
  let_star_provenance (SUC fuel) ev [] body original out =
    MEM out (ev body) ∧
  let_star_provenance (SUC fuel) ev (binding :: rest) body original out =
    (case let_binding_pair binding of
     | SOME (v, value) =>
         ∃evaluated.
           MEM evaluated (ev value) ∧
           let_star_provenance fuel ev
             (subst_binding_pairs v evaluated rest)
             (apply_subst [Bind v evaluated] body) original out
     | NONE => out = error_atom original (Sym 10))
Termination
  WF_REL_TAC
    ‘measure (λ(fuel,ev,bindings,body,original,out). fuel)’ \\
  rw[]
End

Definition eval_m1_rec_def:
  eval_m1_rec 0 space atom = [error_atom atom (Sym 3)] ∧
  eval_m1_rec (SUC fuel) space atom =
    (case atom of
    | Expr [Sym 11; a; b] =>
        rec_add_values atom
          (eval_m1_rec fuel space a)
          (eval_m1_rec fuel space b)
    | Expr [Sym 45; a; b] =>
        rec_mul_values atom
          (eval_m1_rec fuel space a)
          (eval_m1_rec fuel space b)
    | Expr [Sym 46; a; b] =>
        rec_sub_values atom
          (eval_m1_rec fuel space a)
          (eval_m1_rec fuel space b)
    | Expr [Sym 12; a; b] =>
        rec_lt_values atom
          (eval_m1_rec fuel space a)
          (eval_m1_rec fuel space b)
    | Expr [Sym 47; a; b] =>
        rec_eq_values atom
          (eval_m1_rec fuel space a)
          (eval_m1_rec fuel space b)
    | Expr [Sym 31; a; b] =>
        rec_and_values atom
          (eval_m1_rec fuel space a)
          (eval_m1_rec fuel space b)
    | Expr [Sym 32; a; b] =>
        rec_or_values atom
          (eval_m1_rec fuel space a)
          (eval_m1_rec fuel space b)
    | Expr [Sym 33; a] =>
        rec_not_values atom (eval_m1_rec fuel space a)
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
    | Expr [Sym 57; term; expected] =>
        evalc_values space term expected
          (if hol_typed_add_bad space term
           then [error_atom term (Sym 10)]
           else eval_m1_rec fuel space term)
    | Expr [Sym 58; elem; tail] =>
        [dependent_vec_cons_type space elem tail]
    | Expr [Sym 54; scrut; Expr branches] =>
        eval_case_values_with
          (eval_m1_rec fuel space)
          (eval_m1_rec fuel space scrut) branches
    | Expr [Sym 54; scrut; branches] =>
        [error_atom atom (Sym 10)]
    | Expr [Sym 55; scrut; Expr branches] =>
        eval_switch_values_with
          (eval_m1_rec fuel space)
          (eval_m1_rec fuel space scrut) branches
    | Expr [Sym 55; scrut; branches] =>
        [error_atom atom (Sym 10)]
    | Expr [Sym 56; Expr bindings; body] =>
        eval_let_star_with (SUC (LENGTH bindings))
          (eval_m1_rec fuel space) bindings body atom
    | Expr [Sym 56; bindings; body] =>
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

Definition export_eval_m1_rec_def:
  export_eval_m1_rec fuel space atom =
    MAP export_atom (eval_m1_rec fuel space atom)
End

Theorem import_export_eval_m1_rec:
  ∀fuel space atom.
    MAP import_exported_atom (export_eval_m1_rec fuel space atom) =
    eval_m1_rec fuel space atom
Proof
  rw[export_eval_m1_rec_def, import_export_atom_map]
QED

Definition eval_return_fragment_def:
  eval_return_fragment atom =
    case atom of
    | Expr [Sym 19; value] => [Expr [Sym 19; value]]
    | _ => [atom]
End

Definition export_eval_return_fragment_def:
  export_eval_return_fragment atom =
    MAP export_atom (eval_return_fragment atom)
End

Theorem import_export_eval_return_fragment:
  ∀atom.
    MAP import_exported_atom (export_eval_return_fragment atom) =
    eval_return_fragment atom
Proof
  rw[export_eval_return_fragment_def, import_export_atom_map]
QED

Theorem eval_return_fragment_agrees_with_eval_m1_rec:
  ∀fuel space value.
    eval_return_fragment (Expr [Sym 19; value]) =
    eval_m1_rec (SUC fuel) space (Expr [Sym 19; value])
Proof
  rw[eval_return_fragment_def, eval_m1_rec_def]
QED

Definition eval_add_fragment_def:
  eval_add_fragment fuel space atom =
    case atom of
    | Expr [Sym 11; a; b] =>
        rec_add_values atom
          (eval_m1_rec fuel space a)
          (eval_m1_rec fuel space b)
    | _ => [atom]
End

Definition export_eval_add_fragment_def:
  export_eval_add_fragment fuel space atom =
    MAP export_atom (eval_add_fragment fuel space atom)
End

Theorem import_export_eval_add_fragment:
  ∀fuel space atom.
    MAP import_exported_atom (export_eval_add_fragment fuel space atom) =
    eval_add_fragment fuel space atom
Proof
  rw[export_eval_add_fragment_def, import_export_atom_map]
QED

Theorem eval_add_fragment_agrees_with_eval_m1_rec:
  ∀fuel space a b.
    eval_add_fragment fuel space (Expr [Sym 11; a; b]) =
    eval_m1_rec (SUC fuel) space (Expr [Sym 11; a; b])
Proof
  rw[eval_add_fragment_def, eval_m1_rec_def]
QED

Definition eval_eval_fragment_def:
  eval_eval_fragment fuel space atom =
    case atom of
    | Expr [Sym 20; body] =>
        let rs = eval_m1_rec fuel space body in
          if rs = [body] then [Sym 23] else rs
    | _ => [atom]
End

Definition export_eval_eval_fragment_def:
  export_eval_eval_fragment fuel space atom =
    MAP export_atom (eval_eval_fragment fuel space atom)
End

Theorem import_export_eval_eval_fragment:
  ∀fuel space atom.
    MAP import_exported_atom (export_eval_eval_fragment fuel space atom) =
    eval_eval_fragment fuel space atom
Proof
  rw[export_eval_eval_fragment_def, import_export_atom_map]
QED

Theorem eval_eval_fragment_agrees_with_eval_m1_rec:
  ∀fuel space body.
    eval_eval_fragment fuel space (Expr [Sym 20; body]) =
    eval_m1_rec (SUC fuel) space (Expr [Sym 20; body])
Proof
  rw[eval_eval_fragment_def, eval_m1_rec_def]
QED

Definition eval_chain_fragment_def:
  eval_chain_fragment fuel space atom =
    case atom of
    | Expr [Sym 21; nested; Var v; templ] =>
        eval_m1_rec_chain fuel space v
          (eval_m1_rec fuel space nested) templ
    | _ => [atom]
End

Definition export_eval_chain_fragment_def:
  export_eval_chain_fragment fuel space atom =
    MAP export_atom (eval_chain_fragment fuel space atom)
End

Theorem import_export_eval_chain_fragment:
  ∀fuel space atom.
    MAP import_exported_atom (export_eval_chain_fragment fuel space atom) =
    eval_chain_fragment fuel space atom
Proof
  rw[export_eval_chain_fragment_def, import_export_atom_map]
QED

Theorem eval_chain_fragment_agrees_with_eval_m1_rec:
  ∀fuel space nested v templ.
    eval_chain_fragment fuel space (Expr [Sym 21; nested; Var v; templ]) =
    eval_m1_rec (SUC fuel) space (Expr [Sym 21; nested; Var v; templ])
Proof
  rw[eval_chain_fragment_def, eval_m1_rec_def]
QED

Definition eval_case_fragment_def:
  eval_case_fragment fuel space atom =
    case atom of
    | Expr [Sym 54; scrut; Expr branches] =>
        eval_case_values_with
          (λa. eval_m1_rec fuel space a)
          (eval_m1_rec fuel space scrut) branches
    | _ => [atom]
End

Definition export_eval_case_fragment_def:
  export_eval_case_fragment fuel space atom =
    MAP export_atom (eval_case_fragment fuel space atom)
End

Theorem import_export_eval_case_fragment:
  ∀fuel space atom.
    MAP import_exported_atom (export_eval_case_fragment fuel space atom) =
    eval_case_fragment fuel space atom
Proof
  rw[export_eval_case_fragment_def, import_export_atom_map]
QED

Theorem eval_case_fragment_agrees_with_eval_m1_rec:
  ∀fuel space scrut branches.
    eval_case_fragment fuel space (Expr [Sym 54; scrut; Expr branches]) =
    eval_m1_rec (SUC fuel) space (Expr [Sym 54; scrut; Expr branches])
Proof
  rw[eval_case_fragment_def, eval_m1_rec_def]
QED

Definition typed_eval_m1_rec_def:
  typed_eval_m1_rec fuel space atom =
    if hol_typed_add_bad space atom then [error_atom atom (Sym 10)]
    else eval_m1_rec fuel space atom
End

Definition evalc_like_def:
  evalc_like fuel space atom expected =
    evalc_values space atom expected (typed_eval_m1_rec fuel space atom)
End

Definition lookup_named_space_def:
  lookup_named_space name [] = NONE ∧
  lookup_named_space name ((key, stored) :: rest) =
    (if name = key then SOME stored else lookup_named_space name rest)
End

Definition set_named_space_def:
  set_named_space name stored [] = [(name, stored)] ∧
  set_named_space name stored ((key, old) :: rest) =
    (if name = key then (name, stored) :: rest
     else (key, old) :: set_named_space name stored rest)
End

Definition bind_empty_named_space_def:
  bind_empty_named_space name spaces =
    set_named_space name [] spaces
End

Definition add_atom_to_named_space_def:
  add_atom_to_named_space name atom spaces =
    case lookup_named_space name spaces of
    | SOME stored =>
        SOME (set_named_space name (stored ++ [atom]) spaces)
    | NONE => NONE
End

Definition evalc_context_def:
  evalc_context fuel self named term (Sym name) =
    (if name = 5 then visible_results (eval_m1_rec fuel self term)
     else
       case lookup_named_space name named of
       | SOME ctx => visible_results (eval_m1_rec fuel ctx term)
       | NONE => [error_atom (Expr [Sym 61; term; Sym name]) (Sym 10)]) ∧
  evalc_context fuel self named term bad_space =
    [error_atom (Expr [Sym 61; term; bad_space]) (Sym 10)]
End

Definition match_context_space_def:
  match_context_space self named (Sym name) pattern templ =
    (if name = 5 then match_space self pattern templ
     else
       case lookup_named_space name named of
       | SOME ctx => match_space ctx pattern templ
       | NONE => [error_atom (Expr [Sym 4; Sym name; pattern; templ]) (Sym 10)]) ∧
  match_context_space self named bad_space pattern templ =
    [error_atom (Expr [Sym 4; bad_space; pattern; templ]) (Sym 10)]
End

Definition eval_typed_fragment_def:
  eval_typed_fragment fuel space atom =
    typed_eval_m1_rec fuel space atom
End

Definition export_eval_typed_fragment_def:
  export_eval_typed_fragment fuel space atom =
    MAP export_atom (eval_typed_fragment fuel space atom)
End

Theorem import_export_eval_typed_fragment:
  ∀fuel space atom.
    MAP import_exported_atom (export_eval_typed_fragment fuel space atom) =
    eval_typed_fragment fuel space atom
Proof
  rw[export_eval_typed_fragment_def, eval_typed_fragment_def,
     import_export_atom_map]
QED

Theorem eval_typed_fragment_agrees_with_typed_eval_m1_rec:
  ∀fuel space atom.
    eval_typed_fragment fuel space atom =
    typed_eval_m1_rec fuel space atom
Proof
  rw[eval_typed_fragment_def]
QED

Definition eval_evalc_fragment_def:
  eval_evalc_fragment fuel space atom =
    case atom of
    | Expr [Sym 57; term; expected] =>
        evalc_values space term expected
          (typed_eval_m1_rec fuel space term)
    | _ => [atom]
End

Definition export_eval_evalc_fragment_def:
  export_eval_evalc_fragment fuel space atom =
    MAP export_atom (eval_evalc_fragment fuel space atom)
End

Theorem import_export_eval_evalc_fragment:
  ∀fuel space atom.
    MAP import_exported_atom (export_eval_evalc_fragment fuel space atom) =
    eval_evalc_fragment fuel space atom
Proof
  rw[export_eval_evalc_fragment_def, import_export_atom_map]
QED

Theorem eval_evalc_fragment_agrees_with_eval_m1_rec:
  ∀fuel space term expected.
    eval_evalc_fragment fuel space (Expr [Sym 57; term; expected]) =
    eval_m1_rec (SUC fuel) space (Expr [Sym 57; term; expected])
Proof
  rw[eval_evalc_fragment_def, eval_m1_rec_def, typed_eval_m1_rec_def]
QED

Definition eval_vec_cons_fragment_def:
  eval_vec_cons_fragment space atom =
    case atom of
    | Expr [Sym 58; elem; tail] =>
        [dependent_vec_cons_type space elem tail]
    | _ => [atom]
End

Definition export_eval_vec_cons_fragment_def:
  export_eval_vec_cons_fragment space atom =
    MAP export_atom (eval_vec_cons_fragment space atom)
End

Theorem import_export_eval_vec_cons_fragment:
  ∀space atom.
    MAP import_exported_atom (export_eval_vec_cons_fragment space atom) =
    eval_vec_cons_fragment space atom
Proof
  rw[export_eval_vec_cons_fragment_def, import_export_atom_map]
QED

Theorem eval_vec_cons_fragment_agrees_with_eval_m1_rec:
  ∀fuel space elem tail.
    eval_vec_cons_fragment space (Expr [Sym 58; elem; tail]) =
    eval_m1_rec (SUC fuel) space (Expr [Sym 58; elem; tail])
Proof
  rw[eval_vec_cons_fragment_def, eval_m1_rec_def]
QED

Theorem lookup_named_space_hit:
  ∀name stored rest.
    lookup_named_space name ((name, stored) :: rest) = SOME stored
Proof
  rw[lookup_named_space_def]
QED

Theorem lookup_named_space_miss_cons:
  ∀name key stored rest.
    name ≠ key ⇒
    lookup_named_space name ((key, stored) :: rest) =
    lookup_named_space name rest
Proof
  rw[lookup_named_space_def]
QED

Theorem lookup_named_space_set_hit:
  ∀spaces name stored.
    lookup_named_space name (set_named_space name stored spaces) =
    SOME stored
Proof
  Induct \\ rw[lookup_named_space_def, set_named_space_def] \\
  PairCases_on ‘h’ \\
  rw[lookup_named_space_def, set_named_space_def]
QED

Theorem lookup_named_space_set_other:
  ∀spaces name other stored.
    name ≠ other ⇒
    lookup_named_space name (set_named_space other stored spaces) =
    lookup_named_space name spaces
Proof
  Induct \\ rw[lookup_named_space_def, set_named_space_def] \\
  PairCases_on ‘h’ \\
  rw[lookup_named_space_def, set_named_space_def]
QED

Theorem bind_empty_named_space_lookup:
  ∀spaces name.
    lookup_named_space name (bind_empty_named_space name spaces) = SOME []
Proof
  rw[bind_empty_named_space_def, lookup_named_space_set_hit]
QED

Theorem add_atom_to_named_space_lookup_hit:
  ∀spaces name stored atom spaces2.
    lookup_named_space name spaces = SOME stored ∧
    add_atom_to_named_space name atom spaces = SOME spaces2 ⇒
    lookup_named_space name spaces2 = SOME (stored ++ [atom])
Proof
  rw[add_atom_to_named_space_def] \\
  gvs[lookup_named_space_set_hit]
QED

Theorem add_atom_to_named_space_missing:
  ∀spaces name atom.
    lookup_named_space name spaces = NONE ⇒
    add_atom_to_named_space name atom spaces = NONE
Proof
  rw[add_atom_to_named_space_def]
QED

Theorem add_atom_to_named_space_example:
  add_atom_to_named_space 66 (Sym 25) [(66, [Sym 24])] =
  SOME [(66, [Sym 24; Sym 25])]
Proof
  EVAL_TAC
QED

Theorem evalc_context_self_example:
  ∀fuel.
    evalc_context (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; Sym 25]]
      [] (Expr [Sym 24]) (Sym 5) =
    [Sym 25]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem evalc_context_named_space_example:
  ∀fuel.
    evalc_context (SUC (SUC fuel)) []
      [(66, [Expr [Sym 2; Expr [Sym 24]; Sym 25]])]
      (Expr [Sym 24]) (Sym 66) =
    [Sym 25]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem evalc_context_missing_space_example:
  evalc_context 7 [] [] (Sym 24) (Sym 66) =
  [error_atom (Expr [Sym 61; Sym 24; Sym 66]) (Sym 10)]
Proof
  EVAL_TAC
QED

Theorem evalc_context_bad_space_atom_example:
  evalc_context 7 [] [] (Sym 24) (Expr [Sym 66]) =
  [error_atom (Expr [Sym 61; Sym 24; Expr [Sym 66]]) (Sym 10)]
Proof
  EVAL_TAC
QED

Theorem match_context_space_self_example:
  match_context_space
    [Expr [Sym 2; Expr [Sym 24]; Sym 25]]
    [] (Sym 5)
    (Expr [Sym 2; Expr [Sym 24]; Var 0]) (Var 0) =
  [Sym 25]
Proof
  EVAL_TAC
QED

Theorem match_context_space_named_example:
  match_context_space []
    [(66, [Expr [Sym 2; Expr [Sym 24]; Sym 25]])]
    (Sym 66)
    (Expr [Sym 2; Expr [Sym 24]; Var 0]) (Var 0) =
  [Sym 25]
Proof
  EVAL_TAC
QED

Definition eval_case_one_def:
  eval_case_one fuel space value [] original = [] ∧
  eval_case_one fuel space value (branch :: rest) original =
    case branch_pair branch of
    | SOME (pattern, body) =>
        (case match_atom pattern value [] of
         | SOME bs => eval_m1_rec fuel space (apply_subst bs body)
         | NONE => eval_case_one fuel space value rest original)
    | NONE => eval_case_one fuel space value rest original
End

Definition eval_case_values_def:
  eval_case_values fuel space [] branches original = [] ∧
  eval_case_values fuel space (value :: rest) branches original =
    eval_case_one fuel space value branches original ++
    eval_case_values fuel space rest branches original
End

Definition eval_case_like_def:
  eval_case_like fuel space scrut branches original =
    eval_case_values fuel space (eval_m1_rec fuel space scrut) branches original
End

Definition eval_switch_one_def:
  eval_switch_one fuel space value [] original = [] ∧
  eval_switch_one fuel space value (branch :: rest) original =
    case branch_pair branch of
    | SOME (pattern, body) =>
        (case match_atom pattern value [] of
         | SOME bs => eval_m1_rec fuel space (apply_subst bs body)
         | NONE => eval_switch_one fuel space value rest original)
    | NONE => eval_switch_one fuel space value rest original
End

Definition eval_switch_values_def:
  eval_switch_values fuel space [] branches original = [] ∧
  eval_switch_values fuel space (value :: rest) branches original =
    eval_switch_one fuel space value branches original ++
    eval_switch_values fuel space rest branches original
End

Definition eval_switch_like_def:
  eval_switch_like fuel space scrut branches original =
    eval_switch_values fuel space (eval_m1_rec fuel space scrut) branches original
End

Definition eval_let1_values_def:
  eval_let1_values fuel space v [] body original = [] ∧
  eval_let1_values fuel space v (value :: rest) body original =
    eval_m1_rec fuel space (apply_subst [Bind v value] body) ++
    eval_let1_values fuel space v rest body original
End

Definition eval_let1_like_def:
  eval_let1_like fuel space binding body original =
    case let_binding_pair binding of
    | SOME (v, value) =>
        eval_let1_values fuel space v
          (eval_m1_rec fuel space value) body original
    | NONE => [error_atom original (Sym 10)]
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

Theorem eval_m1_ext_mul_example:
  ∀fuel x y.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 45; IntLit x; IntLit y]) =
    [IntLit (int_mul x y)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_sub_example:
  ∀fuel x y.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 46; IntLit x; IntLit y]) =
    [IntLit (x - y)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_eq_true_example:
  ∀fuel a.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 47; a; a]) = [Sym 8]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_and_true_false_example:
  ∀fuel.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 31; Sym 8; Sym 9]) = [Sym 9]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_or_false_true_example:
  ∀fuel.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 32; Sym 9; Sym 8]) = [Sym 8]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_not_true_example:
  ∀fuel.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 33; Sym 8]) = [Sym 9]
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

Theorem eval_m1_ext_call_ml_inc_example:
  ∀fuel x.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 28; Sym 30; IntLit x]) =
    [IntLit (int_add x 1)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_call_native_fronts_call_ml_example:
  ∀fuel x.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 29; Sym 30; IntLit x]) =
    [IntLit (int_add x 1)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_call_ml_bad_arg_example:
  ∀fuel n.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 28; Sym 30; Sym n]) =
    [error_atom (Expr [Sym 28; Sym 30; Sym n]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_call_ml_unknown_example:
  ∀fuel n a.
    n ≠ 30 ⇒
    eval_m1_ext (SUC fuel) [] (Expr [Sym 28; Sym n; a]) =
    [Sym 23]
Proof
  rw[] \\ EVAL_TAC \\ rw[]
QED

Theorem host_inc_profile_call_ml:
  ∀a. host_inc_profile (Sym 28) (Sym 30) [a]
Proof
  rw[host_inc_profile_def, host_impl_def]
QED

Theorem host_inc_profile_call_native:
  ∀a. host_inc_profile (Sym 29) (Sym 30) [a]
Proof
  rw[host_inc_profile_def, host_impl_def]
QED

Theorem host_inc_profile_rejects_other_name:
  ∀tag name args.
    name ≠ Sym 30 ⇒ ¬host_inc_profile tag name args
Proof
  rw[host_inc_profile_def]
QED

Theorem host_impl_supported:
  ∀tag.
    (host_impl tag = HostML ∨ host_impl tag = HostNative) ⇔
    tag = Sym 28 ∨ tag = Sym 29
Proof
  Cases \\ rw[host_impl_def] \\
  Cases_on ‘n = 28’ \\ Cases_on ‘n = 29’ \\ rw[host_impl_def]
QED

Theorem host_inc_profile_cases:
  ∀tag name args.
    host_inc_profile tag name args ⇔
    (tag = Sym 28 ∨ tag = Sym 29) ∧ name = Sym 30 ∧
    ∃arg. args = [arg]
Proof
  rw[host_inc_profile_def, host_impl_supported]
QED

Theorem builtin_eval_host_profile_inc_int:
  ∀tag name x.
    host_inc_profile tag name [IntLit x] ⇒
    builtin_eval (Expr [tag; name; IntLit x]) =
    BuiltinResult [IntLit (int_add x 1)]
Proof
  rw[host_inc_profile_cases] \\ rw[builtin_eval_def]
QED

Theorem builtin_eval_host_profile_bad_arg:
  ∀tag name arg.
    host_inc_profile tag name [arg] ∧ (∀x. arg ≠ IntLit x) ⇒
    builtin_eval (Expr [tag; name; arg]) =
    BuiltinResult [error_atom (Expr [tag; name; arg]) (Sym 10)]
Proof
  rw[host_inc_profile_cases] \\
  Cases_on ‘arg’ \\ rw[builtin_eval_def]
QED

Theorem eval_m1_ext_host_profile_inc_int:
  ∀fuel tag x.
    (tag = Sym 28 ∨ tag = Sym 29) ⇒
    eval_m1_ext (SUC fuel) [] (Expr [tag; Sym 30; IntLit x]) =
    [IntLit (int_add x 1)]
Proof
  rw[] \\ EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_host_profile_unknown_name:
  ∀fuel tag n a.
    (tag = Sym 28 ∨ tag = Sym 29) ∧ n ≠ 30 ⇒
    eval_m1_ext (SUC fuel) [] (Expr [tag; Sym n; a]) = [Sym 23]
Proof
  rw[] \\ EVAL_TAC \\ rw[]
QED

Theorem eval_m1_ext_host_profile_boundary:
  ∀fuel tag name arg out.
    host_inc_profile tag name [arg] ∧
    MEM out (eval_m1_ext (SUC fuel) [] (Expr [tag; name; arg])) ⇒
    (∃x. arg = IntLit x ∧ out = IntLit (int_add x 1)) ∨
    ((∀x. arg ≠ IntLit x) ∧
     out = error_atom (Expr [tag; name; arg]) (Sym 10))
Proof
  rw[host_inc_profile_cases] \\
  Cases_on ‘arg’ \\
  gvs[eval_m1_ext_def, builtin_eval_def, error_atom_def]
QED

Theorem eval_m1_ext_call_native_fronts_call_ml_int:
  ∀fuel x.
    eval_m1_ext (SUC fuel) [] (Expr [Sym 29; Sym 30; IntLit x]) =
    eval_m1_ext (SUC fuel) [] (Expr [Sym 28; Sym 30; IntLit x])
Proof
  rw[eval_m1_ext_def, builtin_eval_def]
QED

Theorem host_byte_response_call_ml_inc:
  ∀x meta marker.
    host_byte_response (Sym 28) [1; x; meta; marker] =
    [0; x + 1; meta + 7; 7]
Proof
  rw[host_byte_response_def, host_byte_conf_len_def, host_byte_success_def]
QED

Theorem host_byte_response_call_native_front_inc:
  ∀x meta marker.
    host_byte_response (Sym 29) [1; x; meta; marker] =
    [0; x + 1; meta + 19; 7]
Proof
  rw[host_byte_response_def, host_byte_conf_len_def, host_byte_success_def]
QED

Theorem host_byte_response_call_ml_dec:
  ∀x meta marker.
    host_byte_response (Sym 28) [2; x; meta; marker] =
    [0; x - 1; meta + 7; 8]
Proof
  rw[host_byte_response_def, host_byte_conf_len_def, host_byte_success_def]
QED

Theorem host_byte_response_call_ml_echo:
  ∀x meta marker.
    host_byte_response (Sym 28) [3; x; meta; marker] =
    [0; x; meta + 7; 9]
Proof
  rw[host_byte_response_def, host_byte_conf_len_def, host_byte_success_def]
QED

Theorem host_byte_response_call_native_front_dec:
  ∀x meta marker.
    host_byte_response (Sym 29) [2; x; meta; marker] =
    [0; x - 1; meta + 19; 8]
Proof
  rw[host_byte_response_def, host_byte_conf_len_def, host_byte_success_def]
QED

Theorem host_byte_response_call_native_front_echo:
  ∀x meta marker.
    host_byte_response (Sym 29) [3; x; meta; marker] =
    [0; x; meta + 19; 9]
Proof
  rw[host_byte_response_def, host_byte_conf_len_def, host_byte_success_def]
QED

Theorem host_byte_response_rejects_unknown_conf:
  ∀tag opcode x meta marker.
    tag ≠ Sym 28 ∧ tag ≠ Sym 29 ⇒
    host_byte_response tag [opcode; x; meta; marker] =
    [2; x; meta; 254]
Proof
  Cases_on ‘tag’ \\
  rw[host_byte_response_def, host_byte_conf_len_def]
QED

Theorem host_byte_response_supported_conf_rejects_unknown_opcode:
  ∀tag opcode x meta marker.
    (tag = Sym 28 ∨ tag = Sym 29) ∧
    opcode ≠ 1 ∧ opcode ≠ 2 ∧ opcode ≠ 3 ⇒
    host_byte_response tag [opcode; x; meta; marker] =
    [3; x; meta; 255]
Proof
  Cases_on ‘tag’ \\
  rw[host_byte_response_def, host_byte_conf_len_def, host_byte_success_def] \\
  gvs[]
QED

Theorem eval_m1_ext_host_byte_profile_boundary:
  ∀fuel tag x meta response out.
    host_inc_profile tag (Sym 30) [IntLit x] ∧
    response = host_byte_response tag [1; x; meta; 0] ∧
    MEM out (eval_m1_ext (SUC fuel) [] (Expr [tag; Sym 30; IntLit x])) ⇒
    host_call_byte_boundary tag x meta response out ∧
    ((tag = Sym 28 ∧ response = [0; x + 1; meta + 7; 7]) ∨
     (tag = Sym 29 ∧ response = [0; x + 1; meta + 19; 7]))
Proof
  rw[host_inc_profile_cases, host_call_byte_boundary_def,
     host_byte_response_def, host_byte_conf_len_def,
     host_byte_success_def, eval_m1_ext_def, builtin_eval_def] \\
  gvs[]
QED

Theorem host_call_table_lookup_call_ml_inc:
  host_call_table_lookup host_call_table (Sym 28) (Sym 30) 1 = SOME 7
Proof
  rw[host_call_table_def, host_call_table_lookup_def]
QED

Theorem host_call_table_lookup_call_native_inc:
  host_call_table_lookup host_call_table (Sym 29) (Sym 30) 1 = SOME 19
Proof
  rw[host_call_table_def, host_call_table_lookup_def]
QED

Theorem host_call_table_lookup_sound:
  ∀tag name arity conf.
    host_call_table_lookup host_call_table tag name arity = SOME conf ⇒
    arity = 1 ∧ name = Sym 30 ∧
    (tag = Sym 28 ∨ tag = Sym 29) ∧
    host_byte_conf_len tag = SOME conf
Proof
  rw[host_call_table_def, host_call_table_lookup_def,
     host_byte_conf_len_def] \\
  gvs[]
QED

Theorem host_call_table_lookup_profile:
  ∀tag name arity conf arg.
    host_call_table_lookup host_call_table tag name arity = SOME conf ⇒
    arity = 1 ∧ host_inc_profile tag name [arg] ∧
    host_byte_conf_len tag = SOME conf
Proof
  rw[] \\
  drule host_call_table_lookup_sound \\
  rw[host_inc_profile_cases]
QED

Theorem host_call_table_lookup_complete_inc:
  ∀tag arg.
    host_inc_profile tag (Sym 30) [arg] ⇒
    ∃conf.
      host_call_table_lookup host_call_table tag (Sym 30) 1 = SOME conf ∧
      host_byte_conf_len tag = SOME conf
Proof
  rw[host_inc_profile_cases, host_call_table_def,
     host_call_table_lookup_def, host_byte_conf_len_def]
QED

Theorem eval_m1_ext_host_call_table_boundary:
  ∀fuel tag name x meta conf response out.
    host_call_table_lookup host_call_table tag name 1 = SOME conf ∧
    response = host_byte_response tag [1; x; meta; 0] ∧
    MEM out (eval_m1_ext (SUC fuel) [] (Expr [tag; name; IntLit x])) ⇒
    host_inc_profile tag name [IntLit x] ∧
    host_call_byte_boundary tag x meta response out ∧
    response = [0; x + 1; meta + conf; 7]
Proof
  rw[] \\
  drule host_call_table_lookup_sound \\
  rw[] \\
  ‘MEM out [IntLit (int_add x 1)]’ by
    metis_tac[eval_m1_ext_host_profile_inc_int] \\
  gvs[host_inc_profile_cases, host_call_byte_boundary_def,
      host_byte_response_def, host_byte_conf_len_def, host_byte_success_def]
QED

Theorem host_byte_call_table_lookup_call_ml_dec:
  host_byte_call_table_lookup host_byte_call_table (Sym 28) (Sym 59) 1 =
  SOME (7, 2)
Proof
  rw[host_byte_call_table_def, host_byte_call_table_lookup_def]
QED

Theorem host_byte_call_table_lookup_call_ml_echo:
  host_byte_call_table_lookup host_byte_call_table (Sym 28) (Sym 60) 1 =
  SOME (7, 3)
Proof
  rw[host_byte_call_table_def, host_byte_call_table_lookup_def]
QED

Theorem host_byte_call_table_lookup_call_native_dec:
  host_byte_call_table_lookup host_byte_call_table (Sym 29) (Sym 59) 1 =
  SOME (19, 2)
Proof
  rw[host_byte_call_table_def, host_byte_call_table_lookup_def]
QED

Theorem host_byte_call_table_lookup_call_native_echo:
  host_byte_call_table_lookup host_byte_call_table (Sym 29) (Sym 60) 1 =
  SOME (19, 3)
Proof
  rw[host_byte_call_table_def, host_byte_call_table_lookup_def]
QED

Theorem host_byte_call_table_lookup_sound:
  ∀tag name arity conf opcode.
    host_byte_call_table_lookup host_byte_call_table tag name arity =
    SOME (conf, opcode) ⇒
    host_byte_profile tag name arity conf opcode
Proof
  rw[host_byte_call_table_def, host_byte_call_table_lookup_def,
     host_byte_profile_def, host_byte_conf_len_def] \\
  gvs[]
QED

Theorem host_byte_call_table_lookup_complete:
  ∀tag name arity conf opcode.
    host_byte_profile tag name arity conf opcode ⇒
    host_byte_call_table_lookup host_byte_call_table tag name arity =
    SOME (conf, opcode)
Proof
  Cases_on ‘tag’ \\
  rw[host_byte_profile_def, host_byte_conf_len_def,
     host_byte_call_table_def, host_byte_call_table_lookup_def] \\
  gvs[]
QED

Theorem host_byte_call_table_boundary:
  ∀tag name conf opcode x meta response.
    host_byte_call_table_lookup host_byte_call_table tag name 1 =
    SOME (conf, opcode) ∧
    response = host_byte_response tag [opcode; x; meta; 0] ⇒
    host_byte_profile tag name 1 conf opcode ∧
    response = host_byte_success opcode x meta conf
Proof
  rw[] \\
  drule host_byte_call_table_lookup_sound \\
  rw[host_byte_response_def, host_byte_profile_def]
QED

Theorem host_call_table_lookup_eval_profile:
  ∀tag name arity conf.
    host_call_table_lookup host_call_table tag name arity = SOME conf ⇒
    host_eval_profile tag name arity
Proof
  rw[] \\
  drule host_call_table_lookup_sound \\
  rw[host_eval_profile_def]
QED

Theorem host_byte_profile_inc_is_eval_profile:
  ∀tag arity conf opcode.
    host_byte_profile tag (Sym 30) arity conf opcode ⇒
    host_eval_profile tag (Sym 30) arity ∧ opcode = 1
Proof
  Cases_on ‘tag’ \\
  rw[host_byte_profile_def, host_byte_conf_len_def,
     host_eval_profile_def] \\
  gvs[]
QED

Theorem host_byte_profile_dec_echo_byte_only:
  ∀tag name arity conf opcode.
    host_byte_profile tag name arity conf opcode ∧
    (name = Sym 59 ∨ name = Sym 60) ⇒
    host_byte_only_profile tag name arity conf opcode
Proof
  rw[host_byte_only_profile_def, host_eval_profile_def]
QED

Theorem host_byte_call_table_lookup_dec_echo_byte_only:
  ∀tag name arity conf opcode.
    host_byte_call_table_lookup host_byte_call_table tag name arity =
    SOME (conf, opcode) ∧
    (name = Sym 59 ∨ name = Sym 60) ⇒
    host_byte_only_profile tag name arity conf opcode
Proof
  rw[] \\
  drule host_byte_call_table_lookup_sound \\
  rw[host_byte_profile_dec_echo_byte_only]
QED

Theorem host_call_table_lookup_supported_eval_only:
  ∀tag name arity conf.
    host_call_table_lookup host_call_table tag name arity = SOME conf ⇒
    host_eval_profile tag name arity ∧
    ¬∃opcode. host_byte_only_profile tag name arity conf opcode
Proof
  rw[] \\
  drule host_call_table_lookup_sound \\
  rw[host_eval_profile_def, host_byte_only_profile_def]
QED

Theorem host_eval_profile_lookup_complete:
  ∀tag name arity.
    host_eval_profile tag name arity ⇒
    ∃conf.
      host_call_table_lookup host_call_table tag name arity = SOME conf
Proof
  Cases_on ‘tag’ \\
  rw[host_eval_profile_def, host_call_table_def,
     host_call_table_lookup_def]
QED

Theorem host_byte_only_profile_not_host_call_table:
  ∀tag name arity conf opcode.
    host_byte_only_profile tag name arity conf opcode ⇒
    host_call_table_lookup host_call_table tag name arity = NONE
Proof
  Cases_on ‘tag’ \\
  rw[host_byte_only_profile_def, host_byte_profile_def,
     host_eval_profile_def, host_byte_conf_len_def,
     host_call_table_def, host_call_table_lookup_def] \\
  gvs[]
QED

Theorem rec_add_right_member_sound:
  ∀ys original x out.
    MEM out (rec_add_right original x ys) ⇒
    (∃xi yi. out = IntLit (int_add xi yi)) ∨
    out = error_atom original (Sym 10)
Proof
  Induct \\ rw[rec_add_right_def] \\
  Cases_on ‘x’ \\ Cases_on ‘h’ \\
  fs[rec_add_right_def] \\
  rw[] \\
  metis_tac[]
QED

Theorem rec_add_values_member_sound:
  ∀xs ys original out.
    MEM out (rec_add_values original xs ys) ⇒
    (∃xi yi. out = IntLit (int_add xi yi)) ∨
    out = error_atom original (Sym 10)
Proof
  Induct \\ rw[rec_add_values_def] >-
    metis_tac[rec_add_right_member_sound] \\
  metis_tac[]
QED

Theorem rec_add_right_member_input_sound:
  ∀original x ys out.
    MEM out (rec_add_right original x ys) ⇒
    (∃xi yi.
       x = IntLit xi ∧ MEM (IntLit yi) ys ∧
       out = IntLit (int_add xi yi)) ∨
    out = error_atom original (Sym 10)
Proof
  ho_match_mp_tac rec_add_right_ind \\
  rw[rec_add_right_def] \\
  metis_tac[]
QED

Theorem rec_add_values_member_input_sound:
  ∀xs ys original out.
    MEM out (rec_add_values original xs ys) ⇒
    (∃xi yi.
       MEM (IntLit xi) xs ∧ MEM (IntLit yi) ys ∧
       out = IntLit (int_add xi yi)) ∨
    out = error_atom original (Sym 10)
Proof
  Induct \\ rw[rec_add_values_def] >-
    metis_tac[rec_add_right_member_input_sound] \\
  metis_tac[]
QED

Theorem rec_mul_right_member_input_sound:
  ∀original x ys out.
    MEM out (rec_mul_right original x ys) ⇒
    (∃xi yi.
       x = IntLit xi ∧ MEM (IntLit yi) ys ∧
       out = IntLit (int_mul xi yi)) ∨
    out = error_atom original (Sym 10)
Proof
  ho_match_mp_tac rec_mul_right_ind \\
  rw[rec_mul_right_def] \\
  metis_tac[]
QED

Theorem rec_mul_values_member_input_sound:
  ∀xs ys original out.
    MEM out (rec_mul_values original xs ys) ⇒
    (∃xi yi.
       MEM (IntLit xi) xs ∧ MEM (IntLit yi) ys ∧
       out = IntLit (int_mul xi yi)) ∨
    out = error_atom original (Sym 10)
Proof
  Induct \\ rw[rec_mul_values_def] >-
    metis_tac[rec_mul_right_member_input_sound] \\
  metis_tac[]
QED

Theorem rec_sub_right_member_input_sound:
  ∀original x ys out.
    MEM out (rec_sub_right original x ys) ⇒
    (∃xi yi.
       x = IntLit xi ∧ MEM (IntLit yi) ys ∧
       out = IntLit (xi - yi)) ∨
    out = error_atom original (Sym 10)
Proof
  ho_match_mp_tac rec_sub_right_ind \\
  rw[rec_sub_right_def] \\
  metis_tac[]
QED

Theorem rec_sub_values_member_input_sound:
  ∀xs ys original out.
    MEM out (rec_sub_values original xs ys) ⇒
    (∃xi yi.
       MEM (IntLit xi) xs ∧ MEM (IntLit yi) ys ∧
       out = IntLit (xi - yi)) ∨
    out = error_atom original (Sym 10)
Proof
  Induct \\ rw[rec_sub_values_def] >-
    metis_tac[rec_sub_right_member_input_sound] \\
  metis_tac[]
QED

Theorem rec_lt_right_member_input_sound:
  ∀original x ys out.
    MEM out (rec_lt_right original x ys) ⇒
    (∃xi yi.
       x = IntLit xi ∧ MEM (IntLit yi) ys ∧
       out = (if int_lt xi yi then Sym 8 else Sym 9)) ∨
    out = error_atom original (Sym 10)
Proof
  ho_match_mp_tac rec_lt_right_ind \\
  rw[rec_lt_right_def] \\
  metis_tac[]
QED

Theorem rec_lt_values_member_input_sound:
  ∀xs ys original out.
    MEM out (rec_lt_values original xs ys) ⇒
    (∃xi yi.
       MEM (IntLit xi) xs ∧ MEM (IntLit yi) ys ∧
       out = (if int_lt xi yi then Sym 8 else Sym 9)) ∨
    out = error_atom original (Sym 10)
Proof
  Induct \\ rw[rec_lt_values_def] >-
    metis_tac[rec_lt_right_member_input_sound] \\
  metis_tac[]
QED

Theorem rec_eq_right_member_input_sound:
  ∀ys original x out.
    MEM out (rec_eq_right original x ys) ⇒
    ∃y. MEM y ys ∧ out = (if x = y then Sym 8 else Sym 9)
Proof
  Induct \\ rw[rec_eq_right_def] \\
  metis_tac[]
QED

Theorem rec_eq_values_member_input_sound:
  ∀xs ys original out.
    MEM out (rec_eq_values original xs ys) ⇒
    ∃x y.
      MEM x xs ∧ MEM y ys ∧
      out = (if x = y then Sym 8 else Sym 9)
Proof
  Induct \\ rw[rec_eq_values_def] >-
    (drule rec_eq_right_member_input_sound \\ rw[] \\
     qexists_tac ‘h’ \\ qexists_tac ‘y’ \\ rw[]) \\
  first_x_assum drule \\ rw[] \\
  qexists_tac ‘x’ \\ qexists_tac ‘y’ \\ rw[]
QED

Theorem rec_and_right_member_input_sound:
  ∀ys original x out.
    MEM out (rec_and_right original x ys) ⇒
    ∃y. MEM y ys ∧ out = bool_and_result original x y
Proof
  Induct \\ rw[rec_and_right_def] \\
  metis_tac[]
QED

Theorem rec_and_values_member_input_sound:
  ∀xs ys original out.
    MEM out (rec_and_values original xs ys) ⇒
    ∃x y.
      MEM x xs ∧ MEM y ys ∧
      out = bool_and_result original x y
Proof
  Induct \\ rw[rec_and_values_def] >-
    metis_tac[rec_and_right_member_input_sound] \\
  metis_tac[]
QED

Theorem rec_or_right_member_input_sound:
  ∀ys original x out.
    MEM out (rec_or_right original x ys) ⇒
    ∃y. MEM y ys ∧ out = bool_or_result original x y
Proof
  Induct \\ rw[rec_or_right_def] \\
  metis_tac[]
QED

Theorem rec_or_values_member_input_sound:
  ∀xs ys original out.
    MEM out (rec_or_values original xs ys) ⇒
    ∃x y.
      MEM x xs ∧ MEM y ys ∧
      out = bool_or_result original x y
Proof
  Induct \\ rw[rec_or_values_def] >-
    metis_tac[rec_or_right_member_input_sound] \\
  metis_tac[]
QED

Theorem rec_not_values_member_input_sound:
  ∀xs original out.
    MEM out (rec_not_values original xs) ⇒
    ∃x. MEM x xs ∧ out = bool_not_result original x
Proof
  Induct \\ rw[rec_not_values_def] \\
  metis_tac[]
QED

Theorem rec_add_right_nonempty:
  ∀ys original x. ys ≠ [] ⇒ rec_add_right original x ys ≠ []
Proof
  Cases \\ rw[rec_add_right_def] \\
  Cases_on ‘x’ \\ Cases_on ‘h’ \\ rw[rec_add_right_def]
QED

Theorem rec_add_values_nonempty:
  ∀xs ys original.
    xs ≠ [] ∧ ys ≠ [] ⇒ rec_add_values original xs ys ≠ []
Proof
  Cases \\ Cases_on ‘ys’ \\
  rw[rec_add_values_def] \\
  Cases_on ‘rec_add_right original h (h'::t')’ \\
  fs[rec_add_right_nonempty]
QED

Theorem rec_mul_right_nonempty:
  ∀ys original x. ys ≠ [] ⇒ rec_mul_right original x ys ≠ []
Proof
  Cases \\ rw[rec_mul_right_def] \\
  Cases_on ‘x’ \\ Cases_on ‘h’ \\ rw[rec_mul_right_def]
QED

Theorem rec_mul_values_nonempty:
  ∀xs ys original.
    xs ≠ [] ∧ ys ≠ [] ⇒ rec_mul_values original xs ys ≠ []
Proof
  Cases \\ Cases_on ‘ys’ \\
  rw[rec_mul_values_def] \\
  Cases_on ‘rec_mul_right original h (h'::t')’ \\
  fs[rec_mul_right_nonempty]
QED

Theorem rec_sub_right_nonempty:
  ∀ys original x. ys ≠ [] ⇒ rec_sub_right original x ys ≠ []
Proof
  Cases \\ rw[rec_sub_right_def] \\
  Cases_on ‘x’ \\ Cases_on ‘h’ \\ rw[rec_sub_right_def]
QED

Theorem rec_sub_values_nonempty:
  ∀xs ys original.
    xs ≠ [] ∧ ys ≠ [] ⇒ rec_sub_values original xs ys ≠ []
Proof
  Cases \\ Cases_on ‘ys’ \\
  rw[rec_sub_values_def] \\
  Cases_on ‘rec_sub_right original h (h'::t')’ \\
  fs[rec_sub_right_nonempty]
QED

Theorem rec_lt_right_nonempty:
  ∀ys original x. ys ≠ [] ⇒ rec_lt_right original x ys ≠ []
Proof
  Cases \\ rw[rec_lt_right_def] \\
  Cases_on ‘x’ \\ Cases_on ‘h’ \\ rw[rec_lt_right_def]
QED

Theorem rec_lt_values_nonempty:
  ∀xs ys original.
    xs ≠ [] ∧ ys ≠ [] ⇒ rec_lt_values original xs ys ≠ []
Proof
  Cases \\ Cases_on ‘ys’ \\
  rw[rec_lt_values_def] \\
  Cases_on ‘rec_lt_right original h (h'::t')’ \\
  fs[rec_lt_right_nonempty]
QED

Theorem rec_eq_right_nonempty:
  ∀ys original x. ys ≠ [] ⇒ rec_eq_right original x ys ≠ []
Proof
  Cases \\ rw[rec_eq_right_def]
QED

Theorem rec_eq_values_nonempty:
  ∀xs ys original.
    xs ≠ [] ∧ ys ≠ [] ⇒ rec_eq_values original xs ys ≠ []
Proof
  Cases \\ Cases_on ‘ys’ \\
  rw[rec_eq_values_def] \\
  Cases_on ‘rec_eq_right original h (h'::t')’ \\
  fs[rec_eq_right_nonempty]
QED

Theorem rec_not_values_nonempty:
  ∀xs original. xs ≠ [] ⇒ rec_not_values original xs ≠ []
Proof
  Cases \\ rw[rec_not_values_def]
QED

Theorem rec_and_right_nonempty:
  ∀ys original x. ys ≠ [] ⇒ rec_and_right original x ys ≠ []
Proof
  Cases \\ rw[rec_and_right_def]
QED

Theorem rec_and_values_nonempty:
  ∀xs ys original.
    xs ≠ [] ∧ ys ≠ [] ⇒ rec_and_values original xs ys ≠ []
Proof
  Cases \\ Cases_on ‘ys’ \\ rw[rec_and_values_def, rec_and_right_def]
QED

Theorem rec_or_right_nonempty:
  ∀ys original x. ys ≠ [] ⇒ rec_or_right original x ys ≠ []
Proof
  Cases \\ rw[rec_or_right_def]
QED

Theorem rec_or_values_nonempty:
  ∀xs ys original.
    xs ≠ [] ∧ ys ≠ [] ⇒ rec_or_values original xs ys ≠ []
Proof
  Cases \\ Cases_on ‘ys’ \\ rw[rec_or_values_def, rec_or_right_def]
QED

Theorem return_payloads_rest_member_sound:
  ∀vals original out.
    MEM out (return_payloads_rest original vals) ⇒
    (∃atom value.
       MEM atom vals ∧ return_payload_of atom = SOME value ∧ out = value) ∨
    out = error_atom original (Sym 22)
Proof
  Induct \\ rw[return_payloads_rest_def] \\
  Cases_on ‘return_payload_of h’ \\ gvs[] \\
  metis_tac[]
QED

Theorem return_payloads_member_sound:
  ∀vals original out.
    MEM out (return_payloads original vals) ⇒
    (∃atom value.
       MEM atom vals ∧ return_payload_of atom = SOME value ∧ out = value) ∨
    out = error_atom original (Sym 22)
Proof
  Cases \\ rw[return_payloads_def] \\
  Cases_on ‘return_payload_of h’ \\ gvs[] \\
  metis_tac[return_payloads_rest_member_sound]
QED

Theorem return_payloads_nonempty:
  ∀vals original. return_payloads original vals ≠ []
Proof
  Cases \\ rw[return_payloads_def] \\
  Cases_on ‘return_payload_of h’ \\ rw[]
QED

Theorem eval_m1_rec_return_nonempty:
  ∀fuel space value.
    eval_m1_rec (SUC fuel) space (Expr [Sym 19; value]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  fs[]
QED

Theorem eval_m1_rec_eval_nonempty:
  ∀fuel space body.
    eval_m1_rec fuel space body ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 20; body]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  Cases_on ‘eval_m1_rec fuel space body = [body]’ \\ rw[]
QED

Theorem eval_m1_rec_chain_member_sound:
  ∀vals fuel space v templ out.
    MEM out (eval_m1_rec_chain fuel space v vals templ) ⇒
    ∃x.
      MEM x vals ∧
      MEM out (eval_m1_rec fuel space (apply_subst [Bind v x] templ))
Proof
  Induct \\ rw[eval_m1_rec_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_chain_nonempty:
  ∀vals fuel space v templ.
    (∃x.
       MEM x vals ∧
       eval_m1_rec fuel space (apply_subst [Bind v x] templ) ≠ []) ⇒
    eval_m1_rec_chain fuel space v vals templ ≠ []
Proof
  Induct \\ rw[eval_m1_rec_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_add_member_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 11; a; b])) ⇒
    (∃x y. out = IntLit (int_add x y)) ∨
    out = error_atom (Expr [Sym 11; a; b]) (Sym 10)
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_add_values_member_sound]
QED

Theorem eval_m1_rec_add_member_input_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 11; a; b])) ⇒
    (∃x y.
       MEM (IntLit x) (eval_m1_rec fuel space a) ∧
       MEM (IntLit y) (eval_m1_rec fuel space b) ∧
       out = IntLit (int_add x y)) ∨
    out = error_atom (Expr [Sym 11; a; b]) (Sym 10)
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_add_values_member_input_sound]
QED

Theorem eval_m1_rec_mul_member_input_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 45; a; b])) ⇒
    (∃x y.
       MEM (IntLit x) (eval_m1_rec fuel space a) ∧
       MEM (IntLit y) (eval_m1_rec fuel space b) ∧
       out = IntLit (int_mul x y)) ∨
    out = error_atom (Expr [Sym 45; a; b]) (Sym 10)
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_mul_values_member_input_sound]
QED

Theorem eval_m1_rec_sub_member_input_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 46; a; b])) ⇒
    (∃x y.
       MEM (IntLit x) (eval_m1_rec fuel space a) ∧
       MEM (IntLit y) (eval_m1_rec fuel space b) ∧
       out = IntLit (x - y)) ∨
    out = error_atom (Expr [Sym 46; a; b]) (Sym 10)
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_sub_values_member_input_sound]
QED

Theorem eval_m1_rec_lt_member_input_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 12; a; b])) ⇒
    (∃x y.
       MEM (IntLit x) (eval_m1_rec fuel space a) ∧
       MEM (IntLit y) (eval_m1_rec fuel space b) ∧
       out = (if int_lt x y then Sym 8 else Sym 9)) ∨
    out = error_atom (Expr [Sym 12; a; b]) (Sym 10)
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_lt_values_member_input_sound]
QED

Theorem eval_m1_rec_eq_member_input_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 47; a; b])) ⇒
    ∃x y.
      MEM x (eval_m1_rec fuel space a) ∧
      MEM y (eval_m1_rec fuel space b) ∧
      out = (if x = y then Sym 8 else Sym 9)
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_eq_values_member_input_sound]
QED

Theorem eval_m1_rec_and_member_input_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 31; a; b])) ⇒
    ∃x y.
      MEM x (eval_m1_rec fuel space a) ∧
      MEM y (eval_m1_rec fuel space b) ∧
      out = bool_and_result (Expr [Sym 31; a; b]) x y
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_and_values_member_input_sound]
QED

Theorem eval_m1_rec_or_member_input_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 32; a; b])) ⇒
    ∃x y.
      MEM x (eval_m1_rec fuel space a) ∧
      MEM y (eval_m1_rec fuel space b) ∧
      out = bool_or_result (Expr [Sym 32; a; b]) x y
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_or_values_member_input_sound]
QED

Theorem eval_m1_rec_not_member_input_sound:
  ∀fuel space a out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 33; a])) ⇒
    ∃x.
      MEM x (eval_m1_rec fuel space a) ∧
      out = bool_not_result (Expr [Sym 33; a]) x
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_not_values_member_input_sound]
QED

Theorem eval_m1_rec_function_member_sound:
  ∀fuel space body out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 18; body])) ⇒
    (∃atom value.
       MEM atom (eval_m1_rec fuel space body) ∧
       return_payload_of atom = SOME value ∧ out = value) ∨
    out = error_atom (Expr [Sym 18; body]) (Sym 22)
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[return_payloads_member_sound]
QED

Theorem eval_m1_rec_chain_branch_member_sound:
  ∀fuel space nested v templ out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 21; nested; Var v; templ])) ⇒
    ∃x.
      MEM x (eval_m1_rec fuel space nested) ∧
      MEM out (eval_m1_rec fuel space (apply_subst [Bind v x] templ))
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[eval_m1_rec_chain_member_sound]
QED

Theorem eval_m1_rec_add_nonempty:
  ∀fuel space a b.
    eval_m1_rec fuel space a ≠ [] ∧
    eval_m1_rec fuel space b ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 11; a; b]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_add_values_nonempty]
QED

Theorem eval_m1_rec_mul_nonempty:
  ∀fuel space a b.
    eval_m1_rec fuel space a ≠ [] ∧
    eval_m1_rec fuel space b ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 45; a; b]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_mul_values_nonempty]
QED

Theorem eval_m1_rec_sub_nonempty:
  ∀fuel space a b.
    eval_m1_rec fuel space a ≠ [] ∧
    eval_m1_rec fuel space b ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 46; a; b]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_sub_values_nonempty]
QED

Theorem eval_m1_rec_lt_nonempty:
  ∀fuel space a b.
    eval_m1_rec fuel space a ≠ [] ∧
    eval_m1_rec fuel space b ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 12; a; b]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_lt_values_nonempty]
QED

Theorem eval_m1_rec_eq_nonempty:
  ∀fuel space a b.
    eval_m1_rec fuel space a ≠ [] ∧
    eval_m1_rec fuel space b ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 47; a; b]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_eq_values_nonempty]
QED

Theorem eval_m1_rec_not_nonempty:
  ∀fuel space a.
    eval_m1_rec fuel space a ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 33; a]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_not_values_nonempty]
QED

Theorem eval_m1_rec_and_nonempty:
  ∀fuel space a b.
    eval_m1_rec fuel space a ≠ [] ∧
    eval_m1_rec fuel space b ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 31; a; b]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_and_values_nonempty]
QED

Theorem eval_m1_rec_or_nonempty:
  ∀fuel space a b.
    eval_m1_rec fuel space a ≠ [] ∧
    eval_m1_rec fuel space b ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 32; a; b]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[rec_or_values_nonempty]
QED

Theorem eval_m1_rec_function_nonempty:
  ∀fuel space body.
    eval_m1_rec (SUC fuel) space (Expr [Sym 18; body]) ≠ []
Proof
  rw[eval_m1_rec_def, return_payloads_nonempty]
QED

Theorem eval_m1_rec_chain_branch_nonempty:
  ∀fuel space nested v templ.
    (∃x.
       MEM x (eval_m1_rec fuel space nested) ∧
       eval_m1_rec fuel space (apply_subst [Bind v x] templ) ≠ []) ⇒
    eval_m1_rec (SUC fuel) space
      (Expr [Sym 21; nested; Var v; templ]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[eval_m1_rec_chain_nonempty]
QED

Theorem evalc_values_nonempty:
  ∀vals space original expected.
    vals ≠ [] ⇒ evalc_values space original expected vals ≠ []
Proof
  Cases \\ rw[evalc_values_def]
QED

Theorem eval_typed_fragment_bad_add_nonempty:
  ∀fuel space atom.
    hol_typed_add_bad space atom ⇒
    eval_typed_fragment fuel space atom ≠ []
Proof
  rw[eval_typed_fragment_def, typed_eval_m1_rec_def]
QED

Theorem eval_evalc_fragment_nonempty:
  ∀fuel space term expected.
    typed_eval_m1_rec fuel space term ≠ [] ⇒
    eval_evalc_fragment fuel space (Expr [Sym 57; term; expected]) ≠ []
Proof
  rw[eval_evalc_fragment_def, evalc_values_nonempty]
QED

Theorem eval_m1_rec_evalc_nonempty:
  ∀fuel space term expected.
    hol_typed_add_bad space term ∨ eval_m1_rec fuel space term ≠ [] ⇒
    eval_m1_rec (SUC fuel) space (Expr [Sym 57; term; expected]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  Cases_on ‘hol_typed_add_bad space term’ \\
  rw[evalc_values_nonempty]
QED

Theorem eval_m1_rec_vec_cons_nonempty:
  ∀fuel space elem tail.
    eval_m1_rec (SUC fuel) space (Expr [Sym 58; elem; tail]) ≠ []
Proof
  rw[eval_m1_rec_def]
QED

Theorem eval_vec_cons_fragment_nonempty:
  ∀space elem tail.
    eval_vec_cons_fragment space (Expr [Sym 58; elem; tail]) ≠ []
Proof
  rw[eval_vec_cons_fragment_def]
QED

Theorem eval_case_values_with_nonempty:
  ∀vals ev branches.
    (∃value.
       MEM value vals ∧ eval_case_one_with ev value branches ≠ []) ⇒
    eval_case_values_with ev vals branches ≠ []
Proof
  Induct \\ rw[eval_case_values_with_def] \\
  Cases_on ‘eval_case_one_with ev h branches’ \\
  rw[] \\
  metis_tac[]
QED

Theorem eval_switch_values_with_nonempty:
  ∀vals ev branches.
    (∃value.
       MEM value vals ∧ eval_switch_one_with ev value branches ≠ []) ⇒
    eval_switch_values_with ev vals branches ≠ []
Proof
  Induct \\ rw[eval_switch_values_with_def] \\
  Cases_on ‘eval_switch_one_with ev h branches’ \\
  rw[] \\
  metis_tac[]
QED

Theorem eval_m1_rec_case_branch_nonempty:
  ∀fuel space scrut branches.
    (∃value.
       MEM value (eval_m1_rec fuel space scrut) ∧
       eval_case_one_with (eval_m1_rec fuel space) value branches ≠ []) ⇒
    eval_m1_rec (SUC fuel) space
      (Expr [Sym 54; scrut; Expr branches]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[eval_case_values_with_nonempty]
QED

Theorem eval_m1_rec_switch_branch_nonempty:
  ∀fuel space scrut branches.
    (∃value.
       MEM value (eval_m1_rec fuel space scrut) ∧
       eval_switch_one_with (λa. eval_m1_rec fuel space a) value branches ≠ []) ⇒
    eval_m1_rec (SUC fuel) space
      (Expr [Sym 55; scrut; Expr branches]) ≠ []
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[eval_switch_values_with_nonempty]
QED

Theorem eval_m1_rec_chain_bad_var_nonempty:
  ∀fuel space nested bad_var templ.
    (∀v. bad_var ≠ Var v) ⇒
    eval_m1_rec (SUC fuel) space
      (Expr [Sym 21; nested; bad_var; templ]) ≠ []
Proof
  Cases_on ‘bad_var’ \\ rw[eval_m1_rec_def]
QED

Theorem eval_m1_rec_case_bad_branches_nonempty:
  ∀fuel space scrut bad_branches.
    (∀branches. bad_branches ≠ Expr branches) ⇒
    eval_m1_rec (SUC fuel) space
      (Expr [Sym 54; scrut; bad_branches]) ≠ []
Proof
  Cases_on ‘bad_branches’ \\ rw[eval_m1_rec_def]
QED

Theorem eval_m1_rec_switch_bad_branches_nonempty:
  ∀fuel space scrut bad_branches.
    (∀branches. bad_branches ≠ Expr branches) ⇒
    eval_m1_rec (SUC fuel) space
      (Expr [Sym 55; scrut; bad_branches]) ≠ []
Proof
  Cases_on ‘bad_branches’ \\ rw[eval_m1_rec_def]
QED

Theorem eval_m1_rec_let_star_bad_bindings_nonempty:
  ∀fuel space bad_bindings body.
    (∀bindings. bad_bindings ≠ Expr bindings) ⇒
    eval_m1_rec (SUC fuel) space
      (Expr [Sym 56; bad_bindings; body]) ≠ []
Proof
  Cases_on ‘bad_bindings’ \\ rw[eval_m1_rec_def]
QED

Theorem evalc_values_member_sound:
  ∀vals space original expected out.
    MEM out (evalc_values space original expected vals) ⇒
    ∃value.
      MEM value vals ∧
      ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
       (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
        out = error_atom original (Sym 10)))
Proof
  Induct \\ rw[evalc_values_def] \\
  metis_tac[]
QED

Theorem evalc_like_member_sound:
  ∀fuel space atom expected out.
    MEM out (evalc_like fuel space atom expected) ⇒
    ∃value.
      MEM value (typed_eval_m1_rec fuel space atom) ∧
      ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
       (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
        out = error_atom atom (Sym 10)))
Proof
  rw[evalc_like_def] \\
  metis_tac[evalc_values_member_sound]
QED

Theorem eval_m1_rec_evalc_member_sound:
  ∀fuel space term expected out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 57; term; expected])) ⇒
    ∃value.
      MEM value
        (if hol_typed_add_bad space term
         then [error_atom term (Sym 10)]
         else eval_m1_rec fuel space term) ∧
      ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
       (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
        out = error_atom term (Sym 10)))
Proof
  rw[eval_m1_rec_def] \\
  drule evalc_values_member_sound \\
  rw[] \\
  qexists_tac ‘value’ \\
  rw[]
QED

Theorem eval_m1_rec_evalc_non_error_type_sound:
  ∀fuel space term expected out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 57; term; expected])) ∧
    out ≠ error_atom term (Sym 10) ⇒
    hol_any_type_match expected
      (hol_declared_or_default_type_lookup space out)
Proof
  rw[] \\
  drule eval_m1_rec_evalc_member_sound \\
  rw[]
QED

Theorem eval_m1_rec_evalc_type_or_error_sound:
  ∀fuel space term expected out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 57; term; expected])) ⇒
    out = error_atom term (Sym 10) ∨
    hol_any_type_match expected
      (hol_declared_or_default_type_lookup space out)
Proof
  rw[] \\
  drule eval_m1_rec_evalc_member_sound \\
  rw[] \\
  metis_tac[]
QED

Theorem typed_eval_m1_rec_bad_add_error:
  ∀fuel space atom.
    hol_typed_add_bad space atom ⇒
    typed_eval_m1_rec fuel space atom = [error_atom atom (Sym 10)]
Proof
  rw[typed_eval_m1_rec_def]
QED

Theorem typed_eval_m1_rec_not_bad_eq_eval:
  ∀fuel space atom.
    ¬hol_typed_add_bad space atom ⇒
    typed_eval_m1_rec fuel space atom = eval_m1_rec fuel space atom
Proof
  rw[typed_eval_m1_rec_def]
QED

Theorem eval_case_one_member_sound:
  ∀branches fuel space value original out.
    MEM out (eval_case_one fuel space value branches original) ⇒
    ∃branch pattern body bs.
      MEM branch branches ∧ branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (eval_m1_rec fuel space (apply_subst bs body))
Proof
  Induct \\ rw[eval_case_one_def] \\
  Cases_on ‘branch_pair h’ \\ gvs[] >-
    metis_tac[] \\
  PairCases_on ‘x’ \\
  Cases_on ‘match_atom x0 value []’ \\ gvs[] \\
  metis_tac[]
QED

Theorem eval_case_values_member_sound:
  ∀vals fuel space branches original out.
    MEM out (eval_case_values fuel space vals branches original) ⇒
    ∃value.
      MEM value vals ∧
      MEM out (eval_case_one fuel space value branches original)
Proof
  Induct \\ rw[eval_case_values_def] \\
  metis_tac[]
QED

Theorem eval_case_like_member_sound:
  ∀fuel space scrut branches original out.
    MEM out (eval_case_like fuel space scrut branches original) ⇒
    ∃value.
      MEM value (eval_m1_rec fuel space scrut) ∧
      MEM out (eval_case_one fuel space value branches original)
Proof
  rw[eval_case_like_def] \\
  metis_tac[eval_case_values_member_sound]
QED

Theorem eval_case_one_with_member_sound:
  ∀branches ev value out.
    MEM out (eval_case_one_with ev value branches) ⇒
    ∃branch pattern body bs.
      MEM branch branches ∧ branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (ev (apply_subst bs body))
Proof
  Induct \\ rw[eval_case_one_with_def] \\
  Cases_on ‘branch_pair h’ \\ gvs[] >-
    metis_tac[] \\
  PairCases_on ‘x’ \\
  Cases_on ‘match_atom x0 value []’ \\ gvs[] \\
  metis_tac[]
QED

Theorem eval_case_values_with_member_sound:
  ∀vals ev branches out.
    MEM out (eval_case_values_with ev vals branches) ⇒
    ∃value.
      MEM value vals ∧ MEM out (eval_case_one_with ev value branches)
Proof
  Induct \\ rw[eval_case_values_with_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_case_branch_member_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 54; scrut; Expr branches])) ⇒
    ∃value.
      MEM value (eval_m1_rec fuel space scrut) ∧
      MEM out (eval_case_one_with (eval_m1_rec fuel space) value branches)
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[eval_case_values_with_member_sound]
QED

Theorem eval_switch_one_member_sound:
  ∀branches fuel space value original out.
    MEM out (eval_switch_one fuel space value branches original) ⇒
    ∃branch pattern body bs.
      MEM branch branches ∧ branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (eval_m1_rec fuel space (apply_subst bs body))
Proof
  Induct \\ rw[eval_switch_one_def] \\
  Cases_on ‘branch_pair h’ \\ gvs[] >-
    metis_tac[] \\
  PairCases_on ‘x’ \\
  Cases_on ‘match_atom x0 value []’ \\ gvs[] \\
  metis_tac[]
QED

Theorem eval_switch_values_member_sound:
  ∀vals fuel space branches original out.
    MEM out (eval_switch_values fuel space vals branches original) ⇒
    ∃value.
      MEM value vals ∧
      MEM out (eval_switch_one fuel space value branches original)
Proof
  Induct \\ rw[eval_switch_values_def] \\
  metis_tac[]
QED

Theorem eval_switch_like_member_sound:
  ∀fuel space scrut branches original out.
    MEM out (eval_switch_like fuel space scrut branches original) ⇒
    ∃value.
      MEM value (eval_m1_rec fuel space scrut) ∧
      MEM out (eval_switch_one fuel space value branches original)
Proof
  rw[eval_switch_like_def] \\
  metis_tac[eval_switch_values_member_sound]
QED

Theorem eval_switch_one_with_member_sound:
  ∀branches ev value out.
    MEM out (eval_switch_one_with ev value branches) ⇒
    ∃branch pattern body bs.
      MEM branch branches ∧ branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (ev (apply_subst bs body))
Proof
  Induct \\ rw[eval_switch_one_with_def] \\
  Cases_on ‘branch_pair h’ \\ gvs[] >-
    metis_tac[] \\
  PairCases_on ‘x’ \\
  Cases_on ‘match_atom x0 value []’ \\ gvs[] \\
  metis_tac[]
QED

Theorem eval_switch_values_with_member_sound:
  ∀vals ev branches out.
    MEM out (eval_switch_values_with ev vals branches) ⇒
    ∃value.
      MEM value vals ∧ MEM out (eval_switch_one_with ev value branches)
Proof
  Induct \\ rw[eval_switch_values_with_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_switch_branch_member_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 55; scrut; Expr branches])) ⇒
    ∃value.
      MEM value (eval_m1_rec fuel space scrut) ∧
      MEM out (eval_switch_one_with (λa. eval_m1_rec fuel space a) value branches)
Proof
  rw[eval_m1_rec_def] \\
  metis_tac[eval_switch_values_with_member_sound]
QED

Theorem eval_let1_values_member_sound:
  ∀vals fuel space v body original out.
    MEM out (eval_let1_values fuel space v vals body original) ⇒
    ∃value.
      MEM value vals ∧
      MEM out (eval_m1_rec fuel space (apply_subst [Bind v value] body))
Proof
  Induct \\ rw[eval_let1_values_def] \\
  metis_tac[]
QED

Theorem eval_let1_like_valid_member_sound:
  ∀fuel space binding body original out v rhs.
    let_binding_pair binding = SOME (v, rhs) ∧
    MEM out (eval_let1_like fuel space binding body original) ⇒
    ∃evaluated.
      MEM evaluated (eval_m1_rec fuel space rhs) ∧
      MEM out
        (eval_m1_rec fuel space (apply_subst [Bind v evaluated] body))
Proof
  rw[eval_let1_like_def] \\ gvs[] \\
  drule eval_let1_values_member_sound \\ rw[] \\
  qexists_tac ‘value’ \\ rw[]
QED

Theorem eval_let1_like_invalid_binding:
  ∀fuel space binding body original.
    let_binding_pair binding = NONE ⇒
    eval_let1_like fuel space binding body original =
    [error_atom original (Sym 10)]
Proof
  rw[eval_let1_like_def]
QED

Theorem eval_let_star_with_invalid_binding:
  ∀fuel ev binding rest body original.
    let_binding_pair binding = NONE ⇒
    eval_let_star_with (SUC fuel) ev (binding :: rest) body original =
    [error_atom original (Sym 10)]
Proof
  rw[eval_let_star_with_def]
QED

Theorem eval_let_star_with_member_iff:
  ∀fuel ev bindings body original out.
    MEM out (eval_let_star_with fuel ev bindings body original) ⇔
    let_star_provenance fuel ev bindings body original out
Proof
  Induct \\ rw[eval_let_star_with_def, let_star_provenance_def] \\
  Cases_on ‘bindings’ \\ rw[eval_let_star_with_def, let_star_provenance_def] \\
  Cases_on ‘let_binding_pair h’ \\ rw[eval_let_star_with_def, let_star_provenance_def] \\
  PairCases_on ‘x’ \\
  rw[MEM_FLAT, MEM_MAP, PULL_EXISTS] \\
  metis_tac[]
QED

Theorem eval_let_star_with_member_sound:
  ∀fuel ev bindings body original out.
    MEM out (eval_let_star_with fuel ev bindings body original) ⇒
    let_star_provenance fuel ev bindings body original out
Proof
  rw[eval_let_star_with_member_iff]
QED

Theorem eval_let_star_with_provenance_nonempty:
  ∀fuel ev bindings body original.
    (∃out. let_star_provenance fuel ev bindings body original out) ⇒
    eval_let_star_with fuel ev bindings body original ≠ []
Proof
  rw[] \\
  ‘MEM out (eval_let_star_with fuel ev bindings body original)’ by
    metis_tac[eval_let_star_with_member_iff] \\
  Cases_on ‘eval_let_star_with fuel ev bindings body original’ \\
  gvs[]
QED

Theorem eval_m1_rec_let_star_branch:
  ∀fuel space bindings body.
    eval_m1_rec (SUC fuel) space
      (Expr [Sym 56; Expr bindings; body]) =
    eval_let_star_with (SUC (LENGTH bindings))
      (λa. eval_m1_rec fuel space a) bindings body
      (Expr [Sym 56; Expr bindings; body])
Proof
  rw[eval_m1_rec_def]
QED

Theorem eval_m1_rec_let_star_member_iff:
  ∀fuel space bindings body out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 56; Expr bindings; body])) ⇔
    let_star_provenance (SUC (LENGTH bindings))
      (λa. eval_m1_rec fuel space a) bindings body
      (Expr [Sym 56; Expr bindings; body]) out
Proof
  rw[eval_m1_rec_let_star_branch, eval_let_star_with_member_iff]
QED

Theorem eval_m1_rec_let_star_member_sound:
  ∀fuel space bindings body out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 56; Expr bindings; body])) ⇒
    let_star_provenance (SUC (LENGTH bindings))
      (λa. eval_m1_rec fuel space a) bindings body
      (Expr [Sym 56; Expr bindings; body]) out
Proof
  rw[eval_m1_rec_let_star_member_iff]
QED

Theorem eval_m1_rec_let_star_provenance_nonempty:
  ∀fuel space bindings body.
    (∃out.
       let_star_provenance (SUC (LENGTH bindings))
         (λa. eval_m1_rec fuel space a) bindings body
         (Expr [Sym 56; Expr bindings; body]) out) ⇒
    eval_m1_rec (SUC fuel) space
      (Expr [Sym 56; Expr bindings; body]) ≠ []
Proof
  rw[eval_m1_rec_let_star_branch] \\
  metis_tac[eval_let_star_with_provenance_nonempty]
QED

Theorem eval_m1_rec_case_branch_semantic_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 54; scrut; Expr branches])) ⇒
    ∃value branch pattern body bs.
      MEM value (eval_m1_rec fuel space scrut) ∧
      MEM branch branches ∧
      branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (eval_m1_rec fuel space (apply_subst bs body))
Proof
  rw[] \\
  drule eval_m1_rec_case_branch_member_sound \\
  rw[] \\
  drule eval_case_one_with_member_sound \\
  rw[] \\
  metis_tac[]
QED

Theorem eval_m1_rec_switch_branch_semantic_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 55; scrut; Expr branches])) ⇒
    ∃value branch pattern body bs.
      MEM value (eval_m1_rec fuel space scrut) ∧
      MEM branch branches ∧
      branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (eval_m1_rec fuel space (apply_subst bs body))
Proof
  rw[] \\
  drule eval_m1_rec_switch_branch_member_sound \\
  rw[] \\
  drule eval_switch_one_with_member_sound \\
  rw[] \\
  metis_tac[]
QED

Theorem eval_m1_rec_vec_cons_member_sound:
  ∀fuel space elem tail out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 58; elem; tail])) ⇒
    out = dependent_vec_cons_type space elem tail
Proof
  rw[eval_m1_rec_def]
QED

Theorem eval_m1_rec_timeout_sound:
  ∀space atom out.
    MEM out (eval_m1_rec 0 space atom) ⇒
    out = error_atom atom (Sym 3)
Proof
  rw[eval_m1_rec_def]
QED

Definition eval_m1_rec_branch_sound_def:
  eval_m1_rec_branch_sound fuel space atom out ⇔
    (∃a b.
       atom = Expr [Sym 11; a; b] ∧
       ((∃x y.
          MEM (IntLit x) (eval_m1_rec fuel space a) ∧
          MEM (IntLit y) (eval_m1_rec fuel space b) ∧
          out = IntLit (int_add x y)) ∨
        out = error_atom atom (Sym 10))) ∨
    (∃a b.
       atom = Expr [Sym 45; a; b] ∧
       ((∃x y.
          MEM (IntLit x) (eval_m1_rec fuel space a) ∧
          MEM (IntLit y) (eval_m1_rec fuel space b) ∧
          out = IntLit (int_mul x y)) ∨
        out = error_atom atom (Sym 10))) ∨
    (∃a b.
       atom = Expr [Sym 46; a; b] ∧
       ((∃x y.
          MEM (IntLit x) (eval_m1_rec fuel space a) ∧
          MEM (IntLit y) (eval_m1_rec fuel space b) ∧
          out = IntLit (x - y)) ∨
        out = error_atom atom (Sym 10))) ∨
    (∃a b.
       atom = Expr [Sym 12; a; b] ∧
       ((∃x y.
          MEM (IntLit x) (eval_m1_rec fuel space a) ∧
          MEM (IntLit y) (eval_m1_rec fuel space b) ∧
          out = (if int_lt x y then Sym 8 else Sym 9)) ∨
        out = error_atom atom (Sym 10))) ∨
    (∃a b x y.
       atom = Expr [Sym 47; a; b] ∧
       MEM x (eval_m1_rec fuel space a) ∧
       MEM y (eval_m1_rec fuel space b) ∧
       out = (if x = y then Sym 8 else Sym 9)) ∨
    (∃a b x y.
       atom = Expr [Sym 31; a; b] ∧
       MEM x (eval_m1_rec fuel space a) ∧
       MEM y (eval_m1_rec fuel space b) ∧
       out = bool_and_result atom x y) ∨
    (∃a b x y.
       atom = Expr [Sym 32; a; b] ∧
       MEM x (eval_m1_rec fuel space a) ∧
       MEM y (eval_m1_rec fuel space b) ∧
       out = bool_or_result atom x y) ∨
    (∃a x.
       atom = Expr [Sym 33; a] ∧
       MEM x (eval_m1_rec fuel space a) ∧
       out = bool_not_result atom x) ∨
    (∃body.
       atom = Expr [Sym 18; body] ∧
       ((∃inner value.
          MEM inner (eval_m1_rec fuel space body) ∧
          return_payload_of inner = SOME value ∧ out = value) ∨
        out = error_atom atom (Sym 22))) ∨
    (∃value.
       atom = Expr [Sym 19; value] ∧ out = atom) ∨
    (∃body.
       atom = Expr [Sym 20; body] ∧
       ((eval_m1_rec fuel space body = [body] ∧ out = Sym 23) ∨
        (eval_m1_rec fuel space body ≠ [body] ∧
         MEM out (eval_m1_rec fuel space body)))) ∨
    (∃nested v templ x.
       atom = Expr [Sym 21; nested; Var v; templ] ∧
       MEM x (eval_m1_rec fuel space nested) ∧
       MEM out (eval_m1_rec fuel space (apply_subst [Bind v x] templ))) ∨
    (∃nested bad_var templ.
       atom = Expr [Sym 21; nested; bad_var; templ] ∧
       (∀v. bad_var ≠ Var v) ∧
       out = error_atom atom (Sym 10)) ∨
    (∃term expected value.
       atom = Expr [Sym 57; term; expected] ∧
       MEM value
         (if hol_typed_add_bad space term
          then [error_atom term (Sym 10)]
          else eval_m1_rec fuel space term) ∧
       ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
        (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
         out = error_atom term (Sym 10)))) ∨
    (∃elem tail.
       atom = Expr [Sym 58; elem; tail] ∧
       out = dependent_vec_cons_type space elem tail) ∨
    (∃scrut branches value branch pattern body bs.
       atom = Expr [Sym 54; scrut; Expr branches] ∧
       MEM value (eval_m1_rec fuel space scrut) ∧
       MEM branch branches ∧
       branch_pair branch = SOME (pattern, body) ∧
       match_atom pattern value [] = SOME bs ∧
       MEM out (eval_m1_rec fuel space (apply_subst bs body))) ∨
    (∃scrut bad_branches.
       atom = Expr [Sym 54; scrut; bad_branches] ∧
       (∀branches. bad_branches ≠ Expr branches) ∧
       out = error_atom atom (Sym 10)) ∨
    (∃scrut branches value branch pattern body bs.
      atom = Expr [Sym 55; scrut; Expr branches] ∧
      MEM value (eval_m1_rec fuel space scrut) ∧
      MEM branch branches ∧
      branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (eval_m1_rec fuel space (apply_subst bs body))) ∨
    (∃scrut bad_branches.
       atom = Expr [Sym 55; scrut; bad_branches] ∧
       (∀branches. bad_branches ≠ Expr branches) ∧
       out = error_atom atom (Sym 10)) ∨
    (∃bindings body.
       atom = Expr [Sym 56; Expr bindings; body] ∧
       let_star_provenance (SUC (LENGTH bindings))
         (λa. eval_m1_rec fuel space a) bindings body atom out) ∨
    (∃bad_bindings body.
       atom = Expr [Sym 56; bad_bindings; body] ∧
       (∀bindings. bad_bindings ≠ Expr bindings) ∧
       out = error_atom atom (Sym 10))
End

Definition eval_m1_rec_proven_branch_atom_def:
  eval_m1_rec_proven_branch_atom atom ⇔
    (∃a b. atom = Expr [Sym 11; a; b]) ∨
    (∃a b. atom = Expr [Sym 45; a; b]) ∨
    (∃a b. atom = Expr [Sym 46; a; b]) ∨
    (∃a b. atom = Expr [Sym 12; a; b]) ∨
    (∃a b. atom = Expr [Sym 47; a; b]) ∨
    (∃a b. atom = Expr [Sym 31; a; b]) ∨
    (∃a b. atom = Expr [Sym 32; a; b]) ∨
    (∃a. atom = Expr [Sym 33; a]) ∨
    (∃body. atom = Expr [Sym 18; body]) ∨
    (∃value. atom = Expr [Sym 19; value]) ∨
    (∃body. atom = Expr [Sym 20; body]) ∨
    (∃nested selector templ.
       atom = Expr [Sym 21; nested; selector; templ]) ∨
    (∃term expected. atom = Expr [Sym 57; term; expected]) ∨
    (∃elem tail. atom = Expr [Sym 58; elem; tail]) ∨
    (∃scrut branches. atom = Expr [Sym 54; scrut; branches]) ∨
    (∃scrut branches. atom = Expr [Sym 55; scrut; branches]) ∨
    (∃bindings body. atom = Expr [Sym 56; bindings; body])
End

Theorem eval_m1_rec_add_branch_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 11; a; b])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 11; a; b]) out
Proof
  rw[] \\
  drule eval_m1_rec_add_member_input_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_mul_branch_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 45; a; b])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 45; a; b]) out
Proof
  rw[] \\
  drule eval_m1_rec_mul_member_input_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_sub_branch_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 46; a; b])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 46; a; b]) out
Proof
  rw[] \\
  drule eval_m1_rec_sub_member_input_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_lt_branch_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 12; a; b])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 12; a; b]) out
Proof
  rw[] \\
  drule eval_m1_rec_lt_member_input_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_eq_branch_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 47; a; b])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 47; a; b]) out
Proof
  rw[] \\
  drule eval_m1_rec_eq_member_input_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_and_branch_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 31; a; b])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 31; a; b]) out
Proof
  rw[] \\
  drule eval_m1_rec_and_member_input_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_or_branch_sound:
  ∀fuel space a b out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 32; a; b])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 32; a; b]) out
Proof
  rw[] \\
  drule eval_m1_rec_or_member_input_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_not_branch_sound:
  ∀fuel space a out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 33; a])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 33; a]) out
Proof
  rw[] \\
  drule eval_m1_rec_not_member_input_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_function_branch_sound:
  ∀fuel space body out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 18; body])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 18; body]) out
Proof
  rw[] \\
  drule eval_m1_rec_function_member_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_return_branch_sound:
  ∀fuel space value out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 19; value])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 19; value]) out
Proof
  rw[eval_m1_rec_def, eval_m1_rec_branch_sound_def]
QED

Theorem eval_m1_rec_eval_branch_sound:
  ∀fuel space body out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 20; body])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 20; body]) out
Proof
  rw[eval_m1_rec_def, eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_chain_branch_sound:
  ∀fuel space nested v templ out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 21; nested; Var v; templ])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 21; nested; Var v; templ]) out
Proof
  rw[] \\
  drule eval_m1_rec_chain_branch_member_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_chain_bad_var_branch_sound:
  ∀fuel space nested bad_var templ out.
    (∀v. bad_var ≠ Var v) ∧
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 21; nested; bad_var; templ])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 21; nested; bad_var; templ]) out
Proof
  Cases_on ‘bad_var’ \\
  rw[eval_m1_rec_def, eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_chain_any_branch_sound:
  ∀fuel space nested selector templ out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 21; nested; selector; templ])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 21; nested; selector; templ]) out
Proof
  Cases_on ‘selector’ \\
  rw[] \\
  metis_tac[
    eval_m1_rec_chain_branch_sound,
    eval_m1_rec_chain_bad_var_branch_sound]
QED

Theorem eval_m1_rec_evalc_branch_sound:
  ∀fuel space term expected out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 57; term; expected])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 57; term; expected]) out
Proof
  rw[] \\
  drule eval_m1_rec_evalc_member_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_vec_cons_branch_sound:
  ∀fuel space elem tail out.
    MEM out (eval_m1_rec (SUC fuel) space (Expr [Sym 58; elem; tail])) ⇒
    eval_m1_rec_branch_sound fuel space (Expr [Sym 58; elem; tail]) out
Proof
  rw[] \\
  drule eval_m1_rec_vec_cons_member_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_case_branch_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 54; scrut; Expr branches])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 54; scrut; Expr branches]) out
Proof
  rw[] \\
  drule eval_m1_rec_case_branch_semantic_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_case_bad_branches_branch_sound:
  ∀fuel space scrut bad_branches out.
    (∀branches. bad_branches ≠ Expr branches) ∧
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 54; scrut; bad_branches])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 54; scrut; bad_branches]) out
Proof
  Cases_on ‘bad_branches’ \\
  rw[eval_m1_rec_def, eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_case_any_branch_sound:
  ∀fuel space scrut branch_atom out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 54; scrut; branch_atom])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 54; scrut; branch_atom]) out
Proof
  Cases_on ‘branch_atom’ \\
  rw[] \\
  metis_tac[
    eval_m1_rec_case_branch_sound,
    eval_m1_rec_case_bad_branches_branch_sound]
QED

Theorem eval_m1_rec_switch_branch_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 55; scrut; Expr branches])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 55; scrut; Expr branches]) out
Proof
  rw[] \\
  drule eval_m1_rec_switch_branch_semantic_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_switch_bad_branches_branch_sound:
  ∀fuel space scrut bad_branches out.
    (∀branches. bad_branches ≠ Expr branches) ∧
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 55; scrut; bad_branches])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 55; scrut; bad_branches]) out
Proof
  Cases_on ‘bad_branches’ \\
  rw[eval_m1_rec_def, eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_switch_any_branch_sound:
  ∀fuel space scrut branch_atom out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 55; scrut; branch_atom])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 55; scrut; branch_atom]) out
Proof
  Cases_on ‘branch_atom’ \\
  rw[] \\
  metis_tac[
    eval_m1_rec_switch_branch_sound,
    eval_m1_rec_switch_bad_branches_branch_sound]
QED

Theorem eval_m1_rec_let_star_branch_sound:
  ∀fuel space bindings body out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 56; Expr bindings; body])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 56; Expr bindings; body]) out
Proof
  rw[] \\
  drule eval_m1_rec_let_star_member_sound \\
  rw[eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_let_star_bad_bindings_branch_sound:
  ∀fuel space bad_bindings body out.
    (∀bindings. bad_bindings ≠ Expr bindings) ∧
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 56; bad_bindings; body])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 56; bad_bindings; body]) out
Proof
  Cases_on ‘bad_bindings’ \\
  rw[eval_m1_rec_def, eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_let_star_any_branch_sound:
  ∀fuel space bindings body out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 56; bindings; body])) ⇒
    eval_m1_rec_branch_sound fuel space
      (Expr [Sym 56; bindings; body]) out
Proof
  Cases_on ‘bindings’ \\
  rw[] \\
  metis_tac[
    eval_m1_rec_let_star_branch_sound,
    eval_m1_rec_let_star_bad_bindings_branch_sound]
QED

Theorem eval_m1_rec_proven_branch_sound:
  ∀fuel space atom out.
    eval_m1_rec_proven_branch_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_branch_sound fuel space atom out
Proof
  rw[eval_m1_rec_proven_branch_atom_def] >-
    metis_tac[eval_m1_rec_add_branch_sound] >-
    metis_tac[eval_m1_rec_mul_branch_sound] >-
    metis_tac[eval_m1_rec_sub_branch_sound] >-
    metis_tac[eval_m1_rec_lt_branch_sound] >-
    metis_tac[eval_m1_rec_eq_branch_sound] >-
    metis_tac[eval_m1_rec_and_branch_sound] >-
    metis_tac[eval_m1_rec_or_branch_sound] >-
    metis_tac[eval_m1_rec_not_branch_sound] >-
    metis_tac[eval_m1_rec_function_branch_sound] >-
    metis_tac[eval_m1_rec_return_branch_sound] >-
    metis_tac[eval_m1_rec_eval_branch_sound] >-
    metis_tac[eval_m1_rec_chain_any_branch_sound] >-
    metis_tac[eval_m1_rec_evalc_branch_sound] >-
    metis_tac[eval_m1_rec_vec_cons_branch_sound] >-
    metis_tac[eval_m1_rec_case_any_branch_sound] >-
    metis_tac[eval_m1_rec_switch_any_branch_sound] >-
    metis_tac[eval_m1_rec_let_star_any_branch_sound]
QED

Theorem eval_m1_rec_fallback_ext_eq:
  ∀fuel space atom.
    ¬eval_m1_rec_proven_branch_atom atom ⇒
    eval_m1_rec (SUC fuel) space atom = eval_m1_ext (SUC fuel) space atom
Proof
  Cases_on ‘atom’ \\
  rw[eval_m1_rec_def] \\
  Cases_on ‘l’ \\
  gvs[eval_m1_rec_def, eval_m1_rec_proven_branch_atom_def] \\
  Cases_on ‘t’ \\
  gvs[eval_m1_rec_def, eval_m1_rec_proven_branch_atom_def] \\
  Cases_on ‘t'’ \\
  gvs[eval_m1_rec_def, eval_m1_rec_proven_branch_atom_def] \\
  Cases_on ‘h’ \\
  gvs[eval_m1_rec_def, eval_m1_rec_proven_branch_atom_def] \\
  TRY (Cases_on ‘t’) \\
  gvs[eval_m1_rec_def, eval_m1_rec_proven_branch_atom_def] \\
  TRY (Cases_on ‘t'’) \\
  gvs[eval_m1_rec_def, eval_m1_rec_proven_branch_atom_def] \\
  TRY (Cases_on ‘n = 21’) \\
  rw[]
QED

Theorem eval_m1_rec_fallback_ext_member:
  ∀fuel space atom out.
    ¬eval_m1_rec_proven_branch_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    MEM out (eval_m1_ext (SUC fuel) space atom)
Proof
  metis_tac[eval_m1_rec_fallback_ext_eq]
QED

Definition eval_m1_rec_result_sound_def:
  eval_m1_rec_result_sound fuel space atom out ⇔
    (fuel = 0 ∧ out = error_atom atom (Sym 3)) ∨
    (∃fuel0.
       fuel = SUC fuel0 ∧
       ((eval_m1_rec_proven_branch_atom atom ∧
         eval_m1_rec_branch_sound fuel0 space atom out) ∨
        (¬eval_m1_rec_proven_branch_atom atom ∧
         (out = atom ∨ out = error_atom atom (Sym 3) ∨
          equality_step space atom out ∨ builtin_step atom out ∨
          ∃pattern templ.
            atom = Expr [Sym 4; Sym 5; pattern; templ] ∧
            MEM out (match_space space pattern templ)))))
End

Theorem eval_m1_rec_result_sound:
  ∀fuel space atom out.
    MEM out (eval_m1_rec fuel space atom) ⇒
    eval_m1_rec_result_sound fuel space atom out
Proof
  Cases \\
  rw[eval_m1_rec_result_sound_def] >-
    metis_tac[eval_m1_rec_timeout_sound] \\
  Cases_on ‘eval_m1_rec_proven_branch_atom atom’ >-
    metis_tac[eval_m1_rec_proven_branch_sound] \\
  ‘MEM out (eval_m1_ext (SUC n) space atom)’ by
    metis_tac[eval_m1_rec_fallback_ext_member] \\
  drule eval_m1_ext_sound \\
  rw[] \\
  metis_tac[]
QED

Definition eval_m1_rec_arith_compare_atom_def:
  eval_m1_rec_arith_compare_atom atom ⇔
    (∃a b. atom = Expr [Sym 11; a; b]) ∨
    (∃a b. atom = Expr [Sym 45; a; b]) ∨
    (∃a b. atom = Expr [Sym 46; a; b]) ∨
    (∃a b. atom = Expr [Sym 12; a; b]) ∨
    (∃a b. atom = Expr [Sym 47; a; b])
End

Definition eval_m1_rec_arith_compare_sound_def:
  eval_m1_rec_arith_compare_sound fuel space atom out ⇔
    (∃a b.
       atom = Expr [Sym 11; a; b] ∧
       ((∃x y.
          MEM (IntLit x) (eval_m1_rec fuel space a) ∧
          MEM (IntLit y) (eval_m1_rec fuel space b) ∧
          out = IntLit (int_add x y)) ∨
        out = error_atom atom (Sym 10))) ∨
    (∃a b.
       atom = Expr [Sym 45; a; b] ∧
       ((∃x y.
          MEM (IntLit x) (eval_m1_rec fuel space a) ∧
          MEM (IntLit y) (eval_m1_rec fuel space b) ∧
          out = IntLit (int_mul x y)) ∨
        out = error_atom atom (Sym 10))) ∨
    (∃a b.
       atom = Expr [Sym 46; a; b] ∧
       ((∃x y.
          MEM (IntLit x) (eval_m1_rec fuel space a) ∧
          MEM (IntLit y) (eval_m1_rec fuel space b) ∧
          out = IntLit (x - y)) ∨
        out = error_atom atom (Sym 10))) ∨
    (∃a b.
       atom = Expr [Sym 12; a; b] ∧
       ((∃x y.
          MEM (IntLit x) (eval_m1_rec fuel space a) ∧
          MEM (IntLit y) (eval_m1_rec fuel space b) ∧
          out = (if int_lt x y then Sym 8 else Sym 9)) ∨
        out = error_atom atom (Sym 10))) ∨
    (∃a b x y.
       atom = Expr [Sym 47; a; b] ∧
       MEM x (eval_m1_rec fuel space a) ∧
       MEM y (eval_m1_rec fuel space b) ∧
       out = (if x = y then Sym 8 else Sym 9))
End

Definition eval_m1_rec_boolean_atom_def:
  eval_m1_rec_boolean_atom atom ⇔
    (∃a b. atom = Expr [Sym 31; a; b]) ∨
    (∃a b. atom = Expr [Sym 32; a; b]) ∨
    (∃a. atom = Expr [Sym 33; a])
End

Definition eval_m1_rec_boolean_sound_def:
  eval_m1_rec_boolean_sound fuel space atom out ⇔
    (∃a b x y.
       atom = Expr [Sym 31; a; b] ∧
       MEM x (eval_m1_rec fuel space a) ∧
       MEM y (eval_m1_rec fuel space b) ∧
       out = bool_and_result atom x y) ∨
    (∃a b x y.
       atom = Expr [Sym 32; a; b] ∧
       MEM x (eval_m1_rec fuel space a) ∧
       MEM y (eval_m1_rec fuel space b) ∧
       out = bool_or_result atom x y) ∨
    (∃a x.
       atom = Expr [Sym 33; a] ∧
       MEM x (eval_m1_rec fuel space a) ∧
       out = bool_not_result atom x)
End

Definition eval_m1_rec_control_atom_def:
  eval_m1_rec_control_atom atom ⇔
    (∃body. atom = Expr [Sym 18; body]) ∨
    (∃value. atom = Expr [Sym 19; value]) ∨
    (∃body. atom = Expr [Sym 20; body]) ∨
    (∃nested selector templ.
       atom = Expr [Sym 21; nested; selector; templ])
End

Definition eval_m1_rec_control_sound_def:
  eval_m1_rec_control_sound fuel space atom out ⇔
    (∃body.
       atom = Expr [Sym 18; body] ∧
       ((∃inner value.
          MEM inner (eval_m1_rec fuel space body) ∧
          return_payload_of inner = SOME value ∧ out = value) ∨
        out = error_atom atom (Sym 22))) ∨
    (∃value.
       atom = Expr [Sym 19; value] ∧ out = atom) ∨
    (∃body.
       atom = Expr [Sym 20; body] ∧
       ((eval_m1_rec fuel space body = [body] ∧ out = Sym 23) ∨
        (eval_m1_rec fuel space body ≠ [body] ∧
         MEM out (eval_m1_rec fuel space body)))) ∨
    (∃nested v templ x.
       atom = Expr [Sym 21; nested; Var v; templ] ∧
       MEM x (eval_m1_rec fuel space nested) ∧
       MEM out (eval_m1_rec fuel space (apply_subst [Bind v x] templ))) ∨
    (∃nested bad_var templ.
       atom = Expr [Sym 21; nested; bad_var; templ] ∧
       (∀v. bad_var ≠ Var v) ∧
       out = error_atom atom (Sym 10))
End

Definition eval_m1_rec_structural_atom_def:
  eval_m1_rec_structural_atom atom ⇔
    (∃term expected. atom = Expr [Sym 57; term; expected]) ∨
    (∃elem tail. atom = Expr [Sym 58; elem; tail]) ∨
    (∃scrut branches. atom = Expr [Sym 54; scrut; branches]) ∨
    (∃scrut branches. atom = Expr [Sym 55; scrut; branches]) ∨
    (∃bindings body. atom = Expr [Sym 56; bindings; body])
End

Definition eval_m1_rec_structural_sound_def:
  eval_m1_rec_structural_sound fuel space atom out ⇔
    (∃term expected value.
       atom = Expr [Sym 57; term; expected] ∧
       MEM value
         (if hol_typed_add_bad space term
          then [error_atom term (Sym 10)]
          else eval_m1_rec fuel space term) ∧
       ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
        (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
         out = error_atom term (Sym 10)))) ∨
    (∃elem tail.
       atom = Expr [Sym 58; elem; tail] ∧
       out = dependent_vec_cons_type space elem tail) ∨
    (∃scrut branches value branch pattern body bs.
       atom = Expr [Sym 54; scrut; Expr branches] ∧
       MEM value (eval_m1_rec fuel space scrut) ∧
       MEM branch branches ∧
       branch_pair branch = SOME (pattern, body) ∧
       match_atom pattern value [] = SOME bs ∧
       MEM out (eval_m1_rec fuel space (apply_subst bs body))) ∨
    (∃scrut bad_branches.
       atom = Expr [Sym 54; scrut; bad_branches] ∧
       (∀branches. bad_branches ≠ Expr branches) ∧
       out = error_atom atom (Sym 10)) ∨
    (∃scrut branches value branch pattern body bs.
       atom = Expr [Sym 55; scrut; Expr branches] ∧
       MEM value (eval_m1_rec fuel space scrut) ∧
       MEM branch branches ∧
       branch_pair branch = SOME (pattern, body) ∧
       match_atom pattern value [] = SOME bs ∧
       MEM out (eval_m1_rec fuel space (apply_subst bs body))) ∨
    (∃scrut bad_branches.
       atom = Expr [Sym 55; scrut; bad_branches] ∧
       (∀branches. bad_branches ≠ Expr branches) ∧
       out = error_atom atom (Sym 10)) ∨
    (∃bindings body.
       atom = Expr [Sym 56; Expr bindings; body] ∧
       let_star_provenance (SUC (LENGTH bindings))
         (λa. eval_m1_rec fuel space a) bindings body atom out) ∨
    (∃bad_bindings body.
       atom = Expr [Sym 56; bad_bindings; body] ∧
       (∀bindings. bad_bindings ≠ Expr bindings) ∧
       out = error_atom atom (Sym 10))
End

Theorem eval_m1_rec_control_from_branch_sound:
  ∀fuel space atom out.
    eval_m1_rec_control_atom atom ∧
    eval_m1_rec_branch_sound fuel space atom out ⇒
    eval_m1_rec_control_sound fuel space atom out
Proof
  rw[eval_m1_rec_control_atom_def,
     eval_m1_rec_branch_sound_def,
     eval_m1_rec_control_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_structural_from_branch_sound:
  ∀fuel space atom out.
    eval_m1_rec_structural_atom atom ∧
    eval_m1_rec_branch_sound fuel space atom out ⇒
    eval_m1_rec_structural_sound fuel space atom out
Proof
  rw[eval_m1_rec_structural_atom_def,
     eval_m1_rec_branch_sound_def,
     eval_m1_rec_structural_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_arith_compare_input_sound:
  ∀fuel space atom out.
    eval_m1_rec_arith_compare_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_arith_compare_sound fuel space atom out
Proof
  rw[eval_m1_rec_arith_compare_atom_def] >-
    (drule eval_m1_rec_add_member_input_sound \\
     rw[eval_m1_rec_arith_compare_sound_def] \\
     metis_tac[]) >-
    (drule eval_m1_rec_mul_member_input_sound \\
     rw[eval_m1_rec_arith_compare_sound_def] \\
     metis_tac[]) >-
    (drule eval_m1_rec_sub_member_input_sound \\
     rw[eval_m1_rec_arith_compare_sound_def] \\
     metis_tac[]) >-
    (drule eval_m1_rec_lt_member_input_sound \\
     rw[eval_m1_rec_arith_compare_sound_def] \\
     metis_tac[]) >-
    (drule eval_m1_rec_eq_member_input_sound \\
     rw[eval_m1_rec_arith_compare_sound_def] \\
     metis_tac[])
QED

Theorem eval_m1_rec_boolean_input_sound:
  ∀fuel space atom out.
    eval_m1_rec_boolean_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_boolean_sound fuel space atom out
Proof
  rw[eval_m1_rec_boolean_atom_def] >-
    (drule eval_m1_rec_and_member_input_sound \\
     rw[eval_m1_rec_boolean_sound_def] \\
     metis_tac[]) >-
    (drule eval_m1_rec_or_member_input_sound \\
     rw[eval_m1_rec_boolean_sound_def] \\
     metis_tac[]) >-
    (drule eval_m1_rec_not_member_input_sound \\
     rw[eval_m1_rec_boolean_sound_def] \\
     metis_tac[])
QED

Theorem eval_m1_rec_control_input_sound:
  ∀fuel space atom out.
    eval_m1_rec_control_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_control_sound fuel space atom out
Proof
  rw[] \\
  irule eval_m1_rec_control_from_branch_sound \\
  rw[] \\
  irule eval_m1_rec_proven_branch_sound \\
  fs[eval_m1_rec_control_atom_def,
     eval_m1_rec_proven_branch_atom_def]
QED

Theorem eval_m1_rec_structural_input_sound:
  ∀fuel space atom out.
    eval_m1_rec_structural_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_structural_sound fuel space atom out
Proof
  rw[] \\
  irule eval_m1_rec_structural_from_branch_sound \\
  rw[] \\
  irule eval_m1_rec_proven_branch_sound \\
  fs[eval_m1_rec_structural_atom_def,
     eval_m1_rec_proven_branch_atom_def]
QED

Theorem eval_m1_rec_chain_family_input_sound:
  ∀fuel space nested v templ out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 21; nested; Var v; templ])) ⇒
    eval_m1_rec_control_sound fuel space
      (Expr [Sym 21; nested; Var v; templ]) out ∧
    ∃x.
      MEM x (eval_m1_rec fuel space nested) ∧
      MEM out (eval_m1_rec fuel space (apply_subst [Bind v x] templ))
Proof
  rw[] \\
  drule eval_m1_rec_chain_branch_member_sound \\
  rw[eval_m1_rec_control_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_evalc_family_input_sound:
  ∀fuel space term expected out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 57; term; expected])) ⇒
    eval_m1_rec_structural_sound fuel space
      (Expr [Sym 57; term; expected]) out ∧
    ∃value.
      MEM value
        (if hol_typed_add_bad space term
         then [error_atom term (Sym 10)]
         else eval_m1_rec fuel space term) ∧
      ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
       (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
        out = error_atom term (Sym 10)))
Proof
  rw[] \\
  drule eval_m1_rec_evalc_member_sound \\
  rw[eval_m1_rec_structural_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_case_family_input_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 54; scrut; Expr branches])) ⇒
    eval_m1_rec_structural_sound fuel space
      (Expr [Sym 54; scrut; Expr branches]) out ∧
    ∃value branch pattern body bs.
      MEM value (eval_m1_rec fuel space scrut) ∧
      MEM branch branches ∧
      branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (eval_m1_rec fuel space (apply_subst bs body))
Proof
  rw[] \\
  drule eval_m1_rec_case_branch_semantic_sound \\
  rw[eval_m1_rec_structural_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_switch_family_input_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 55; scrut; Expr branches])) ⇒
    eval_m1_rec_structural_sound fuel space
      (Expr [Sym 55; scrut; Expr branches]) out ∧
    ∃value branch pattern body bs.
      MEM value (eval_m1_rec fuel space scrut) ∧
      MEM branch branches ∧
      branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (eval_m1_rec fuel space (apply_subst bs body))
Proof
  rw[] \\
  drule eval_m1_rec_switch_branch_semantic_sound \\
  rw[eval_m1_rec_structural_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_let_star_family_input_sound:
  ∀fuel space bindings body out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 56; Expr bindings; body])) ⇒
    eval_m1_rec_structural_sound fuel space
      (Expr [Sym 56; Expr bindings; body]) out ∧
    let_star_provenance (SUC (LENGTH bindings))
      (λa. eval_m1_rec fuel space a) bindings body
      (Expr [Sym 56; Expr bindings; body]) out
Proof
  rw[] \\
  drule eval_m1_rec_let_star_member_sound \\
  rw[eval_m1_rec_structural_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_arith_compare_refines_branch_sound:
  ∀fuel space atom out.
    eval_m1_rec_arith_compare_sound fuel space atom out ⇒
    eval_m1_rec_branch_sound fuel space atom out
Proof
  rw[eval_m1_rec_arith_compare_sound_def,
     eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_boolean_refines_branch_sound:
  ∀fuel space atom out.
    eval_m1_rec_boolean_sound fuel space atom out ⇒
    eval_m1_rec_branch_sound fuel space atom out
Proof
  rw[eval_m1_rec_boolean_sound_def,
     eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_control_refines_branch_sound:
  ∀fuel space atom out.
    eval_m1_rec_control_sound fuel space atom out ⇒
    eval_m1_rec_branch_sound fuel space atom out
Proof
  rw[eval_m1_rec_control_sound_def,
     eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_structural_refines_branch_sound:
  ∀fuel space atom out.
    eval_m1_rec_structural_sound fuel space atom out ⇒
    eval_m1_rec_branch_sound fuel space atom out
Proof
  rw[eval_m1_rec_structural_sound_def,
     eval_m1_rec_branch_sound_def] \\
  metis_tac[]
QED

Definition eval_m1_rec_family_atom_def:
  eval_m1_rec_family_atom atom ⇔
    eval_m1_rec_arith_compare_atom atom ∨
    eval_m1_rec_boolean_atom atom ∨
    eval_m1_rec_control_atom atom ∨
    eval_m1_rec_structural_atom atom
End

Definition eval_m1_rec_family_sound_def:
  eval_m1_rec_family_sound fuel space atom out ⇔
    (fuel = 0 ∧ out = error_atom atom (Sym 3)) ∨
    (∃fuel0.
       fuel = SUC fuel0 ∧
       ((eval_m1_rec_arith_compare_atom atom ∧
         eval_m1_rec_arith_compare_sound fuel0 space atom out) ∨
        (eval_m1_rec_boolean_atom atom ∧
         eval_m1_rec_boolean_sound fuel0 space atom out) ∨
        (eval_m1_rec_control_atom atom ∧
         eval_m1_rec_control_sound fuel0 space atom out) ∨
        (eval_m1_rec_structural_atom atom ∧
         eval_m1_rec_structural_sound fuel0 space atom out) ∨
        (¬eval_m1_rec_family_atom atom ∧
         (out = atom ∨ out = error_atom atom (Sym 3) ∨
          equality_step space atom out ∨ builtin_step atom out ∨
          ∃pattern templ.
            atom = Expr [Sym 4; Sym 5; pattern; templ] ∧
            MEM out (match_space space pattern templ)))))
End

Theorem eval_m1_rec_family_atom_iff_proven_branch:
  ∀atom.
    eval_m1_rec_family_atom atom ⇔ eval_m1_rec_proven_branch_atom atom
Proof
  rw[eval_m1_rec_family_atom_def,
     eval_m1_rec_arith_compare_atom_def,
     eval_m1_rec_boolean_atom_def,
     eval_m1_rec_control_atom_def,
     eval_m1_rec_structural_atom_def,
     eval_m1_rec_proven_branch_atom_def] \\
  metis_tac[]
QED

Theorem eval_m1_rec_family_result_sound:
  ∀fuel space atom out.
    MEM out (eval_m1_rec fuel space atom) ⇒
    eval_m1_rec_family_sound fuel space atom out
Proof
  Cases \\
  rw[eval_m1_rec_family_sound_def] >-
    metis_tac[eval_m1_rec_timeout_sound] \\
  Cases_on ‘eval_m1_rec_arith_compare_atom atom’ >-
    metis_tac[eval_m1_rec_arith_compare_input_sound] \\
  Cases_on ‘eval_m1_rec_boolean_atom atom’ >-
    metis_tac[eval_m1_rec_boolean_input_sound] \\
  Cases_on ‘eval_m1_rec_control_atom atom’ >-
    metis_tac[eval_m1_rec_control_input_sound] \\
  Cases_on ‘eval_m1_rec_structural_atom atom’ >-
    metis_tac[eval_m1_rec_structural_input_sound] \\
  ‘¬eval_m1_rec_proven_branch_atom atom’ by
    metis_tac[eval_m1_rec_family_atom_iff_proven_branch,
              eval_m1_rec_family_atom_def] \\
  ‘MEM out (eval_m1_ext (SUC n) space atom)’ by
    metis_tac[eval_m1_rec_fallback_ext_member] \\
  drule eval_m1_ext_sound \\
  rw[] \\
  metis_tac[eval_m1_rec_family_atom_def]
QED

Definition let_star_family_provenance_def:
  let_star_family_provenance rec_fuel space 0 bindings body original out =
    (out = error_atom original (Sym 3)) ∧
  let_star_family_provenance rec_fuel space (SUC let_fuel) [] body original out =
    (MEM out (eval_m1_rec rec_fuel space body) ∧
     eval_m1_rec_family_sound rec_fuel space body out) ∧
  let_star_family_provenance rec_fuel space (SUC let_fuel) (binding :: rest)
    body original out =
    (case let_binding_pair binding of
     | SOME (v, value) =>
         ∃evaluated.
           MEM evaluated (eval_m1_rec rec_fuel space value) ∧
           eval_m1_rec_family_sound rec_fuel space value evaluated ∧
           let_star_family_provenance rec_fuel space let_fuel
             (subst_binding_pairs v evaluated rest)
             (apply_subst [Bind v evaluated] body) original out
     | NONE => out = error_atom original (Sym 10))
Termination
  WF_REL_TAC
    ‘measure (λ(rec_fuel,space,let_fuel,bindings,body,original,out). let_fuel)’ \\
  rw[]
End

Theorem let_star_provenance_family_sound:
  ∀let_fuel rec_fuel space bindings body original out.
    let_star_provenance let_fuel
      (λa. eval_m1_rec rec_fuel space a) bindings body original out ⇒
    let_star_family_provenance rec_fuel space let_fuel
      bindings body original out
Proof
  Induct \\
  rw[let_star_provenance_def, let_star_family_provenance_def] \\
  Cases_on ‘bindings’ \\
  gvs[let_star_provenance_def, let_star_family_provenance_def] >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  Cases_on ‘let_binding_pair h’ \\
  gvs[let_star_provenance_def, let_star_family_provenance_def] \\
  PairCases_on ‘x’ \\
  gvs[] \\
  metis_tac[eval_m1_rec_family_result_sound]
QED

Theorem eval_m1_rec_chain_nested_family_sound:
  ∀fuel space nested v templ out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 21; nested; Var v; templ])) ⇒
    eval_m1_rec_control_sound fuel space
      (Expr [Sym 21; nested; Var v; templ]) out ∧
    ∃x.
      MEM x (eval_m1_rec fuel space nested) ∧
      eval_m1_rec_family_sound fuel space nested x ∧
      MEM out (eval_m1_rec fuel space (apply_subst [Bind v x] templ)) ∧
      eval_m1_rec_family_sound fuel space (apply_subst [Bind v x] templ) out
Proof
  rw[] \\
  drule eval_m1_rec_chain_family_input_sound \\
  rw[] \\
  metis_tac[eval_m1_rec_family_result_sound]
QED

Theorem eval_m1_rec_evalc_nested_family_sound:
  ∀fuel space term expected out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 57; term; expected])) ⇒
    eval_m1_rec_structural_sound fuel space
      (Expr [Sym 57; term; expected]) out ∧
    ∃value.
      MEM value
        (if hol_typed_add_bad space term
         then [error_atom term (Sym 10)]
         else eval_m1_rec fuel space term) ∧
      (¬hol_typed_add_bad space term ⇒
       eval_m1_rec_family_sound fuel space term value) ∧
      ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
       (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
        out = error_atom term (Sym 10)))
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_evalc_family_input_sound] \\
  metis_tac[
    eval_m1_rec_evalc_family_input_sound,
    eval_m1_rec_family_result_sound]
QED

Theorem eval_m1_rec_case_nested_family_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 54; scrut; Expr branches])) ⇒
    eval_m1_rec_structural_sound fuel space
      (Expr [Sym 54; scrut; Expr branches]) out ∧
    ∃value branch pattern body bs.
      MEM value (eval_m1_rec fuel space scrut) ∧
      eval_m1_rec_family_sound fuel space scrut value ∧
      MEM branch branches ∧
      branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (eval_m1_rec fuel space (apply_subst bs body)) ∧
      eval_m1_rec_family_sound fuel space (apply_subst bs body) out
Proof
  rw[] \\
  drule eval_m1_rec_case_family_input_sound \\
  rw[] \\
  metis_tac[eval_m1_rec_family_result_sound]
QED

Theorem eval_m1_rec_switch_nested_family_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space (Expr [Sym 55; scrut; Expr branches])) ⇒
    eval_m1_rec_structural_sound fuel space
      (Expr [Sym 55; scrut; Expr branches]) out ∧
    ∃value branch pattern body bs.
      MEM value (eval_m1_rec fuel space scrut) ∧
      eval_m1_rec_family_sound fuel space scrut value ∧
      MEM branch branches ∧
      branch_pair branch = SOME (pattern, body) ∧
      match_atom pattern value [] = SOME bs ∧
      MEM out (eval_m1_rec fuel space (apply_subst bs body)) ∧
      eval_m1_rec_family_sound fuel space (apply_subst bs body) out
Proof
  rw[] \\
  drule eval_m1_rec_switch_family_input_sound \\
  rw[] \\
  metis_tac[eval_m1_rec_family_result_sound]
QED

Theorem eval_m1_rec_let_star_nested_family_sound:
  ∀fuel space bindings body out.
    MEM out
      (eval_m1_rec (SUC fuel) space
         (Expr [Sym 56; Expr bindings; body])) ⇒
    eval_m1_rec_structural_sound fuel space
      (Expr [Sym 56; Expr bindings; body]) out ∧
    let_star_family_provenance fuel space (SUC (LENGTH bindings))
      bindings body (Expr [Sym 56; Expr bindings; body]) out
Proof
  rw[] \\
  drule eval_m1_rec_let_star_family_input_sound \\
  rw[] \\
  drule let_star_provenance_family_sound \\
  rw[]
QED

Definition eval_m1_rec_nested_family_atom_def:
  eval_m1_rec_nested_family_atom atom ⇔
    (∃nested v templ.
       atom = Expr [Sym 21; nested; Var v; templ]) ∨
    (∃term expected.
       atom = Expr [Sym 57; term; expected]) ∨
    (∃scrut branches.
       atom = Expr [Sym 54; scrut; Expr branches]) ∨
    (∃scrut branches.
       atom = Expr [Sym 55; scrut; Expr branches]) ∨
    (∃bindings body.
       atom = Expr [Sym 56; Expr bindings; body])
End

Definition eval_m1_rec_nested_family_sound_def:
  eval_m1_rec_nested_family_sound fuel space atom out ⇔
    (∃nested v templ x.
       atom = Expr [Sym 21; nested; Var v; templ] ∧
       eval_m1_rec_control_sound fuel space atom out ∧
       MEM x (eval_m1_rec fuel space nested) ∧
       eval_m1_rec_family_sound fuel space nested x ∧
       MEM out (eval_m1_rec fuel space (apply_subst [Bind v x] templ)) ∧
       eval_m1_rec_family_sound fuel space
         (apply_subst [Bind v x] templ) out) ∨
    (∃term expected value.
       atom = Expr [Sym 57; term; expected] ∧
       eval_m1_rec_structural_sound fuel space atom out ∧
       MEM value
         (if hol_typed_add_bad space term
          then [error_atom term (Sym 10)]
          else eval_m1_rec fuel space term) ∧
       (¬hol_typed_add_bad space term ⇒
        eval_m1_rec_family_sound fuel space term value) ∧
       ((hol_any_type_match expected
           (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
        (¬hol_any_type_match expected
           (hol_declared_or_default_type_lookup space value) ∧
         out = error_atom term (Sym 10)))) ∨
    (∃scrut branches value branch pattern body bs.
       atom = Expr [Sym 54; scrut; Expr branches] ∧
       eval_m1_rec_structural_sound fuel space atom out ∧
       MEM value (eval_m1_rec fuel space scrut) ∧
       eval_m1_rec_family_sound fuel space scrut value ∧
       MEM branch branches ∧
       branch_pair branch = SOME (pattern, body) ∧
       match_atom pattern value [] = SOME bs ∧
       MEM out (eval_m1_rec fuel space (apply_subst bs body)) ∧
       eval_m1_rec_family_sound fuel space (apply_subst bs body) out) ∨
    (∃scrut branches value branch pattern body bs.
       atom = Expr [Sym 55; scrut; Expr branches] ∧
       eval_m1_rec_structural_sound fuel space atom out ∧
       MEM value (eval_m1_rec fuel space scrut) ∧
       eval_m1_rec_family_sound fuel space scrut value ∧
       MEM branch branches ∧
       branch_pair branch = SOME (pattern, body) ∧
       match_atom pattern value [] = SOME bs ∧
       MEM out (eval_m1_rec fuel space (apply_subst bs body)) ∧
       eval_m1_rec_family_sound fuel space (apply_subst bs body) out) ∨
    (∃bindings body.
       atom = Expr [Sym 56; Expr bindings; body] ∧
       eval_m1_rec_structural_sound fuel space atom out ∧
       let_star_family_provenance fuel space (SUC (LENGTH bindings))
         bindings body atom out)
End

Theorem eval_m1_rec_nested_family_result_sound:
  ∀fuel space atom out.
    eval_m1_rec_nested_family_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_nested_family_sound fuel space atom out
Proof
  rw[eval_m1_rec_nested_family_atom_def,
     eval_m1_rec_nested_family_sound_def] >-
    metis_tac[eval_m1_rec_chain_nested_family_sound] >-
    metis_tac[eval_m1_rec_evalc_nested_family_sound] >-
    metis_tac[eval_m1_rec_case_nested_family_sound] >-
    metis_tac[eval_m1_rec_switch_nested_family_sound] >-
    metis_tac[eval_m1_rec_let_star_nested_family_sound]
QED

Theorem eval_m1_rec_nested_family_to_recursive_result_sound:
  ∀fuel space atom out.
    eval_m1_rec_nested_family_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_nested_family_sound fuel space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out
Proof
  rw[] \\
  metis_tac[
    eval_m1_rec_nested_family_result_sound,
    eval_m1_rec_family_result_sound]
QED

Theorem eval_m1_rec_fuller_result_sound:
  ∀fuel space atom out.
    MEM out (eval_m1_rec fuel space atom) ⇒
    eval_m1_rec_result_sound fuel space atom out ∧
    (∀fuel0.
       fuel = SUC fuel0 ∧ eval_m1_rec_nested_family_atom atom ⇒
       eval_m1_rec_nested_family_sound fuel0 space atom out)
Proof
  Cases \\
  rw[] >-
    metis_tac[eval_m1_rec_result_sound] >-
    metis_tac[eval_m1_rec_result_sound] \\
  metis_tac[eval_m1_rec_nested_family_result_sound]
QED

Theorem eval_m1_rec_add_evaluates_args_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; IntLit 2];
       Expr [Sym 2; Expr [Sym 25]; IntLit 3]]
      (Expr [Sym 11; Expr [Sym 24]; Expr [Sym 25]]) =
    [IntLit 5]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_add_cross_product_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; IntLit 1];
       Expr [Sym 2; Expr [Sym 24]; IntLit 2];
       Expr [Sym 2; Expr [Sym 25]; IntLit 10];
       Expr [Sym 2; Expr [Sym 25]; IntLit 20]]
      (Expr [Sym 11; Expr [Sym 24]; Expr [Sym 25]]) =
    [IntLit 11; IntLit 21; IntLit 12; IntLit 22]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_mul_evaluates_args_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; IntLit 4];
       Expr [Sym 2; Expr [Sym 25]; IntLit 5]]
      (Expr [Sym 45; Expr [Sym 24]; Expr [Sym 25]]) =
    [IntLit 20]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_sub_evaluates_args_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; IntLit 9];
       Expr [Sym 2; Expr [Sym 25]; IntLit 4]]
      (Expr [Sym 46; Expr [Sym 24]; Expr [Sym 25]]) =
    [IntLit 5]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_lt_evaluates_args_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; IntLit 2];
       Expr [Sym 2; Expr [Sym 25]; IntLit 3]]
      (Expr [Sym 12; Expr [Sym 24]; Expr [Sym 25]]) =
    [Sym 8]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_eq_evaluates_args_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; Sym 25];
       Expr [Sym 2; Expr [Sym 26]; Sym 25]]
      (Expr [Sym 47; Expr [Sym 24]; Expr [Sym 26]]) =
    [Sym 8]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_and_evaluates_args_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; Sym 8];
       Expr [Sym 2; Expr [Sym 25]; Sym 9]]
      (Expr [Sym 31; Expr [Sym 24]; Expr [Sym 25]]) =
    [Sym 9]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_or_evaluates_args_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; Sym 9];
       Expr [Sym 2; Expr [Sym 25]; Sym 8]]
      (Expr [Sym 32; Expr [Sym 24]; Expr [Sym 25]]) =
    [Sym 8]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_not_evaluates_arg_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 2; Expr [Sym 24]; Sym 8]]
      (Expr [Sym 33; Expr [Sym 24]]) =
    [Sym 9]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_add_bad_evaluated_arg_example:
  ∀fuel n.
    eval_m1_rec (SUC (SUC fuel)) []
      (Expr [Sym 11; Sym n; IntLit 0]) =
    [error_atom (Expr [Sym 11; Sym n; IntLit 0]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem hol_type_lookup_declared_nat_example:
  hol_type_lookup
    [Expr [Sym 34; Sym 24; Sym 36]]
    (Sym 24) = [Sym 36; Sym 39]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem hol_typed_add_bad_rejects_function_as_nat_example:
  hol_typed_add_bad
    [Expr [Sym 34; Sym 24; Sym 36];
     Expr [Sym 34; Sym 25; Expr [Sym 37; Sym 36; Sym 36]];
     Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]]]
    (Expr [Sym 38; Sym 25; Sym 24])
Proof
  EVAL_TAC \\ rw[]
QED

Theorem typed_eval_m1_rec_add_good_example:
  ∀fuel.
    typed_eval_m1_rec (SUC fuel)
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 38; Sym 24; Sym 24]) =
    [Sym 24]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem typed_eval_m1_rec_add_bad_arg_example:
  ∀fuel.
    typed_eval_m1_rec (SUC fuel)
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 25; Expr [Sym 37; Sym 36; Sym 36]];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 38; Sym 25; Sym 24]) =
    [error_atom (Expr [Sym 38; Sym 25; Sym 24]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem evalc_like_good_example:
  ∀fuel.
    evalc_like (SUC fuel)
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 38; Sym 24; Sym 24]) (Sym 36) =
    [Sym 24]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem evalc_like_bad_result_type_example:
  ∀fuel.
    evalc_like (SUC fuel)
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 38; Sym 24; Sym 24]) (Sym 42) =
    [error_atom (Expr [Sym 38; Sym 24; Sym 24]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_evalc_good_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 57; Expr [Sym 38; Sym 24; Sym 24]; Sym 36]) =
    [Sym 24]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_evalc_bad_result_type_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel))
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 57; Expr [Sym 38; Sym 24; Sym 24]; Sym 42]) =
    [error_atom (Expr [Sym 38; Sym 24; Sym 24]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem dependent_vec_cons_type_good_example:
  dependent_vec_cons_type
    [Expr [Sym 34; Sym 24; Sym 50];
     Expr [Sym 34; Sym 52; Expr [Sym 49; Sym 50; Sym 53]]]
    (Sym 24) (Sym 52) =
  Expr [Sym 49; Sym 50; Expr [Sym 51; Sym 53]]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem dependent_vec_cons_type_bad_elem_example:
  dependent_vec_cons_type
    [Expr [Sym 34; Sym 24; Sym 42];
     Expr [Sym 34; Sym 52; Expr [Sym 49; Sym 50; Sym 53]]]
    (Sym 24) (Sym 52) =
  Sym 10
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_vec_cons_type_good_example:
  ∀fuel.
    eval_m1_rec (SUC fuel)
      [Expr [Sym 34; Sym 24; Sym 50];
       Expr [Sym 34; Sym 52; Expr [Sym 49; Sym 50; Sym 53]]]
      (Expr [Sym 58; Sym 24; Sym 52]) =
    [Expr [Sym 49; Sym 50; Expr [Sym 51; Sym 53]]]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_case_like_first_match_example:
  ∀fuel.
    eval_case_like (SUC fuel) [] (Sym 24)
      [Expr [Sym 24; Sym 25]; Expr [Var 0; Var 0]]
      (Expr [Sym 54; Sym 24]) =
    [Sym 25]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_case_first_match_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel)) []
      (Expr [Sym 54; Sym 24;
             Expr [Expr [Sym 24; Sym 25]; Expr [Var 0; Var 0]]]) =
    [Sym 25]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_case_like_variable_match_example:
  ∀fuel.
    eval_case_like (SUC fuel) [] (Sym 24)
      [Expr [Sym 25; Sym 26]; Expr [Var 0; Var 0]]
      (Expr [Sym 54; Sym 24]) =
    [Sym 24]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_case_variable_match_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel)) []
      (Expr [Sym 54; Sym 24;
             Expr [Expr [Sym 25; Sym 26]; Expr [Var 0; Var 0]]]) =
    [Sym 24]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_switch_like_structural_match_example:
  ∀fuel.
    eval_switch_like (SUC fuel) [] (Sym 24)
      [Expr [Sym 25; Sym 26]; Expr [Sym 24; Sym 27]]
      (Expr [Sym 55; Sym 24]) =
    [Sym 27]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_switch_structural_match_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC fuel)) []
      (Expr [Sym 55; Sym 24;
             Expr [Expr [Sym 25; Sym 26]; Expr [Sym 24; Sym 27]]]) =
    [Sym 27]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_let1_like_add_example:
  ∀fuel.
    eval_let1_like (SUC (SUC fuel)) []
      (Expr [Var 0; IntLit 2])
      (Expr [Sym 11; Var 0; IntLit 1])
      (Expr [Sym 56; Expr [Var 0; IntLit 2]]) =
    [IntLit 3]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_let1_like_bad_binding_example:
  ∀fuel.
    eval_let1_like (SUC fuel) []
      (Expr [Sym 24; IntLit 2])
      (Expr [Sym 11; Sym 24; IntLit 1])
      (Expr [Sym 56; Expr [Sym 24; IntLit 2]]) =
    [error_atom (Expr [Sym 56; Expr [Sym 24; IntLit 2]]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_let_star_sequential_example:
  ∀fuel.
    eval_m1_rec (SUC (SUC (SUC fuel))) []
      (Expr [Sym 56;
             Expr [Expr [Var 0; IntLit 1];
                   Expr [Var 1; Expr [Sym 11; Var 0; IntLit 2]]];
             Expr [Sym 11; Var 1; IntLit 3]]) =
    [IntLit 6]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_m1_rec_let_star_bad_binding_example:
  ∀fuel.
    eval_m1_rec (SUC fuel) []
      (Expr [Sym 56; Expr [Expr [Sym 24; IntLit 2]];
             Expr [Sym 11; Sym 24; IntLit 1]]) =
    [error_atom
       (Expr [Sym 56; Expr [Expr [Sym 24; IntLit 2]];
              Expr [Sym 11; Sym 24; IntLit 1]]) (Sym 10)]
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

Theorem eval_typed_fragment_add_good_example:
  ∀fuel.
    eval_typed_fragment (SUC fuel)
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 38; Sym 24; Sym 24]) =
    [Sym 24]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_typed_fragment_add_bad_arg_example:
  ∀fuel.
    eval_typed_fragment (SUC fuel)
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 25; Expr [Sym 37; Sym 36; Sym 36]];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 38; Sym 25; Sym 24]) =
    [error_atom (Expr [Sym 38; Sym 25; Sym 24]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_evalc_fragment_good_example:
  ∀fuel.
    eval_evalc_fragment (SUC fuel)
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 57; Expr [Sym 38; Sym 24; Sym 24]; Sym 36]) =
    [Sym 24]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_evalc_fragment_bad_result_type_example:
  ∀fuel.
    eval_evalc_fragment (SUC fuel)
      [Expr [Sym 34; Sym 24; Sym 36];
       Expr [Sym 34; Sym 38; Expr [Sym 37; Sym 36; Sym 36; Sym 36]];
       Expr [Sym 2; Expr [Sym 38; Var 0; Sym 24]; Var 0]]
      (Expr [Sym 57; Expr [Sym 38; Sym 24; Sym 24]; Sym 42]) =
    [error_atom (Expr [Sym 38; Sym 24; Sym 24]) (Sym 10)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem eval_vec_cons_fragment_good_example:
  eval_vec_cons_fragment
    [Expr [Sym 34; Sym 24; Sym 50];
     Expr [Sym 34; Sym 52; Expr [Sym 49; Sym 50; Sym 53]]]
    (Expr [Sym 58; Sym 24; Sym 52]) =
  [Expr [Sym 49; Sym 50; Expr [Sym 51; Sym 53]]]
Proof
  EVAL_TAC \\ rw[]
QED
