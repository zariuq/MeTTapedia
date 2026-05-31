Theory substitution_zoo
Ancestors
  metta_m1
Libs
  preamble

Definition subst_extends_def:
  subst_extends old new ⇔
    ∀v a. lookup_bind v old = SOME a ⇒ lookup_bind v new = SOME a
End

Theorem lookup_bind_append:
  ∀v xs ys.
    lookup_bind v (xs ++ ys) =
      case lookup_bind v xs of
      | SOME a => SOME a
      | NONE => lookup_bind v ys
Proof
  Induct_on ‘xs’ \\ rw[lookup_bind_def] \\ Cases_on ‘h’ \\ rw[lookup_bind_def]
QED

Theorem lookup_bind_cons_preserve:
  ∀old v a w b.
    lookup_bind v old = NONE ∧ lookup_bind w old = SOME b ⇒
    lookup_bind w (Bind v a :: old) = SOME b
Proof
  rw[lookup_bind_def] \\ Cases_on ‘w = v’ \\ gvs[]
QED

Theorem subst_extends_refl:
  ∀bs. subst_extends bs bs
Proof
  rw[subst_extends_def]
QED

Theorem subst_extends_trans:
  ∀a b c. subst_extends a b ∧ subst_extends b c ⇒ subst_extends a c
Proof
  rw[subst_extends_def] \\ res_tac
QED

Theorem subst_extends_cons_fresh:
  ∀bs v a.
    lookup_bind v bs = NONE ⇒ subst_extends bs (Bind v a :: bs)
Proof
  rw[subst_extends_def] \\
  rename1 ‘lookup_bind w bs = SOME b’ \\
  Cases_on ‘w = v’ \\ gvs[lookup_bind_def]
QED

Theorem bind_var_extends:
  ∀v a bs new.
    bind_var v a bs = SOME new ⇒ subst_extends bs new
Proof
  rw[bind_var_def] \\
  Cases_on ‘lookup_bind v bs’ \\ gvs[] >-
    (irule subst_extends_cons_fresh \\ fs[]) \\
  Cases_on ‘x = a’ \\ gvs[subst_extends_refl]
QED

Theorem subst_extends_apply_bound_var:
  ∀old new v a.
    subst_extends old new ∧ lookup_bind v old = SOME a ⇒
    apply_subst new (Var v) = a
Proof
  rw[subst_extends_def, apply_subst_def] \\ res_tac \\ fs[]
QED

Theorem subst_extends_apply_covered_var:
  ∀old new v.
    (∃a. lookup_bind v old = SOME a) ∧ subst_extends old new ⇒
    apply_subst new (Var v) = apply_subst old (Var v)
Proof
  rw[subst_extends_def, apply_subst_def] \\ res_tac \\ fs[]
QED

Definition subst_covers_def:
  subst_covers bs (Sym n) = T ∧
  subst_covers bs (Var v) = (∃a. lookup_bind v bs = SOME a) ∧
  subst_covers bs (IntLit i) = T ∧
  subst_covers bs (StrLit s) = T ∧
  subst_covers bs (Expr xs) = subst_covers_list bs xs ∧
  subst_covers_list bs [] = T ∧
  subst_covers_list bs (x :: xs) =
    (subst_covers bs x ∧ subst_covers_list bs xs)
Termination
  WF_REL_TAC
    ‘measure (λx.
       case x of
       | INL (bs,a) => atom_depth a
       | INR (bs,xs) => atom_list_depth xs)’ \\
  rw[atom_depth_def] \\ DECIDE_TAC
End

Theorem subst_extends_covers:
  (∀a bs bs2.
     subst_covers bs a ∧ subst_extends bs bs2 ⇒ subst_covers bs2 a) ∧
  (∀xs bs bs2.
     subst_covers_list bs xs ∧ subst_extends bs bs2 ⇒
     subst_covers_list bs2 xs)
Proof
  ho_match_mp_tac atom_induction \\
  rw[subst_covers_def, subst_extends_def] \\ res_tac \\ fs[]
QED

Theorem subst_covers_list_EVERY:
  ∀xs bs. subst_covers_list bs xs ⇔ EVERY (subst_covers bs) xs
Proof
  Induct \\ rw[subst_covers_def]
QED

Theorem atom_depth_mem_lt:
  ∀xs a. MEM a xs ⇒ atom_depth a < atom_depth (Expr xs)
Proof
  Induct \\ rw[atom_depth_def] >-
    (imp_res_tac atom_depth_pos \\ DECIDE_TAC) \\
  res_tac \\ fs[atom_depth_def] \\
  imp_res_tac atom_depth_pos \\ DECIDE_TAC
QED

Theorem subst_extends_apply_covers_atom:
  ∀a bs bs2.
    subst_covers bs a ∧ subst_extends bs bs2 ⇒
    apply_subst bs2 a = apply_subst bs a
Proof
  completeInduct_on ‘atom_depth a’ \\
  rw[] \\
  Cases_on ‘a’ \\ gvs[subst_covers_def, apply_subst_def,
                       subst_covers_list_EVERY] >-
    (fs[subst_extends_def] \\ res_tac \\ fs[]) \\
  simp[MAP_EQ_f] \\ rw[] \\
  first_x_assum irule \\
  imp_res_tac atom_depth_mem_lt \\
  fs[EVERY_MEM]
QED

Theorem subst_extends_apply_covers_list:
  ∀xs bs bs2.
    subst_covers_list bs xs ∧ subst_extends bs bs2 ⇒
    MAP (apply_subst bs2) xs = MAP (apply_subst bs) xs
Proof
  rw[subst_covers_list_EVERY, MAP_EQ_f] \\
  irule subst_extends_apply_covers_atom \\ fs[EVERY_MEM]
QED

Theorem subst_extends_apply_covers:
  (∀a bs bs2.
     subst_covers bs a ∧ subst_extends bs bs2 ⇒
     apply_subst bs2 a = apply_subst bs a) ∧
  (∀xs bs bs2.
     subst_covers_list bs xs ∧ subst_extends bs bs2 ⇒
     MAP (apply_subst bs2) xs = MAP (apply_subst bs) xs)
Proof
  rw[subst_extends_apply_covers_atom, subst_extends_apply_covers_list]
QED

Theorem bind_var_lookup:
  ∀v a bs bs2.
    bind_var v a bs = SOME bs2 ⇒ lookup_bind v bs2 = SOME a
Proof
  rw[bind_var_def] \\ every_case_tac \\ gvs[lookup_bind_def]
QED

Theorem match_sound_ext:
  (∀p q bs bs2.
     match_atom p q bs = SOME bs2 ⇒
     subst_extends bs bs2 ∧ subst_covers bs2 p ∧
     ∀bs3. subst_extends bs2 bs3 ⇒ apply_subst bs3 p = q) ∧
  (∀ps qs bs bs2.
     match_list ps qs bs = SOME bs2 ⇒
     subst_extends bs bs2 ∧ subst_covers_list bs2 ps ∧
     ∀bs3. subst_extends bs2 bs3 ⇒ MAP (apply_subst bs3) ps = qs)
Proof
  ho_match_mp_tac match_atom_ind \\
  rw[match_atom_def] \\ gvs[] \\
  every_case_tac \\ gvs[] \\
  imp_res_tac bind_var_extends \\
  imp_res_tac bind_var_lookup \\
  rpt (first_x_assum (drule_all_then strip_assume_tac)) \\
  imp_res_tac subst_extends_trans \\
  imp_res_tac subst_extends_covers \\
  imp_res_tac subst_extends_apply_bound_var \\
  imp_res_tac subst_extends_apply_covers_atom \\
  imp_res_tac subst_extends_apply_covers_list \\
  gvs[subst_extends_refl, subst_covers_def, apply_subst_def,
      subst_extends_apply_bound_var] \\
  simp[MAP_EQ_f]
QED

Theorem match_sound:
  (∀p q bs bs2.
     match_atom p q bs = SOME bs2 ⇒
     subst_extends bs bs2 ∧ subst_covers bs2 p ∧ apply_subst bs2 p = q) ∧
  (∀ps qs bs bs2.
     match_list ps qs bs = SOME bs2 ⇒
     subst_extends bs bs2 ∧ subst_covers_list bs2 ps ∧
     MAP (apply_subst bs2) ps = qs)
Proof
  metis_tac[match_sound_ext, subst_extends_refl]
QED

Datatype:
  subst_constraint = CEq atom atom
                   | CMatch atom atom
                   | CAbbrev num atom
End

Definition constraint_holds_def:
  constraint_holds bs (CEq lhs rhs) =
    (apply_subst bs lhs = apply_subst bs rhs) ∧
  constraint_holds bs (CMatch pattern subject) =
    (apply_subst bs pattern = subject) ∧
  constraint_holds bs (CAbbrev v atom) =
    (apply_subst bs (Var v) = apply_subst bs atom)
End

Definition constraints_hold_def:
  constraints_hold bs [] = T ∧
  constraints_hold bs (c :: cs) =
    (constraint_holds bs c ∧ constraints_hold bs cs)
End

Definition add_constraint_def:
  add_constraint c cs = c :: cs
End

Definition defer_constraint_def:
  defer_constraint c cs = cs ++ [c]
End

Definition simplify_constraint_def:
  simplify_constraint bs c =
    if constraint_holds bs c then [] else [c]
End

Definition simplify_queue_def:
  simplify_queue bs [] = [] ∧
  simplify_queue bs (c :: cs) =
    simplify_constraint bs c ++ simplify_queue bs cs
End

Definition constraint_covers_def:
  constraint_covers bs (CEq lhs rhs) =
    (subst_covers bs lhs ∧ subst_covers bs rhs) ∧
  constraint_covers bs (CMatch pattern subject) =
    subst_covers bs pattern ∧
  constraint_covers bs (CAbbrev v atom) =
    ((∃a. lookup_bind v bs = SOME a) ∧ subst_covers bs atom)
End

Definition constraints_cover_def:
  constraints_cover bs [] = T ∧
  constraints_cover bs (c :: cs) =
    (constraint_covers bs c ∧ constraints_cover bs cs)
End

Datatype:
  constraint_rule_result = RuleOK (binding list) (subst_constraint list)
                         | RuleFail
End

Definition simplify_constraint_rule_def:
  simplify_constraint_rule bs c =
    if constraint_holds bs c ∧ constraint_covers bs c then RuleOK bs []
    else
      case c of
      | CEq (Var v) rhs =>
          if subst_covers bs rhs then
            case bind_var v (apply_subst bs rhs) bs of
            | SOME bs2 => RuleOK bs2 []
            | NONE => RuleFail
          else RuleOK bs [c]
      | CEq lhs (Var v) =>
          if subst_covers bs lhs then
            case bind_var v (apply_subst bs lhs) bs of
            | SOME bs2 => RuleOK bs2 []
            | NONE => RuleFail
          else RuleOK bs [c]
      | CEq lhs rhs => RuleOK bs [c]
      | CMatch pattern subject =>
          (case match_atom pattern subject bs of
           | SOME bs2 => RuleOK bs2 []
           | NONE => RuleFail)
      | CAbbrev v atom =>
          if subst_covers bs atom then
            case bind_var v (apply_subst bs atom) bs of
            | SOME bs2 => RuleOK bs2 []
            | NONE => RuleFail
          else RuleOK bs [c]
End

Definition simplify_queue_rule_def:
  simplify_queue_rule bs [] = RuleOK bs [] ∧
  simplify_queue_rule bs (c :: cs) =
    case simplify_constraint_rule bs c of
    | RuleFail => RuleFail
    | RuleOK bs2 residual =>
        (case simplify_queue_rule bs2 cs of
         | RuleFail => RuleFail
         | RuleOK bs3 residual2 => RuleOK bs3 (residual ++ residual2))
End

Definition solved_form_def:
  solved_form [] = T ∧
  solved_form (CAbbrev v atom :: cs) = solved_form cs ∧
  solved_form (_ :: cs) = F
End

Definition extract_solved_bindings_def:
  extract_solved_bindings [] = [] ∧
  extract_solved_bindings (CAbbrev v atom :: cs) =
    Bind v atom :: extract_solved_bindings cs ∧
  extract_solved_bindings (_ :: cs) = extract_solved_bindings cs
End

Theorem constraints_hold_cons:
  ∀bs c cs.
    constraints_hold bs (c :: cs) ⇔
    constraint_holds bs c ∧ constraints_hold bs cs
Proof
  rw[constraints_hold_def]
QED

Theorem constraints_hold_append:
  ∀bs xs ys.
    constraints_hold bs (xs ++ ys) ⇔
    constraints_hold bs xs ∧ constraints_hold bs ys
Proof
  Induct_on ‘xs’ \\ rw[constraints_hold_def] \\ metis_tac[]
QED

Theorem constraints_hold_add_sound:
  ∀bs c cs.
    constraint_holds bs c ∧ constraints_hold bs cs ⇒
    constraints_hold bs (add_constraint c cs)
Proof
  rw[add_constraint_def, constraints_hold_def]
QED

Theorem constraints_hold_defer:
  ∀bs c cs.
    constraints_hold bs (defer_constraint c cs) ⇔
    constraints_hold bs cs ∧ constraint_holds bs c
Proof
  rw[defer_constraint_def, constraints_hold_append, constraints_hold_def]
QED

Theorem simplify_constraint_preserves:
  ∀bs c.
    constraints_hold bs (simplify_constraint bs c) ⇔
    constraint_holds bs c
Proof
  rw[simplify_constraint_def, constraints_hold_def]
QED

Theorem simplify_queue_preserves:
  ∀bs cs.
    constraints_hold bs (simplify_queue bs cs) ⇔
    constraints_hold bs cs
Proof
  Induct_on ‘cs’ \\
  rw[simplify_queue_def, constraints_hold_def, constraints_hold_append,
     simplify_constraint_preserves]
QED

Theorem constraint_holds_extends:
  ∀old new c.
    constraint_holds old c ∧ constraint_covers old c ∧
    subst_extends old new ⇒
    constraint_holds new c
Proof
  Cases_on ‘c’ \\
  rw[constraint_holds_def, constraint_covers_def] \\
  imp_res_tac subst_extends_apply_covers_atom \\
  imp_res_tac subst_extends_apply_covered_var \\
  imp_res_tac subst_extends_apply_bound_var \\
  fs[]
QED

Theorem constraints_hold_extends:
  ∀old new cs.
    constraints_hold old cs ∧ constraints_cover old cs ∧
    subst_extends old new ⇒
    constraints_hold new cs
Proof
  Induct_on ‘cs’ \\
  rw[constraints_hold_def, constraints_cover_def] \\
  metis_tac[constraint_holds_extends]
QED

Theorem constraints_hold_member:
  ∀bs cs c.
    constraints_hold bs cs ∧ MEM c cs ⇒ constraint_holds bs c
Proof
  Induct_on ‘cs’ \\ rw[constraints_hold_def] \\ metis_tac[]
QED

Theorem extract_solved_bindings_member:
  ∀cs v atom.
    MEM (Bind v atom) (extract_solved_bindings cs) ⇒
    MEM (CAbbrev v atom) cs
Proof
  Induct_on ‘cs’ \\
  rw[extract_solved_bindings_def] \\
  Cases_on ‘h’ \\ gvs[extract_solved_bindings_def] \\ metis_tac[]
QED

Theorem extract_solved_bindings_sound:
  ∀bs cs v atom.
    constraints_hold bs cs ∧
    MEM (Bind v atom) (extract_solved_bindings cs) ⇒
    constraint_holds bs (CAbbrev v atom)
Proof
  metis_tac[extract_solved_bindings_member, constraints_hold_member]
QED

Theorem simplify_constraint_rule_extends:
  ∀bs c bs2 residual.
    simplify_constraint_rule bs c = RuleOK bs2 residual ⇒
    subst_extends bs bs2
Proof
  rw[simplify_constraint_rule_def] \\
  every_case_tac \\ gvs[subst_extends_refl] \\
  imp_res_tac bind_var_extends \\
  imp_res_tac match_sound \\ fs[]
QED

Theorem simplify_constraint_rule_sound_ext:
  ∀bs c bs2 residual final.
    simplify_constraint_rule bs c = RuleOK bs2 residual ∧
    subst_extends bs2 final ∧ constraints_hold final residual ⇒
    constraint_holds final c
Proof
  rw[simplify_constraint_rule_def] \\
  every_case_tac \\ gvs[constraints_hold_def] \\
  imp_res_tac constraint_holds_extends \\
  imp_res_tac bind_var_extends \\
  imp_res_tac bind_var_lookup \\
  imp_res_tac subst_extends_trans \\
  imp_res_tac subst_extends_apply_bound_var \\
  imp_res_tac subst_extends_apply_covers_atom \\
  imp_res_tac match_sound_ext \\
  gvs[constraint_holds_def]
QED

Theorem simplify_queue_rule_extends:
  ∀cs bs bs2 residual.
    simplify_queue_rule bs cs = RuleOK bs2 residual ⇒
    subst_extends bs bs2
Proof
  Induct \\ rw[simplify_queue_rule_def, subst_extends_refl] \\
  every_case_tac \\ gvs[] \\
  imp_res_tac simplify_constraint_rule_extends \\
  first_x_assum drule \\
  rw[] \\
  imp_res_tac subst_extends_trans
QED

Theorem simplify_queue_rule_sound:
  ∀cs bs bs2 residual.
    simplify_queue_rule bs cs = RuleOK bs2 residual ∧
    constraints_hold bs2 residual ⇒
    constraints_hold bs2 cs
Proof
  Induct \\ rw[simplify_queue_rule_def, constraints_hold_def] \\
  every_case_tac \\ gvs[constraints_hold_append, constraints_hold_def] \\
  imp_res_tac simplify_queue_rule_extends \\
  metis_tac[simplify_constraint_rule_sound_ext]
QED

Theorem solved_form_abbrev_pair:
  ∀v a w b.
    solved_form [CAbbrev v a; CAbbrev w b]
Proof
  rw[solved_form_def]
QED

Theorem solved_form_rejects_eq:
  ∀a b. ¬solved_form [CEq a b]
Proof
  rw[solved_form_def]
QED

Theorem extract_solved_bindings_example:
  ∀v n a.
    extract_solved_bindings [CAbbrev v (Sym n); CEq a a] =
    [Bind v (Sym n)]
Proof
  rw[extract_solved_bindings_def]
QED

Theorem simplify_constraint_rule_eq_left_example:
  simplify_constraint_rule [] (CEq (Var 0) (Sym 1)) =
    RuleOK [Bind 0 (Sym 1)] []
Proof
  EVAL_TAC \\ rw[]
QED

Theorem simplify_constraint_rule_eq_conflict_example:
  simplify_constraint_rule [Bind 0 (Sym 1)] (CEq (Var 0) (Sym 2)) =
    RuleFail
Proof
  EVAL_TAC \\ rw[]
QED

Theorem simplify_constraint_rule_match_example:
  simplify_constraint_rule []
    (CMatch (Expr [Sym 0; Var 1]) (Expr [Sym 0; Sym 2])) =
    RuleOK [Bind 1 (Sym 2)] []
Proof
  EVAL_TAC \\ rw[]
QED

Theorem simplify_constraint_positive_drops:
  ∀v n.
    simplify_constraint [Bind v (Sym n)] (CEq (Var v) (Sym n)) = []
Proof
  rw[simplify_constraint_def, constraint_holds_def, apply_subst_def,
     lookup_bind_def]
QED

Theorem simplify_constraint_negative_defers:
  ∀v n m.
    n ≠ m ⇒
    simplify_constraint [Bind v (Sym n)] (CEq (Var v) (Sym m)) =
      [CEq (Var v) (Sym m)]
Proof
  rw[simplify_constraint_def, constraint_holds_def, apply_subst_def,
     lookup_bind_def]
QED

Theorem constraint_eq_var_sym_positive:
  ∀v n.
    constraint_holds [Bind v (Sym n)] (CEq (Var v) (Sym n))
Proof
  rw[constraint_holds_def, apply_subst_def, lookup_bind_def]
QED

Theorem constraint_eq_var_sym_negative:
  ∀v n m.
    n ≠ m ⇒
    ¬constraint_holds [Bind v (Sym n)] (CEq (Var v) (Sym m))
Proof
  rw[constraint_holds_def, apply_subst_def, lookup_bind_def]
QED

Theorem constraint_abbrev_var_sym_positive:
  ∀v n.
    constraint_holds [Bind v (Sym n)] (CAbbrev v (Sym n))
Proof
  rw[constraint_holds_def, apply_subst_def, lookup_bind_def]
QED

Theorem match_sound_constraint:
  ∀p q bs bs2.
    match_atom p q bs = SOME bs2 ⇒
    constraint_holds bs2 (CMatch p q)
Proof
  rw[constraint_holds_def] \\ imp_res_tac match_sound \\ fs[]
QED

Theorem equality_step_instantiates_lhs:
  ∀space atom out.
    equality_step space atom out ⇒
    ∃lhs rhs bs.
      MEM (Expr [Sym 2; lhs; rhs]) space ∧
      match_atom lhs atom [] = SOME bs ∧
      out = apply_subst bs rhs ∧
      apply_subst bs lhs = atom
Proof
  rw[equality_step_def] \\ metis_tac[match_sound]
QED

Theorem eval_m1_match_member_instantiates_pattern:
  ∀fuel space pattern templ out.
    MEM out (eval_m1 (SUC fuel) space (Expr [Sym 4; Sym 5; pattern; templ])) ⇒
    ∃entry bs.
      MEM entry space ∧
      match_atom pattern entry [] = SOME bs ∧
      out = apply_subst bs templ ∧
      apply_subst bs pattern = entry
Proof
  metis_tac[eval_m1_match_member_sound, match_sound]
QED

Theorem eval_m1_match_member_constraint_sound:
  ∀fuel space pattern templ out.
    MEM out (eval_m1 (SUC fuel) space (Expr [Sym 4; Sym 5; pattern; templ])) ⇒
    ∃entry bs.
      MEM entry space ∧
      match_atom pattern entry [] = SOME bs ∧
      out = apply_subst bs templ ∧
      constraint_holds bs (CMatch pattern entry)
Proof
  metis_tac[eval_m1_match_member_instantiates_pattern, constraint_holds_def]
QED

Definition subst_binding_def:
  subst_binding outer (Bind v a) = Bind v (apply_subst outer a)
End

Definition compose_subst_def:
  compose_subst outer inner = MAP (subst_binding outer) inner ++ outer
End

Theorem lookup_bind_subst_binding_hit:
  ∀v a outer inner.
    lookup_bind v inner = SOME a ⇒
    lookup_bind v (MAP (subst_binding outer) inner) =
      SOME (apply_subst outer a)
Proof
  Induct_on ‘inner’ \\ rw[lookup_bind_def] \\
  Cases_on ‘h’ \\ gvs[lookup_bind_def, subst_binding_def] \\
  Cases_on ‘v = n’ \\ gvs[]
QED

Theorem compose_subst_var_hit_inner:
  ∀v a outer inner.
    lookup_bind v inner = SOME a ⇒
    apply_subst (compose_subst outer inner) (Var v) = apply_subst outer a
Proof
  rw[compose_subst_def, apply_subst_def, lookup_bind_append] \\
  imp_res_tac lookup_bind_subst_binding_hit \\ fs[]
QED

Theorem compose_subst_var_hit_outer:
  ∀v a outer inner.
    lookup_bind v inner = NONE ∧ lookup_bind v outer = SOME a ⇒
    apply_subst (compose_subst outer inner) (Var v) = a
Proof
  rw[compose_subst_def, apply_subst_def, lookup_bind_append] \\
  Induct_on ‘inner’ \\ rw[lookup_bind_def] \\
  Cases_on ‘h’ \\ gvs[lookup_bind_def, subst_binding_def]
QED

Definition bind_trail_def:
  bind_trail v a bs =
    case bind_var v a bs of
    | NONE => NONE
    | SOME bs2 => SOME (bs2,bs)
End

Definition rollback_def:
  rollback tr = SND tr
End

Theorem bind_trail_extends:
  ∀v a bs bs2 saved.
    bind_trail v a bs = SOME (bs2,saved) ⇒
    saved = bs ∧ subst_extends bs bs2
Proof
  rw[bind_trail_def] \\ every_case_tac \\ gvs[] \\
  imp_res_tac bind_var_extends \\ fs[]
QED

Theorem bind_trail_rollback:
  ∀v a bs bs2 saved.
    bind_trail v a bs = SOME (bs2,saved) ⇒ rollback (bs2,saved) = bs
Proof
  rw[bind_trail_def, rollback_def] \\ every_case_tac \\ gvs[]
QED

Definition deref_var_def:
  deref_var 0 bs v = Var v ∧
  deref_var (SUC fuel) bs v =
    case lookup_bind v bs of
    | NONE => Var v
    | SOME (Var w) => deref_var fuel bs w
    | SOME a => a
End

Theorem deref_var_empty:
  ∀fuel v. deref_var fuel [] v = Var v
Proof
  Cases \\ rw[deref_var_def, lookup_bind_def]
QED

Theorem deref_var_direct_hit:
  ∀fuel v a.
    (∀w. a ≠ Var w) ⇒ deref_var (SUC fuel) [Bind v a] v = a
Proof
  rw[deref_var_def, lookup_bind_def] \\ Cases_on ‘a’ \\ gvs[]
QED

Theorem deref_var_chain_two:
  ∀v w a.
    v ≠ w ∧ (∀u. a ≠ Var u) ⇒
    deref_var 2 [Bind v (Var w); Bind w a] v = a
Proof
  rw[] \\ Cases_on ‘a’ \\ gvs[] \\ EVAL_TAC \\ rw[]
QED

Theorem deref_var_self_cycle_fuel_one:
  ∀v. deref_var 1 [Bind v (Var v)] v = Var v
Proof
  EVAL_TAC \\ rw[]
QED

Definition occurs_in_def:
  occurs_in v (Sym n) = F ∧
  occurs_in v (Var w) = (v = w) ∧
  occurs_in v (IntLit i) = F ∧
  occurs_in v (StrLit s) = F ∧
  occurs_in v (Expr xs) = occurs_in_list v xs ∧
  occurs_in_list v [] = F ∧
  occurs_in_list v (x :: xs) = (occurs_in v x ∨ occurs_in_list v xs)
Termination
  WF_REL_TAC
    ‘measure (λx.
       case x of
       | INL (v,a) => atom_depth a
       | INR (v,xs) => atom_list_depth xs)’ \\
  rw[atom_depth_def] \\ DECIDE_TAC
End

Definition bind_var_occurs_def:
  bind_var_occurs v a bs =
    if occurs_in v a then NONE else bind_var v a bs
End

Definition bind_var_occurs_checked_def:
  bind_var_occurs_checked v a bs =
    case lookup_bind v bs of
    | NONE =>
        let rhs = apply_subst bs a in
          if occurs_in v rhs then NONE else bind_var v rhs bs
    | SOME old => bind_var v (apply_subst bs a) bs
End

Definition simplify_constraint_rule_occurs_def:
  simplify_constraint_rule_occurs bs c =
    if constraint_holds bs c ∧ constraint_covers bs c then RuleOK bs []
    else
      case c of
      | CEq (Var v) rhs =>
          if rhs = Var v then RuleOK bs []
          else if occurs_in v (apply_subst bs rhs) then RuleFail
          else if subst_covers bs rhs then
            case bind_var_occurs_checked v rhs bs of
            | SOME bs2 => RuleOK bs2 []
            | NONE => RuleFail
          else RuleOK bs [c]
      | CEq lhs (Var v) =>
          if lhs = Var v then RuleOK bs []
          else if occurs_in v (apply_subst bs lhs) then RuleFail
          else if subst_covers bs lhs then
            case bind_var_occurs_checked v lhs bs of
            | SOME bs2 => RuleOK bs2 []
            | NONE => RuleFail
          else RuleOK bs [c]
      | CEq lhs rhs => RuleOK bs [c]
      | CMatch pattern subject =>
          (case match_atom pattern subject bs of
           | SOME bs2 => RuleOK bs2 []
           | NONE => RuleFail)
      | CAbbrev v atom =>
          if atom = Var v then RuleOK bs []
          else if occurs_in v (apply_subst bs atom) then RuleFail
          else if subst_covers bs atom then
            case bind_var_occurs_checked v atom bs of
            | SOME bs2 => RuleOK bs2 []
            | NONE => RuleFail
          else RuleOK bs [c]
End

Definition simplify_queue_rule_occurs_def:
  simplify_queue_rule_occurs bs [] = RuleOK bs [] ∧
  simplify_queue_rule_occurs bs (c :: cs) =
    case simplify_constraint_rule_occurs bs c of
    | RuleFail => RuleFail
    | RuleOK bs2 residual =>
        (case simplify_queue_rule_occurs bs2 cs of
         | RuleFail => RuleFail
         | RuleOK bs3 residual2 => RuleOK bs3 (residual ++ residual2))
End

Definition solved_form_loop_def:
  solved_form_loop 0 bs cs = simplify_queue_rule_occurs bs cs ∧
  solved_form_loop (SUC fuel) bs cs =
    case simplify_queue_rule_occurs bs cs of
    | RuleFail => RuleFail
    | RuleOK bs2 residual =>
        if residual = [] ∨ solved_form residual ∨ residual = cs then
          RuleOK bs2 residual
        else solved_form_loop fuel bs2 residual
End

Theorem occurs_in_var_self:
  ∀v. occurs_in v (Var v)
Proof
  rw[occurs_in_def]
QED

Theorem occurs_in_var_other:
  ∀v w. v ≠ w ⇒ ¬occurs_in v (Var w)
Proof
  rw[occurs_in_def]
QED

Theorem bind_var_occurs_rejects_self:
  ∀v bs. bind_var_occurs v (Var v) bs = NONE
Proof
  rw[bind_var_occurs_def, occurs_in_def]
QED

Theorem bind_var_occurs_accepts_fresh:
  ∀v a bs.
    ¬occurs_in v a ⇒ bind_var_occurs v a bs = bind_var v a bs
Proof
  rw[bind_var_occurs_def]
QED

Theorem bind_var_occurs_checked_extends:
  ∀v a bs bs2.
    bind_var_occurs_checked v a bs = SOME bs2 ⇒
    subst_extends bs bs2
Proof
  rw[bind_var_occurs_checked_def] \\
  every_case_tac \\ gvs[] \\
  imp_res_tac bind_var_extends
QED

Theorem bind_var_occurs_checked_lookup:
  ∀v a bs bs2.
    bind_var_occurs_checked v a bs = SOME bs2 ⇒
    lookup_bind v bs2 = SOME (apply_subst bs a)
Proof
  rw[bind_var_occurs_checked_def] \\
  every_case_tac \\ gvs[] \\
  imp_res_tac bind_var_lookup
QED

Theorem simplify_constraint_rule_occurs_extends:
  ∀bs c bs2 residual.
    simplify_constraint_rule_occurs bs c = RuleOK bs2 residual ⇒
    subst_extends bs bs2
Proof
  rw[simplify_constraint_rule_occurs_def] \\
  every_case_tac \\ gvs[subst_extends_refl] \\
  imp_res_tac bind_var_occurs_checked_extends \\
  imp_res_tac match_sound \\ fs[]
QED

Theorem simplify_constraint_rule_occurs_sound_ext:
  ∀bs c bs2 residual final.
    simplify_constraint_rule_occurs bs c = RuleOK bs2 residual ∧
    subst_extends bs2 final ∧ constraints_hold final residual ⇒
    constraint_holds final c
Proof
  rw[simplify_constraint_rule_occurs_def] \\
  every_case_tac \\ gvs[constraints_hold_def] \\
  imp_res_tac constraint_holds_extends \\
  imp_res_tac bind_var_occurs_checked_extends \\
  imp_res_tac bind_var_occurs_checked_lookup \\
  imp_res_tac subst_extends_trans \\
  imp_res_tac subst_extends_apply_bound_var \\
  imp_res_tac subst_extends_apply_covers_atom \\
  imp_res_tac match_sound_ext \\
  gvs[constraint_holds_def]
QED

Theorem simplify_queue_rule_occurs_extends:
  ∀cs bs bs2 residual.
    simplify_queue_rule_occurs bs cs = RuleOK bs2 residual ⇒
    subst_extends bs bs2
Proof
  Induct \\ rw[simplify_queue_rule_occurs_def, subst_extends_refl] \\
  every_case_tac \\ gvs[] \\
  imp_res_tac simplify_constraint_rule_occurs_extends \\
  first_x_assum drule \\
  rw[] \\
  imp_res_tac subst_extends_trans
QED

Theorem simplify_queue_rule_occurs_sound_ext:
  ∀cs bs bs2 residual final.
    simplify_queue_rule_occurs bs cs = RuleOK bs2 residual ∧
    subst_extends bs2 final ∧ constraints_hold final residual ⇒
    constraints_hold final cs
Proof
  Induct \\ rw[simplify_queue_rule_occurs_def, constraints_hold_def] \\
  every_case_tac \\ gvs[constraints_hold_append, constraints_hold_def] \\
  imp_res_tac simplify_constraint_rule_occurs_extends \\
  imp_res_tac simplify_queue_rule_occurs_extends \\
  metis_tac[
    simplify_constraint_rule_occurs_sound_ext,
    subst_extends_trans]
QED

Theorem solved_form_loop_extends:
  ∀fuel bs cs bs2 residual.
    solved_form_loop fuel bs cs = RuleOK bs2 residual ⇒
    subst_extends bs bs2
Proof
  Induct \\ rw[solved_form_loop_def] \\
  every_case_tac \\ gvs[] \\
  imp_res_tac simplify_queue_rule_occurs_extends \\
  first_x_assum drule_all \\
  rw[] \\
  imp_res_tac subst_extends_trans
QED

Theorem solved_form_loop_sound_ext:
  ∀fuel bs cs bs2 residual final.
    solved_form_loop fuel bs cs = RuleOK bs2 residual ∧
    subst_extends bs2 final ∧ constraints_hold final residual ⇒
    constraints_hold final cs
Proof
  Induct \\ rw[solved_form_loop_def] \\
  every_case_tac \\ gvs[] \\
  imp_res_tac simplify_queue_rule_occurs_extends \\
  imp_res_tac solved_form_loop_extends \\
  metis_tac[
    simplify_queue_rule_occurs_sound_ext,
    subst_extends_trans]
QED

Theorem simplify_queue_rule_occurs_rejects_direct_cycle:
  simplify_queue_rule_occurs []
    [CEq (Var 0) (Expr [Var 0])] = RuleFail
Proof
  EVAL_TAC \\ rw[]
QED

Theorem simplify_queue_rule_occurs_rejects_indirect_cycle:
  simplify_queue_rule_occurs []
    [CEq (Var 1) (Sym 2); CEq (Var 0) (Expr [Var 1; Var 0])] =
    RuleFail
Proof
  EVAL_TAC \\ rw[]
QED

Theorem solved_form_loop_occurs_accepts_chain:
  solved_form_loop 3 []
    [CEq (Var 0) (Sym 1); CEq (Var 1) (Sym 2)] =
    RuleOK [Bind 1 (Sym 2); Bind 0 (Sym 1)] []
Proof
  EVAL_TAC \\ rw[]
QED

Theorem solved_form_loop_deferred_abbrev_example:
  solved_form_loop 1 [] [CAbbrev 0 (Var 1)] =
    RuleOK [] [CAbbrev 0 (Var 1)]
Proof
  EVAL_TAC \\ rw[]
QED

Definition extract_solved_bindings_seq_def:
  extract_solved_bindings_seq bs [] = SOME bs ∧
  extract_solved_bindings_seq bs (CAbbrev v atom :: cs) =
    (if subst_covers bs atom then
       case bind_var_occurs_checked v atom bs of
       | SOME bs2 => extract_solved_bindings_seq bs2 cs
       | NONE => NONE
     else NONE) ∧
  extract_solved_bindings_seq bs (_ :: cs) = NONE
End

Theorem extract_solved_bindings_seq_extends:
  ∀cs bs bs2.
    extract_solved_bindings_seq bs cs = SOME bs2 ⇒
    subst_extends bs bs2
Proof
  Induct \\ rw[extract_solved_bindings_seq_def, subst_extends_refl] \\
  Cases_on ‘h’ \\ gvs[extract_solved_bindings_seq_def] \\
  every_case_tac \\ gvs[] \\
  imp_res_tac bind_var_occurs_checked_extends \\
  first_x_assum drule \\
  rw[] \\
  imp_res_tac subst_extends_trans
QED

Theorem extract_solved_bindings_seq_sound_ext:
  ∀cs bs bs2 final.
    extract_solved_bindings_seq bs cs = SOME bs2 ∧
    subst_extends bs2 final ⇒
    constraints_hold final cs
Proof
  Induct \\ rw[extract_solved_bindings_seq_def, constraints_hold_def] \\
  Cases_on ‘h’ \\ gvs[extract_solved_bindings_seq_def] \\
  every_case_tac \\ gvs[] \\
  imp_res_tac bind_var_occurs_checked_extends \\
  imp_res_tac bind_var_occurs_checked_lookup \\
  imp_res_tac extract_solved_bindings_seq_extends \\
  imp_res_tac subst_extends_trans \\
  imp_res_tac subst_extends_apply_bound_var \\
  imp_res_tac subst_extends_apply_covers_atom \\
  gvs[constraint_holds_def] \\
  metis_tac[subst_extends_trans]
QED

Theorem extract_solved_bindings_seq_sound:
  ∀cs bs bs2.
    extract_solved_bindings_seq bs cs = SOME bs2 ⇒
    constraints_hold bs2 cs
Proof
  metis_tac[extract_solved_bindings_seq_sound_ext, subst_extends_refl]
QED

Theorem solved_form_loop_extract_sound:
  ∀fuel bs cs bs2 residual final.
    solved_form_loop fuel bs cs = RuleOK bs2 residual ∧
    extract_solved_bindings_seq bs2 residual = SOME final ⇒
    subst_extends bs final ∧ constraints_hold final cs
Proof
  rw[] >-
    metis_tac[
      solved_form_loop_extends,
      extract_solved_bindings_seq_extends,
      subst_extends_trans] \\
  metis_tac[
    solved_form_loop_sound_ext,
    extract_solved_bindings_seq_extends,
    extract_solved_bindings_seq_sound]
QED

Theorem match_atom_extract_solved_residual_sound:
  ∀p q bs bs2 residual final.
    match_atom p q bs = SOME bs2 ∧
    extract_solved_bindings_seq bs2 residual = SOME final ⇒
    subst_extends bs final ∧
    constraint_holds final (CMatch p q) ∧
    constraints_hold final residual
Proof
  rw[] >-
    metis_tac[
      match_sound_ext,
      extract_solved_bindings_seq_extends,
      subst_extends_trans] >-
    metis_tac[
      match_sound_ext,
      extract_solved_bindings_seq_extends,
      constraint_holds_def] \\
  metis_tac[extract_solved_bindings_seq_sound]
QED

Theorem equality_step_extract_solved_residual_sound:
  ∀space atom out residual.
    equality_step space atom out ⇒
    ∃lhs rhs bs.
      MEM (Expr [Sym 2; lhs; rhs]) space ∧
      match_atom lhs atom [] = SOME bs ∧
      out = apply_subst bs rhs ∧
      ∀final.
        extract_solved_bindings_seq bs residual = SOME final ⇒
        subst_extends [] final ∧
        constraint_holds final (CMatch lhs atom) ∧
        constraints_hold final residual
Proof
  rw[equality_step_def] \\
  qexists_tac ‘lhs’ \\
  qexists_tac ‘rhs’ \\
  qexists_tac ‘bs’ \\
  rw[] \\
  metis_tac[match_atom_extract_solved_residual_sound]
QED

Theorem eval_m1_match_member_extract_solved_residual_sound:
  ∀fuel space pattern templ out residual.
    MEM out (eval_m1 (SUC fuel) space (Expr [Sym 4; Sym 5; pattern; templ])) ⇒
    ∃entry bs.
      MEM entry space ∧
      match_atom pattern entry [] = SOME bs ∧
      out = apply_subst bs templ ∧
      ∀final.
        extract_solved_bindings_seq bs residual = SOME final ⇒
        subst_extends [] final ∧
        constraint_holds final (CMatch pattern entry) ∧
        constraints_hold final residual
Proof
  rw[] \\
  imp_res_tac eval_m1_match_member_sound \\
  qexists_tac ‘entry’ \\
  qexists_tac ‘bs’ \\
  rw[] \\
  metis_tac[match_atom_extract_solved_residual_sound]
QED

Theorem extract_solved_bindings_seq_simple_example:
  extract_solved_bindings_seq [] [CAbbrev 0 (Sym 1)] =
    SOME [Bind 0 (Sym 1)]
Proof
  EVAL_TAC \\ rw[]
QED

Theorem extract_solved_bindings_seq_covered_var_example:
  extract_solved_bindings_seq [Bind 1 (Sym 2)] [CAbbrev 0 (Var 1)] =
    SOME [Bind 0 (Sym 2); Bind 1 (Sym 2)]
Proof
  ‘subst_covers [Bind 1 (Sym 2)] (Var 1)’ by
    (rw[subst_covers_def, lookup_bind_def] \\
     qexists_tac ‘Sym 2’ \\
     rw[]) \\
  rw[
    extract_solved_bindings_seq_def,
    bind_var_occurs_checked_def,
    apply_subst_def,
    lookup_bind_def,
    occurs_in_def,
    bind_var_def]
QED

Theorem extract_solved_bindings_seq_uncovered_var_example:
  extract_solved_bindings_seq [] [CAbbrev 0 (Var 1)] = NONE
Proof
  EVAL_TAC \\ rw[]
QED

Theorem solved_form_loop_extract_closed_example:
  solved_form_loop 1 [] [CAbbrev 0 (Sym 1)] =
      RuleOK [Bind 0 (Sym 1)] [] ∧
  extract_solved_bindings_seq [Bind 0 (Sym 1)] [] =
      SOME [Bind 0 (Sym 1)] ∧
  constraints_hold [Bind 0 (Sym 1)] [CAbbrev 0 (Sym 1)]
Proof
  EVAL_TAC \\ rw[]
QED

Definition apply_token_subst_def:
  apply_token_subst bs [] = [] ∧
  apply_token_subst bs (tok :: rest) =
    (case tok of
     | Var v =>
         (case lookup_bind v bs of
          | NONE => Var v :: apply_token_subst bs rest
          | SOME (Expr xs) => xs ++ apply_token_subst bs rest
          | SOME a => a :: apply_token_subst bs rest)
     | _ => tok :: apply_token_subst bs rest)
End

Theorem apply_token_subst_empty:
  ∀stmt. apply_token_subst [] stmt = stmt
Proof
  Induct \\ rw[apply_token_subst_def, lookup_bind_def] \\
  Cases_on ‘h’ \\ rw[apply_token_subst_def, lookup_bind_def]
QED

Theorem apply_token_subst_append:
  ∀bs xs ys.
    apply_token_subst bs (xs ++ ys) =
    apply_token_subst bs xs ++ apply_token_subst bs ys
Proof
  Induct_on ‘xs’ \\ rw[apply_token_subst_def] \\
  Cases_on ‘h’ \\ rw[apply_token_subst_def] \\
  every_case_tac \\ gvs[]
QED

Theorem apply_token_subst_var_hit_atom:
  ∀v a.
    apply_token_subst [Bind v a] [Var v] =
      case a of
      | Expr xs => xs
      | _ => [a]
Proof
  rw[apply_token_subst_def, lookup_bind_def] \\ Cases_on ‘a’ \\ rw[]
QED

Definition lookup_nth_def:
  lookup_nth n [] = NONE ∧
  lookup_nth 0 (x :: xs) = SOME x ∧
  lookup_nth (SUC n) (x :: xs) = lookup_nth n xs
End

Definition apply_pos_subst_def:
  apply_pos_subst subs (Sym n) = Sym n ∧
  apply_pos_subst subs (Var v) =
    (case lookup_nth v subs of
     | NONE => Var v
     | SOME a => a) ∧
  apply_pos_subst subs (IntLit i) = IntLit i ∧
  apply_pos_subst subs (StrLit s) = StrLit s ∧
  apply_pos_subst subs (Expr xs) = Expr (MAP (apply_pos_subst subs) xs)
End

Theorem lookup_nth_hit_zero:
  ∀x xs. lookup_nth 0 (x :: xs) = SOME x
Proof
  rw[lookup_nth_def]
QED

Theorem lookup_nth_miss_empty:
  ∀n. lookup_nth n [] = NONE
Proof
  Cases \\ rw[lookup_nth_def]
QED

Theorem apply_pos_subst_var_hit_zero:
  ∀a rest. apply_pos_subst (a :: rest) (Var 0) = a
Proof
  rw[apply_pos_subst_def, lookup_nth_def]
QED

Theorem apply_pos_subst_var_shift_hit:
  ∀v a rest out.
    lookup_nth v rest = SOME out ⇒
    apply_pos_subst (a :: rest) (Var (SUC v)) = out
Proof
  rw[apply_pos_subst_def, lookup_nth_def]
QED

Theorem apply_pos_subst_var_shift_miss:
  ∀v a rest.
    lookup_nth v rest = NONE ⇒
    apply_pos_subst (a :: rest) (Var (SUC v)) = Var (SUC v)
Proof
  rw[apply_pos_subst_def, lookup_nth_def]
QED

Definition apply_subst_noquote_def:
  apply_subst_noquote q bs (Sym n) = Sym n ∧
  apply_subst_noquote q bs (Var v) =
    (case lookup_bind v bs of
     | NONE => Var v
     | SOME a => a) ∧
  apply_subst_noquote q bs (IntLit i) = IntLit i ∧
  apply_subst_noquote q bs (StrLit s) = StrLit s ∧
  apply_subst_noquote q bs (Expr xs) =
    (case xs of
     | [Sym tag; body] =>
         if tag = q then Expr [Sym tag; body]
         else Expr (apply_subst_noquote_list q bs xs)
     | _ => Expr (apply_subst_noquote_list q bs xs)) ∧
  apply_subst_noquote_list q bs [] = [] ∧
  apply_subst_noquote_list q bs (x :: xs) =
    apply_subst_noquote q bs x :: apply_subst_noquote_list q bs xs
Termination
  WF_REL_TAC
    ‘measure (λx.
       case x of
       | INL (q,bs,a) => atom_depth a
       | INR (q,bs,xs) => atom_list_depth xs)’ \\
  rw[atom_depth_def] \\ DECIDE_TAC
End

Theorem apply_subst_noquote_top:
  ∀q bs body. apply_subst_noquote q bs (Expr [Sym q; body]) = Expr [Sym q; body]
Proof
  rw[apply_subst_noquote_def]
QED

Theorem apply_subst_noquote_var_hit:
  ∀q v a. apply_subst_noquote q [Bind v a] (Var v) = a
Proof
  rw[apply_subst_noquote_def, lookup_bind_def]
QED

Theorem apply_subst_noquote_nested_quote:
  ∀q v a body.
    apply_subst_noquote q [Bind v a] (Expr [Sym q; Expr [Var v; body]]) =
    Expr [Sym q; Expr [Var v; body]]
Proof
  rw[apply_subst_noquote_def]
QED
