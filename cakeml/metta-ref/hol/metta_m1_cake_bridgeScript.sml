Theory metta_m1_cake_bridge
Ancestors
  metta_m1 ml_translator mlstring basisProg[qualified] fromSexp[qualified]
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib astToSexprLib

val _ = translation_extends "basisProg";
val _ = hide_environments true;
val _ = Globals.max_print_depth := 20;
val bridge_mlstring_EQ_CONV =
  REWR_CONV mlstringTheory.mlstring_11 THENC stringLib.string_EQ_CONV;

Definition bridge_add_int_def:
  bridge_add_int (x:int) (y:int) = x + y
End

Definition bridge_add_atom_result_def:
  bridge_add_atom_result x y = [metta_m1$IntLit (bridge_add_int x y)]
End

Definition bridge_symbol_table_def:
  bridge_symbol_table =
    [(0:num, strlit"Error");
     (1, strlit"Empty");
     (2, strlit"=");
     (3, strlit"StackOverflow");
     (4, strlit"match");
     (5, strlit"&self");
     (6, strlit"let");
     (7, strlit"if");
     (8, strlit"True");
     (9, strlit"False");
     (10, strlit"BadArgType");
     (11, strlit"+");
     (12, strlit"<");
     (13, strlit"unify");
     (14, strlit"decons-atom");
     (15, strlit"cons-atom");
     (16, strlit"collapse");
     (17, strlit"superpose");
     (18, strlit"function");
     (19, strlit"return");
     (20, strlit"eval");
     (21, strlit"chain");
     (22, strlit"NoReturn");
     (23, strlit"NotReducible");
     (28, strlit"call-ml");
     (29, strlit"call-native");
     (30, strlit"inc");
     (31, strlit"and");
     (32, strlit"or");
     (33, strlit"not");
     (34, strlit":");
     (36, strlit"Nat");
     (37, strlit"->");
     (38, strlit"Add");
     (39, strlit"%Undefined%");
     (40, strlit"Number");
     (41, strlit"Expression");
     (42, strlit"String");
     (43, strlit"Variable");
     (44, strlit"Atom");
     (45, strlit"*");
     (46, strlit"-");
     (47, strlit"==");
     (49, strlit"Vec");
     (50, strlit"Person");
     (51, strlit"S");
     (52, strlit"Nil");
     (53, strlit"Z");
     (54, strlit"case");
     (55, strlit"switch");
     (56, strlit"let*");
     (57, strlit"evalc-type");
     (58, strlit"VecConsType");
     (59, strlit"dec");
     (60, strlit"echo");
     (61, strlit"evalc")]
End

Definition bridge_symbol_name_def:
  bridge_symbol_name (n:num) = ALOOKUP bridge_symbol_table n
End

Definition bridge_symbol_intern_def:
  bridge_symbol_intern (s:mlstring) =
    ALOOKUP (MAP (λ(n,s). (s,n)) bridge_symbol_table) s
End

Theorem bridge_symbol_table_code_distinct:
  ALL_DISTINCT (MAP FST bridge_symbol_table)
Proof
  EVAL_TAC \\
  rw[]
QED

Theorem bridge_symbol_table_name_distinct:
  ALL_DISTINCT (MAP SND bridge_symbol_table)
Proof
  rw[bridge_symbol_table_def] \\
  CONV_TAC (DEPTH_CONV bridge_mlstring_EQ_CONV) \\
  EVAL_TAC
QED

Theorem bridge_symbol_intern_table_distinct:
  ALL_DISTINCT (MAP FST (MAP (λ(n,s). (s,n)) bridge_symbol_table))
Proof
  rw[bridge_symbol_table_def] \\
  CONV_TAC (DEPTH_CONV bridge_mlstring_EQ_CONV) \\
  EVAL_TAC
QED

Theorem bridge_symbol_intern_name_roundtrip:
  ∀n s.
    bridge_symbol_name n = SOME s ⇒
    bridge_symbol_intern s = SOME n
Proof
  rw[bridge_symbol_name_def, bridge_symbol_intern_def] \\
  drule ALOOKUP_MEM \\ rw[] \\
  irule ALOOKUP_ALL_DISTINCT_MEM \\
  rw[bridge_symbol_intern_table_distinct, MEM_MAP, EXISTS_PROD] \\
  metis_tac[]
QED

Theorem bridge_symbol_name_intern_roundtrip:
  ∀s n.
    bridge_symbol_intern s = SOME n ⇒
    bridge_symbol_name n = SOME s
Proof
  rw[bridge_symbol_name_def, bridge_symbol_intern_def] \\
  drule ALOOKUP_MEM \\
  rw[MEM_MAP, EXISTS_PROD] \\
  irule ALOOKUP_ALL_DISTINCT_MEM \\
  rw[bridge_symbol_table_code_distinct]
QED

Theorem bridge_symbol_code_functional:
  ∀n s1 s2.
    bridge_symbol_name n = SOME s1 ∧
    bridge_symbol_name n = SOME s2 ⇒
    s1 = s2
Proof
  rw[bridge_symbol_name_def] \\
  metis_tac[optionTheory.SOME_11]
QED

Theorem bridge_symbol_name_injective:
  ∀n1 n2 s.
    bridge_symbol_name n1 = SOME s ∧
    bridge_symbol_name n2 = SOME s ⇒
    n1 = n2
Proof
  metis_tac[bridge_symbol_intern_name_roundtrip, optionTheory.SOME_11]
QED

Theorem bridge_symbol_intern_functional:
  ∀s n1 n2.
    bridge_symbol_intern s = SOME n1 ∧
    bridge_symbol_intern s = SOME n2 ⇒
    n1 = n2
Proof
  rw[bridge_symbol_intern_def] \\
  metis_tac[optionTheory.SOME_11]
QED

Theorem bridge_symbol_plus_positive_example:
  bridge_symbol_name 11 = SOME (strlit"+") ∧
  bridge_symbol_intern (strlit"+") = SOME 11
Proof
  EVAL_TAC \\
  rw[]
QED

Theorem bridge_symbol_return_positive_example:
  bridge_symbol_name 19 = SOME (strlit"return") ∧
  bridge_symbol_intern (strlit"return") = SOME 19
Proof
  EVAL_TAC
QED

Theorem bridge_symbol_unknown_negative_example:
  bridge_symbol_name 999 = NONE ∧
  bridge_symbol_intern (strlit"not-a-core-symbol") = NONE
Proof
  rw[bridge_symbol_name_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  CONV_TAC (DEPTH_CONV bridge_mlstring_EQ_CONV) \\
  EVAL_TAC
QED

Theorem bridge_symbol_intern_return_iff:
  ∀s. bridge_symbol_intern s = SOME 19 ⇔ s = strlit"return"
Proof
  rw[EQ_IMP_THM]
  >- (
    drule bridge_symbol_name_intern_roundtrip \\
    rw[bridge_symbol_name_def, bridge_symbol_table_def] \\
    CONV_TAC (DEPTH_CONV bridge_mlstring_EQ_CONV) \\
    gvs[])
  >- EVAL_TAC
QED

Datatype:
  bridge_surface_atom =
    BSym mlstring
  | BVar num
  | BInt int
  | BStr num
  | BExpr (bridge_surface_atom list)
End

Definition bridge_import_surface_atom_def:
  bridge_import_surface_atom (BSym s) =
    (case bridge_symbol_intern s of
     | SOME n => SOME (metta_m1$Sym n)
     | NONE => NONE) ∧
  bridge_import_surface_atom (BVar v) = SOME (metta_m1$Var v) ∧
  bridge_import_surface_atom (BInt i) = SOME (metta_m1$IntLit i) ∧
  bridge_import_surface_atom (BStr s) = SOME (metta_m1$StrLit s) ∧
  bridge_import_surface_atom (BExpr xs) =
    (case bridge_import_surface_atom_list xs of
     | SOME ys => SOME (metta_m1$Expr ys)
     | NONE => NONE) ∧
  bridge_import_surface_atom_list [] = SOME [] ∧
  bridge_import_surface_atom_list (x :: xs) =
    (case bridge_import_surface_atom x of
     | SOME y =>
         (case bridge_import_surface_atom_list xs of
          | SOME ys => SOME (y :: ys)
          | NONE => NONE)
     | NONE => NONE)
End

Definition bridge_export_surface_atom_def:
  bridge_export_surface_atom (metta_m1$Sym n) =
    (case bridge_symbol_name n of
     | SOME s => SOME (BSym s)
     | NONE => NONE) ∧
  bridge_export_surface_atom (metta_m1$Var v) = SOME (BVar v) ∧
  bridge_export_surface_atom (metta_m1$IntLit i) = SOME (BInt i) ∧
  bridge_export_surface_atom (metta_m1$StrLit s) = SOME (BStr s) ∧
  bridge_export_surface_atom (metta_m1$Expr xs) =
    (case bridge_export_surface_atom_list xs of
     | SOME ys => SOME (BExpr ys)
     | NONE => NONE) ∧
  bridge_export_surface_atom_list [] = SOME [] ∧
  bridge_export_surface_atom_list (x :: xs) =
    (case bridge_export_surface_atom x of
     | SOME y =>
         (case bridge_export_surface_atom_list xs of
          | SOME ys => SOME (y :: ys)
          | NONE => NONE)
     | NONE => NONE)
End

Theorem bridge_import_known_symbol_example:
  bridge_import_surface_atom (BSym (strlit"+")) =
  SOME (metta_m1$Sym 11)
Proof
  EVAL_TAC
QED

Theorem bridge_import_unknown_symbol_example:
  bridge_import_surface_atom (BSym (strlit"not-a-core-symbol")) = NONE
Proof
  EVAL_TAC
QED

Definition bridge_dynamic_code_def:
  bridge_dynamic_code (n:num) ⇔ 1000 ≤ n
End

Definition bridge_dyn_env_ok_def:
  bridge_dyn_env_ok env ⇔
    ALL_DISTINCT (MAP FST env) ∧
    ALL_DISTINCT (MAP SND env) ∧
    EVERY
      (λ(s,n).
         bridge_symbol_intern s = NONE ∧
         bridge_symbol_name n = NONE ∧
         bridge_dynamic_code n)
      env
End

Definition bridge_dyn_symbol_intern_def:
  bridge_dyn_symbol_intern env (s:mlstring) = ALOOKUP env s
End

Definition bridge_dyn_symbol_name_def:
  bridge_dyn_symbol_name env (n:num) =
    ALOOKUP (MAP (λ(s,n). (n,s)) env) n
End

Definition bridge_import_symbol_with_env_def:
  bridge_import_symbol_with_env env s =
    case bridge_symbol_intern s of
    | SOME n => SOME n
    | NONE => bridge_dyn_symbol_intern env s
End

Definition bridge_export_symbol_with_env_def:
  bridge_export_symbol_with_env env n =
    case bridge_symbol_name n of
    | SOME s => SOME s
    | NONE => bridge_dyn_symbol_name env n
End

Theorem bridge_dyn_env_empty_ok:
  bridge_dyn_env_ok []
Proof
  EVAL_TAC
QED

Theorem bridge_dyn_symbol_positive_example:
  bridge_dyn_env_ok [(strlit"Foo", 1000)] ∧
  bridge_import_symbol_with_env [(strlit"Foo", 1000)] (strlit"Foo") =
    SOME 1000 ∧
  bridge_export_symbol_with_env [(strlit"Foo", 1000)] 1000 =
    SOME (strlit"Foo") ∧
  bridge_import_symbol_with_env [(strlit"Foo", 1000)] (strlit"+") =
    SOME 11 ∧
  bridge_export_symbol_with_env [(strlit"Foo", 1000)] 11 =
    SOME (strlit"+")
Proof
  rw[bridge_dyn_env_ok_def, bridge_dynamic_code_def,
     bridge_import_symbol_with_env_def, bridge_export_symbol_with_env_def,
     bridge_dyn_symbol_intern_def, bridge_dyn_symbol_name_def,
     bridge_symbol_name_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  CONV_TAC (DEPTH_CONV bridge_mlstring_EQ_CONV) \\
  EVAL_TAC
QED

Theorem bridge_dyn_symbol_negative_example:
  bridge_import_symbol_with_env [] (strlit"Foo") = NONE ∧
  bridge_export_symbol_with_env [] 1000 = NONE
Proof
  EVAL_TAC
QED

Theorem bridge_dyn_swap_fst_map:
  ∀env.
    MAP FST (MAP (λ(s,n). (n,s)) env) = MAP SND env
Proof
  Induct \\ rw[] \\
  Cases_on ‘h’ \\ rw[]
QED

Theorem bridge_dyn_symbol_name_table_distinct:
  ∀env.
    bridge_dyn_env_ok env ⇒
    ALL_DISTINCT (MAP FST (MAP (λ(s,n). (n,s)) env))
Proof
  rw[bridge_dyn_env_ok_def, bridge_dyn_swap_fst_map]
QED

Theorem bridge_dyn_symbol_intern_name_roundtrip:
  ∀env s n.
    bridge_dyn_env_ok env ∧
    bridge_dyn_symbol_intern env s = SOME n ⇒
    bridge_dyn_symbol_name env n = SOME s
Proof
  rw[bridge_dyn_symbol_intern_def, bridge_dyn_symbol_name_def] \\
  drule ALOOKUP_MEM \\ rw[] \\
  irule ALOOKUP_ALL_DISTINCT_MEM \\
  rw[bridge_dyn_symbol_name_table_distinct, MEM_MAP, EXISTS_PROD] \\
  metis_tac[]
QED

Theorem bridge_dyn_symbol_name_intern_roundtrip:
  ∀env n s.
    bridge_dyn_env_ok env ∧
    bridge_dyn_symbol_name env n = SOME s ⇒
    bridge_dyn_symbol_intern env s = SOME n
Proof
  rw[bridge_dyn_symbol_name_def, bridge_dyn_symbol_intern_def] \\
  drule ALOOKUP_MEM \\
  rw[MEM_MAP, EXISTS_PROD] \\
  irule ALOOKUP_ALL_DISTINCT_MEM \\
  gvs[bridge_dyn_env_ok_def]
QED

Theorem bridge_dyn_symbol_intern_reserved_name_none:
  ∀env s n.
    bridge_dyn_env_ok env ∧
    bridge_dyn_symbol_intern env s = SOME n ⇒
    bridge_symbol_name n = NONE
Proof
  rw[bridge_dyn_symbol_intern_def] \\
  drule ALOOKUP_MEM \\
  rw[] \\
  fs[bridge_dyn_env_ok_def, EVERY_MEM, FORALL_PROD] \\
  metis_tac[]
QED

Theorem bridge_dyn_symbol_name_reserved_intern_none:
  ∀env n s.
    bridge_dyn_env_ok env ∧
    bridge_dyn_symbol_name env n = SOME s ⇒
    bridge_symbol_intern s = NONE
Proof
  rw[bridge_dyn_symbol_name_def] \\
  drule ALOOKUP_MEM \\
  rw[MEM_MAP, EXISTS_PROD] \\
  fs[bridge_dyn_env_ok_def, EVERY_MEM, FORALL_PROD] \\
  metis_tac[]
QED

Theorem bridge_dyn_symbol_intern_injective:
  ∀env s1 s2 n.
    bridge_dyn_env_ok env ∧
    bridge_dyn_symbol_intern env s1 = SOME n ∧
    bridge_dyn_symbol_intern env s2 = SOME n ⇒
    s1 = s2
Proof
  metis_tac[bridge_dyn_symbol_intern_name_roundtrip,
            optionTheory.SOME_11]
QED

Theorem bridge_dyn_symbol_name_injective:
  ∀env n1 n2 s.
    bridge_dyn_env_ok env ∧
    bridge_dyn_symbol_name env n1 = SOME s ∧
    bridge_dyn_symbol_name env n2 = SOME s ⇒
    n1 = n2
Proof
  metis_tac[bridge_dyn_symbol_name_intern_roundtrip,
            optionTheory.SOME_11]
QED

Theorem bridge_import_export_symbol_with_env_roundtrip:
  ∀env s n.
    bridge_dyn_env_ok env ∧
    bridge_import_symbol_with_env env s = SOME n ⇒
    bridge_export_symbol_with_env env n = SOME s
Proof
  rw[bridge_import_symbol_with_env_def,
     bridge_export_symbol_with_env_def] \\
  gvs[AllCaseEqs()] \\
  metis_tac[bridge_symbol_name_intern_roundtrip,
            bridge_dyn_symbol_intern_name_roundtrip,
            bridge_dyn_symbol_intern_reserved_name_none]
QED

Theorem bridge_export_import_symbol_with_env_roundtrip:
  ∀env n s.
    bridge_dyn_env_ok env ∧
    bridge_export_symbol_with_env env n = SOME s ⇒
    bridge_import_symbol_with_env env s = SOME n
Proof
  rw[bridge_import_symbol_with_env_def,
     bridge_export_symbol_with_env_def] \\
  gvs[AllCaseEqs()] \\
  metis_tac[bridge_symbol_intern_name_roundtrip,
            bridge_dyn_symbol_name_intern_roundtrip,
            bridge_dyn_symbol_name_reserved_intern_none]
QED

Theorem bridge_import_symbol_with_env_return_iff:
  ∀env s.
    bridge_dyn_env_ok env ⇒
    (bridge_import_symbol_with_env env s = SOME 19 ⇔ s = strlit"return")
Proof
  rw[EQ_IMP_THM, bridge_import_symbol_with_env_def]
  >- (
    every_case_tac \\
    gvs[bridge_symbol_intern_return_iff] \\
    drule_all bridge_dyn_symbol_intern_reserved_name_none \\
    rw[bridge_symbol_name_def, bridge_symbol_table_def])
  >- EVAL_TAC
QED

Definition bridge_import_surface_atom_with_env_def:
  bridge_import_surface_atom_with_env env (BSym s) =
    (case bridge_import_symbol_with_env env s of
     | SOME n => SOME (metta_m1$Sym n)
     | NONE => NONE) ∧
  bridge_import_surface_atom_with_env env (BVar v) = SOME (metta_m1$Var v) ∧
  bridge_import_surface_atom_with_env env (BInt i) = SOME (metta_m1$IntLit i) ∧
  bridge_import_surface_atom_with_env env (BStr s) = SOME (metta_m1$StrLit s) ∧
  bridge_import_surface_atom_with_env env (BExpr xs) =
    (case bridge_import_surface_atom_list_with_env env xs of
     | SOME ys => SOME (metta_m1$Expr ys)
     | NONE => NONE) ∧
  bridge_import_surface_atom_list_with_env env [] = SOME [] ∧
  bridge_import_surface_atom_list_with_env env (x :: xs) =
    (case bridge_import_surface_atom_with_env env x of
     | SOME y =>
         (case bridge_import_surface_atom_list_with_env env xs of
          | SOME ys => SOME (y :: ys)
          | NONE => NONE)
     | NONE => NONE)
End

Definition bridge_export_surface_atom_with_env_def:
  bridge_export_surface_atom_with_env env (metta_m1$Sym n) =
    (case bridge_export_symbol_with_env env n of
     | SOME s => SOME (BSym s)
     | NONE => NONE) ∧
  bridge_export_surface_atom_with_env env (metta_m1$Var v) = SOME (BVar v) ∧
  bridge_export_surface_atom_with_env env (metta_m1$IntLit i) = SOME (BInt i) ∧
  bridge_export_surface_atom_with_env env (metta_m1$StrLit s) = SOME (BStr s) ∧
  bridge_export_surface_atom_with_env env (metta_m1$Expr xs) =
    (case bridge_export_surface_atom_list_with_env env xs of
     | SOME ys => SOME (BExpr ys)
     | NONE => NONE) ∧
  bridge_export_surface_atom_list_with_env env [] = SOME [] ∧
  bridge_export_surface_atom_list_with_env env (x :: xs) =
    (case bridge_export_surface_atom_with_env env x of
     | SOME y =>
         (case bridge_export_surface_atom_list_with_env env xs of
          | SOME ys => SOME (y :: ys)
          | NONE => NONE)
     | NONE => NONE)
End

Theorem bridge_import_surface_atom_with_env_reserved_example:
  bridge_import_surface_atom_with_env [(strlit"Foo", 1000)] (BSym (strlit"+")) =
  SOME (metta_m1$Sym 11)
Proof
  EVAL_TAC
QED

Theorem bridge_import_surface_atom_with_env_dynamic_example:
  bridge_import_surface_atom_with_env [(strlit"Foo", 1000)] (BSym (strlit"Foo")) =
  SOME (metta_m1$Sym 1000)
Proof
  EVAL_TAC
QED

Theorem bridge_import_surface_atom_with_env_unknown_example:
  bridge_import_surface_atom_with_env [] (BSym (strlit"Foo")) = NONE
Proof
  EVAL_TAC
QED

Theorem bridge_import_surface_with_env_export_roundtrip:
  ∀env.
    bridge_dyn_env_ok env ⇒
    (∀sa a.
       bridge_import_surface_atom_with_env env sa = SOME a ⇒
       bridge_export_surface_atom_with_env env a = SOME sa) ∧
    (∀sas atoms.
       bridge_import_surface_atom_list_with_env env sas = SOME atoms ⇒
       bridge_export_surface_atom_list_with_env env atoms = SOME sas)
Proof
  ntac 2 strip_tac \\
  irule (CONV_RULE (DEPTH_CONV BETA_CONV) (Q.SPECL
    [‘λsa.
        ∀a.
          bridge_import_surface_atom_with_env env sa = SOME a ⇒
          bridge_export_surface_atom_with_env env a = SOME sa’,
     ‘λsas.
        ∀atoms.
          bridge_import_surface_atom_list_with_env env sas = SOME atoms ⇒
          bridge_export_surface_atom_list_with_env env atoms = SOME sas’]
    (fetch "-" "bridge_surface_atom_induction"))) \\
  rw[bridge_import_surface_atom_with_env_def,
     bridge_export_surface_atom_with_env_def] \\
  gvs[AllCaseEqs(), bridge_export_surface_atom_with_env_def] \\
  metis_tac[bridge_import_export_symbol_with_env_roundtrip]
QED

Theorem bridge_import_surface_atom_with_env_export_roundtrip:
  ∀env sa a.
    bridge_dyn_env_ok env ∧
    bridge_import_surface_atom_with_env env sa = SOME a ⇒
    bridge_export_surface_atom_with_env env a = SOME sa
Proof
  metis_tac[bridge_import_surface_with_env_export_roundtrip]
QED

Theorem bridge_import_surface_atom_list_with_env_export_roundtrip:
  ∀env sas atoms.
    bridge_dyn_env_ok env ∧
    bridge_import_surface_atom_list_with_env env sas = SOME atoms ⇒
    bridge_export_surface_atom_list_with_env env atoms = SOME sas
Proof
  metis_tac[bridge_import_surface_with_env_export_roundtrip]
QED

Theorem bridge_export_surface_with_env_import_roundtrip:
  ∀env.
    bridge_dyn_env_ok env ⇒
    (∀a sa.
       bridge_export_surface_atom_with_env env a = SOME sa ⇒
       bridge_import_surface_atom_with_env env sa = SOME a) ∧
    (∀atoms sas.
       bridge_export_surface_atom_list_with_env env atoms = SOME sas ⇒
       bridge_import_surface_atom_list_with_env env sas = SOME atoms)
Proof
  ntac 2 strip_tac \\
  irule (CONV_RULE (DEPTH_CONV BETA_CONV) (Q.SPECL
    [‘λa.
        ∀sa.
          bridge_export_surface_atom_with_env env a = SOME sa ⇒
          bridge_import_surface_atom_with_env env sa = SOME a’,
     ‘λatoms.
        ∀sas.
          bridge_export_surface_atom_list_with_env env atoms = SOME sas ⇒
          bridge_import_surface_atom_list_with_env env sas = SOME atoms’]
    (fetch "metta_m1" "atom_induction"))) \\
  rw[bridge_import_surface_atom_with_env_def,
     bridge_export_surface_atom_with_env_def] \\
  gvs[AllCaseEqs(), bridge_import_surface_atom_with_env_def] \\
  metis_tac[bridge_export_import_symbol_with_env_roundtrip]
QED

Theorem bridge_export_surface_atom_with_env_import_roundtrip:
  ∀env a sa.
    bridge_dyn_env_ok env ∧
    bridge_export_surface_atom_with_env env a = SOME sa ⇒
    bridge_import_surface_atom_with_env env sa = SOME a
Proof
  metis_tac[bridge_export_surface_with_env_import_roundtrip]
QED

Theorem bridge_export_surface_atom_list_with_env_import_roundtrip:
  ∀env atoms sas.
    bridge_dyn_env_ok env ∧
    bridge_export_surface_atom_list_with_env env atoms = SOME sas ⇒
    bridge_import_surface_atom_list_with_env env sas = SOME atoms
Proof
  metis_tac[bridge_export_surface_with_env_import_roundtrip]
QED

Datatype:
  bridge_token =
    BTokLParen
  | BTokRParen
  | BTokBang
  | BTokAtom bridge_surface_atom
End

Definition bridge_parse_atom_token_def:
  bridge_parse_atom_token (BTokAtom atom :: rest) = SOME (atom, rest) ∧
  bridge_parse_atom_token _ = NONE
End

Definition bridge_token_is_atom_def:
  bridge_token_is_atom (BTokAtom atom) = T ∧
  bridge_token_is_atom BTokLParen = F ∧
  bridge_token_is_atom BTokRParen = F ∧
  bridge_token_is_atom BTokBang = F
End

Theorem bridge_token_is_atom_parse_singleton:
  ∀tok.
    bridge_token_is_atom tok ⇔
    ∃atom. bridge_parse_atom_token [tok] = SOME (atom, [])
Proof
  Cases \\ rw[bridge_token_is_atom_def, bridge_parse_atom_token_def]
QED

Theorem bridge_token_is_atom_positive_example:
  bridge_token_is_atom (BTokAtom (BSym (strlit"return")))
Proof
  EVAL_TAC
QED

Theorem bridge_token_is_atom_negative_example:
  ¬bridge_token_is_atom BTokLParen ∧
  ¬bridge_token_is_atom BTokRParen ∧
  ¬bridge_token_is_atom BTokBang
Proof
  EVAL_TAC
QED

Datatype:
  bridge_atom_token_parse_result =
    BAtomTokenParsed bridge_surface_atom (bridge_token list)
  | BAtomTokenParseError num
End

Definition bridge_parse_atom_token_result_def:
  bridge_parse_atom_token_result (BTokAtom atom :: rest) =
    BAtomTokenParsed atom rest ∧
  bridge_parse_atom_token_result [] = BAtomTokenParseError 0 ∧
  bridge_parse_atom_token_result (BTokLParen :: rest) =
    BAtomTokenParseError 1 ∧
  bridge_parse_atom_token_result (BTokRParen :: rest) =
    BAtomTokenParseError 2 ∧
  bridge_parse_atom_token_result (BTokBang :: rest) =
    BAtomTokenParseError 3
End

Theorem bridge_parse_atom_token_result_success:
  ∀toks atom rest.
    bridge_parse_atom_token_result toks = BAtomTokenParsed atom rest ⇔
    bridge_parse_atom_token toks = SOME (atom, rest)
Proof
  Cases \\ rw[bridge_parse_atom_token_result_def,
              bridge_parse_atom_token_def] \\
  Cases_on ‘h’ \\
  rw[bridge_parse_atom_token_result_def,
     bridge_parse_atom_token_def]
QED

Theorem bridge_parse_atom_token_result_positive_example:
  bridge_parse_atom_token_result
    [BTokAtom (BSym (strlit"return"))] =
  BAtomTokenParsed (BSym (strlit"return")) []
Proof
  EVAL_TAC
QED

Theorem bridge_parse_atom_token_result_negative_example:
  bridge_parse_atom_token_result [] = BAtomTokenParseError 0 ∧
  bridge_parse_atom_token_result [BTokLParen] = BAtomTokenParseError 1 ∧
  bridge_parse_atom_token_result [BTokRParen] = BAtomTokenParseError 2 ∧
  bridge_parse_atom_token_result [BTokBang] = BAtomTokenParseError 3
Proof
  EVAL_TAC
QED

Definition bridge_import_parsed_atom_token_def:
  bridge_import_parsed_atom_token toks =
    case bridge_parse_atom_token toks of
    | SOME (atom, rest) =>
        (case bridge_import_surface_atom atom of
         | SOME imported => SOME (imported, rest)
         | NONE => NONE)
    | NONE => NONE
End

Definition bridge_import_parsed_atom_token_with_env_def:
  bridge_import_parsed_atom_token_with_env env toks =
    case bridge_parse_atom_token toks of
    | SOME (atom, rest) =>
        (case bridge_import_surface_atom_with_env env atom of
         | SOME imported => SOME (imported, rest)
         | NONE => NONE)
    | NONE => NONE
End

Theorem bridge_import_parsed_atom_token_plus_example:
  bridge_import_parsed_atom_token [BTokAtom (BSym (strlit"+"))] =
  SOME (metta_m1$Sym 11, [])
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_atom_token_dynamic_example:
  bridge_import_parsed_atom_token_with_env [(strlit"Foo", 1000)]
    [BTokAtom (BSym (strlit"Foo"))] =
  SOME (metta_m1$Sym 1000, [])
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_atom_token_negative_example:
  bridge_import_parsed_atom_token [BTokAtom (BSym (strlit"not-a-core-symbol"))] =
    NONE ∧
  bridge_import_parsed_atom_token [BTokLParen] = NONE
Proof
  EVAL_TAC
QED

Datatype:
  bridge_full_atom_parse_result =
    BFullAtomParsed bridge_surface_atom (bridge_token list)
  | BFullAtomParseError num
End

Definition bridge_parse_atom_tokens_fuel_def:
  bridge_parse_atom_tokens_fuel 0 toks = BFullAtomParseError 99 ∧
  bridge_parse_atom_tokens_fuel (SUC fuel) toks =
    (case toks of
     | BTokAtom atom :: rest => BFullAtomParsed atom rest
     | BTokLParen :: rest => bridge_parse_expr_items_fuel fuel [] rest
     | BTokRParen :: rest => BFullAtomParseError 1
     | BTokBang :: rest => BFullAtomParseError 2
     | [] => BFullAtomParseError 3) ∧
  bridge_parse_expr_items_fuel 0 items toks = BFullAtomParseError 99 ∧
  bridge_parse_expr_items_fuel (SUC fuel) items toks =
    (case toks of
     | BTokRParen :: rest => BFullAtomParsed (BExpr items) rest
     | [] => BFullAtomParseError 4
     | _ =>
        (case bridge_parse_atom_tokens_fuel fuel toks of
         | BFullAtomParsed atom rest =>
             bridge_parse_expr_items_fuel fuel (items ++ [atom]) rest
         | BFullAtomParseError n => BFullAtomParseError n))
Termination
  WF_REL_TAC
    ‘measure
       (λx. case x of
        | INL (fuel,toks) => fuel
        | INR (fuel,items,toks) => fuel)’ \\
  rw[]
End

Definition bridge_import_parsed_atom_tokens_with_env_def:
  bridge_import_parsed_atom_tokens_with_env env fuel toks =
    case bridge_parse_atom_tokens_fuel fuel toks of
    | BFullAtomParsed atom rest =>
        (case bridge_import_surface_atom_with_env env atom of
         | SOME imported => SOME (imported, rest)
         | NONE => NONE)
    | BFullAtomParseError n => NONE
End

Definition bridge_import_parsed_atom_tokens_def:
  bridge_import_parsed_atom_tokens fuel toks =
    bridge_import_parsed_atom_tokens_with_env [] fuel toks
End

Datatype:
  bridge_imported_atom_parse_result =
    BImportedAtomParsed metta_m1$atom (bridge_token list)
  | BImportedAtomParseError num
  | BImportedAtomImportError
End

Definition bridge_import_parsed_atom_tokens_result_with_env_def:
  bridge_import_parsed_atom_tokens_result_with_env env fuel toks =
    case bridge_parse_atom_tokens_fuel fuel toks of
    | BFullAtomParsed surface rest =>
        (case bridge_import_surface_atom_with_env env surface of
         | SOME imported => BImportedAtomParsed imported rest
         | NONE => BImportedAtomImportError)
    | BFullAtomParseError n => BImportedAtomParseError n
End

Theorem bridge_import_parsed_atom_tokens_result_with_env_success:
  ∀env fuel toks atom rest.
    bridge_import_parsed_atom_tokens_result_with_env env fuel toks =
      BImportedAtomParsed atom rest ⇔
    bridge_import_parsed_atom_tokens_with_env env fuel toks =
      SOME (atom, rest)
Proof
  rw[bridge_import_parsed_atom_tokens_result_with_env_def,
     bridge_import_parsed_atom_tokens_with_env_def] \\
  every_case_tac \\
  rw[]
QED

Theorem bridge_import_parsed_atom_tokens_result_with_env_positive_example:
  bridge_import_parsed_atom_tokens_result_with_env
    [(strlit"Foo", 1000)] 10 [BTokAtom (BSym (strlit"Foo"))] =
  BImportedAtomParsed (metta_m1$Sym 1000) []
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_atom_tokens_result_with_env_negative_example:
  bridge_import_parsed_atom_tokens_result_with_env
    [] 10 [BTokAtom (BSym (strlit"Foo"))] =
  BImportedAtomImportError ∧
  bridge_import_parsed_atom_tokens_result_with_env [] 10 [] =
  BImportedAtomParseError 3
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_atom_tokens_with_env_sound:
  ∀env fuel toks imported rest.
    bridge_import_parsed_atom_tokens_with_env env fuel toks =
      SOME (imported, rest) ⇒
    ∃surface.
      bridge_parse_atom_tokens_fuel fuel toks =
        BFullAtomParsed surface rest ∧
      bridge_import_surface_atom_with_env env surface = SOME imported
Proof
  rw[bridge_import_parsed_atom_tokens_with_env_def] \\
  gvs[AllCaseEqs()]
QED

Theorem bridge_import_parsed_atom_tokens_with_env_export_sound:
  ∀env fuel toks imported rest.
    bridge_dyn_env_ok env ∧
    bridge_import_parsed_atom_tokens_with_env env fuel toks =
      SOME (imported, rest) ⇒
    ∃surface.
      bridge_parse_atom_tokens_fuel fuel toks =
        BFullAtomParsed surface rest ∧
      bridge_export_surface_atom_with_env env imported = SOME surface
Proof
  rw[] \\
  drule bridge_import_parsed_atom_tokens_with_env_sound \\
  rw[] \\
  qexists_tac ‘surface’ \\
  rw[] \\
  metis_tac[bridge_import_surface_atom_with_env_export_roundtrip]
QED

Theorem bridge_parse_atom_tokens_full_expr_import_example:
  bridge_import_parsed_atom_tokens 10
    [BTokLParen;
     BTokAtom (BSym (strlit"+"));
     BTokAtom (BInt 1);
     BTokAtom (BInt 2);
     BTokRParen] =
  SOME
    (metta_m1$Expr [metta_m1$Sym 11;
                    metta_m1$IntLit 1;
                    metta_m1$IntLit 2],
     [])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_atom_tokens_nested_dynamic_import_example:
  bridge_import_parsed_atom_tokens_with_env [(strlit"Foo", 1000)] 20
    [BTokLParen;
     BTokAtom (BSym (strlit"Foo"));
     BTokLParen;
     BTokAtom (BSym (strlit"+"));
     BTokAtom (BInt 1);
     BTokAtom (BInt 2);
     BTokRParen;
     BTokRParen] =
  SOME
    (metta_m1$Expr
      [metta_m1$Sym 1000;
       metta_m1$Expr [metta_m1$Sym 11;
                      metta_m1$IntLit 1;
                      metta_m1$IntLit 2]],
     [])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_atom_tokens_unclosed_negative_example:
  bridge_import_parsed_atom_tokens 10
    [BTokLParen; BTokAtom (BSym (strlit"+"))] = NONE
Proof
  EVAL_TAC
QED

Theorem bridge_import_surface_export_roundtrip:
  (∀sa a.
     bridge_import_surface_atom sa = SOME a ⇒
     bridge_export_surface_atom a = SOME sa) ∧
  (∀sas atoms.
     bridge_import_surface_atom_list sas = SOME atoms ⇒
     bridge_export_surface_atom_list atoms = SOME sas)
Proof
  irule (CONV_RULE (DEPTH_CONV BETA_CONV) (Q.SPECL
    [‘λsa.
        ∀a.
          bridge_import_surface_atom sa = SOME a ⇒
          bridge_export_surface_atom a = SOME sa’,
     ‘λsas.
        ∀atoms.
          bridge_import_surface_atom_list sas = SOME atoms ⇒
          bridge_export_surface_atom_list atoms = SOME sas’]
    (fetch "-" "bridge_surface_atom_induction"))) \\
  rw[bridge_import_surface_atom_def,
    bridge_export_surface_atom_def] \\
  gvs[AllCaseEqs(), bridge_export_surface_atom_def] \\
  metis_tac[bridge_symbol_name_intern_roundtrip]
QED

Theorem bridge_import_surface_atom_export_roundtrip:
  ∀sa a.
    bridge_import_surface_atom sa = SOME a ⇒
    bridge_export_surface_atom a = SOME sa
Proof
  metis_tac[bridge_import_surface_export_roundtrip]
QED

Theorem bridge_import_surface_atom_list_export_roundtrip:
  ∀sas atoms.
    bridge_import_surface_atom_list sas = SOME atoms ⇒
    bridge_export_surface_atom_list atoms = SOME sas
Proof
  metis_tac[bridge_import_surface_export_roundtrip]
QED

Theorem bridge_export_surface_import_roundtrip_full:
  (∀a sa.
     bridge_export_surface_atom a = SOME sa ⇒
     bridge_import_surface_atom sa = SOME a) ∧
  (∀atoms sas.
     bridge_export_surface_atom_list atoms = SOME sas ⇒
     bridge_import_surface_atom_list sas = SOME atoms)
Proof
  irule (CONV_RULE (DEPTH_CONV BETA_CONV) (Q.SPECL
    [‘λa.
        ∀sa.
          bridge_export_surface_atom a = SOME sa ⇒
          bridge_import_surface_atom sa = SOME a’,
     ‘λatoms.
        ∀sas.
          bridge_export_surface_atom_list atoms = SOME sas ⇒
          bridge_import_surface_atom_list sas = SOME atoms’]
    (fetch "metta_m1" "atom_induction"))) \\
  rw[bridge_import_surface_atom_def,
    bridge_export_surface_atom_def] \\
  gvs[AllCaseEqs(), bridge_import_surface_atom_def] \\
  metis_tac[bridge_symbol_intern_name_roundtrip]
QED

Theorem bridge_export_surface_import_roundtrip:
  ∀a sa.
    bridge_export_surface_atom a = SOME sa ⇒
    bridge_import_surface_atom sa = SOME a
Proof
  metis_tac[bridge_export_surface_import_roundtrip_full]
QED

Theorem bridge_export_surface_atom_list_import_roundtrip:
  ∀atoms sas.
    bridge_export_surface_atom_list atoms = SOME sas ⇒
    bridge_import_surface_atom_list sas = SOME atoms
Proof
  metis_tac[bridge_export_surface_import_roundtrip_full]
QED

Definition bridge_surface_is_return_symbol_def:
  bridge_surface_is_return_symbol s ⇔ s = strlit"return"
End

Definition bridge_surface_eval_return_fragment_core_def:
  bridge_surface_eval_return_fragment_core atom =
    case atom of
    | BExpr [BSym s; value] =>
        if bridge_surface_is_return_symbol s then
          [BExpr [BSym (strlit"return"); value]]
        else [atom]
    | _ => [atom]
End

Theorem bridge_surface_eval_return_fragment_core_import_expr:
  ∀xs ys.
    bridge_import_surface_atom_list xs = SOME ys ⇒
    bridge_import_surface_atom_list
      (bridge_surface_eval_return_fragment_core (BExpr xs)) =
    SOME (eval_return_fragment (metta_m1$Expr ys))
Proof
  rw[bridge_surface_eval_return_fragment_core_def,
     bridge_surface_is_return_symbol_def,
     bridge_import_surface_atom_def, eval_return_fragment_def] \\
  every_case_tac \\
  gvs[bridge_surface_eval_return_fragment_core_def,
      bridge_surface_is_return_symbol_def,
      bridge_import_surface_atom_def, eval_return_fragment_def,
      bridge_symbol_intern_return_iff]
QED

Theorem bridge_surface_eval_return_fragment_core_import:
  ∀surface atom.
    bridge_import_surface_atom surface = SOME atom ⇒
    bridge_import_surface_atom_list
      (bridge_surface_eval_return_fragment_core surface) =
    SOME (eval_return_fragment atom)
Proof
  Cases_on ‘surface’
  >- (rw[bridge_surface_eval_return_fragment_core_def,
         bridge_import_surface_atom_def, eval_return_fragment_def] \\
      gvs[AllCaseEqs()])
  >- (rw[bridge_surface_eval_return_fragment_core_def,
         bridge_import_surface_atom_def, eval_return_fragment_def] \\
      gvs[AllCaseEqs()])
  >- (rw[bridge_surface_eval_return_fragment_core_def,
         bridge_import_surface_atom_def, eval_return_fragment_def] \\
      gvs[AllCaseEqs()])
  >- (rw[bridge_surface_eval_return_fragment_core_def,
         bridge_import_surface_atom_def, eval_return_fragment_def] \\
      gvs[AllCaseEqs()]) \\
  rw[bridge_import_surface_atom_def] \\
  Cases_on ‘bridge_import_surface_atom_list l’ \\
  gvs[] \\
  qspecl_then [‘l’, ‘x’] mp_tac
    bridge_surface_eval_return_fragment_core_import_expr \\
  rw[]
QED

Theorem bridge_surface_eval_return_fragment_core_import_with_env_expr:
  ∀env xs ys.
    bridge_dyn_env_ok env ∧
    bridge_import_surface_atom_list_with_env env xs = SOME ys ⇒
    bridge_import_surface_atom_list_with_env env
      (bridge_surface_eval_return_fragment_core (BExpr xs)) =
    SOME (eval_return_fragment (metta_m1$Expr ys))
Proof
  rw[bridge_surface_eval_return_fragment_core_def,
     bridge_surface_is_return_symbol_def,
     bridge_import_surface_atom_with_env_def,
     eval_return_fragment_def] \\
  every_case_tac \\
  gvs[bridge_surface_eval_return_fragment_core_def,
      bridge_surface_is_return_symbol_def,
      bridge_import_surface_atom_with_env_def,
      eval_return_fragment_def,
      bridge_import_symbol_with_env_return_iff]
QED

Theorem bridge_surface_eval_return_fragment_core_import_with_env:
  ∀env surface atom.
    bridge_dyn_env_ok env ∧
    bridge_import_surface_atom_with_env env surface = SOME atom ⇒
    bridge_import_surface_atom_list_with_env env
      (bridge_surface_eval_return_fragment_core surface) =
    SOME (eval_return_fragment atom)
Proof
  Cases_on ‘surface’
  >- (rw[bridge_surface_eval_return_fragment_core_def,
         bridge_import_surface_atom_with_env_def, eval_return_fragment_def] \\
      gvs[AllCaseEqs()])
  >- (rw[bridge_surface_eval_return_fragment_core_def,
         bridge_import_surface_atom_with_env_def, eval_return_fragment_def] \\
      gvs[AllCaseEqs()])
  >- (rw[bridge_surface_eval_return_fragment_core_def,
         bridge_import_surface_atom_with_env_def, eval_return_fragment_def] \\
      gvs[AllCaseEqs()])
  >- (rw[bridge_surface_eval_return_fragment_core_def,
         bridge_import_surface_atom_with_env_def, eval_return_fragment_def] \\
      gvs[AllCaseEqs()]) \\
  rw[bridge_import_surface_atom_with_env_def] \\
  Cases_on ‘bridge_import_surface_atom_list_with_env env l’ \\
  gvs[] \\
  qspecl_then [‘env’, ‘l’, ‘x’] mp_tac
    bridge_surface_eval_return_fragment_core_import_with_env_expr \\
  rw[]
QED

Theorem bridge_surface_eval_return_fragment_core_positive_example:
  bridge_import_surface_atom_list
    (bridge_surface_eval_return_fragment_core
      (BExpr [BSym (strlit"return"); BInt 7])) =
  SOME
    (eval_return_fragment
      (metta_m1$Expr [metta_m1$Sym 19; metta_m1$IntLit 7]))
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_return_fragment_core_negative_example:
  bridge_import_surface_atom_list
    (bridge_surface_eval_return_fragment_core
      (BExpr [BSym (strlit"not-return"); BInt 7])) = NONE
Proof
  EVAL_TAC
QED

Datatype:
  bridge_source_atom =
    SrcSym mlstring
  | SrcVar mlstring
  | SrcInt int
  | SrcStr mlstring
  | SrcExpr (bridge_source_atom list)
End

Definition bridge_source_surface_rel_def:
  bridge_source_surface_rel var_env str_env (SrcSym s) (BSym t) =
    (s = t) ∧
  bridge_source_surface_rel var_env str_env (SrcVar v) (BVar n) =
    (ALOOKUP var_env v = SOME n) ∧
  bridge_source_surface_rel var_env str_env (SrcInt i) (BInt j) =
    (i = j) ∧
  bridge_source_surface_rel var_env str_env (SrcStr s) (BStr n) =
    (ALOOKUP str_env s = SOME n) ∧
  bridge_source_surface_rel var_env str_env (SrcExpr xs) (BExpr ys) =
    bridge_source_surface_rel_list var_env str_env xs ys ∧
  bridge_source_surface_rel var_env str_env _ _ = F ∧
  bridge_source_surface_rel_list var_env str_env [] [] = T ∧
  bridge_source_surface_rel_list var_env str_env (x :: xs) (y :: ys) =
    (bridge_source_surface_rel var_env str_env x y ∧
     bridge_source_surface_rel_list var_env str_env xs ys) ∧
  bridge_source_surface_rel_list var_env str_env _ _ = F
End

Definition bridge_source_eval_return_fragment_core_def:
  bridge_source_eval_return_fragment_core atom =
    case atom of
    | SrcExpr [SrcSym s; value] =>
        if s = strlit"return" then
          [SrcExpr [SrcSym (strlit"return"); value]]
        else [atom]
    | _ => [atom]
End

Theorem bridge_source_surface_rel_return_symbol:
  ∀var_env str_env s t.
    bridge_source_surface_rel var_env str_env (SrcSym s) (BSym t) ⇒
    (s = strlit"return" ⇔ bridge_surface_is_return_symbol t)
Proof
  rw[bridge_source_surface_rel_def,
     bridge_surface_is_return_symbol_def]
QED

Theorem bridge_source_eval_return_fragment_core_refines_surface_expr:
  ∀var_env str_env xs ys.
    bridge_source_surface_rel_list var_env str_env xs ys ⇒
    bridge_source_surface_rel_list var_env str_env
      (bridge_source_eval_return_fragment_core (SrcExpr xs))
      (bridge_surface_eval_return_fragment_core (BExpr ys))
Proof
  rw[bridge_source_eval_return_fragment_core_def,
     bridge_surface_eval_return_fragment_core_def,
     bridge_surface_is_return_symbol_def] \\
  every_case_tac \\
  gvs[bridge_source_eval_return_fragment_core_def,
      bridge_surface_eval_return_fragment_core_def,
      bridge_surface_is_return_symbol_def,
      bridge_source_surface_rel_def]
QED

Theorem bridge_source_eval_return_fragment_core_refines_surface:
  ∀var_env str_env source surface.
    bridge_source_surface_rel var_env str_env source surface ⇒
    bridge_source_surface_rel_list var_env str_env
      (bridge_source_eval_return_fragment_core source)
      (bridge_surface_eval_return_fragment_core surface)
Proof
  Cases_on ‘source’ \\
  Cases_on ‘surface’ \\
  rw[bridge_source_eval_return_fragment_core_def,
     bridge_surface_eval_return_fragment_core_def,
     bridge_surface_is_return_symbol_def,
     bridge_source_surface_rel_def] \\
  every_case_tac \\
  gvs[bridge_source_eval_return_fragment_core_def,
      bridge_surface_eval_return_fragment_core_def,
      bridge_surface_is_return_symbol_def,
      bridge_source_surface_rel_def]
QED

Theorem bridge_source_surface_rel_positive_example:
  bridge_source_surface_rel
    [(strlit"x", 0)] [(strlit"hello", 0)]
    (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")])
    (BExpr [BSym (strlit"return"); BVar 0])
Proof
  EVAL_TAC
QED

Theorem bridge_source_surface_rel_negative_example:
  ¬bridge_source_surface_rel [] []
    (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")])
    (BExpr [BSym (strlit"return"); BVar 0])
Proof
  EVAL_TAC
QED

Datatype:
  bridge_proto_atom =
    ProtoSym mlstring
  | ProtoVar mlstring
  | ProtoInt int
  | ProtoStr mlstring
  | ProtoExpr (bridge_proto_atom list)
End

Definition bridge_proto_source_rel_def:
  bridge_proto_source_rel (ProtoSym s) (SrcSym t) =
    (s = t) ∧
  bridge_proto_source_rel (ProtoVar v) (SrcVar w) =
    (v = w) ∧
  bridge_proto_source_rel (ProtoInt i) (SrcInt j) =
    (i = j) ∧
  bridge_proto_source_rel (ProtoStr s) (SrcStr t) =
    (s = t) ∧
  bridge_proto_source_rel (ProtoExpr xs) (SrcExpr ys) =
    bridge_proto_source_rel_list xs ys ∧
  bridge_proto_source_rel _ _ = F ∧
  bridge_proto_source_rel_list [] [] = T ∧
  bridge_proto_source_rel_list (x :: xs) (y :: ys) =
    (bridge_proto_source_rel x y ∧
     bridge_proto_source_rel_list xs ys) ∧
  bridge_proto_source_rel_list _ _ = F
End

Definition bridge_proto_eval_return_fragment_core_def:
  bridge_proto_eval_return_fragment_core atom =
    case atom of
    | ProtoExpr [ProtoSym s; value] =>
        if s = strlit"return" then
          [ProtoExpr [ProtoSym (strlit"return"); value]]
        else [atom]
    | _ => [atom]
End

Definition bridge_proto_is_return_head_def:
  bridge_proto_is_return_head atom ⇔
    case atom of
    | ProtoSym s => s = strlit"return"
    | _ => F
End

Definition bridge_proto_eval_return_items_factored_def:
  bridge_proto_eval_return_items_factored original [] = [original] ∧
  bridge_proto_eval_return_items_factored original (head :: rest) =
    (case rest of
     | [] => [original]
     | value :: rest2 =>
         (case rest2 of
          | [] =>
              if bridge_proto_is_return_head head then
                [ProtoExpr [ProtoSym (strlit"return"); value]]
              else [original]
          | _ => [original]))
End

Definition bridge_proto_eval_return_fragment_core_factored_def:
  bridge_proto_eval_return_fragment_core_factored atom =
    case atom of
    | ProtoExpr xs => bridge_proto_eval_return_items_factored atom xs
    | _ => [atom]
End

Definition bridge_proto_eval_return_fragment_core_is_return_head_shipped_def:
  bridge_proto_eval_return_fragment_core_is_return_head_shipped atom ⇔
    case atom of
    | ProtoSym s => s = strlit"return"
    | _ => F
End

Definition bridge_proto_eval_return_fragment_core_items_shipped_def:
  bridge_proto_eval_return_fragment_core_items_shipped original [] =
    [original] ∧
  bridge_proto_eval_return_fragment_core_items_shipped
      original (head :: rest) =
    (case rest of
     | [] => [original]
     | value :: rest2 =>
         (case rest2 of
          | [] =>
              if bridge_proto_eval_return_fragment_core_is_return_head_shipped
                   head then
                [ProtoExpr [ProtoSym (strlit"return"); value]]
              else [original]
          | _ => [original]))
End

Definition bridge_proto_eval_return_fragment_core_shipped_def:
  bridge_proto_eval_return_fragment_core_shipped atom =
    case atom of
    | ProtoExpr xs =>
        bridge_proto_eval_return_fragment_core_items_shipped atom xs
    | _ => [atom]
End

Theorem bridge_proto_eval_return_fragment_core_factored_eq:
  ∀atom.
    bridge_proto_eval_return_fragment_core_factored atom =
    bridge_proto_eval_return_fragment_core atom
Proof
  Cases \\
  rw[bridge_proto_eval_return_fragment_core_factored_def,
     bridge_proto_eval_return_fragment_core_def,
     bridge_proto_eval_return_items_factored_def] \\
  every_case_tac \\
  gvs[bridge_proto_eval_return_items_factored_def,
      bridge_proto_is_return_head_def]
QED

Theorem bridge_proto_eval_return_fragment_core_is_return_head_shipped_eq:
  ∀atom.
    bridge_proto_eval_return_fragment_core_is_return_head_shipped atom =
    bridge_proto_is_return_head atom
Proof
  Cases \\
  rw[bridge_proto_eval_return_fragment_core_is_return_head_shipped_def,
     bridge_proto_is_return_head_def]
QED

Theorem bridge_proto_eval_return_fragment_core_items_shipped_eq:
  ∀original xs.
    bridge_proto_eval_return_fragment_core_items_shipped original xs =
    bridge_proto_eval_return_items_factored original xs
Proof
  Cases_on ‘xs’ \\
  rw[bridge_proto_eval_return_fragment_core_items_shipped_def,
     bridge_proto_eval_return_items_factored_def] \\
  Cases_on ‘t’ \\
  rw[bridge_proto_eval_return_fragment_core_items_shipped_def,
     bridge_proto_eval_return_items_factored_def] \\
  Cases_on ‘t'’ \\
  rw[bridge_proto_eval_return_fragment_core_items_shipped_def,
     bridge_proto_eval_return_items_factored_def] \\
  Cases_on ‘bridge_proto_eval_return_fragment_core_is_return_head_shipped h’ \\
  gvs[bridge_proto_eval_return_fragment_core_is_return_head_shipped_eq]
QED

Theorem bridge_proto_eval_return_fragment_core_shipped_eq:
  ∀atom.
    bridge_proto_eval_return_fragment_core_shipped atom =
    bridge_proto_eval_return_fragment_core atom
Proof
  Cases \\
  rw[GSYM bridge_proto_eval_return_fragment_core_factored_eq,
     bridge_proto_eval_return_fragment_core_shipped_def,
     bridge_proto_eval_return_fragment_core_factored_def,
     bridge_proto_eval_return_fragment_core_items_shipped_eq]
QED

Theorem bridge_proto_eval_return_fragment_core_refines_source_expr:
  ∀xs ys.
    bridge_proto_source_rel_list xs ys ⇒
    bridge_proto_source_rel_list
      (bridge_proto_eval_return_fragment_core (ProtoExpr xs))
      (bridge_source_eval_return_fragment_core (SrcExpr ys))
Proof
  rw[bridge_proto_eval_return_fragment_core_def,
     bridge_source_eval_return_fragment_core_def] \\
  every_case_tac \\
  gvs[bridge_proto_eval_return_fragment_core_def,
      bridge_source_eval_return_fragment_core_def,
      bridge_proto_source_rel_def]
QED

Theorem bridge_proto_eval_return_fragment_core_refines_source:
  ∀proto source.
    bridge_proto_source_rel proto source ⇒
    bridge_proto_source_rel_list
      (bridge_proto_eval_return_fragment_core proto)
      (bridge_source_eval_return_fragment_core source)
Proof
  Cases_on ‘proto’ \\
  Cases_on ‘source’ \\
  rw[bridge_proto_eval_return_fragment_core_def,
     bridge_source_eval_return_fragment_core_def,
     bridge_proto_source_rel_def] \\
  every_case_tac \\
  gvs[bridge_proto_eval_return_fragment_core_def,
      bridge_source_eval_return_fragment_core_def,
      bridge_proto_source_rel_def]
QED

Theorem bridge_proto_source_rel_positive_example:
  bridge_proto_source_rel
    (ProtoExpr [ProtoSym (strlit"return"); ProtoVar (strlit"x")])
    (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")])
Proof
  EVAL_TAC
QED

Theorem bridge_proto_source_rel_negative_example:
  ¬bridge_proto_source_rel
    (ProtoExpr [ProtoSym (strlit"return"); ProtoVar (strlit"x")])
    (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"y")])
Proof
  EVAL_TAC
QED

Datatype:
  bridge_source_token =
    BSrcTokLParen
  | BSrcTokRParen
  | BSrcTokBang
  | BSrcTokAtom bridge_source_atom
End

Datatype:
  bridge_proto_token =
    BProtoTokLParen
  | BProtoTokRParen
  | BProtoTokBang
  | BProtoTokAtom bridge_proto_atom
End

Definition bridge_proto_source_token_rel_def:
  bridge_proto_source_token_rel BProtoTokLParen BSrcTokLParen = T ∧
  bridge_proto_source_token_rel BProtoTokRParen BSrcTokRParen = T ∧
  bridge_proto_source_token_rel BProtoTokBang BSrcTokBang = T ∧
  bridge_proto_source_token_rel (BProtoTokAtom proto)
    (BSrcTokAtom source) = bridge_proto_source_rel proto source ∧
  bridge_proto_source_token_rel _ _ = F
End

Definition bridge_proto_source_token_rel_list_def:
  bridge_proto_source_token_rel_list [] [] = T ∧
  bridge_proto_source_token_rel_list (x :: xs) (y :: ys) =
    (bridge_proto_source_token_rel x y ∧
     bridge_proto_source_token_rel_list xs ys) ∧
  bridge_proto_source_token_rel_list _ _ = F
End

Definition bridge_source_char_is_space_def:
  bridge_source_char_is_space c ⇔
    c = #" " ∨ c = #"\n" ∨ c = #"\t" ∨ c = #"\r"
End

Definition bridge_source_char_is_delim_def:
  bridge_source_char_is_delim c ⇔
    bridge_source_char_is_space c ∨
    c = #"(" ∨ c = #")" ∨ c = #"\"" ∨ c = #";"
End

Definition bridge_source_digit_value_def:
  bridge_source_digit_value c =
    if c = #"0" then SOME (0:num)
    else if c = #"1" then SOME (1:num)
    else if c = #"2" then SOME (2:num)
    else if c = #"3" then SOME (3:num)
    else if c = #"4" then SOME (4:num)
    else if c = #"5" then SOME (5:num)
    else if c = #"6" then SOME (6:num)
    else if c = #"7" then SOME (7:num)
    else if c = #"8" then SOME (8:num)
    else if c = #"9" then SOME (9:num)
    else NONE
End

Definition bridge_reverse_chars_acc_def:
  bridge_reverse_chars_acc [] acc = acc ∧
  bridge_reverse_chars_acc (c :: rest) acc =
    bridge_reverse_chars_acc rest (c :: acc)
End

Definition bridge_reverse_chars_def:
  bridge_reverse_chars chars = bridge_reverse_chars_acc chars []
End

Definition bridge_source_all_digits_def:
  bridge_source_all_digits [] = F ∧
  bridge_source_all_digits (c :: rest) =
    (case bridge_source_digit_value c of
     | SOME d =>
         (case rest of
          | [] => T
          | _ => bridge_source_all_digits rest)
     | NONE => F)
End

Definition bridge_source_nat_from_digits_acc_def:
  bridge_source_nat_from_digits_acc [] (acc:num) = acc ∧
  bridge_source_nat_from_digits_acc (c :: rest) (acc:num) =
    (case bridge_source_digit_value c of
     | SOME d => bridge_source_nat_from_digits_acc rest (acc * 10 + d)
     | NONE => acc)
End

Datatype:
  bridge_source_word_atom_result =
    BSourceWordAtom bridge_source_atom
  | BSourceWordError num
End

Definition bridge_source_atom_from_word_chars_def:
  bridge_source_atom_from_word_chars chars =
    case chars of
    | [] => BSourceWordError 10
    | #"$" :: rest =>
        (case rest of
         | [] => BSourceWordError 11
         | _ => BSourceWordAtom (SrcVar (implode rest)))
    | _ =>
        if bridge_source_all_digits chars then
          BSourceWordAtom
            (SrcInt (&bridge_source_nat_from_digits_acc chars 0))
        else
          BSourceWordAtom (SrcSym (implode chars))
End

Definition bridge_source_skip_comment_def:
  bridge_source_skip_comment [] = [] ∧
  bridge_source_skip_comment (#"\n" :: rest) = rest ∧
  bridge_source_skip_comment (c :: rest) =
    bridge_source_skip_comment rest
End

Datatype:
  bridge_source_string_scan_result =
    BSourceStringScanned mlstring (char list)
  | BSourceStringScanError num
End

Definition bridge_source_scan_string_def:
  bridge_source_scan_string acc [] = BSourceStringScanError 12 ∧
  bridge_source_scan_string acc (#"\"" :: rest) =
    BSourceStringScanned (implode (bridge_reverse_chars acc)) rest ∧
  bridge_source_scan_string acc (c :: rest) =
    bridge_source_scan_string (c :: acc) rest
End

Datatype:
  bridge_source_word_scan_result =
    BSourceWordScanned (char list) (char list)
End

Definition bridge_source_scan_word_def:
  bridge_source_scan_word acc [] =
    BSourceWordScanned (bridge_reverse_chars acc) [] ∧
  bridge_source_scan_word acc (c :: rest) =
    if bridge_source_char_is_delim c then
      BSourceWordScanned (bridge_reverse_chars acc) (c :: rest)
    else
      bridge_source_scan_word (c :: acc) rest
End

Datatype:
  bridge_source_lex_result =
    BSourceLexed (bridge_source_token list)
  | BSourceLexError num
End

Definition bridge_tokenize_source_chars_fuel_def:
  bridge_tokenize_source_chars_fuel 0 chars =
    (case chars of
     | [] => BSourceLexed []
     | _ => BSourceLexError 99) ∧
  bridge_tokenize_source_chars_fuel (SUC fuel) [] = BSourceLexed [] ∧
  bridge_tokenize_source_chars_fuel (SUC fuel) (c :: rest) =
    if bridge_source_char_is_space c then
      bridge_tokenize_source_chars_fuel fuel rest
    else if c = #";" then
      bridge_tokenize_source_chars_fuel fuel
        (bridge_source_skip_comment rest)
    else if c = #"(" then
      (case bridge_tokenize_source_chars_fuel fuel rest of
       | BSourceLexed toks => BSourceLexed (BSrcTokLParen :: toks)
       | BSourceLexError n => BSourceLexError n)
    else if c = #")" then
      (case bridge_tokenize_source_chars_fuel fuel rest of
       | BSourceLexed toks => BSourceLexed (BSrcTokRParen :: toks)
       | BSourceLexError n => BSourceLexError n)
    else if c = #"!" then
      (case bridge_tokenize_source_chars_fuel fuel rest of
       | BSourceLexed toks => BSourceLexed (BSrcTokBang :: toks)
       | BSourceLexError n => BSourceLexError n)
    else if c = #"\"" then
      (case bridge_source_scan_string [] rest of
       | BSourceStringScanned s rest2 =>
           (case bridge_tokenize_source_chars_fuel fuel rest2 of
            | BSourceLexed toks =>
                BSourceLexed (BSrcTokAtom (SrcStr s) :: toks)
            | BSourceLexError n => BSourceLexError n)
       | BSourceStringScanError n => BSourceLexError n)
    else
      (case bridge_source_scan_word [c] rest of
       | BSourceWordScanned word_chars rest2 =>
           (case bridge_source_atom_from_word_chars word_chars of
            | BSourceWordAtom atom =>
                (case bridge_tokenize_source_chars_fuel fuel rest2 of
                 | BSourceLexed toks =>
                     BSourceLexed (BSrcTokAtom atom :: toks)
                 | BSourceLexError n => BSourceLexError n)
            | BSourceWordError n => BSourceLexError n))
End

Definition bridge_tokenize_source_string_fuel_def:
  bridge_tokenize_source_string_fuel fuel text =
    bridge_tokenize_source_chars_fuel fuel (explode text)
End

Theorem bridge_source_skip_comment_length:
  ∀chars.
    LENGTH (bridge_source_skip_comment chars) ≤ LENGTH chars
Proof
  Induct_on ‘chars’ \\
  rw[bridge_source_skip_comment_def] \\
  Cases_on ‘h = #"\n"’ \\
  rw[bridge_source_skip_comment_def]
QED

Theorem bridge_source_scan_string_rest_length:
  ∀chars acc s rest.
    bridge_source_scan_string acc chars = BSourceStringScanned s rest ⇒
    LENGTH rest < LENGTH chars
Proof
  Induct_on ‘chars’ \\
  rw[bridge_source_scan_string_def] \\
  Cases_on ‘h = #"\""’
  >- (gvs[bridge_source_scan_string_def] \\ TRY DECIDE_TAC) \\
  gvs[bridge_source_scan_string_def] \\
  first_x_assum drule \\
  rw[] \\
  DECIDE_TAC
QED

Theorem bridge_source_scan_string_error_not_fuel:
  ∀chars acc n.
    bridge_source_scan_string acc chars = BSourceStringScanError n ⇒
    n ≠ 99
Proof
  Induct_on ‘chars’ \\
  rw[bridge_source_scan_string_def] \\
  Cases_on ‘h = #"\""’
  >- gvs[bridge_source_scan_string_def] \\
  gvs[bridge_source_scan_string_def] \\
  metis_tac[]
QED

Theorem bridge_source_scan_word_rest_length:
  ∀chars acc word rest.
    bridge_source_scan_word acc chars = BSourceWordScanned word rest ⇒
    LENGTH rest ≤ LENGTH chars
Proof
  Induct_on ‘chars’ \\
  rw[bridge_source_scan_word_def] \\
  Cases_on ‘bridge_source_char_is_delim h’
  >- (gvs[bridge_source_scan_word_def] \\ TRY DECIDE_TAC) \\
  gvs[bridge_source_scan_word_def] \\
  first_x_assum drule \\
  rw[] \\
  DECIDE_TAC
QED

Theorem bridge_source_atom_from_word_chars_error_not_fuel:
  ∀chars n.
    bridge_source_atom_from_word_chars chars = BSourceWordError n ⇒
    n ≠ 99
Proof
  Cases_on ‘chars’ \\
  rw[bridge_source_atom_from_word_chars_def] \\
  Cases_on ‘h = #"$"’ \\
  gvs[bridge_source_atom_from_word_chars_def] \\
  Cases_on ‘t’ \\
  gvs[bridge_source_atom_from_word_chars_def]
QED

Theorem bridge_tokenize_source_chars_fuel_no_fuel_error:
  ∀fuel chars.
    LENGTH chars ≤ fuel ⇒
    bridge_tokenize_source_chars_fuel fuel chars ≠ BSourceLexError 99
Proof
  Induct_on ‘fuel’
  >- (
    gen_tac \\
    strip_tac \\
    Cases_on ‘chars’ \\
    gvs[bridge_tokenize_source_chars_fuel_def]) \\
  gen_tac \\
  strip_tac \\
  CCONTR_TAC \\
  Cases_on ‘chars’ \\
  gvs[bridge_tokenize_source_chars_fuel_def] \\
  every_case_tac \\
  gvs[] \\
  imp_res_tac bridge_source_skip_comment_length \\
  imp_res_tac bridge_source_scan_string_rest_length \\
  imp_res_tac bridge_source_scan_string_error_not_fuel \\
  imp_res_tac bridge_source_scan_word_rest_length \\
  imp_res_tac bridge_source_atom_from_word_chars_error_not_fuel \\
  TRY (
    qpat_x_assum
      ‘bridge_tokenize_source_chars_fuel fuel t = BSourceLexError 99’
      mp_tac \\
    qpat_x_assum
      ‘∀chars.
         LENGTH chars ≤ fuel ⇒
         bridge_tokenize_source_chars_fuel fuel chars ≠ BSourceLexError 99’
      (qspec_then ‘t’ mp_tac) \\
    impl_tac >- DECIDE_TAC \\
    rw[] \\
    gvs[]) \\
  TRY (
    qpat_x_assum
      ‘bridge_tokenize_source_chars_fuel fuel
         (bridge_source_skip_comment t) = BSourceLexError 99’
      mp_tac \\
    qpat_x_assum
      ‘∀chars.
         LENGTH chars ≤ fuel ⇒
         bridge_tokenize_source_chars_fuel fuel chars ≠ BSourceLexError 99’
      (qspec_then ‘bridge_source_skip_comment t’ mp_tac) \\
    impl_tac
    >- (
      qspec_then ‘t’ mp_tac bridge_source_skip_comment_length \\
      DECIDE_TAC) \\
    rw[] \\
    gvs[]) \\
  TRY (
    qpat_x_assum
      ‘bridge_tokenize_source_chars_fuel fuel l = BSourceLexError 99’
      mp_tac \\
    qpat_x_assum
      ‘∀chars.
         LENGTH chars ≤ fuel ⇒
         bridge_tokenize_source_chars_fuel fuel chars ≠ BSourceLexError 99’
      (qspec_then ‘l’ mp_tac) \\
    impl_tac >- DECIDE_TAC \\
    rw[] \\
    gvs[]) \\
  TRY (
    qpat_x_assum
      ‘bridge_tokenize_source_chars_fuel fuel l0 = BSourceLexError 99’
      mp_tac \\
    qpat_x_assum
      ‘∀chars.
         LENGTH chars ≤ fuel ⇒
         bridge_tokenize_source_chars_fuel fuel chars ≠ BSourceLexError 99’
      (qspec_then ‘l0’ mp_tac) \\
    impl_tac >- DECIDE_TAC \\
    rw[] \\
    gvs[]) \\
  gvs[]
QED

Theorem bridge_source_char_is_space_positive_example:
  bridge_source_char_is_space #" " ∧
  bridge_source_char_is_space #"\n" ∧
  bridge_source_char_is_space #"\t" ∧
  bridge_source_char_is_space #"\r"
Proof
  EVAL_TAC
QED

Theorem bridge_source_char_is_space_negative_example:
  ¬bridge_source_char_is_space #"a" ∧
  ¬bridge_source_char_is_space #"!"
Proof
  EVAL_TAC
QED

Theorem bridge_source_atom_from_word_chars_positive_example:
  bridge_source_atom_from_word_chars [#"$"; #"x"] =
    BSourceWordAtom (SrcVar (strlit"x")) ∧
  bridge_source_atom_from_word_chars [#"1"; #"2"; #"3"] =
    BSourceWordAtom (SrcInt 123) ∧
  bridge_source_atom_from_word_chars [#"+"; #"!"] =
    BSourceWordAtom (SrcSym (strlit"+!"))
Proof
  EVAL_TAC
QED

Theorem bridge_source_atom_from_word_chars_negative_example:
  bridge_source_atom_from_word_chars [] = BSourceWordError 10 ∧
  bridge_source_atom_from_word_chars [#"$"] = BSourceWordError 11
Proof
  EVAL_TAC
QED

Theorem bridge_tokenize_source_chars_fuel_positive_example:
  bridge_tokenize_source_chars_fuel 100
    [#"("; #"r"; #"e"; #"t"; #"u"; #"r"; #"n"; #" ";
     #"$"; #"x"; #")"; #"\n";
     #";"; #" "; #"c"; #"o"; #"m"; #"m"; #"e"; #"n"; #"t"; #"\n";
     #"!"; #"("; #"+"; #" "; #"1"; #" "; #"2"; #")"; #" ";
     #"\""; #"h"; #"i"; #"\""] =
  BSourceLexed
    [BSrcTokLParen;
     BSrcTokAtom (SrcSym (strlit"return"));
     BSrcTokAtom (SrcVar (strlit"x"));
     BSrcTokRParen;
     BSrcTokBang;
     BSrcTokLParen;
     BSrcTokAtom (SrcSym (strlit"+"));
     BSrcTokAtom (SrcInt 1);
     BSrcTokAtom (SrcInt 2);
     BSrcTokRParen;
     BSrcTokAtom (SrcStr (strlit"hi"))]
Proof
  EVAL_TAC
QED

Theorem bridge_tokenize_source_chars_fuel_negative_example:
  bridge_tokenize_source_chars_fuel 10 [#"\""; #"h"] =
    BSourceLexError 12 ∧
  bridge_tokenize_source_chars_fuel 10 [#"$"; #")"] =
    BSourceLexError 11
Proof
  EVAL_TAC
QED

Theorem bridge_tokenize_source_string_fuel_positive_example:
  bridge_tokenize_source_string_fuel 100
    (strlit"(return $x)\n; comment\n!(+ 1 2)") =
  BSourceLexed
    [BSrcTokLParen;
     BSrcTokAtom (SrcSym (strlit"return"));
     BSrcTokAtom (SrcVar (strlit"x"));
     BSrcTokRParen;
     BSrcTokBang;
     BSrcTokLParen;
     BSrcTokAtom (SrcSym (strlit"+"));
     BSrcTokAtom (SrcInt 1);
     BSrcTokAtom (SrcInt 2);
     BSrcTokRParen]
Proof
  EVAL_TAC
QED

Theorem bridge_tokenize_source_string_fuel_negative_example:
  bridge_tokenize_source_string_fuel 10 (strlit"$)") =
    BSourceLexError 11
Proof
  EVAL_TAC
QED

Definition bridge_source_surface_token_rel_def:
  bridge_source_surface_token_rel var_env str_env source_tok surface_tok =
    case source_tok of
    | BSrcTokLParen =>
        (case surface_tok of BTokLParen => T | _ => F)
    | BSrcTokRParen =>
        (case surface_tok of BTokRParen => T | _ => F)
    | BSrcTokBang =>
        (case surface_tok of BTokBang => T | _ => F)
    | BSrcTokAtom source =>
        (case surface_tok of
         | BTokAtom surface =>
             bridge_source_surface_rel var_env str_env source surface
         | _ => F)
End

Definition bridge_source_surface_token_rel_list_def:
  bridge_source_surface_token_rel_list var_env str_env [] [] = T ∧
  bridge_source_surface_token_rel_list var_env str_env
    (x :: xs) (y :: ys) =
      (bridge_source_surface_token_rel var_env str_env x y ∧
       bridge_source_surface_token_rel_list var_env str_env xs ys) ∧
  bridge_source_surface_token_rel_list var_env str_env _ _ = F
End

Theorem bridge_source_surface_token_rel_list_nil_cons:
  ∀var_env str_env (tok:bridge_token) toks.
    ¬bridge_source_surface_token_rel_list var_env str_env [] (tok :: toks)
Proof
  rw[bridge_source_surface_token_rel_list_def]
QED

Theorem bridge_source_surface_token_rel_list_cons_nil:
  ∀var_env str_env (tok:bridge_source_token) toks.
    ¬bridge_source_surface_token_rel_list var_env str_env (tok :: toks) []
Proof
  rw[bridge_source_surface_token_rel_list_def]
QED

Theorem bridge_source_surface_token_rel_list_cons_lparen:
  ∀var_env str_env xs ys.
    bridge_source_surface_token_rel_list var_env str_env xs ys ⇒
    bridge_source_surface_token_rel_list var_env str_env
      (BSrcTokLParen :: xs) (BTokLParen :: ys)
Proof
  rw[bridge_source_surface_token_rel_def,
     bridge_source_surface_token_rel_list_def]
QED

Definition bridge_parse_source_atom_token_def:
  bridge_parse_source_atom_token (BSrcTokAtom atom :: rest) =
    SOME (atom, rest) ∧
  bridge_parse_source_atom_token _ = NONE
End

Datatype:
  bridge_source_full_atom_parse_result =
    BSourceFullAtomParsed bridge_source_atom (bridge_source_token list)
  | BSourceFullAtomParseError num
End

Definition bridge_parse_source_atom_tokens_fuel_def:
  bridge_parse_source_atom_tokens_fuel 0 toks =
    BSourceFullAtomParseError 99 ∧
  bridge_parse_source_atom_tokens_fuel (SUC fuel) toks =
    (case toks of
     | BSrcTokAtom atom :: rest => BSourceFullAtomParsed atom rest
     | BSrcTokLParen :: rest => bridge_parse_source_expr_items_fuel fuel [] rest
     | BSrcTokRParen :: rest => BSourceFullAtomParseError 1
     | BSrcTokBang :: rest => BSourceFullAtomParseError 2
     | [] => BSourceFullAtomParseError 3) ∧
  bridge_parse_source_expr_items_fuel 0 items toks =
    BSourceFullAtomParseError 99 ∧
  bridge_parse_source_expr_items_fuel (SUC fuel) items toks =
    (case toks of
     | BSrcTokRParen :: rest => BSourceFullAtomParsed (SrcExpr items) rest
     | [] => BSourceFullAtomParseError 4
     | _ =>
        (case bridge_parse_source_atom_tokens_fuel fuel toks of
         | BSourceFullAtomParsed atom rest =>
             bridge_parse_source_expr_items_fuel fuel (items ++ [atom]) rest
         | BSourceFullAtomParseError n => BSourceFullAtomParseError n))
Termination
  WF_REL_TAC
    ‘measure
       (λx. case x of
        | INL (fuel,toks) => fuel
        | INR (fuel,items,toks) => fuel)’ \\
  rw[]
End

Definition bridge_parse_proto_atom_token_def:
  bridge_parse_proto_atom_token (BProtoTokAtom atom :: rest) =
    SOME (atom, rest) ∧
  bridge_parse_proto_atom_token _ = NONE
End

Datatype:
  bridge_proto_full_atom_parse_result =
    BProtoFullAtomParsed bridge_proto_atom (bridge_proto_token list)
  | BProtoFullAtomParseError num
End

Definition bridge_parse_proto_atom_tokens_fuel_def:
  bridge_parse_proto_atom_tokens_fuel 0 toks =
    BProtoFullAtomParseError 99 ∧
  bridge_parse_proto_atom_tokens_fuel (SUC fuel) toks =
    (case toks of
     | BProtoTokAtom atom :: rest => BProtoFullAtomParsed atom rest
     | BProtoTokLParen :: rest => bridge_parse_proto_expr_items_fuel fuel [] rest
     | BProtoTokRParen :: rest => BProtoFullAtomParseError 1
     | BProtoTokBang :: rest => BProtoFullAtomParseError 2
     | [] => BProtoFullAtomParseError 3) ∧
  bridge_parse_proto_expr_items_fuel 0 items toks =
    BProtoFullAtomParseError 99 ∧
  bridge_parse_proto_expr_items_fuel (SUC fuel) items toks =
    (case toks of
     | BProtoTokRParen :: rest => BProtoFullAtomParsed (ProtoExpr items) rest
     | [] => BProtoFullAtomParseError 4
     | _ =>
        (case bridge_parse_proto_atom_tokens_fuel fuel toks of
         | BProtoFullAtomParsed atom rest =>
             bridge_parse_proto_expr_items_fuel fuel (items ++ [atom]) rest
         | BProtoFullAtomParseError n => BProtoFullAtomParseError n))
Termination
  WF_REL_TAC
    ‘measure
       (λx. case x of
        | INL (fuel,toks) => fuel
        | INR (fuel,items,toks) => fuel)’ \\
  rw[]
End

Theorem bridge_proto_source_rel_list_snoc:
  ∀proto_items source_items proto source.
    bridge_proto_source_rel_list proto_items source_items ∧
    bridge_proto_source_rel proto source ⇒
    bridge_proto_source_rel_list
      (proto_items ++ [proto]) (source_items ++ [source])
Proof
  Induct_on ‘proto_items’ \\
  Cases_on ‘source_items’ \\
  rw[bridge_proto_source_rel_def]
QED

Definition bridge_proto_source_parse_result_rel_def:
  bridge_proto_source_parse_result_rel
    (BProtoFullAtomParsed proto rest_proto)
    (BSourceFullAtomParsed source rest_source) =
      (bridge_proto_source_rel proto source ∧
       bridge_proto_source_token_rel_list rest_proto rest_source) ∧
  bridge_proto_source_parse_result_rel
    (BProtoFullAtomParseError n) (BSourceFullAtomParseError m) =
      (n = m) ∧
  bridge_proto_source_parse_result_rel _ _ = F
End

Theorem bridge_parse_proto_source_full_expr_positive_example:
  ∃proto source rest_proto rest_source.
    bridge_parse_proto_atom_tokens_fuel 10
      [BProtoTokLParen;
       BProtoTokAtom (ProtoSym (strlit"return"));
       BProtoTokAtom (ProtoVar (strlit"x"));
       BProtoTokRParen] =
      BProtoFullAtomParsed proto rest_proto ∧
    bridge_parse_source_atom_tokens_fuel 10
      [BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"return"));
       BSrcTokAtom (SrcVar (strlit"x"));
       BSrcTokRParen] =
      BSourceFullAtomParsed source rest_source ∧
    bridge_proto_source_rel proto source ∧
    bridge_proto_source_token_rel_list rest_proto rest_source
Proof
  qexists_tac ‘ProtoExpr [ProtoSym (strlit"return"); ProtoVar (strlit"x")]’ \\
  qexists_tac ‘SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")]’ \\
  qexists_tac ‘[]’ \\
  qexists_tac ‘[]’ \\
  EVAL_TAC
QED

Theorem bridge_parse_atom_token_proto_source_related:
  ∀proto_toks source_toks proto rest_proto source rest_source.
    bridge_proto_source_token_rel_list proto_toks source_toks ∧
    bridge_parse_proto_atom_token proto_toks =
      SOME (proto, rest_proto) ∧
    bridge_parse_source_atom_token source_toks =
      SOME (source, rest_source) ⇒
    bridge_proto_source_rel proto source ∧
    bridge_proto_source_token_rel_list rest_proto rest_source
Proof
  Cases_on ‘proto_toks’ \\
  Cases_on ‘source_toks’ \\
  rw[bridge_parse_proto_atom_token_def,
     bridge_parse_source_atom_token_def,
     bridge_proto_source_token_rel_def,
     bridge_proto_source_token_rel_list_def] \\
  Cases_on ‘h’ \\
  Cases_on ‘h'’ \\
  gvs[bridge_parse_proto_atom_token_def,
      bridge_parse_source_atom_token_def,
      bridge_proto_source_token_rel_def,
      bridge_proto_source_token_rel_list_def]
QED

Theorem bridge_parse_atom_token_proto_source_positive_example:
  ∃proto source rest_proto rest_source.
    bridge_parse_proto_atom_token
      [BProtoTokAtom (ProtoSym (strlit"return"))] =
      SOME (proto, rest_proto) ∧
    bridge_parse_source_atom_token
      [BSrcTokAtom (SrcSym (strlit"return"))] =
      SOME (source, rest_source) ∧
    bridge_proto_source_rel proto source ∧
    bridge_proto_source_token_rel_list rest_proto rest_source
Proof
  qexists_tac ‘ProtoSym (strlit"return")’ \\
  qexists_tac ‘SrcSym (strlit"return")’ \\
  qexists_tac ‘[]’ \\
  qexists_tac ‘[]’ \\
  EVAL_TAC
QED

Theorem bridge_parse_atom_token_proto_source_negative_example:
  ¬bridge_proto_source_token_rel_list
    [BProtoTokAtom (ProtoVar (strlit"x"))]
    [BSrcTokAtom (SrcVar (strlit"y"))]
Proof
  EVAL_TAC
QED

Theorem bridge_parse_proto_source_tokens_fuel_related:
  ∀fuel.
    (∀proto_toks source_toks.
      bridge_proto_source_token_rel_list proto_toks source_toks ⇒
      bridge_proto_source_parse_result_rel
        (bridge_parse_proto_atom_tokens_fuel fuel proto_toks)
        (bridge_parse_source_atom_tokens_fuel fuel source_toks)) ∧
    (∀proto_items source_items proto_toks source_toks.
      bridge_proto_source_rel_list proto_items source_items ∧
      bridge_proto_source_token_rel_list proto_toks source_toks ⇒
      bridge_proto_source_parse_result_rel
        (bridge_parse_proto_expr_items_fuel
          fuel proto_items proto_toks)
        (bridge_parse_source_expr_items_fuel
          fuel source_items source_toks))
Proof
  Induct_on ‘fuel’
  >- rw[bridge_parse_proto_atom_tokens_fuel_def,
        bridge_parse_source_atom_tokens_fuel_def,
        bridge_proto_source_parse_result_rel_def] \\
  rw[]
  >- (
    Cases_on ‘proto_toks’ \\
    Cases_on ‘source_toks’ \\
    gvs[bridge_parse_proto_atom_tokens_fuel_def,
        bridge_parse_source_atom_tokens_fuel_def,
        bridge_proto_source_token_rel_def,
        bridge_proto_source_token_rel_list_def,
        bridge_proto_source_parse_result_rel_def] \\
    every_case_tac \\
    gvs[bridge_parse_proto_atom_tokens_fuel_def,
        bridge_parse_source_atom_tokens_fuel_def,
        bridge_proto_source_token_rel_def,
        bridge_proto_source_token_rel_list_def,
        bridge_proto_source_parse_result_rel_def] \\
    TRY (
      rename1
        ‘bridge_proto_source_token_rel_list proto_rest source_rest’ \\
      qpat_x_assum
        ‘∀proto_items source_items proto_toks source_toks. _’
        (qspecl_then
          [‘[]’, ‘[]’, ‘proto_rest’, ‘source_rest’] mp_tac) \\
      rw[bridge_proto_source_rel_def]) \\
    metis_tac[bridge_proto_source_rel_def])
  >- (
    qpat_x_assum ‘∀proto_toks source_toks. _’
      (qspecl_then [‘proto_toks’, ‘source_toks’] mp_tac) \\
    impl_tac
    >- gvs[bridge_proto_source_token_rel_list_def] \\
    strip_tac \\
    Cases_on ‘proto_toks’ \\
    Cases_on ‘source_toks’ \\
    gvs[bridge_parse_proto_atom_tokens_fuel_def,
        bridge_parse_source_atom_tokens_fuel_def,
        bridge_proto_source_token_rel_def,
        bridge_proto_source_token_rel_list_def,
        bridge_proto_source_parse_result_rel_def] \\
    every_case_tac \\
    gvs[bridge_parse_proto_atom_tokens_fuel_def,
        bridge_parse_source_atom_tokens_fuel_def,
        bridge_proto_source_token_rel_def,
        bridge_proto_source_token_rel_list_def,
        bridge_proto_source_parse_result_rel_def,
        bridge_proto_source_rel_def] \\
    metis_tac[bridge_proto_source_rel_list_snoc,
              bridge_proto_source_rel_def])
QED

Theorem bridge_parse_proto_source_full_tokens_related:
  ∀fuel proto_toks source_toks.
    bridge_proto_source_token_rel_list proto_toks source_toks ⇒
    bridge_proto_source_parse_result_rel
      (bridge_parse_proto_atom_tokens_fuel fuel proto_toks)
      (bridge_parse_source_atom_tokens_fuel fuel source_toks)
Proof
  metis_tac[bridge_parse_proto_source_tokens_fuel_related]
QED

Theorem bridge_source_surface_rel_list_snoc:
  ∀var_env str_env source_items surface_items source surface.
    bridge_source_surface_rel_list var_env str_env
      source_items surface_items ∧
    bridge_source_surface_rel var_env str_env source surface ⇒
    bridge_source_surface_rel_list var_env str_env
      (source_items ++ [source]) (surface_items ++ [surface])
Proof
  Induct_on ‘source_items’ \\
  Cases_on ‘surface_items’ \\
  rw[bridge_source_surface_rel_def]
QED

Definition bridge_source_surface_parse_result_rel_def:
  bridge_source_surface_parse_result_rel var_env str_env
    (BSourceFullAtomParsed source rest_source)
    (BFullAtomParsed surface rest_surface) =
      (bridge_source_surface_rel var_env str_env source surface ∧
       bridge_source_surface_token_rel_list var_env str_env
         rest_source rest_surface) ∧
  bridge_source_surface_parse_result_rel var_env str_env
    (BSourceFullAtomParseError n) (BFullAtomParseError m) =
      (n = m) ∧
  bridge_source_surface_parse_result_rel var_env str_env _ _ = F
End

Theorem bridge_parse_source_surface_full_expr_positive_example:
  ∃source surface rest_source rest_surface.
    bridge_parse_source_atom_tokens_fuel 10
      [BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"return"));
       BSrcTokAtom (SrcVar (strlit"x"));
       BSrcTokRParen] =
      BSourceFullAtomParsed source rest_source ∧
    bridge_parse_atom_tokens_fuel 10
      [BTokLParen;
       BTokAtom (BSym (strlit"return"));
       BTokAtom (BVar 0);
       BTokRParen] =
      BFullAtomParsed surface rest_surface ∧
    bridge_source_surface_rel [(strlit"x", 0)] []
      source surface ∧
    bridge_source_surface_token_rel_list [(strlit"x", 0)] []
      rest_source rest_surface
Proof
  qexists_tac ‘SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")]’ \\
  qexists_tac ‘BExpr [BSym (strlit"return"); BVar 0]’ \\
  qexists_tac ‘[]’ \\
  qexists_tac ‘[]’ \\
  EVAL_TAC
QED

Theorem bridge_parse_atom_token_source_surface_related:
  ∀var_env str_env source_toks surface_toks source rest_source surface rest_surface.
    bridge_source_surface_token_rel_list var_env str_env
      source_toks surface_toks ∧
    bridge_parse_source_atom_token source_toks =
      SOME (source, rest_source) ∧
    bridge_parse_atom_token surface_toks =
      SOME (surface, rest_surface) ⇒
    bridge_source_surface_rel var_env str_env source surface ∧
    bridge_source_surface_token_rel_list var_env str_env
      rest_source rest_surface
Proof
  Cases_on ‘source_toks’ \\
  Cases_on ‘surface_toks’ \\
  rw[bridge_parse_source_atom_token_def,
     bridge_parse_atom_token_def,
     bridge_source_surface_token_rel_def,
     bridge_source_surface_token_rel_list_def] \\
  Cases_on ‘h’ \\
  Cases_on ‘h'’ \\
  gvs[bridge_parse_source_atom_token_def,
      bridge_parse_atom_token_def,
      bridge_source_surface_token_rel_def,
      bridge_source_surface_token_rel_list_def]
QED

Theorem bridge_parse_atom_token_source_surface_positive_example:
  ∃source surface rest_source rest_surface.
    bridge_parse_source_atom_token
      [BSrcTokAtom (SrcSym (strlit"return"))] =
      SOME (source, rest_source) ∧
    bridge_parse_atom_token [BTokAtom (BSym (strlit"return"))] =
      SOME (surface, rest_surface) ∧
    bridge_source_surface_rel [] [] source surface ∧
    bridge_source_surface_token_rel_list [] [] rest_source rest_surface
Proof
  qexists_tac ‘SrcSym (strlit"return")’ \\
  qexists_tac ‘BSym (strlit"return")’ \\
  qexists_tac ‘[]’ \\
  qexists_tac ‘[]’ \\
  EVAL_TAC
QED

Theorem bridge_parse_atom_token_source_surface_negative_example:
  ¬bridge_source_surface_token_rel_list [] []
    [BSrcTokAtom (SrcVar (strlit"x"))]
    [BTokAtom (BVar 0)]
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_surface_tokens_fuel_related:
  ∀fuel.
    (∀var_env str_env source_toks surface_toks.
      bridge_source_surface_token_rel_list var_env str_env
        source_toks surface_toks ⇒
      bridge_source_surface_parse_result_rel var_env str_env
        (bridge_parse_source_atom_tokens_fuel fuel source_toks)
        (bridge_parse_atom_tokens_fuel fuel surface_toks)) ∧
    (∀var_env str_env source_items surface_items source_toks surface_toks.
      bridge_source_surface_rel_list var_env str_env
        source_items surface_items ∧
      bridge_source_surface_token_rel_list var_env str_env
        source_toks surface_toks ⇒
      bridge_source_surface_parse_result_rel var_env str_env
        (bridge_parse_source_expr_items_fuel
          fuel source_items source_toks)
        (bridge_parse_expr_items_fuel
          fuel surface_items surface_toks))
Proof
  Induct_on ‘fuel’
  >- rw[bridge_parse_source_atom_tokens_fuel_def,
        bridge_parse_atom_tokens_fuel_def,
        bridge_source_surface_parse_result_rel_def] \\
  rw[]
  >- (
    Cases_on ‘source_toks’ \\
    Cases_on ‘surface_toks’ \\
    gvs[bridge_parse_source_atom_tokens_fuel_def,
        bridge_parse_atom_tokens_fuel_def,
        bridge_source_surface_token_rel_def,
        bridge_source_surface_token_rel_list_def,
        bridge_source_surface_parse_result_rel_def] \\
    every_case_tac \\
    gvs[bridge_parse_source_atom_tokens_fuel_def,
        bridge_parse_atom_tokens_fuel_def,
        bridge_source_surface_token_rel_def,
        bridge_source_surface_token_rel_list_def,
        bridge_source_surface_parse_result_rel_def] \\
    TRY (
      rename1
        ‘bridge_source_surface_token_rel_list var_env str_env
          source_rest surface_rest’ \\
      qpat_x_assum
        ‘∀var_env str_env source_items surface_items source_toks surface_toks. _’
        (qspecl_then
          [‘var_env’, ‘str_env’, ‘[]’, ‘[]’,
           ‘source_rest’, ‘surface_rest’] mp_tac) \\
      rw[bridge_source_surface_rel_def]) \\
    metis_tac[bridge_source_surface_rel_def])
  >- (
    qpat_x_assum ‘∀var_env str_env source_toks surface_toks. _’
      (qspecl_then
        [‘var_env’, ‘str_env’, ‘source_toks’, ‘surface_toks’] mp_tac) \\
    impl_tac
    >- gvs[bridge_source_surface_token_rel_list_def] \\
    strip_tac \\
    Cases_on ‘source_toks’ \\
    Cases_on ‘surface_toks’ \\
    gvs[bridge_parse_source_atom_tokens_fuel_def,
        bridge_parse_atom_tokens_fuel_def,
        bridge_source_surface_token_rel_def,
        bridge_source_surface_token_rel_list_def,
        bridge_source_surface_parse_result_rel_def] \\
    every_case_tac \\
    gvs[bridge_parse_source_atom_tokens_fuel_def,
        bridge_parse_atom_tokens_fuel_def,
        bridge_source_surface_token_rel_def,
        bridge_source_surface_token_rel_list_def,
        bridge_source_surface_parse_result_rel_def,
        bridge_source_surface_rel_def] \\
    metis_tac[bridge_source_surface_rel_list_snoc,
              bridge_source_surface_rel_def])
QED

Theorem bridge_parse_source_surface_full_tokens_related:
  ∀fuel var_env str_env source_toks surface_toks.
    bridge_source_surface_token_rel_list var_env str_env
      source_toks surface_toks ⇒
    bridge_source_surface_parse_result_rel var_env str_env
      (bridge_parse_source_atom_tokens_fuel fuel source_toks)
      (bridge_parse_atom_tokens_fuel fuel surface_toks)
Proof
  metis_tac[bridge_parse_source_surface_tokens_fuel_related]
QED

Datatype:
  bridge_command =
    BCmdAdd bridge_surface_atom
  | BCmdRun bridge_surface_atom
End

Datatype:
  bridge_command_parse_result =
    BCommandParsed bridge_command (bridge_token list)
  | BCommandParseError num
End

Datatype:
  bridge_program_parse_result =
    BProgramParsed (bridge_command list)
  | BProgramParseError num
End

Datatype:
  bridge_numeric_command =
    BNumCmdAdd metta_m1$atom
  | BNumCmdRun metta_m1$atom
End

Definition bridge_import_command_with_env_def:
  bridge_import_command_with_env env (BCmdAdd atom) =
    (case bridge_import_surface_atom_with_env env atom of
     | SOME imported => SOME (BNumCmdAdd imported)
     | NONE => NONE) ∧
  bridge_import_command_with_env env (BCmdRun atom) =
    (case bridge_import_surface_atom_with_env env atom of
     | SOME imported => SOME (BNumCmdRun imported)
     | NONE => NONE)
End

Definition bridge_import_command_list_with_env_def:
  bridge_import_command_list_with_env env [] = SOME [] ∧
  bridge_import_command_list_with_env env (cmd :: cmds) =
    (case bridge_import_command_with_env env cmd of
     | SOME imported =>
         (case bridge_import_command_list_with_env env cmds of
          | SOME rest => SOME (imported :: rest)
          | NONE => NONE)
     | NONE => NONE)
End

Definition bridge_export_command_with_env_def:
  bridge_export_command_with_env env (BNumCmdAdd atom) =
    (case bridge_export_surface_atom_with_env env atom of
     | SOME surface => SOME (BCmdAdd surface)
     | NONE => NONE) ∧
  bridge_export_command_with_env env (BNumCmdRun atom) =
    (case bridge_export_surface_atom_with_env env atom of
     | SOME surface => SOME (BCmdRun surface)
     | NONE => NONE)
End

Definition bridge_export_command_list_with_env_def:
  bridge_export_command_list_with_env env [] = SOME [] ∧
  bridge_export_command_list_with_env env (cmd :: cmds) =
    (case bridge_export_command_with_env env cmd of
     | SOME surface =>
         (case bridge_export_command_list_with_env env cmds of
          | SOME rest => SOME (surface :: rest)
          | NONE => NONE)
     | NONE => NONE)
End

Theorem bridge_import_command_with_env_export_roundtrip:
  ∀env cmd imported.
    bridge_dyn_env_ok env ∧
    bridge_import_command_with_env env cmd = SOME imported ⇒
    bridge_export_command_with_env env imported = SOME cmd
Proof
  Cases_on ‘cmd’ \\
  rw[bridge_import_command_with_env_def] \\
  every_case_tac \\
  gvs[bridge_export_command_with_env_def] \\
  drule_all bridge_import_surface_atom_with_env_export_roundtrip \\
  rw[]
QED

Theorem bridge_import_command_list_with_env_export_roundtrip:
  ∀env cmds imported.
    bridge_dyn_env_ok env ∧
    bridge_import_command_list_with_env env cmds = SOME imported ⇒
    bridge_export_command_list_with_env env imported = SOME cmds
Proof
  Induct_on ‘cmds’ \\
  rw[bridge_import_command_list_with_env_def,
     bridge_export_command_list_with_env_def] \\
  Cases_on ‘bridge_import_command_with_env env h’
  >- gvs[] \\
  Cases_on ‘bridge_import_command_list_with_env env cmds’
  >- gvs[] \\
  gvs[] \\
  rename1 ‘bridge_import_command_with_env env cmd = SOME imported_cmd’ \\
  rename1 ‘bridge_import_command_list_with_env env cmds = SOME imported_cmds’ \\
  drule_all bridge_import_command_with_env_export_roundtrip \\
  strip_tac \\
  qpat_x_assum
    ‘∀env imported.
       bridge_dyn_env_ok env ∧
       bridge_import_command_list_with_env env cmds = SOME imported ⇒
       bridge_export_command_list_with_env env imported = SOME cmds’
    (qspecl_then [‘env’, ‘imported_cmds’] mp_tac) \\
  rw[bridge_export_command_list_with_env_def]
QED

Theorem bridge_export_command_with_env_import_roundtrip:
  ∀env imported cmd.
    bridge_dyn_env_ok env ∧
    bridge_export_command_with_env env imported = SOME cmd ⇒
    bridge_import_command_with_env env cmd = SOME imported
Proof
  Cases_on ‘imported’ \\
  rw[bridge_export_command_with_env_def] \\
  every_case_tac \\
  gvs[bridge_import_command_with_env_def] \\
  drule_all bridge_export_surface_atom_with_env_import_roundtrip \\
  rw[]
QED

Theorem bridge_export_command_list_with_env_import_roundtrip:
  ∀env imported cmds.
    bridge_dyn_env_ok env ∧
    bridge_export_command_list_with_env env imported = SOME cmds ⇒
    bridge_import_command_list_with_env env cmds = SOME imported
Proof
  Induct_on ‘imported’ \\
  rw[bridge_import_command_list_with_env_def,
     bridge_export_command_list_with_env_def] \\
  Cases_on ‘bridge_export_command_with_env env h’
  >- gvs[] \\
  Cases_on ‘bridge_export_command_list_with_env env imported’
  >- gvs[] \\
  gvs[] \\
  rename1 ‘bridge_export_command_with_env env cmd = SOME surface_cmd’ \\
  rename1 ‘bridge_export_command_list_with_env env imported = SOME surface_cmds’ \\
  drule_all bridge_export_command_with_env_import_roundtrip \\
  strip_tac \\
  qpat_x_assum
    ‘∀env cmds.
       bridge_dyn_env_ok env ∧
       bridge_export_command_list_with_env env imported = SOME cmds ⇒
       bridge_import_command_list_with_env env cmds = SOME imported’
    (qspecl_then [‘env’, ‘surface_cmds’] mp_tac) \\
  rw[bridge_import_command_list_with_env_def]
QED

Definition bridge_parse_command_tokens_fuel_def:
  bridge_parse_command_tokens_fuel fuel toks =
    case toks of
    | BTokBang :: rest =>
        (case bridge_parse_atom_tokens_fuel fuel rest of
         | BFullAtomParsed atom rest2 =>
             BCommandParsed (BCmdRun atom) rest2
         | BFullAtomParseError n => BCommandParseError n)
    | _ =>
        (case bridge_parse_atom_tokens_fuel fuel toks of
         | BFullAtomParsed atom rest => BCommandParsed (BCmdAdd atom) rest
         | BFullAtomParseError n => BCommandParseError n)
End

Definition bridge_parse_program_tokens_fuel_def:
  bridge_parse_program_tokens_fuel 0 toks =
    (case toks of
     | [] => BProgramParsed []
     | _ => BProgramParseError 99) ∧
  bridge_parse_program_tokens_fuel (SUC fuel) toks =
    (case toks of
     | [] => BProgramParsed []
     | _ =>
        (case bridge_parse_command_tokens_fuel (SUC fuel) toks of
         | BCommandParsed cmd rest =>
             (case bridge_parse_program_tokens_fuel fuel rest of
              | BProgramParsed cmds => BProgramParsed (cmd :: cmds)
              | BProgramParseError n => BProgramParseError n)
         | BCommandParseError n => BProgramParseError n))
End

Definition bridge_import_parsed_command_tokens_with_env_def:
  bridge_import_parsed_command_tokens_with_env env fuel toks =
    case bridge_parse_command_tokens_fuel fuel toks of
    | BCommandParsed cmd rest =>
        (case bridge_import_command_with_env env cmd of
         | SOME imported => SOME (imported, rest)
         | NONE => NONE)
    | BCommandParseError n => NONE
End

Datatype:
  bridge_imported_command_parse_result =
    BImportedCommandParsed bridge_numeric_command (bridge_token list)
  | BImportedCommandParseError num
  | BImportedCommandImportError
End

Definition bridge_import_parsed_command_tokens_result_with_env_def:
  bridge_import_parsed_command_tokens_result_with_env env fuel toks =
    case bridge_parse_command_tokens_fuel fuel toks of
    | BCommandParsed cmd rest =>
        (case bridge_import_command_with_env env cmd of
         | SOME imported => BImportedCommandParsed imported rest
         | NONE => BImportedCommandImportError)
    | BCommandParseError n => BImportedCommandParseError n
End

Definition bridge_import_parsed_program_tokens_with_env_def:
  bridge_import_parsed_program_tokens_with_env env fuel toks =
    case bridge_parse_program_tokens_fuel fuel toks of
    | BProgramParsed cmds => bridge_import_command_list_with_env env cmds
    | BProgramParseError n => NONE
End

Datatype:
  bridge_imported_program_parse_result =
    BImportedProgramParsed (bridge_numeric_command list)
  | BImportedProgramParseError num
  | BImportedProgramImportError
End

Definition bridge_import_parsed_program_tokens_result_with_env_def:
  bridge_import_parsed_program_tokens_result_with_env env fuel toks =
    case bridge_parse_program_tokens_fuel fuel toks of
    | BProgramParsed cmds =>
        (case bridge_import_command_list_with_env env cmds of
         | SOME imported => BImportedProgramParsed imported
         | NONE => BImportedProgramImportError)
    | BProgramParseError n => BImportedProgramParseError n
End

Theorem bridge_import_parsed_command_tokens_result_with_env_success:
  ∀env fuel toks cmd rest.
    bridge_import_parsed_command_tokens_result_with_env env fuel toks =
      BImportedCommandParsed cmd rest ⇔
    bridge_import_parsed_command_tokens_with_env env fuel toks =
      SOME (cmd, rest)
Proof
  rw[bridge_import_parsed_command_tokens_result_with_env_def,
     bridge_import_parsed_command_tokens_with_env_def] \\
  every_case_tac \\
  rw[]
QED

Theorem bridge_import_parsed_program_tokens_result_with_env_success:
  ∀env fuel toks cmds.
    bridge_import_parsed_program_tokens_result_with_env env fuel toks =
      BImportedProgramParsed cmds ⇔
    bridge_import_parsed_program_tokens_with_env env fuel toks =
      SOME cmds
Proof
  rw[bridge_import_parsed_program_tokens_result_with_env_def,
     bridge_import_parsed_program_tokens_with_env_def] \\
  every_case_tac \\
  rw[]
QED

Theorem bridge_import_parsed_command_tokens_with_env_export_sound:
  ∀env fuel toks imported rest.
    bridge_dyn_env_ok env ∧
    bridge_import_parsed_command_tokens_with_env env fuel toks =
      SOME (imported, rest) ⇒
    ∃surface.
      bridge_parse_command_tokens_fuel fuel toks =
        BCommandParsed surface rest ∧
      bridge_export_command_with_env env imported = SOME surface
Proof
  rw[bridge_import_parsed_command_tokens_with_env_def] \\
  gvs[AllCaseEqs()] \\
  metis_tac[bridge_import_command_with_env_export_roundtrip]
QED

Theorem bridge_import_parsed_program_tokens_with_env_export_sound:
  ∀env fuel toks imported.
    bridge_dyn_env_ok env ∧
    bridge_import_parsed_program_tokens_with_env env fuel toks =
      SOME imported ⇒
    ∃surface.
      bridge_parse_program_tokens_fuel fuel toks = BProgramParsed surface ∧
      bridge_export_command_list_with_env env imported = SOME surface
Proof
  rw[bridge_import_parsed_program_tokens_with_env_def] \\
  gvs[AllCaseEqs()] \\
  metis_tac[bridge_import_command_list_with_env_export_roundtrip]
QED

Theorem bridge_import_parsed_command_tokens_with_env_run_example:
  bridge_import_parsed_command_tokens_with_env [(strlit"Foo", 1000)] 10
    [BTokBang; BTokAtom (BSym (strlit"Foo"))] =
  SOME (BNumCmdRun (metta_m1$Sym 1000), [])
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_command_tokens_result_with_env_run_example:
  bridge_import_parsed_command_tokens_result_with_env [(strlit"Foo", 1000)] 10
    [BTokBang; BTokAtom (BSym (strlit"Foo"))] =
  BImportedCommandParsed (BNumCmdRun (metta_m1$Sym 1000)) []
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_program_tokens_result_with_env_example:
  bridge_import_parsed_program_tokens_result_with_env [(strlit"Foo", 1000)] 10
    [BTokAtom (BSym (strlit"Foo"));
     BTokBang; BTokAtom (BSym (strlit"+"))] =
  BImportedProgramParsed
    [BNumCmdAdd (metta_m1$Sym 1000); BNumCmdRun (metta_m1$Sym 11)]
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_program_tokens_with_env_example:
  bridge_import_parsed_program_tokens_with_env [(strlit"Foo", 1000)] 10
    [BTokAtom (BSym (strlit"Foo"));
     BTokBang; BTokAtom (BSym (strlit"+"))] =
  SOME [BNumCmdAdd (metta_m1$Sym 1000); BNumCmdRun (metta_m1$Sym 11)]
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_command_tokens_with_env_unknown_negative_example:
  bridge_import_parsed_command_tokens_with_env [] 10
    [BTokBang; BTokAtom (BSym (strlit"Foo"))] = NONE
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_command_tokens_result_with_env_negative_example:
  bridge_import_parsed_command_tokens_result_with_env [] 10
    [BTokBang; BTokAtom (BSym (strlit"Foo"))] =
  BImportedCommandImportError ∧
  bridge_import_parsed_command_tokens_result_with_env [] 10 [] =
  BImportedCommandParseError 3
Proof
  EVAL_TAC
QED

Theorem bridge_import_parsed_program_tokens_result_with_env_negative_example:
  bridge_import_parsed_program_tokens_result_with_env [] 10
    [BTokAtom (BSym (strlit"Foo"))] =
  BImportedProgramImportError ∧
  bridge_import_parsed_program_tokens_result_with_env [] 0
    [BTokAtom (BSym (strlit"+"))] =
  BImportedProgramParseError 99
Proof
  EVAL_TAC
QED

Theorem bridge_export_command_with_env_dynamic_example:
  bridge_export_command_with_env [(strlit"Foo", 1000)]
    (BNumCmdAdd (metta_m1$Sym 1000)) =
    SOME (BCmdAdd (BSym (strlit"Foo"))) ∧
  bridge_export_command_list_with_env [(strlit"Foo", 1000)]
    [BNumCmdAdd (metta_m1$Sym 1000);
     BNumCmdRun (metta_m1$Sym 11)] =
    SOME [BCmdAdd (BSym (strlit"Foo"));
          BCmdRun (BSym (strlit"+"))]
Proof
  EVAL_TAC
QED

Theorem bridge_export_command_with_env_unknown_negative_example:
  bridge_export_command_with_env []
    (BNumCmdRun (metta_m1$Sym 1000)) = NONE ∧
  bridge_export_command_list_with_env []
    [BNumCmdRun (metta_m1$Sym 1000)] = NONE
Proof
  EVAL_TAC
QED

Definition bridge_expected_result_atoms_def:
  bridge_expected_result_atoms (metta_m1$Expr xs) = xs ∧
  bridge_expected_result_atoms atom = [atom]
End

Definition bridge_eval_top_def:
  bridge_eval_top fuel space atom =
    visible_results (eval_m1_rec fuel space atom)
End

Definition bridge_eval_env_def:
  bridge_eval_env env fuel self spaces atom =
    (case atom of
     | metta_m1$Expr
         [metta_m1$Sym match_sym; metta_m1$Sym space_name; pattern; templ] =>
         if bridge_import_symbol_with_env env (strlit"match") = SOME match_sym
         then
           match_context_space self spaces (metta_m1$Sym space_name)
             pattern templ
         else bridge_eval_top fuel self atom
     | metta_m1$Expr [metta_m1$Sym head_sym; lhs; rhs] =>
         if bridge_import_symbol_with_env env (strlit"assertEqual") =
              SOME head_sym
         then
           if bridge_eval_env env fuel self spaces lhs =
              bridge_eval_env env fuel self spaces rhs
           then [metta_m1$Expr []]
           else [error_atom atom (metta_m1$Sym 10)]
         else if bridge_import_symbol_with_env env
                   (strlit"assertEqualToResult") =
                   SOME head_sym
         then
           if bridge_eval_env env fuel self spaces lhs =
              bridge_expected_result_atoms rhs
           then [metta_m1$Expr []]
           else [error_atom atom (metta_m1$Sym 10)]
         else
           (case rhs of
            | metta_m1$Sym space_name =>
                if bridge_import_symbol_with_env env (strlit"evalc") =
                     SOME head_sym
                then
                  evalc_context fuel self spaces lhs
                    (metta_m1$Sym space_name)
                else bridge_eval_top fuel self atom
            | _ => bridge_eval_top fuel self atom)
     | _ => bridge_eval_top fuel self atom)
Termination
  WF_REL_TAC
    ‘measure (λ(env,fuel,self,spaces,atom). atom_size atom)’ \\
  rw[]
End

Definition bridge_run_effect_def:
  bridge_run_effect env fuel self spaces atom =
    case atom of
    | metta_m1$Expr
        [metta_m1$Sym bind_sym; metta_m1$Sym space_name;
         metta_m1$Expr [metta_m1$Sym new_space_sym]] =>
        if bridge_import_symbol_with_env env (strlit"bind!") = SOME bind_sym ∧
           bridge_import_symbol_with_env env (strlit"new-space") =
             SOME new_space_sym
        then
          (self, bind_empty_named_space space_name spaces,
           [metta_m1$Expr []])
        else (self, spaces, bridge_eval_env env fuel self spaces atom)
    | metta_m1$Expr
        [metta_m1$Sym add_sym; metta_m1$Sym 5; new_atom] =>
        if bridge_import_symbol_with_env env (strlit"add-atom") = SOME add_sym
        then (self ++ [new_atom], spaces, [metta_m1$Expr []])
        else (self, spaces, bridge_eval_env env fuel self spaces atom)
    | metta_m1$Expr
        [metta_m1$Sym add_sym; metta_m1$Sym space_name; new_atom] =>
        if bridge_import_symbol_with_env env (strlit"add-atom") = SOME add_sym
        then
          (case add_atom_to_named_space space_name new_atom spaces of
           | SOME spaces2 => (self, spaces2, [metta_m1$Expr []])
           | NONE => (self, spaces, [error_atom atom (metta_m1$Sym 10)]))
        else (self, spaces, bridge_eval_env env fuel self spaces atom)
    | _ => (self, spaces, bridge_eval_env env fuel self spaces atom)
End

Datatype:
  bridge_state_effect_result =
    BStateEffectResult
      (metta_m1$atom list) ((num # (metta_m1$atom list)) list)
      ((metta_m1$atom list))
End

Definition bridge_try_run_state_effect_def:
  bridge_try_run_state_effect env self spaces atom =
    case atom of
    | metta_m1$Expr
        [metta_m1$Sym bind_sym; metta_m1$Sym space_name;
         metta_m1$Expr [metta_m1$Sym new_space_sym]] =>
        if bridge_import_symbol_with_env env (strlit"bind!") = SOME bind_sym ∧
           bridge_import_symbol_with_env env (strlit"new-space") =
             SOME new_space_sym
        then
          SOME
            (BStateEffectResult self
              (bind_empty_named_space space_name spaces)
              [metta_m1$Expr []])
        else NONE
    | metta_m1$Expr
        [metta_m1$Sym add_sym; metta_m1$Sym 5; new_atom] =>
        if bridge_import_symbol_with_env env (strlit"add-atom") = SOME add_sym
        then
          SOME
            (BStateEffectResult (self ++ [new_atom]) spaces
              [metta_m1$Expr []])
        else NONE
    | metta_m1$Expr
        [metta_m1$Sym add_sym; metta_m1$Sym space_name; new_atom] =>
        if bridge_import_symbol_with_env env (strlit"add-atom") = SOME add_sym
        then
          (case add_atom_to_named_space space_name new_atom spaces of
           | SOME spaces2 =>
               SOME
                 (BStateEffectResult self spaces2 [metta_m1$Expr []])
           | NONE =>
               SOME
                 (BStateEffectResult self spaces
                   [error_atom atom (metta_m1$Sym 10)]))
        else NONE
    | _ => NONE
End

Theorem bridge_try_run_state_effect_success_agrees_with_run_effect:
  ∀env fuel self spaces atom state_res.
    bridge_try_run_state_effect env self spaces atom = SOME state_res ⇒
    ∃self1 spaces1 outs.
      state_res = BStateEffectResult self1 spaces1 outs ∧
      bridge_run_effect env fuel self spaces atom = (self1, spaces1, outs)
Proof
  rw[bridge_try_run_state_effect_def, bridge_run_effect_def] \\
  every_case_tac \\
  gvs[]
QED

Theorem bridge_try_run_state_effect_none_fallback:
  ∀env fuel self spaces atom.
    bridge_try_run_state_effect env self spaces atom = NONE ⇒
    bridge_run_effect env fuel self spaces atom =
      (self, spaces, bridge_eval_env env fuel self spaces atom)
Proof
  rw[bridge_try_run_state_effect_def, bridge_run_effect_def] \\
  every_case_tac \\
  gvs[]
QED

Theorem bridge_try_run_state_effect_dynamic_example:
  bridge_try_run_state_effect
    [(strlit"bind!", 1000); (strlit"new-space", 1001);
     (strlit"add-atom", 1002); (strlit"Box", 1003);
     (strlit"Foo", 1004)]
    [] []
    (metta_m1$Expr
      [metta_m1$Sym 1000; metta_m1$Sym 1003;
       metta_m1$Expr [metta_m1$Sym 1001]]) =
    SOME (BStateEffectResult [] [(1003, [])] [metta_m1$Expr []]) ∧
  bridge_try_run_state_effect
    [(strlit"bind!", 1000); (strlit"new-space", 1001);
     (strlit"add-atom", 1002); (strlit"Box", 1003);
     (strlit"Foo", 1004)]
    [] [(1003, [])]
    (metta_m1$Expr
      [metta_m1$Sym 1002; metta_m1$Sym 1003; metta_m1$Sym 1004]) =
    SOME
      (BStateEffectResult [] [(1003, [metta_m1$Sym 1004])]
        [metta_m1$Expr []])
Proof
  EVAL_TAC
QED

Theorem bridge_try_run_state_effect_negative_example:
  bridge_try_run_state_effect
    [(strlit"add-atom", 1000); (strlit"Box", 1001); (strlit"Foo", 1002)]
    [] []
    (metta_m1$Expr
      [metta_m1$Sym 1000; metta_m1$Sym 1001; metta_m1$Sym 1002]) =
    SOME
      (BStateEffectResult [] []
        [error_atom
           (metta_m1$Expr
             [metta_m1$Sym 1000; metta_m1$Sym 1001; metta_m1$Sym 1002])
           (metta_m1$Sym 10)]) ∧
  bridge_try_run_state_effect [] [] [] (metta_m1$Sym 11) = NONE
Proof
  EVAL_TAC
QED

Definition bridge_run_program_env_def:
  bridge_run_program_env env fuel self spaces [] = (self, spaces, []) ∧
  bridge_run_program_env env fuel self spaces
    (BNumCmdAdd atom :: rest) =
      bridge_run_program_env env fuel (self ++ [atom]) spaces rest ∧
  bridge_run_program_env env fuel self spaces
    (BNumCmdRun atom :: rest) =
      (case bridge_run_effect env fuel self spaces atom of
       | (self1, spaces1, rs) =>
           (case bridge_run_program_env env fuel self1 spaces1 rest of
            | (self2, spaces2, outs) => (self2, spaces2, rs :: outs)))
End

Definition bridge_run_program_def:
  bridge_run_program env fuel space commands =
    case bridge_run_program_env env fuel space [] commands of
    | (self, spaces, outs) => (self, outs)
End

Datatype:
  bridge_state_program_result =
    BStateProgramResult
      (metta_m1$atom list) ((num # (metta_m1$atom list)) list)
      ((metta_m1$atom list) list)
End

Definition bridge_run_program_state_prefix_def:
  bridge_run_program_state_prefix env fuel self spaces [] =
    SOME (BStateProgramResult self spaces []) ∧
  bridge_run_program_state_prefix env fuel self spaces
    (BNumCmdAdd atom :: rest) =
      bridge_run_program_state_prefix env fuel (self ++ [atom]) spaces rest ∧
  bridge_run_program_state_prefix env fuel self spaces
    (BNumCmdRun atom :: rest) =
      (case bridge_try_run_state_effect env self spaces atom of
       | SOME (BStateEffectResult self1 spaces1 rs) =>
           (case bridge_run_program_state_prefix
                   env fuel self1 spaces1 rest of
            | SOME (BStateProgramResult self2 spaces2 outs) =>
                SOME
                  (BStateProgramResult self2 spaces2 (rs :: outs))
            | NONE => NONE)
       | NONE => NONE)
End

Theorem bridge_run_program_state_prefix_agrees:
  ∀env fuel self spaces cmds self1 spaces1 outs.
    bridge_run_program_state_prefix env fuel self spaces cmds =
      SOME (BStateProgramResult self1 spaces1 outs) ⇒
    bridge_run_program_env env fuel self spaces cmds =
      (self1, spaces1, outs)
Proof
  Induct_on ‘cmds’
  >- rw[bridge_run_program_state_prefix_def,
        bridge_run_program_env_def]
  \\ Cases_on ‘h’
  >- (
    rw[bridge_run_program_state_prefix_def,
       bridge_run_program_env_def] \\
    qpat_x_assum
      ‘∀env fuel self spaces self1 spaces1 outs.
         bridge_run_program_state_prefix env fuel self spaces cmds =
           SOME (BStateProgramResult self1 spaces1 outs) ⇒
         bridge_run_program_env env fuel self spaces cmds =
           (self1,spaces1,outs)’
      drule \\
    rw[] \\
    gvs[])
  \\ rw[bridge_run_program_state_prefix_def,
        bridge_run_program_env_def]
  \\ every_case_tac
  \\ gvs[]
  \\ drule bridge_try_run_state_effect_success_agrees_with_run_effect
  \\ rw[]
  \\ qpat_x_assum
       ‘∀env fuel self spaces self1 spaces1 outs.
          bridge_run_program_state_prefix env fuel self spaces cmds =
            SOME (BStateProgramResult self1 spaces1 outs) ⇒
          bridge_run_program_env env fuel self spaces cmds =
            (self1,spaces1,outs)’
       drule
  \\ rw[]
  \\ gvs[]
QED

Theorem bridge_run_program_state_prefix_sound:
  ∀env fuel self spaces cmds state_res.
    bridge_run_program_state_prefix env fuel self spaces cmds =
      SOME state_res ⇒
    ∃self1 spaces1 outs.
      state_res = BStateProgramResult self1 spaces1 outs ∧
      bridge_run_program_env env fuel self spaces cmds =
        (self1, spaces1, outs)
Proof
  Cases_on ‘state_res’ \\
  rw[] \\
  metis_tac[bridge_run_program_state_prefix_agrees]
QED

Theorem bridge_run_program_state_prefix_dynamic_example:
  bridge_run_program_state_prefix
    [(strlit"bind!", 1000); (strlit"new-space", 1001);
     (strlit"add-atom", 1002); (strlit"Box", 1003);
     (strlit"Foo", 1004)]
    7 [] []
    [BNumCmdAdd (metta_m1$Sym 1004);
     BNumCmdRun
       (metta_m1$Expr
         [metta_m1$Sym 1000; metta_m1$Sym 1003;
          metta_m1$Expr [metta_m1$Sym 1001]]);
     BNumCmdRun
       (metta_m1$Expr
         [metta_m1$Sym 1002; metta_m1$Sym 1003;
          metta_m1$Sym 1004])] =
  SOME
    (BStateProgramResult
      [metta_m1$Sym 1004]
      [(1003, [metta_m1$Sym 1004])]
      [[metta_m1$Expr []]; [metta_m1$Expr []]])
Proof
  EVAL_TAC
QED

Theorem bridge_run_program_state_prefix_negative_example:
  bridge_run_program_state_prefix [] 7 [] []
    [BNumCmdRun (metta_m1$Sym 11)] = NONE
Proof
  EVAL_TAC
QED

Datatype:
  bridge_imported_program_run_result =
    BImportedProgramRunResult
      (metta_m1$atom list) ((num # (metta_m1$atom list)) list)
      ((metta_m1$atom list) list)
  | BImportedProgramRunParseError num
  | BImportedProgramRunImportError
End

Definition bridge_run_imported_program_tokens_result_with_env_def:
  bridge_run_imported_program_tokens_result_with_env
    env parse_fuel eval_fuel toks =
    case bridge_import_parsed_program_tokens_result_with_env env parse_fuel toks of
    | BImportedProgramParsed cmds =>
        (case bridge_run_program_env env eval_fuel [] [] cmds of
         | (self, spaces, outs) =>
             BImportedProgramRunResult self spaces outs)
    | BImportedProgramParseError n => BImportedProgramRunParseError n
    | BImportedProgramImportError => BImportedProgramRunImportError
End

Theorem bridge_run_imported_program_tokens_result_with_env_success:
  ∀env parse_fuel eval_fuel toks cmds.
    bridge_import_parsed_program_tokens_result_with_env env parse_fuel toks =
      BImportedProgramParsed cmds ⇒
    bridge_run_imported_program_tokens_result_with_env
      env parse_fuel eval_fuel toks =
      (case bridge_run_program_env env eval_fuel [] [] cmds of
       | (self, spaces, outs) =>
           BImportedProgramRunResult self spaces outs)
Proof
  rw[bridge_run_imported_program_tokens_result_with_env_def]
QED

Theorem bridge_run_program_env_assert_equal_dynamic_example:
  bridge_run_program_env
    [(strlit"assertEqual", 1000); (strlit"Foo", 1001)] 7 [] []
    [BNumCmdAdd (metta_m1$Sym 1001);
     BNumCmdRun
       (metta_m1$Expr
         [metta_m1$Sym 1000; metta_m1$Sym 1001; metta_m1$Sym 1001])] =
  ([metta_m1$Sym 1001], [], [[metta_m1$Expr []]])
Proof
  EVAL_TAC
QED

Theorem bridge_run_effect_named_space_dynamic_example:
  bridge_run_effect
    [(strlit"bind!", 1000); (strlit"new-space", 1001);
     (strlit"add-atom", 1002); (strlit"Box", 1003);
     (strlit"Foo", 1004)]
    7 [] []
    (metta_m1$Expr
      [metta_m1$Sym 1000; metta_m1$Sym 1003;
       metta_m1$Expr [metta_m1$Sym 1001]]) =
    ([], [(1003, [])], [metta_m1$Expr []]) ∧
  bridge_run_effect
    [(strlit"bind!", 1000); (strlit"new-space", 1001);
     (strlit"add-atom", 1002); (strlit"Box", 1003);
     (strlit"Foo", 1004)]
    7 [] [(1003, [])]
    (metta_m1$Expr
      [metta_m1$Sym 1002; metta_m1$Sym 1003; metta_m1$Sym 1004]) =
    ([], [(1003, [metta_m1$Sym 1004])], [metta_m1$Expr []])
Proof
  EVAL_TAC
QED

Theorem bridge_run_effect_missing_named_space_negative_example:
  bridge_run_effect
    [(strlit"add-atom", 1000); (strlit"Box", 1001); (strlit"Foo", 1002)]
    7 [] []
    (metta_m1$Expr
      [metta_m1$Sym 1000; metta_m1$Sym 1001; metta_m1$Sym 1002]) =
    ([],
     [],
     [error_atom
        (metta_m1$Expr
          [metta_m1$Sym 1000; metta_m1$Sym 1001; metta_m1$Sym 1002])
        (metta_m1$Sym 10)])
Proof
  EVAL_TAC
QED

Theorem bridge_run_imported_program_tokens_result_with_env_dynamic_example:
  bridge_run_imported_program_tokens_result_with_env
    [(strlit"assertEqual", 1000); (strlit"Foo", 1001)]
    20 7
    [BTokAtom (BSym (strlit"Foo"));
     BTokBang; BTokLParen;
     BTokAtom (BSym (strlit"assertEqual"));
     BTokAtom (BSym (strlit"Foo"));
     BTokAtom (BSym (strlit"Foo"));
     BTokRParen] =
    BImportedProgramRunResult
      [metta_m1$Sym 1001] [] [[metta_m1$Expr []]]
Proof
  EVAL_TAC
QED

Datatype:
  bridge_source_command =
    BSrcCmdAdd bridge_source_atom
  | BSrcCmdRun bridge_source_atom
End

Datatype:
  bridge_source_command_parse_result =
    BSourceCommandParsed bridge_source_command (bridge_source_token list)
  | BSourceCommandParseError num
End

Datatype:
  bridge_source_program_parse_result =
    BSourceProgramParsed (bridge_source_command list)
  | BSourceProgramParseError num
End

Definition bridge_import_source_atom_with_env_def:
  bridge_import_source_atom_with_env dyn_env var_env str_env (SrcSym s) =
    (case bridge_import_symbol_with_env dyn_env s of
     | SOME n => SOME (metta_m1$Sym n)
     | NONE => NONE) ∧
  bridge_import_source_atom_with_env dyn_env var_env str_env (SrcVar v) =
    (case ALOOKUP var_env v of
     | SOME n => SOME (metta_m1$Var n)
     | NONE => NONE) ∧
  bridge_import_source_atom_with_env dyn_env var_env str_env (SrcInt i) =
    SOME (metta_m1$IntLit i) ∧
  bridge_import_source_atom_with_env dyn_env var_env str_env (SrcStr s) =
    (case ALOOKUP str_env s of
     | SOME n => SOME (metta_m1$StrLit n)
     | NONE => NONE) ∧
  bridge_import_source_atom_with_env dyn_env var_env str_env (SrcExpr xs) =
    (case bridge_import_source_atom_list_with_env dyn_env var_env str_env xs of
     | SOME ys => SOME (metta_m1$Expr ys)
     | NONE => NONE) ∧
  bridge_import_source_atom_list_with_env dyn_env var_env str_env [] = SOME [] ∧
  bridge_import_source_atom_list_with_env dyn_env var_env str_env (x :: xs) =
    (case bridge_import_source_atom_with_env dyn_env var_env str_env x of
     | SOME y =>
         (case bridge_import_source_atom_list_with_env
                 dyn_env var_env str_env xs of
          | SOME ys => SOME (y :: ys)
          | NONE => NONE)
     | NONE => NONE)
End

Definition bridge_import_source_command_with_env_def:
  bridge_import_source_command_with_env dyn_env var_env str_env
    (BSrcCmdAdd atom) =
    (case bridge_import_source_atom_with_env dyn_env var_env str_env atom of
     | SOME imported => SOME (BNumCmdAdd imported)
     | NONE => NONE) ∧
  bridge_import_source_command_with_env dyn_env var_env str_env
    (BSrcCmdRun atom) =
    (case bridge_import_source_atom_with_env dyn_env var_env str_env atom of
     | SOME imported => SOME (BNumCmdRun imported)
     | NONE => NONE)
End

Definition bridge_import_source_command_list_with_env_def:
  bridge_import_source_command_list_with_env dyn_env var_env str_env [] =
    SOME [] ∧
  bridge_import_source_command_list_with_env dyn_env var_env str_env
    (cmd :: cmds) =
    (case bridge_import_source_command_with_env dyn_env var_env str_env cmd of
     | SOME imported =>
         (case bridge_import_source_command_list_with_env
                 dyn_env var_env str_env cmds of
          | SOME rest => SOME (imported :: rest)
          | NONE => NONE)
     | NONE => NONE)
End

Theorem bridge_import_source_atom_with_env_dynamic_example:
  bridge_import_source_atom_with_env
    [(strlit"Foo", 1000)] [(strlit"x", 0)] [(strlit"hi", 7)]
    (SrcExpr [SrcSym (strlit"return");
              SrcSym (strlit"Foo");
              SrcVar (strlit"x");
              SrcStr (strlit"hi")]) =
  SOME
    (metta_m1$Expr
      [metta_m1$Sym 19; metta_m1$Sym 1000;
       metta_m1$Var 0; metta_m1$StrLit 7])
Proof
  EVAL_TAC
QED

Theorem bridge_import_source_atom_with_env_negative_example:
  bridge_import_source_atom_with_env [] [] []
    (SrcSym (strlit"Foo")) = NONE ∧
  bridge_import_source_atom_with_env [] [] []
    (SrcVar (strlit"x")) = NONE ∧
  bridge_import_source_atom_with_env [] [] []
    (SrcStr (strlit"hi")) = NONE
Proof
  EVAL_TAC
QED

Theorem bridge_import_source_command_list_with_env_dynamic_example:
  bridge_import_source_command_list_with_env
    [(strlit"assertEqual", 1000); (strlit"Foo", 1001)] [] []
    [BSrcCmdAdd (SrcSym (strlit"Foo"));
     BSrcCmdRun
       (SrcExpr [SrcSym (strlit"assertEqual");
                 SrcSym (strlit"Foo");
                 SrcSym (strlit"Foo")])] =
  SOME
      [BNumCmdAdd (metta_m1$Sym 1001);
       BNumCmdRun
         (metta_m1$Expr
           [metta_m1$Sym 1000; metta_m1$Sym 1001; metta_m1$Sym 1001])]
Proof
  EVAL_TAC
QED

Definition bridge_source_lookup_named_space_def:
  bridge_source_lookup_named_space name [] = NONE ∧
  bridge_source_lookup_named_space name ((key, stored) :: rest) =
    if name = key then SOME stored
    else bridge_source_lookup_named_space name rest
End

Definition bridge_source_set_named_space_def:
  bridge_source_set_named_space name stored [] = [(name, stored)] ∧
  bridge_source_set_named_space name stored ((key, old) :: rest) =
    if name = key then (name, stored) :: rest
    else (key, old) :: bridge_source_set_named_space name stored rest
End

Definition bridge_source_error_atom_def:
  bridge_source_error_atom subject reason =
    SrcExpr [SrcSym (strlit"Error"); subject; SrcSym reason]
End

Definition bridge_import_source_named_spaces_with_env_def:
  bridge_import_source_named_spaces_with_env dyn_env var_env str_env [] =
    SOME [] ∧
  bridge_import_source_named_spaces_with_env dyn_env var_env str_env
    ((name, stored) :: rest) =
    (case bridge_import_symbol_with_env dyn_env name of
     | SOME imported_name =>
         (case bridge_import_source_atom_list_with_env
                 dyn_env var_env str_env stored of
          | SOME imported_stored =>
              (case bridge_import_source_named_spaces_with_env
                      dyn_env var_env str_env rest of
               | SOME imported_rest =>
                   SOME ((imported_name, imported_stored) :: imported_rest)
               | NONE => NONE)
          | NONE => NONE)
     | NONE => NONE)
End

Datatype:
  bridge_source_state_effect_result =
    BSourceStateEffectResult
      (bridge_source_atom list)
      ((mlstring # (bridge_source_atom list)) list)
      (bridge_source_atom list)
End

Definition bridge_source_try_run_state_effect_def:
  bridge_source_try_run_state_effect self spaces atom =
    case atom of
    | SrcExpr
        [SrcSym bind_sym; SrcSym space_name;
         SrcExpr [SrcSym new_space_sym]] =>
        if bind_sym = strlit"bind!" ∧ new_space_sym = strlit"new-space"
        then
          SOME
            (BSourceStateEffectResult self
              (bridge_source_set_named_space space_name [] spaces)
              [SrcExpr []])
        else NONE
    | SrcExpr [SrcSym add_sym; SrcSym self_name; new_atom] =>
        if add_sym = strlit"add-atom" ∧ self_name = strlit"&self"
        then
          SOME
            (BSourceStateEffectResult (self ++ [new_atom]) spaces
              [SrcExpr []])
        else if add_sym = strlit"add-atom"
        then
          (case bridge_source_lookup_named_space self_name spaces of
           | SOME stored =>
               SOME
                 (BSourceStateEffectResult self
                   (bridge_source_set_named_space self_name
                     (stored ++ [new_atom]) spaces)
                   [SrcExpr []])
           | NONE =>
               SOME
                 (BSourceStateEffectResult self spaces
                   [bridge_source_error_atom atom (strlit"BadArgType")]))
        else NONE
    | _ => NONE
End

Definition bridge_import_source_state_effect_result_with_env_def:
  bridge_import_source_state_effect_result_with_env dyn_env var_env str_env
    (BSourceStateEffectResult self spaces outs) =
    case bridge_import_source_atom_list_with_env dyn_env var_env str_env self of
    | SOME imported_self =>
        (case bridge_import_source_named_spaces_with_env
                dyn_env var_env str_env spaces of
         | SOME imported_spaces =>
             (case bridge_import_source_atom_list_with_env
                     dyn_env var_env str_env outs of
              | SOME imported_outs =>
                  SOME
                    (BStateEffectResult imported_self imported_spaces
                      imported_outs)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE
End

Theorem bridge_import_source_atom_list_with_env_snoc:
  ∀dyn_env var_env str_env xs ys x y.
    bridge_import_source_atom_list_with_env dyn_env var_env str_env xs =
      SOME ys ∧
    bridge_import_source_atom_with_env dyn_env var_env str_env x = SOME y ⇒
    bridge_import_source_atom_list_with_env dyn_env var_env str_env
      (xs ++ [x]) = SOME (ys ++ [y])
Proof
  Induct_on ‘xs’
  >- simp[bridge_import_source_atom_with_env_def]
  \\ simp[bridge_import_source_atom_with_env_def]
  \\ rpt strip_tac
  \\ every_case_tac
  \\ gvs[bridge_import_source_atom_with_env_def]
  \\ res_tac
  \\ gvs[]
QED

Theorem bridge_source_try_run_state_effect_self_non_singleton_refines_numeric:
  ∀dyn_env var_env str_env self spaces new_atom
    selfi spacesi newatomi addi.
    bridge_import_source_atom_list_with_env dyn_env var_env str_env self =
      SOME selfi ∧
    bridge_import_source_named_spaces_with_env dyn_env var_env str_env spaces =
      SOME spacesi ∧
    bridge_import_source_atom_with_env dyn_env var_env str_env new_atom =
      SOME newatomi ∧
    (¬∃ns. newatomi = metta_m1$Expr [metta_m1$Sym ns]) ∧
    bridge_import_symbol_with_env dyn_env (strlit"add-atom") = SOME addi ⇒
    bridge_import_source_state_effect_result_with_env
      dyn_env var_env str_env
      (BSourceStateEffectResult (self ++ [new_atom]) spaces [SrcExpr []]) =
      SOME
        (BStateEffectResult (selfi ++ [newatomi]) spacesi
          [metta_m1$Expr []]) ∧
    bridge_try_run_state_effect dyn_env selfi spacesi
      (metta_m1$Expr [metta_m1$Sym addi; metta_m1$Sym 5; newatomi]) =
      SOME
        (BStateEffectResult (selfi ++ [newatomi]) spacesi
          [metta_m1$Expr []])
Proof
  rw[bridge_import_source_state_effect_result_with_env_def,
     bridge_try_run_state_effect_def] \\
  imp_res_tac bridge_import_source_atom_list_with_env_snoc \\
  every_case_tac \\
  gvs[bridge_import_source_atom_with_env_def]
QED

Theorem bridge_source_try_run_state_effect_dynamic_example:
  bridge_source_try_run_state_effect
    [SrcSym (strlit"Foo")]
    [(strlit"Space", [SrcInt 1])]
    (SrcExpr
      [SrcSym (strlit"add-atom"); SrcSym (strlit"Space");
       SrcInt 2]) =
  SOME
    (BSourceStateEffectResult
      [SrcSym (strlit"Foo")]
      [(strlit"Space", [SrcInt 1; SrcInt 2])]
      [SrcExpr []])
Proof
  EVAL_TAC
QED

Theorem bridge_source_try_run_state_effect_negative_example:
  bridge_source_try_run_state_effect [] [] (SrcSym (strlit"+")) = NONE
Proof
  EVAL_TAC
QED

Datatype:
  bridge_source_program_run_result =
    BSourceProgramRunResult
      (metta_m1$atom list) ((num # (metta_m1$atom list)) list)
      ((metta_m1$atom list) list)
  | BSourceProgramRunParseError mlstring
  | BSourceProgramRunImportError
End

Definition bridge_parse_source_command_tokens_fuel_def:
  bridge_parse_source_command_tokens_fuel fuel toks =
    case toks of
    | BSrcTokBang :: rest =>
        (case bridge_parse_source_atom_tokens_fuel fuel rest of
         | BSourceFullAtomParsed atom rest2 =>
             BSourceCommandParsed (BSrcCmdRun atom) rest2
         | BSourceFullAtomParseError n => BSourceCommandParseError n)
    | _ =>
        (case bridge_parse_source_atom_tokens_fuel fuel toks of
         | BSourceFullAtomParsed atom rest =>
             BSourceCommandParsed (BSrcCmdAdd atom) rest
         | BSourceFullAtomParseError n => BSourceCommandParseError n)
End

Definition bridge_parse_source_program_tokens_fuel_def:
  bridge_parse_source_program_tokens_fuel 0 toks =
    (case toks of
     | [] => BSourceProgramParsed []
     | _ => BSourceProgramParseError 99) ∧
  bridge_parse_source_program_tokens_fuel (SUC fuel) toks =
    (case toks of
     | [] => BSourceProgramParsed []
     | _ =>
        (case bridge_parse_source_command_tokens_fuel (SUC fuel) toks of
         | BSourceCommandParsed cmd rest =>
             (case bridge_parse_source_program_tokens_fuel fuel rest of
              | BSourceProgramParsed cmds =>
                  BSourceProgramParsed (cmd :: cmds)
              | BSourceProgramParseError n => BSourceProgramParseError n)
         | BSourceCommandParseError n => BSourceProgramParseError n))
End

Definition bridge_parse_source_program_chars_fuel_def:
  bridge_parse_source_program_chars_fuel lex_fuel parse_fuel chars =
    case bridge_tokenize_source_chars_fuel lex_fuel chars of
    | BSourceLexed toks =>
        bridge_parse_source_program_tokens_fuel parse_fuel toks
    | BSourceLexError n => BSourceProgramParseError n
End

Definition bridge_parse_source_program_string_fuel_def:
  bridge_parse_source_program_string_fuel lex_fuel parse_fuel text =
    bridge_parse_source_program_chars_fuel
      lex_fuel parse_fuel (explode text)
End

Datatype:
  bridge_proto_command =
    BProtoCmdAdd bridge_proto_atom
  | BProtoCmdRun bridge_proto_atom
End

Datatype:
  bridge_proto_command_parse_result =
    BProtoCommandParsed bridge_proto_command (bridge_proto_token list)
  | BProtoCommandParseError num
End

Datatype:
  bridge_proto_program_parse_result =
    BProtoProgramParsed (bridge_proto_command list)
  | BProtoProgramParseError num
End

Definition bridge_parse_proto_command_tokens_fuel_def:
  bridge_parse_proto_command_tokens_fuel fuel toks =
    case toks of
    | BProtoTokBang :: rest =>
        (case bridge_parse_proto_atom_tokens_fuel fuel rest of
         | BProtoFullAtomParsed atom rest2 =>
             BProtoCommandParsed (BProtoCmdRun atom) rest2
         | BProtoFullAtomParseError n => BProtoCommandParseError n)
    | _ =>
        (case bridge_parse_proto_atom_tokens_fuel fuel toks of
         | BProtoFullAtomParsed atom rest =>
             BProtoCommandParsed (BProtoCmdAdd atom) rest
         | BProtoFullAtomParseError n => BProtoCommandParseError n)
End

Definition bridge_parse_proto_program_tokens_fuel_def:
  bridge_parse_proto_program_tokens_fuel 0 toks =
    (case toks of
     | [] => BProtoProgramParsed []
     | _ => BProtoProgramParseError 99) ∧
  bridge_parse_proto_program_tokens_fuel (SUC fuel) toks =
    (case toks of
     | [] => BProtoProgramParsed []
     | _ =>
        (case bridge_parse_proto_command_tokens_fuel (SUC fuel) toks of
         | BProtoCommandParsed cmd rest =>
             (case bridge_parse_proto_program_tokens_fuel fuel rest of
              | BProtoProgramParsed cmds =>
                  BProtoProgramParsed (cmd :: cmds)
              | BProtoProgramParseError n => BProtoProgramParseError n)
         | BProtoCommandParseError n => BProtoProgramParseError n))
End

Definition bridge_parse_source_atom_tokens_bound_def:
  bridge_parse_source_atom_tokens_bound toks =
    bridge_parse_source_atom_tokens_fuel (SUC (2 * LENGTH toks)) toks
End

Definition bridge_parse_source_command_tokens_bound_def:
  bridge_parse_source_command_tokens_bound toks =
    bridge_parse_source_command_tokens_fuel (SUC (2 * LENGTH toks)) toks
End

Definition bridge_parse_source_program_tokens_bound_def:
  bridge_parse_source_program_tokens_bound toks =
    bridge_parse_source_program_tokens_fuel (SUC (2 * LENGTH toks)) toks
End

Definition bridge_parse_proto_atom_tokens_bound_def:
  bridge_parse_proto_atom_tokens_bound toks =
    bridge_parse_proto_atom_tokens_fuel (SUC (2 * LENGTH toks)) toks
End

Definition bridge_parse_proto_command_tokens_bound_def:
  bridge_parse_proto_command_tokens_bound toks =
    bridge_parse_proto_command_tokens_fuel (SUC (2 * LENGTH toks)) toks
End

Definition bridge_parse_proto_program_tokens_bound_def:
  bridge_parse_proto_program_tokens_bound toks =
    bridge_parse_proto_program_tokens_fuel (SUC (2 * LENGTH toks)) toks
End

Theorem bridge_parse_source_atom_tokens_fuel_rest_lt:
  (∀fuel toks atom rest.
      bridge_parse_source_atom_tokens_fuel fuel toks =
        BSourceFullAtomParsed atom rest ⇒
      LENGTH rest < LENGTH toks) ∧
  (∀fuel items toks atom rest.
      bridge_parse_source_expr_items_fuel fuel items toks =
        BSourceFullAtomParsed atom rest ⇒
      LENGTH rest < LENGTH toks)
Proof
  ho_match_mp_tac bridge_parse_source_atom_tokens_fuel_ind \\
  rw[bridge_parse_source_atom_tokens_fuel_def] \\
  every_case_tac \\
  gvs[bridge_parse_source_atom_tokens_fuel_def] \\
  res_tac \\
  DECIDE_TAC
QED

Theorem bridge_parse_source_lparen_tail_error_not_fuel_from_unfolded_atom_bound:
  ∀fuel t n.
    (∀toks.
       2 * LENGTH toks ≤ SUC fuel ⇒
       (case toks of
        | [] => BSourceFullAtomParseError 3
        | BSrcTokLParen :: rest =>
            bridge_parse_source_expr_items_fuel fuel [] rest
        | BSrcTokRParen :: rest => BSourceFullAtomParseError 1
        | BSrcTokBang :: rest => BSourceFullAtomParseError 2
        | BSrcTokAtom atom :: rest => BSourceFullAtomParsed atom rest) ≠
       BSourceFullAtomParseError 99) ∧
    2 * SUC (LENGTH t) < SUC (SUC fuel) ∧
    bridge_parse_source_expr_items_fuel fuel [] t =
      BSourceFullAtomParseError n ⇒
    n ≠ 99
Proof
  rw[] \\
  qpat_x_assum ‘∀toks. _’ (qspec_then ‘BSrcTokLParen :: t’ mp_tac) \\
  impl_tac >- (gvs[] \\ DECIDE_TAC) \\
  gvs[]
QED

Theorem bridge_parse_source_atom_tokens_fuel_no_fuel_error_strong:
  ∀fuel.
  (∀toks.
      0 < fuel ∧ 2 * LENGTH toks ≤ fuel ⇒
      bridge_parse_source_atom_tokens_fuel fuel toks ≠
        BSourceFullAtomParseError 99) ∧
  (∀items toks.
      0 < fuel ∧ 2 * LENGTH toks < fuel ⇒
      bridge_parse_source_expr_items_fuel fuel items toks ≠
        BSourceFullAtomParseError 99)
Proof
  Induct_on ‘fuel’
  >- rw[bridge_parse_source_atom_tokens_fuel_def] \\
  rw[bridge_parse_source_atom_tokens_fuel_def] \\
  every_case_tac \\
  gvs[bridge_parse_source_atom_tokens_fuel_def] \\
  Cases_on ‘fuel’ \\
  gvs[bridge_parse_source_atom_tokens_fuel_def] \\
  res_tac \\
  imp_res_tac (CONJUNCT1 bridge_parse_source_atom_tokens_fuel_rest_lt) \\
  imp_res_tac (CONJUNCT2 bridge_parse_source_atom_tokens_fuel_rest_lt) \\
  TRY
    (Cases_on ‘l’ \\
     gvs[bridge_parse_source_atom_tokens_fuel_def] \\
     Cases_on ‘h’ \\
     gvs[bridge_parse_source_atom_tokens_fuel_def] \\
     res_tac) \\
  imp_res_tac
    bridge_parse_source_lparen_tail_error_not_fuel_from_unfolded_atom_bound \\
  DECIDE_TAC
QED

Theorem bridge_parse_source_atom_tokens_double_bound_no_fuel_error:
  (∀toks.
      bridge_parse_source_atom_tokens_fuel
        (SUC (2 * LENGTH toks)) toks ≠ BSourceFullAtomParseError 99) ∧
  (∀items toks.
      bridge_parse_source_expr_items_fuel
        (SUC (2 * LENGTH toks)) items toks ≠ BSourceFullAtomParseError 99)
Proof
  rw[] \\
  qspecl_then [‘SUC (2 * LENGTH toks)’] mp_tac
    bridge_parse_source_atom_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Theorem bridge_parse_source_atom_tokens_fuel_no_fuel_error:
  ∀fuel toks.
    0 < fuel ∧ 2 * LENGTH toks ≤ fuel ⇒
    bridge_parse_source_atom_tokens_fuel fuel toks ≠
      BSourceFullAtomParseError 99
Proof
  rw[] \\
  qspecl_then [‘fuel’] mp_tac
    bridge_parse_source_atom_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Theorem bridge_parse_source_command_tokens_fuel_no_fuel_error_strong:
  ∀fuel toks.
    0 < fuel ∧ 2 * LENGTH toks ≤ fuel ⇒
    bridge_parse_source_command_tokens_fuel fuel toks ≠
      BSourceCommandParseError 99
Proof
  rw[] \\
  Cases_on ‘toks’
  >- (
    rw[bridge_parse_source_command_tokens_fuel_def] \\
    Cases_on ‘bridge_parse_source_atom_tokens_fuel fuel []’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    qspecl_then [‘fuel’, ‘[]’] mp_tac
      bridge_parse_source_atom_tokens_fuel_no_fuel_error \\
    rw[]) \\
  Cases_on ‘h’ \\
  rw[bridge_parse_source_command_tokens_fuel_def]
  >- (
    Cases_on
      ‘bridge_parse_source_atom_tokens_fuel fuel (BSrcTokLParen :: t)’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    qspecl_then [‘fuel’, ‘BSrcTokLParen :: t’] mp_tac
      bridge_parse_source_atom_tokens_fuel_no_fuel_error \\
    rw[])
  >- (
    Cases_on
      ‘bridge_parse_source_atom_tokens_fuel fuel (BSrcTokRParen :: t)’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    qspecl_then [‘fuel’, ‘BSrcTokRParen :: t’] mp_tac
      bridge_parse_source_atom_tokens_fuel_no_fuel_error \\
    rw[])
  >- (
    Cases_on ‘bridge_parse_source_atom_tokens_fuel fuel t’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    qspecl_then [‘fuel’, ‘t’] mp_tac
      bridge_parse_source_atom_tokens_fuel_no_fuel_error \\
    impl_tac >- DECIDE_TAC \\
    rw[]) \\
  Cases_on ‘bridge_parse_source_atom_tokens_fuel fuel (BSrcTokAtom b :: t)’ \\
  gvs[] \\
  CCONTR_TAC \\
  gvs[] \\
  qspecl_then [‘fuel’, ‘BSrcTokAtom b :: t’] mp_tac
    bridge_parse_source_atom_tokens_fuel_no_fuel_error \\
  rw[]
QED

Theorem bridge_parse_source_atom_tokens_bound_no_fuel_error:
  ∀toks.
    bridge_parse_source_atom_tokens_bound toks ≠
      BSourceFullAtomParseError 99
Proof
  rw[bridge_parse_source_atom_tokens_bound_def,
     bridge_parse_source_atom_tokens_double_bound_no_fuel_error]
QED

Theorem bridge_parse_source_command_tokens_bound_no_fuel_error:
  ∀toks.
    bridge_parse_source_command_tokens_bound toks ≠
      BSourceCommandParseError 99
Proof
  rw[bridge_parse_source_command_tokens_bound_def] \\
  irule bridge_parse_source_command_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Theorem bridge_parse_source_command_tokens_fuel_rest_lt:
  ∀fuel toks cmd rest.
    bridge_parse_source_command_tokens_fuel fuel toks =
      BSourceCommandParsed cmd rest ⇒
    LENGTH rest < LENGTH toks
Proof
  rw[bridge_parse_source_command_tokens_fuel_def] \\
  every_case_tac \\
  gvs[] \\
  imp_res_tac (CONJUNCT1 bridge_parse_source_atom_tokens_fuel_rest_lt) \\
  gvs[] \\
  DECIDE_TAC
QED

Theorem bridge_parse_source_program_tokens_fuel_no_fuel_error_strong:
  ∀fuel toks.
    2 * LENGTH toks ≤ fuel ⇒
    bridge_parse_source_program_tokens_fuel fuel toks ≠
      BSourceProgramParseError 99
Proof
  Induct_on ‘fuel’
  >- (
    Cases_on ‘toks’ \\
    rw[bridge_parse_source_program_tokens_fuel_def]) \\
  rw[] \\
  Cases_on ‘toks’
  >- rw[bridge_parse_source_program_tokens_fuel_def] \\
  rw[bridge_parse_source_program_tokens_fuel_def] \\
  Cases_on ‘bridge_parse_source_command_tokens_fuel (SUC fuel) (h :: t)’
  >- (
    Cases_on ‘l = []’
    >- (
      Cases_on ‘fuel’ \\
      gvs[bridge_parse_source_program_tokens_fuel_def]) \\
    imp_res_tac bridge_parse_source_command_tokens_fuel_rest_lt \\
    Cases_on ‘bridge_parse_source_program_tokens_fuel fuel l’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    ‘2 * LENGTH l ≤ fuel’ by DECIDE_TAC \\
    res_tac \\
    gvs[]) \\
  CCONTR_TAC \\
  gvs[] \\
  qspecl_then [‘SUC fuel’, ‘h :: t’] mp_tac
    bridge_parse_source_command_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Theorem bridge_parse_source_program_tokens_bound_no_fuel_error:
  ∀toks.
    bridge_parse_source_program_tokens_bound toks ≠
      BSourceProgramParseError 99
Proof
  rw[bridge_parse_source_program_tokens_bound_def] \\
  irule bridge_parse_source_program_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Theorem bridge_parse_proto_atom_tokens_fuel_rest_lt:
  (∀fuel toks atom rest.
      bridge_parse_proto_atom_tokens_fuel fuel toks =
        BProtoFullAtomParsed atom rest ⇒
      LENGTH rest < LENGTH toks) ∧
  (∀fuel items toks atom rest.
      bridge_parse_proto_expr_items_fuel fuel items toks =
        BProtoFullAtomParsed atom rest ⇒
      LENGTH rest < LENGTH toks)
Proof
  ho_match_mp_tac bridge_parse_proto_atom_tokens_fuel_ind \\
  rw[bridge_parse_proto_atom_tokens_fuel_def] \\
  every_case_tac \\
  gvs[bridge_parse_proto_atom_tokens_fuel_def] \\
  res_tac \\
  DECIDE_TAC
QED

Theorem bridge_parse_proto_lparen_tail_error_not_fuel_from_unfolded_atom_bound:
  ∀fuel t n.
    (∀toks.
       2 * LENGTH toks ≤ SUC fuel ⇒
       (case toks of
        | [] => BProtoFullAtomParseError 3
        | BProtoTokLParen :: rest =>
            bridge_parse_proto_expr_items_fuel fuel [] rest
        | BProtoTokRParen :: rest => BProtoFullAtomParseError 1
        | BProtoTokBang :: rest => BProtoFullAtomParseError 2
        | BProtoTokAtom atom :: rest => BProtoFullAtomParsed atom rest) ≠
       BProtoFullAtomParseError 99) ∧
    2 * SUC (LENGTH t) < SUC (SUC fuel) ∧
    bridge_parse_proto_expr_items_fuel fuel [] t =
      BProtoFullAtomParseError n ⇒
    n ≠ 99
Proof
  rw[] \\
  qpat_x_assum ‘∀toks. _’ (qspec_then ‘BProtoTokLParen :: t’ mp_tac) \\
  impl_tac >- (gvs[] \\ DECIDE_TAC) \\
  gvs[]
QED

Theorem bridge_parse_proto_atom_tokens_fuel_no_fuel_error_strong:
  ∀fuel.
  (∀toks.
      0 < fuel ∧ 2 * LENGTH toks ≤ fuel ⇒
      bridge_parse_proto_atom_tokens_fuel fuel toks ≠
        BProtoFullAtomParseError 99) ∧
  (∀items toks.
      0 < fuel ∧ 2 * LENGTH toks < fuel ⇒
      bridge_parse_proto_expr_items_fuel fuel items toks ≠
        BProtoFullAtomParseError 99)
Proof
  Induct_on ‘fuel’
  >- rw[bridge_parse_proto_atom_tokens_fuel_def] \\
  rw[bridge_parse_proto_atom_tokens_fuel_def] \\
  every_case_tac \\
  gvs[bridge_parse_proto_atom_tokens_fuel_def] \\
  Cases_on ‘fuel’ \\
  gvs[bridge_parse_proto_atom_tokens_fuel_def] \\
  res_tac \\
  imp_res_tac (CONJUNCT1 bridge_parse_proto_atom_tokens_fuel_rest_lt) \\
  imp_res_tac (CONJUNCT2 bridge_parse_proto_atom_tokens_fuel_rest_lt) \\
  TRY
    (Cases_on ‘l’ \\
     gvs[bridge_parse_proto_atom_tokens_fuel_def] \\
     Cases_on ‘h’ \\
     gvs[bridge_parse_proto_atom_tokens_fuel_def] \\
     res_tac) \\
  imp_res_tac
    bridge_parse_proto_lparen_tail_error_not_fuel_from_unfolded_atom_bound \\
  DECIDE_TAC
QED

Theorem bridge_parse_proto_atom_tokens_double_bound_no_fuel_error:
  (∀toks.
      bridge_parse_proto_atom_tokens_fuel
        (SUC (2 * LENGTH toks)) toks ≠ BProtoFullAtomParseError 99) ∧
  (∀items toks.
      bridge_parse_proto_expr_items_fuel
        (SUC (2 * LENGTH toks)) items toks ≠ BProtoFullAtomParseError 99)
Proof
  rw[] \\
  qspecl_then [‘SUC (2 * LENGTH toks)’] mp_tac
    bridge_parse_proto_atom_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Theorem bridge_parse_proto_atom_tokens_fuel_no_fuel_error:
  ∀fuel toks.
    0 < fuel ∧ 2 * LENGTH toks ≤ fuel ⇒
    bridge_parse_proto_atom_tokens_fuel fuel toks ≠
      BProtoFullAtomParseError 99
Proof
  rw[] \\
  qspecl_then [‘fuel’] mp_tac
    bridge_parse_proto_atom_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Theorem bridge_parse_proto_command_tokens_fuel_no_fuel_error_strong:
  ∀fuel toks.
    0 < fuel ∧ 2 * LENGTH toks ≤ fuel ⇒
    bridge_parse_proto_command_tokens_fuel fuel toks ≠
      BProtoCommandParseError 99
Proof
  rw[] \\
  Cases_on ‘toks’
  >- (
    rw[bridge_parse_proto_command_tokens_fuel_def] \\
    Cases_on ‘bridge_parse_proto_atom_tokens_fuel fuel []’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    qspecl_then [‘fuel’, ‘[]’] mp_tac
      bridge_parse_proto_atom_tokens_fuel_no_fuel_error \\
    rw[]) \\
  Cases_on ‘h’ \\
  rw[bridge_parse_proto_command_tokens_fuel_def]
  >- (
    Cases_on
      ‘bridge_parse_proto_atom_tokens_fuel fuel (BProtoTokLParen :: t)’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    qspecl_then [‘fuel’, ‘BProtoTokLParen :: t’] mp_tac
      bridge_parse_proto_atom_tokens_fuel_no_fuel_error \\
    rw[])
  >- (
    Cases_on
      ‘bridge_parse_proto_atom_tokens_fuel fuel (BProtoTokRParen :: t)’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    qspecl_then [‘fuel’, ‘BProtoTokRParen :: t’] mp_tac
      bridge_parse_proto_atom_tokens_fuel_no_fuel_error \\
    rw[])
  >- (
    Cases_on ‘bridge_parse_proto_atom_tokens_fuel fuel t’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    qspecl_then [‘fuel’, ‘t’] mp_tac
      bridge_parse_proto_atom_tokens_fuel_no_fuel_error \\
    impl_tac >- DECIDE_TAC \\
    rw[]) \\
  Cases_on ‘bridge_parse_proto_atom_tokens_fuel fuel (BProtoTokAtom b :: t)’ \\
  gvs[] \\
  CCONTR_TAC \\
  gvs[] \\
  qspecl_then [‘fuel’, ‘BProtoTokAtom b :: t’] mp_tac
    bridge_parse_proto_atom_tokens_fuel_no_fuel_error \\
  rw[]
QED

Theorem bridge_parse_proto_atom_tokens_bound_no_fuel_error:
  ∀toks.
    bridge_parse_proto_atom_tokens_bound toks ≠
      BProtoFullAtomParseError 99
Proof
  rw[bridge_parse_proto_atom_tokens_bound_def,
     bridge_parse_proto_atom_tokens_double_bound_no_fuel_error]
QED

Theorem bridge_parse_proto_command_tokens_bound_no_fuel_error:
  ∀toks.
    bridge_parse_proto_command_tokens_bound toks ≠
      BProtoCommandParseError 99
Proof
  rw[bridge_parse_proto_command_tokens_bound_def] \\
  irule bridge_parse_proto_command_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Theorem bridge_parse_proto_command_tokens_fuel_rest_lt:
  ∀fuel toks cmd rest.
    bridge_parse_proto_command_tokens_fuel fuel toks =
      BProtoCommandParsed cmd rest ⇒
    LENGTH rest < LENGTH toks
Proof
  rw[bridge_parse_proto_command_tokens_fuel_def] \\
  every_case_tac \\
  gvs[] \\
  imp_res_tac (CONJUNCT1 bridge_parse_proto_atom_tokens_fuel_rest_lt) \\
  gvs[] \\
  DECIDE_TAC
QED

Theorem bridge_parse_proto_program_tokens_fuel_no_fuel_error_strong:
  ∀fuel toks.
    2 * LENGTH toks ≤ fuel ⇒
    bridge_parse_proto_program_tokens_fuel fuel toks ≠
      BProtoProgramParseError 99
Proof
  Induct_on ‘fuel’
  >- (
    Cases_on ‘toks’ \\
    rw[bridge_parse_proto_program_tokens_fuel_def]) \\
  rw[] \\
  Cases_on ‘toks’
  >- rw[bridge_parse_proto_program_tokens_fuel_def] \\
  rw[bridge_parse_proto_program_tokens_fuel_def] \\
  Cases_on ‘bridge_parse_proto_command_tokens_fuel (SUC fuel) (h :: t)’
  >- (
    Cases_on ‘l = []’
    >- (
      Cases_on ‘fuel’ \\
      gvs[bridge_parse_proto_program_tokens_fuel_def]) \\
    imp_res_tac bridge_parse_proto_command_tokens_fuel_rest_lt \\
    Cases_on ‘bridge_parse_proto_program_tokens_fuel fuel l’ \\
    gvs[] \\
    CCONTR_TAC \\
    gvs[] \\
    ‘2 * LENGTH l ≤ fuel’ by DECIDE_TAC \\
    res_tac \\
    gvs[]) \\
  CCONTR_TAC \\
  gvs[] \\
  qspecl_then [‘SUC fuel’, ‘h :: t’] mp_tac
    bridge_parse_proto_command_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Theorem bridge_parse_proto_program_tokens_bound_no_fuel_error:
  ∀toks.
    bridge_parse_proto_program_tokens_bound toks ≠
      BProtoProgramParseError 99
Proof
  rw[bridge_parse_proto_program_tokens_bound_def] \\
  irule bridge_parse_proto_program_tokens_fuel_no_fuel_error_strong \\
  rw[]
QED

Definition bridge_parse_error_message_def:
  bridge_parse_error_message (n:num) =
    if n = 1 then strlit"unexpected )"
    else if n = 2 then strlit"unexpected !"
    else if n = 3 then strlit"expected atom"
    else if n = 4 then strlit"unterminated expression"
    else if n = 99 then strlit"parser fuel exhausted"
    else strlit"parser error"
End

Datatype:
  bridge_source_shipped_atom_parse_result =
    BSourceShippedAtomParsed bridge_source_atom (bridge_source_token list)
  | BSourceShippedAtomParseError mlstring
End

Datatype:
  bridge_source_shipped_command_parse_result =
    BSourceShippedCommandParsed bridge_source_command (bridge_source_token list)
  | BSourceShippedCommandParseError mlstring
End

Datatype:
  bridge_source_shipped_program_parse_result =
    BSourceShippedProgramParsed (bridge_source_command list)
  | BSourceShippedProgramParseError mlstring
End

Datatype:
  bridge_proto_shipped_atom_parse_result =
    BProtoShippedAtomParsed bridge_proto_atom (bridge_proto_token list)
  | BProtoShippedAtomParseError mlstring
End

Datatype:
  bridge_proto_shipped_command_parse_result =
    BProtoShippedCommandParsed bridge_proto_command (bridge_proto_token list)
  | BProtoShippedCommandParseError mlstring
End

Datatype:
  bridge_proto_shipped_program_parse_result =
    BProtoShippedProgramParsed (bridge_proto_command list)
  | BProtoShippedProgramParseError mlstring
End

Definition bridge_source_full_atom_parse_result_to_shipped_def:
  bridge_source_full_atom_parse_result_to_shipped
    (BSourceFullAtomParsed atom rest) =
      BSourceShippedAtomParsed atom rest ∧
  bridge_source_full_atom_parse_result_to_shipped
    (BSourceFullAtomParseError n) =
      BSourceShippedAtomParseError (bridge_parse_error_message n)
End

Definition bridge_source_command_parse_result_to_shipped_def:
  bridge_source_command_parse_result_to_shipped
    (BSourceCommandParsed cmd rest) =
      BSourceShippedCommandParsed cmd rest ∧
  bridge_source_command_parse_result_to_shipped
    (BSourceCommandParseError n) =
      BSourceShippedCommandParseError (bridge_parse_error_message n)
End

Definition bridge_source_program_parse_result_to_shipped_def:
  bridge_source_program_parse_result_to_shipped
    (BSourceProgramParsed cmds) =
      BSourceShippedProgramParsed cmds ∧
  bridge_source_program_parse_result_to_shipped
    (BSourceProgramParseError n) =
      BSourceShippedProgramParseError (bridge_parse_error_message n)
End

Definition bridge_proto_full_atom_parse_result_to_shipped_def:
  bridge_proto_full_atom_parse_result_to_shipped
    (BProtoFullAtomParsed atom rest) =
      BProtoShippedAtomParsed atom rest ∧
  bridge_proto_full_atom_parse_result_to_shipped
    (BProtoFullAtomParseError n) =
      BProtoShippedAtomParseError (bridge_parse_error_message n)
End

Definition bridge_proto_command_parse_result_to_shipped_def:
  bridge_proto_command_parse_result_to_shipped
    (BProtoCommandParsed cmd rest) =
      BProtoShippedCommandParsed cmd rest ∧
  bridge_proto_command_parse_result_to_shipped
    (BProtoCommandParseError n) =
      BProtoShippedCommandParseError (bridge_parse_error_message n)
End

Definition bridge_proto_program_parse_result_to_shipped_def:
  bridge_proto_program_parse_result_to_shipped
    (BProtoProgramParsed cmds) =
      BProtoShippedProgramParsed cmds ∧
  bridge_proto_program_parse_result_to_shipped
    (BProtoProgramParseError n) =
      BProtoShippedProgramParseError (bridge_parse_error_message n)
End

Definition bridge_parse_source_atom_tokens_shipped_def:
  bridge_parse_source_atom_tokens_shipped toks =
    bridge_source_full_atom_parse_result_to_shipped
      (bridge_parse_source_atom_tokens_bound toks)
End

Definition bridge_parse_source_command_tokens_shipped_def:
  bridge_parse_source_command_tokens_shipped toks =
    bridge_source_command_parse_result_to_shipped
      (bridge_parse_source_command_tokens_bound toks)
End

Definition bridge_parse_source_program_tokens_shipped_def:
  bridge_parse_source_program_tokens_shipped toks =
    bridge_source_program_parse_result_to_shipped
      (bridge_parse_source_program_tokens_bound toks)
End

Theorem bridge_parse_error_message_parser_fuel_eq:
  ∀n.
    (bridge_parse_error_message n = strlit"parser fuel exhausted" ⇔ n = 99)
Proof
  rw[bridge_parse_error_message_def]
QED

Theorem bridge_parse_source_atom_tokens_shipped_no_parser_fuel_error:
  ∀toks.
    bridge_parse_source_atom_tokens_shipped toks ≠
      BSourceShippedAtomParseError (strlit"parser fuel exhausted")
Proof
  rw[bridge_parse_source_atom_tokens_shipped_def,
     bridge_source_full_atom_parse_result_to_shipped_def] \\
  Cases_on ‘bridge_parse_source_atom_tokens_bound toks’ \\
  gvs[] \\
  CCONTR_TAC \\
  gvs[bridge_parse_error_message_parser_fuel_eq,
      bridge_parse_source_atom_tokens_bound_no_fuel_error,
      bridge_source_full_atom_parse_result_to_shipped_def]
QED

Theorem bridge_parse_source_command_tokens_shipped_no_parser_fuel_error:
  ∀toks.
    bridge_parse_source_command_tokens_shipped toks ≠
      BSourceShippedCommandParseError (strlit"parser fuel exhausted")
Proof
  rw[bridge_parse_source_command_tokens_shipped_def,
     bridge_source_command_parse_result_to_shipped_def] \\
  Cases_on ‘bridge_parse_source_command_tokens_bound toks’ \\
  gvs[] \\
  CCONTR_TAC \\
  gvs[bridge_parse_error_message_parser_fuel_eq,
      bridge_parse_source_command_tokens_bound_no_fuel_error,
      bridge_source_command_parse_result_to_shipped_def]
QED

Theorem bridge_parse_source_program_tokens_shipped_no_parser_fuel_error:
  ∀toks.
    bridge_parse_source_program_tokens_shipped toks ≠
      BSourceShippedProgramParseError (strlit"parser fuel exhausted")
Proof
  rw[bridge_parse_source_program_tokens_shipped_def,
     bridge_source_program_parse_result_to_shipped_def] \\
  Cases_on ‘bridge_parse_source_program_tokens_bound toks’ \\
  gvs[] \\
  CCONTR_TAC \\
  gvs[bridge_parse_error_message_parser_fuel_eq,
      bridge_parse_source_program_tokens_bound_no_fuel_error,
      bridge_source_program_parse_result_to_shipped_def]
QED

Definition bridge_parse_proto_atom_tokens_shipped_def:
  bridge_parse_proto_atom_tokens_shipped toks =
    bridge_proto_full_atom_parse_result_to_shipped
      (bridge_parse_proto_atom_tokens_bound toks)
End

Definition bridge_parse_proto_command_tokens_shipped_def:
  bridge_parse_proto_command_tokens_shipped toks =
    bridge_proto_command_parse_result_to_shipped
      (bridge_parse_proto_command_tokens_bound toks)
End

Definition bridge_parse_proto_program_tokens_shipped_def:
  bridge_parse_proto_program_tokens_shipped toks =
    bridge_proto_program_parse_result_to_shipped
      (bridge_parse_proto_program_tokens_bound toks)
End

Definition bridge_parse_proto_command_tokens_shipped_body_def:
  bridge_parse_proto_command_tokens_shipped_body toks =
    case toks of
    | BProtoTokBang :: rest =>
        (case bridge_parse_proto_atom_tokens_shipped rest of
         | BProtoShippedAtomParsed atom rest2 =>
             BProtoShippedCommandParsed (BProtoCmdRun atom) rest2
         | BProtoShippedAtomParseError msg =>
             BProtoShippedCommandParseError msg)
    | _ =>
        (case bridge_parse_proto_atom_tokens_shipped toks of
         | BProtoShippedAtomParsed atom rest =>
             BProtoShippedCommandParsed (BProtoCmdAdd atom) rest
         | BProtoShippedAtomParseError msg =>
             BProtoShippedCommandParseError msg)
End

Theorem bridge_parse_proto_atom_tokens_shipped_no_parser_fuel_error:
  ∀toks.
    bridge_parse_proto_atom_tokens_shipped toks ≠
      BProtoShippedAtomParseError (strlit"parser fuel exhausted")
Proof
  rw[bridge_parse_proto_atom_tokens_shipped_def,
     bridge_proto_full_atom_parse_result_to_shipped_def] \\
  Cases_on ‘bridge_parse_proto_atom_tokens_bound toks’ \\
  gvs[] \\
  CCONTR_TAC \\
  gvs[bridge_parse_error_message_parser_fuel_eq,
      bridge_parse_proto_atom_tokens_bound_no_fuel_error,
      bridge_proto_full_atom_parse_result_to_shipped_def]
QED

Theorem bridge_parse_proto_command_tokens_shipped_no_parser_fuel_error:
  ∀toks.
    bridge_parse_proto_command_tokens_shipped toks ≠
      BProtoShippedCommandParseError (strlit"parser fuel exhausted")
Proof
  rw[bridge_parse_proto_command_tokens_shipped_def,
     bridge_proto_command_parse_result_to_shipped_def] \\
  Cases_on ‘bridge_parse_proto_command_tokens_bound toks’ \\
  gvs[] \\
  CCONTR_TAC \\
  gvs[bridge_parse_error_message_parser_fuel_eq,
      bridge_parse_proto_command_tokens_bound_no_fuel_error,
      bridge_proto_command_parse_result_to_shipped_def]
QED

Theorem bridge_parse_proto_command_tokens_shipped_body_no_parser_fuel_error:
  ∀toks.
    bridge_parse_proto_command_tokens_shipped_body toks ≠
      BProtoShippedCommandParseError (strlit"parser fuel exhausted")
Proof
  Cases_on ‘toks’
  >- (
    gvs[bridge_parse_proto_command_tokens_shipped_body_def] \\
    Cases_on ‘bridge_parse_proto_atom_tokens_shipped []’ \\
    gvs[] \\
    metis_tac[bridge_parse_proto_atom_tokens_shipped_no_parser_fuel_error])
  >- (
    Cases_on ‘h’ \\
    gvs[bridge_parse_proto_command_tokens_shipped_body_def]
    >- (
      Cases_on ‘bridge_parse_proto_atom_tokens_shipped (BProtoTokLParen::t)’ \\
      gvs[] \\
      metis_tac[bridge_parse_proto_atom_tokens_shipped_no_parser_fuel_error])
    >- (
      Cases_on ‘bridge_parse_proto_atom_tokens_shipped (BProtoTokRParen::t)’ \\
      gvs[] \\
      metis_tac[bridge_parse_proto_atom_tokens_shipped_no_parser_fuel_error])
    >- (
      Cases_on ‘bridge_parse_proto_atom_tokens_shipped t’ \\
      gvs[] \\
      metis_tac[bridge_parse_proto_atom_tokens_shipped_no_parser_fuel_error]) \\
    Cases_on ‘bridge_parse_proto_atom_tokens_shipped (BProtoTokAtom b::t)’ \\
    gvs[] \\
    metis_tac[bridge_parse_proto_atom_tokens_shipped_no_parser_fuel_error])
QED

Theorem bridge_parse_proto_program_tokens_shipped_no_parser_fuel_error:
  ∀toks.
    bridge_parse_proto_program_tokens_shipped toks ≠
      BProtoShippedProgramParseError (strlit"parser fuel exhausted")
Proof
  rw[bridge_parse_proto_program_tokens_shipped_def,
     bridge_proto_program_parse_result_to_shipped_def] \\
  Cases_on ‘bridge_parse_proto_program_tokens_bound toks’ \\
  gvs[] \\
  CCONTR_TAC \\
  gvs[bridge_parse_error_message_parser_fuel_eq,
      bridge_parse_proto_program_tokens_bound_no_fuel_error,
      bridge_proto_program_parse_result_to_shipped_def]
QED

Definition bridge_lex_error_message_def:
  bridge_lex_error_message (n:num) =
    if n = 10 then strlit"empty token"
    else if n = 11 then strlit"empty variable"
    else if n = 12 then strlit"unterminated string"
    else if n = 99 then strlit"lexer fuel exhausted"
    else strlit"lexer error"
End

Datatype:
  bridge_source_parsed_atom_result =
    BSourceParsedAtom bridge_source_atom
  | BSourceParseAtomError mlstring
End

Datatype:
  bridge_source_parsed_command_result =
    BSourceParsedCommand bridge_source_command
  | BSourceParseCommandError mlstring
End

Datatype:
  bridge_source_parsed_program_result =
    BSourceParsedProgram (bridge_source_command list)
  | BSourceParseProgramError mlstring
End

Definition bridge_parse_source_atom_string_shipped_def:
  bridge_parse_source_atom_string_shipped lex_fuel text =
    case bridge_tokenize_source_string_fuel lex_fuel text of
    | BSourceLexed toks =>
        (case bridge_parse_source_atom_tokens_shipped toks of
         | BSourceShippedAtomParsed atom rest =>
             (case rest of
              | [] => BSourceParsedAtom atom
              | _ => BSourceParseAtomError
                       (strlit"trailing tokens after atom"))
         | BSourceShippedAtomParseError msg =>
             BSourceParseAtomError msg)
    | BSourceLexError n => BSourceParseAtomError (bridge_lex_error_message n)
End

Definition bridge_parse_source_command_string_shipped_def:
  bridge_parse_source_command_string_shipped lex_fuel text =
    case bridge_tokenize_source_string_fuel lex_fuel text of
    | BSourceLexed toks =>
        (case bridge_parse_source_command_tokens_shipped toks of
         | BSourceShippedCommandParsed cmd rest =>
             (case rest of
              | [] => BSourceParsedCommand cmd
              | _ => BSourceParseCommandError
                       (strlit"trailing tokens after command"))
         | BSourceShippedCommandParseError msg =>
             BSourceParseCommandError msg)
    | BSourceLexError n =>
        BSourceParseCommandError (bridge_lex_error_message n)
End

Definition bridge_parse_source_program_string_shipped_def:
  bridge_parse_source_program_string_shipped lex_fuel text =
    case bridge_tokenize_source_string_fuel lex_fuel text of
    | BSourceLexed toks =>
        (case bridge_parse_source_program_tokens_shipped toks of
         | BSourceShippedProgramParsed cmds => BSourceParsedProgram cmds
         | BSourceShippedProgramParseError msg =>
             BSourceParseProgramError msg)
    | BSourceLexError n =>
        BSourceParseProgramError (bridge_lex_error_message n)
End

Definition bridge_tokenize_source_string_bound_def:
  bridge_tokenize_source_string_bound text =
    bridge_tokenize_source_string_fuel (SUC (LENGTH (explode text))) text
End

Definition bridge_parse_source_atom_string_shipped_bound_def:
  bridge_parse_source_atom_string_shipped_bound text =
    bridge_parse_source_atom_string_shipped
      (SUC (LENGTH (explode text))) text
End

Definition bridge_parse_source_command_string_shipped_bound_def:
  bridge_parse_source_command_string_shipped_bound text =
    bridge_parse_source_command_string_shipped
      (SUC (LENGTH (explode text))) text
End

Definition bridge_parse_source_program_string_shipped_bound_def:
  bridge_parse_source_program_string_shipped_bound text =
    bridge_parse_source_program_string_shipped
      (SUC (LENGTH (explode text))) text
End

Definition bridge_run_source_program_string_shipped_bound_with_env_def:
  bridge_run_source_program_string_shipped_bound_with_env
    dyn_env var_env str_env eval_fuel text =
    case bridge_parse_source_program_string_shipped_bound text of
    | BSourceParsedProgram cmds =>
        (case bridge_import_source_command_list_with_env
                dyn_env var_env str_env cmds of
         | SOME imported =>
             (case bridge_run_program_env dyn_env eval_fuel [] [] imported of
              | (self, spaces, outs) =>
                  BSourceProgramRunResult self spaces outs)
         | NONE => BSourceProgramRunImportError)
    | BSourceParseProgramError msg => BSourceProgramRunParseError msg
End

Theorem bridge_run_source_program_string_shipped_bound_with_env_success:
  ∀dyn_env var_env str_env eval_fuel text cmds imported.
    bridge_parse_source_program_string_shipped_bound text =
      BSourceParsedProgram cmds ∧
    bridge_import_source_command_list_with_env
      dyn_env var_env str_env cmds = SOME imported ⇒
    bridge_run_source_program_string_shipped_bound_with_env
      dyn_env var_env str_env eval_fuel text =
      (case bridge_run_program_env dyn_env eval_fuel [] [] imported of
       | (self, spaces, outs) =>
           BSourceProgramRunResult self spaces outs)
Proof
  rw[bridge_run_source_program_string_shipped_bound_with_env_def]
QED

Theorem bridge_run_source_program_string_shipped_bound_with_env_dynamic_example:
  bridge_run_source_program_string_shipped_bound_with_env
    [(strlit"assertEqual", 1000); (strlit"Foo", 1001)] [] [] 7
    (strlit"Foo\n!(assertEqual Foo Foo)") =
    BSourceProgramRunResult
      [metta_m1$Sym 1001] [] [[metta_m1$Expr []]]
Proof
  EVAL_TAC
QED

Theorem bridge_run_source_program_string_shipped_bound_with_env_negative_example:
  bridge_run_source_program_string_shipped_bound_with_env
    [(strlit"assertEqual", 1000)] [] [] 7
    (strlit"Foo\n!(assertEqual Foo Foo)") =
    BSourceProgramRunImportError ∧
  bridge_run_source_program_string_shipped_bound_with_env [] [] [] 7
    (strlit"(return $x") =
    BSourceProgramRunParseError (strlit"unterminated expression")
Proof
  EVAL_TAC
QED

Theorem bridge_tokenize_source_string_bound_no_fuel_error:
  ∀text.
    bridge_tokenize_source_string_bound text ≠ BSourceLexError 99
Proof
  rw[bridge_tokenize_source_string_bound_def,
     bridge_tokenize_source_string_fuel_def] \\
  irule bridge_tokenize_source_chars_fuel_no_fuel_error \\
  rw[]
QED

Definition bridge_proto_source_command_rel_def:
  bridge_proto_source_command_rel
    (BProtoCmdAdd proto) (BSrcCmdAdd source) =
      bridge_proto_source_rel proto source ∧
  bridge_proto_source_command_rel
    (BProtoCmdRun proto) (BSrcCmdRun source) =
      bridge_proto_source_rel proto source ∧
  bridge_proto_source_command_rel _ _ = F
End

Definition bridge_proto_source_command_rel_list_def:
  bridge_proto_source_command_rel_list [] [] = T ∧
  bridge_proto_source_command_rel_list (x :: xs) (y :: ys) =
    (bridge_proto_source_command_rel x y ∧
     bridge_proto_source_command_rel_list xs ys) ∧
  bridge_proto_source_command_rel_list _ _ = F
End

Definition bridge_proto_source_command_parse_result_rel_def:
  bridge_proto_source_command_parse_result_rel
    (BProtoCommandParsed proto rest_proto)
    (BSourceCommandParsed source rest_source) =
      (bridge_proto_source_command_rel proto source ∧
       bridge_proto_source_token_rel_list rest_proto rest_source) ∧
  bridge_proto_source_command_parse_result_rel
    (BProtoCommandParseError n) (BSourceCommandParseError m) =
      (n = m) ∧
  bridge_proto_source_command_parse_result_rel _ _ = F
End

Definition bridge_proto_source_program_parse_result_rel_def:
  bridge_proto_source_program_parse_result_rel
    (BProtoProgramParsed proto_cmds) (BSourceProgramParsed source_cmds) =
      bridge_proto_source_command_rel_list proto_cmds source_cmds ∧
  bridge_proto_source_program_parse_result_rel
    (BProtoProgramParseError n) (BSourceProgramParseError m) =
      (n = m) ∧
  bridge_proto_source_program_parse_result_rel _ _ = F
End

Definition bridge_proto_source_shipped_atom_parse_result_rel_def:
  bridge_proto_source_shipped_atom_parse_result_rel
    (BProtoShippedAtomParsed proto rest_proto)
    (BSourceShippedAtomParsed source rest_source) =
      (bridge_proto_source_rel proto source ∧
       bridge_proto_source_token_rel_list rest_proto rest_source) ∧
  bridge_proto_source_shipped_atom_parse_result_rel
    (BProtoShippedAtomParseError msg1)
    (BSourceShippedAtomParseError msg2) =
      (msg1 = msg2) ∧
  bridge_proto_source_shipped_atom_parse_result_rel _ _ = F
End

Definition bridge_proto_source_shipped_command_parse_result_rel_def:
  bridge_proto_source_shipped_command_parse_result_rel
    (BProtoShippedCommandParsed proto rest_proto)
    (BSourceShippedCommandParsed source rest_source) =
      (bridge_proto_source_command_rel proto source ∧
       bridge_proto_source_token_rel_list rest_proto rest_source) ∧
  bridge_proto_source_shipped_command_parse_result_rel
    (BProtoShippedCommandParseError msg1)
    (BSourceShippedCommandParseError msg2) =
      (msg1 = msg2) ∧
  bridge_proto_source_shipped_command_parse_result_rel _ _ = F
End

Definition bridge_proto_source_shipped_program_parse_result_rel_def:
  bridge_proto_source_shipped_program_parse_result_rel
    (BProtoShippedProgramParsed proto_cmds)
    (BSourceShippedProgramParsed source_cmds) =
      bridge_proto_source_command_rel_list proto_cmds source_cmds ∧
  bridge_proto_source_shipped_program_parse_result_rel
    (BProtoShippedProgramParseError msg1)
    (BSourceShippedProgramParseError msg2) =
      (msg1 = msg2) ∧
  bridge_proto_source_shipped_program_parse_result_rel _ _ = F
End

Theorem bridge_parse_command_proto_source_add_case_related:
  ∀fuel proto_toks source_toks.
    bridge_proto_source_token_rel_list proto_toks source_toks ⇒
    bridge_proto_source_command_parse_result_rel
      (case bridge_parse_proto_atom_tokens_fuel fuel proto_toks of
       | BProtoFullAtomParsed atom rest =>
           BProtoCommandParsed (BProtoCmdAdd atom) rest
       | BProtoFullAtomParseError n => BProtoCommandParseError n)
      (case bridge_parse_source_atom_tokens_fuel fuel source_toks of
       | BSourceFullAtomParsed atom rest =>
           BSourceCommandParsed (BSrcCmdAdd atom) rest
       | BSourceFullAtomParseError n => BSourceCommandParseError n)
Proof
  rw[] \\
  qspecl_then
    [‘fuel’, ‘proto_toks’, ‘source_toks’]
    mp_tac bridge_parse_proto_source_full_tokens_related \\
  rw[] \\
  every_case_tac \\
  gvs[bridge_proto_source_parse_result_rel_def,
      bridge_proto_source_command_parse_result_rel_def,
      bridge_proto_source_command_rel_def]
QED

Theorem bridge_parse_command_proto_source_run_case_related:
  ∀fuel proto_toks source_toks.
    bridge_proto_source_token_rel_list proto_toks source_toks ⇒
    bridge_proto_source_command_parse_result_rel
      (case bridge_parse_proto_atom_tokens_fuel fuel proto_toks of
       | BProtoFullAtomParsed atom rest =>
           BProtoCommandParsed (BProtoCmdRun atom) rest
       | BProtoFullAtomParseError n => BProtoCommandParseError n)
      (case bridge_parse_source_atom_tokens_fuel fuel source_toks of
       | BSourceFullAtomParsed atom rest =>
           BSourceCommandParsed (BSrcCmdRun atom) rest
       | BSourceFullAtomParseError n => BSourceCommandParseError n)
Proof
  rw[] \\
  qspecl_then
    [‘fuel’, ‘proto_toks’, ‘source_toks’]
    mp_tac bridge_parse_proto_source_full_tokens_related \\
  rw[] \\
  every_case_tac \\
  gvs[bridge_proto_source_parse_result_rel_def,
      bridge_proto_source_command_parse_result_rel_def,
      bridge_proto_source_command_rel_def]
QED

Theorem bridge_parse_command_proto_source_tokens_fuel_related:
  ∀fuel proto_toks source_toks.
    bridge_proto_source_token_rel_list proto_toks source_toks ⇒
    bridge_proto_source_command_parse_result_rel
      (bridge_parse_proto_command_tokens_fuel fuel proto_toks)
      (bridge_parse_source_command_tokens_fuel fuel source_toks)
Proof
  rw[] \\
  Cases_on ‘proto_toks’
  >- (
    Cases_on ‘source_toks’
    >- (
      rw[bridge_parse_proto_command_tokens_fuel_def,
         bridge_parse_source_command_tokens_fuel_def] \\
      irule bridge_parse_command_proto_source_add_case_related \\
      rw[bridge_proto_source_token_rel_list_def]) \\
    gvs[bridge_proto_source_token_rel_list_def]) \\
  Cases_on ‘source_toks’
  >- gvs[bridge_proto_source_token_rel_list_def] \\
  Cases_on ‘h’ \\
  Cases_on ‘h'’ \\
  gvs[bridge_parse_proto_command_tokens_fuel_def,
      bridge_parse_source_command_tokens_fuel_def,
      bridge_proto_source_token_rel_list_def,
      bridge_proto_source_token_rel_def] \\
  TRY (
    irule bridge_parse_command_proto_source_run_case_related \\
    gvs[bridge_proto_source_token_rel_list_def]) \\
  TRY (
    irule bridge_parse_command_proto_source_add_case_related \\
    gvs[bridge_proto_source_token_rel_list_def,
        bridge_proto_source_token_rel_def]) \\
  gvs[bridge_proto_source_token_rel_list_def,
      bridge_proto_source_token_rel_def]
QED

Theorem bridge_parse_program_proto_source_tokens_fuel_related:
  ∀fuel proto_toks source_toks.
    bridge_proto_source_token_rel_list proto_toks source_toks ⇒
    bridge_proto_source_program_parse_result_rel
      (bridge_parse_proto_program_tokens_fuel fuel proto_toks)
      (bridge_parse_source_program_tokens_fuel fuel source_toks)
Proof
  Induct_on ‘fuel’
  >- (
    Cases_on ‘proto_toks’ \\
    Cases_on ‘source_toks’ \\
    rw[bridge_parse_proto_program_tokens_fuel_def,
       bridge_parse_source_program_tokens_fuel_def,
       bridge_proto_source_token_rel_list_def,
       bridge_proto_source_program_parse_result_rel_def,
       bridge_proto_source_command_rel_list_def]) \\
  rw[] \\
  Cases_on ‘proto_toks’ \\
  Cases_on ‘source_toks’ \\
  gvs[bridge_parse_proto_program_tokens_fuel_def,
      bridge_parse_source_program_tokens_fuel_def,
      bridge_proto_source_token_rel_list_def,
      bridge_proto_source_program_parse_result_rel_def,
      bridge_proto_source_command_rel_list_def] \\
  qspecl_then
    [‘SUC fuel’, ‘h :: t’, ‘h' :: t'’]
    mp_tac
    bridge_parse_command_proto_source_tokens_fuel_related \\
  impl_tac
  >- gvs[bridge_proto_source_token_rel_list_def] \\
  strip_tac \\
  Cases_on ‘bridge_parse_proto_command_tokens_fuel (SUC fuel) (h::t)’ \\
  Cases_on ‘bridge_parse_source_command_tokens_fuel (SUC fuel) (h'::t')’ \\
  gvs[bridge_proto_source_command_parse_result_rel_def,
      bridge_proto_source_program_parse_result_rel_def] \\
  first_x_assum drule \\
  strip_tac \\
  every_case_tac \\
  gvs[bridge_proto_source_program_parse_result_rel_def,
      bridge_proto_source_command_rel_list_def]
QED

Theorem bridge_proto_source_token_list_parser_simulation:
  ∀fuel proto_toks source_toks.
    bridge_proto_source_token_rel_list proto_toks source_toks ⇒
    bridge_proto_source_parse_result_rel
      (bridge_parse_proto_atom_tokens_fuel fuel proto_toks)
      (bridge_parse_source_atom_tokens_fuel fuel source_toks) ∧
    bridge_proto_source_command_parse_result_rel
      (bridge_parse_proto_command_tokens_fuel fuel proto_toks)
      (bridge_parse_source_command_tokens_fuel fuel source_toks) ∧
    bridge_proto_source_program_parse_result_rel
      (bridge_parse_proto_program_tokens_fuel fuel proto_toks)
      (bridge_parse_source_program_tokens_fuel fuel source_toks)
Proof
  metis_tac[bridge_parse_proto_source_full_tokens_related,
            bridge_parse_command_proto_source_tokens_fuel_related,
            bridge_parse_program_proto_source_tokens_fuel_related]
QED

Theorem bridge_proto_source_token_rel_list_length:
  ∀proto_toks source_toks.
    bridge_proto_source_token_rel_list proto_toks source_toks ⇒
    LENGTH proto_toks = LENGTH source_toks
Proof
  Induct_on ‘proto_toks’ \\
  Cases_on ‘source_toks’ \\
  rw[bridge_proto_source_token_rel_list_def]
QED

Theorem bridge_proto_source_bound_parser_simulation:
  ∀proto_toks source_toks.
    bridge_proto_source_token_rel_list proto_toks source_toks ⇒
    bridge_proto_source_parse_result_rel
      (bridge_parse_proto_atom_tokens_bound proto_toks)
      (bridge_parse_source_atom_tokens_bound source_toks) ∧
    bridge_proto_source_command_parse_result_rel
      (bridge_parse_proto_command_tokens_bound proto_toks)
      (bridge_parse_source_command_tokens_bound source_toks) ∧
    bridge_proto_source_program_parse_result_rel
      (bridge_parse_proto_program_tokens_bound proto_toks)
      (bridge_parse_source_program_tokens_bound source_toks)
Proof
  rw[bridge_parse_proto_atom_tokens_bound_def,
     bridge_parse_source_atom_tokens_bound_def,
     bridge_parse_proto_command_tokens_bound_def,
     bridge_parse_source_command_tokens_bound_def,
     bridge_parse_proto_program_tokens_bound_def,
     bridge_parse_source_program_tokens_bound_def] \\
  drule bridge_proto_source_token_rel_list_length \\
  rw[] \\
  metis_tac[bridge_proto_source_token_list_parser_simulation]
QED

Theorem bridge_proto_source_shipped_parser_simulation:
  ∀proto_toks source_toks.
    bridge_proto_source_token_rel_list proto_toks source_toks ⇒
    bridge_proto_source_shipped_atom_parse_result_rel
      (bridge_parse_proto_atom_tokens_shipped proto_toks)
      (bridge_parse_source_atom_tokens_shipped source_toks) ∧
    bridge_proto_source_shipped_command_parse_result_rel
      (bridge_parse_proto_command_tokens_shipped proto_toks)
      (bridge_parse_source_command_tokens_shipped source_toks) ∧
    bridge_proto_source_shipped_program_parse_result_rel
      (bridge_parse_proto_program_tokens_shipped proto_toks)
      (bridge_parse_source_program_tokens_shipped source_toks)
Proof
  rw[bridge_parse_proto_atom_tokens_shipped_def,
     bridge_parse_source_atom_tokens_shipped_def,
     bridge_parse_proto_command_tokens_shipped_def,
     bridge_parse_source_command_tokens_shipped_def,
     bridge_parse_proto_program_tokens_shipped_def,
     bridge_parse_source_program_tokens_shipped_def] \\
  drule bridge_proto_source_bound_parser_simulation \\
  strip_tac \\
  rpt conj_tac
  >- (
    Cases_on ‘bridge_parse_proto_atom_tokens_bound proto_toks’ \\
    Cases_on ‘bridge_parse_source_atom_tokens_bound source_toks’ \\
    gvs[bridge_proto_source_parse_result_rel_def,
        bridge_source_full_atom_parse_result_to_shipped_def,
        bridge_proto_full_atom_parse_result_to_shipped_def,
        bridge_proto_source_shipped_atom_parse_result_rel_def])
  >- (
    Cases_on ‘bridge_parse_proto_command_tokens_bound proto_toks’ \\
    Cases_on ‘bridge_parse_source_command_tokens_bound source_toks’ \\
    gvs[bridge_proto_source_command_parse_result_rel_def,
        bridge_source_command_parse_result_to_shipped_def,
        bridge_proto_command_parse_result_to_shipped_def,
        bridge_proto_source_shipped_command_parse_result_rel_def]) \\
  Cases_on ‘bridge_parse_proto_program_tokens_bound proto_toks’ \\
  Cases_on ‘bridge_parse_source_program_tokens_bound source_toks’ \\
  gvs[bridge_proto_source_program_parse_result_rel_def,
      bridge_source_program_parse_result_to_shipped_def,
      bridge_proto_program_parse_result_to_shipped_def,
      bridge_proto_source_shipped_program_parse_result_rel_def]
QED

Theorem bridge_parse_program_proto_source_positive_example:
  bridge_proto_source_program_parse_result_rel
    (bridge_parse_proto_program_tokens_fuel 20
      [BProtoTokLParen;
       BProtoTokAtom (ProtoSym (strlit"return"));
       BProtoTokAtom (ProtoVar (strlit"x"));
       BProtoTokRParen;
       BProtoTokBang;
       BProtoTokLParen;
       BProtoTokAtom (ProtoSym (strlit"+"));
       BProtoTokAtom (ProtoInt 1);
       BProtoTokAtom (ProtoInt 2);
       BProtoTokRParen])
    (bridge_parse_source_program_tokens_fuel 20
      [BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"return"));
       BSrcTokAtom (SrcVar (strlit"x"));
       BSrcTokRParen;
       BSrcTokBang;
       BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"+"));
       BSrcTokAtom (SrcInt 1);
       BSrcTokAtom (SrcInt 2);
       BSrcTokRParen])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_program_proto_source_bound_positive_example:
  bridge_proto_source_program_parse_result_rel
    (bridge_parse_proto_program_tokens_bound
      [BProtoTokLParen;
       BProtoTokAtom (ProtoSym (strlit"return"));
       BProtoTokAtom (ProtoVar (strlit"x"));
       BProtoTokRParen;
       BProtoTokBang;
       BProtoTokLParen;
       BProtoTokAtom (ProtoSym (strlit"+"));
       BProtoTokAtom (ProtoInt 1);
       BProtoTokAtom (ProtoInt 2);
       BProtoTokRParen])
    (bridge_parse_source_program_tokens_bound
      [BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"return"));
       BSrcTokAtom (SrcVar (strlit"x"));
       BSrcTokRParen;
       BSrcTokBang;
       BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"+"));
       BSrcTokAtom (SrcInt 1);
       BSrcTokAtom (SrcInt 2);
       BSrcTokRParen])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_program_proto_source_negative_example:
  ¬bridge_proto_source_program_parse_result_rel
    (bridge_parse_proto_program_tokens_fuel 20
      [BProtoTokAtom (ProtoVar (strlit"x"))])
    (bridge_parse_source_program_tokens_fuel 20
      [BSrcTokAtom (SrcVar (strlit"y"))])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_program_proto_source_bound_negative_example:
  ¬bridge_proto_source_program_parse_result_rel
    (bridge_parse_proto_program_tokens_bound
      [BProtoTokAtom (ProtoVar (strlit"x"))])
    (bridge_parse_source_program_tokens_bound
      [BSrcTokAtom (SrcVar (strlit"y"))])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_error_message_positive_example:
  bridge_parse_error_message 1 = strlit"unexpected )" ∧
  bridge_parse_error_message 2 = strlit"unexpected !" ∧
  bridge_parse_error_message 3 = strlit"expected atom" ∧
  bridge_parse_error_message 4 = strlit"unterminated expression"
Proof
  EVAL_TAC
QED

Theorem bridge_parse_error_message_negative_example:
  bridge_parse_error_message 77 = strlit"parser error" ∧
  bridge_parse_error_message 99 = strlit"parser fuel exhausted"
Proof
  EVAL_TAC
QED

Theorem bridge_lex_error_message_positive_example:
  bridge_lex_error_message 10 = strlit"empty token" ∧
  bridge_lex_error_message 11 = strlit"empty variable" ∧
  bridge_lex_error_message 12 = strlit"unterminated string"
Proof
  EVAL_TAC
QED

Theorem bridge_lex_error_message_negative_example:
  bridge_lex_error_message 77 = strlit"lexer error" ∧
  bridge_lex_error_message 99 = strlit"lexer fuel exhausted"
Proof
  EVAL_TAC
QED

Theorem bridge_parse_proto_atom_tokens_shipped_error_example:
  bridge_parse_proto_atom_tokens_shipped [BProtoTokRParen] =
    BProtoShippedAtomParseError (strlit"unexpected )") ∧
  bridge_parse_proto_atom_tokens_shipped [] =
    BProtoShippedAtomParseError (strlit"expected atom")
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_atom_string_shipped_positive_example:
  bridge_parse_source_atom_string_shipped 100 (strlit"(return $x)") =
    BSourceParsedAtom
      (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_atom_string_shipped_trailing_negative_example:
  bridge_parse_source_atom_string_shipped 100 (strlit"a b") =
    BSourceParseAtomError (strlit"trailing tokens after atom")
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_atom_string_shipped_lex_negative_example:
  bridge_parse_source_atom_string_shipped 100 (strlit"$)") =
    BSourceParseAtomError (strlit"empty variable") ∧
  bridge_parse_source_atom_string_shipped 100 (strlit"\"unterminated") =
    BSourceParseAtomError (strlit"unterminated string")
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_command_string_shipped_positive_example:
  bridge_parse_source_command_string_shipped 100 (strlit"!(return 7)") =
    BSourceParsedCommand
      (BSrcCmdRun (SrcExpr [SrcSym (strlit"return"); SrcInt 7]))
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_command_string_shipped_trailing_negative_example:
  bridge_parse_source_command_string_shipped 100 (strlit"!(return 7) x") =
    BSourceParseCommandError (strlit"trailing tokens after command")
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_program_string_shipped_positive_example:
  bridge_parse_source_program_string_shipped 100
    (strlit"(return $x)\n!(+ 1 2)") =
    BSourceParsedProgram
      [BSrcCmdAdd (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")]);
       BSrcCmdRun (SrcExpr [SrcSym (strlit"+"); SrcInt 1; SrcInt 2])]
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_program_string_shipped_negative_example:
  bridge_parse_source_program_string_shipped 100 (strlit"(return $x") =
    BSourceParseProgramError (strlit"unterminated expression")
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_atom_string_shipped_bound_positive_example:
  bridge_parse_source_atom_string_shipped_bound (strlit"(return $x)") =
    BSourceParsedAtom
      (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_atom_string_shipped_bound_trailing_negative_example:
  bridge_parse_source_atom_string_shipped_bound (strlit"a b") =
    BSourceParseAtomError (strlit"trailing tokens after atom")
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_atom_string_shipped_bound_lex_negative_example:
  bridge_parse_source_atom_string_shipped_bound (strlit"$)") =
    BSourceParseAtomError (strlit"empty variable") ∧
  bridge_parse_source_atom_string_shipped_bound (strlit"\"unterminated") =
    BSourceParseAtomError (strlit"unterminated string")
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_command_string_shipped_bound_positive_example:
  bridge_parse_source_command_string_shipped_bound (strlit"!(return 7)") =
    BSourceParsedCommand
      (BSrcCmdRun (SrcExpr [SrcSym (strlit"return"); SrcInt 7]))
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_command_string_shipped_bound_trailing_negative_example:
  bridge_parse_source_command_string_shipped_bound (strlit"!(return 7) x") =
    BSourceParseCommandError (strlit"trailing tokens after command")
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_program_string_shipped_bound_positive_example:
  bridge_parse_source_program_string_shipped_bound
    (strlit"(return $x)\n!(+ 1 2)") =
    BSourceParsedProgram
      [BSrcCmdAdd (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")]);
       BSrcCmdRun (SrcExpr [SrcSym (strlit"+"); SrcInt 1; SrcInt 2])]
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_program_string_shipped_bound_negative_example:
  bridge_parse_source_program_string_shipped_bound (strlit"(return $x") =
    BSourceParseProgramError (strlit"unterminated expression")
Proof
  EVAL_TAC
QED

Theorem bridge_parse_program_proto_source_shipped_positive_example:
  bridge_proto_source_shipped_program_parse_result_rel
    (bridge_parse_proto_program_tokens_shipped
      [BProtoTokLParen;
       BProtoTokAtom (ProtoSym (strlit"return"));
       BProtoTokAtom (ProtoVar (strlit"x"));
       BProtoTokRParen;
       BProtoTokBang;
       BProtoTokLParen;
       BProtoTokAtom (ProtoSym (strlit"+"));
       BProtoTokAtom (ProtoInt 1);
       BProtoTokAtom (ProtoInt 2);
       BProtoTokRParen])
    (bridge_parse_source_program_tokens_shipped
      [BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"return"));
       BSrcTokAtom (SrcVar (strlit"x"));
       BSrcTokRParen;
       BSrcTokBang;
       BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"+"));
       BSrcTokAtom (SrcInt 1);
       BSrcTokAtom (SrcInt 2);
       BSrcTokRParen])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_program_proto_source_shipped_negative_example:
  ¬bridge_proto_source_shipped_program_parse_result_rel
    (bridge_parse_proto_program_tokens_shipped
      [BProtoTokAtom (ProtoVar (strlit"x"))])
    (bridge_parse_source_program_tokens_shipped
      [BSrcTokAtom (SrcVar (strlit"y"))])
Proof
  EVAL_TAC
QED

Definition bridge_source_surface_command_rel_def:
  bridge_source_surface_command_rel var_env str_env
    (BSrcCmdAdd source) (BCmdAdd surface) =
      bridge_source_surface_rel var_env str_env source surface ∧
  bridge_source_surface_command_rel var_env str_env
    (BSrcCmdRun source) (BCmdRun surface) =
      bridge_source_surface_rel var_env str_env source surface ∧
  bridge_source_surface_command_rel var_env str_env _ _ = F
End

Definition bridge_source_surface_command_rel_list_def:
  bridge_source_surface_command_rel_list var_env str_env [] [] = T ∧
  bridge_source_surface_command_rel_list var_env str_env
    (x :: xs) (y :: ys) =
      (bridge_source_surface_command_rel var_env str_env x y ∧
       bridge_source_surface_command_rel_list var_env str_env xs ys) ∧
  bridge_source_surface_command_rel_list var_env str_env _ _ = F
End

Definition bridge_source_surface_command_parse_result_rel_def:
  bridge_source_surface_command_parse_result_rel var_env str_env
    (BSourceCommandParsed source rest_source)
    (BCommandParsed surface rest_surface) =
      (bridge_source_surface_command_rel var_env str_env source surface ∧
       bridge_source_surface_token_rel_list var_env str_env
         rest_source rest_surface) ∧
  bridge_source_surface_command_parse_result_rel var_env str_env
    (BSourceCommandParseError n) (BCommandParseError m) =
      (n = m) ∧
  bridge_source_surface_command_parse_result_rel var_env str_env _ _ = F
End

Definition bridge_source_surface_program_parse_result_rel_def:
  bridge_source_surface_program_parse_result_rel var_env str_env
    (BSourceProgramParsed source_cmds) (BProgramParsed surface_cmds) =
      bridge_source_surface_command_rel_list var_env str_env
        source_cmds surface_cmds ∧
  bridge_source_surface_program_parse_result_rel var_env str_env
    (BSourceProgramParseError n) (BProgramParseError m) =
      (n = m) ∧
  bridge_source_surface_program_parse_result_rel var_env str_env _ _ = F
End

Theorem bridge_parse_command_add_case_related:
  ∀fuel var_env str_env source_toks surface_toks.
    bridge_source_surface_token_rel_list var_env str_env
      source_toks surface_toks ⇒
    bridge_source_surface_command_parse_result_rel var_env str_env
      (case bridge_parse_source_atom_tokens_fuel fuel source_toks of
       | BSourceFullAtomParsed atom rest =>
           BSourceCommandParsed (BSrcCmdAdd atom) rest
       | BSourceFullAtomParseError n => BSourceCommandParseError n)
      (case bridge_parse_atom_tokens_fuel fuel surface_toks of
       | BFullAtomParsed atom rest => BCommandParsed (BCmdAdd atom) rest
       | BFullAtomParseError n => BCommandParseError n)
Proof
  rw[] \\
  qspecl_then
    [‘fuel’, ‘var_env’, ‘str_env’, ‘source_toks’, ‘surface_toks’]
    mp_tac bridge_parse_source_surface_full_tokens_related \\
  rw[] \\
  every_case_tac \\
  gvs[bridge_source_surface_parse_result_rel_def,
      bridge_source_surface_command_parse_result_rel_def,
      bridge_source_surface_command_rel_def]
QED

Theorem bridge_parse_command_run_case_related:
  ∀fuel var_env str_env source_toks surface_toks.
    bridge_source_surface_token_rel_list var_env str_env
      source_toks surface_toks ⇒
    bridge_source_surface_command_parse_result_rel var_env str_env
      (case bridge_parse_source_atom_tokens_fuel fuel source_toks of
       | BSourceFullAtomParsed atom rest =>
           BSourceCommandParsed (BSrcCmdRun atom) rest
       | BSourceFullAtomParseError n => BSourceCommandParseError n)
      (case bridge_parse_atom_tokens_fuel fuel surface_toks of
       | BFullAtomParsed atom rest => BCommandParsed (BCmdRun atom) rest
       | BFullAtomParseError n => BCommandParseError n)
Proof
  rw[] \\
  qspecl_then
    [‘fuel’, ‘var_env’, ‘str_env’, ‘source_toks’, ‘surface_toks’]
    mp_tac bridge_parse_source_surface_full_tokens_related \\
  rw[] \\
  every_case_tac \\
  gvs[bridge_source_surface_parse_result_rel_def,
      bridge_source_surface_command_parse_result_rel_def,
      bridge_source_surface_command_rel_def]
QED

Theorem bridge_parse_command_source_surface_tokens_fuel_related:
  ∀fuel var_env str_env source_toks surface_toks.
    bridge_source_surface_token_rel_list var_env str_env
      source_toks surface_toks ⇒
    bridge_source_surface_command_parse_result_rel var_env str_env
      (bridge_parse_source_command_tokens_fuel fuel source_toks)
      (bridge_parse_command_tokens_fuel fuel surface_toks)
Proof
  rw[] \\
  Cases_on ‘source_toks’
  >- (
    Cases_on ‘surface_toks’
    >- (
      rw[bridge_parse_source_command_tokens_fuel_def,
         bridge_parse_command_tokens_fuel_def] \\
      irule bridge_parse_command_add_case_related \\
      rw[bridge_source_surface_token_rel_list_def]) \\
    gvs[bridge_source_surface_token_rel_list_def]) \\
  Cases_on ‘surface_toks’
  >- gvs[bridge_source_surface_token_rel_list_def] \\
  Cases_on ‘h’ \\
  Cases_on ‘h'’ \\
  gvs[bridge_parse_source_command_tokens_fuel_def,
      bridge_parse_command_tokens_fuel_def,
      bridge_source_surface_token_rel_list_def,
      bridge_source_surface_token_rel_def] \\
  TRY (
    irule bridge_parse_command_run_case_related \\
    gvs[bridge_source_surface_token_rel_list_def]) \\
  TRY (
    irule bridge_parse_command_add_case_related \\
    gvs[bridge_source_surface_token_rel_list_def,
        bridge_source_surface_token_rel_def]) \\
  gvs[bridge_source_surface_token_rel_list_def,
      bridge_source_surface_token_rel_def]
QED

Theorem bridge_parse_program_source_surface_tokens_fuel_related:
  ∀fuel var_env str_env source_toks surface_toks.
    bridge_source_surface_token_rel_list var_env str_env
      source_toks surface_toks ⇒
    bridge_source_surface_program_parse_result_rel var_env str_env
      (bridge_parse_source_program_tokens_fuel fuel source_toks)
      (bridge_parse_program_tokens_fuel fuel surface_toks)
Proof
  Induct_on ‘fuel’
  >- (
    Cases_on ‘source_toks’ \\
    Cases_on ‘surface_toks’ \\
    rw[bridge_parse_source_program_tokens_fuel_def,
       bridge_parse_program_tokens_fuel_def,
       bridge_source_surface_token_rel_list_def,
       bridge_source_surface_program_parse_result_rel_def,
       bridge_source_surface_command_rel_list_def]) \\
  rw[] \\
  Cases_on ‘source_toks’ \\
  Cases_on ‘surface_toks’ \\
  gvs[bridge_parse_source_program_tokens_fuel_def,
      bridge_parse_program_tokens_fuel_def,
      bridge_source_surface_token_rel_list_def,
      bridge_source_surface_program_parse_result_rel_def,
      bridge_source_surface_command_rel_list_def] \\
  qspecl_then
    [‘SUC fuel’, ‘var_env’, ‘str_env’, ‘h :: t’, ‘h' :: t'’]
    mp_tac
    bridge_parse_command_source_surface_tokens_fuel_related \\
  impl_tac
  >- gvs[bridge_source_surface_token_rel_list_def] \\
  strip_tac \\
  Cases_on ‘bridge_parse_source_command_tokens_fuel (SUC fuel) (h::t)’ \\
  Cases_on ‘bridge_parse_command_tokens_fuel (SUC fuel) (h'::t')’ \\
  gvs[bridge_source_surface_command_parse_result_rel_def,
      bridge_source_surface_program_parse_result_rel_def] \\
  first_x_assum drule \\
  strip_tac \\
  every_case_tac \\
  gvs[bridge_source_surface_program_parse_result_rel_def,
      bridge_source_surface_command_rel_list_def]
QED

Theorem bridge_source_surface_token_list_parser_simulation:
  ∀fuel var_env str_env source_toks surface_toks.
    bridge_source_surface_token_rel_list var_env str_env
      source_toks surface_toks ⇒
    bridge_source_surface_parse_result_rel var_env str_env
      (bridge_parse_source_atom_tokens_fuel fuel source_toks)
      (bridge_parse_atom_tokens_fuel fuel surface_toks) ∧
    bridge_source_surface_command_parse_result_rel var_env str_env
      (bridge_parse_source_command_tokens_fuel fuel source_toks)
      (bridge_parse_command_tokens_fuel fuel surface_toks) ∧
    bridge_source_surface_program_parse_result_rel var_env str_env
      (bridge_parse_source_program_tokens_fuel fuel source_toks)
      (bridge_parse_program_tokens_fuel fuel surface_toks)
Proof
  metis_tac[bridge_parse_source_surface_full_tokens_related,
            bridge_parse_command_source_surface_tokens_fuel_related,
            bridge_parse_program_source_surface_tokens_fuel_related]
QED

Theorem bridge_source_token_to_bridge_token_full_parser_simulation:
  ∀fuel var_env str_env source_toks bridge_toks.
    bridge_source_surface_token_rel_list var_env str_env
      source_toks bridge_toks ⇒
    bridge_source_surface_parse_result_rel var_env str_env
      (bridge_parse_source_atom_tokens_fuel fuel source_toks)
      (bridge_parse_atom_tokens_fuel fuel bridge_toks) ∧
    bridge_source_surface_command_parse_result_rel var_env str_env
      (bridge_parse_source_command_tokens_fuel fuel source_toks)
      (bridge_parse_command_tokens_fuel fuel bridge_toks) ∧
    bridge_source_surface_program_parse_result_rel var_env str_env
      (bridge_parse_source_program_tokens_fuel fuel source_toks)
      (bridge_parse_program_tokens_fuel fuel bridge_toks)
Proof
  metis_tac[bridge_source_surface_token_list_parser_simulation]
QED

Theorem bridge_source_chars_to_surface_program_parser_related:
  ∀lex_fuel parse_fuel chars source_toks surface_toks var_env str_env.
    bridge_tokenize_source_chars_fuel lex_fuel chars =
      BSourceLexed source_toks ∧
    bridge_source_surface_token_rel_list var_env str_env
      source_toks surface_toks ⇒
    bridge_source_surface_program_parse_result_rel var_env str_env
      (bridge_parse_source_program_chars_fuel
        lex_fuel parse_fuel chars)
      (bridge_parse_program_tokens_fuel parse_fuel surface_toks)
Proof
  rw[bridge_parse_source_program_chars_fuel_def] \\
  metis_tac[bridge_parse_program_source_surface_tokens_fuel_related]
QED

Theorem bridge_source_string_to_surface_program_parser_related:
  ∀lex_fuel parse_fuel text source_toks surface_toks var_env str_env.
    bridge_tokenize_source_string_fuel lex_fuel text =
      BSourceLexed source_toks ∧
    bridge_source_surface_token_rel_list var_env str_env
      source_toks surface_toks ⇒
    bridge_source_surface_program_parse_result_rel var_env str_env
      (bridge_parse_source_program_string_fuel
        lex_fuel parse_fuel text)
      (bridge_parse_program_tokens_fuel parse_fuel surface_toks)
Proof
  rw[bridge_tokenize_source_string_fuel_def,
     bridge_parse_source_program_string_fuel_def] \\
  metis_tac[bridge_source_chars_to_surface_program_parser_related]
QED

Theorem bridge_parse_source_program_chars_fuel_positive_example:
  bridge_parse_source_program_chars_fuel 100 20
    [#"("; #"r"; #"e"; #"t"; #"u"; #"r"; #"n"; #" ";
     #"$"; #"x"; #")"; #"\n";
     #"!"; #"("; #"+"; #" "; #"1"; #" "; #"2"; #")"] =
  BSourceProgramParsed
    [BSrcCmdAdd
       (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")]);
     BSrcCmdRun
       (SrcExpr [SrcSym (strlit"+"); SrcInt 1; SrcInt 2])]
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_program_string_fuel_positive_example:
  bridge_parse_source_program_string_fuel 100 20
    (strlit"(return $x)\n!(+ 1 2)") =
  BSourceProgramParsed
    [BSrcCmdAdd
       (SrcExpr [SrcSym (strlit"return"); SrcVar (strlit"x")]);
     BSrcCmdRun
       (SrcExpr [SrcSym (strlit"+"); SrcInt 1; SrcInt 2])]
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_program_chars_fuel_negative_example:
  bridge_parse_source_program_chars_fuel 10 20 [#"\""; #"h"] =
    BSourceProgramParseError 12
Proof
  EVAL_TAC
QED

Theorem bridge_parse_source_program_string_fuel_negative_example:
  bridge_parse_source_program_string_fuel 10 20 (strlit"$)") =
    BSourceProgramParseError 11
Proof
  EVAL_TAC
QED

Theorem bridge_parse_command_source_surface_positive_example:
  bridge_source_surface_command_parse_result_rel [(strlit"x", 0)] []
    (bridge_parse_source_command_tokens_fuel 10
      [BSrcTokBang;
       BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"return"));
       BSrcTokAtom (SrcVar (strlit"x"));
       BSrcTokRParen])
    (bridge_parse_command_tokens_fuel 10
      [BTokBang;
       BTokLParen;
       BTokAtom (BSym (strlit"return"));
       BTokAtom (BVar 0);
       BTokRParen])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_program_source_surface_positive_example:
  bridge_source_surface_program_parse_result_rel [(strlit"x", 0)] []
    (bridge_parse_source_program_tokens_fuel 20
      [BSrcTokAtom (SrcSym (strlit"A"));
       BSrcTokBang;
       BSrcTokLParen;
       BSrcTokAtom (SrcSym (strlit"return"));
       BSrcTokAtom (SrcVar (strlit"x"));
       BSrcTokRParen])
    (bridge_parse_program_tokens_fuel 20
      [BTokAtom (BSym (strlit"A"));
       BTokBang;
       BTokLParen;
       BTokAtom (BSym (strlit"return"));
       BTokAtom (BVar 0);
       BTokRParen])
Proof
  EVAL_TAC
QED

Theorem bridge_parse_program_source_surface_negative_example:
  ¬bridge_source_surface_program_parse_result_rel [] []
    (bridge_parse_source_program_tokens_fuel 20
      [BSrcTokAtom (SrcVar (strlit"x"))])
    (bridge_parse_program_tokens_fuel 20
      [BTokAtom (BVar 0)])
Proof
  EVAL_TAC
QED

Definition bridge_add_ground_atom_def:
  bridge_add_ground_atom atom =
    case atom of
    | metta_m1$Expr
        [metta_m1$Sym 11; metta_m1$IntLit x; metta_m1$IntLit y] =>
        bridge_add_atom_result x y
    | _ => [atom]
End

Definition bridge_prepend_arg_def:
  bridge_prepend_arg x [] = [] ∧
  bridge_prepend_arg x (metta_m1$Expr ys :: rest) =
    metta_m1$Expr (x :: ys) :: bridge_prepend_arg x rest ∧
  bridge_prepend_arg x (_ :: rest) = bridge_prepend_arg x rest
End

Definition bridge_combine_eval_args_def:
  bridge_combine_eval_args [] yss = [] ∧
  bridge_combine_eval_args (x :: rest) yss =
    bridge_prepend_arg x yss ++ bridge_combine_eval_args rest yss
End

Definition bridge_eval_args2_def:
  bridge_eval_args2 xs ys =
    bridge_combine_eval_args xs
      (bridge_combine_eval_args ys [metta_m1$Expr []])
End

Definition bridge_eval_int_add_values_def:
  bridge_eval_int_add_values [] original = [] ∧
  bridge_eval_int_add_values (atom :: rest) original =
    (case atom of
     | metta_m1$Expr [metta_m1$IntLit x; metta_m1$IntLit y] =>
         metta_m1$IntLit (int_add x y)
     | _ => error_atom original (metta_m1$Sym 10)) ::
    bridge_eval_int_add_values rest original
End

Theorem bridge_eval_int_add_values_append:
  ∀xs ys original.
    bridge_eval_int_add_values (xs ++ ys) original =
    bridge_eval_int_add_values xs original ++
      bridge_eval_int_add_values ys original
Proof
  Induct \\ rw[bridge_eval_int_add_values_def]
QED

Theorem bridge_combine_eval_args_singletons:
  ∀ys.
    bridge_combine_eval_args ys [metta_m1$Expr []] =
    MAP (λy. metta_m1$Expr [y]) ys
Proof
  Induct \\ rw[bridge_combine_eval_args_def, bridge_prepend_arg_def]
QED

Theorem bridge_prepend_arg_pairs:
  ∀x ys.
    bridge_prepend_arg x (MAP (λy. metta_m1$Expr [y]) ys) =
    MAP (λy. metta_m1$Expr [x; y]) ys
Proof
  Induct_on ‘ys’ \\ rw[bridge_prepend_arg_def]
QED

Theorem bridge_eval_int_add_values_pairs:
  ∀x ys original.
    bridge_eval_int_add_values
      (MAP (λy. metta_m1$Expr [x; y]) ys) original =
    rec_add_right original x ys
Proof
  Cases \\ Induct_on ‘ys’ \\
  rw[bridge_eval_int_add_values_def, rec_add_right_def] \\
  Cases_on ‘h’ \\ rw[bridge_eval_int_add_values_def, rec_add_right_def]
QED

Theorem bridge_eval_int_add_values_combine_pairs:
  ∀original xs ys.
    bridge_eval_int_add_values
      (bridge_combine_eval_args xs (MAP (λy. metta_m1$Expr [y]) ys))
      original =
    rec_add_values original xs ys
Proof
  Induct_on ‘xs’ \\
  rw[bridge_combine_eval_args_def, rec_add_values_def,
     bridge_eval_int_add_values_def,
     bridge_eval_int_add_values_append, bridge_prepend_arg_pairs,
     bridge_eval_int_add_values_pairs]
QED

Theorem bridge_eval_int_add_values_args2_matches_rec_add_values:
  ∀original xs ys.
    bridge_eval_int_add_values (bridge_eval_args2 xs ys) original =
    rec_add_values original xs ys
Proof
  rw[bridge_eval_args2_def, bridge_combine_eval_args_singletons,
     bridge_eval_int_add_values_combine_pairs]
QED

Definition bridge_eval_add_values_fragment_def:
  bridge_eval_add_values_fragment original xs ys =
    bridge_eval_int_add_values (bridge_eval_args2 xs ys) original
End

Theorem bridge_eval_add_values_fragment_matches_rec_add_values:
  ∀original xs ys.
    bridge_eval_add_values_fragment original xs ys =
    rec_add_values original xs ys
Proof
  rw[bridge_eval_add_values_fragment_def,
     bridge_eval_int_add_values_args2_matches_rec_add_values]
QED

Definition bridge_surface_eval_add_values_wrapper_def:
  bridge_surface_eval_add_values_wrapper surface_original surface_xs surface_ys =
    case bridge_import_surface_atom surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_add_values_fragment original xs ys))
End

Definition bridge_surface_eval_add_evaluated_args_wrapper_def:
  bridge_surface_eval_add_evaluated_args_wrapper
    surface_original surface_xs surface_ys =
      bridge_surface_eval_add_values_wrapper
        surface_original surface_xs surface_ys
End

Definition bridge_surface_eval_add_values_wrapper_with_env_def:
  bridge_surface_eval_add_values_wrapper_with_env
    env surface_original surface_xs surface_ys =
    case bridge_import_surface_atom_with_env env surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list_with_env env surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list_with_env env surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_add_values_fragment original xs ys))
End

Definition bridge_surface_eval_add_evaluated_args_wrapper_with_env_def:
  bridge_surface_eval_add_evaluated_args_wrapper_with_env
    env surface_original surface_xs surface_ys =
      bridge_surface_eval_add_values_wrapper_with_env
        env surface_original surface_xs surface_ys
End

Theorem bridge_surface_eval_add_values_wrapper_import:
  ∀surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    bridge_surface_eval_add_values_wrapper
      surface_original surface_xs surface_ys =
    bridge_eval_add_values_fragment original xs ys
Proof
  rw[bridge_surface_eval_add_values_wrapper_def]
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_import:
  ∀surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    bridge_surface_eval_add_evaluated_args_wrapper
      surface_original surface_xs surface_ys =
    bridge_eval_add_values_fragment original xs ys
Proof
  rw[bridge_surface_eval_add_evaluated_args_wrapper_def,
     bridge_surface_eval_add_values_wrapper_import]
QED

Theorem bridge_surface_eval_add_values_wrapper_with_env_import:
  ∀env surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    bridge_surface_eval_add_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    bridge_eval_add_values_fragment original xs ys
Proof
  rw[bridge_surface_eval_add_values_wrapper_with_env_def]
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_with_env_import:
  ∀env surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    bridge_surface_eval_add_evaluated_args_wrapper_with_env
      env surface_original surface_xs surface_ys =
    bridge_eval_add_values_fragment original xs ys
Proof
  rw[bridge_surface_eval_add_evaluated_args_wrapper_with_env_def,
     bridge_surface_eval_add_values_wrapper_with_env_import]
QED

Theorem bridge_surface_eval_add_values_wrapper_matches_rec_add_values:
  ∀surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    bridge_surface_eval_add_values_wrapper
      surface_original surface_xs surface_ys =
    rec_add_values original xs ys
Proof
  gvs[bridge_surface_eval_add_values_wrapper_def,
      bridge_eval_add_values_fragment_matches_rec_add_values]
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_matches_rec_add_values:
  ∀surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    bridge_surface_eval_add_evaluated_args_wrapper
      surface_original surface_xs surface_ys =
    rec_add_values original xs ys
Proof
  rw[bridge_surface_eval_add_evaluated_args_wrapper_def,
     bridge_surface_eval_add_values_wrapper_matches_rec_add_values]
QED

Theorem bridge_surface_eval_add_values_wrapper_with_env_matches_rec_add_values:
  ∀env surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    bridge_surface_eval_add_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_add_values original xs ys
Proof
  gvs[bridge_surface_eval_add_values_wrapper_with_env_def,
      bridge_eval_add_values_fragment_matches_rec_add_values]
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_with_env_matches_rec_add_values:
  ∀env surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    bridge_surface_eval_add_evaluated_args_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_add_values original xs ys
Proof
  rw[bridge_surface_eval_add_evaluated_args_wrapper_with_env_def,
     bridge_surface_eval_add_values_wrapper_with_env_matches_rec_add_values]
QED

Theorem bridge_surface_eval_add_values_wrapper_positive_example:
  bridge_surface_eval_add_values_wrapper
    (BExpr [BSym (strlit"+"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  [metta_m1$IntLit 5]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_positive_example:
  bridge_surface_eval_add_evaluated_args_wrapper
    (BExpr [BSym (strlit"+"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  [metta_m1$IntLit 5]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_with_env_dynamic_example:
  bridge_surface_eval_add_evaluated_args_wrapper_with_env
    [(strlit"Foo", 1000)]
    (BExpr [BSym (strlit"Foo"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  [metta_m1$IntLit 5]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_add_values_wrapper_negative_example:
  bridge_surface_eval_add_values_wrapper
    (BExpr [BSym (strlit"not-a-core-symbol"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_negative_example:
  bridge_surface_eval_add_evaluated_args_wrapper
    (BExpr [BSym (strlit"not-a-core-symbol"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_with_env_negative_example:
  bridge_surface_eval_add_evaluated_args_wrapper_with_env []
    (BExpr [BSym (strlit"Foo"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_lt_values_def:
  bridge_eval_lt_values [] original = [] ∧
  bridge_eval_lt_values (atom :: rest) original =
    (case atom of
     | metta_m1$Expr [metta_m1$IntLit x; metta_m1$IntLit y] =>
         if int_lt x y then metta_m1$Sym 8 else metta_m1$Sym 9
     | _ => error_atom original (metta_m1$Sym 10)) ::
    bridge_eval_lt_values rest original
End

Theorem bridge_eval_lt_values_append:
  ∀xs ys original.
    bridge_eval_lt_values (xs ++ ys) original =
    bridge_eval_lt_values xs original ++ bridge_eval_lt_values ys original
Proof
  Induct \\ rw[bridge_eval_lt_values_def]
QED

Theorem bridge_eval_lt_values_pairs:
  ∀x ys original.
    bridge_eval_lt_values
      (MAP (λy. metta_m1$Expr [x; y]) ys) original =
    rec_lt_right original x ys
Proof
  Cases \\ Induct_on ‘ys’ \\
  rw[bridge_eval_lt_values_def, rec_lt_right_def] \\
  Cases_on ‘h’ \\ rw[bridge_eval_lt_values_def, rec_lt_right_def]
QED

Theorem bridge_eval_lt_values_combine_pairs:
  ∀original xs ys.
    bridge_eval_lt_values
      (bridge_combine_eval_args xs (MAP (λy. metta_m1$Expr [y]) ys))
      original =
    rec_lt_values original xs ys
Proof
  Induct_on ‘xs’ \\
  rw[bridge_combine_eval_args_def, rec_lt_values_def,
     bridge_eval_lt_values_def,
     bridge_eval_lt_values_append, bridge_prepend_arg_pairs,
     bridge_eval_lt_values_pairs]
QED

Theorem bridge_eval_lt_values_args2_matches_rec_lt_values:
  ∀original xs ys.
    bridge_eval_lt_values (bridge_eval_args2 xs ys) original =
    rec_lt_values original xs ys
Proof
  rw[bridge_eval_args2_def, bridge_combine_eval_args_singletons,
     bridge_eval_lt_values_combine_pairs]
QED

Definition bridge_eval_lt_values_fragment_def:
  bridge_eval_lt_values_fragment original xs ys =
    bridge_eval_lt_values (bridge_eval_args2 xs ys) original
End

Theorem bridge_eval_lt_values_fragment_matches_rec_lt_values:
  ∀original xs ys.
    bridge_eval_lt_values_fragment original xs ys =
    rec_lt_values original xs ys
Proof
  rw[bridge_eval_lt_values_fragment_def,
     bridge_eval_lt_values_args2_matches_rec_lt_values]
QED

Definition bridge_eval_eq_values_def:
  bridge_eval_eq_values [] original = [] ∧
  bridge_eval_eq_values (atom :: rest) original =
    (case atom of
     | metta_m1$Expr [x; y] =>
         if x = y then metta_m1$Sym 8 else metta_m1$Sym 9
     | _ => error_atom original (metta_m1$Sym 10)) ::
    bridge_eval_eq_values rest original
End

Theorem bridge_eval_eq_values_append:
  ∀xs ys original.
    bridge_eval_eq_values (xs ++ ys) original =
    bridge_eval_eq_values xs original ++ bridge_eval_eq_values ys original
Proof
  Induct \\ rw[bridge_eval_eq_values_def]
QED

Theorem bridge_eval_eq_values_pairs:
  ∀x ys original.
    bridge_eval_eq_values
      (MAP (λy. metta_m1$Expr [x; y]) ys) original =
    rec_eq_right original x ys
Proof
  Induct_on ‘ys’ \\ rw[bridge_eval_eq_values_def, rec_eq_right_def]
QED

Theorem bridge_eval_eq_values_combine_pairs:
  ∀original xs ys.
    bridge_eval_eq_values
      (bridge_combine_eval_args xs (MAP (λy. metta_m1$Expr [y]) ys))
      original =
    rec_eq_values original xs ys
Proof
  Induct_on ‘xs’ \\
  rw[bridge_combine_eval_args_def, rec_eq_values_def,
     bridge_eval_eq_values_def,
     bridge_eval_eq_values_append, bridge_prepend_arg_pairs,
     bridge_eval_eq_values_pairs]
QED

Theorem bridge_eval_eq_values_args2_matches_rec_eq_values:
  ∀original xs ys.
    bridge_eval_eq_values (bridge_eval_args2 xs ys) original =
    rec_eq_values original xs ys
Proof
  rw[bridge_eval_args2_def, bridge_combine_eval_args_singletons,
     bridge_eval_eq_values_combine_pairs]
QED

Definition bridge_eval_eq_values_fragment_def:
  bridge_eval_eq_values_fragment original xs ys =
    bridge_eval_eq_values (bridge_eval_args2 xs ys) original
End

Theorem bridge_eval_eq_values_fragment_matches_rec_eq_values:
  ∀original xs ys.
    bridge_eval_eq_values_fragment original xs ys =
    rec_eq_values original xs ys
Proof
  rw[bridge_eval_eq_values_fragment_def,
     bridge_eval_eq_values_args2_matches_rec_eq_values]
QED

Definition bridge_eval_and_values_def:
  bridge_eval_and_values [] original = [] ∧
  bridge_eval_and_values (atom :: rest) original =
    (case atom of
     | metta_m1$Expr [x; y] => bool_and_result original x y
     | _ => error_atom original (metta_m1$Sym 10)) ::
    bridge_eval_and_values rest original
End

Theorem bridge_eval_and_values_append:
  ∀xs ys original.
    bridge_eval_and_values (xs ++ ys) original =
    bridge_eval_and_values xs original ++ bridge_eval_and_values ys original
Proof
  Induct \\ rw[bridge_eval_and_values_def]
QED

Theorem bridge_eval_and_values_pairs:
  ∀x ys original.
    bridge_eval_and_values
      (MAP (λy. metta_m1$Expr [x; y]) ys) original =
    rec_and_right original x ys
Proof
  Induct_on ‘ys’ \\ rw[bridge_eval_and_values_def, rec_and_right_def]
QED

Theorem bridge_eval_and_values_combine_pairs:
  ∀original xs ys.
    bridge_eval_and_values
      (bridge_combine_eval_args xs (MAP (λy. metta_m1$Expr [y]) ys))
      original =
    rec_and_values original xs ys
Proof
  Induct_on ‘xs’ \\
  rw[bridge_combine_eval_args_def, rec_and_values_def,
     bridge_eval_and_values_def,
     bridge_eval_and_values_append, bridge_prepend_arg_pairs,
     bridge_eval_and_values_pairs]
QED

Theorem bridge_eval_and_values_args2_matches_rec_and_values:
  ∀original xs ys.
    bridge_eval_and_values (bridge_eval_args2 xs ys) original =
    rec_and_values original xs ys
Proof
  rw[bridge_eval_args2_def, bridge_combine_eval_args_singletons,
     bridge_eval_and_values_combine_pairs]
QED

Definition bridge_eval_and_values_fragment_def:
  bridge_eval_and_values_fragment original xs ys =
    bridge_eval_and_values (bridge_eval_args2 xs ys) original
End

Theorem bridge_eval_and_values_fragment_matches_rec_and_values:
  ∀original xs ys.
    bridge_eval_and_values_fragment original xs ys =
    rec_and_values original xs ys
Proof
  rw[bridge_eval_and_values_fragment_def,
     bridge_eval_and_values_args2_matches_rec_and_values]
QED

Definition bridge_eval_or_values_def:
  bridge_eval_or_values [] original = [] ∧
  bridge_eval_or_values (atom :: rest) original =
    (case atom of
     | metta_m1$Expr [x; y] => bool_or_result original x y
     | _ => error_atom original (metta_m1$Sym 10)) ::
    bridge_eval_or_values rest original
End

Theorem bridge_eval_or_values_append:
  ∀xs ys original.
    bridge_eval_or_values (xs ++ ys) original =
    bridge_eval_or_values xs original ++ bridge_eval_or_values ys original
Proof
  Induct \\ rw[bridge_eval_or_values_def]
QED

Theorem bridge_eval_or_values_pairs:
  ∀x ys original.
    bridge_eval_or_values
      (MAP (λy. metta_m1$Expr [x; y]) ys) original =
    rec_or_right original x ys
Proof
  Induct_on ‘ys’ \\ rw[bridge_eval_or_values_def, rec_or_right_def]
QED

Theorem bridge_eval_or_values_combine_pairs:
  ∀original xs ys.
    bridge_eval_or_values
      (bridge_combine_eval_args xs (MAP (λy. metta_m1$Expr [y]) ys))
      original =
    rec_or_values original xs ys
Proof
  Induct_on ‘xs’ \\
  rw[bridge_combine_eval_args_def, rec_or_values_def,
     bridge_eval_or_values_def,
     bridge_eval_or_values_append, bridge_prepend_arg_pairs,
     bridge_eval_or_values_pairs]
QED

Theorem bridge_eval_or_values_args2_matches_rec_or_values:
  ∀original xs ys.
    bridge_eval_or_values (bridge_eval_args2 xs ys) original =
    rec_or_values original xs ys
Proof
  rw[bridge_eval_args2_def, bridge_combine_eval_args_singletons,
     bridge_eval_or_values_combine_pairs]
QED

Definition bridge_eval_or_values_fragment_def:
  bridge_eval_or_values_fragment original xs ys =
    bridge_eval_or_values (bridge_eval_args2 xs ys) original
End

Theorem bridge_eval_or_values_fragment_matches_rec_or_values:
  ∀original xs ys.
    bridge_eval_or_values_fragment original xs ys =
    rec_or_values original xs ys
Proof
  rw[bridge_eval_or_values_fragment_def,
     bridge_eval_or_values_args2_matches_rec_or_values]
QED

Definition bridge_eval_not_values_def:
  bridge_eval_not_values [] original = [] ∧
  bridge_eval_not_values (x :: xs) original =
    bool_not_result original x :: bridge_eval_not_values xs original
End

Theorem bridge_eval_not_values_matches_rec_not_values:
  ∀original xs.
    bridge_eval_not_values xs original = rec_not_values original xs
Proof
  Induct_on ‘xs’ \\ rw[bridge_eval_not_values_def, rec_not_values_def]
QED

Definition bridge_eval_not_values_fragment_def:
  bridge_eval_not_values_fragment original xs =
    bridge_eval_not_values xs original
End

Theorem bridge_eval_not_values_fragment_matches_rec_not_values:
  ∀original xs.
    bridge_eval_not_values_fragment original xs =
    rec_not_values original xs
Proof
  rw[bridge_eval_not_values_fragment_def,
     bridge_eval_not_values_matches_rec_not_values]
QED

Definition bridge_surface_eval_lt_values_wrapper_def:
  bridge_surface_eval_lt_values_wrapper surface_original surface_xs surface_ys =
    case bridge_import_surface_atom surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_lt_values_fragment original xs ys))
End

Theorem bridge_surface_eval_lt_values_wrapper_matches_rec_lt_values:
  ∀surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    bridge_surface_eval_lt_values_wrapper
      surface_original surface_xs surface_ys =
    rec_lt_values original xs ys
Proof
  gvs[bridge_surface_eval_lt_values_wrapper_def,
      bridge_eval_lt_values_fragment_matches_rec_lt_values]
QED

Theorem bridge_surface_eval_lt_values_wrapper_positive_example:
  bridge_surface_eval_lt_values_wrapper
    (BExpr [BSym (strlit"<"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_lt_values_wrapper_negative_example:
  bridge_surface_eval_lt_values_wrapper
    (BExpr [BSym (strlit"not-a-core-symbol"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  []
Proof
  EVAL_TAC
QED

Definition bridge_surface_eval_eq_values_wrapper_def:
  bridge_surface_eval_eq_values_wrapper surface_original surface_xs surface_ys =
    case bridge_import_surface_atom surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_eq_values_fragment original xs ys))
End

Theorem bridge_surface_eval_eq_values_wrapper_matches_rec_eq_values:
  ∀surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    bridge_surface_eval_eq_values_wrapper
      surface_original surface_xs surface_ys =
    rec_eq_values original xs ys
Proof
  gvs[bridge_surface_eval_eq_values_wrapper_def,
      bridge_eval_eq_values_fragment_matches_rec_eq_values]
QED

Theorem bridge_surface_eval_eq_values_wrapper_positive_example:
  bridge_surface_eval_eq_values_wrapper
    (BExpr [BSym (strlit"=="); BInt 2; BInt 2])
    [BInt 2] [BInt 2] =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_eq_values_wrapper_negative_example:
  bridge_surface_eval_eq_values_wrapper
    (BExpr [BSym (strlit"not-a-core-symbol"); BInt 2; BInt 2])
    [BInt 2] [BInt 2] =
  []
Proof
  EVAL_TAC
QED

Definition bridge_surface_eval_and_values_wrapper_def:
  bridge_surface_eval_and_values_wrapper surface_original surface_xs surface_ys =
    case bridge_import_surface_atom surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_and_values_fragment original xs ys))
End

Theorem bridge_surface_eval_and_values_wrapper_matches_rec_and_values:
  ∀surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    bridge_surface_eval_and_values_wrapper
      surface_original surface_xs surface_ys =
    rec_and_values original xs ys
Proof
  gvs[bridge_surface_eval_and_values_wrapper_def,
      bridge_eval_and_values_fragment_matches_rec_and_values]
QED

Theorem bridge_surface_eval_and_values_wrapper_positive_example:
  bridge_surface_eval_and_values_wrapper
    (BExpr [BSym (strlit"and"); BSym (strlit"True");
            BSym (strlit"False")])
    [BSym (strlit"True")] [BSym (strlit"False")] =
  [metta_m1$Sym 9]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_and_values_wrapper_negative_example:
  bridge_surface_eval_and_values_wrapper
    (BExpr [BSym (strlit"not-a-core-symbol"); BSym (strlit"True");
            BSym (strlit"False")])
    [BSym (strlit"True")] [BSym (strlit"False")] =
  []
Proof
  EVAL_TAC
QED

Definition bridge_surface_eval_or_values_wrapper_def:
  bridge_surface_eval_or_values_wrapper surface_original surface_xs surface_ys =
    case bridge_import_surface_atom surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_or_values_fragment original xs ys))
End

Theorem bridge_surface_eval_or_values_wrapper_matches_rec_or_values:
  ∀surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    bridge_surface_eval_or_values_wrapper
      surface_original surface_xs surface_ys =
    rec_or_values original xs ys
Proof
  gvs[bridge_surface_eval_or_values_wrapper_def,
      bridge_eval_or_values_fragment_matches_rec_or_values]
QED

Theorem bridge_surface_eval_or_values_wrapper_positive_example:
  bridge_surface_eval_or_values_wrapper
    (BExpr [BSym (strlit"or"); BSym (strlit"True");
            BSym (strlit"False")])
    [BSym (strlit"True")] [BSym (strlit"False")] =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_or_values_wrapper_negative_example:
  bridge_surface_eval_or_values_wrapper
    (BExpr [BSym (strlit"not-a-core-symbol"); BSym (strlit"True");
            BSym (strlit"False")])
    [BSym (strlit"True")] [BSym (strlit"False")] =
  []
Proof
  EVAL_TAC
QED

Definition bridge_surface_eval_not_values_wrapper_def:
  bridge_surface_eval_not_values_wrapper surface_original surface_xs =
    case bridge_import_surface_atom surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list surface_xs of
         | NONE => []
         | SOME xs => bridge_eval_not_values_fragment original xs)
End

Theorem bridge_surface_eval_not_values_wrapper_matches_rec_not_values:
  ∀surface_original surface_xs original xs.
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ⇒
    bridge_surface_eval_not_values_wrapper surface_original surface_xs =
    rec_not_values original xs
Proof
  gvs[bridge_surface_eval_not_values_wrapper_def,
      bridge_eval_not_values_fragment_matches_rec_not_values]
QED

Theorem bridge_surface_eval_not_values_wrapper_positive_example:
  bridge_surface_eval_not_values_wrapper
    (BExpr [BSym (strlit"not"); BSym (strlit"False")])
    [BSym (strlit"False")] =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_not_values_wrapper_negative_example:
  bridge_surface_eval_not_values_wrapper
    (BExpr [BSym (strlit"not-a-core-symbol"); BSym (strlit"False")])
    [BSym (strlit"False")] =
  []
Proof
  EVAL_TAC
QED

Definition bridge_surface_eval_lt_values_wrapper_with_env_def:
  bridge_surface_eval_lt_values_wrapper_with_env
    env surface_original surface_xs surface_ys =
    case bridge_import_surface_atom_with_env env surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list_with_env env surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list_with_env env surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_lt_values_fragment original xs ys))
End

Theorem bridge_surface_eval_lt_values_wrapper_with_env_matches_rec_lt_values:
  ∀env surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    bridge_surface_eval_lt_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_lt_values original xs ys
Proof
  gvs[bridge_surface_eval_lt_values_wrapper_with_env_def,
      bridge_eval_lt_values_fragment_matches_rec_lt_values]
QED

Definition bridge_surface_eval_eq_values_wrapper_with_env_def:
  bridge_surface_eval_eq_values_wrapper_with_env
    env surface_original surface_xs surface_ys =
    case bridge_import_surface_atom_with_env env surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list_with_env env surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list_with_env env surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_eq_values_fragment original xs ys))
End

Theorem bridge_surface_eval_eq_values_wrapper_with_env_matches_rec_eq_values:
  ∀env surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    bridge_surface_eval_eq_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_eq_values original xs ys
Proof
  gvs[bridge_surface_eval_eq_values_wrapper_with_env_def,
      bridge_eval_eq_values_fragment_matches_rec_eq_values]
QED

Definition bridge_surface_eval_and_values_wrapper_with_env_def:
  bridge_surface_eval_and_values_wrapper_with_env
    env surface_original surface_xs surface_ys =
    case bridge_import_surface_atom_with_env env surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list_with_env env surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list_with_env env surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_and_values_fragment original xs ys))
End

Theorem bridge_surface_eval_and_values_wrapper_with_env_matches_rec_and_values:
  ∀env surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    bridge_surface_eval_and_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_and_values original xs ys
Proof
  gvs[bridge_surface_eval_and_values_wrapper_with_env_def,
      bridge_eval_and_values_fragment_matches_rec_and_values]
QED

Definition bridge_surface_eval_or_values_wrapper_with_env_def:
  bridge_surface_eval_or_values_wrapper_with_env
    env surface_original surface_xs surface_ys =
    case bridge_import_surface_atom_with_env env surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list_with_env env surface_xs of
         | NONE => []
         | SOME xs =>
             (case bridge_import_surface_atom_list_with_env env surface_ys of
              | NONE => []
              | SOME ys => bridge_eval_or_values_fragment original xs ys))
End

Theorem bridge_surface_eval_or_values_wrapper_with_env_matches_rec_or_values:
  ∀env surface_original surface_xs surface_ys original xs ys.
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    bridge_surface_eval_or_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_or_values original xs ys
Proof
  gvs[bridge_surface_eval_or_values_wrapper_with_env_def,
      bridge_eval_or_values_fragment_matches_rec_or_values]
QED

Definition bridge_surface_eval_not_values_wrapper_with_env_def:
  bridge_surface_eval_not_values_wrapper_with_env
    env surface_original surface_xs =
    case bridge_import_surface_atom_with_env env surface_original of
    | NONE => []
    | SOME original =>
        (case bridge_import_surface_atom_list_with_env env surface_xs of
         | NONE => []
         | SOME xs => bridge_eval_not_values_fragment original xs)
End

Theorem bridge_surface_eval_not_values_wrapper_with_env_matches_rec_not_values:
  ∀env surface_original surface_xs original xs.
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ⇒
    bridge_surface_eval_not_values_wrapper_with_env
      env surface_original surface_xs =
    rec_not_values original xs
Proof
  gvs[bridge_surface_eval_not_values_wrapper_with_env_def,
      bridge_eval_not_values_fragment_matches_rec_not_values]
QED

Theorem bridge_surface_eval_lt_values_wrapper_with_env_dynamic_example:
  bridge_surface_eval_lt_values_wrapper_with_env [(strlit"Foo", 1000)]
    (BExpr [BSym (strlit"Foo"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_eq_values_wrapper_with_env_dynamic_example:
  bridge_surface_eval_eq_values_wrapper_with_env [(strlit"Foo", 1000)]
    (BExpr [BSym (strlit"Foo"); BInt 2; BInt 2])
    [BInt 2] [BInt 2] =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_and_values_wrapper_with_env_dynamic_example:
  bridge_surface_eval_and_values_wrapper_with_env [(strlit"Foo", 1000)]
    (BExpr [BSym (strlit"Foo"); BSym (strlit"True");
            BSym (strlit"False")])
    [BSym (strlit"True")] [BSym (strlit"False")] =
  [metta_m1$Sym 9]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_or_values_wrapper_with_env_dynamic_example:
  bridge_surface_eval_or_values_wrapper_with_env [(strlit"Foo", 1000)]
    (BExpr [BSym (strlit"Foo"); BSym (strlit"True");
            BSym (strlit"False")])
    [BSym (strlit"True")] [BSym (strlit"False")] =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_not_values_wrapper_with_env_dynamic_example:
  bridge_surface_eval_not_values_wrapper_with_env [(strlit"Foo", 1000)]
    (BExpr [BSym (strlit"Foo"); BSym (strlit"False")])
    [BSym (strlit"False")] =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_lt_values_wrapper_with_env_negative_example:
  bridge_surface_eval_lt_values_wrapper_with_env []
    (BExpr [BSym (strlit"Foo"); BInt 2; BInt 3])
    [BInt 2] [BInt 3] =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_eq_values_wrapper_with_env_negative_example:
  bridge_surface_eval_eq_values_wrapper_with_env []
    (BExpr [BSym (strlit"Foo"); BInt 2; BInt 2])
    [BInt 2] [BInt 2] =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_and_values_wrapper_with_env_negative_example:
  bridge_surface_eval_and_values_wrapper_with_env []
    (BExpr [BSym (strlit"Foo"); BSym (strlit"True");
            BSym (strlit"False")])
    [BSym (strlit"True")] [BSym (strlit"False")] =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_or_values_wrapper_with_env_negative_example:
  bridge_surface_eval_or_values_wrapper_with_env []
    (BExpr [BSym (strlit"Foo"); BSym (strlit"True");
            BSym (strlit"False")])
    [BSym (strlit"True")] [BSym (strlit"False")] =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_not_values_wrapper_with_env_negative_example:
  bridge_surface_eval_not_values_wrapper_with_env []
    (BExpr [BSym (strlit"Foo"); BSym (strlit"False")])
    [BSym (strlit"False")] =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_add_fragment_def:
  bridge_eval_add_fragment fuel space atom =
    case atom of
    | metta_m1$Expr [metta_m1$Sym 11; a; b] =>
        bridge_eval_int_add_values
          (bridge_eval_args2
            (eval_m1_rec fuel space a)
            (eval_m1_rec fuel space b))
          atom
    | _ => [atom]
End

Theorem bridge_eval_add_fragment_matches_eval_add_fragment:
  ∀fuel space a b.
    bridge_eval_add_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 11; a; b]) =
    eval_add_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 11; a; b])
Proof
  rw[bridge_eval_add_fragment_def, eval_add_fragment_def,
     bridge_eval_int_add_values_args2_matches_rec_add_values]
QED

Theorem bridge_eval_add_fragment_agrees_with_eval_m1_rec:
  ∀fuel space a b.
    bridge_eval_add_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 11; a; b]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 11; a; b])
Proof
  rw[bridge_eval_add_fragment_matches_eval_add_fragment,
     eval_add_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_eval_add_fragment_via_values_fragment:
  ∀fuel space a b.
    bridge_eval_add_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 11; a; b]) =
    bridge_eval_add_values_fragment
      (metta_m1$Expr [metta_m1$Sym 11; a; b])
      (eval_m1_rec fuel space a)
      (eval_m1_rec fuel space b)
Proof
  rw[bridge_eval_add_fragment_def, bridge_eval_add_values_fragment_def]
QED

Definition bridge_surface_eval_add_fragment_wrapper_def:
  bridge_surface_eval_add_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_add_fragment fuel space atom)
End

Theorem bridge_surface_eval_add_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space a b space atom_a atom_b.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom a = SOME atom_a ∧
    bridge_import_surface_atom b = SOME atom_b ⇒
    bridge_surface_eval_add_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"+"); a; b]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 11; atom_a; atom_b])
Proof
  rw[bridge_surface_eval_add_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_add_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_add_fragment_wrapper_via_values:
  ∀fuel surface_space a b space atom_a atom_b.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom a = SOME atom_a ∧
    bridge_import_surface_atom b = SOME atom_b ⇒
    bridge_surface_eval_add_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"+"); a; b]) =
    bridge_eval_add_values_fragment
      (metta_m1$Expr [metta_m1$Sym 11; atom_a; atom_b])
      (eval_m1_rec fuel space atom_a)
      (eval_m1_rec fuel space atom_b)
Proof
  rw[bridge_surface_eval_add_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_add_fragment_via_values_fragment]
QED

Theorem bridge_surface_eval_add_fragment_wrapper_positive_example:
  bridge_surface_eval_add_fragment_wrapper 1 []
    (BExpr [BSym (strlit"+"); BInt 2; BInt 3]) =
  [metta_m1$IntLit 5]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_add_fragment_wrapper_evaluated_arg_example:
  bridge_surface_eval_add_fragment_wrapper 2 []
    (BExpr
      [BSym (strlit"+");
       BExpr [BSym (strlit"+"); BInt 1; BInt 2];
       BInt 4]) =
  [metta_m1$IntLit 7]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_add_fragment_wrapper_negative_example:
  bridge_surface_eval_add_fragment_wrapper 1 []
    (BExpr [BSym (strlit"not-a-core-symbol"); BInt 2; BInt 3]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_lt_fragment_def:
  bridge_eval_lt_fragment fuel space atom =
    case atom of
    | metta_m1$Expr [metta_m1$Sym 12; a; b] =>
        bridge_eval_lt_values
          (bridge_eval_args2
            (eval_m1_rec fuel space a)
            (eval_m1_rec fuel space b))
          atom
    | _ => [atom]
End

Theorem bridge_eval_lt_fragment_agrees_with_eval_m1_rec:
  ∀fuel space a b.
    bridge_eval_lt_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 12; a; b]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 12; a; b])
Proof
  rw[bridge_eval_lt_fragment_def, eval_m1_rec_def,
     bridge_eval_lt_values_args2_matches_rec_lt_values]
QED

Theorem bridge_eval_lt_fragment_via_values_fragment:
  ∀fuel space a b.
    bridge_eval_lt_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 12; a; b]) =
    bridge_eval_lt_values_fragment
      (metta_m1$Expr [metta_m1$Sym 12; a; b])
      (eval_m1_rec fuel space a)
      (eval_m1_rec fuel space b)
Proof
  rw[bridge_eval_lt_fragment_def, bridge_eval_lt_values_fragment_def]
QED

Definition bridge_surface_eval_lt_fragment_wrapper_def:
  bridge_surface_eval_lt_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_lt_fragment fuel space atom)
End

Theorem bridge_surface_eval_lt_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space a b space atom_a atom_b.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom a = SOME atom_a ∧
    bridge_import_surface_atom b = SOME atom_b ⇒
    bridge_surface_eval_lt_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"<"); a; b]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 12; atom_a; atom_b])
Proof
  rw[bridge_surface_eval_lt_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_lt_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_lt_fragment_wrapper_positive_example:
  bridge_surface_eval_lt_fragment_wrapper 1 []
    (BExpr [BSym (strlit"<"); BInt 2; BInt 3]) =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_lt_fragment_wrapper_negative_example:
  bridge_surface_eval_lt_fragment_wrapper 1 []
    (BExpr [BSym (strlit"not-a-core-symbol"); BInt 2; BInt 3]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_eq_fragment_def:
  bridge_eval_eq_fragment fuel space atom =
    case atom of
    | metta_m1$Expr [metta_m1$Sym 47; a; b] =>
        bridge_eval_eq_values
          (bridge_eval_args2
            (eval_m1_rec fuel space a)
            (eval_m1_rec fuel space b))
          atom
    | _ => [atom]
End

Theorem bridge_eval_eq_fragment_agrees_with_eval_m1_rec:
  ∀fuel space a b.
    bridge_eval_eq_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 47; a; b]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 47; a; b])
Proof
  rw[bridge_eval_eq_fragment_def, eval_m1_rec_def,
     bridge_eval_eq_values_args2_matches_rec_eq_values]
QED

Theorem bridge_eval_eq_fragment_via_values_fragment:
  ∀fuel space a b.
    bridge_eval_eq_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 47; a; b]) =
    bridge_eval_eq_values_fragment
      (metta_m1$Expr [metta_m1$Sym 47; a; b])
      (eval_m1_rec fuel space a)
      (eval_m1_rec fuel space b)
Proof
  rw[bridge_eval_eq_fragment_def, bridge_eval_eq_values_fragment_def]
QED

Definition bridge_surface_eval_eq_fragment_wrapper_def:
  bridge_surface_eval_eq_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_eq_fragment fuel space atom)
End

Theorem bridge_surface_eval_eq_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space a b space atom_a atom_b.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom a = SOME atom_a ∧
    bridge_import_surface_atom b = SOME atom_b ⇒
    bridge_surface_eval_eq_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"=="); a; b]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 47; atom_a; atom_b])
Proof
  rw[bridge_surface_eval_eq_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_eq_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_eq_fragment_wrapper_positive_example:
  bridge_surface_eval_eq_fragment_wrapper 1 []
    (BExpr [BSym (strlit"=="); BInt 2; BInt 2]) =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_eq_fragment_wrapper_negative_example:
  bridge_surface_eval_eq_fragment_wrapper 1 []
    (BExpr [BSym (strlit"not-a-core-symbol"); BInt 2; BInt 2]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_and_fragment_def:
  bridge_eval_and_fragment fuel space atom =
    case atom of
    | metta_m1$Expr [metta_m1$Sym 31; a; b] =>
        bridge_eval_and_values
          (bridge_eval_args2
            (eval_m1_rec fuel space a)
            (eval_m1_rec fuel space b))
          atom
    | _ => [atom]
End

Theorem bridge_eval_and_fragment_agrees_with_eval_m1_rec:
  ∀fuel space a b.
    bridge_eval_and_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 31; a; b]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 31; a; b])
Proof
  rw[bridge_eval_and_fragment_def, eval_m1_rec_def,
     bridge_eval_and_values_args2_matches_rec_and_values]
QED

Theorem bridge_eval_and_fragment_via_values_fragment:
  ∀fuel space a b.
    bridge_eval_and_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 31; a; b]) =
    bridge_eval_and_values_fragment
      (metta_m1$Expr [metta_m1$Sym 31; a; b])
      (eval_m1_rec fuel space a)
      (eval_m1_rec fuel space b)
Proof
  rw[bridge_eval_and_fragment_def, bridge_eval_and_values_fragment_def]
QED

Definition bridge_surface_eval_and_fragment_wrapper_def:
  bridge_surface_eval_and_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_and_fragment fuel space atom)
End

Theorem bridge_surface_eval_and_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space a b space atom_a atom_b.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom a = SOME atom_a ∧
    bridge_import_surface_atom b = SOME atom_b ⇒
    bridge_surface_eval_and_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"and"); a; b]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 31; atom_a; atom_b])
Proof
  rw[bridge_surface_eval_and_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_and_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_and_fragment_wrapper_positive_example:
  bridge_surface_eval_and_fragment_wrapper 1 []
    (BExpr [BSym (strlit"and"); BSym (strlit"True");
            BSym (strlit"False")]) =
  [metta_m1$Sym 9]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_and_fragment_wrapper_negative_example:
  bridge_surface_eval_and_fragment_wrapper 1 []
    (BExpr [BSym (strlit"not-a-core-symbol"); BSym (strlit"True");
            BSym (strlit"False")]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_or_fragment_def:
  bridge_eval_or_fragment fuel space atom =
    case atom of
    | metta_m1$Expr [metta_m1$Sym 32; a; b] =>
        bridge_eval_or_values
          (bridge_eval_args2
            (eval_m1_rec fuel space a)
            (eval_m1_rec fuel space b))
          atom
    | _ => [atom]
End

Theorem bridge_eval_or_fragment_agrees_with_eval_m1_rec:
  ∀fuel space a b.
    bridge_eval_or_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 32; a; b]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 32; a; b])
Proof
  rw[bridge_eval_or_fragment_def, eval_m1_rec_def,
     bridge_eval_or_values_args2_matches_rec_or_values]
QED

Theorem bridge_eval_or_fragment_via_values_fragment:
  ∀fuel space a b.
    bridge_eval_or_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 32; a; b]) =
    bridge_eval_or_values_fragment
      (metta_m1$Expr [metta_m1$Sym 32; a; b])
      (eval_m1_rec fuel space a)
      (eval_m1_rec fuel space b)
Proof
  rw[bridge_eval_or_fragment_def, bridge_eval_or_values_fragment_def]
QED

Definition bridge_surface_eval_or_fragment_wrapper_def:
  bridge_surface_eval_or_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_or_fragment fuel space atom)
End

Theorem bridge_surface_eval_or_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space a b space atom_a atom_b.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom a = SOME atom_a ∧
    bridge_import_surface_atom b = SOME atom_b ⇒
    bridge_surface_eval_or_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"or"); a; b]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 32; atom_a; atom_b])
Proof
  rw[bridge_surface_eval_or_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_or_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_or_fragment_wrapper_positive_example:
  bridge_surface_eval_or_fragment_wrapper 1 []
    (BExpr [BSym (strlit"or"); BSym (strlit"True");
            BSym (strlit"False")]) =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_or_fragment_wrapper_negative_example:
  bridge_surface_eval_or_fragment_wrapper 1 []
    (BExpr [BSym (strlit"not-a-core-symbol"); BSym (strlit"True");
            BSym (strlit"False")]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_not_fragment_def:
  bridge_eval_not_fragment fuel space atom =
    case atom of
    | metta_m1$Expr [metta_m1$Sym 33; a] =>
        bridge_eval_not_values (eval_m1_rec fuel space a) atom
    | _ => [atom]
End

Theorem bridge_eval_not_fragment_agrees_with_eval_m1_rec:
  ∀fuel space a.
    bridge_eval_not_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 33; a]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 33; a])
Proof
  rw[bridge_eval_not_fragment_def, eval_m1_rec_def,
     bridge_eval_not_values_matches_rec_not_values]
QED

Theorem bridge_eval_not_fragment_via_values_fragment:
  ∀fuel space a.
    bridge_eval_not_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 33; a]) =
    bridge_eval_not_values_fragment
      (metta_m1$Expr [metta_m1$Sym 33; a])
      (eval_m1_rec fuel space a)
Proof
  rw[bridge_eval_not_fragment_def, bridge_eval_not_values_fragment_def]
QED

Definition bridge_surface_eval_not_fragment_wrapper_def:
  bridge_surface_eval_not_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_not_fragment fuel space atom)
End

Theorem bridge_surface_eval_not_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space a space atom_a.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom a = SOME atom_a ⇒
    bridge_surface_eval_not_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"not"); a]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 33; atom_a])
Proof
  rw[bridge_surface_eval_not_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_not_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_not_fragment_wrapper_positive_example:
  bridge_surface_eval_not_fragment_wrapper 1 []
    (BExpr [BSym (strlit"not"); BSym (strlit"False")]) =
  [metta_m1$Sym 8]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_not_fragment_wrapper_negative_example:
  bridge_surface_eval_not_fragment_wrapper 1 []
    (BExpr [BSym (strlit"not-a-core-symbol"); BSym (strlit"False")]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_eval_fragment_def:
  bridge_eval_eval_fragment fuel space atom =
    eval_eval_fragment fuel space atom
End

Theorem bridge_eval_eval_fragment_agrees_with_eval_m1_rec:
  ∀fuel space body.
    bridge_eval_eval_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 20; body]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 20; body])
Proof
  rw[bridge_eval_eval_fragment_def,
     eval_eval_fragment_agrees_with_eval_m1_rec]
QED

Definition bridge_surface_eval_eval_fragment_wrapper_def:
  bridge_surface_eval_eval_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_eval_fragment fuel space atom)
End

Theorem bridge_surface_eval_eval_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space body space body_atom.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom body = SOME body_atom ⇒
    bridge_surface_eval_eval_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"eval"); body]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 20; body_atom])
Proof
  rw[bridge_surface_eval_eval_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_eval_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_eval_fragment_wrapper_positive_example:
  bridge_surface_eval_eval_fragment_wrapper 2 []
    (BExpr [BSym (strlit"eval");
            BExpr [BSym (strlit"+"); BInt 2; BInt 3]]) =
  [metta_m1$IntLit 5]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_eval_fragment_wrapper_negative_example:
  bridge_surface_eval_eval_fragment_wrapper 1 []
    (BExpr [BSym (strlit"not-a-core-symbol"); BInt 2]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_case_fragment_def:
  bridge_eval_case_fragment fuel space atom =
    eval_case_fragment fuel space atom
End

Theorem bridge_eval_case_fragment_agrees_with_eval_m1_rec:
  ∀fuel space scrut branches.
    bridge_eval_case_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 54; scrut; metta_m1$Expr branches]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 54; scrut; metta_m1$Expr branches])
Proof
  rw[bridge_eval_case_fragment_def,
     eval_case_fragment_agrees_with_eval_m1_rec]
QED

Definition bridge_surface_eval_case_fragment_wrapper_def:
  bridge_surface_eval_case_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_case_fragment fuel space atom)
End

Theorem bridge_surface_eval_case_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space scrut branches space scrut_atom branch_atoms.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom scrut = SOME scrut_atom ∧
    bridge_import_surface_atom_list branches = SOME branch_atoms ⇒
    bridge_surface_eval_case_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"case"); scrut; BExpr branches]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 54; scrut_atom; metta_m1$Expr branch_atoms])
Proof
  rw[bridge_surface_eval_case_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_case_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_case_fragment_wrapper_positive_example:
  bridge_surface_eval_case_fragment_wrapper 1 []
    (BExpr
      [BSym (strlit"case"); BSym (strlit"True");
       BExpr
        [BExpr [BSym (strlit"True"); BInt 1];
         BExpr [BVar 0; BInt 2]]]) =
  [metta_m1$IntLit 1]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_case_fragment_wrapper_negative_example:
  bridge_surface_eval_case_fragment_wrapper 1 []
    (BExpr
      [BSym (strlit"not-a-core-symbol"); BSym (strlit"True");
       BExpr [BExpr [BSym (strlit"True"); BInt 1]]]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_switch_fragment_def:
  bridge_eval_switch_fragment fuel space atom =
    case atom of
    | metta_m1$Expr [metta_m1$Sym 55; scrut; metta_m1$Expr branches] =>
        eval_switch_values_with
          (λa. eval_m1_rec fuel space a)
          (eval_m1_rec fuel space scrut) branches
    | _ => [atom]
End

Theorem bridge_eval_switch_fragment_agrees_with_eval_m1_rec:
  ∀fuel space scrut branches.
    bridge_eval_switch_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 55; scrut; metta_m1$Expr branches]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 55; scrut; metta_m1$Expr branches])
Proof
  rw[bridge_eval_switch_fragment_def, eval_m1_rec_def]
QED

Definition bridge_surface_eval_switch_fragment_wrapper_def:
  bridge_surface_eval_switch_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_switch_fragment fuel space atom)
End

Theorem bridge_surface_eval_switch_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space scrut branches space scrut_atom branch_atoms.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom scrut = SOME scrut_atom ∧
    bridge_import_surface_atom_list branches = SOME branch_atoms ⇒
    bridge_surface_eval_switch_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"switch"); scrut; BExpr branches]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 55; scrut_atom; metta_m1$Expr branch_atoms])
Proof
  rw[bridge_surface_eval_switch_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_switch_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_switch_fragment_wrapper_positive_example:
  bridge_surface_eval_switch_fragment_wrapper 1 []
    (BExpr
      [BSym (strlit"switch"); BSym (strlit"True");
       BExpr
        [BExpr [BSym (strlit"True"); BInt 1];
         BExpr [BVar 0; BInt 2]]]) =
  [metta_m1$IntLit 1]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_switch_fragment_wrapper_negative_example:
  bridge_surface_eval_switch_fragment_wrapper 1 []
    (BExpr
      [BSym (strlit"not-a-core-symbol"); BSym (strlit"True");
       BExpr [BExpr [BSym (strlit"True"); BInt 1]]]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_eval_let_star_fragment_def:
  bridge_eval_let_star_fragment fuel space atom =
    case atom of
    | metta_m1$Expr [metta_m1$Sym 56; metta_m1$Expr bindings; body] =>
        eval_let_star_with (SUC (LENGTH bindings))
          (λa. eval_m1_rec fuel space a) bindings body atom
    | _ => [atom]
End

Theorem bridge_eval_let_star_fragment_agrees_with_eval_m1_rec:
  ∀fuel space bindings body.
    bridge_eval_let_star_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 56; metta_m1$Expr bindings; body]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 56; metta_m1$Expr bindings; body])
Proof
  rw[bridge_eval_let_star_fragment_def, eval_m1_rec_def]
QED

Definition bridge_surface_eval_let_star_fragment_wrapper_def:
  bridge_surface_eval_let_star_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_let_star_fragment fuel space atom)
End

Theorem bridge_surface_eval_let_star_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space bindings body space binding_atoms body_atom.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom_list bindings = SOME binding_atoms ∧
    bridge_import_surface_atom body = SOME body_atom ⇒
    bridge_surface_eval_let_star_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"let*"); BExpr bindings; body]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr binding_atoms; body_atom])
Proof
  rw[bridge_surface_eval_let_star_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_let_star_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_let_star_fragment_wrapper_positive_example:
  bridge_surface_eval_let_star_fragment_wrapper 2 []
    (BExpr
      [BSym (strlit"let*");
       BExpr [BExpr [BVar 0; BInt 2]];
       BExpr [BSym (strlit"+"); BVar 0; BInt 3]]) =
  [metta_m1$IntLit 5]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_let_star_fragment_wrapper_negative_example:
  bridge_surface_eval_let_star_fragment_wrapper 1 []
    (BExpr
      [BSym (strlit"not-a-core-symbol");
       BExpr [BExpr [BVar 0; BInt 2]];
       BVar 0]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_lookup_bind_def:
  bridge_lookup_bind v [] = NONE ∧
  bridge_lookup_bind v (metta_m1$Bind w a :: rest) =
    if v = w then SOME a else bridge_lookup_bind v rest
End

Theorem bridge_lookup_bind_matches_lookup_bind:
  ∀v bs.
    bridge_lookup_bind v bs = lookup_bind v bs
Proof
  Induct_on ‘bs’ \\ rw[bridge_lookup_bind_def, lookup_bind_def] \\
  Cases_on ‘h’ \\ rw[bridge_lookup_bind_def, lookup_bind_def]
QED

Definition bridge_apply_subst_def:
  bridge_apply_subst bs (metta_m1$Sym n) = metta_m1$Sym n ∧
  bridge_apply_subst bs (metta_m1$Var v) =
    (case bridge_lookup_bind v bs of
     | NONE => metta_m1$Var v
     | SOME a => a) ∧
  bridge_apply_subst bs (metta_m1$IntLit i) = metta_m1$IntLit i ∧
  bridge_apply_subst bs (metta_m1$StrLit s) = metta_m1$StrLit s ∧
  bridge_apply_subst bs (metta_m1$Expr xs) =
    metta_m1$Expr (bridge_apply_subst_list bs xs) ∧
  bridge_apply_subst_list bs [] = [] ∧
  bridge_apply_subst_list bs (x :: xs) =
    bridge_apply_subst bs x :: bridge_apply_subst_list bs xs
End

Theorem bridge_apply_subst_map_eta:
  ∀bs atoms.
    MAP (apply_subst bs) atoms =
    MAP (λatom. apply_subst bs atom) atoms
Proof
  Induct_on ‘atoms’ \\ rw[]
QED

Theorem bridge_apply_subst_matches_apply_subst:
  (∀atom bs.
     bridge_apply_subst bs atom = apply_subst bs atom) ∧
  (∀atoms bs.
     bridge_apply_subst_list bs atoms = MAP (apply_subst bs) atoms)
Proof
  irule (CONV_RULE (DEPTH_CONV BETA_CONV) (Q.SPECL
    [‘λatom.
        ∀bs. bridge_apply_subst bs atom = apply_subst bs atom’,
     ‘λatoms.
        ∀bs. bridge_apply_subst_list bs atoms =
             MAP (apply_subst bs) atoms’]
    (fetch "metta_m1" "atom_induction"))) \\
  rw[bridge_apply_subst_def, apply_subst_def,
     bridge_lookup_bind_matches_lookup_bind,
     bridge_apply_subst_map_eta]
QED

Theorem bridge_apply_subst_atom_matches_apply_subst:
  ∀bs atom.
    bridge_apply_subst bs atom = apply_subst bs atom
Proof
  metis_tac[bridge_apply_subst_matches_apply_subst]
QED

Definition bridge_bind_var_def:
  bridge_bind_var v a bs =
    case bridge_lookup_bind v bs of
    | NONE => SOME (metta_m1$Bind v a :: bs)
    | SOME old => if old = a then SOME bs else NONE
End

Theorem bridge_bind_var_matches_bind_var:
  ∀v a bs.
    bridge_bind_var v a bs = bind_var v a bs
Proof
  rw[bridge_bind_var_def, bind_var_def,
     bridge_lookup_bind_matches_lookup_bind]
QED

Definition bridge_match_atom_def:
  bridge_match_atom (metta_m1$Var v) a bs = bridge_bind_var v a bs ∧
  bridge_match_atom (metta_m1$Sym x) (metta_m1$Sym y) bs =
    (if x = y then SOME bs else NONE) ∧
  bridge_match_atom (metta_m1$IntLit x) (metta_m1$IntLit y) bs =
    (if x = y then SOME bs else NONE) ∧
  bridge_match_atom (metta_m1$StrLit x) (metta_m1$StrLit y) bs =
    (if x = y then SOME bs else NONE) ∧
  bridge_match_atom (metta_m1$Expr ps) (metta_m1$Expr qs) bs =
    bridge_match_list ps qs bs ∧
  bridge_match_atom _ _ bs = NONE ∧
  bridge_match_list [] [] bs = SOME bs ∧
  bridge_match_list (p :: ps) (q :: qs) bs =
    (case bridge_match_atom p q bs of
     | SOME bs2 => bridge_match_list ps qs bs2
     | NONE => NONE) ∧
  bridge_match_list _ _ bs = NONE
Termination
  WF_REL_TAC
    ‘measure (λx.
       case x of
       | INL (p,q,bs) => atom_depth p + atom_depth q
       | INR (ps,qs,bs) => atom_list_depth ps + atom_list_depth qs)’ \\
  rw[atom_depth_def] \\ DECIDE_TAC
End

Theorem bridge_match_atom_matches_match_atom:
  (∀p q bs.
     bridge_match_atom p q bs = match_atom p q bs) ∧
  (∀ps qs bs.
     bridge_match_list ps qs bs = match_list ps qs bs)
Proof
  ho_match_mp_tac bridge_match_atom_ind \\
  rw[bridge_match_atom_def, match_atom_def,
     bridge_bind_var_matches_bind_var] \\
  every_case_tac \\ fs[]
QED

Theorem bridge_match_atom_positive_example:
  bridge_match_atom
    (metta_m1$Expr [metta_m1$Sym 100; metta_m1$Var 0])
    (metta_m1$Expr [metta_m1$Sym 100; metta_m1$Sym 8])
    [] =
  SOME [metta_m1$Bind 0 (metta_m1$Sym 8)]
Proof
  EVAL_TAC
QED

Theorem bridge_match_atom_negative_example:
  bridge_match_atom
    (metta_m1$Expr [metta_m1$Sym 100; metta_m1$Var 0; metta_m1$Var 0])
    (metta_m1$Expr [metta_m1$Sym 100; metta_m1$Sym 8; metta_m1$Sym 9])
    [] =
  NONE
Proof
  EVAL_TAC
QED

Definition bridge_match_space_payload_def:
  bridge_match_space_payload [] pattern templ = [] ∧
  bridge_match_space_payload (entry :: rest) pattern templ =
    case bridge_match_atom pattern entry [] of
    | SOME bs =>
        bridge_apply_subst bs templ ::
          bridge_match_space_payload rest pattern templ
    | NONE => bridge_match_space_payload rest pattern templ
End

Theorem bridge_match_space_payload_matches_match_space:
  ∀space pattern templ.
    bridge_match_space_payload space pattern templ =
    match_space space pattern templ
Proof
  Induct_on ‘space’ \\
  rw[bridge_match_space_payload_def, match_space_def,
     bridge_match_atom_matches_match_atom] \\
  Cases_on ‘match_atom pattern h []’ \\
  rw[bridge_apply_subst_atom_matches_apply_subst]
QED

Definition bridge_eval_match_fragment_def:
  bridge_eval_match_fragment space atom =
    case atom of
    | metta_m1$Expr
        [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ] =>
        bridge_match_space_payload space pattern templ
    | _ => [atom]
End

Theorem bridge_eval_match_fragment_agrees_with_eval_m1_ext:
  ∀fuel space pattern templ.
    bridge_eval_match_fragment space
      (metta_m1$Expr
        [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) =
    eval_m1_ext (SUC fuel) space
      (metta_m1$Expr
        [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ])
Proof
  rw[bridge_eval_match_fragment_def, eval_m1_ext_def,
     bridge_match_space_payload_matches_match_space]
QED

Theorem bridge_eval_match_fragment_agrees_with_eval_m1_rec:
  ∀fuel space pattern templ.
    bridge_eval_match_fragment space
      (metta_m1$Expr
        [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr
        [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ])
Proof
  rw[bridge_eval_match_fragment_def, eval_m1_rec_def, eval_m1_ext_def,
     bridge_match_space_payload_matches_match_space]
QED

Theorem bridge_eval_match_fragment_positive_example:
  bridge_eval_match_fragment
    [metta_m1$Expr [metta_m1$Sym 100; metta_m1$Sym 8];
     metta_m1$Expr [metta_m1$Sym 100; metta_m1$Sym 9]]
    (metta_m1$Expr
      [metta_m1$Sym 4; metta_m1$Sym 5;
       metta_m1$Expr [metta_m1$Sym 100; metta_m1$Var 0];
       metta_m1$Expr [metta_m1$Sym 101; metta_m1$Var 0]]) =
  [metta_m1$Expr [metta_m1$Sym 101; metta_m1$Sym 8];
   metta_m1$Expr [metta_m1$Sym 101; metta_m1$Sym 9]]
Proof
  EVAL_TAC
QED

Theorem bridge_eval_match_fragment_negative_example:
  bridge_eval_match_fragment
    [metta_m1$Expr [metta_m1$Sym 100; metta_m1$Sym 8]]
    (metta_m1$Expr
      [metta_m1$Sym 4; metta_m1$Sym 5;
       metta_m1$Expr [metta_m1$Sym 200; metta_m1$Var 0];
       metta_m1$Var 0]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_surface_eval_match_fragment_rel_def:
  bridge_surface_eval_match_fragment_rel surface_space surface_atom numeric_outs ⇔
    ∃space atom.
      bridge_import_surface_atom_list surface_space = SOME space ∧
      bridge_import_surface_atom surface_atom = SOME atom ∧
      numeric_outs = bridge_eval_match_fragment space atom
End

Theorem bridge_surface_eval_match_fragment_rel_sound:
  ∀surface_space surface_atom numeric_outs.
    bridge_surface_eval_match_fragment_rel surface_space surface_atom numeric_outs ⇒
    ∃space atom.
      bridge_import_surface_atom_list surface_space = SOME space ∧
      bridge_import_surface_atom surface_atom = SOME atom ∧
      numeric_outs = bridge_eval_match_fragment space atom
Proof
  rw[bridge_surface_eval_match_fragment_rel_def]
QED

Theorem bridge_surface_eval_match_fragment_rel_agrees_with_eval_m1_rec:
  ∀fuel surface_space pattern templ space pattern_atom templ_atom numeric_outs.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom pattern = SOME pattern_atom ∧
    bridge_import_surface_atom templ = SOME templ_atom ∧
    bridge_surface_eval_match_fragment_rel surface_space
      (BExpr [BSym (strlit"match"); BSym (strlit"&self");
              pattern; templ])
      numeric_outs ⇒
    numeric_outs =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern_atom; templ_atom])
Proof
  rw[bridge_surface_eval_match_fragment_rel_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_match_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_match_fragment_rel_positive_example:
  bridge_surface_eval_match_fragment_rel
    [BExpr [BSym (strlit"Person"); BSym (strlit"True")];
     BExpr [BSym (strlit"Person"); BSym (strlit"False")]]
    (BExpr
      [BSym (strlit"match"); BSym (strlit"&self");
       BExpr [BSym (strlit"Person"); BVar 0];
       BExpr [BSym (strlit"return"); BVar 0]])
    [metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 8];
     metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 9]]
Proof
  rw[bridge_surface_eval_match_fragment_rel_def] \\
  qexists_tac
    ‘[metta_m1$Expr [metta_m1$Sym 50; metta_m1$Sym 8];
       metta_m1$Expr [metta_m1$Sym 50; metta_m1$Sym 9]]’ \\
  qexists_tac
    ‘metta_m1$Expr
      [metta_m1$Sym 4; metta_m1$Sym 5;
       metta_m1$Expr [metta_m1$Sym 50; metta_m1$Var 0];
       metta_m1$Expr [metta_m1$Sym 19; metta_m1$Var 0]]’ \\
  EVAL_TAC
QED

Theorem bridge_surface_eval_match_fragment_rel_negative_example:
  ¬bridge_surface_eval_match_fragment_rel
    [BExpr [BSym (strlit"Person"); BSym (strlit"True")]]
    (BExpr
      [BSym (strlit"match"); BSym (strlit"&self");
       BExpr [BSym (strlit"not-a-core-symbol"); BVar 0];
       BVar 0])
    []
Proof
  EVAL_TAC \\
  rw[]
QED

Definition bridge_surface_eval_match_fragment_wrapper_def:
  bridge_surface_eval_match_fragment_wrapper surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_match_fragment space atom)
End

Theorem bridge_surface_eval_match_fragment_wrapper_rel:
  ∀surface_space surface_atom numeric_outs.
    bridge_surface_eval_match_fragment_rel
      surface_space surface_atom numeric_outs ⇒
    bridge_surface_eval_match_fragment_wrapper surface_space surface_atom =
      numeric_outs
Proof
  rw[bridge_surface_eval_match_fragment_rel_def,
     bridge_surface_eval_match_fragment_wrapper_def] \\
  gvs[]
QED

Theorem bridge_surface_eval_match_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space pattern templ space pattern_atom templ_atom.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom pattern = SOME pattern_atom ∧
    bridge_import_surface_atom templ = SOME templ_atom ⇒
    bridge_surface_eval_match_fragment_wrapper surface_space
      (BExpr [BSym (strlit"match"); BSym (strlit"&self");
              pattern; templ]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern_atom; templ_atom])
Proof
  rw[bridge_surface_eval_match_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_match_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_match_fragment_wrapper_positive_example:
  bridge_surface_eval_match_fragment_wrapper
    [BExpr [BSym (strlit"Person"); BSym (strlit"True")];
     BExpr [BSym (strlit"Person"); BSym (strlit"False")]]
    (BExpr
      [BSym (strlit"match"); BSym (strlit"&self");
       BExpr [BSym (strlit"Person"); BVar 0];
       BExpr [BSym (strlit"return"); BVar 0]]) =
    [metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 8];
     metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 9]]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_match_fragment_wrapper_negative_example:
  bridge_surface_eval_match_fragment_wrapper
    [BExpr [BSym (strlit"Person"); BSym (strlit"True")]]
    (BExpr
      [BSym (strlit"match"); BSym (strlit"&self");
       BExpr [BSym (strlit"not-a-core-symbol"); BVar 0];
       BVar 0]) =
    []
Proof
  EVAL_TAC
QED

Definition bridge_surface_eval_match_fragment_rel_with_env_def:
  bridge_surface_eval_match_fragment_rel_with_env
    env surface_space surface_atom numeric_outs ⇔
    ∃space atom.
      bridge_import_surface_atom_list_with_env env surface_space =
        SOME space ∧
      bridge_import_surface_atom_with_env env surface_atom = SOME atom ∧
      numeric_outs = bridge_eval_match_fragment space atom
End

Theorem bridge_surface_eval_match_fragment_rel_with_env_sound:
  ∀env surface_space surface_atom numeric_outs.
    bridge_surface_eval_match_fragment_rel_with_env
      env surface_space surface_atom numeric_outs ⇒
    ∃space atom.
      bridge_import_surface_atom_list_with_env env surface_space =
        SOME space ∧
      bridge_import_surface_atom_with_env env surface_atom = SOME atom ∧
      numeric_outs = bridge_eval_match_fragment space atom
Proof
  rw[bridge_surface_eval_match_fragment_rel_with_env_def]
QED

Theorem bridge_surface_eval_match_fragment_rel_with_env_agrees_with_eval_m1_rec:
  ∀fuel env surface_space pattern templ space pattern_atom templ_atom
     numeric_outs.
    bridge_import_surface_atom_list_with_env env surface_space =
      SOME space ∧
    bridge_import_surface_atom_with_env env pattern = SOME pattern_atom ∧
    bridge_import_surface_atom_with_env env templ = SOME templ_atom ∧
    bridge_surface_eval_match_fragment_rel_with_env env surface_space
      (BExpr [BSym (strlit"match"); BSym (strlit"&self");
              pattern; templ])
      numeric_outs ⇒
    numeric_outs =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern_atom; templ_atom])
Proof
  rw[bridge_surface_eval_match_fragment_rel_with_env_def,
     bridge_import_surface_atom_with_env_def,
     bridge_import_symbol_with_env_def,
     bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_match_fragment_agrees_with_eval_m1_rec]
QED

Definition bridge_surface_eval_match_fragment_wrapper_with_env_def:
  bridge_surface_eval_match_fragment_wrapper_with_env
    env surface_space surface_atom =
    case bridge_import_surface_atom_list_with_env env surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom_with_env env surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_match_fragment space atom)
End

Theorem bridge_surface_eval_match_fragment_wrapper_with_env_rel:
  ∀env surface_space surface_atom numeric_outs.
    bridge_surface_eval_match_fragment_rel_with_env
      env surface_space surface_atom numeric_outs ⇒
    bridge_surface_eval_match_fragment_wrapper_with_env
      env surface_space surface_atom =
      numeric_outs
Proof
  rw[bridge_surface_eval_match_fragment_rel_with_env_def,
     bridge_surface_eval_match_fragment_wrapper_with_env_def] \\
  gvs[]
QED

Theorem bridge_surface_eval_match_fragment_wrapper_with_env_agrees_with_eval_m1_rec:
  ∀fuel env surface_space pattern templ space pattern_atom templ_atom.
    bridge_import_surface_atom_list_with_env env surface_space =
      SOME space ∧
    bridge_import_surface_atom_with_env env pattern = SOME pattern_atom ∧
    bridge_import_surface_atom_with_env env templ = SOME templ_atom ⇒
    bridge_surface_eval_match_fragment_wrapper_with_env env surface_space
      (BExpr [BSym (strlit"match"); BSym (strlit"&self");
              pattern; templ]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern_atom; templ_atom])
Proof
  rw[bridge_surface_eval_match_fragment_wrapper_with_env_def,
     bridge_import_surface_atom_with_env_def,
     bridge_import_symbol_with_env_def,
     bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_match_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_match_fragment_wrapper_with_env_dynamic_example:
  bridge_surface_eval_match_fragment_wrapper_with_env [(strlit"Foo", 1000)]
    [BExpr [BSym (strlit"Foo"); BSym (strlit"True")];
     BExpr [BSym (strlit"Foo"); BSym (strlit"False")]]
    (BExpr
      [BSym (strlit"match"); BSym (strlit"&self");
       BExpr [BSym (strlit"Foo"); BVar 0];
       BExpr [BSym (strlit"return"); BVar 0]]) =
    [metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 8];
     metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 9]]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_match_fragment_wrapper_with_env_negative_example:
  bridge_surface_eval_match_fragment_wrapper_with_env []
    [BExpr [BSym (strlit"Foo"); BSym (strlit"True")]]
    (BExpr
      [BSym (strlit"match"); BSym (strlit"&self");
       BExpr [BSym (strlit"Foo"); BVar 0];
       BVar 0]) =
    []
Proof
  EVAL_TAC
QED

Definition bridge_eval_match_fragment_artifact_manifest_def:
  bridge_eval_match_fragment_artifact_manifest ⇔
    strlit"bridge_eval_match_fragment" = strlit"bridge_eval_match_fragment" ∧
    strlit"bridge_eval_match_fragment_v_certificate" =
      strlit"bridge_eval_match_fragment_v_certificate" ∧
    strlit"bridge_eval_match_fragment_v_app_spec_certificate" =
      strlit"bridge_eval_match_fragment_v_app_spec_certificate" ∧
    strlit"generated/bridge_eval_match_fragment.sexp" =
      strlit"generated/bridge_eval_match_fragment.sexp"
End

Theorem bridge_eval_match_fragment_artifact_manifest_checked:
  bridge_eval_match_fragment_artifact_manifest
Proof
  EVAL_TAC
QED

Theorem bridge_eval_match_fragment_artifact_manifest_points_to_match_branch:
  bridge_eval_match_fragment_artifact_manifest ⇒
  ∀fuel space pattern templ.
    bridge_eval_match_fragment space
      (metta_m1$Expr
        [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr
        [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ])
Proof
  rw[bridge_eval_match_fragment_artifact_manifest_checked,
     bridge_eval_match_fragment_agrees_with_eval_m1_rec]
QED

Definition bridge_chain_concat_results_def:
  bridge_chain_concat_results [] = [] ∧
  bridge_chain_concat_results (xs :: xss) =
    xs ++ bridge_chain_concat_results xss
End

Definition bridge_chain_subst_values_def:
  bridge_chain_subst_values v [] templ = [] ∧
  bridge_chain_subst_values v (x :: xs) templ =
    bridge_apply_subst [metta_m1$Bind v x] templ ::
      bridge_chain_subst_values v xs templ
End

Theorem bridge_chain_subst_values_member:
  ∀v vals templ substituted.
    MEM substituted (bridge_chain_subst_values v vals templ) ⇔
    ∃x.
      MEM x vals ∧
      substituted = bridge_apply_subst [metta_m1$Bind v x] templ
Proof
  Induct_on ‘vals’ \\ rw[bridge_chain_subst_values_def] \\
  metis_tac[]
QED

Theorem bridge_chain_subst_values_nonempty:
  ∀v vals templ.
    vals ≠ [] ⇒ bridge_chain_subst_values v vals templ ≠ []
Proof
  Cases_on ‘vals’ \\ rw[bridge_chain_subst_values_def]
QED

Theorem bridge_chain_concat_results_append:
  ∀xss yss.
    bridge_chain_concat_results (xss ++ yss) =
    bridge_chain_concat_results xss ++ bridge_chain_concat_results yss
Proof
  Induct \\ rw[bridge_chain_concat_results_def]
QED

Definition bridge_first_branch_payloads_def:
  bridge_first_branch_payloads value [] = [] ∧
  bridge_first_branch_payloads value (branch :: rest) =
    (case branch_pair branch of
     | SOME (pattern, body) =>
         (case bridge_match_atom pattern value [] of
          | SOME bs => [bridge_apply_subst bs body]
          | NONE => bridge_first_branch_payloads value rest)
     | NONE => bridge_first_branch_payloads value rest)
End

Definition bridge_branch_values_payloads_def:
  bridge_branch_values_payloads [] branches = [] ∧
  bridge_branch_values_payloads (value :: rest) branches =
    bridge_first_branch_payloads value branches ++
    bridge_branch_values_payloads rest branches
End

Theorem bridge_first_branch_payloads_switch_decompose:
  ∀ev value branches.
    eval_switch_one_with ev value branches =
    bridge_chain_concat_results
      (MAP ev (bridge_first_branch_payloads value branches))
Proof
  Induct_on ‘branches’ \\
  rw[eval_switch_one_with_def, bridge_first_branch_payloads_def,
     bridge_chain_concat_results_def] \\
  Cases_on ‘branch_pair h’ \\
  rw[eval_switch_one_with_def, bridge_first_branch_payloads_def,
     bridge_chain_concat_results_def] \\
  PairCases_on ‘x’ \\
  rw[] \\
  Cases_on ‘match_atom x0 value []’ \\
  rw[bridge_match_atom_matches_match_atom,
     bridge_apply_subst_atom_matches_apply_subst,
     bridge_chain_concat_results_def]
QED

Theorem bridge_first_branch_payloads_case_decompose:
  ∀ev value branches.
    eval_case_one_with ev value branches =
    bridge_chain_concat_results
      (MAP ev (bridge_first_branch_payloads value branches))
Proof
  Induct_on ‘branches’ \\
  rw[eval_case_one_with_def, bridge_first_branch_payloads_def,
     bridge_chain_concat_results_def] \\
  Cases_on ‘branch_pair h’ \\
  rw[eval_case_one_with_def, bridge_first_branch_payloads_def,
     bridge_chain_concat_results_def] \\
  PairCases_on ‘x’ \\
  rw[] \\
  Cases_on ‘match_atom x0 value []’ \\
  rw[bridge_match_atom_matches_match_atom,
     bridge_apply_subst_atom_matches_apply_subst,
     bridge_chain_concat_results_def]
QED

Theorem bridge_branch_values_payloads_case_decompose:
  ∀ev vals branches.
    eval_case_values_with ev vals branches =
    bridge_chain_concat_results
      (MAP ev (bridge_branch_values_payloads vals branches))
Proof
  Induct_on ‘vals’ \\
  rw[eval_case_values_with_def, bridge_branch_values_payloads_def,
     bridge_chain_concat_results_def, MAP_APPEND,
     bridge_chain_concat_results_append,
     bridge_first_branch_payloads_case_decompose]
QED

Theorem bridge_branch_values_payloads_switch_decompose:
  ∀ev vals branches.
    eval_switch_values_with ev vals branches =
    bridge_chain_concat_results
      (MAP ev (bridge_branch_values_payloads vals branches))
Proof
  Induct_on ‘vals’ \\
  rw[eval_switch_values_with_def, bridge_branch_values_payloads_def,
     bridge_chain_concat_results_def, MAP_APPEND,
     bridge_chain_concat_results_append,
     bridge_first_branch_payloads_switch_decompose]
QED

Theorem bridge_eval_switch_fragment_decomposes:
  ∀fuel space scrut branches.
    bridge_eval_switch_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 55; scrut; metta_m1$Expr branches]) =
    bridge_chain_concat_results
      (MAP
        (λpayload. eval_m1_rec fuel space payload)
        (bridge_branch_values_payloads
          (eval_m1_rec fuel space scrut) branches))
Proof
  rw[bridge_eval_switch_fragment_def,
     bridge_branch_values_payloads_switch_decompose]
QED

Theorem bridge_eval_case_fragment_decomposes:
  ∀fuel space scrut branches.
    bridge_eval_case_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 54; scrut; metta_m1$Expr branches]) =
    bridge_chain_concat_results
      (MAP
        (λpayload. eval_m1_rec fuel space payload)
        (bridge_branch_values_payloads
          (eval_m1_rec fuel space scrut) branches))
Proof
  rw[bridge_eval_case_fragment_def, eval_case_fragment_def,
     bridge_branch_values_payloads_case_decompose]
QED

Theorem bridge_first_branch_payloads_positive_example:
  bridge_first_branch_payloads (metta_m1$Sym 8)
    [metta_m1$Expr [metta_m1$Sym 8; metta_m1$IntLit 1];
     metta_m1$Expr [metta_m1$Var 0; metta_m1$IntLit 2]] =
  [metta_m1$IntLit 1]
Proof
  EVAL_TAC
QED

Theorem bridge_first_branch_payloads_negative_example:
  bridge_first_branch_payloads (metta_m1$Sym 9)
    [metta_m1$Expr [metta_m1$Sym 8; metta_m1$IntLit 1];
     metta_m1$Sym 100] =
  []
Proof
  EVAL_TAC
QED

Definition bridge_surface_switch_payloads_wrapper_def:
  bridge_surface_switch_payloads_wrapper surface_scrut surface_branches =
    case bridge_import_surface_atom surface_scrut of
    | NONE => []
    | SOME scrut =>
        (case bridge_import_surface_atom_list surface_branches of
         | NONE => []
         | SOME branches => bridge_first_branch_payloads scrut branches)
End

Definition bridge_surface_case_payloads_wrapper_def:
  bridge_surface_case_payloads_wrapper surface_values surface_branches =
    case bridge_import_surface_atom_list surface_values of
    | NONE => []
    | SOME values =>
        (case bridge_import_surface_atom_list surface_branches of
         | NONE => []
         | SOME branches => bridge_branch_values_payloads values branches)
End

Definition bridge_surface_switch_payloads_wrapper_with_env_def:
  bridge_surface_switch_payloads_wrapper_with_env
    env surface_scrut surface_branches =
    case bridge_import_surface_atom_with_env env surface_scrut of
    | NONE => []
    | SOME scrut =>
        (case bridge_import_surface_atom_list_with_env env
                surface_branches of
         | NONE => []
         | SOME branches => bridge_first_branch_payloads scrut branches)
End

Definition bridge_surface_case_payloads_wrapper_with_env_def:
  bridge_surface_case_payloads_wrapper_with_env
    env surface_values surface_branches =
    case bridge_import_surface_atom_list_with_env env surface_values of
    | NONE => []
    | SOME values =>
        (case bridge_import_surface_atom_list_with_env env
                surface_branches of
         | NONE => []
         | SOME branches => bridge_branch_values_payloads values branches)
End

Theorem bridge_surface_switch_payloads_wrapper_import:
  ∀surface_scrut surface_branches scrut branches.
    bridge_import_surface_atom surface_scrut = SOME scrut ∧
    bridge_import_surface_atom_list surface_branches = SOME branches ⇒
    bridge_surface_switch_payloads_wrapper
      surface_scrut surface_branches =
    bridge_first_branch_payloads scrut branches
Proof
  rw[bridge_surface_switch_payloads_wrapper_def]
QED

Theorem bridge_surface_case_payloads_wrapper_import:
  ∀surface_values surface_branches values branches.
    bridge_import_surface_atom_list surface_values = SOME values ∧
    bridge_import_surface_atom_list surface_branches = SOME branches ⇒
    bridge_surface_case_payloads_wrapper
      surface_values surface_branches =
    bridge_branch_values_payloads values branches
Proof
  rw[bridge_surface_case_payloads_wrapper_def]
QED

Theorem bridge_surface_switch_payloads_wrapper_with_env_import:
  ∀env surface_scrut surface_branches scrut branches.
    bridge_import_surface_atom_with_env env surface_scrut = SOME scrut ∧
    bridge_import_surface_atom_list_with_env env surface_branches =
      SOME branches ⇒
    bridge_surface_switch_payloads_wrapper_with_env
      env surface_scrut surface_branches =
    bridge_first_branch_payloads scrut branches
Proof
  rw[bridge_surface_switch_payloads_wrapper_with_env_def]
QED

Theorem bridge_surface_case_payloads_wrapper_with_env_import:
  ∀env surface_values surface_branches values branches.
    bridge_import_surface_atom_list_with_env env surface_values =
      SOME values ∧
    bridge_import_surface_atom_list_with_env env surface_branches =
      SOME branches ⇒
    bridge_surface_case_payloads_wrapper_with_env
      env surface_values surface_branches =
    bridge_branch_values_payloads values branches
Proof
  rw[bridge_surface_case_payloads_wrapper_with_env_def]
QED

Theorem bridge_chain_concat_results_member:
  ∀xss out.
    MEM out (bridge_chain_concat_results xss) ⇔
    ∃xs. MEM xs xss ∧ MEM out xs
Proof
  Induct \\ rw[bridge_chain_concat_results_def] \\
  metis_tac[]
QED

Theorem bridge_eval_switch_fragment_payload_recursive_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 55; scrut;
                         metta_m1$Expr branches])) ⇒
    ∃payload.
      MEM payload
        (bridge_branch_values_payloads
          (eval_m1_rec fuel space scrut) branches) ∧
      MEM out (eval_m1_rec fuel space payload) ∧
      eval_m1_rec_result_sound fuel space payload out ∧
      eval_m1_rec_family_sound fuel space payload out
Proof
  rpt strip_tac \\
  ‘MEM out
     (bridge_eval_switch_fragment fuel space
       (metta_m1$Expr [metta_m1$Sym 55; scrut;
                        metta_m1$Expr branches]))’
    by metis_tac[bridge_eval_switch_fragment_agrees_with_eval_m1_rec] \\
  fs[bridge_eval_switch_fragment_decomposes,
     bridge_chain_concat_results_member, MEM_MAP] \\
  metis_tac[eval_m1_rec_result_sound, eval_m1_rec_family_result_sound]
QED

Theorem bridge_eval_case_fragment_payload_recursive_sound:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 54; scrut;
                         metta_m1$Expr branches])) ⇒
    ∃payload.
      MEM payload
        (bridge_branch_values_payloads
          (eval_m1_rec fuel space scrut) branches) ∧
      MEM out (eval_m1_rec fuel space payload) ∧
      eval_m1_rec_result_sound fuel space payload out ∧
      eval_m1_rec_family_sound fuel space payload out
Proof
  rpt strip_tac \\
  ‘MEM out
     (bridge_eval_case_fragment fuel space
       (metta_m1$Expr [metta_m1$Sym 54; scrut;
                        metta_m1$Expr branches]))’
    by metis_tac[bridge_eval_case_fragment_agrees_with_eval_m1_rec] \\
  fs[bridge_eval_case_fragment_decomposes,
     bridge_chain_concat_results_member, MEM_MAP] \\
  metis_tac[eval_m1_rec_result_sound, eval_m1_rec_family_result_sound]
QED

Definition bridge_eval_payload_result_def:
  bridge_eval_payload_result body rs =
    if rs = [body] then [metta_m1$Sym 23] else rs
End

Theorem bridge_eval_eval_fragment_decomposes:
  ∀fuel space body.
    bridge_eval_eval_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 20; body]) =
    bridge_eval_payload_result body (eval_m1_rec fuel space body)
Proof
  rw[bridge_eval_eval_fragment_def, eval_eval_fragment_def,
     bridge_eval_payload_result_def]
QED

Definition bridge_evalc_checked_values_def:
  bridge_evalc_checked_values space term expected vals =
    evalc_values space term expected vals
End

Theorem bridge_eval_evalc_fragment_decomposes:
  ∀fuel space term expected.
    eval_evalc_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 57; term; expected]) =
    bridge_evalc_checked_values space term expected
      (if hol_typed_add_bad space term
       then [error_atom term (metta_m1$Sym 10)]
       else eval_m1_rec fuel space term)
Proof
  rw[eval_evalc_fragment_def, typed_eval_m1_rec_def,
     bridge_evalc_checked_values_def]
QED

Definition bridge_surface_eval_payload_result_wrapper_def:
  bridge_surface_eval_payload_result_wrapper surface_body surface_rs =
    case bridge_import_surface_atom surface_body of
    | NONE => []
    | SOME body =>
        (case bridge_import_surface_atom_list surface_rs of
         | NONE => []
         | SOME rs => bridge_eval_payload_result body rs)
End

Definition bridge_surface_evalc_checked_values_wrapper_def:
  bridge_surface_evalc_checked_values_wrapper
    surface_space surface_term surface_expected surface_vals =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_term of
         | NONE => []
         | SOME term =>
             (case bridge_import_surface_atom surface_expected of
              | NONE => []
              | SOME expected =>
                  (case bridge_import_surface_atom_list surface_vals of
                   | NONE => []
                   | SOME vals =>
                       bridge_evalc_checked_values
                         space term expected vals)))
End

Theorem bridge_surface_eval_payload_result_wrapper_import:
  ∀surface_body surface_rs body rs.
    bridge_import_surface_atom surface_body = SOME body ∧
    bridge_import_surface_atom_list surface_rs = SOME rs ⇒
    bridge_surface_eval_payload_result_wrapper surface_body surface_rs =
    bridge_eval_payload_result body rs
Proof
  rw[bridge_surface_eval_payload_result_wrapper_def]
QED

Theorem bridge_surface_evalc_checked_values_wrapper_import:
  ∀surface_space surface_term surface_expected surface_vals
     space term expected vals.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom surface_term = SOME term ∧
    bridge_import_surface_atom surface_expected = SOME expected ∧
    bridge_import_surface_atom_list surface_vals = SOME vals ⇒
    bridge_surface_evalc_checked_values_wrapper
      surface_space surface_term surface_expected surface_vals =
    bridge_evalc_checked_values space term expected vals
Proof
  rw[bridge_surface_evalc_checked_values_wrapper_def]
QED

Theorem bridge_surface_eval_payload_result_wrapper_eval_fragment:
  ∀fuel space surface_body surface_rs body.
    bridge_import_surface_atom surface_body = SOME body ∧
    bridge_import_surface_atom_list surface_rs =
      SOME (eval_m1_rec fuel space body) ⇒
    bridge_surface_eval_payload_result_wrapper surface_body surface_rs =
    bridge_eval_eval_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 20; body])
Proof
  rw[bridge_surface_eval_payload_result_wrapper_import,
     bridge_eval_eval_fragment_decomposes]
QED

Theorem bridge_surface_evalc_checked_values_wrapper_evalc_fragment:
  ∀fuel surface_space surface_term surface_expected surface_vals
     space term expected.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom surface_term = SOME term ∧
    bridge_import_surface_atom surface_expected = SOME expected ∧
    bridge_import_surface_atom_list surface_vals =
      SOME
        (if hol_typed_add_bad space term
         then [error_atom term (metta_m1$Sym 10)]
         else eval_m1_rec fuel space term) ⇒
    bridge_surface_evalc_checked_values_wrapper
      surface_space surface_term surface_expected surface_vals =
    eval_evalc_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 57; term; expected])
Proof
  rw[bridge_surface_evalc_checked_values_wrapper_import,
     bridge_eval_evalc_fragment_decomposes]
QED

Theorem bridge_evalc_checked_values_member:
  ∀space term expected vals out.
    MEM out (bridge_evalc_checked_values space term expected vals) ⇒
    ∃value.
      MEM value vals ∧
      ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
       (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
        out = error_atom term (metta_m1$Sym 10)))
Proof
  rw[bridge_evalc_checked_values_def] \\
  metis_tac[evalc_values_member_sound]
QED

Theorem bridge_eval_evalc_fragment_payload_recursive_sound:
  ∀fuel space term expected out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 57; term; expected])) ⇒
    ∃value checked_values.
      checked_values =
        (if hol_typed_add_bad space term
         then [error_atom term (metta_m1$Sym 10)]
         else eval_m1_rec fuel space term) ∧
      MEM value checked_values ∧
      MEM out
        (bridge_evalc_checked_values space term expected checked_values) ∧
      (¬hol_typed_add_bad space term ⇒
       eval_m1_rec_result_sound fuel space term value ∧
       eval_m1_rec_family_sound fuel space term value) ∧
      ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
       (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
        out = error_atom term (metta_m1$Sym 10)))
Proof
  rpt strip_tac \\
  qabbrev_tac
    ‘checked_values =
       if hol_typed_add_bad space term
       then [error_atom term (metta_m1$Sym 10)]
       else eval_m1_rec fuel space term’ \\
  ‘MEM out
     (bridge_evalc_checked_values space term expected checked_values)’
    by (qunabbrev_tac ‘checked_values’ \\
        fs[GSYM bridge_eval_evalc_fragment_decomposes,
           eval_evalc_fragment_agrees_with_eval_m1_rec]) \\
  drule bridge_evalc_checked_values_member \\
  strip_tac \\
  qexists_tac ‘value’ \\
  qexists_tac ‘checked_values’ \\
  rw[] \\
  qunabbrev_tac ‘checked_values’ \\
  fs[] \\
  metis_tac[eval_m1_rec_result_sound, eval_m1_rec_family_result_sound]
QED

Theorem bridge_eval_m1_rec_fuller_evalc_payload_sound:
  ∀fuel space term expected out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 57; term; expected])) ⇒
    eval_m1_rec_result_sound (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 57; term; expected]) out ∧
    eval_m1_rec_nested_family_sound fuel space
      (metta_m1$Expr [metta_m1$Sym 57; term; expected]) out ∧
    eval_m1_rec_family_sound (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 57; term; expected]) out ∧
    ∃value checked_values.
      checked_values =
        (if hol_typed_add_bad space term
         then [error_atom term (metta_m1$Sym 10)]
         else eval_m1_rec fuel space term) ∧
      MEM value checked_values ∧
      MEM out
        (bridge_evalc_checked_values space term expected checked_values) ∧
      (¬hol_typed_add_bad space term ⇒
       eval_m1_rec_result_sound fuel space term value ∧
       eval_m1_rec_family_sound fuel space term value) ∧
      ((hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
       (¬hol_any_type_match expected
          (hol_declared_or_default_type_lookup space value) ∧
        out = error_atom term (metta_m1$Sym 10)))
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >- (
    irule eval_m1_rec_nested_family_result_sound \\
    rw[eval_m1_rec_nested_family_atom_def]) \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  metis_tac[bridge_eval_evalc_fragment_payload_recursive_sound]
QED

Definition bridge_subst_binding_pair_def:
  bridge_subst_binding_pair v value
    (metta_m1$Expr [metta_m1$Var w; rhs]) =
      metta_m1$Expr
        [metta_m1$Var w;
         bridge_apply_subst [metta_m1$Bind v value] rhs] ∧
  bridge_subst_binding_pair v value other = other
End

Definition bridge_subst_binding_pairs_def:
  bridge_subst_binding_pairs v value [] = [] ∧
  bridge_subst_binding_pairs v value (pair :: rest) =
    bridge_subst_binding_pair v value pair ::
    bridge_subst_binding_pairs v value rest
End

Theorem bridge_subst_binding_pair_matches_subst_binding_pair:
  ∀v value pair.
    bridge_subst_binding_pair v value pair =
    subst_binding_pair v value pair
Proof
  Cases_on ‘pair’ \\
  rw[bridge_subst_binding_pair_def, subst_binding_pair_def,
     bridge_apply_subst_atom_matches_apply_subst] \\
  Cases_on ‘l’ \\
  rw[bridge_subst_binding_pair_def, subst_binding_pair_def,
     bridge_apply_subst_atom_matches_apply_subst] \\
  Cases_on ‘t’ \\
  rw[bridge_subst_binding_pair_def, subst_binding_pair_def,
     bridge_apply_subst_atom_matches_apply_subst] \\
  Cases_on ‘h’ \\
  rw[bridge_subst_binding_pair_def, subst_binding_pair_def,
     bridge_apply_subst_atom_matches_apply_subst] \\
  rename1 ‘metta_m1$Expr (metta_m1$Var n :: rhs :: rest)’ \\
  Cases_on ‘rest’ \\
  rw[bridge_subst_binding_pair_def, subst_binding_pair_def,
     bridge_apply_subst_atom_matches_apply_subst]
QED

Theorem bridge_subst_binding_pairs_matches_subst_binding_pairs:
  ∀v value bindings.
    bridge_subst_binding_pairs v value bindings =
    subst_binding_pairs v value bindings
Proof
  Induct_on ‘bindings’ \\
  rw[bridge_subst_binding_pairs_def, subst_binding_pairs_def,
     bridge_subst_binding_pair_matches_subst_binding_pair]
QED

Definition bridge_let_star_step_payloads_def:
  bridge_let_star_step_payloads binding rest body evaluated_values =
    case let_binding_pair binding of
    | SOME (v, value) =>
        MAP
          (λevaluated.
             (bridge_subst_binding_pairs v evaluated rest,
              bridge_apply_subst [metta_m1$Bind v evaluated] body))
          evaluated_values
    | NONE => []
End

Theorem bridge_let_star_step_payloads_member:
  ∀binding rest body evaluated_values payload.
    MEM payload
      (bridge_let_star_step_payloads binding rest body evaluated_values) ⇔
    ∃v value evaluated.
      let_binding_pair binding = SOME (v, value) ∧
      MEM evaluated evaluated_values ∧
      payload =
        (bridge_subst_binding_pairs v evaluated rest,
         bridge_apply_subst [metta_m1$Bind v evaluated] body)
Proof
  rw[bridge_let_star_step_payloads_def] \\
  Cases_on ‘let_binding_pair binding’ \\
  rw[] \\
  PairCases_on ‘x’ \\
  rw[MEM_MAP, EQ_IMP_THM] \\
  metis_tac[]
QED

Theorem bridge_chain_concat_results_map:
  ∀f xs.
    bridge_chain_concat_results (MAP f xs) = FLAT (MAP f xs)
Proof
  Induct_on ‘xs’ \\ rw[bridge_chain_concat_results_def]
QED

Theorem bridge_let_star_step_payloads_results:
  ∀let_fuel ev v value rest body original vals.
    bridge_chain_concat_results
      (MAP
        (λpayload.
           eval_let_star_with let_fuel ev
             (FST payload) (SND payload) original)
        (MAP
          (λevaluated.
             (subst_binding_pairs v evaluated rest,
              apply_subst [metta_m1$Bind v evaluated] body))
          vals)) =
    FLAT
      (MAP
        (λevaluated.
           eval_let_star_with let_fuel ev
             (subst_binding_pairs v evaluated rest)
             (apply_subst [metta_m1$Bind v evaluated] body) original)
        vals)
Proof
  Induct_on ‘vals’ \\ rw[bridge_chain_concat_results_def]
QED

Theorem bridge_eval_let_star_with_step_decomposes:
  ∀let_fuel ev binding rest body original.
    eval_let_star_with (SUC let_fuel) ev (binding :: rest) body original =
    case let_binding_pair binding of
    | SOME (v, value) =>
        bridge_chain_concat_results
          (MAP
            (λpayload.
               eval_let_star_with let_fuel ev
                 (FST payload) (SND payload) original)
            (bridge_let_star_step_payloads binding rest body (ev value)))
    | NONE => [error_atom original (metta_m1$Sym 10)]
Proof
  rw[eval_let_star_with_def,
     bridge_let_star_step_payloads_def,
     GSYM bridge_let_star_step_payloads_results,
     bridge_subst_binding_pairs_matches_subst_binding_pairs,
     bridge_apply_subst_atom_matches_apply_subst] \\
  every_case_tac \\
  rw[]
QED

Theorem bridge_eval_let_star_fragment_step_decomposes:
  ∀fuel space binding rest body.
    bridge_eval_let_star_fragment fuel space
      (metta_m1$Expr
        [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) =
    case let_binding_pair binding of
    | SOME (v, value) =>
        bridge_chain_concat_results
          (MAP
            (λpayload.
               eval_let_star_with (SUC (LENGTH rest))
                 (λa. eval_m1_rec fuel space a)
                 (FST payload) (SND payload)
                 (metta_m1$Expr
                   [metta_m1$Sym 56;
                    metta_m1$Expr (binding :: rest); body]))
            (bridge_let_star_step_payloads binding rest body
              (eval_m1_rec fuel space value)))
    | NONE =>
        [error_atom
          (metta_m1$Expr
            [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body])
          (metta_m1$Sym 10)]
Proof
  rw[bridge_eval_let_star_fragment_def,
     bridge_eval_let_star_with_step_decomposes]
QED

Theorem bridge_let_star_provenance_valid_head:
  ∀let_fuel ev binding rest body original out v value.
    let_binding_pair binding = SOME (v, value) ∧
    let_star_provenance (SUC let_fuel) ev (binding :: rest)
      body original out ⇒
    ∃evaluated.
      MEM evaluated (ev value) ∧
      let_star_provenance let_fuel ev
        (subst_binding_pairs v evaluated rest)
        (apply_subst [metta_m1$Bind v evaluated] body)
        original out
Proof
  rw[] \\
  qpat_x_assum ‘let_star_provenance _ _ _ _ _ _’ mp_tac \\
  rw[let_star_provenance_def] \\
  gvs[]
QED

Theorem bridge_eval_let_star_fragment_payload_recursive_sound:
  ∀fuel space binding rest body v value out.
    let_binding_pair binding = SOME (v, value) ∧
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body])) ⇒
    ∃evaluated payload.
      MEM evaluated (eval_m1_rec fuel space value) ∧
      eval_m1_rec_result_sound fuel space value evaluated ∧
      eval_m1_rec_family_sound fuel space value evaluated ∧
      payload =
        (bridge_subst_binding_pairs v evaluated rest,
         bridge_apply_subst [metta_m1$Bind v evaluated] body) ∧
      MEM payload
        (bridge_let_star_step_payloads binding rest body
          (eval_m1_rec fuel space value)) ∧
      MEM out
        (eval_let_star_with (SUC (LENGTH rest))
          (λa. eval_m1_rec fuel space a)
          (FST payload) (SND payload)
          (metta_m1$Expr
            [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body])) ∧
      let_star_provenance (SUC (LENGTH rest))
        (λa. eval_m1_rec fuel space a)
        (FST payload) (SND payload)
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out ∧
      let_star_family_provenance fuel space (SUC (LENGTH rest))
        (FST payload) (SND payload)
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out
Proof
  rpt strip_tac \\
  qabbrev_tac
    ‘original =
       metta_m1$Expr
         [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]’ \\
  ‘let_star_provenance (SUC (LENGTH (binding :: rest)))
     (λa. eval_m1_rec fuel space a) (binding :: rest) body
     original out’
    by (qunabbrev_tac ‘original’ \\
        fs[eval_m1_rec_let_star_member_iff]) \\
  ‘∃evaluated.
     MEM evaluated (eval_m1_rec fuel space value) ∧
     let_star_provenance (SUC (LENGTH rest))
       (λa. eval_m1_rec fuel space a)
       (subst_binding_pairs v evaluated rest)
       (apply_subst [metta_m1$Bind v evaluated] body)
       original out’
    by (fs[] \\
        metis_tac[bridge_let_star_provenance_valid_head]) \\
  pop_assum strip_assume_tac \\
  ‘eval_m1_rec_result_sound fuel space value evaluated’
    by (irule eval_m1_rec_result_sound \\ rw[]) \\
  ‘eval_m1_rec_family_sound fuel space value evaluated’
    by (irule eval_m1_rec_family_result_sound \\ rw[]) \\
  ‘MEM
     (bridge_subst_binding_pairs v evaluated rest,
      bridge_apply_subst [metta_m1$Bind v evaluated] body)
     (bridge_let_star_step_payloads binding rest body
       (eval_m1_rec fuel space value))’
    by metis_tac[bridge_let_star_step_payloads_member] \\
  ‘let_star_provenance (SUC (LENGTH rest))
     (λa. eval_m1_rec fuel space a)
     (bridge_subst_binding_pairs v evaluated rest)
     (bridge_apply_subst [metta_m1$Bind v evaluated] body)
     original out’
    by fs[bridge_subst_binding_pairs_matches_subst_binding_pairs,
          bridge_apply_subst_atom_matches_apply_subst] \\
  ‘MEM out
     (eval_let_star_with (SUC (LENGTH rest))
       (λa. eval_m1_rec fuel space a)
       (bridge_subst_binding_pairs v evaluated rest)
       (bridge_apply_subst [metta_m1$Bind v evaluated] body)
       original)’
    by fs[eval_let_star_with_member_iff] \\
  ‘let_star_family_provenance fuel space (SUC (LENGTH rest))
     (bridge_subst_binding_pairs v evaluated rest)
     (bridge_apply_subst [metta_m1$Bind v evaluated] body)
     original out’
    by metis_tac[let_star_provenance_family_sound] \\
  qexists_tac ‘evaluated’ \\
  qexists_tac
    ‘(bridge_subst_binding_pairs v evaluated rest,
      bridge_apply_subst [metta_m1$Bind v evaluated] body)’ \\
  rw[]
QED

Theorem bridge_eval_m1_rec_fuller_let_star_payload_sound:
  ∀fuel space binding rest body v value out.
    let_binding_pair binding = SOME (v, value) ∧
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body])) ⇒
    eval_m1_rec_result_sound (SUC fuel) space
      (metta_m1$Expr
        [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out ∧
    eval_m1_rec_nested_family_sound fuel space
      (metta_m1$Expr
        [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out ∧
    eval_m1_rec_family_sound (SUC fuel) space
      (metta_m1$Expr
        [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out ∧
    ∃evaluated payload.
      MEM evaluated (eval_m1_rec fuel space value) ∧
      eval_m1_rec_result_sound fuel space value evaluated ∧
      eval_m1_rec_family_sound fuel space value evaluated ∧
      payload =
        (bridge_subst_binding_pairs v evaluated rest,
         bridge_apply_subst [metta_m1$Bind v evaluated] body) ∧
      MEM payload
        (bridge_let_star_step_payloads binding rest body
          (eval_m1_rec fuel space value)) ∧
      MEM out
        (eval_let_star_with (SUC (LENGTH rest))
          (λa. eval_m1_rec fuel space a)
          (FST payload) (SND payload)
          (metta_m1$Expr
            [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body])) ∧
      let_star_provenance (SUC (LENGTH rest))
        (λa. eval_m1_rec fuel space a)
        (FST payload) (SND payload)
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out ∧
      let_star_family_provenance fuel space (SUC (LENGTH rest))
        (FST payload) (SND payload)
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >- (
    irule eval_m1_rec_nested_family_result_sound \\
    rw[eval_m1_rec_nested_family_atom_def]) \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  metis_tac[bridge_eval_let_star_fragment_payload_recursive_sound]
QED

Theorem bridge_eval_let_star_fragment_empty_decomposes:
  ∀fuel space body.
    bridge_eval_let_star_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 56; metta_m1$Expr []; body]) =
    eval_m1_rec fuel space body
Proof
  rw[bridge_eval_let_star_fragment_def, eval_let_star_with_def]
QED

Theorem bridge_let_star_step_payloads_positive_example:
  bridge_let_star_step_payloads
    (metta_m1$Expr [metta_m1$Var 0; metta_m1$IntLit 2])
    [metta_m1$Expr [metta_m1$Var 1; metta_m1$Var 0]]
    (metta_m1$Expr [metta_m1$Sym 11; metta_m1$Var 0; metta_m1$Var 1])
    [metta_m1$IntLit 7] =
  [([metta_m1$Expr [metta_m1$Var 1; metta_m1$IntLit 7]],
    metta_m1$Expr
      [metta_m1$Sym 11; metta_m1$IntLit 7; metta_m1$Var 1])]
Proof
  EVAL_TAC
QED

Theorem bridge_let_star_step_payloads_negative_example:
  bridge_let_star_step_payloads
    (metta_m1$Expr [metta_m1$Sym 8; metta_m1$IntLit 2])
    [] (metta_m1$Var 0) [metta_m1$IntLit 7] =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_eval_chain_values_decompose:
  ∀vals fuel space v templ.
    eval_m1_rec_chain fuel space v vals templ =
    bridge_chain_concat_results
      (MAP
        (λsubstituted. eval_m1_rec fuel space substituted)
        (bridge_chain_subst_values v vals templ))
Proof
  Induct \\ rw[eval_m1_rec_def, bridge_chain_subst_values_def,
    bridge_chain_concat_results_def,
    bridge_apply_subst_atom_matches_apply_subst]
QED

Theorem eval_chain_fragment_decomposes:
  ∀fuel space nested v templ.
    eval_chain_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 21; nested; metta_m1$Var v; templ]) =
    bridge_chain_concat_results
      (MAP
        (λsubstituted. eval_m1_rec fuel space substituted)
        (bridge_chain_subst_values v
          (eval_m1_rec fuel space nested) templ))
Proof
  rw[eval_chain_fragment_def, bridge_eval_chain_values_decompose]
QED

Theorem bridge_chain_subst_values_positive_example:
  bridge_chain_subst_values 0
    [metta_m1$Sym 8; metta_m1$Sym 9]
    (metta_m1$Expr [metta_m1$Sym 100; metta_m1$Var 0]) =
  [metta_m1$Expr [metta_m1$Sym 100; metta_m1$Sym 8];
   metta_m1$Expr [metta_m1$Sym 100; metta_m1$Sym 9]]
Proof
  EVAL_TAC
QED

Theorem bridge_chain_subst_values_negative_example:
  bridge_chain_subst_values 0
    [metta_m1$Sym 8]
    (metta_m1$Expr [metta_m1$Sym 100; metta_m1$Var 1]) =
  [metta_m1$Expr [metta_m1$Sym 100; metta_m1$Var 1]]
Proof
  EVAL_TAC
QED

Definition bridge_eval_chain_fragment_def:
  bridge_eval_chain_fragment fuel space atom =
    eval_chain_fragment fuel space atom
End

Theorem bridge_eval_chain_fragment_agrees_with_eval_m1_rec:
  ∀fuel space nested v templ.
    bridge_eval_chain_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 21; nested; metta_m1$Var v; templ]) =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 21; nested; metta_m1$Var v; templ])
Proof
  rw[bridge_eval_chain_fragment_def,
     eval_chain_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_eval_chain_fragment_matches_hol_fragment:
  ∀fuel space atom.
    bridge_eval_chain_fragment fuel space atom =
    eval_chain_fragment fuel space atom
Proof
  rw[bridge_eval_chain_fragment_def]
QED

Theorem bridge_eval_chain_fragment_decomposes:
  ∀fuel space nested v templ.
    bridge_eval_chain_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 21; nested; metta_m1$Var v; templ]) =
    bridge_chain_concat_results
      (MAP
        (λsubstituted. eval_m1_rec fuel space substituted)
        (bridge_chain_subst_values v
          (eval_m1_rec fuel space nested) templ))
Proof
  rw[bridge_eval_chain_fragment_def, eval_chain_fragment_decomposes]
QED

Theorem bridge_eval_chain_fragment_member_uses_subst_payload:
  ∀fuel space nested v templ out.
    MEM out
      (bridge_eval_chain_fragment fuel space
        (metta_m1$Expr
          [metta_m1$Sym 21; nested; metta_m1$Var v; templ])) ⇒
    ∃substituted.
      MEM substituted
        (bridge_chain_subst_values v
          (eval_m1_rec fuel space nested) templ) ∧
      MEM out (eval_m1_rec fuel space substituted)
Proof
  rw[bridge_eval_chain_fragment_def, eval_chain_fragment_def] \\
  drule eval_m1_rec_chain_member_sound \\
  rw[bridge_chain_subst_values_member,
     bridge_apply_subst_atom_matches_apply_subst] \\
  metis_tac[]
QED

Definition bridge_surface_eval_chain_fragment_wrapper_def:
  bridge_surface_eval_chain_fragment_wrapper fuel surface_space surface_atom =
    case bridge_import_surface_atom_list surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_chain_fragment fuel space atom)
End

Theorem bridge_surface_eval_chain_fragment_wrapper_agrees_with_eval_m1_rec:
  ∀fuel surface_space nested v templ space nested_atom templ_atom.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom nested = SOME nested_atom ∧
    bridge_import_surface_atom templ = SOME templ_atom ⇒
    bridge_surface_eval_chain_fragment_wrapper fuel surface_space
      (BExpr [BSym (strlit"chain"); nested; BVar v; templ]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 21; nested_atom; metta_m1$Var v; templ_atom])
Proof
  rw[bridge_surface_eval_chain_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_chain_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_chain_fragment_wrapper_member_uses_subst_payload:
  ∀fuel surface_space nested v templ space nested_atom templ_atom out.
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom nested = SOME nested_atom ∧
    bridge_import_surface_atom templ = SOME templ_atom ∧
    MEM out
      (bridge_surface_eval_chain_fragment_wrapper fuel surface_space
        (BExpr [BSym (strlit"chain"); nested; BVar v; templ])) ⇒
    ∃substituted.
      MEM substituted
        (bridge_chain_subst_values v
          (eval_m1_rec fuel space nested_atom) templ_atom) ∧
      MEM out (eval_m1_rec fuel space substituted)
Proof
  rw[bridge_surface_eval_chain_fragment_wrapper_def,
     bridge_import_surface_atom_def, bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  drule bridge_eval_chain_fragment_member_uses_subst_payload \\
  rw[]
QED

Theorem bridge_eval_chain_fragment_payload_recursive_sound:
  ∀fuel space nested v templ out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 21; nested; metta_m1$Var v; templ])) ⇒
    ∃payload.
      MEM payload
        (bridge_chain_subst_values v
          (eval_m1_rec fuel space nested) templ) ∧
      MEM out (eval_m1_rec fuel space payload) ∧
      eval_m1_rec_result_sound fuel space payload out ∧
      eval_m1_rec_family_sound fuel space payload out
Proof
  rpt strip_tac \\
  ‘MEM out
     (bridge_eval_chain_fragment fuel space
       (metta_m1$Expr
         [metta_m1$Sym 21; nested; metta_m1$Var v; templ]))’
    by metis_tac[bridge_eval_chain_fragment_agrees_with_eval_m1_rec] \\
  metis_tac[bridge_eval_chain_fragment_member_uses_subst_payload,
            eval_m1_rec_result_sound,
            eval_m1_rec_family_result_sound]
QED

Definition bridge_nested_payload_supported_atom_def:
  bridge_nested_payload_supported_atom atom ⇔
    (∃nested v templ.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 21; nested; metta_m1$Var v; templ]) ∨
    (∃term expected.
       atom =
         metta_m1$Expr [metta_m1$Sym 57; term; expected]) ∨
    (∃scrut branches.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 54; scrut; metta_m1$Expr branches]) ∨
    (∃scrut branches.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 55; scrut; metta_m1$Expr branches]) ∨
    (∃binding rest body v value.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body] ∧
       let_binding_pair binding = SOME (v, value))
End

Definition bridge_let_star_payload_result_def:
  bridge_let_star_payload_result fuel space binding rest body v value out ⇔
    ∃evaluated payload.
      MEM evaluated (eval_m1_rec fuel space value) ∧
      eval_m1_rec_result_sound fuel space value evaluated ∧
      eval_m1_rec_family_sound fuel space value evaluated ∧
      payload =
        (bridge_subst_binding_pairs v evaluated rest,
         bridge_apply_subst [metta_m1$Bind v evaluated] body) ∧
      MEM payload
        (bridge_let_star_step_payloads binding rest body
          (eval_m1_rec fuel space value)) ∧
      MEM out
        (eval_let_star_with (SUC (LENGTH rest))
          (λa. eval_m1_rec fuel space a)
          (FST payload) (SND payload)
          (metta_m1$Expr
            [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body])) ∧
      let_star_provenance (SUC (LENGTH rest))
        (λa. eval_m1_rec fuel space a)
        (FST payload) (SND payload)
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out ∧
      let_star_family_provenance fuel space (SUC (LENGTH rest))
        (FST payload) (SND payload)
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out
End

Definition bridge_nested_payload_result_def:
  bridge_nested_payload_result fuel space atom out ⇔
    (∃nested v templ payload.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 21; nested; metta_m1$Var v; templ] ∧
       MEM payload
         (bridge_chain_subst_values v
           (eval_m1_rec fuel space nested) templ) ∧
       MEM out (eval_m1_rec fuel space payload) ∧
       eval_m1_rec_result_sound fuel space payload out ∧
       eval_m1_rec_family_sound fuel space payload out) ∨
    (∃term expected value checked_values.
       atom =
         metta_m1$Expr [metta_m1$Sym 57; term; expected] ∧
       checked_values =
         (if hol_typed_add_bad space term
          then [error_atom term (metta_m1$Sym 10)]
          else eval_m1_rec fuel space term) ∧
       MEM value checked_values ∧
       MEM out
         (bridge_evalc_checked_values space term expected checked_values) ∧
       (¬hol_typed_add_bad space term ⇒
        eval_m1_rec_result_sound fuel space term value ∧
        eval_m1_rec_family_sound fuel space term value) ∧
       ((hol_any_type_match expected
           (hol_declared_or_default_type_lookup space value) ∧ out = value) ∨
        (¬hol_any_type_match expected
           (hol_declared_or_default_type_lookup space value) ∧
         out = error_atom term (metta_m1$Sym 10)))) ∨
    (∃scrut branches payload.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 54; scrut; metta_m1$Expr branches] ∧
       MEM payload
         (bridge_branch_values_payloads
           (eval_m1_rec fuel space scrut) branches) ∧
       MEM out (eval_m1_rec fuel space payload) ∧
       eval_m1_rec_result_sound fuel space payload out ∧
       eval_m1_rec_family_sound fuel space payload out) ∨
    (∃scrut branches payload.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 55; scrut; metta_m1$Expr branches] ∧
       MEM payload
         (bridge_branch_values_payloads
           (eval_m1_rec fuel space scrut) branches) ∧
       MEM out (eval_m1_rec fuel space payload) ∧
       eval_m1_rec_result_sound fuel space payload out ∧
       eval_m1_rec_family_sound fuel space payload out) ∨
    (∃binding rest body v value.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body] ∧
       let_binding_pair binding = SOME (v, value) ∧
       bridge_let_star_payload_result fuel space
         binding rest body v value out)
End

Theorem bridge_nested_payload_result_chain:
  ∀fuel space nested v templ out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 21; nested; metta_m1$Var v; templ])) ⇒
    bridge_nested_payload_result fuel space
      (metta_m1$Expr
        [metta_m1$Sym 21; nested; metta_m1$Var v; templ]) out
Proof
  rw[bridge_nested_payload_result_def] \\
  metis_tac[bridge_eval_chain_fragment_payload_recursive_sound]
QED

Theorem bridge_nested_payload_result_evalc:
  ∀fuel space term expected out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 57; term; expected])) ⇒
    bridge_nested_payload_result fuel space
      (metta_m1$Expr [metta_m1$Sym 57; term; expected]) out
Proof
  rpt strip_tac \\
  first_x_assum
    (fn th =>
       mp_tac (MATCH_MP
         bridge_eval_evalc_fragment_payload_recursive_sound th)) \\
  rw[bridge_nested_payload_result_def] \\
  metis_tac[]
QED

Theorem bridge_nested_payload_result_case:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 54; scrut; metta_m1$Expr branches])) ⇒
    bridge_nested_payload_result fuel space
      (metta_m1$Expr
        [metta_m1$Sym 54; scrut; metta_m1$Expr branches]) out
Proof
  rpt strip_tac \\
  first_x_assum
    (fn th =>
       mp_tac (MATCH_MP
         bridge_eval_case_fragment_payload_recursive_sound th)) \\
  rw[bridge_nested_payload_result_def] \\
  metis_tac[]
QED

Theorem bridge_nested_payload_result_switch:
  ∀fuel space scrut branches out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 55; scrut; metta_m1$Expr branches])) ⇒
    bridge_nested_payload_result fuel space
      (metta_m1$Expr
        [metta_m1$Sym 55; scrut; metta_m1$Expr branches]) out
Proof
  rpt strip_tac \\
  first_x_assum
    (fn th =>
       mp_tac (MATCH_MP
         bridge_eval_switch_fragment_payload_recursive_sound th)) \\
  rw[bridge_nested_payload_result_def] \\
  metis_tac[]
QED

Theorem bridge_let_star_payload_result_sound:
  ∀fuel space binding rest body v value out.
    let_binding_pair binding = SOME (v, value) ∧
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body])) ⇒
    bridge_let_star_payload_result fuel space binding rest body v value out
Proof
  rpt strip_tac \\
  ‘∃evaluated payload.
     MEM evaluated (eval_m1_rec fuel space value) ∧
     eval_m1_rec_result_sound fuel space value evaluated ∧
     eval_m1_rec_family_sound fuel space value evaluated ∧
     payload =
       (bridge_subst_binding_pairs v evaluated rest,
        bridge_apply_subst [metta_m1$Bind v evaluated] body) ∧
     MEM payload
       (bridge_let_star_step_payloads binding rest body
         (eval_m1_rec fuel space value)) ∧
     MEM out
       (eval_let_star_with (SUC (LENGTH rest))
         (λa. eval_m1_rec fuel space a)
         (FST payload) (SND payload)
         (metta_m1$Expr
           [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body])) ∧
     let_star_provenance (SUC (LENGTH rest))
       (λa. eval_m1_rec fuel space a)
       (FST payload) (SND payload)
       (metta_m1$Expr
         [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out ∧
     let_star_family_provenance fuel space (SUC (LENGTH rest))
       (FST payload) (SND payload)
       (metta_m1$Expr
         [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out’
    by (irule bridge_eval_let_star_fragment_payload_recursive_sound \\
        rw[]) \\
  pop_assum strip_assume_tac \\
  rw[bridge_let_star_payload_result_def] \\
  qexists_tac ‘evaluated’ \\
  fs[]
QED

Theorem bridge_nested_payload_result_let_star:
  ∀fuel space binding rest body v value out.
    let_binding_pair binding = SOME (v, value) ∧
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body])) ⇒
    bridge_nested_payload_result fuel space
      (metta_m1$Expr
        [metta_m1$Sym 56; metta_m1$Expr (binding :: rest); body]) out
Proof
  rw[bridge_nested_payload_result_def] \\
  metis_tac[bridge_let_star_payload_result_sound]
QED

Theorem bridge_eval_m1_rec_supported_nested_payload_sound:
  ∀fuel space atom out.
    bridge_nested_payload_supported_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    bridge_nested_payload_result fuel space atom out
Proof
  rw[bridge_nested_payload_supported_atom_def] \\
  gvs[] >-
    metis_tac[bridge_nested_payload_result_chain] >-
    metis_tac[bridge_nested_payload_result_evalc] >-
    metis_tac[bridge_nested_payload_result_case] >-
    metis_tac[bridge_nested_payload_result_switch] \\
  metis_tac[bridge_nested_payload_result_let_star]
QED

Theorem bridge_nested_payload_supported_atom_nested_family:
  ∀atom.
    bridge_nested_payload_supported_atom atom ⇒
    eval_m1_rec_nested_family_atom atom
Proof
  rw[bridge_nested_payload_supported_atom_def,
     eval_m1_rec_nested_family_atom_def] \\
  metis_tac[]
QED

Theorem bridge_eval_m1_rec_supported_nested_fuller_sound:
  ∀fuel space atom out.
    bridge_nested_payload_supported_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_nested_family_sound fuel space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_nested_payload_result fuel space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[bridge_nested_payload_supported_atom_nested_family,
              eval_m1_rec_nested_family_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  metis_tac[bridge_eval_m1_rec_supported_nested_payload_sound]
QED

Definition bridge_eval_payload_result_sound_def:
  bridge_eval_payload_result_sound fuel space body out ⇔
    (eval_m1_rec fuel space body = [body] ∧ out = metta_m1$Sym 23) ∨
    (eval_m1_rec fuel space body ≠ [body] ∧
     MEM out (eval_m1_rec fuel space body) ∧
     eval_m1_rec_result_sound fuel space body out ∧
     eval_m1_rec_family_sound fuel space body out)
End

Definition bridge_return_payload_result_def:
  bridge_return_payload_result value out ⇔
    out = metta_m1$Expr [metta_m1$Sym 19; value]
End

Definition bridge_function_payload_result_def:
  bridge_function_payload_result fuel space body out ⇔
    MEM out
      (return_payloads
        (metta_m1$Expr [metta_m1$Sym 18; body])
        (eval_m1_rec fuel space body)) ∧
    ((∃inner value.
       MEM inner (eval_m1_rec fuel space body) ∧
       eval_m1_rec_result_sound fuel space body inner ∧
       eval_m1_rec_family_sound fuel space body inner ∧
       return_payload_of inner = SOME value ∧ out = value) ∨
     out =
       error_atom
         (metta_m1$Expr [metta_m1$Sym 18; body])
         (metta_m1$Sym 22))
End

Theorem bridge_eval_eval_fragment_payload_recursive_sound:
  ∀fuel space body out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 20; body])) ⇒
    bridge_eval_payload_result_sound fuel space body out
Proof
  rw[eval_m1_rec_def, bridge_eval_payload_result_sound_def] \\
  metis_tac[eval_m1_rec_result_sound, eval_m1_rec_family_result_sound]
QED

Theorem bridge_eval_return_fragment_payload_sound:
  ∀fuel space value out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 19; value])) ⇒
    bridge_return_payload_result value out
Proof
  rw[eval_m1_rec_def, bridge_return_payload_result_def]
QED

Theorem bridge_eval_function_fragment_payload_recursive_sound:
  ∀fuel space body out.
    MEM out
      (eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 18; body])) ⇒
    bridge_function_payload_result fuel space body out
Proof
  rw[eval_m1_rec_def, bridge_function_payload_result_def] \\
  drule return_payloads_member_sound \\
  rw[] \\
  metis_tac[eval_m1_rec_result_sound, eval_m1_rec_family_result_sound]
QED

Definition bridge_control_payload_supported_atom_def:
  bridge_control_payload_supported_atom atom ⇔
    (∃body. atom = metta_m1$Expr [metta_m1$Sym 18; body]) ∨
    (∃value. atom = metta_m1$Expr [metta_m1$Sym 19; value]) ∨
    (∃body. atom = metta_m1$Expr [metta_m1$Sym 20; body])
End

Definition bridge_control_payload_result_def:
  bridge_control_payload_result fuel space atom out ⇔
    (∃body.
       atom = metta_m1$Expr [metta_m1$Sym 18; body] ∧
       bridge_function_payload_result fuel space body out) ∨
    (∃value.
       atom = metta_m1$Expr [metta_m1$Sym 19; value] ∧
       bridge_return_payload_result value out) ∨
    (∃body.
       atom = metta_m1$Expr [metta_m1$Sym 20; body] ∧
       bridge_eval_payload_result_sound fuel space body out)
End

Theorem bridge_control_payload_supported_atom_control:
  ∀atom.
    bridge_control_payload_supported_atom atom ⇒
    eval_m1_rec_control_atom atom
Proof
  rw[bridge_control_payload_supported_atom_def,
     eval_m1_rec_control_atom_def] \\
  metis_tac[]
QED

Theorem bridge_eval_m1_rec_supported_control_payload_sound:
  ∀fuel space atom out.
    bridge_control_payload_supported_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    bridge_control_payload_result fuel space atom out
Proof
  rw[bridge_control_payload_supported_atom_def,
     bridge_control_payload_result_def] >-
    metis_tac[bridge_eval_function_fragment_payload_recursive_sound] >-
    metis_tac[bridge_eval_return_fragment_payload_sound] \\
  metis_tac[bridge_eval_eval_fragment_payload_recursive_sound]
QED

Theorem bridge_eval_m1_rec_supported_control_fuller_sound:
  ∀fuel space atom out.
    bridge_control_payload_supported_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_control_sound fuel space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_control_payload_result fuel space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[bridge_control_payload_supported_atom_control,
              eval_m1_rec_control_input_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  metis_tac[bridge_eval_m1_rec_supported_control_payload_sound]
QED

Definition bridge_supported_branch_payload_atom_def:
  bridge_supported_branch_payload_atom atom ⇔
    bridge_control_payload_supported_atom atom ∨
    bridge_nested_payload_supported_atom atom
End

Definition bridge_supported_branch_payload_result_def:
  bridge_supported_branch_payload_result fuel space atom out ⇔
    (bridge_control_payload_supported_atom atom ∧
     eval_m1_rec_control_sound fuel space atom out ∧
     bridge_control_payload_result fuel space atom out) ∨
    (bridge_nested_payload_supported_atom atom ∧
     eval_m1_rec_nested_family_sound fuel space atom out ∧
     bridge_nested_payload_result fuel space atom out)
End

Theorem bridge_eval_m1_rec_supported_branch_payload_sound:
  ∀fuel space atom out.
    bridge_supported_branch_payload_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    bridge_supported_branch_payload_result fuel space atom out
Proof
  rw[bridge_supported_branch_payload_atom_def,
     bridge_supported_branch_payload_result_def] >-
    metis_tac[bridge_eval_m1_rec_supported_control_fuller_sound] \\
  metis_tac[bridge_eval_m1_rec_supported_nested_fuller_sound]
QED

Theorem bridge_eval_m1_rec_supported_branch_fuller_sound:
  ∀fuel space atom out.
    bridge_supported_branch_payload_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_supported_branch_payload_result fuel space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  metis_tac[bridge_eval_m1_rec_supported_branch_payload_sound]
QED

Definition bridge_fallback_payload_supported_atom_def:
  bridge_fallback_payload_supported_atom atom ⇔
    ¬eval_m1_rec_proven_branch_atom atom
End

Definition bridge_fallback_payload_result_def:
  bridge_fallback_payload_result fuel space atom out ⇔
    MEM out (eval_m1_ext (SUC fuel) space atom) ∧
    (out = atom ∨ out = error_atom atom (metta_m1$Sym 3) ∨
     equality_step space atom out ∨ builtin_step atom out ∨
     ∃pattern templ.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ] ∧
       MEM out (bridge_match_space_payload space pattern templ))
End

Theorem bridge_eval_m1_rec_fallback_payload_sound:
  ∀fuel space atom out.
    bridge_fallback_payload_supported_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    bridge_fallback_payload_result fuel space atom out
Proof
  rpt strip_tac \\
  ‘MEM out (eval_m1_ext (SUC fuel) space atom)’
    by metis_tac[bridge_fallback_payload_supported_atom_def,
                  eval_m1_rec_fallback_ext_member] \\
  rw[bridge_fallback_payload_result_def] \\
  drule eval_m1_ext_sound \\
  rw[] \\
  metis_tac[bridge_match_space_payload_matches_match_space]
QED

Theorem bridge_eval_m1_rec_fallback_fuller_sound:
  ∀fuel space atom out.
    bridge_fallback_payload_supported_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_fallback_payload_result fuel space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  metis_tac[bridge_eval_m1_rec_fallback_payload_sound]
QED

Definition bridge_supported_or_fallback_payload_atom_def:
  bridge_supported_or_fallback_payload_atom atom ⇔
    bridge_supported_branch_payload_atom atom ∨
    bridge_fallback_payload_supported_atom atom
End

Definition bridge_supported_or_fallback_payload_result_def:
  bridge_supported_or_fallback_payload_result fuel space atom out ⇔
    (bridge_supported_branch_payload_atom atom ∧
     bridge_supported_branch_payload_result fuel space atom out) ∨
    (bridge_fallback_payload_supported_atom atom ∧
     bridge_fallback_payload_result fuel space atom out)
End

Theorem bridge_eval_m1_rec_supported_or_fallback_fuller_sound:
  ∀fuel space atom out.
    bridge_supported_or_fallback_payload_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_supported_or_fallback_payload_result fuel space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  fs[bridge_supported_or_fallback_payload_atom_def] >- (
    simp[Once bridge_supported_or_fallback_payload_result_def] \\
    disj1_tac \\
    metis_tac[bridge_eval_m1_rec_supported_branch_fuller_sound]) \\
  simp[Once bridge_supported_or_fallback_payload_result_def] \\
  disj2_tac \\
  metis_tac[bridge_eval_m1_rec_fallback_fuller_sound]
QED

Definition bridge_match_fallback_payload_supported_atom_def:
  bridge_match_fallback_payload_supported_atom atom ⇔
    ∃pattern templ.
      atom =
        metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]
End

Definition bridge_match_fallback_payload_result_def:
  bridge_match_fallback_payload_result space atom out ⇔
    ∃pattern templ.
      atom =
        metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ] ∧
      MEM out (bridge_match_space_payload space pattern templ)
End

Theorem bridge_match_fallback_payload_supported_atom_fallback:
  ∀atom.
    bridge_match_fallback_payload_supported_atom atom ⇒
    bridge_fallback_payload_supported_atom atom
Proof
  rw[bridge_match_fallback_payload_supported_atom_def,
     bridge_fallback_payload_supported_atom_def,
     eval_m1_rec_proven_branch_atom_def]
QED

Theorem bridge_eval_m1_rec_match_fallback_payload_sound:
  ∀fuel space atom out.
    bridge_match_fallback_payload_supported_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    bridge_match_fallback_payload_result space atom out
Proof
  rw[bridge_match_fallback_payload_supported_atom_def,
     bridge_match_fallback_payload_result_def] \\
  ‘bridge_eval_match_fragment space
     (metta_m1$Expr
       [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) =
   eval_m1_rec (SUC fuel) space
     (metta_m1$Expr
       [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ])’
    by rw[bridge_eval_match_fragment_agrees_with_eval_m1_rec] \\
  fs[bridge_eval_match_fragment_def]
QED

Theorem bridge_eval_m1_rec_match_fallback_fuller_sound:
  ∀fuel space atom out.
    bridge_match_fallback_payload_supported_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_fallback_payload_result fuel space atom out ∧
    bridge_match_fallback_payload_result space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  conj_tac >-
    metis_tac[bridge_match_fallback_payload_supported_atom_fallback,
              bridge_eval_m1_rec_fallback_payload_sound] \\
  metis_tac[bridge_eval_m1_rec_match_fallback_payload_sound]
QED

Definition bridge_equality_fallback_payload_supported_def:
  bridge_equality_fallback_payload_supported space atom ⇔
    bridge_fallback_payload_supported_atom atom ∧
    (∀pattern templ.
       atom ≠
         metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) ∧
    builtin_eval atom = NoBuiltin ∧
    eval_equalities space atom ≠ []
End

Definition bridge_equality_fallback_payload_result_def:
  bridge_equality_fallback_payload_result space atom out ⇔
    MEM out (eval_equalities space atom) ∧
    equality_step space atom out
End

Theorem bridge_eval_m1_ext_equality_fallback_eq:
  ∀fuel space atom.
    (∀pattern templ.
       atom ≠
         metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) ∧
    builtin_eval atom = NoBuiltin ∧
    eval_equalities space atom ≠ [] ⇒
    eval_m1_ext (SUC fuel) space atom = eval_equalities space atom
Proof
  rw[eval_m1_ext_def] \\
  every_case_tac \\
  gvs[]
QED

Theorem bridge_eval_m1_rec_equality_fallback_payload_sound:
  ∀fuel space atom out.
    bridge_equality_fallback_payload_supported space atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    bridge_equality_fallback_payload_result space atom out
Proof
  rw[bridge_equality_fallback_payload_supported_def,
     bridge_equality_fallback_payload_result_def] \\
  ‘eval_m1_rec (SUC fuel) space atom =
   eval_m1_ext (SUC fuel) space atom’
    by metis_tac[bridge_fallback_payload_supported_atom_def,
                  eval_m1_rec_fallback_ext_eq] \\
  ‘eval_m1_ext (SUC fuel) space atom = eval_equalities space atom’
    by metis_tac[bridge_eval_m1_ext_equality_fallback_eq] \\
  rw[] \\
  metis_tac[eval_equalities_sound]
QED

Theorem bridge_eval_m1_rec_equality_fallback_fuller_sound:
  ∀fuel space atom out.
    bridge_equality_fallback_payload_supported space atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_fallback_payload_result fuel space atom out ∧
    bridge_equality_fallback_payload_result space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  conj_tac >-
    metis_tac[bridge_equality_fallback_payload_supported_def,
              bridge_eval_m1_rec_fallback_payload_sound] \\
  metis_tac[bridge_eval_m1_rec_equality_fallback_payload_sound]
QED

Definition bridge_builtin_fallback_payload_supported_def:
  bridge_builtin_fallback_payload_supported atom ⇔
    bridge_fallback_payload_supported_atom atom ∧
    (∀pattern templ.
       atom ≠
         metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) ∧
    ∃outs. builtin_eval atom = BuiltinResult outs
End

Definition bridge_builtin_fallback_payload_result_def:
  bridge_builtin_fallback_payload_result atom out ⇔
    builtin_step atom out
End

Theorem bridge_eval_m1_ext_builtin_fallback_eq:
  ∀fuel space atom outs.
    (∀pattern templ.
       atom ≠
         metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) ∧
    builtin_eval atom = BuiltinResult outs ⇒
    eval_m1_ext (SUC fuel) space atom = outs
Proof
  rw[eval_m1_ext_def] \\
  every_case_tac \\
  gvs[]
QED

Theorem bridge_eval_m1_rec_builtin_fallback_payload_sound:
  ∀fuel space atom out.
    bridge_builtin_fallback_payload_supported atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    bridge_builtin_fallback_payload_result atom out
Proof
  rpt strip_tac \\
  fs[bridge_builtin_fallback_payload_supported_def] \\
  ‘eval_m1_rec (SUC fuel) space atom =
   eval_m1_ext (SUC fuel) space atom’
    by metis_tac[bridge_fallback_payload_supported_atom_def,
                  eval_m1_rec_fallback_ext_eq] \\
  ‘eval_m1_ext (SUC fuel) space atom = outs’
    by metis_tac[bridge_eval_m1_ext_builtin_fallback_eq] \\
  fs[bridge_builtin_fallback_payload_result_def, builtin_step_def] \\
  metis_tac[]
QED

Theorem bridge_eval_m1_rec_builtin_fallback_fuller_sound:
  ∀fuel space atom out.
    bridge_builtin_fallback_payload_supported atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_fallback_payload_result fuel space atom out ∧
    bridge_builtin_fallback_payload_result atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  conj_tac >-
    metis_tac[bridge_builtin_fallback_payload_supported_def,
              bridge_eval_m1_rec_fallback_payload_sound] \\
  metis_tac[bridge_eval_m1_rec_builtin_fallback_payload_sound]
QED

Definition bridge_identity_fallback_payload_supported_def:
  bridge_identity_fallback_payload_supported space atom ⇔
    bridge_fallback_payload_supported_atom atom ∧
    (∀pattern templ.
       atom ≠
         metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) ∧
    builtin_eval atom = NoBuiltin ∧
    eval_equalities space atom = []
End

Definition bridge_identity_fallback_payload_result_def:
  bridge_identity_fallback_payload_result atom out ⇔
    out = atom
End

Theorem bridge_eval_m1_ext_identity_fallback_eq:
  ∀fuel space atom.
    (∀pattern templ.
       atom ≠
         metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]) ∧
    builtin_eval atom = NoBuiltin ∧
    eval_equalities space atom = [] ⇒
    eval_m1_ext (SUC fuel) space atom = [atom]
Proof
  rw[eval_m1_ext_def] \\
  every_case_tac \\
  gvs[]
QED

Theorem bridge_eval_m1_rec_identity_fallback_payload_sound:
  ∀fuel space atom out.
    bridge_identity_fallback_payload_supported space atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    bridge_identity_fallback_payload_result atom out
Proof
  rpt strip_tac \\
  fs[bridge_identity_fallback_payload_supported_def] \\
  ‘eval_m1_rec (SUC fuel) space atom =
   eval_m1_ext (SUC fuel) space atom’
    by metis_tac[bridge_fallback_payload_supported_atom_def,
                  eval_m1_rec_fallback_ext_eq] \\
  ‘eval_m1_ext (SUC fuel) space atom = [atom]’
    by metis_tac[bridge_eval_m1_ext_identity_fallback_eq] \\
  fs[bridge_identity_fallback_payload_result_def]
QED

Theorem bridge_eval_m1_rec_identity_fallback_fuller_sound:
  ∀fuel space atom out.
    bridge_identity_fallback_payload_supported space atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_fallback_payload_result fuel space atom out ∧
    bridge_identity_fallback_payload_result atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  conj_tac >-
    metis_tac[bridge_identity_fallback_payload_supported_def,
              bridge_eval_m1_rec_fallback_payload_sound] \\
  metis_tac[bridge_eval_m1_rec_identity_fallback_payload_sound]
QED

Definition bridge_split_fallback_payload_atom_def:
  bridge_split_fallback_payload_atom space atom ⇔
    bridge_match_fallback_payload_supported_atom atom ∨
    bridge_builtin_fallback_payload_supported atom ∨
    bridge_equality_fallback_payload_supported space atom ∨
    bridge_identity_fallback_payload_supported space atom
End

Definition bridge_split_fallback_payload_result_def:
  bridge_split_fallback_payload_result space atom out ⇔
    (bridge_match_fallback_payload_supported_atom atom ∧
     bridge_match_fallback_payload_result space atom out) ∨
    (bridge_builtin_fallback_payload_supported atom ∧
     bridge_builtin_fallback_payload_result atom out) ∨
    (bridge_equality_fallback_payload_supported space atom ∧
     bridge_equality_fallback_payload_result space atom out) ∨
    (bridge_identity_fallback_payload_supported space atom ∧
     bridge_identity_fallback_payload_result atom out)
End

Theorem bridge_fallback_payload_supported_atom_split:
  ∀space atom.
    bridge_fallback_payload_supported_atom atom ⇒
    bridge_split_fallback_payload_atom space atom
Proof
  rpt strip_tac \\
  rw[bridge_split_fallback_payload_atom_def] \\
  Cases_on
    ‘∃pattern templ.
       atom =
         metta_m1$Expr
          [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]’ >- (
    disj1_tac \\
    rw[bridge_match_fallback_payload_supported_atom_def]) \\
  ‘∀pattern templ.
     atom ≠
       metta_m1$Expr
        [metta_m1$Sym 4; metta_m1$Sym 5; pattern; templ]’
    by metis_tac[] \\
  Cases_on ‘builtin_eval atom’ >- (
    rename1 ‘builtin_eval atom = BuiltinResult outs’ \\
    disj2_tac \\
    disj1_tac \\
    rw[bridge_builtin_fallback_payload_supported_def] \\
    qexists_tac ‘outs’ \\
    rw[]) \\
  disj2_tac \\
  disj2_tac \\
  Cases_on ‘eval_equalities space atom = []’ >- (
    disj2_tac \\
    rw[bridge_identity_fallback_payload_supported_def]) \\
  disj1_tac \\
  rw[bridge_equality_fallback_payload_supported_def]
QED

Theorem bridge_eval_m1_rec_split_fallback_fuller_sound:
  ∀fuel space atom out.
    bridge_fallback_payload_supported_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_fallback_payload_result fuel space atom out ∧
    bridge_split_fallback_payload_result space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  ‘bridge_split_fallback_payload_atom space atom’
    by metis_tac[bridge_fallback_payload_supported_atom_split] \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  fs[bridge_split_fallback_payload_atom_def] >- (
    ‘bridge_fallback_payload_result fuel space atom out ∧
     bridge_match_fallback_payload_result space atom out’
      by metis_tac[bridge_eval_m1_rec_match_fallback_fuller_sound] \\
    rw[bridge_split_fallback_payload_result_def]) >- (
    ‘bridge_fallback_payload_result fuel space atom out ∧
     bridge_builtin_fallback_payload_result atom out’
      by metis_tac[bridge_eval_m1_rec_builtin_fallback_fuller_sound] \\
    rw[bridge_split_fallback_payload_result_def]) >- (
    ‘bridge_fallback_payload_result fuel space atom out ∧
     bridge_equality_fallback_payload_result space atom out’
      by metis_tac[bridge_eval_m1_rec_equality_fallback_fuller_sound] \\
    rw[bridge_split_fallback_payload_result_def]) \\
  ‘bridge_fallback_payload_result fuel space atom out ∧
   bridge_identity_fallback_payload_result atom out’
    by metis_tac[bridge_eval_m1_rec_identity_fallback_fuller_sound] \\
  rw[bridge_split_fallback_payload_result_def]
QED

Definition bridge_supported_or_split_fallback_payload_result_def:
  bridge_supported_or_split_fallback_payload_result fuel space atom out ⇔
    (bridge_supported_branch_payload_atom atom ∧
     bridge_supported_branch_payload_result fuel space atom out) ∨
    (bridge_fallback_payload_supported_atom atom ∧
     bridge_fallback_payload_result fuel space atom out ∧
     bridge_split_fallback_payload_result space atom out)
End

Theorem bridge_eval_m1_rec_supported_or_split_fallback_fuller_sound:
  ∀fuel space atom out.
    bridge_supported_or_fallback_payload_atom atom ∧
    MEM out (eval_m1_rec (SUC fuel) space atom) ⇒
    eval_m1_rec_result_sound (SUC fuel) space atom out ∧
    eval_m1_rec_family_sound (SUC fuel) space atom out ∧
    bridge_supported_or_split_fallback_payload_result fuel space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  fs[bridge_supported_or_fallback_payload_atom_def] >- (
    simp[Once bridge_supported_or_split_fallback_payload_result_def] \\
    disj1_tac \\
    metis_tac[bridge_eval_m1_rec_supported_branch_fuller_sound]) \\
  simp[Once bridge_supported_or_split_fallback_payload_result_def] \\
  disj2_tac \\
  metis_tac[bridge_eval_m1_rec_split_fallback_fuller_sound]
QED

Theorem bridge_surface_eval_chain_fragment_wrapper_positive_example:
  bridge_surface_eval_chain_fragment_wrapper 1
    [BExpr [BSym (strlit"Person"); BSym (strlit"True")]]
    (BExpr
      [BSym (strlit"chain");
       BExpr
        [BSym (strlit"match"); BSym (strlit"&self");
         BExpr [BSym (strlit"Person"); BVar 0];
         BVar 0];
       BVar 1;
       BExpr [BSym (strlit"return"); BVar 1]]) =
  [metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 8]]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_chain_fragment_wrapper_negative_example:
  bridge_surface_eval_chain_fragment_wrapper 1 []
    (BExpr
      [BSym (strlit"not-a-core-symbol"); BInt 1; BVar 0; BVar 0]) =
  []
Proof
  EVAL_TAC
QED

Definition bridge_surface_eval_eval_fragment_wrapper_with_env_def:
  bridge_surface_eval_eval_fragment_wrapper_with_env
    fuel env surface_space surface_atom =
    case bridge_import_surface_atom_list_with_env env surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom_with_env env surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_eval_fragment fuel space atom)
End

Theorem bridge_surface_eval_eval_fragment_wrapper_with_env_agrees_with_eval_m1_rec:
  ∀fuel env surface_space body space body_atom.
    bridge_import_surface_atom_list_with_env env surface_space =
      SOME space ∧
    bridge_import_surface_atom_with_env env body = SOME body_atom ⇒
    bridge_surface_eval_eval_fragment_wrapper_with_env fuel env surface_space
      (BExpr [BSym (strlit"eval"); body]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr [metta_m1$Sym 20; body_atom])
Proof
  rw[bridge_surface_eval_eval_fragment_wrapper_with_env_def,
     bridge_import_surface_atom_with_env_def,
     bridge_import_symbol_with_env_def,
     bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_eval_fragment_agrees_with_eval_m1_rec]
QED

Definition bridge_surface_eval_case_fragment_wrapper_with_env_def:
  bridge_surface_eval_case_fragment_wrapper_with_env
    fuel env surface_space surface_atom =
    case bridge_import_surface_atom_list_with_env env surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom_with_env env surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_case_fragment fuel space atom)
End

Theorem bridge_surface_eval_case_fragment_wrapper_with_env_agrees_with_eval_m1_rec:
  ∀fuel env surface_space scrut branches space scrut_atom branch_atoms.
    bridge_import_surface_atom_list_with_env env surface_space =
      SOME space ∧
    bridge_import_surface_atom_with_env env scrut = SOME scrut_atom ∧
    bridge_import_surface_atom_list_with_env env branches =
      SOME branch_atoms ⇒
    bridge_surface_eval_case_fragment_wrapper_with_env fuel env surface_space
      (BExpr [BSym (strlit"case"); scrut; BExpr branches]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 54; scrut_atom; metta_m1$Expr branch_atoms])
Proof
  rw[bridge_surface_eval_case_fragment_wrapper_with_env_def,
     bridge_import_surface_atom_with_env_def,
     bridge_import_symbol_with_env_def,
     bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_case_fragment_agrees_with_eval_m1_rec]
QED

Definition bridge_surface_eval_switch_fragment_wrapper_with_env_def:
  bridge_surface_eval_switch_fragment_wrapper_with_env
    fuel env surface_space surface_atom =
    case bridge_import_surface_atom_list_with_env env surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom_with_env env surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_switch_fragment fuel space atom)
End

Theorem bridge_surface_eval_switch_fragment_wrapper_with_env_agrees_with_eval_m1_rec:
  ∀fuel env surface_space scrut branches space scrut_atom branch_atoms.
    bridge_import_surface_atom_list_with_env env surface_space =
      SOME space ∧
    bridge_import_surface_atom_with_env env scrut = SOME scrut_atom ∧
    bridge_import_surface_atom_list_with_env env branches =
      SOME branch_atoms ⇒
    bridge_surface_eval_switch_fragment_wrapper_with_env fuel env surface_space
      (BExpr [BSym (strlit"switch"); scrut; BExpr branches]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 55; scrut_atom; metta_m1$Expr branch_atoms])
Proof
  rw[bridge_surface_eval_switch_fragment_wrapper_with_env_def,
     bridge_import_surface_atom_with_env_def,
     bridge_import_symbol_with_env_def,
     bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_switch_fragment_agrees_with_eval_m1_rec]
QED

Definition bridge_surface_eval_let_star_fragment_wrapper_with_env_def:
  bridge_surface_eval_let_star_fragment_wrapper_with_env
    fuel env surface_space surface_atom =
    case bridge_import_surface_atom_list_with_env env surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom_with_env env surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_let_star_fragment fuel space atom)
End

Theorem bridge_surface_eval_let_star_fragment_wrapper_with_env_agrees_with_eval_m1_rec:
  ∀fuel env surface_space bindings body space binding_atoms body_atom.
    bridge_import_surface_atom_list_with_env env surface_space =
      SOME space ∧
    bridge_import_surface_atom_list_with_env env bindings =
      SOME binding_atoms ∧
    bridge_import_surface_atom_with_env env body = SOME body_atom ⇒
    bridge_surface_eval_let_star_fragment_wrapper_with_env fuel env surface_space
      (BExpr [BSym (strlit"let*"); BExpr bindings; body]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 56; metta_m1$Expr binding_atoms; body_atom])
Proof
  rw[bridge_surface_eval_let_star_fragment_wrapper_with_env_def,
     bridge_import_surface_atom_with_env_def,
     bridge_import_symbol_with_env_def,
     bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_let_star_fragment_agrees_with_eval_m1_rec]
QED

Definition bridge_surface_eval_chain_fragment_wrapper_with_env_def:
  bridge_surface_eval_chain_fragment_wrapper_with_env
    fuel env surface_space surface_atom =
    case bridge_import_surface_atom_list_with_env env surface_space of
    | NONE => []
    | SOME space =>
        (case bridge_import_surface_atom_with_env env surface_atom of
         | NONE => []
         | SOME atom => bridge_eval_chain_fragment fuel space atom)
End

Theorem bridge_surface_eval_chain_fragment_wrapper_with_env_agrees_with_eval_m1_rec:
  ∀fuel env surface_space nested v templ space nested_atom templ_atom.
    bridge_import_surface_atom_list_with_env env surface_space =
      SOME space ∧
    bridge_import_surface_atom_with_env env nested = SOME nested_atom ∧
    bridge_import_surface_atom_with_env env templ = SOME templ_atom ⇒
    bridge_surface_eval_chain_fragment_wrapper_with_env fuel env surface_space
      (BExpr [BSym (strlit"chain"); nested; BVar v; templ]) =
      eval_m1_rec (SUC fuel) space
        (metta_m1$Expr
          [metta_m1$Sym 21; nested_atom; metta_m1$Var v; templ_atom])
Proof
  rw[bridge_surface_eval_chain_fragment_wrapper_with_env_def,
     bridge_import_surface_atom_with_env_def,
     bridge_import_symbol_with_env_def,
     bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  rw[bridge_eval_chain_fragment_agrees_with_eval_m1_rec]
QED

Theorem bridge_surface_eval_chain_fragment_wrapper_with_env_member_uses_subst_payload:
  ∀fuel env surface_space nested v templ space nested_atom templ_atom out.
    bridge_import_surface_atom_list_with_env env surface_space =
      SOME space ∧
    bridge_import_surface_atom_with_env env nested = SOME nested_atom ∧
    bridge_import_surface_atom_with_env env templ = SOME templ_atom ∧
    MEM out
      (bridge_surface_eval_chain_fragment_wrapper_with_env
        fuel env surface_space
        (BExpr [BSym (strlit"chain"); nested; BVar v; templ])) ⇒
    ∃substituted.
      MEM substituted
        (bridge_chain_subst_values v
          (eval_m1_rec fuel space nested_atom) templ_atom) ∧
      MEM out (eval_m1_rec fuel space substituted)
Proof
  rw[bridge_surface_eval_chain_fragment_wrapper_with_env_def,
     bridge_import_surface_atom_with_env_def,
     bridge_import_symbol_with_env_def,
     bridge_symbol_intern_def,
     bridge_symbol_table_def] \\
  gvs[AllCaseEqs()] \\
  drule bridge_eval_chain_fragment_member_uses_subst_payload \\
  rw[]
QED

Theorem bridge_surface_eval_eval_fragment_wrapper_with_env_dynamic_example:
  bridge_surface_eval_eval_fragment_wrapper_with_env 2
    [(strlit"Foo", 1000)] []
    (BExpr [BSym (strlit"eval");
            BExpr [BSym (strlit"+"); BInt 2; BInt 3]]) =
  [metta_m1$IntLit 5]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_case_fragment_wrapper_with_env_dynamic_example:
  bridge_surface_eval_case_fragment_wrapper_with_env 1
    [(strlit"Foo", 1000)] []
    (BExpr
      [BSym (strlit"case"); BSym (strlit"Foo");
       BExpr [BExpr [BSym (strlit"Foo"); BInt 7]]]) =
  [metta_m1$IntLit 7]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_switch_fragment_wrapper_with_env_dynamic_example:
  bridge_surface_eval_switch_fragment_wrapper_with_env 1
    [(strlit"Foo", 1000)] []
    (BExpr
      [BSym (strlit"switch"); BSym (strlit"Foo");
       BExpr [BExpr [BSym (strlit"Foo"); BInt 7]]]) =
  [metta_m1$IntLit 7]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_let_star_fragment_wrapper_with_env_dynamic_example:
  bridge_surface_eval_let_star_fragment_wrapper_with_env 2
    [(strlit"Foo", 1000)] []
    (BExpr
      [BSym (strlit"let*");
       BExpr [BExpr [BVar 0; BSym (strlit"Foo")]];
       BVar 0]) =
  [metta_m1$Sym 1000]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_chain_fragment_wrapper_with_env_dynamic_example:
  bridge_surface_eval_chain_fragment_wrapper_with_env 1
    [(strlit"Foo", 1000)]
    [BExpr [BSym (strlit"Foo"); BSym (strlit"True")]]
    (BExpr
      [BSym (strlit"chain");
       BExpr
        [BSym (strlit"match"); BSym (strlit"&self");
         BExpr [BSym (strlit"Foo"); BVar 0];
         BVar 0];
       BVar 1;
       BExpr [BSym (strlit"return"); BVar 1]]) =
  [metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 8]]
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_eval_fragment_wrapper_with_env_negative_example:
  bridge_surface_eval_eval_fragment_wrapper_with_env 1 [] []
    (BExpr [BSym (strlit"not-a-core-symbol"); BInt 2]) =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_case_fragment_wrapper_with_env_negative_example:
  bridge_surface_eval_case_fragment_wrapper_with_env 1 [] []
    (BExpr
      [BSym (strlit"case"); BSym (strlit"Foo");
       BExpr [BExpr [BSym (strlit"Foo"); BInt 7]]]) =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_switch_fragment_wrapper_with_env_negative_example:
  bridge_surface_eval_switch_fragment_wrapper_with_env 1 [] []
    (BExpr
      [BSym (strlit"switch"); BSym (strlit"Foo");
       BExpr [BExpr [BSym (strlit"Foo"); BInt 7]]]) =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_let_star_fragment_wrapper_with_env_negative_example:
  bridge_surface_eval_let_star_fragment_wrapper_with_env 1 [] []
    (BExpr
      [BSym (strlit"let*");
       BExpr [BExpr [BVar 0; BSym (strlit"Foo")]];
       BVar 0]) =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_surface_eval_chain_fragment_wrapper_with_env_negative_example:
  bridge_surface_eval_chain_fragment_wrapper_with_env 1 [] []
    (BExpr
      [BSym (strlit"chain"); BSym (strlit"Foo"); BVar 0; BVar 0]) =
  []
Proof
  EVAL_TAC
QED

Theorem bridge_eval_add_fragment_fallback_example:
  bridge_eval_add_fragment fuel space (metta_m1$Sym 0) = [metta_m1$Sym 0]
Proof
  rw[bridge_eval_add_fragment_def]
QED

Theorem bridge_add_atom_result_matches_eval_add_fragment:
  ∀x y.
    bridge_add_atom_result x y =
    eval_add_fragment 1 []
      (metta_m1$Expr
        [metta_m1$Sym 11; metta_m1$IntLit x; metta_m1$IntLit y])
Proof
  EVAL_TAC \\ rw[]
QED

Theorem bridge_add_ground_atom_matches_eval_add_fragment:
  ∀x y.
    bridge_add_ground_atom
      (metta_m1$Expr
        [metta_m1$Sym 11; metta_m1$IntLit x; metta_m1$IntLit y]) =
    eval_add_fragment 1 []
      (metta_m1$Expr
        [metta_m1$Sym 11; metta_m1$IntLit x; metta_m1$IntLit y])
Proof
  EVAL_TAC \\ rw[]
QED

val bridge_symbol_table_v_thm = translate bridge_symbol_table_def;
val bridge_symbol_name_v_thm = translate bridge_symbol_name_def;
val bridge_symbol_intern_v_thm = translate bridge_symbol_intern_def;
val bridge_dyn_symbol_intern_v_thm =
  translate bridge_dyn_symbol_intern_def;
val bridge_dyn_symbol_name_v_thm =
  translate bridge_dyn_symbol_name_def;
val bridge_import_symbol_with_env_v_thm =
  translate bridge_import_symbol_with_env_def;
val bridge_export_symbol_with_env_v_thm =
  translate bridge_export_symbol_with_env_def;
val bridge_import_surface_atom_v_thm =
  translate bridge_import_surface_atom_def;
val bridge_import_surface_atom_with_env_v_thm =
  translate bridge_import_surface_atom_with_env_def;
val bridge_export_surface_atom_with_env_v_thm =
  translate bridge_export_surface_atom_with_env_def;
val bridge_source_char_is_space_v_thm =
  translate bridge_source_char_is_space_def;
val bridge_source_char_is_delim_v_thm =
  translate bridge_source_char_is_delim_def;
val bridge_source_digit_value_v_thm =
  translate bridge_source_digit_value_def;
val bridge_reverse_chars_acc_v_thm =
  translate bridge_reverse_chars_acc_def;
val bridge_reverse_chars_v_thm =
  translate bridge_reverse_chars_def;
val bridge_source_all_digits_v_thm =
  translate bridge_source_all_digits_def;
val bridge_source_nat_from_digits_acc_v_thm =
  translate bridge_source_nat_from_digits_acc_def;
val bridge_source_atom_from_word_chars_v_thm =
  translate bridge_source_atom_from_word_chars_def;
val bridge_source_skip_comment_v_thm =
  translate bridge_source_skip_comment_def;
val bridge_source_scan_string_v_thm =
  translate bridge_source_scan_string_def;
val bridge_source_scan_word_v_thm =
  translate bridge_source_scan_word_def;
val bridge_tokenize_source_chars_fuel_v_thm =
  translate bridge_tokenize_source_chars_fuel_def;
val bridge_tokenize_source_string_fuel_v_thm =
  translate bridge_tokenize_source_string_fuel_def;
val bridge_parse_atom_token_v_thm =
  translate bridge_parse_atom_token_def;
val bridge_parse_atom_token_result_v_thm =
  translate bridge_parse_atom_token_result_def;
val bridge_parse_atom_tokens_fuel_v_thm =
  translate bridge_parse_atom_tokens_fuel_def;
val bridge_import_parsed_atom_tokens_result_with_env_v_thm =
  translate bridge_import_parsed_atom_tokens_result_with_env_def;
val bridge_parse_source_atom_token_v_thm =
  translate bridge_parse_source_atom_token_def;
val bridge_parse_source_atom_tokens_fuel_v_thm =
  translate bridge_parse_source_atom_tokens_fuel_def;
val bridge_parse_proto_atom_token_v_thm =
  translate bridge_parse_proto_atom_token_def;
val bridge_parse_proto_atom_tokens_fuel_v_thm =
  translate bridge_parse_proto_atom_tokens_fuel_def;
val bridge_parse_command_tokens_fuel_v_thm =
  translate bridge_parse_command_tokens_fuel_def;
val bridge_parse_program_tokens_fuel_v_thm =
  translate bridge_parse_program_tokens_fuel_def;
val bridge_import_command_with_env_v_thm =
  translate bridge_import_command_with_env_def;
val bridge_import_command_list_with_env_v_thm =
  translate bridge_import_command_list_with_env_def;
val bridge_export_command_with_env_v_thm =
  translate bridge_export_command_with_env_def;
val bridge_export_command_list_with_env_v_thm =
  translate bridge_export_command_list_with_env_def;
val bridge_import_parsed_command_tokens_with_env_v_thm =
  translate bridge_import_parsed_command_tokens_with_env_def;
val bridge_import_parsed_command_tokens_result_with_env_v_thm =
  translate bridge_import_parsed_command_tokens_result_with_env_def;
val bridge_import_parsed_program_tokens_with_env_v_thm =
  translate bridge_import_parsed_program_tokens_with_env_def;
val bridge_import_parsed_program_tokens_result_with_env_v_thm =
  translate bridge_import_parsed_program_tokens_result_with_env_def;
val bridge_expected_result_atoms_v_thm =
  translate bridge_expected_result_atoms_def;
val lookup_named_space_v_thm = translate lookup_named_space_def;
val set_named_space_v_thm = translate set_named_space_def;
val bind_empty_named_space_v_thm =
  translate bind_empty_named_space_def;
val add_atom_to_named_space_v_thm =
  translate add_atom_to_named_space_def;
val bridge_error_atom_v_thm = translate error_atom_def;
val bridge_try_run_state_effect_v_thm =
  translate bridge_try_run_state_effect_def;
val bridge_run_program_state_prefix_v_thm =
  translate bridge_run_program_state_prefix_def;
val bridge_source_lookup_named_space_v_thm =
  translate bridge_source_lookup_named_space_def;
val bridge_source_set_named_space_v_thm =
  translate bridge_source_set_named_space_def;
val bridge_source_error_atom_v_thm =
  translate bridge_source_error_atom_def;
val bridge_source_try_run_state_effect_v_thm =
  translate bridge_source_try_run_state_effect_def;
val bridge_import_source_atom_with_env_v_thm =
  translate bridge_import_source_atom_with_env_def;
val bridge_import_source_command_with_env_v_thm =
  translate bridge_import_source_command_with_env_def;
val bridge_import_source_command_list_with_env_v_thm =
  translate bridge_import_source_command_list_with_env_def;
val bridge_parse_source_command_tokens_fuel_v_thm =
  translate bridge_parse_source_command_tokens_fuel_def;
val bridge_parse_source_program_tokens_fuel_v_thm =
  translate bridge_parse_source_program_tokens_fuel_def;
val bridge_parse_source_program_chars_fuel_v_thm =
  translate bridge_parse_source_program_chars_fuel_def;
val bridge_parse_source_program_string_fuel_v_thm =
  translate bridge_parse_source_program_string_fuel_def;
val bridge_parse_proto_command_tokens_fuel_v_thm =
  translate bridge_parse_proto_command_tokens_fuel_def;
val bridge_parse_proto_program_tokens_fuel_v_thm =
  translate bridge_parse_proto_program_tokens_fuel_def;
val bridge_parse_source_atom_tokens_bound_v_thm =
  translate bridge_parse_source_atom_tokens_bound_def;
val bridge_parse_source_command_tokens_bound_v_thm =
  translate bridge_parse_source_command_tokens_bound_def;
val bridge_parse_source_program_tokens_bound_v_thm =
  translate bridge_parse_source_program_tokens_bound_def;
val bridge_parse_proto_atom_tokens_bound_v_thm =
  translate bridge_parse_proto_atom_tokens_bound_def;
val bridge_parse_proto_command_tokens_bound_v_thm =
  translate bridge_parse_proto_command_tokens_bound_def;
val bridge_parse_proto_program_tokens_bound_v_thm =
  translate bridge_parse_proto_program_tokens_bound_def;
val bridge_parse_error_message_v_thm =
  translate bridge_parse_error_message_def;
val bridge_source_full_atom_parse_result_to_shipped_v_thm =
  translate bridge_source_full_atom_parse_result_to_shipped_def;
val bridge_source_command_parse_result_to_shipped_v_thm =
  translate bridge_source_command_parse_result_to_shipped_def;
val bridge_source_program_parse_result_to_shipped_v_thm =
  translate bridge_source_program_parse_result_to_shipped_def;
val bridge_proto_full_atom_parse_result_to_shipped_v_thm =
  translate bridge_proto_full_atom_parse_result_to_shipped_def;
val bridge_proto_command_parse_result_to_shipped_v_thm =
  translate bridge_proto_command_parse_result_to_shipped_def;
val bridge_proto_program_parse_result_to_shipped_v_thm =
  translate bridge_proto_program_parse_result_to_shipped_def;
val bridge_parse_source_atom_tokens_shipped_v_thm =
  translate bridge_parse_source_atom_tokens_shipped_def;
val bridge_parse_source_command_tokens_shipped_v_thm =
  translate bridge_parse_source_command_tokens_shipped_def;
val bridge_parse_source_program_tokens_shipped_v_thm =
  translate bridge_parse_source_program_tokens_shipped_def;
val bridge_parse_proto_atom_tokens_shipped_v_thm =
  translate bridge_parse_proto_atom_tokens_shipped_def;
val bridge_parse_proto_command_tokens_shipped_v_thm =
  translate bridge_parse_proto_command_tokens_shipped_def;
val bridge_parse_proto_program_tokens_shipped_v_thm =
  translate bridge_parse_proto_program_tokens_shipped_def;
val bridge_lex_error_message_v_thm =
  translate bridge_lex_error_message_def;
val bridge_parse_source_atom_string_shipped_v_thm =
  translate bridge_parse_source_atom_string_shipped_def;
val bridge_parse_source_command_string_shipped_v_thm =
  translate bridge_parse_source_command_string_shipped_def;
val bridge_parse_source_program_string_shipped_v_thm =
  translate bridge_parse_source_program_string_shipped_def;
val bridge_tokenize_source_string_bound_v_thm =
  translate bridge_tokenize_source_string_bound_def;
val bridge_parse_source_atom_string_shipped_bound_v_thm =
  translate bridge_parse_source_atom_string_shipped_bound_def;
val bridge_parse_source_command_string_shipped_bound_v_thm =
  translate bridge_parse_source_command_string_shipped_bound_def;
val bridge_parse_source_program_string_shipped_bound_v_thm =
  translate bridge_parse_source_program_string_shipped_bound_def;
val bridge_proto_is_return_head_v_thm =
  translate bridge_proto_is_return_head_def;
val bridge_proto_eval_return_items_factored_v_thm =
  translate bridge_proto_eval_return_items_factored_def;
val bridge_proto_eval_return_fragment_core_factored_v_thm =
  translate bridge_proto_eval_return_fragment_core_factored_def;
val bridge_proto_eval_return_fragment_core_v_thm =
  translate bridge_proto_eval_return_fragment_core_def;
val bridge_add_int_v_thm = translate bridge_add_int_def;
val bridge_add_atom_result_v_thm = translate bridge_add_atom_result_def;
val bridge_add_ground_atom_v_thm = translate bridge_add_ground_atom_def;
val bridge_bool_and_result_v_thm = translate bool_and_result_def;
val bridge_bool_or_result_v_thm = translate bool_or_result_def;
val bridge_bool_not_result_v_thm = translate bool_not_result_def;
val bridge_prepend_arg_v_thm = translate bridge_prepend_arg_def;
val bridge_combine_eval_args_v_thm = translate bridge_combine_eval_args_def;
val bridge_eval_args2_v_thm = translate bridge_eval_args2_def;
val bridge_eval_int_add_values_v_thm = translate bridge_eval_int_add_values_def;
val bridge_eval_add_values_fragment_v_thm =
  translate bridge_eval_add_values_fragment_def;
val bridge_surface_eval_add_values_wrapper_v_thm =
  translate bridge_surface_eval_add_values_wrapper_def;
val bridge_surface_eval_add_evaluated_args_wrapper_v_thm =
  translate bridge_surface_eval_add_evaluated_args_wrapper_def;
val bridge_surface_eval_add_values_wrapper_with_env_v_thm =
  translate bridge_surface_eval_add_values_wrapper_with_env_def;
val bridge_surface_eval_add_evaluated_args_wrapper_with_env_v_thm =
  translate bridge_surface_eval_add_evaluated_args_wrapper_with_env_def;
val bridge_eval_lt_values_v_thm = translate bridge_eval_lt_values_def;
val bridge_eval_lt_values_fragment_v_thm =
  translate bridge_eval_lt_values_fragment_def;
val bridge_eval_eq_values_v_thm = translate bridge_eval_eq_values_def;
val bridge_eval_eq_values_fragment_v_thm =
  translate bridge_eval_eq_values_fragment_def;
val bridge_eval_and_values_v_thm = translate bridge_eval_and_values_def;
val bridge_eval_and_values_fragment_v_thm =
  translate bridge_eval_and_values_fragment_def;
val bridge_eval_or_values_v_thm = translate bridge_eval_or_values_def;
val bridge_eval_or_values_fragment_v_thm =
  translate bridge_eval_or_values_fragment_def;
val bridge_eval_not_values_v_thm = translate bridge_eval_not_values_def;
val bridge_eval_not_values_fragment_v_thm =
  translate bridge_eval_not_values_fragment_def;
val bridge_surface_eval_lt_values_wrapper_v_thm =
  translate bridge_surface_eval_lt_values_wrapper_def;
val bridge_surface_eval_eq_values_wrapper_v_thm =
  translate bridge_surface_eval_eq_values_wrapper_def;
val bridge_surface_eval_and_values_wrapper_v_thm =
  translate bridge_surface_eval_and_values_wrapper_def;
val bridge_surface_eval_or_values_wrapper_v_thm =
  translate bridge_surface_eval_or_values_wrapper_def;
val bridge_surface_eval_not_values_wrapper_v_thm =
  translate bridge_surface_eval_not_values_wrapper_def;
val bridge_surface_eval_lt_values_wrapper_with_env_v_thm =
  translate bridge_surface_eval_lt_values_wrapper_with_env_def;
val bridge_surface_eval_eq_values_wrapper_with_env_v_thm =
  translate bridge_surface_eval_eq_values_wrapper_with_env_def;
val bridge_surface_eval_and_values_wrapper_with_env_v_thm =
  translate bridge_surface_eval_and_values_wrapper_with_env_def;
val bridge_surface_eval_or_values_wrapper_with_env_v_thm =
  translate bridge_surface_eval_or_values_wrapper_with_env_def;
val bridge_surface_eval_not_values_wrapper_with_env_v_thm =
  translate bridge_surface_eval_not_values_wrapper_with_env_def;
val eval_return_fragment_v_thm = translate eval_return_fragment_def;
val bridge_source_eval_return_fragment_core_v_thm =
  translate bridge_source_eval_return_fragment_core_def;
val bridge_lookup_bind_v_thm = translate bridge_lookup_bind_def;
val bridge_apply_subst_v_thm = translate bridge_apply_subst_def;
val bridge_bind_var_v_thm = translate bridge_bind_var_def;
val bridge_match_atom_v_thm = translate bridge_match_atom_def;
val branch_pair_v_thm = translate branch_pair_def;
val bridge_first_branch_payloads_v_thm =
  translate bridge_first_branch_payloads_def;
val bridge_branch_values_payloads_v_thm =
  translate bridge_branch_values_payloads_def;
val bridge_surface_switch_payloads_wrapper_v_thm =
  translate bridge_surface_switch_payloads_wrapper_def;
val bridge_surface_case_payloads_wrapper_v_thm =
  translate bridge_surface_case_payloads_wrapper_def;
val bridge_surface_switch_payloads_wrapper_with_env_v_thm =
  translate bridge_surface_switch_payloads_wrapper_with_env_def;
val bridge_surface_case_payloads_wrapper_with_env_v_thm =
  translate bridge_surface_case_payloads_wrapper_with_env_def;
val bridge_eval_payload_result_v_thm =
  translate bridge_eval_payload_result_def;
val default_types_v_thm = translate default_types_def;
val hol_declared_type_lookup_v_thm =
  translate hol_declared_type_lookup_def;
val hol_declared_or_default_type_lookup_v_thm =
  translate hol_declared_or_default_type_lookup_def;
val hol_type_matches_v_thm = translate hol_type_matches_def;
val hol_any_type_match_v_thm = translate hol_any_type_match_def;
val evalc_values_v_thm = translate evalc_values_def;
val bridge_evalc_checked_values_v_thm =
  translate bridge_evalc_checked_values_def;
val bridge_surface_eval_payload_result_wrapper_v_thm =
  translate bridge_surface_eval_payload_result_wrapper_def;
val bridge_surface_evalc_checked_values_wrapper_v_thm =
  translate bridge_surface_evalc_checked_values_wrapper_def;
val let_binding_pair_v_thm = translate let_binding_pair_def;
val bridge_subst_binding_pair_v_thm =
  translate bridge_subst_binding_pair_def;
val bridge_subst_binding_pairs_v_thm =
  translate bridge_subst_binding_pairs_def;
val bridge_let_star_step_payloads_v_thm =
  translate bridge_let_star_step_payloads_def;
val bridge_match_space_payload_v_thm =
  translate bridge_match_space_payload_def;
val bridge_eval_match_fragment_v_thm =
  translate bridge_eval_match_fragment_def;
val bridge_surface_eval_match_fragment_wrapper_v_thm =
  translate bridge_surface_eval_match_fragment_wrapper_def;
val bridge_surface_eval_match_fragment_wrapper_with_env_v_thm =
  translate bridge_surface_eval_match_fragment_wrapper_with_env_def;
val bridge_chain_concat_results_v_thm =
  translate bridge_chain_concat_results_def;
val bridge_chain_subst_values_v_thm =
  translate bridge_chain_subst_values_def;
val metta_m1_atom_type_def = fetch "-" "METTA_M1_ATOM_TYPE_def";
val bridge_proto_atom_type_def =
  fetch "-" "METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE_def";

Theorem bridge_symbol_table_v_certificate =
  bridge_symbol_table_v_thm
Theorem bridge_symbol_name_v_certificate =
  bridge_symbol_name_v_thm
Theorem bridge_symbol_intern_v_certificate =
  bridge_symbol_intern_v_thm
Theorem bridge_dyn_symbol_intern_v_certificate =
  bridge_dyn_symbol_intern_v_thm
Theorem bridge_dyn_symbol_name_v_certificate =
  bridge_dyn_symbol_name_v_thm
Theorem bridge_import_symbol_with_env_v_certificate =
  bridge_import_symbol_with_env_v_thm
Theorem bridge_export_symbol_with_env_v_certificate =
  bridge_export_symbol_with_env_v_thm
Theorem bridge_import_surface_atom_v_certificate =
  bridge_import_surface_atom_v_thm
Theorem bridge_import_surface_atom_with_env_v_certificate =
  bridge_import_surface_atom_with_env_v_thm
Theorem bridge_export_surface_atom_with_env_v_certificate =
  bridge_export_surface_atom_with_env_v_thm
Theorem bridge_source_char_is_space_v_certificate =
  bridge_source_char_is_space_v_thm
Theorem bridge_source_char_is_delim_v_certificate =
  bridge_source_char_is_delim_v_thm
Theorem bridge_source_digit_value_v_certificate =
  bridge_source_digit_value_v_thm
Theorem bridge_reverse_chars_acc_v_certificate =
  bridge_reverse_chars_acc_v_thm
Theorem bridge_reverse_chars_v_certificate =
  bridge_reverse_chars_v_thm
Theorem bridge_source_all_digits_v_certificate =
  bridge_source_all_digits_v_thm
Theorem bridge_source_nat_from_digits_acc_v_certificate =
  bridge_source_nat_from_digits_acc_v_thm
Theorem bridge_source_atom_from_word_chars_v_certificate =
  bridge_source_atom_from_word_chars_v_thm
Theorem bridge_source_skip_comment_v_certificate =
  bridge_source_skip_comment_v_thm
Theorem bridge_source_scan_string_v_certificate =
  bridge_source_scan_string_v_thm
Theorem bridge_source_scan_word_v_certificate =
  bridge_source_scan_word_v_thm
Theorem bridge_tokenize_source_chars_fuel_v_certificate =
  bridge_tokenize_source_chars_fuel_v_thm
Theorem bridge_tokenize_source_string_fuel_v_certificate =
  bridge_tokenize_source_string_fuel_v_thm
Theorem bridge_parse_atom_token_v_certificate =
  bridge_parse_atom_token_v_thm
Theorem bridge_parse_atom_token_result_v_certificate =
  bridge_parse_atom_token_result_v_thm
Theorem bridge_parse_atom_tokens_fuel_v_certificate =
  bridge_parse_atom_tokens_fuel_v_thm
Theorem bridge_import_parsed_atom_tokens_result_with_env_v_certificate =
  bridge_import_parsed_atom_tokens_result_with_env_v_thm
Theorem bridge_parse_source_atom_token_v_certificate =
  bridge_parse_source_atom_token_v_thm
Theorem bridge_parse_source_atom_tokens_fuel_v_certificate =
  bridge_parse_source_atom_tokens_fuel_v_thm
Theorem bridge_parse_proto_atom_token_v_certificate =
  bridge_parse_proto_atom_token_v_thm
Theorem bridge_parse_proto_atom_tokens_fuel_v_certificate =
  bridge_parse_proto_atom_tokens_fuel_v_thm
Theorem bridge_parse_command_tokens_fuel_v_certificate =
  bridge_parse_command_tokens_fuel_v_thm
Theorem bridge_parse_program_tokens_fuel_v_certificate =
  bridge_parse_program_tokens_fuel_v_thm
Theorem bridge_import_command_with_env_v_certificate =
  bridge_import_command_with_env_v_thm
Theorem bridge_import_command_list_with_env_v_certificate =
  bridge_import_command_list_with_env_v_thm
Theorem bridge_export_command_with_env_v_certificate =
  bridge_export_command_with_env_v_thm
Theorem bridge_export_command_list_with_env_v_certificate =
  bridge_export_command_list_with_env_v_thm
Theorem bridge_import_parsed_command_tokens_with_env_v_certificate =
  bridge_import_parsed_command_tokens_with_env_v_thm
Theorem bridge_import_parsed_command_tokens_result_with_env_v_certificate =
  bridge_import_parsed_command_tokens_result_with_env_v_thm
Theorem bridge_import_parsed_program_tokens_with_env_v_certificate =
  bridge_import_parsed_program_tokens_with_env_v_thm
Theorem bridge_import_parsed_program_tokens_result_with_env_v_certificate =
  bridge_import_parsed_program_tokens_result_with_env_v_thm
Theorem bridge_expected_result_atoms_v_certificate =
  bridge_expected_result_atoms_v_thm
Theorem lookup_named_space_v_certificate =
  lookup_named_space_v_thm
Theorem set_named_space_v_certificate =
  set_named_space_v_thm
Theorem bind_empty_named_space_v_certificate =
  bind_empty_named_space_v_thm
Theorem add_atom_to_named_space_v_certificate =
  add_atom_to_named_space_v_thm
Theorem bridge_try_run_state_effect_v_certificate =
  bridge_try_run_state_effect_v_thm
Theorem bridge_run_program_state_prefix_v_certificate =
  bridge_run_program_state_prefix_v_thm
Theorem bridge_source_try_run_state_effect_v_certificate =
  bridge_source_try_run_state_effect_v_thm
Theorem bridge_import_source_atom_with_env_v_certificate =
  bridge_import_source_atom_with_env_v_thm
Theorem bridge_import_source_command_with_env_v_certificate =
  bridge_import_source_command_with_env_v_thm
Theorem bridge_import_source_command_list_with_env_v_certificate =
  bridge_import_source_command_list_with_env_v_thm
Theorem bridge_parse_source_command_tokens_fuel_v_certificate =
  bridge_parse_source_command_tokens_fuel_v_thm
Theorem bridge_parse_source_program_tokens_fuel_v_certificate =
  bridge_parse_source_program_tokens_fuel_v_thm
Theorem bridge_parse_source_program_chars_fuel_v_certificate =
  bridge_parse_source_program_chars_fuel_v_thm
Theorem bridge_parse_source_program_string_fuel_v_certificate =
  bridge_parse_source_program_string_fuel_v_thm
Theorem bridge_parse_proto_command_tokens_fuel_v_certificate =
  bridge_parse_proto_command_tokens_fuel_v_thm
Theorem bridge_parse_proto_program_tokens_fuel_v_certificate =
  bridge_parse_proto_program_tokens_fuel_v_thm
Theorem bridge_parse_source_atom_tokens_bound_v_certificate =
  bridge_parse_source_atom_tokens_bound_v_thm
Theorem bridge_parse_source_command_tokens_bound_v_certificate =
  bridge_parse_source_command_tokens_bound_v_thm
Theorem bridge_parse_source_program_tokens_bound_v_certificate =
  bridge_parse_source_program_tokens_bound_v_thm
Theorem bridge_parse_proto_atom_tokens_bound_v_certificate =
  bridge_parse_proto_atom_tokens_bound_v_thm
Theorem bridge_parse_proto_command_tokens_bound_v_certificate =
  bridge_parse_proto_command_tokens_bound_v_thm
Theorem bridge_parse_proto_program_tokens_bound_v_certificate =
  bridge_parse_proto_program_tokens_bound_v_thm
Theorem bridge_parse_error_message_v_certificate =
  bridge_parse_error_message_v_thm
Theorem bridge_source_full_atom_parse_result_to_shipped_v_certificate =
  bridge_source_full_atom_parse_result_to_shipped_v_thm
Theorem bridge_source_command_parse_result_to_shipped_v_certificate =
  bridge_source_command_parse_result_to_shipped_v_thm
Theorem bridge_source_program_parse_result_to_shipped_v_certificate =
  bridge_source_program_parse_result_to_shipped_v_thm
Theorem bridge_proto_full_atom_parse_result_to_shipped_v_certificate =
  bridge_proto_full_atom_parse_result_to_shipped_v_thm
Theorem bridge_proto_command_parse_result_to_shipped_v_certificate =
  bridge_proto_command_parse_result_to_shipped_v_thm
Theorem bridge_proto_program_parse_result_to_shipped_v_certificate =
  bridge_proto_program_parse_result_to_shipped_v_thm
Theorem bridge_parse_source_atom_tokens_shipped_v_certificate =
  bridge_parse_source_atom_tokens_shipped_v_thm
Theorem bridge_parse_source_command_tokens_shipped_v_certificate =
  bridge_parse_source_command_tokens_shipped_v_thm
Theorem bridge_parse_source_program_tokens_shipped_v_certificate =
  bridge_parse_source_program_tokens_shipped_v_thm
Theorem bridge_parse_proto_atom_tokens_shipped_v_certificate =
  bridge_parse_proto_atom_tokens_shipped_v_thm
Theorem bridge_parse_proto_command_tokens_shipped_v_certificate =
  bridge_parse_proto_command_tokens_shipped_v_thm
Theorem bridge_parse_proto_program_tokens_shipped_v_certificate =
  bridge_parse_proto_program_tokens_shipped_v_thm
Theorem bridge_lex_error_message_v_certificate =
  bridge_lex_error_message_v_thm
Theorem bridge_parse_source_atom_string_shipped_v_certificate =
  bridge_parse_source_atom_string_shipped_v_thm
Theorem bridge_parse_source_command_string_shipped_v_certificate =
  bridge_parse_source_command_string_shipped_v_thm
Theorem bridge_parse_source_program_string_shipped_v_certificate =
  bridge_parse_source_program_string_shipped_v_thm
Theorem bridge_tokenize_source_string_bound_v_certificate =
  bridge_tokenize_source_string_bound_v_thm
Theorem bridge_parse_source_atom_string_shipped_bound_v_certificate =
  bridge_parse_source_atom_string_shipped_bound_v_thm
Theorem bridge_parse_source_command_string_shipped_bound_v_certificate =
  bridge_parse_source_command_string_shipped_bound_v_thm
Theorem bridge_parse_source_program_string_shipped_bound_v_certificate =
  bridge_parse_source_program_string_shipped_bound_v_thm
Theorem bridge_proto_is_return_head_v_certificate =
  bridge_proto_is_return_head_v_thm
Theorem bridge_proto_eval_return_items_factored_v_certificate =
  bridge_proto_eval_return_items_factored_v_thm
Theorem bridge_proto_eval_return_fragment_core_factored_v_certificate =
  bridge_proto_eval_return_fragment_core_factored_v_thm
Theorem bridge_proto_eval_return_fragment_core_v_certificate =
  bridge_proto_eval_return_fragment_core_v_thm
Theorem bridge_add_int_v_certificate = bridge_add_int_v_thm
Theorem bridge_add_atom_result_v_certificate = bridge_add_atom_result_v_thm
Theorem bridge_add_ground_atom_v_certificate = bridge_add_ground_atom_v_thm
Theorem bridge_eval_add_values_fragment_v_certificate =
  bridge_eval_add_values_fragment_v_thm
Theorem bridge_surface_eval_add_values_wrapper_v_certificate =
  bridge_surface_eval_add_values_wrapper_v_thm
Theorem bridge_surface_eval_add_evaluated_args_wrapper_v_certificate =
  bridge_surface_eval_add_evaluated_args_wrapper_v_thm
Theorem bridge_surface_eval_add_values_wrapper_with_env_v_certificate =
  bridge_surface_eval_add_values_wrapper_with_env_v_thm
Theorem bridge_surface_eval_add_evaluated_args_wrapper_with_env_v_certificate =
  bridge_surface_eval_add_evaluated_args_wrapper_with_env_v_thm
Theorem bridge_eval_lt_values_fragment_v_certificate =
  bridge_eval_lt_values_fragment_v_thm
Theorem bridge_eval_eq_values_fragment_v_certificate =
  bridge_eval_eq_values_fragment_v_thm
Theorem bridge_eval_and_values_fragment_v_certificate =
  bridge_eval_and_values_fragment_v_thm
Theorem bridge_eval_or_values_fragment_v_certificate =
  bridge_eval_or_values_fragment_v_thm
Theorem bridge_eval_not_values_fragment_v_certificate =
  bridge_eval_not_values_fragment_v_thm
Theorem bridge_surface_eval_lt_values_wrapper_v_certificate =
  bridge_surface_eval_lt_values_wrapper_v_thm
Theorem bridge_surface_eval_eq_values_wrapper_v_certificate =
  bridge_surface_eval_eq_values_wrapper_v_thm
Theorem bridge_surface_eval_and_values_wrapper_v_certificate =
  bridge_surface_eval_and_values_wrapper_v_thm
Theorem bridge_surface_eval_or_values_wrapper_v_certificate =
  bridge_surface_eval_or_values_wrapper_v_thm
Theorem bridge_surface_eval_not_values_wrapper_v_certificate =
  bridge_surface_eval_not_values_wrapper_v_thm
Theorem bridge_surface_eval_lt_values_wrapper_with_env_v_certificate =
  bridge_surface_eval_lt_values_wrapper_with_env_v_thm
Theorem bridge_surface_eval_eq_values_wrapper_with_env_v_certificate =
  bridge_surface_eval_eq_values_wrapper_with_env_v_thm
Theorem bridge_surface_eval_and_values_wrapper_with_env_v_certificate =
  bridge_surface_eval_and_values_wrapper_with_env_v_thm
Theorem bridge_surface_eval_or_values_wrapper_with_env_v_certificate =
  bridge_surface_eval_or_values_wrapper_with_env_v_thm
Theorem bridge_surface_eval_not_values_wrapper_with_env_v_certificate =
  bridge_surface_eval_not_values_wrapper_with_env_v_thm
Theorem eval_return_fragment_v_certificate =
  eval_return_fragment_v_thm
Theorem bridge_source_eval_return_fragment_core_v_certificate =
  bridge_source_eval_return_fragment_core_v_thm
Theorem bridge_lookup_bind_v_certificate =
  bridge_lookup_bind_v_thm
Theorem bridge_apply_subst_v_certificate =
  bridge_apply_subst_v_thm
Theorem bridge_bind_var_v_certificate =
  bridge_bind_var_v_thm
Theorem bridge_match_atom_v_certificate =
  bridge_match_atom_v_thm
Theorem branch_pair_v_certificate =
  branch_pair_v_thm
Theorem bridge_first_branch_payloads_v_certificate =
  bridge_first_branch_payloads_v_thm
Theorem bridge_branch_values_payloads_v_certificate =
  bridge_branch_values_payloads_v_thm
Theorem bridge_surface_switch_payloads_wrapper_v_certificate =
  bridge_surface_switch_payloads_wrapper_v_thm
Theorem bridge_surface_case_payloads_wrapper_v_certificate =
  bridge_surface_case_payloads_wrapper_v_thm
Theorem bridge_surface_switch_payloads_wrapper_with_env_v_certificate =
  bridge_surface_switch_payloads_wrapper_with_env_v_thm
Theorem bridge_surface_case_payloads_wrapper_with_env_v_certificate =
  bridge_surface_case_payloads_wrapper_with_env_v_thm
Theorem bridge_eval_payload_result_v_certificate =
  bridge_eval_payload_result_v_thm
Theorem evalc_values_v_certificate =
  evalc_values_v_thm
Theorem bridge_evalc_checked_values_v_certificate =
  bridge_evalc_checked_values_v_thm
Theorem bridge_surface_eval_payload_result_wrapper_v_certificate =
  bridge_surface_eval_payload_result_wrapper_v_thm
Theorem bridge_surface_evalc_checked_values_wrapper_v_certificate =
  bridge_surface_evalc_checked_values_wrapper_v_thm
Theorem let_binding_pair_v_certificate =
  let_binding_pair_v_thm
Theorem bridge_subst_binding_pair_v_certificate =
  bridge_subst_binding_pair_v_thm
Theorem bridge_subst_binding_pairs_v_certificate =
  bridge_subst_binding_pairs_v_thm
Theorem bridge_let_star_step_payloads_v_certificate =
  bridge_let_star_step_payloads_v_thm
Theorem bridge_match_space_payload_v_certificate =
  bridge_match_space_payload_v_thm
Theorem bridge_eval_match_fragment_v_certificate =
  bridge_eval_match_fragment_v_thm
Theorem bridge_surface_eval_match_fragment_wrapper_v_certificate =
  bridge_surface_eval_match_fragment_wrapper_v_thm
Theorem bridge_surface_eval_match_fragment_wrapper_with_env_v_certificate =
  bridge_surface_eval_match_fragment_wrapper_with_env_v_thm
Theorem bridge_chain_concat_results_v_certificate =
  bridge_chain_concat_results_v_thm
Theorem bridge_chain_subst_values_v_certificate =
  bridge_chain_subst_values_v_thm

val bridge_add_ground_atom_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_add_ground_atom_v_thm;
val bridge_tokenize_source_chars_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_tokenize_source_chars_fuel_v_thm;
val bridge_tokenize_source_string_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_tokenize_source_string_fuel_v_thm;
val bridge_parse_atom_token_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_parse_atom_token_v_thm;
val bridge_parse_atom_token_result_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_atom_token_result_v_thm;
val bridge_parse_atom_tokens_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    (CONJUNCT1 bridge_parse_atom_tokens_fuel_v_thm);
val bridge_import_parsed_atom_tokens_result_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_import_parsed_atom_tokens_result_with_env_v_thm;
val bridge_parse_source_atom_token_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_parse_source_atom_token_v_thm;
val bridge_parse_source_atom_tokens_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    (CONJUNCT1 bridge_parse_source_atom_tokens_fuel_v_thm);
val bridge_parse_proto_atom_token_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_parse_proto_atom_token_v_thm;
val bridge_parse_proto_atom_tokens_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    (CONJUNCT1 bridge_parse_proto_atom_tokens_fuel_v_thm);
val bridge_parse_command_tokens_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_command_tokens_fuel_v_thm;
val bridge_parse_program_tokens_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_program_tokens_fuel_v_thm;
val bridge_import_command_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_import_command_with_env_v_thm;
val bridge_import_command_list_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_import_command_list_with_env_v_thm;
val bridge_export_command_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_export_command_with_env_v_thm;
val bridge_export_command_list_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_export_command_list_with_env_v_thm;
val bridge_import_parsed_command_tokens_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_import_parsed_command_tokens_with_env_v_thm;
val bridge_import_parsed_command_tokens_result_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_import_parsed_command_tokens_result_with_env_v_thm;
val bridge_import_parsed_program_tokens_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_import_parsed_program_tokens_with_env_v_thm;
val bridge_import_parsed_program_tokens_result_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_import_parsed_program_tokens_result_with_env_v_thm;
val bridge_expected_result_atoms_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_expected_result_atoms_v_thm;
val lookup_named_space_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` lookup_named_space_v_thm;
val set_named_space_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` set_named_space_v_thm;
val bind_empty_named_space_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bind_empty_named_space_v_thm;
val add_atom_to_named_space_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` add_atom_to_named_space_v_thm;
val bridge_try_run_state_effect_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_try_run_state_effect_v_thm;
val bridge_run_program_state_prefix_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_run_program_state_prefix_v_thm;
val bridge_source_try_run_state_effect_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_source_try_run_state_effect_v_thm;
val bridge_import_source_atom_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    (CONJUNCT1 bridge_import_source_atom_with_env_v_thm);
val bridge_import_source_command_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_import_source_command_with_env_v_thm;
val bridge_import_source_command_list_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_import_source_command_list_with_env_v_thm;
val bridge_parse_source_command_tokens_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_command_tokens_fuel_v_thm;
val bridge_parse_source_program_tokens_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_program_tokens_fuel_v_thm;
val bridge_parse_source_program_chars_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_program_chars_fuel_v_thm;
val bridge_parse_source_program_string_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_program_string_fuel_v_thm;
val bridge_parse_proto_command_tokens_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_proto_command_tokens_fuel_v_thm;
val bridge_parse_proto_program_tokens_fuel_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_proto_program_tokens_fuel_v_thm;
val bridge_parse_source_atom_tokens_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_atom_tokens_bound_v_thm;
val bridge_parse_source_command_tokens_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_command_tokens_bound_v_thm;
val bridge_parse_source_program_tokens_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_program_tokens_bound_v_thm;
val bridge_parse_proto_atom_tokens_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_proto_atom_tokens_bound_v_thm;
val bridge_parse_proto_command_tokens_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_proto_command_tokens_bound_v_thm;
val bridge_parse_proto_program_tokens_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_proto_program_tokens_bound_v_thm;
val bridge_parse_source_atom_tokens_shipped_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_atom_tokens_shipped_v_thm;
val bridge_parse_source_command_tokens_shipped_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_command_tokens_shipped_v_thm;
val bridge_parse_source_program_tokens_shipped_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_program_tokens_shipped_v_thm;
val bridge_parse_proto_atom_tokens_shipped_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_proto_atom_tokens_shipped_v_thm;
val bridge_parse_proto_command_tokens_shipped_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_proto_command_tokens_shipped_v_thm;
val bridge_parse_proto_program_tokens_shipped_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_proto_program_tokens_shipped_v_thm;
val bridge_lex_error_message_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_lex_error_message_v_thm;
val bridge_parse_source_atom_string_shipped_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_atom_string_shipped_v_thm;
val bridge_parse_source_command_string_shipped_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_command_string_shipped_v_thm;
val bridge_parse_source_program_string_shipped_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_program_string_shipped_v_thm;
val bridge_tokenize_source_string_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_tokenize_source_string_bound_v_thm;
val bridge_parse_source_atom_string_shipped_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_atom_string_shipped_bound_v_thm;
val bridge_parse_source_command_string_shipped_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_command_string_shipped_bound_v_thm;
val bridge_parse_source_program_string_shipped_bound_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_parse_source_program_string_shipped_bound_v_thm;
val bridge_proto_is_return_head_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_proto_is_return_head_v_thm;
val bridge_proto_eval_return_items_factored_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_proto_eval_return_items_factored_v_thm;
val bridge_proto_eval_return_fragment_core_factored_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_proto_eval_return_fragment_core_factored_v_thm;
val bridge_proto_eval_return_fragment_core_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_proto_eval_return_fragment_core_v_thm;
val bridge_bool_not_result_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_bool_not_result_v_thm;
val bridge_eval_args2_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_eval_args2_v_thm;
val bridge_eval_int_add_values_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_eval_int_add_values_v_thm;
val bridge_eval_add_values_fragment_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_eval_add_values_fragment_v_thm;
val bridge_surface_eval_add_values_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_add_values_wrapper_v_thm;
val bridge_surface_eval_add_evaluated_args_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_add_evaluated_args_wrapper_v_thm;
val bridge_surface_eval_add_values_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_add_values_wrapper_with_env_v_thm;
val bridge_surface_eval_add_evaluated_args_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_add_evaluated_args_wrapper_with_env_v_thm;
val bridge_eval_lt_values_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_eval_lt_values_v_thm;
val bridge_eval_lt_values_fragment_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_eval_lt_values_fragment_v_thm;
val bridge_eval_eq_values_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_eval_eq_values_v_thm;
val bridge_eval_eq_values_fragment_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_eval_eq_values_fragment_v_thm;
val bridge_eval_and_values_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_eval_and_values_v_thm;
val bridge_eval_and_values_fragment_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_eval_and_values_fragment_v_thm;
val bridge_eval_or_values_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_eval_or_values_v_thm;
val bridge_eval_or_values_fragment_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_eval_or_values_fragment_v_thm;
val bridge_eval_not_values_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` bridge_eval_not_values_v_thm;
val bridge_eval_not_values_fragment_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_eval_not_values_fragment_v_thm;
val bridge_surface_eval_lt_values_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_lt_values_wrapper_v_thm;
val bridge_surface_eval_eq_values_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_eq_values_wrapper_v_thm;
val bridge_surface_eval_and_values_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_and_values_wrapper_v_thm;
val bridge_surface_eval_or_values_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_or_values_wrapper_v_thm;
val bridge_surface_eval_not_values_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_not_values_wrapper_v_thm;
val bridge_surface_eval_lt_values_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_lt_values_wrapper_with_env_v_thm;
val bridge_surface_eval_eq_values_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_eq_values_wrapper_with_env_v_thm;
val bridge_surface_eval_and_values_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_and_values_wrapper_with_env_v_thm;
val bridge_surface_eval_or_values_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_or_values_wrapper_with_env_v_thm;
val bridge_surface_eval_not_values_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_not_values_wrapper_with_env_v_thm;
val eval_return_fragment_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi`` eval_return_fragment_v_thm;
val bridge_source_eval_return_fragment_core_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_source_eval_return_fragment_core_v_thm;
val bridge_chain_subst_values_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_chain_subst_values_v_thm;
val bridge_first_branch_payloads_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_first_branch_payloads_v_thm;
val bridge_branch_values_payloads_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_branch_values_payloads_v_thm;
val bridge_surface_switch_payloads_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_switch_payloads_wrapper_v_thm;
val bridge_surface_case_payloads_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_case_payloads_wrapper_v_thm;
val bridge_surface_switch_payloads_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_switch_payloads_wrapper_with_env_v_thm;
val bridge_surface_case_payloads_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_case_payloads_wrapper_with_env_v_thm;
val bridge_eval_payload_result_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_eval_payload_result_v_thm;
val bridge_evalc_checked_values_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_evalc_checked_values_v_thm;
val bridge_surface_eval_payload_result_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_payload_result_wrapper_v_thm;
val bridge_surface_evalc_checked_values_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_evalc_checked_values_wrapper_v_thm;
val bridge_let_star_step_payloads_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_let_star_step_payloads_v_thm;
val bridge_match_space_payload_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_match_space_payload_v_thm;
val bridge_eval_match_fragment_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_eval_match_fragment_v_thm;
val bridge_surface_eval_match_fragment_wrapper_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_match_fragment_wrapper_v_thm;
val bridge_surface_eval_match_fragment_wrapper_with_env_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_surface_eval_match_fragment_wrapper_with_env_v_thm;
val bridge_chain_concat_results_v_app_spec =
  cfAppLib.app_of_Arrow_rule ``:'ffi``
    bridge_chain_concat_results_v_thm;

Theorem bridge_proto_eval_return_fragment_core_v_app_spec_certificate =
  bridge_proto_eval_return_fragment_core_v_app_spec
Theorem bridge_tokenize_source_chars_fuel_v_app_spec_certificate =
  bridge_tokenize_source_chars_fuel_v_app_spec
Theorem bridge_tokenize_source_string_fuel_v_app_spec_certificate =
  bridge_tokenize_source_string_fuel_v_app_spec
Theorem bridge_parse_atom_token_v_app_spec_certificate =
  bridge_parse_atom_token_v_app_spec
Theorem bridge_parse_atom_token_result_v_app_spec_certificate =
  bridge_parse_atom_token_result_v_app_spec
Theorem bridge_parse_atom_tokens_fuel_v_app_spec_certificate =
  bridge_parse_atom_tokens_fuel_v_app_spec
Theorem bridge_import_parsed_atom_tokens_result_with_env_v_app_spec_certificate =
  bridge_import_parsed_atom_tokens_result_with_env_v_app_spec
Theorem bridge_parse_source_atom_token_v_app_spec_certificate =
  bridge_parse_source_atom_token_v_app_spec
Theorem bridge_parse_source_atom_tokens_fuel_v_app_spec_certificate =
  bridge_parse_source_atom_tokens_fuel_v_app_spec
Theorem bridge_parse_proto_atom_token_v_app_spec_certificate =
  bridge_parse_proto_atom_token_v_app_spec
Theorem bridge_parse_proto_atom_tokens_fuel_v_app_spec_certificate =
  bridge_parse_proto_atom_tokens_fuel_v_app_spec
Theorem bridge_parse_command_tokens_fuel_v_app_spec_certificate =
  bridge_parse_command_tokens_fuel_v_app_spec
Theorem bridge_parse_program_tokens_fuel_v_app_spec_certificate =
  bridge_parse_program_tokens_fuel_v_app_spec
Theorem bridge_import_command_with_env_v_app_spec_certificate =
  bridge_import_command_with_env_v_app_spec
Theorem bridge_import_command_list_with_env_v_app_spec_certificate =
  bridge_import_command_list_with_env_v_app_spec
Theorem bridge_export_command_with_env_v_app_spec_certificate =
  bridge_export_command_with_env_v_app_spec
Theorem bridge_export_command_list_with_env_v_app_spec_certificate =
  bridge_export_command_list_with_env_v_app_spec
Theorem bridge_import_parsed_command_tokens_with_env_v_app_spec_certificate =
  bridge_import_parsed_command_tokens_with_env_v_app_spec
Theorem bridge_import_parsed_command_tokens_result_with_env_v_app_spec_certificate =
  bridge_import_parsed_command_tokens_result_with_env_v_app_spec
Theorem bridge_import_parsed_program_tokens_with_env_v_app_spec_certificate =
  bridge_import_parsed_program_tokens_with_env_v_app_spec
Theorem bridge_import_parsed_program_tokens_result_with_env_v_app_spec_certificate =
  bridge_import_parsed_program_tokens_result_with_env_v_app_spec
Theorem bridge_expected_result_atoms_v_app_spec_certificate =
  bridge_expected_result_atoms_v_app_spec
Theorem lookup_named_space_v_app_spec_certificate =
  lookup_named_space_v_app_spec
Theorem set_named_space_v_app_spec_certificate =
  set_named_space_v_app_spec
Theorem bind_empty_named_space_v_app_spec_certificate =
  bind_empty_named_space_v_app_spec
Theorem add_atom_to_named_space_v_app_spec_certificate =
  add_atom_to_named_space_v_app_spec
Theorem bridge_try_run_state_effect_v_app_spec_certificate =
  bridge_try_run_state_effect_v_app_spec
Theorem bridge_run_program_state_prefix_v_app_spec_certificate =
  bridge_run_program_state_prefix_v_app_spec
Theorem bridge_source_try_run_state_effect_v_app_spec_certificate =
  bridge_source_try_run_state_effect_v_app_spec
Theorem bridge_import_source_atom_with_env_v_app_spec_certificate =
  bridge_import_source_atom_with_env_v_app_spec
Theorem bridge_import_source_command_with_env_v_app_spec_certificate =
  bridge_import_source_command_with_env_v_app_spec
Theorem bridge_import_source_command_list_with_env_v_app_spec_certificate =
  bridge_import_source_command_list_with_env_v_app_spec
Theorem bridge_parse_source_command_tokens_fuel_v_app_spec_certificate =
  bridge_parse_source_command_tokens_fuel_v_app_spec
Theorem bridge_parse_source_program_tokens_fuel_v_app_spec_certificate =
  bridge_parse_source_program_tokens_fuel_v_app_spec
Theorem bridge_parse_source_program_chars_fuel_v_app_spec_certificate =
  bridge_parse_source_program_chars_fuel_v_app_spec
Theorem bridge_parse_source_program_string_fuel_v_app_spec_certificate =
  bridge_parse_source_program_string_fuel_v_app_spec
Theorem bridge_parse_proto_command_tokens_fuel_v_app_spec_certificate =
  bridge_parse_proto_command_tokens_fuel_v_app_spec
Theorem bridge_parse_proto_program_tokens_fuel_v_app_spec_certificate =
  bridge_parse_proto_program_tokens_fuel_v_app_spec
Theorem bridge_parse_source_atom_tokens_bound_v_app_spec_certificate =
  bridge_parse_source_atom_tokens_bound_v_app_spec
Theorem bridge_parse_source_command_tokens_bound_v_app_spec_certificate =
  bridge_parse_source_command_tokens_bound_v_app_spec
Theorem bridge_parse_source_program_tokens_bound_v_app_spec_certificate =
  bridge_parse_source_program_tokens_bound_v_app_spec
Theorem bridge_parse_proto_atom_tokens_bound_v_app_spec_certificate =
  bridge_parse_proto_atom_tokens_bound_v_app_spec
Theorem bridge_parse_proto_command_tokens_bound_v_app_spec_certificate =
  bridge_parse_proto_command_tokens_bound_v_app_spec
Theorem bridge_parse_proto_program_tokens_bound_v_app_spec_certificate =
  bridge_parse_proto_program_tokens_bound_v_app_spec
Theorem bridge_parse_source_atom_tokens_shipped_v_app_spec_certificate =
  bridge_parse_source_atom_tokens_shipped_v_app_spec
Theorem bridge_parse_source_command_tokens_shipped_v_app_spec_certificate =
  bridge_parse_source_command_tokens_shipped_v_app_spec
Theorem bridge_parse_source_program_tokens_shipped_v_app_spec_certificate =
  bridge_parse_source_program_tokens_shipped_v_app_spec
Theorem bridge_parse_proto_atom_tokens_shipped_v_app_spec_certificate =
  bridge_parse_proto_atom_tokens_shipped_v_app_spec
Theorem bridge_parse_proto_command_tokens_shipped_v_app_spec_certificate =
  bridge_parse_proto_command_tokens_shipped_v_app_spec
Theorem bridge_parse_proto_program_tokens_shipped_v_app_spec_certificate =
  bridge_parse_proto_program_tokens_shipped_v_app_spec
Theorem bridge_lex_error_message_v_app_spec_certificate =
  bridge_lex_error_message_v_app_spec
Theorem bridge_parse_source_atom_string_shipped_v_app_spec_certificate =
  bridge_parse_source_atom_string_shipped_v_app_spec
Theorem bridge_parse_source_command_string_shipped_v_app_spec_certificate =
  bridge_parse_source_command_string_shipped_v_app_spec
Theorem bridge_parse_source_program_string_shipped_v_app_spec_certificate =
  bridge_parse_source_program_string_shipped_v_app_spec
Theorem bridge_tokenize_source_string_bound_v_app_spec_certificate =
  bridge_tokenize_source_string_bound_v_app_spec
Theorem bridge_parse_source_atom_string_shipped_bound_v_app_spec_certificate =
  bridge_parse_source_atom_string_shipped_bound_v_app_spec
Theorem bridge_parse_source_command_string_shipped_bound_v_app_spec_certificate =
  bridge_parse_source_command_string_shipped_bound_v_app_spec
Theorem bridge_parse_source_program_string_shipped_bound_v_app_spec_certificate =
  bridge_parse_source_program_string_shipped_bound_v_app_spec
Theorem bridge_proto_is_return_head_v_app_spec_certificate =
  bridge_proto_is_return_head_v_app_spec
Theorem bridge_proto_eval_return_items_factored_v_app_spec_certificate =
  bridge_proto_eval_return_items_factored_v_app_spec
Theorem bridge_proto_eval_return_fragment_core_factored_v_app_spec_certificate =
  bridge_proto_eval_return_fragment_core_factored_v_app_spec
Theorem bridge_add_ground_atom_v_app_spec_certificate =
  bridge_add_ground_atom_v_app_spec
Theorem bridge_eval_add_values_fragment_v_app_spec_certificate =
  bridge_eval_add_values_fragment_v_app_spec
Theorem bridge_surface_eval_add_values_wrapper_v_app_spec_certificate =
  bridge_surface_eval_add_values_wrapper_v_app_spec
Theorem bridge_surface_eval_add_evaluated_args_wrapper_v_app_spec_certificate =
  bridge_surface_eval_add_evaluated_args_wrapper_v_app_spec
Theorem bridge_surface_eval_add_values_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_eval_add_values_wrapper_with_env_v_app_spec
Theorem bridge_surface_eval_add_evaluated_args_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_eval_add_evaluated_args_wrapper_with_env_v_app_spec
Theorem bridge_eval_lt_values_fragment_v_app_spec_certificate =
  bridge_eval_lt_values_fragment_v_app_spec
Theorem bridge_eval_eq_values_fragment_v_app_spec_certificate =
  bridge_eval_eq_values_fragment_v_app_spec
Theorem bridge_eval_and_values_fragment_v_app_spec_certificate =
  bridge_eval_and_values_fragment_v_app_spec
Theorem bridge_eval_or_values_fragment_v_app_spec_certificate =
  bridge_eval_or_values_fragment_v_app_spec
Theorem bridge_eval_not_values_fragment_v_app_spec_certificate =
  bridge_eval_not_values_fragment_v_app_spec
Theorem bridge_surface_eval_lt_values_wrapper_v_app_spec_certificate =
  bridge_surface_eval_lt_values_wrapper_v_app_spec
Theorem bridge_surface_eval_eq_values_wrapper_v_app_spec_certificate =
  bridge_surface_eval_eq_values_wrapper_v_app_spec
Theorem bridge_surface_eval_and_values_wrapper_v_app_spec_certificate =
  bridge_surface_eval_and_values_wrapper_v_app_spec
Theorem bridge_surface_eval_or_values_wrapper_v_app_spec_certificate =
  bridge_surface_eval_or_values_wrapper_v_app_spec
Theorem bridge_surface_eval_not_values_wrapper_v_app_spec_certificate =
  bridge_surface_eval_not_values_wrapper_v_app_spec
Theorem bridge_surface_eval_lt_values_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_eval_lt_values_wrapper_with_env_v_app_spec
Theorem bridge_surface_eval_eq_values_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_eval_eq_values_wrapper_with_env_v_app_spec
Theorem bridge_surface_eval_and_values_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_eval_and_values_wrapper_with_env_v_app_spec
Theorem bridge_surface_eval_or_values_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_eval_or_values_wrapper_with_env_v_app_spec
Theorem bridge_surface_eval_not_values_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_eval_not_values_wrapper_with_env_v_app_spec
Theorem eval_return_fragment_v_app_spec_certificate =
  eval_return_fragment_v_app_spec
Theorem bridge_source_eval_return_fragment_core_v_app_spec_certificate =
  bridge_source_eval_return_fragment_core_v_app_spec
Theorem bridge_chain_subst_values_v_app_spec_certificate =
  bridge_chain_subst_values_v_app_spec
Theorem bridge_first_branch_payloads_v_app_spec_certificate =
  bridge_first_branch_payloads_v_app_spec
Theorem bridge_branch_values_payloads_v_app_spec_certificate =
  bridge_branch_values_payloads_v_app_spec
Theorem bridge_surface_switch_payloads_wrapper_v_app_spec_certificate =
  bridge_surface_switch_payloads_wrapper_v_app_spec
Theorem bridge_surface_case_payloads_wrapper_v_app_spec_certificate =
  bridge_surface_case_payloads_wrapper_v_app_spec
Theorem bridge_surface_switch_payloads_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_switch_payloads_wrapper_with_env_v_app_spec
Theorem bridge_surface_case_payloads_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_case_payloads_wrapper_with_env_v_app_spec
Theorem bridge_eval_payload_result_v_app_spec_certificate =
  bridge_eval_payload_result_v_app_spec
Theorem bridge_evalc_checked_values_v_app_spec_certificate =
  bridge_evalc_checked_values_v_app_spec
Theorem bridge_surface_eval_payload_result_wrapper_v_app_spec_certificate =
  bridge_surface_eval_payload_result_wrapper_v_app_spec
Theorem bridge_surface_evalc_checked_values_wrapper_v_app_spec_certificate =
  bridge_surface_evalc_checked_values_wrapper_v_app_spec
Theorem bridge_let_star_step_payloads_v_app_spec_certificate =
  bridge_let_star_step_payloads_v_app_spec
Theorem bridge_match_space_payload_v_app_spec_certificate =
  bridge_match_space_payload_v_app_spec
Theorem bridge_eval_match_fragment_v_app_spec_certificate =
  bridge_eval_match_fragment_v_app_spec
Theorem bridge_surface_eval_match_fragment_wrapper_v_app_spec_certificate =
  bridge_surface_eval_match_fragment_wrapper_v_app_spec
Theorem bridge_surface_eval_match_fragment_wrapper_with_env_v_app_spec_certificate =
  bridge_surface_eval_match_fragment_wrapper_with_env_v_app_spec
Theorem bridge_chain_concat_results_v_app_spec_certificate =
  bridge_chain_concat_results_v_app_spec

val bridge_eval_match_fragment_prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_prog;

val _ =
  astToSexprLib.write_ast_to_file
    "../generated/bridge_eval_match_fragment.sexp"
    bridge_eval_match_fragment_prog;

Quote add_cakeml:
fun bridge_add_int_hand x y = x + y;
End

val bridge_hand_st = get_ml_prog_state ();

Theorem bridge_add_int_hand_spec:
  ∀ffi_p x y xv yv.
    INT x xv ∧ INT y yv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_add_int_hand" bridge_hand_st)
      [xv; yv] emp
      (POSTv v. &INT (bridge_add_int x y) v)
Proof
  rw[bridge_add_int_def] \\
  xcf "bridge_add_int_hand" bridge_hand_st \\
  xapp \\
  xsimpl
QED

Quote add_cakeml:
fun bridge_add_ground_atom_hand atom =
  bridge_add_ground_atom atom;
End

val bridge_atom_hand_st = get_ml_prog_state ();

Theorem bridge_add_ground_atom_hand_spec:
  ∀ffi_p atom atomv.
    METTA_M1_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_add_ground_atom_hand" bridge_atom_hand_st)
      [atomv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_add_ground_atom atom) v)
Proof
  rw[] \\
  xcf "bridge_add_ground_atom_hand" bridge_atom_hand_st \\
  xapp_spec bridge_add_ground_atom_v_app_spec \\
  xsimpl
QED

Quote add_cakeml:
fun bridge_eval_add_values_hand original xs ys =
  bridge_eval_int_add_values (bridge_eval_args2 xs ys) original;
End

val bridge_eval_add_values_hand_st = get_ml_prog_state ();

Theorem bridge_eval_add_values_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_eval_add_values_hand"
          bridge_eval_add_values_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_add_values_fragment original xs ys) v)
Proof
  rw[bridge_eval_add_values_fragment_def] \\
  xcf "bridge_eval_add_values_hand" bridge_eval_add_values_hand_st \\
  xlet `POSTv valsv.
          &LIST_TYPE METTA_M1_ATOM_TYPE (bridge_eval_args2 xs ys) valsv`
  >- (xapp_spec bridge_eval_args2_v_app_spec \\ xsimpl) \\
  xapp_spec bridge_eval_int_add_values_v_app_spec \\
  xsimpl
QED

Quote add_cakeml:
fun bridge_eval_lt_values_hand original xs ys =
  bridge_eval_lt_values (bridge_eval_args2 xs ys) original;

fun bridge_eval_eq_values_hand original xs ys =
  bridge_eval_eq_values (bridge_eval_args2 xs ys) original;

fun bridge_eval_and_values_hand original xs ys =
  bridge_eval_and_values (bridge_eval_args2 xs ys) original;

fun bridge_eval_or_values_hand original xs ys =
  bridge_eval_or_values (bridge_eval_args2 xs ys) original;

fun bridge_eval_not_values_hand original xs =
  bridge_eval_not_values xs original;
End

val bridge_eval_primitive_values_hand_st = get_ml_prog_state ();

Theorem bridge_eval_lt_values_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_eval_lt_values_hand"
          bridge_eval_primitive_values_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_lt_values_fragment original xs ys) v)
Proof
  rw[bridge_eval_lt_values_fragment_def] \\
  xcf "bridge_eval_lt_values_hand" bridge_eval_primitive_values_hand_st \\
  xlet `POSTv valsv.
          &LIST_TYPE METTA_M1_ATOM_TYPE (bridge_eval_args2 xs ys) valsv`
  >- (xapp_spec bridge_eval_args2_v_app_spec \\ xsimpl) \\
  xapp_spec bridge_eval_lt_values_v_app_spec \\
  xsimpl
QED

Theorem bridge_eval_eq_values_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_eval_eq_values_hand"
          bridge_eval_primitive_values_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_eq_values_fragment original xs ys) v)
Proof
  rw[bridge_eval_eq_values_fragment_def] \\
  xcf "bridge_eval_eq_values_hand" bridge_eval_primitive_values_hand_st \\
  xlet `POSTv valsv.
          &LIST_TYPE METTA_M1_ATOM_TYPE (bridge_eval_args2 xs ys) valsv`
  >- (xapp_spec bridge_eval_args2_v_app_spec \\ xsimpl) \\
  xapp_spec bridge_eval_eq_values_v_app_spec \\
  xsimpl
QED

Theorem bridge_eval_and_values_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_eval_and_values_hand"
          bridge_eval_primitive_values_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_and_values_fragment original xs ys) v)
Proof
  rw[bridge_eval_and_values_fragment_def] \\
  xcf "bridge_eval_and_values_hand" bridge_eval_primitive_values_hand_st \\
  xlet `POSTv valsv.
          &LIST_TYPE METTA_M1_ATOM_TYPE (bridge_eval_args2 xs ys) valsv`
  >- (xapp_spec bridge_eval_args2_v_app_spec \\ xsimpl) \\
  xapp_spec bridge_eval_and_values_v_app_spec \\
  xsimpl
QED

Theorem bridge_eval_or_values_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_eval_or_values_hand"
          bridge_eval_primitive_values_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_or_values_fragment original xs ys) v)
Proof
  rw[bridge_eval_or_values_fragment_def] \\
  xcf "bridge_eval_or_values_hand" bridge_eval_primitive_values_hand_st \\
  xlet `POSTv valsv.
          &LIST_TYPE METTA_M1_ATOM_TYPE (bridge_eval_args2 xs ys) valsv`
  >- (xapp_spec bridge_eval_args2_v_app_spec \\ xsimpl) \\
  xapp_spec bridge_eval_or_values_v_app_spec \\
  xsimpl
QED

Theorem bridge_eval_not_values_hand_spec:
  ∀ffi_p original originalv xs xsv.
    METTA_M1_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE xs xsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_eval_not_values_hand"
          bridge_eval_primitive_values_hand_st)
      [originalv; xsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_not_values_fragment original xs) v)
Proof
  rw[bridge_eval_not_values_fragment_def, bridge_eval_not_values_def] \\
  xcf "bridge_eval_not_values_hand" bridge_eval_primitive_values_hand_st \\
  xapp_spec bridge_eval_not_values_v_app_spec \\
  xsimpl
QED

Quote add_cakeml:
fun bridge_eval_return_fragment_hand atom =
  eval_return_fragment atom;

fun bridge_eval_match_fragment_hand space atom =
  bridge_eval_match_fragment space atom;

fun bridge_proto_eval_return_fragment_core_hand atom =
  bridge_proto_eval_return_fragment_core atom;

fun bridge_proto_is_return_head_factored_hand atom =
  case atom of
    Protosym s => s = "return"
  | _ => False;

fun bridge_proto_return_singleton_hand atom =
  [atom];

fun bridge_proto_return_value_hand value =
  [Protoexpr [Protosym "return", value]];

fun bridge_proto_eval_return_items_factored_hand original xs =
  case xs of
    [] => bridge_proto_return_singleton_hand original
  | head :: rest =>
      (case rest of
         [] => bridge_proto_return_singleton_hand original
       | value :: rest2 =>
           (case rest2 of
              [] =>
                if bridge_proto_is_return_head_factored_hand head then
                  bridge_proto_return_value_hand value
                else bridge_proto_return_singleton_hand original
            | _ => bridge_proto_return_singleton_hand original));

fun bridge_proto_eval_return_fragment_core_factored_body_hand atom =
  case atom of
    Protoexpr xs => bridge_proto_eval_return_items_factored_hand atom xs
  | _ => bridge_proto_return_singleton_hand atom;

fun bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand atom =
  case atom of
    Protosym s => s = "return"
  | _ => False;

fun bridge_proto_eval_return_fragment_core_items_shipped_hand original xs =
  case xs of
    [] => [original]
  | head :: rest =>
      (case rest of
         [] => [original]
       | value :: rest2 =>
           (case rest2 of
              [] =>
                if bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand
                     head then
                  [Protoexpr [Protosym "return", value]]
                else [original]
            | _ => [original]));

fun bridge_proto_eval_return_fragment_core_shipped_hand atom =
  case atom of
    Protoexpr xs =>
      bridge_proto_eval_return_fragment_core_items_shipped_hand atom xs
  | _ => [atom];

fun bridge_source_eval_return_fragment_core_hand atom =
  bridge_source_eval_return_fragment_core atom;

fun bridge_surface_eval_add_values_wrapper_hand original xs ys =
  bridge_surface_eval_add_values_wrapper original xs ys;

fun bridge_surface_eval_add_evaluated_args_wrapper_hand original xs ys =
  bridge_surface_eval_add_evaluated_args_wrapper original xs ys;

fun bridge_surface_eval_add_values_wrapper_with_env_hand env original xs ys =
  bridge_surface_eval_add_values_wrapper_with_env env original xs ys;

fun bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand
  env original xs ys =
  bridge_surface_eval_add_evaluated_args_wrapper_with_env env original xs ys;

fun bridge_surface_eval_lt_values_wrapper_hand original xs ys =
  bridge_surface_eval_lt_values_wrapper original xs ys;

fun bridge_surface_eval_eq_values_wrapper_hand original xs ys =
  bridge_surface_eval_eq_values_wrapper original xs ys;

fun bridge_surface_eval_and_values_wrapper_hand original xs ys =
  bridge_surface_eval_and_values_wrapper original xs ys;

fun bridge_surface_eval_or_values_wrapper_hand original xs ys =
  bridge_surface_eval_or_values_wrapper original xs ys;

fun bridge_surface_eval_not_values_wrapper_hand original xs =
  bridge_surface_eval_not_values_wrapper original xs;

fun bridge_surface_eval_lt_values_wrapper_with_env_hand env original xs ys =
  bridge_surface_eval_lt_values_wrapper_with_env env original xs ys;

fun bridge_surface_eval_eq_values_wrapper_with_env_hand env original xs ys =
  bridge_surface_eval_eq_values_wrapper_with_env env original xs ys;

fun bridge_surface_eval_and_values_wrapper_with_env_hand env original xs ys =
  bridge_surface_eval_and_values_wrapper_with_env env original xs ys;

fun bridge_surface_eval_or_values_wrapper_with_env_hand env original xs ys =
  bridge_surface_eval_or_values_wrapper_with_env env original xs ys;

fun bridge_surface_eval_not_values_wrapper_with_env_hand env original xs =
  bridge_surface_eval_not_values_wrapper_with_env env original xs;

fun bridge_surface_eval_match_fragment_wrapper_hand surface_space surface_atom =
  bridge_surface_eval_match_fragment_wrapper surface_space surface_atom;

fun bridge_surface_eval_match_fragment_wrapper_with_env_hand
  env surface_space surface_atom =
  bridge_surface_eval_match_fragment_wrapper_with_env
    env surface_space surface_atom;

fun bridge_surface_eval_payload_result_wrapper_hand body rs =
  bridge_surface_eval_payload_result_wrapper body rs;

fun bridge_surface_evalc_checked_values_wrapper_hand
  surface_space term expected vals =
  bridge_surface_evalc_checked_values_wrapper
    surface_space term expected vals;

fun bridge_surface_switch_payloads_wrapper_hand scrut branches =
  bridge_surface_switch_payloads_wrapper scrut branches;

fun bridge_surface_case_payloads_wrapper_hand values branches =
  bridge_surface_case_payloads_wrapper values branches;

fun bridge_surface_switch_payloads_wrapper_with_env_hand env scrut branches =
  bridge_surface_switch_payloads_wrapper_with_env env scrut branches;

fun bridge_surface_case_payloads_wrapper_with_env_hand env values branches =
  bridge_surface_case_payloads_wrapper_with_env env values branches;

fun bridge_parse_atom_token_hand toks =
  bridge_parse_atom_token toks;

fun bridge_parse_atom_token_result_hand toks =
  bridge_parse_atom_token_result toks;

fun bridge_parse_atom_tokens_fuel_hand fuel toks =
  bridge_parse_atom_tokens_fuel fuel toks;

fun bridge_import_parsed_atom_tokens_result_with_env_hand env fuel toks =
  bridge_import_parsed_atom_tokens_result_with_env env fuel toks;

fun bridge_parse_source_atom_token_hand toks =
  bridge_parse_source_atom_token toks;

fun bridge_parse_source_atom_tokens_fuel_hand fuel toks =
  bridge_parse_source_atom_tokens_fuel fuel toks;

fun bridge_parse_source_atom_tokens_bound_hand toks =
  bridge_parse_source_atom_tokens_bound toks;

fun bridge_parse_proto_atom_token_hand toks =
  bridge_parse_proto_atom_token toks;

fun bridge_parse_proto_atom_tokens_fuel_hand fuel toks =
  bridge_parse_proto_atom_tokens_fuel fuel toks;

fun bridge_parse_proto_atom_tokens_bound_hand toks =
  bridge_parse_proto_atom_tokens_bound toks;

fun bridge_parse_command_tokens_fuel_hand fuel toks =
  bridge_parse_command_tokens_fuel fuel toks;

fun bridge_parse_program_tokens_fuel_hand fuel toks =
  bridge_parse_program_tokens_fuel fuel toks;

fun bridge_import_parsed_command_tokens_with_env_hand env fuel toks =
  bridge_import_parsed_command_tokens_with_env env fuel toks;

fun bridge_import_parsed_command_tokens_result_with_env_hand env fuel toks =
  bridge_import_parsed_command_tokens_result_with_env env fuel toks;

fun bridge_import_parsed_program_tokens_with_env_hand env fuel toks =
  bridge_import_parsed_program_tokens_with_env env fuel toks;

fun bridge_import_parsed_program_tokens_result_with_env_hand env fuel toks =
  bridge_import_parsed_program_tokens_result_with_env env fuel toks;

fun bridge_import_source_atom_with_env_hand dyn_env var_env str_env atom =
  bridge_import_source_atom_with_env dyn_env var_env str_env atom;

fun bridge_import_source_command_with_env_hand dyn_env var_env str_env cmd =
  bridge_import_source_command_with_env dyn_env var_env str_env cmd;

fun bridge_import_source_command_list_with_env_hand
  dyn_env var_env str_env cmds =
  bridge_import_source_command_list_with_env dyn_env var_env str_env cmds;

fun bridge_try_run_state_effect_hand env self spaces atom =
  bridge_try_run_state_effect env self spaces atom;

fun bridge_run_program_state_prefix_hand env fuel self spaces cmds =
  bridge_run_program_state_prefix env fuel self spaces cmds;

fun bridge_source_try_run_state_effect_hand self spaces atom =
  bridge_source_try_run_state_effect self spaces atom;

fun bridge_export_command_with_env_hand env cmd =
  bridge_export_command_with_env env cmd;

fun bridge_export_command_list_with_env_hand env cmds =
  bridge_export_command_list_with_env env cmds;

fun bridge_parse_source_command_tokens_fuel_hand fuel toks =
  bridge_parse_source_command_tokens_fuel fuel toks;

fun bridge_parse_source_program_tokens_fuel_hand fuel toks =
  bridge_parse_source_program_tokens_fuel fuel toks;

fun bridge_parse_source_command_tokens_bound_hand toks =
  bridge_parse_source_command_tokens_bound toks;

fun bridge_parse_source_program_tokens_bound_hand toks =
  bridge_parse_source_program_tokens_bound toks;

fun bridge_parse_source_atom_tokens_shipped_hand toks =
  bridge_parse_source_atom_tokens_shipped toks;

fun bridge_parse_source_command_tokens_shipped_hand toks =
  bridge_parse_source_command_tokens_shipped toks;

fun bridge_parse_source_program_tokens_shipped_hand toks =
  bridge_parse_source_program_tokens_shipped toks;

fun bridge_parse_proto_command_tokens_fuel_hand fuel toks =
  bridge_parse_proto_command_tokens_fuel fuel toks;

fun bridge_parse_proto_program_tokens_fuel_hand fuel toks =
  bridge_parse_proto_program_tokens_fuel fuel toks;

fun bridge_parse_proto_command_tokens_bound_hand toks =
  bridge_parse_proto_command_tokens_bound toks;

fun bridge_parse_proto_program_tokens_bound_hand toks =
  bridge_parse_proto_program_tokens_bound toks;

fun bridge_parse_proto_atom_tokens_shipped_hand toks =
  bridge_parse_proto_atom_tokens_shipped toks;

fun bridge_parse_proto_command_tokens_shipped_hand toks =
  bridge_parse_proto_command_tokens_shipped toks;

fun bridge_parse_proto_program_tokens_shipped_hand toks =
  bridge_parse_proto_program_tokens_shipped toks;

fun bridge_tokenize_source_chars_fuel_hand fuel chars =
  bridge_tokenize_source_chars_fuel fuel chars;

fun bridge_tokenize_source_string_fuel_hand fuel text =
  bridge_tokenize_source_string_fuel fuel text;

fun bridge_parse_source_program_chars_fuel_hand lex_fuel parse_fuel chars =
  bridge_parse_source_program_chars_fuel lex_fuel parse_fuel chars;

fun bridge_parse_source_program_string_fuel_hand lex_fuel parse_fuel text =
  bridge_parse_source_program_string_fuel lex_fuel parse_fuel text;

fun bridge_parse_source_atom_string_shipped_hand lex_fuel text =
  bridge_parse_source_atom_string_shipped lex_fuel text;

fun bridge_parse_source_command_string_shipped_hand lex_fuel text =
  bridge_parse_source_command_string_shipped lex_fuel text;

fun bridge_parse_source_program_string_shipped_hand lex_fuel text =
  bridge_parse_source_program_string_shipped lex_fuel text;

fun bridge_tokenize_source_string_bound_hand text =
  bridge_tokenize_source_string_bound text;

fun bridge_parse_source_atom_string_shipped_bound_hand text =
  bridge_parse_source_atom_string_shipped_bound text;

fun bridge_parse_source_command_string_shipped_bound_hand text =
  bridge_parse_source_command_string_shipped_bound text;

fun bridge_parse_source_program_string_shipped_bound_hand text =
  bridge_parse_source_program_string_shipped_bound text;

fun bridge_surface_is_return_symbol_hand s =
  s = "return";
End

val bridge_eval_fragment_hand_st = get_ml_prog_state ();

Theorem bridge_eval_return_fragment_hand_spec:
  ∀ffi_p atom atomv.
    METTA_M1_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_eval_return_fragment_hand"
          bridge_eval_fragment_hand_st)
      [atomv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (eval_return_fragment atom) v)
Proof
  rw[] \\
  xcf "bridge_eval_return_fragment_hand" bridge_eval_fragment_hand_st \\
  xapp_spec eval_return_fragment_v_app_spec \\
  xsimpl
QED

Theorem bridge_eval_match_fragment_hand_spec:
  ∀ffi_p space spacev atom atomv.
    LIST_TYPE METTA_M1_ATOM_TYPE space spacev ∧
    METTA_M1_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_eval_match_fragment_hand"
          bridge_eval_fragment_hand_st)
      [spacev; atomv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_match_fragment space atom) v)
Proof
  rw[] \\
  xcf "bridge_eval_match_fragment_hand" bridge_eval_fragment_hand_st \\
  xapp_spec bridge_eval_match_fragment_v_app_spec \\
  xsimpl
QED

Theorem bridge_proto_eval_return_fragment_core_hand_spec:
  ∀ffi_p atom atomv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_proto_eval_return_fragment_core_hand"
          bridge_eval_fragment_hand_st)
      [atomv] emp
      (POSTv v. &LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE
        (bridge_proto_eval_return_fragment_core atom) v)
Proof
  rw[] \\
  xcf "bridge_proto_eval_return_fragment_core_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_proto_eval_return_fragment_core_v_app_spec \\
  xsimpl
QED

Theorem bridge_proto_is_return_head_factored_hand_spec:
  ∀ffi_p atom atomv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_proto_is_return_head_factored_hand"
          bridge_eval_fragment_hand_st)
      [atomv] emp
      (POSTv v. &BOOL (bridge_proto_is_return_head atom) v)
Proof
  rw[] \\
  Cases_on ‘atom’ \\
  gvs[bridge_proto_atom_type_def, bridge_proto_is_return_head_def]
  >- (
    xcf "bridge_proto_is_return_head_factored_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xapp
    >- (qexists_tac ‘STRING_TYPE’ \\
        rw[EqualityType_NUM_BOOL] \\
        EVAL_TAC) \\
    xsimpl)
  >- (
    xcf "bridge_proto_is_return_head_factored_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xcon \\
    xsimpl)
  >- (
    xcf "bridge_proto_is_return_head_factored_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xcon \\
    xsimpl)
  >- (
    xcf "bridge_proto_is_return_head_factored_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xcon \\
    xsimpl) \\
  xcf "bridge_proto_is_return_head_factored_hand"
    bridge_eval_fragment_hand_st \\
  xmatch \\
  xcon \\
  xsimpl
QED

Theorem bridge_proto_return_singleton_hand_spec:
  ∀ffi_p atom atomv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_proto_return_singleton_hand"
          bridge_eval_fragment_hand_st)
      [atomv] emp
      (POSTv v. &LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE
        [atom] v)
Proof
  rw[] \\
  xcf "bridge_proto_return_singleton_hand" bridge_eval_fragment_hand_st \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xcon \\
  gvs[LIST_TYPE_def] \\
  xsimpl
QED

Theorem bridge_proto_return_value_hand_spec:
  ∀ffi_p value valuev.
    METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE value valuev ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_proto_return_value_hand"
          bridge_eval_fragment_hand_st)
      [valuev] emp
      (POSTv v. &LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE
        [ProtoExpr [ProtoSym (strlit"return"); value]] v)
Proof
  rw[] \\
  xcf "bridge_proto_return_value_hand" bridge_eval_fragment_hand_st \\
  rpt (xlet_auto >- (xcon \\ xsimpl)) \\
  rpt (xcon >- xsimpl) \\
  xcon \\
  gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
  xsimpl
QED

Theorem bridge_proto_eval_return_items_factored_hand_spec:
  ∀ffi_p original originalv xs xsv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE xs xsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_proto_eval_return_items_factored_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE
        (bridge_proto_eval_return_items_factored original xs) v)
Proof
  rw[] \\
  Cases_on ‘xs’ \\
  gvs[LIST_TYPE_def, bridge_proto_eval_return_items_factored_def]
  >- (
    xcf "bridge_proto_eval_return_items_factored_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xapp \\
    gvs[LIST_TYPE_def] \\
    qexists_tac ‘emp’ \\
    qexists_tac ‘original’ \\
    xsimpl) \\
  rename1 ‘LIST_TYPE _ rest restv’ \\
  Cases_on ‘rest’ \\
  gvs[LIST_TYPE_def, bridge_proto_eval_return_items_factored_def]
  >- (
    xcf "bridge_proto_eval_return_items_factored_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xmatch \\
    xapp_spec bridge_proto_return_singleton_hand_spec \\
    gvs[LIST_TYPE_def] \\
    qexists_tac ‘emp’ \\
    qexists_tac ‘original’ \\
    xsimpl) \\
  rename1 ‘LIST_TYPE _ rest2 rest2v’ \\
  Cases_on ‘rest2’ \\
  gvs[LIST_TYPE_def, bridge_proto_eval_return_items_factored_def]
  >- (
    xcf "bridge_proto_eval_return_items_factored_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xmatch \\
    xmatch \\
    xlet ‘POSTv bv. &BOOL (bridge_proto_is_return_head h) bv’
    >- (
      xapp_spec bridge_proto_is_return_head_factored_hand_spec \\
      gvs[LIST_TYPE_def] \\
      qexists_tac ‘emp’ \\
      qexists_tac ‘h’ \\
      xsimpl) \\
    xif
    >- (
      xapp_spec bridge_proto_return_value_hand_spec \\
      gvs[LIST_TYPE_def] \\
      qexists_tac ‘emp’ \\
      asm_exists_tac \\
      xsimpl)
    >- (
      xapp_spec bridge_proto_return_singleton_hand_spec \\
      gvs[LIST_TYPE_def] \\
      qexists_tac ‘emp’ \\
      qexists_tac ‘original’ \\
      xsimpl)) \\
  xcf "bridge_proto_eval_return_items_factored_hand"
    bridge_eval_fragment_hand_st \\
  xmatch \\
  xmatch \\
  xmatch \\
  xapp_spec bridge_proto_return_singleton_hand_spec \\
  gvs[LIST_TYPE_def] \\
  qexists_tac ‘emp’ \\
  qexists_tac ‘original’ \\
  xsimpl
QED

Theorem bridge_proto_eval_return_fragment_core_factored_body_hand_spec:
  ∀ffi_p atom atomv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_proto_eval_return_fragment_core_factored_body_hand"
          bridge_eval_fragment_hand_st)
      [atomv] emp
      (POSTv v. &LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE
        (bridge_proto_eval_return_fragment_core atom) v)
Proof
  rw[GSYM bridge_proto_eval_return_fragment_core_factored_eq] \\
  Cases_on ‘atom’ \\
  gvs[bridge_proto_atom_type_def,
      bridge_proto_eval_return_fragment_core_factored_def]
  >- (
    xcf "bridge_proto_eval_return_fragment_core_factored_body_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xapp \\
    gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
    xsimpl)
  >- (
    xcf "bridge_proto_eval_return_fragment_core_factored_body_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xapp_spec bridge_proto_return_singleton_hand_spec \\
    gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
    xsimpl)
  >- (
    xcf "bridge_proto_eval_return_fragment_core_factored_body_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xapp_spec bridge_proto_return_singleton_hand_spec \\
    gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
    xsimpl)
  >- (
    xcf "bridge_proto_eval_return_fragment_core_factored_body_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xapp_spec bridge_proto_return_singleton_hand_spec \\
    gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
    xsimpl) \\
  xcf "bridge_proto_eval_return_fragment_core_factored_body_hand"
    bridge_eval_fragment_hand_st \\
  xmatch \\
  xapp_spec bridge_proto_eval_return_items_factored_hand_spec \\
  gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
  xsimpl
QED

Theorem bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand_spec:
  ∀ffi_p atom atomv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v
          "bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand"
          bridge_eval_fragment_hand_st)
      [atomv] emp
      (POSTv v.
        &BOOL
          (bridge_proto_eval_return_fragment_core_is_return_head_shipped
             atom) v)
Proof
  rw[] \\
  Cases_on ‘atom’ \\
  gvs[bridge_proto_atom_type_def,
      bridge_proto_eval_return_fragment_core_is_return_head_shipped_def]
  >- (
    xcf "bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xapp
    >- (qexists_tac ‘STRING_TYPE’ \\
        rw[EqualityType_NUM_BOOL] \\
        EVAL_TAC) \\
    xsimpl)
  >- (
    xcf "bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xcon \\
    xsimpl)
  >- (
    xcf "bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xcon \\
    xsimpl)
  >- (
    xcf "bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xcon \\
    xsimpl) \\
  xcf "bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xmatch \\
  xcon \\
  xsimpl
QED

Theorem bridge_proto_eval_return_fragment_core_items_shipped_hand_spec:
  ∀ffi_p original originalv xs xsv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE xs xsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_proto_eval_return_fragment_core_items_shipped_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv] emp
      (POSTv v. &LIST_TYPE
        METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE
        (bridge_proto_eval_return_fragment_core_items_shipped
          original xs) v)
Proof
  rw[] \\
  Cases_on ‘xs’ \\
  gvs[LIST_TYPE_def,
      bridge_proto_eval_return_fragment_core_items_shipped_def]
  >- (
    xcf "bridge_proto_eval_return_fragment_core_items_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xlet_auto >- (xcon \\ xsimpl) \\
    xcon \\
    gvs[LIST_TYPE_def] \\
    xsimpl) \\
  rename1 ‘LIST_TYPE _ rest restv’ \\
  Cases_on ‘rest’ \\
  gvs[LIST_TYPE_def,
      bridge_proto_eval_return_fragment_core_items_shipped_def]
  >- (
    xcf "bridge_proto_eval_return_fragment_core_items_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xmatch \\
    xlet_auto >- (xcon \\ xsimpl) \\
    xcon \\
    gvs[LIST_TYPE_def] \\
    xsimpl) \\
  rename1 ‘LIST_TYPE _ rest2 rest2v’ \\
  Cases_on ‘rest2’ \\
  gvs[LIST_TYPE_def,
      bridge_proto_eval_return_fragment_core_items_shipped_def]
  >- (
    xcf "bridge_proto_eval_return_fragment_core_items_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xmatch \\
    xmatch \\
    xlet ‘POSTv bv.
            &BOOL
              (bridge_proto_eval_return_fragment_core_is_return_head_shipped
                 h) bv’
    >- (
      xapp_spec
        bridge_proto_eval_return_fragment_core_is_return_head_shipped_hand_spec \\
      gvs[LIST_TYPE_def] \\
      qexists_tac ‘emp’ \\
      qexists_tac ‘h’ \\
      xsimpl) \\
    xif
    >- (
      rpt (xlet_auto >- (xcon \\ xsimpl)) \\
      rpt (xcon >- xsimpl) \\
      xcon \\
      gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
      xsimpl)
    >- (
      xlet_auto >- (xcon \\ xsimpl) \\
      xcon \\
      gvs[LIST_TYPE_def] \\
      xsimpl)) \\
  xcf "bridge_proto_eval_return_fragment_core_items_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xmatch \\
  xmatch \\
  xmatch \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xcon \\
  gvs[LIST_TYPE_def] \\
  xsimpl
QED

Theorem bridge_proto_eval_return_fragment_core_shipped_hand_spec:
  ∀ffi_p atom atomv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_proto_eval_return_fragment_core_shipped_hand"
          bridge_eval_fragment_hand_st)
      [atomv] emp
      (POSTv v. &LIST_TYPE
        METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE
        (bridge_proto_eval_return_fragment_core atom) v)
Proof
  rw[GSYM bridge_proto_eval_return_fragment_core_shipped_eq] \\
  Cases_on ‘atom’ \\
  gvs[bridge_proto_atom_type_def,
      bridge_proto_eval_return_fragment_core_shipped_def]
  >- (
    xcf "bridge_proto_eval_return_fragment_core_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xlet_auto >- (xcon \\ xsimpl) \\
    xcon \\
    gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
    xsimpl)
  >- (
    xcf "bridge_proto_eval_return_fragment_core_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xlet_auto >- (xcon \\ xsimpl) \\
    xcon \\
    gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
    xsimpl)
  >- (
    xcf "bridge_proto_eval_return_fragment_core_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xlet_auto >- (xcon \\ xsimpl) \\
    xcon \\
    gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
    xsimpl)
  >- (
    xcf "bridge_proto_eval_return_fragment_core_shipped_hand"
      bridge_eval_fragment_hand_st \\
    xmatch \\
    xlet_auto >- (xcon \\ xsimpl) \\
    xcon \\
    gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
    xsimpl) \\
  xcf "bridge_proto_eval_return_fragment_core_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xmatch \\
  xapp_spec
    bridge_proto_eval_return_fragment_core_items_shipped_hand_spec \\
  gvs[LIST_TYPE_def, bridge_proto_atom_type_def] \\
  xsimpl
QED

Theorem bridge_source_eval_return_fragment_core_hand_spec:
  ∀ffi_p atom atomv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_source_eval_return_fragment_core_hand"
          bridge_eval_fragment_hand_st)
      [atomv] emp
      (POSTv v. &LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_ATOM_TYPE
        (bridge_source_eval_return_fragment_core atom) v)
Proof
  rw[] \\
  xcf "bridge_source_eval_return_fragment_core_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_source_eval_return_fragment_core_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_add_values_wrapper_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_add_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_add_values_wrapper original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_add_values_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_add_values_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_add_evaluated_args_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_add_evaluated_args_wrapper original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_add_evaluated_args_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_add_evaluated_args_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_hand_rec_add_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_add_evaluated_args_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_add_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_add_evaluated_args_wrapper
      surface_original surface_xs surface_ys =
    rec_add_values original xs ys’
    by metis_tac[
      bridge_surface_eval_add_evaluated_args_wrapper_matches_rec_add_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_add_evaluated_args_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_add_values_wrapper_with_env_hand_spec:
  ∀ffi_p env envv original originalv xs xsv ys ysv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_add_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_add_values_wrapper_with_env
          env original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_add_values_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_add_values_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand_spec:
  ∀ffi_p env envv original originalv xs xsv ys ysv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_add_evaluated_args_wrapper_with_env
          env original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec
    bridge_surface_eval_add_evaluated_args_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand_rec_add_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_add_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_add_evaluated_args_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_add_values original xs ys’
    by metis_tac[
      bridge_surface_eval_add_evaluated_args_wrapper_with_env_matches_rec_add_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_hand_eval_add_fragment_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 11; a; b]) ∧
    bridge_import_surface_atom_list surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_add_evaluated_args_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_add_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 11; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_add_evaluated_args_wrapper
      surface_original surface_xs surface_ys =
    bridge_eval_add_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 11; a; b])’
    by rw[bridge_surface_eval_add_evaluated_args_wrapper_def,
          bridge_surface_eval_add_values_wrapper_def,
          bridge_eval_add_fragment_def,
          bridge_eval_add_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_add_evaluated_args_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand_eval_add_fragment_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 11; a; b]) ∧
    bridge_import_surface_atom_list_with_env env surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list_with_env env surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_add_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 11; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_add_evaluated_args_wrapper_with_env
      env surface_original surface_xs surface_ys =
    bridge_eval_add_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 11; a; b])’
    by rw[bridge_surface_eval_add_evaluated_args_wrapper_with_env_def,
          bridge_surface_eval_add_values_wrapper_with_env_def,
          bridge_eval_add_fragment_def,
          bridge_eval_add_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_add_evaluated_args_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_lt_values_wrapper_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_lt_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_lt_values_wrapper original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_lt_values_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_lt_values_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_lt_values_wrapper_hand_rec_lt_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_lt_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_lt_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_lt_values_wrapper
      surface_original surface_xs surface_ys =
    rec_lt_values original xs ys’
    by metis_tac[
      bridge_surface_eval_lt_values_wrapper_matches_rec_lt_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_lt_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_eq_values_wrapper_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_eq_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_eq_values_wrapper original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_eq_values_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_eq_values_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_eq_values_wrapper_hand_rec_eq_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_eq_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_eq_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_eq_values_wrapper
      surface_original surface_xs surface_ys =
    rec_eq_values original xs ys’
    by metis_tac[
      bridge_surface_eval_eq_values_wrapper_matches_rec_eq_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_eq_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_and_values_wrapper_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_and_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_and_values_wrapper original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_and_values_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_and_values_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_and_values_wrapper_hand_rec_and_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_and_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_and_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_and_values_wrapper
      surface_original surface_xs surface_ys =
    rec_and_values original xs ys’
    by metis_tac[
      bridge_surface_eval_and_values_wrapper_matches_rec_and_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_and_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_or_values_wrapper_hand_spec:
  ∀ffi_p original originalv xs xsv ys ysv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_or_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_or_values_wrapper original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_or_values_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_or_values_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_or_values_wrapper_hand_rec_or_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ∧
    bridge_import_surface_atom_list surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_or_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_or_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_or_values_wrapper
      surface_original surface_xs surface_ys =
    rec_or_values original xs ys’
    by metis_tac[
      bridge_surface_eval_or_values_wrapper_matches_rec_or_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_or_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_not_values_wrapper_hand_spec:
  ∀ffi_p original originalv xs xsv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_not_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_not_values_wrapper original xs) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_not_values_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_not_values_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_not_values_wrapper_hand_rec_not_spec:
  ∀ffi_p surface_original originalv surface_xs xsv original xs.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    bridge_import_surface_atom surface_original = SOME original ∧
    bridge_import_surface_atom_list surface_xs = SOME xs ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_not_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_not_values original xs) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_not_values_wrapper surface_original surface_xs =
    rec_not_values original xs’
    by metis_tac[
      bridge_surface_eval_not_values_wrapper_matches_rec_not_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_not_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_lt_values_wrapper_with_env_hand_spec:
  ∀ffi_p env envv original originalv xs xsv ys ysv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_lt_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_lt_values_wrapper_with_env
          env original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_lt_values_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_lt_values_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_lt_values_wrapper_with_env_hand_rec_lt_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_lt_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_lt_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_lt_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_lt_values original xs ys’
    by metis_tac[
      bridge_surface_eval_lt_values_wrapper_with_env_matches_rec_lt_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_lt_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_eq_values_wrapper_with_env_hand_spec:
  ∀ffi_p env envv original originalv xs xsv ys ysv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_eq_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_eq_values_wrapper_with_env
          env original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_eq_values_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_eq_values_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_eq_values_wrapper_with_env_hand_rec_eq_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_eq_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_eq_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_eq_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_eq_values original xs ys’
    by metis_tac[
      bridge_surface_eval_eq_values_wrapper_with_env_matches_rec_eq_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_eq_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_and_values_wrapper_with_env_hand_spec:
  ∀ffi_p env envv original originalv xs xsv ys ysv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_and_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_and_values_wrapper_with_env
          env original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_and_values_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_and_values_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_and_values_wrapper_with_env_hand_rec_and_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_and_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_and_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_and_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_and_values original xs ys’
    by metis_tac[
      bridge_surface_eval_and_values_wrapper_with_env_matches_rec_and_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_and_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_or_values_wrapper_with_env_hand_spec:
  ∀ffi_p env envv original originalv xs xsv ys ysv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE ys ysv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_or_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_or_values_wrapper_with_env
          env original xs ys) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_or_values_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_or_values_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_or_values_wrapper_with_env_hand_rec_or_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     original xs ys.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ∧
    bridge_import_surface_atom_list_with_env env surface_ys = SOME ys ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_or_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_or_values original xs ys) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_or_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    rec_or_values original xs ys’
    by metis_tac[
      bridge_surface_eval_or_values_wrapper_with_env_matches_rec_or_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_or_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_not_values_wrapper_with_env_hand_spec:
  ∀ffi_p env envv original originalv xs xsv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE xs xsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_not_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_not_values_wrapper_with_env
          env original xs) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_not_values_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_not_values_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_not_values_wrapper_with_env_hand_rec_not_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv original xs.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME original ∧
    bridge_import_surface_atom_list_with_env env surface_xs = SOME xs ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_not_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (rec_not_values original xs) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_not_values_wrapper_with_env
      env surface_original surface_xs =
    rec_not_values original xs’
    by metis_tac[
      bridge_surface_eval_not_values_wrapper_with_env_matches_rec_not_values] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_not_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_lt_values_wrapper_hand_eval_lt_fragment_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 12; a; b]) ∧
    bridge_import_surface_atom_list surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_lt_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_lt_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 12; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_lt_values_wrapper
      surface_original surface_xs surface_ys =
    bridge_eval_lt_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 12; a; b])’
    by rw[bridge_surface_eval_lt_values_wrapper_def,
          bridge_eval_lt_fragment_def,
          bridge_eval_lt_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_lt_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_eq_values_wrapper_hand_eval_eq_fragment_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 47; a; b]) ∧
    bridge_import_surface_atom_list surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_eq_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_eq_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 47; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_eq_values_wrapper
      surface_original surface_xs surface_ys =
    bridge_eval_eq_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 47; a; b])’
    by rw[bridge_surface_eval_eq_values_wrapper_def,
          bridge_eval_eq_fragment_def,
          bridge_eval_eq_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_eq_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_and_values_wrapper_hand_eval_and_fragment_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 31; a; b]) ∧
    bridge_import_surface_atom_list surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_and_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_and_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 31; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_and_values_wrapper
      surface_original surface_xs surface_ys =
    bridge_eval_and_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 31; a; b])’
    by rw[bridge_surface_eval_and_values_wrapper_def,
          bridge_eval_and_fragment_def,
          bridge_eval_and_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_and_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_or_values_wrapper_hand_eval_or_fragment_spec:
  ∀ffi_p surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 32; a; b]) ∧
    bridge_import_surface_atom_list surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_or_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_or_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 32; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_or_values_wrapper
      surface_original surface_xs surface_ys =
    bridge_eval_or_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 32; a; b])’
    by rw[bridge_surface_eval_or_values_wrapper_def,
          bridge_eval_or_fragment_def,
          bridge_eval_or_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_or_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_not_values_wrapper_hand_eval_not_fragment_spec:
  ∀ffi_p surface_original originalv surface_xs xsv fuel space a.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    bridge_import_surface_atom surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 33; a]) ∧
    bridge_import_surface_atom_list surface_xs =
      SOME (eval_m1_rec fuel space a) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_not_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [originalv; xsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_not_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 33; a])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_not_values_wrapper
      surface_original surface_xs =
    bridge_eval_not_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 33; a])’
    by rw[bridge_surface_eval_not_values_wrapper_def,
          bridge_eval_not_fragment_def,
          bridge_eval_not_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_not_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_lt_values_wrapper_with_env_hand_eval_lt_fragment_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 12; a; b]) ∧
    bridge_import_surface_atom_list_with_env env surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list_with_env env surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_lt_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_lt_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 12; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_lt_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    bridge_eval_lt_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 12; a; b])’
    by rw[bridge_surface_eval_lt_values_wrapper_with_env_def,
          bridge_eval_lt_fragment_def,
          bridge_eval_lt_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_lt_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_eq_values_wrapper_with_env_hand_eval_eq_fragment_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 47; a; b]) ∧
    bridge_import_surface_atom_list_with_env env surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list_with_env env surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_eq_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_eq_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 47; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_eq_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    bridge_eval_eq_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 47; a; b])’
    by rw[bridge_surface_eval_eq_values_wrapper_with_env_def,
          bridge_eval_eq_fragment_def,
          bridge_eval_eq_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_eq_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_and_values_wrapper_with_env_hand_eval_and_fragment_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 31; a; b]) ∧
    bridge_import_surface_atom_list_with_env env surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list_with_env env surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_and_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_and_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 31; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_and_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    bridge_eval_and_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 31; a; b])’
    by rw[bridge_surface_eval_and_values_wrapper_with_env_def,
          bridge_eval_and_fragment_def,
          bridge_eval_and_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_and_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_or_values_wrapper_with_env_hand_eval_or_fragment_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv surface_ys ysv
     fuel space a b.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_ys ysv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 32; a; b]) ∧
    bridge_import_surface_atom_list_with_env env surface_xs =
      SOME (eval_m1_rec fuel space a) ∧
    bridge_import_surface_atom_list_with_env env surface_ys =
      SOME (eval_m1_rec fuel space b) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_or_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv; ysv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_or_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 32; a; b])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_or_values_wrapper_with_env
      env surface_original surface_xs surface_ys =
    bridge_eval_or_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 32; a; b])’
    by rw[bridge_surface_eval_or_values_wrapper_with_env_def,
          bridge_eval_or_fragment_def,
          bridge_eval_or_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_or_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_not_values_wrapper_with_env_hand_eval_not_fragment_spec:
  ∀ffi_p env envv surface_original originalv surface_xs xsv fuel space a.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_original originalv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_xs xsv ∧
    bridge_import_surface_atom_with_env env surface_original =
      SOME (metta_m1$Expr [metta_m1$Sym 33; a]) ∧
    bridge_import_surface_atom_list_with_env env surface_xs =
      SOME (eval_m1_rec fuel space a) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_not_values_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; originalv; xsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_not_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 33; a])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_not_values_wrapper_with_env
      env surface_original surface_xs =
    bridge_eval_not_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 33; a])’
    by rw[bridge_surface_eval_not_values_wrapper_with_env_def,
          bridge_eval_not_fragment_def,
          bridge_eval_not_values_fragment_def] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_not_values_wrapper_with_env_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_match_fragment_wrapper_hand_spec:
  ∀ffi_p surface_space surface_spacev surface_atom surface_atomv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_space surface_spacev ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_atom surface_atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_match_fragment_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [surface_spacev; surface_atomv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_match_fragment_wrapper
          surface_space surface_atom) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_match_fragment_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_match_fragment_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_match_fragment_wrapper_with_env_hand_spec:
  ∀ffi_p env envv surface_space surface_spacev surface_atom surface_atomv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_space surface_spacev ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_atom surface_atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_match_fragment_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; surface_spacev; surface_atomv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_match_fragment_wrapper_with_env
          env surface_space surface_atom) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_match_fragment_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_match_fragment_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_payload_result_wrapper_hand_spec:
  ∀ffi_p body bodyv rs rsv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE body bodyv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE rs rsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_payload_result_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [bodyv; rsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_eval_payload_result_wrapper body rs) v)
Proof
  rw[] \\
  xcf "bridge_surface_eval_payload_result_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_eval_payload_result_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_evalc_checked_values_wrapper_hand_spec:
  ∀ffi_p surface_space spacev term termv expected expectedv vals valsv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_space spacev ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE term termv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE expected expectedv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE vals valsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_evalc_checked_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [spacev; termv; expectedv; valsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_evalc_checked_values_wrapper
          surface_space term expected vals) v)
Proof
  rw[] \\
  xcf "bridge_surface_evalc_checked_values_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_evalc_checked_values_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_eval_payload_result_wrapper_hand_eval_fragment_spec:
  ∀ffi_p surface_body bodyv surface_rs rsv fuel space body.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_body bodyv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_rs rsv ∧
    bridge_import_surface_atom surface_body = SOME body ∧
    bridge_import_surface_atom_list surface_rs =
      SOME (eval_m1_rec fuel space body) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_payload_result_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [bodyv; rsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_eval_eval_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 20; body])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_payload_result_wrapper surface_body surface_rs =
    bridge_eval_eval_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 20; body])’
    by metis_tac[bridge_surface_eval_payload_result_wrapper_eval_fragment] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_payload_result_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_eval_payload_result_wrapper_hand_eval_m1_rec_spec:
  ∀ffi_p surface_body bodyv surface_rs rsv fuel space body.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_body bodyv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_rs rsv ∧
    bridge_import_surface_atom surface_body = SOME body ∧
    bridge_import_surface_atom_list surface_rs =
      SOME (eval_m1_rec fuel space body) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_eval_payload_result_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [bodyv; rsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (eval_m1_rec (SUC fuel) space
          (metta_m1$Expr [metta_m1$Sym 20; body])) v)
Proof
  rw[] \\
  ‘bridge_surface_eval_payload_result_wrapper surface_body surface_rs =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 20; body])’
    by metis_tac[
      bridge_surface_eval_payload_result_wrapper_eval_fragment,
      bridge_eval_eval_fragment_agrees_with_eval_m1_rec] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_eval_payload_result_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_evalc_checked_values_wrapper_hand_evalc_fragment_spec:
  ∀ffi_p surface_space spacev surface_term termv
     surface_expected expectedv surface_vals valsv
     fuel space term expected.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_space spacev ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_term termv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_expected expectedv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_vals valsv ∧
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom surface_term = SOME term ∧
    bridge_import_surface_atom surface_expected = SOME expected ∧
    bridge_import_surface_atom_list surface_vals =
      SOME
        (if hol_typed_add_bad space term
         then [error_atom term (metta_m1$Sym 10)]
         else eval_m1_rec fuel space term) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_evalc_checked_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [spacev; termv; expectedv; valsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (eval_evalc_fragment fuel space
          (metta_m1$Expr [metta_m1$Sym 57; term; expected])) v)
Proof
  rw[] \\
  ‘bridge_surface_evalc_checked_values_wrapper
      surface_space surface_term surface_expected surface_vals =
    eval_evalc_fragment fuel space
      (metta_m1$Expr [metta_m1$Sym 57; term; expected])’
    by metis_tac[
      bridge_surface_evalc_checked_values_wrapper_evalc_fragment] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_evalc_checked_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_evalc_checked_values_wrapper_hand_eval_m1_rec_spec:
  ∀ffi_p surface_space spacev surface_term termv
     surface_expected expectedv surface_vals valsv
     fuel space term expected.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_space spacev ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_term termv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_expected expectedv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_vals valsv ∧
    bridge_import_surface_atom_list surface_space = SOME space ∧
    bridge_import_surface_atom surface_term = SOME term ∧
    bridge_import_surface_atom surface_expected = SOME expected ∧
    bridge_import_surface_atom_list surface_vals =
      SOME
        (if hol_typed_add_bad space term
         then [error_atom term (metta_m1$Sym 10)]
         else eval_m1_rec fuel space term) ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_evalc_checked_values_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [spacev; termv; expectedv; valsv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (eval_m1_rec (SUC fuel) space
          (metta_m1$Expr [metta_m1$Sym 57; term; expected])) v)
Proof
  rw[] \\
  ‘bridge_surface_evalc_checked_values_wrapper
      surface_space surface_term surface_expected surface_vals =
    eval_m1_rec (SUC fuel) space
      (metta_m1$Expr [metta_m1$Sym 57; term; expected])’
    by metis_tac[
      bridge_surface_evalc_checked_values_wrapper_evalc_fragment,
      eval_evalc_fragment_agrees_with_eval_m1_rec] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_evalc_checked_values_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_switch_payloads_wrapper_hand_spec:
  ∀ffi_p scrut scrutv branches branchesv.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE scrut scrutv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      branches branchesv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_switch_payloads_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [scrutv; branchesv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_switch_payloads_wrapper scrut branches) v)
Proof
  rw[] \\
  xcf "bridge_surface_switch_payloads_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_switch_payloads_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_case_payloads_wrapper_hand_spec:
  ∀ffi_p values valuesv branches branchesv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      values valuesv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      branches branchesv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_case_payloads_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [valuesv; branchesv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_case_payloads_wrapper values branches) v)
Proof
  rw[] \\
  xcf "bridge_surface_case_payloads_wrapper_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_case_payloads_wrapper_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_switch_payloads_wrapper_with_env_hand_spec:
  ∀ffi_p env envv scrut scrutv branches branchesv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE scrut scrutv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      branches branchesv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_switch_payloads_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; scrutv; branchesv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_switch_payloads_wrapper_with_env
          env scrut branches) v)
Proof
  rw[] \\
  xcf "bridge_surface_switch_payloads_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_switch_payloads_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_case_payloads_wrapper_with_env_hand_spec:
  ∀ffi_p env envv values valuesv branches branchesv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      values valuesv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      branches branchesv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_case_payloads_wrapper_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; valuesv; branchesv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_surface_case_payloads_wrapper_with_env
          env values branches) v)
Proof
  rw[] \\
  xcf "bridge_surface_case_payloads_wrapper_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_surface_case_payloads_wrapper_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_surface_switch_payloads_wrapper_hand_payload_spec:
  ∀ffi_p surface_scrut scrutv surface_branches branchesv scrut branches.
    METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_scrut scrutv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_branches branchesv ∧
    bridge_import_surface_atom surface_scrut = SOME scrut ∧
    bridge_import_surface_atom_list surface_branches = SOME branches ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_switch_payloads_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [scrutv; branchesv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_first_branch_payloads scrut branches) v)
Proof
  rw[] \\
  ‘bridge_surface_switch_payloads_wrapper
      surface_scrut surface_branches =
    bridge_first_branch_payloads scrut branches’
    by metis_tac[bridge_surface_switch_payloads_wrapper_import] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_switch_payloads_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_case_payloads_wrapper_hand_payload_spec:
  ∀ffi_p surface_values valuesv surface_branches branchesv values branches.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_values valuesv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
      surface_branches branchesv ∧
    bridge_import_surface_atom_list surface_values = SOME values ∧
    bridge_import_surface_atom_list surface_branches = SOME branches ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_case_payloads_wrapper_hand"
          bridge_eval_fragment_hand_st)
      [valuesv; branchesv] emp
      (POSTv v. &LIST_TYPE METTA_M1_ATOM_TYPE
        (bridge_branch_values_payloads values branches) v)
Proof
  rw[] \\
  ‘bridge_surface_case_payloads_wrapper
      surface_values surface_branches =
    bridge_branch_values_payloads values branches’
    by metis_tac[bridge_surface_case_payloads_wrapper_import] \\
  pop_assum (fn th => rw[GSYM th]) \\
  irule bridge_surface_case_payloads_wrapper_hand_spec \\
  rw[]
QED

Theorem bridge_surface_is_return_symbol_hand_spec:
  ∀ffi_p s sv.
    STRING_TYPE s sv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_surface_is_return_symbol_hand"
          bridge_eval_fragment_hand_st)
      [sv] emp
      (POSTv v. &BOOL (bridge_surface_is_return_symbol s) v)
Proof
  rw[bridge_surface_is_return_symbol_def] \\
  xcf "bridge_surface_is_return_symbol_hand" bridge_eval_fragment_hand_st \\
  xapp
  >- (qexists_tac ‘STRING_TYPE’ \\
      rw[EqualityType_NUM_BOOL] \\
      EVAL_TAC) \\
  xsimpl
QED

Theorem bridge_parse_atom_token_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_atom_token_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v. &OPTION_TYPE
        (PAIR_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SURFACE_ATOM_TYPE
          (LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE))
        (bridge_parse_atom_token toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_atom_token_hand" bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_atom_token_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_atom_token_result_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_atom_token_result_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_ATOM_TOKEN_PARSE_RESULT_TYPE
          (bridge_parse_atom_token_result toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_atom_token_result_hand" bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_atom_token_result_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_atom_tokens_fuel_hand_spec:
  ∀ffi_p fuel fuelv toks toksv.
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_atom_tokens_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_FULL_ATOM_PARSE_RESULT_TYPE
          (bridge_parse_atom_tokens_fuel fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_atom_tokens_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_atom_tokens_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_import_parsed_atom_tokens_result_with_env_hand_spec:
  ∀ffi_p env envv fuel fuelv toks toksv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_import_parsed_atom_tokens_result_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_IMPORTED_ATOM_PARSE_RESULT_TYPE
          (bridge_import_parsed_atom_tokens_result_with_env env fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_import_parsed_atom_tokens_result_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec
    bridge_import_parsed_atom_tokens_result_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_atom_token_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_atom_token_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v. &OPTION_TYPE
        (PAIR_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_ATOM_TYPE
          (LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE))
        (bridge_parse_source_atom_token toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_atom_token_hand" bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_atom_token_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_atom_tokens_fuel_hand_spec:
  ∀ffi_p fuel fuelv toks toksv.
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_atom_tokens_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_FULL_ATOM_PARSE_RESULT_TYPE
          (bridge_parse_source_atom_tokens_fuel fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_atom_tokens_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_atom_tokens_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_atom_tokens_bound_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_atom_tokens_bound_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_FULL_ATOM_PARSE_RESULT_TYPE
          (bridge_parse_source_atom_tokens_bound toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_atom_tokens_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_atom_tokens_bound_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_atom_token_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_atom_token_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v. &OPTION_TYPE
        (PAIR_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_ATOM_TYPE
          (LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE))
        (bridge_parse_proto_atom_token toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_atom_token_hand" bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_atom_token_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_atom_tokens_fuel_hand_spec:
  ∀ffi_p fuel fuelv toks toksv.
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_atom_tokens_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_FULL_ATOM_PARSE_RESULT_TYPE
          (bridge_parse_proto_atom_tokens_fuel fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_atom_tokens_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_atom_tokens_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_atom_tokens_bound_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_atom_tokens_bound_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_FULL_ATOM_PARSE_RESULT_TYPE
          (bridge_parse_proto_atom_tokens_bound toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_atom_tokens_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_atom_tokens_bound_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_atom_tokens_shipped_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_atom_tokens_shipped_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_SHIPPED_ATOM_PARSE_RESULT_TYPE
          (bridge_parse_source_atom_tokens_shipped toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_atom_tokens_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_atom_tokens_shipped_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_atom_tokens_shipped_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_atom_tokens_shipped_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_SHIPPED_ATOM_PARSE_RESULT_TYPE
          (bridge_parse_proto_atom_tokens_shipped toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_atom_tokens_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_atom_tokens_shipped_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_command_tokens_fuel_hand_spec:
  ∀ffi_p fuel fuelv toks toksv.
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_command_tokens_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_COMMAND_PARSE_RESULT_TYPE
          (bridge_parse_command_tokens_fuel fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_command_tokens_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_command_tokens_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_program_tokens_fuel_hand_spec:
  ∀ffi_p fuel fuelv toks toksv.
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_program_tokens_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROGRAM_PARSE_RESULT_TYPE
          (bridge_parse_program_tokens_fuel fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_program_tokens_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_program_tokens_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_import_parsed_command_tokens_with_env_hand_spec:
  ∀ffi_p env envv fuel fuelv toks toksv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_import_parsed_command_tokens_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; fuelv; toksv] emp
      (POSTv v. &OPTION_TYPE
        (PAIR_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_NUMERIC_COMMAND_TYPE
          (LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE))
        (bridge_import_parsed_command_tokens_with_env env fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_import_parsed_command_tokens_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_import_parsed_command_tokens_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_import_parsed_command_tokens_result_with_env_hand_spec:
  ∀ffi_p env envv fuel fuelv toks toksv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_import_parsed_command_tokens_result_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_IMPORTED_COMMAND_PARSE_RESULT_TYPE
          (bridge_import_parsed_command_tokens_result_with_env
             env fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_import_parsed_command_tokens_result_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec
    bridge_import_parsed_command_tokens_result_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_import_parsed_program_tokens_with_env_hand_spec:
  ∀ffi_p env envv fuel fuelv toks toksv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_import_parsed_program_tokens_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; fuelv; toksv] emp
      (POSTv v. &OPTION_TYPE
        (LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_NUMERIC_COMMAND_TYPE)
        (bridge_import_parsed_program_tokens_with_env env fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_import_parsed_program_tokens_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_import_parsed_program_tokens_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_import_parsed_program_tokens_result_with_env_hand_spec:
  ∀ffi_p env envv fuel fuelv toks toksv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_import_parsed_program_tokens_result_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_IMPORTED_PROGRAM_PARSE_RESULT_TYPE
          (bridge_import_parsed_program_tokens_result_with_env
             env fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_import_parsed_program_tokens_result_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec
    bridge_import_parsed_program_tokens_result_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_import_source_atom_with_env_hand_spec:
  ∀ffi_p dyn_env dyn_envv var_env var_envv str_env str_envv atom atomv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) dyn_env dyn_envv ∧
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) var_env var_envv ∧
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) str_env str_envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_import_source_atom_with_env_hand"
          bridge_eval_fragment_hand_st)
      [dyn_envv; var_envv; str_envv; atomv] emp
      (POSTv v. &OPTION_TYPE METTA_M1_ATOM_TYPE
        (bridge_import_source_atom_with_env dyn_env var_env str_env atom) v)
Proof
  rw[] \\
  xcf "bridge_import_source_atom_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_import_source_atom_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_import_source_command_with_env_hand_spec:
  ∀ffi_p dyn_env dyn_envv var_env var_envv str_env str_envv cmd cmdv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) dyn_env dyn_envv ∧
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) var_env var_envv ∧
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) str_env str_envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_COMMAND_TYPE cmd cmdv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_import_source_command_with_env_hand"
          bridge_eval_fragment_hand_st)
      [dyn_envv; var_envv; str_envv; cmdv] emp
      (POSTv v. &OPTION_TYPE
        METTA_M1_CAKE_BRIDGE_BRIDGE_NUMERIC_COMMAND_TYPE
        (bridge_import_source_command_with_env dyn_env var_env str_env cmd) v)
Proof
  rw[] \\
  xcf "bridge_import_source_command_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_import_source_command_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_import_source_command_list_with_env_hand_spec:
  ∀ffi_p dyn_env dyn_envv var_env var_envv str_env str_envv cmds cmdsv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) dyn_env dyn_envv ∧
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) var_env var_envv ∧
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) str_env str_envv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_COMMAND_TYPE cmds cmdsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_import_source_command_list_with_env_hand"
          bridge_eval_fragment_hand_st)
      [dyn_envv; var_envv; str_envv; cmdsv] emp
      (POSTv v. &OPTION_TYPE
        (LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_NUMERIC_COMMAND_TYPE)
        (bridge_import_source_command_list_with_env
           dyn_env var_env str_env cmds) v)
Proof
  rw[] \\
  xcf "bridge_import_source_command_list_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_import_source_command_list_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_try_run_state_effect_hand_spec:
  ∀ffi_p env envv self selfv spaces spacesv atom atomv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE self selfv ∧
    LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE METTA_M1_ATOM_TYPE)) spaces spacesv ∧
    METTA_M1_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_try_run_state_effect_hand"
          bridge_eval_fragment_hand_st)
      [envv; selfv; spacesv; atomv] emp
      (POSTv v. &OPTION_TYPE
        METTA_M1_CAKE_BRIDGE_BRIDGE_STATE_EFFECT_RESULT_TYPE
        (bridge_try_run_state_effect env self spaces atom) v)
Proof
  rw[] \\
  xcf "bridge_try_run_state_effect_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_try_run_state_effect_v_app_spec \\
  xsimpl
QED

Theorem bridge_run_program_state_prefix_hand_spec:
  ∀ffi_p env envv fuel fuelv self selfv spaces spacesv cmds cmdsv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_ATOM_TYPE self selfv ∧
    LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE METTA_M1_ATOM_TYPE)) spaces spacesv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_NUMERIC_COMMAND_TYPE cmds cmdsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_run_program_state_prefix_hand"
          bridge_eval_fragment_hand_st)
      [envv; fuelv; selfv; spacesv; cmdsv] emp
      (POSTv v. &OPTION_TYPE
        METTA_M1_CAKE_BRIDGE_BRIDGE_STATE_PROGRAM_RESULT_TYPE
        (bridge_run_program_state_prefix env fuel self spaces cmds) v)
Proof
  rw[] \\
  xcf "bridge_run_program_state_prefix_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_run_program_state_prefix_v_app_spec \\
  xsimpl \\
  qexists_tac ‘NUM’ \\
  xsimpl
QED

Theorem bridge_source_try_run_state_effect_hand_spec:
  ∀ffi_p self selfv spaces spacesv atom atomv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_ATOM_TYPE self selfv ∧
    LIST_TYPE
      (PAIR_TYPE STRING_TYPE
        (LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_ATOM_TYPE))
      spaces spacesv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_ATOM_TYPE atom atomv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_source_try_run_state_effect_hand"
          bridge_eval_fragment_hand_st)
      [selfv; spacesv; atomv] emp
      (POSTv v. &OPTION_TYPE
        METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_STATE_EFFECT_RESULT_TYPE
        (bridge_source_try_run_state_effect self spaces atom) v)
Proof
  rw[] \\
  xcf "bridge_source_try_run_state_effect_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_source_try_run_state_effect_v_app_spec \\
  xsimpl
QED

Theorem bridge_export_command_with_env_hand_spec:
  ∀ffi_p env envv cmd cmdv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    METTA_M1_CAKE_BRIDGE_BRIDGE_NUMERIC_COMMAND_TYPE cmd cmdv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_export_command_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; cmdv] emp
      (POSTv v. &OPTION_TYPE
        METTA_M1_CAKE_BRIDGE_BRIDGE_COMMAND_TYPE
        (bridge_export_command_with_env env cmd) v)
Proof
  rw[] \\
  xcf "bridge_export_command_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_export_command_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_export_command_list_with_env_hand_spec:
  ∀ffi_p env envv cmds cmdsv.
    LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) env envv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_NUMERIC_COMMAND_TYPE cmds cmdsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_export_command_list_with_env_hand"
          bridge_eval_fragment_hand_st)
      [envv; cmdsv] emp
      (POSTv v. &OPTION_TYPE
        (LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_COMMAND_TYPE)
        (bridge_export_command_list_with_env env cmds) v)
Proof
  rw[] \\
  xcf "bridge_export_command_list_with_env_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_export_command_list_with_env_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_command_tokens_fuel_hand_spec:
  ∀ffi_p fuel fuelv toks toksv.
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_command_tokens_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_COMMAND_PARSE_RESULT_TYPE
          (bridge_parse_source_command_tokens_fuel fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_command_tokens_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_command_tokens_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_program_tokens_fuel_hand_spec:
  ∀ffi_p fuel fuelv toks toksv.
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_program_tokens_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PROGRAM_PARSE_RESULT_TYPE
          (bridge_parse_source_program_tokens_fuel fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_program_tokens_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_program_tokens_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_command_tokens_bound_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_command_tokens_bound_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_COMMAND_PARSE_RESULT_TYPE
          (bridge_parse_source_command_tokens_bound toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_command_tokens_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_command_tokens_bound_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_program_tokens_bound_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_program_tokens_bound_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PROGRAM_PARSE_RESULT_TYPE
          (bridge_parse_source_program_tokens_bound toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_program_tokens_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_program_tokens_bound_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_command_tokens_shipped_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_command_tokens_shipped_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_SHIPPED_COMMAND_PARSE_RESULT_TYPE
          (bridge_parse_source_command_tokens_shipped toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_command_tokens_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_command_tokens_shipped_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_program_tokens_shipped_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_program_tokens_shipped_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_SHIPPED_PROGRAM_PARSE_RESULT_TYPE
          (bridge_parse_source_program_tokens_shipped toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_program_tokens_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_program_tokens_shipped_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_command_tokens_fuel_hand_spec:
  ∀ffi_p fuel fuelv toks toksv.
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_command_tokens_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_COMMAND_PARSE_RESULT_TYPE
          (bridge_parse_proto_command_tokens_fuel fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_command_tokens_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_command_tokens_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_program_tokens_fuel_hand_spec:
  ∀ffi_p fuel fuelv toks toksv.
    NUM fuel fuelv ∧
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_program_tokens_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_PROGRAM_PARSE_RESULT_TYPE
          (bridge_parse_proto_program_tokens_fuel fuel toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_program_tokens_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_program_tokens_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_command_tokens_bound_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_command_tokens_bound_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_COMMAND_PARSE_RESULT_TYPE
          (bridge_parse_proto_command_tokens_bound toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_command_tokens_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_command_tokens_bound_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_program_tokens_bound_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_program_tokens_bound_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_PROGRAM_PARSE_RESULT_TYPE
          (bridge_parse_proto_program_tokens_bound toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_program_tokens_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_program_tokens_bound_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_command_tokens_shipped_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_command_tokens_shipped_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_SHIPPED_COMMAND_PARSE_RESULT_TYPE
          (bridge_parse_proto_command_tokens_shipped toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_command_tokens_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_command_tokens_shipped_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_proto_program_tokens_shipped_hand_spec:
  ∀ffi_p toks toksv.
    LIST_TYPE METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_TOKEN_TYPE toks toksv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_proto_program_tokens_shipped_hand"
          bridge_eval_fragment_hand_st)
      [toksv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_PROTO_SHIPPED_PROGRAM_PARSE_RESULT_TYPE
          (bridge_parse_proto_program_tokens_shipped toks) v)
Proof
  rw[] \\
  xcf "bridge_parse_proto_program_tokens_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_proto_program_tokens_shipped_v_app_spec \\
  xsimpl
QED

Theorem bridge_tokenize_source_chars_fuel_hand_spec:
  ∀ffi_p fuel fuelv chars charsv.
    NUM fuel fuelv ∧
    LIST_TYPE CHAR chars charsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_tokenize_source_chars_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; charsv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_LEX_RESULT_TYPE
          (bridge_tokenize_source_chars_fuel fuel chars) v)
Proof
  rw[] \\
  xcf "bridge_tokenize_source_chars_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_tokenize_source_chars_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_tokenize_source_string_fuel_hand_spec:
  ∀ffi_p fuel fuelv text textv.
    NUM fuel fuelv ∧
    STRING_TYPE text textv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_tokenize_source_string_fuel_hand"
          bridge_eval_fragment_hand_st)
      [fuelv; textv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_LEX_RESULT_TYPE
          (bridge_tokenize_source_string_fuel fuel text) v)
Proof
  rw[] \\
  xcf "bridge_tokenize_source_string_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_tokenize_source_string_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_program_chars_fuel_hand_spec:
  ∀ffi_p lex_fuel lex_fuelv parse_fuel parse_fuelv chars charsv.
    NUM lex_fuel lex_fuelv ∧
    NUM parse_fuel parse_fuelv ∧
    LIST_TYPE CHAR chars charsv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_program_chars_fuel_hand"
          bridge_eval_fragment_hand_st)
      [lex_fuelv; parse_fuelv; charsv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PROGRAM_PARSE_RESULT_TYPE
          (bridge_parse_source_program_chars_fuel
             lex_fuel parse_fuel chars) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_program_chars_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_program_chars_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_program_string_fuel_hand_spec:
  ∀ffi_p lex_fuel lex_fuelv parse_fuel parse_fuelv text textv.
    NUM lex_fuel lex_fuelv ∧
    NUM parse_fuel parse_fuelv ∧
    STRING_TYPE text textv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_program_string_fuel_hand"
          bridge_eval_fragment_hand_st)
      [lex_fuelv; parse_fuelv; textv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PROGRAM_PARSE_RESULT_TYPE
          (bridge_parse_source_program_string_fuel
             lex_fuel parse_fuel text) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_program_string_fuel_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_program_string_fuel_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_atom_string_shipped_hand_spec:
  ∀ffi_p lex_fuel lex_fuelv text textv.
    NUM lex_fuel lex_fuelv ∧
    STRING_TYPE text textv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_atom_string_shipped_hand"
          bridge_eval_fragment_hand_st)
      [lex_fuelv; textv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PARSED_ATOM_RESULT_TYPE
          (bridge_parse_source_atom_string_shipped lex_fuel text) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_atom_string_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_atom_string_shipped_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_command_string_shipped_hand_spec:
  ∀ffi_p lex_fuel lex_fuelv text textv.
    NUM lex_fuel lex_fuelv ∧
    STRING_TYPE text textv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_command_string_shipped_hand"
          bridge_eval_fragment_hand_st)
      [lex_fuelv; textv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PARSED_COMMAND_RESULT_TYPE
          (bridge_parse_source_command_string_shipped lex_fuel text) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_command_string_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_command_string_shipped_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_program_string_shipped_hand_spec:
  ∀ffi_p lex_fuel lex_fuelv text textv.
    NUM lex_fuel lex_fuelv ∧
    STRING_TYPE text textv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_program_string_shipped_hand"
          bridge_eval_fragment_hand_st)
      [lex_fuelv; textv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PARSED_PROGRAM_RESULT_TYPE
          (bridge_parse_source_program_string_shipped lex_fuel text) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_program_string_shipped_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_program_string_shipped_v_app_spec \\
  xsimpl
QED

Theorem bridge_tokenize_source_string_bound_hand_spec:
  ∀ffi_p text textv.
    STRING_TYPE text textv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_tokenize_source_string_bound_hand"
          bridge_eval_fragment_hand_st)
      [textv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_LEX_RESULT_TYPE
          (bridge_tokenize_source_string_bound text) v)
Proof
  rw[] \\
  xcf "bridge_tokenize_source_string_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_tokenize_source_string_bound_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_atom_string_shipped_bound_hand_spec:
  ∀ffi_p text textv.
    STRING_TYPE text textv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_atom_string_shipped_bound_hand"
          bridge_eval_fragment_hand_st)
      [textv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PARSED_ATOM_RESULT_TYPE
          (bridge_parse_source_atom_string_shipped_bound text) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_atom_string_shipped_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_atom_string_shipped_bound_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_command_string_shipped_bound_hand_spec:
  ∀ffi_p text textv.
    STRING_TYPE text textv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_command_string_shipped_bound_hand"
          bridge_eval_fragment_hand_st)
      [textv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PARSED_COMMAND_RESULT_TYPE
          (bridge_parse_source_command_string_shipped_bound text) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_command_string_shipped_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_command_string_shipped_bound_v_app_spec \\
  xsimpl
QED

Theorem bridge_parse_source_program_string_shipped_bound_hand_spec:
  ∀ffi_p text textv.
    STRING_TYPE text textv ⇒
    app (ffi_p:'ffi ffi_proj)
      ^(fetch_v "bridge_parse_source_program_string_shipped_bound_hand"
          bridge_eval_fragment_hand_st)
      [textv] emp
      (POSTv v.
        &METTA_M1_CAKE_BRIDGE_BRIDGE_SOURCE_PARSED_PROGRAM_RESULT_TYPE
          (bridge_parse_source_program_string_shipped_bound text) v)
Proof
  rw[] \\
  xcf "bridge_parse_source_program_string_shipped_bound_hand"
    bridge_eval_fragment_hand_st \\
  xapp_spec bridge_parse_source_program_string_shipped_bound_v_app_spec \\
  xsimpl
QED
