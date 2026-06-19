use "sml/metta_m1.sml";

val capacity_failures = ref 0;

fun report_capacity name ok details =
  case ok of
    Yes => print ("PASS " ^ name ^ "\n")
  | No =>
      (capacity_failures := !capacity_failures + 1;
       print ("FAIL " ^ name ^ "\n");
       print ("  " ^ details ^ "\n"));

fun expect_bag name got expected =
  report_capacity name (same_bag got expected)
    ("got " ^ result_list_to_string got ^ ", expected " ^ result_list_to_string expected);

fun expect_atom name got expected =
  report_capacity name (atom_eq got expected)
    ("got " ^ atom_to_string got ^ ", expected " ^ atom_to_string expected);

fun call name args =
  Expr (Sym name :: args);

val A = Sym "A";
val B = Sym "B";
val C = Sym "C";
val T = Sym "T";
val Good = Sym "Good";
val Bad = Sym "Bad";
val Nat = Sym "Nat";
val TypeAtom = Sym "Type";
val AtomType = Sym "Atom";
val Number = Sym "Number";
val StateType = Sym "State";

fun parse_expect name text expected =
  case parse_atom_from_string text of
    ParsedAtom atom => expect_atom name atom expected
  | ParseAtomError msg => report_capacity name No msg;

fun get_metatype atom =
  case atom of
    Sym _ => Sym "Symbol"
  | Var _ => Sym "Variable"
  | Expr _ => Sym "Expression"
  | IntLit _ => Sym "Grounded"
  | StrLit _ => Sym "Grounded";

fun type_decl_atom atom typ =
  Expr [Sym ":", atom, typ];

fun type_lookup atom space =
  case space of
    [] =>
      (case atom of
         IntLit _ => [Number]
       | StrLit _ => [Sym "String"]
       | Sym _ => [Sym "%Undefined%"]
       | Var _ => [Sym "Variable"]
       | Expr _ => [Sym "Expression"])
  | Expr [Sym ":", a, typ] :: rest =>
      (case atom_eq atom a of
         Yes => typ :: type_lookup atom rest
       | No => type_lookup atom rest)
  | _ :: rest => type_lookup atom rest;

fun type_matches expected actual =
  if atom_eq expected actual = Yes then Yes
  else
    case (expected, actual) of
      (Sym "%Undefined%", _) => Yes
    | (_, Sym "%Undefined%") => Yes
    | (Sym "Atom", _) => Yes
    | (_, Sym "Atom") => Yes
    | _ => No;

fun any_type_match expected actuals =
  case actuals of
    [] => No
  | a :: rest =>
      (case type_matches expected a of
         Yes => Yes
       | No => any_type_match expected rest);

fun eval_hold_like space arg =
  case any_type_match AtomType (type_lookup arg space) of
    Yes => [arg]
  | No => eval_top 40 space arg;

fun eval_force_like space arg =
  eval_top 40 space arg;

datatype space_entry =
    SpaceEntry of string * atom list;

fun lookup_space name spaces =
  case spaces of
    [] => []
  | SpaceEntry (n, atoms) :: rest =>
      if name = n then atoms else lookup_space name rest;

fun put_space name atoms spaces =
  case spaces of
    [] => [SpaceEntry (name, atoms)]
  | SpaceEntry (n, old) :: rest =>
      if name = n then SpaceEntry (n, atoms) :: rest
      else SpaceEntry (n, old) :: put_space name atoms rest;

fun add_atom_space name atom spaces =
  put_space name (append_atom (lookup_space name spaces) atom) spaces;

fun remove_atom_space name atom spaces =
  put_space name (remove_one atom (lookup_space name spaces)) spaces;

fun match_named_space spaces name pattern templ =
  match_space_raw (lookup_space name spaces) pattern templ;

datatype state_entry =
    StateEntry of int * atom;

fun get_state sid store =
  case store of
    [] => Sym "MissingState"
  | StateEntry (i, value) :: rest =>
      if sid = i then value else get_state sid rest;

fun change_state sid value store =
  case store of
    [] => [StateEntry (sid, value)]
  | StateEntry (i, old) :: rest =>
      if sid = i then StateEntry (i, value) :: rest
      else StateEntry (i, old) :: change_state sid value rest;

datatype module_entry =
    ModuleEntry of string * atom list;

fun lookup_module name mods =
  case mods of
    [] => []
  | ModuleEntry (n, atoms) :: rest =>
      if name = n then atoms else lookup_module name rest;

fun import_module_once name mods self_space =
  append_list self_space (lookup_module name mods);

datatype cmp_mode =
    Ordered
  | Bag;

fun same_order xs ys =
  case (xs, ys) of
    ([], []) => Yes
  | (x :: xr, y :: yr) =>
      (case atom_eq x y of
         Yes => same_order xr yr
       | No => No)
  | _ => No;

fun compare_results mode got expected =
  case mode of
    Ordered => same_order got expected
  | Bag => same_bag got expected;

fun primitive_boundary_call name args =
  if name = "known-prim" then [Expr (Sym "known-prim-result" :: args)]
  else [Sym "NotReducible"];

fun default_types atom =
  case atom of
    IntLit _ => [Number]
  | StrLit _ => [Sym "String"]
  | Sym _ => [Sym "%Undefined%"]
  | Var _ => [Sym "Variable"]
  | Expr _ => [Sym "Expression"];

fun declared_type_lookup atom space =
  case space of
    [] => []
  | Expr [Sym ":", a, typ] :: rest =>
      (case atom_eq atom a of
         Yes => typ :: declared_type_lookup atom rest
       | No => declared_type_lookup atom rest)
  | _ :: rest => declared_type_lookup atom rest;

fun declared_or_default_type_lookup atom space =
  case declared_type_lookup atom space of
    [] => default_types atom
  | types => types;

datatype split_result =
    Split of atom list * atom
  | NoSplit;

fun split_last xs =
  case xs of
    [] => NoSplit
  | [x] => Split ([], x)
  | x :: rest =>
      (case split_last rest of
         Split (front, last) => Split (x :: front, last)
       | NoSplit => NoSplit);

fun type_of_atom space atom =
  case atom of
    Expr (head :: args) =>
      (case function_result_types space (declared_or_default_type_lookup head space) args of
         [] => [Sym "Expression"]
       | types => types)
  | _ => declared_or_default_type_lookup atom space

and function_result_types space head_types args =
  case head_types of
    [] => []
  | Expr (Sym "->" :: parts) :: rest =>
      (case split_last parts of
         Split (arg_types, result_type) =>
           (case all_arg_types_match space arg_types args of
              Yes => result_type :: function_result_types space rest args
            | No => bad_arg_type_atom :: function_result_types space rest args)
       | NoSplit => bad_arg_type_atom :: function_result_types space rest args)
  | _ :: rest => function_result_types space rest args

and all_arg_types_match space expected args =
  case (expected, args) of
    ([], []) => Yes
  | (typ :: typ_rest, arg :: arg_rest) =>
      (case any_type_match typ (type_of_atom space arg) of
         Yes => all_arg_types_match space typ_rest arg_rest
       | No => No)
  | _ => No;

fun has_bad_arg_type types =
  contains_atom bad_arg_type_atom types;

fun typed_eval_top space atom =
  case atom of
    Expr _ =>
      (case has_bad_arg_type (type_of_atom space atom) of
         Yes => [error_atom atom bad_arg_type_atom]
       | No => eval_top 40 space atom)
  | _ => eval_top 40 space atom;

fun evalc_values space original expected vals =
  case vals of
    [] => []
  | value :: rest =>
      (case any_type_match expected (type_of_atom space value) of
         Yes => value :: evalc_values space original expected rest
       | No => error_atom original bad_arg_type_atom ::
           evalc_values space original expected rest);

fun evalc_like space atom expected =
  case has_bad_arg_type (type_of_atom space atom) of
    Yes => [error_atom atom bad_arg_type_atom]
  | No => evalc_values space atom expected (eval_top 40 space atom);

fun dependent_vec_cons_type space elem tail =
  case type_of_atom space tail of
    Expr [Sym "Vec", elem_type, n] :: _ =>
      let
        val actual_elem_type =
          case type_of_atom space elem of
            [] => Sym "%Undefined%"
          | typ :: _ => typ
      in
        case type_matches elem_type actual_elem_type of
          Yes => Expr [Sym "Vec", elem_type, Expr [Sym "S", n]]
        | No => bad_arg_type_atom
      end
  | _ => bad_arg_type_atom;

fun eval_case_one fuel space value branches original =
  case branches of
    [] => []
  | Expr [pattern, body] :: rest =>
      (case match_atom pattern value [] of
         Match bs => eval_top fuel space (apply_subst bs body)
       | NoMatch => eval_case_one fuel space value rest original)
  | _ :: rest => eval_case_one fuel space value rest original;

fun eval_case_values fuel space vals branches original =
  case vals of
    [] => []
  | value :: rest =>
      append_list (eval_case_one fuel space value branches original)
        (eval_case_values fuel space rest branches original);

fun eval_case_like fuel space scrut branches original =
  eval_case_values fuel space (eval_top fuel space scrut) branches original;

fun eval_switch_one fuel space value branches original =
  case branches of
    [] => []
  | Expr [pattern, body] :: rest =>
      (case match_atom pattern value [] of
         Match bs => eval_top fuel space (apply_subst bs body)
       | NoMatch => eval_switch_one fuel space value rest original)
  | _ :: rest => eval_switch_one fuel space value rest original;

fun eval_switch_values fuel space vals branches original =
  case vals of
    [] => []
  | value :: rest =>
      append_list (eval_switch_one fuel space value branches original)
        (eval_switch_values fuel space rest branches original);

fun eval_switch_like fuel space scrut branches original =
  eval_switch_values fuel space (eval_top fuel space scrut) branches original;

fun subst_binding_pair v value pair =
  case pair of
    Expr [Var w, rhs] => Expr [Var w, apply_subst [Bind (v, value)] rhs]
  | other => other;

fun subst_binding_pairs v value pairs =
  case pairs of
    [] => []
  | pair :: rest =>
      subst_binding_pair v value pair :: subst_binding_pairs v value rest;

fun eval_let_star_like fuel space pairs body =
  case pairs of
    [] => eval_top fuel space body
  | Expr [Var v, value] :: rest =>
      eval_let_star_values fuel space v (eval_top fuel space value) rest body
  | _ :: _ => [error_atom (Expr (Sym "let*" :: pairs)) bad_arg_type_atom]

and eval_let_star_values fuel space v vals rest body =
  case vals of
    [] => []
  | value :: more =>
      append_list
        (eval_let_star_like fuel space
          (subst_binding_pairs v value rest)
          (apply_subst [Bind (v, value)] body))
        (eval_let_star_values fuel space v more rest body);

fun quote_like atom =
  [atom];

fun superpose_bind_like alternatives templ =
  case alternatives of
    [] => []
  | bs :: rest => apply_subst bs templ :: superpose_bind_like rest templ;

fun collapse_bind_like alternatives templ =
  [Expr (superpose_bind_like alternatives templ)];

val _ = parse_expect "parser-symbol" "A" A;
val _ = parse_expect "parser-variable" "$x" (Var "x");
val _ = parse_expect "parser-integer" "203" (IntLit 203);
val _ = parse_expect "parser-string" "\"hi\"" (StrLit "hi");
val _ = parse_expect "parser-expression" "(P A)" (call "P" [A]);
val _ = parse_expect "parser-nested-expression" "(P (Q A) $x)" (call "P" [call "Q" [A], Var "x"]);
val _ = parse_expect "parser-empty-expression" "()" (Expr []);
val _ = parse_expect "parser-comment-whitespace" "  ; skip this\n  (P A)  " (call "P" [A]);

val _ =
  report_capacity "parser-run-command"
    (case parse_command_from_string "!(P A)" of
       ParsedCommand (Run atom) => atom_eq atom (call "P" [A])
     | _ => No)
    "expected a Run command for !";

val _ =
  report_capacity "parser-program"
    (case parse_program_from_string "(P A)\n!(match &self (P $x) $x)" of
       ParsedProgram [Add _, Run _] => Yes
     | _ => No)
    "expected one Add and one Run command";

val _ =
  report_capacity "parser-negative-unclosed"
    (case parse_atom_from_string "(P A" of
       ParseAtomError _ => Yes
     | _ => No)
    "unterminated expression should be rejected";

val _ =
  expect_atom "metatype-expression"
    (get_metatype (call "P" [A]))
    (Sym "Expression");

val _ =
  (case run_program 40 []
      [Add (call "P" [A]),
       Add (call "P" [B]),
       Run (call "match" [Sym "&self", call "P" [Var "x"], Var "x"])] of
     (_, [got]) => expect_bag "runner-add-then-query" got [A, B]
   | _ => report_capacity "runner-add-then-query" No "unexpected runner output shape");

val typed_space =
  [type_decl_atom (Sym "Z") Nat,
   type_decl_atom (Sym "Nat") TypeAtom,
   type_decl_atom (Sym "hold") (Expr [Sym "->", AtomType, AtomType]),
   Expr [Sym "=", call "x" [], A]];

val _ =
  expect_bag "type-lookup-custom"
    (type_lookup (Sym "Z") typed_space)
    [Nat, Sym "%Undefined%"];

val _ =
  expect_bag "meta-type-hold-does-not-evaluate"
    (eval_hold_like typed_space (call "x" []))
    [call "x" []];

val _ =
  expect_bag "ordinary-force-evaluates"
    (eval_force_like typed_space (call "x" []))
    [A];

val spaces0 = [SpaceEntry ("self", []), SpaceEntry ("kb", [])];
val spaces1 = add_atom_space "kb" (call "P" [A]) spaces0;
val spaces2 = add_atom_space "self" (call "P" [B]) spaces1;
val spaces3 = remove_atom_space "self" (call "P" [B]) spaces2;

val _ =
  expect_bag "explicit-space-kb"
    (match_named_space spaces1 "kb" (call "P" [Var "x"]) (Var "x"))
    [A];

val _ =
  expect_bag "space-frame-self-unchanged"
    (match_named_space spaces1 "self" (call "P" [Var "x"]) (Var "x"))
    [];

val _ =
  expect_bag "remove-atom-space"
    (match_named_space spaces3 "self" (call "P" [Var "x"]) (Var "x"))
    [];

val states1 = change_state 0 (Sym "off") [];
val states2 = change_state 0 (Sym "on") states1;

val _ = expect_atom "state-get-initial" (get_state 0 states1) (Sym "off");
val _ = expect_atom "state-get-after-change" (get_state 0 states2) (Sym "on");

val modules =
  [ModuleEntry ("moduleA", [Expr [Sym "=", call "f" [Var "x"], call "+" [Var "x", IntLit 1]]])];
val imported_space = import_module_once "moduleA" modules [];

val _ =
  expect_bag "module-import-function"
    (eval_top 40 imported_space (call "f" [IntLit 2]))
    [IntLit 3];

val _ =
  report_capacity "oracle-ordered-detects-order"
    (case compare_results Ordered [A, B] [B, A] of Yes => No | No => Yes)
    "ordered comparison should reject swapped results";

val _ =
  report_capacity "oracle-bag-accepts-order"
    (compare_results Bag [A, B] [B, A])
    "bag comparison should accept swapped results";

val _ =
  expect_bag "primitive-boundary-known"
    (primitive_boundary_call "known-prim" [A])
    [call "known-prim-result" [A]];

val _ =
  expect_bag "primitive-boundary-unknown"
    (primitive_boundary_call "call-native" [A])
    [Sym "NotReducible"];

val typed_arith_space =
  [type_decl_atom Nat TypeAtom,
   type_decl_atom (Sym "Z") Nat,
   type_decl_atom (Sym "S") (Expr [Sym "->", Nat, Nat]),
   type_decl_atom (Sym "Add") (Expr [Sym "->", Nat, Nat, Nat]),
   Expr [Sym "=", call "Add" [Var "x", Sym "Z"], Var "x"]];

val _ =
  expect_bag "typed-call-good"
    (typed_eval_top typed_arith_space (call "Add" [Sym "Z", Sym "Z"]))
    [Sym "Z"];

val _ =
  expect_bag "typed-call-bad-arg"
    (typed_eval_top typed_arith_space (call "Add" [Sym "S", Sym "Z"]))
    [error_atom (call "Add" [Sym "S", Sym "Z"]) bad_arg_type_atom];

val _ =
  expect_bag "evalc-like-good"
    (evalc_like typed_arith_space (call "Add" [Sym "Z", Sym "Z"]) Nat)
    [Sym "Z"];

val _ =
  expect_bag "evalc-like-bad-result-type"
    (evalc_like typed_arith_space (call "Add" [Sym "Z", Sym "Z"]) (Sym "String"))
    [error_atom (call "Add" [Sym "Z", Sym "Z"]) bad_arg_type_atom];

val typed_vec_space =
  [type_decl_atom (Sym "Person") TypeAtom,
   type_decl_atom A (Sym "Person"),
   type_decl_atom (Sym "Nil") (Expr [Sym "Vec", Sym "Person", Sym "Z"])];

val _ =
  expect_atom "dependent-vec-cons-type"
    (dependent_vec_cons_type typed_vec_space A (Sym "Nil"))
    (Expr [Sym "Vec", Sym "Person", call "S" [Sym "Z"]]);

val _ =
  expect_bag "case-first-match"
    (eval_case_like 40 [] A
      [Expr [A, Good],
       Expr [Var "x", Bad]]
      (call "case" [A]))
    [Good];

val _ =
  expect_bag "switch-structural-match"
    (eval_switch_like 40 [] B
      [Expr [A, Bad],
       Expr [B, Good]]
      (call "switch" [B]))
    [Good];

val _ =
  expect_bag "switch-variable-pattern"
    (eval_switch_like 40 [] (call "Pair" [A, B])
      [Expr [call "Pair" [Var "x", Var "y"], call "Tagged" [Var "x", Var "y"]]]
      (call "switch" [call "Pair" [A, B]]))
    [call "Tagged" [A, B]];

val _ =
  expect_bag "switch-evaluates-scrutinee-capacity"
    (eval_switch_like 40 [Expr [Sym "=", call "choose-switch" [], A]]
      (call "choose-switch" [])
      [Expr [A, Bad],
       Expr [call "choose-switch" [], Good]]
      (call "switch" [call "choose-switch" []]))
    [Bad];

val _ =
  expect_bag "let-star-sequential"
    (eval_let_star_like 40 []
      [Expr [Var "x", IntLit 1],
       Expr [Var "y", call "+" [Var "x", IntLit 2]]]
      (call "+" [Var "y", IntLit 3]))
    [IntLit 6];

val _ =
  expect_bag "quote-noeval"
    (quote_like (call "x" []))
    [call "x" []];

val _ =
  expect_atom "quote-subst-skips-body"
    (apply_subst_noquote "quote" [Bind ("x", A)] (call "quote" [Var "x"]))
    (call "quote" [Var "x"]);

val _ =
  expect_atom "quote-subst-outside-body"
    (apply_subst_noquote "quote" [Bind ("x", A)]
      (call "Pair" [Var "x", call "quote" [Var "x"]]))
    (call "Pair" [A, call "quote" [Var "x"]]);

val _ =
  expect_atom "token-subst-splices-expression"
    (Expr (apply_token_subst [Bind ("x", Expr [A, B])] [Sym "P", Var "x", C]))
    (Expr [Sym "P", A, B, C]);

val _ =
  expect_atom "positional-subst-index-vars"
    (apply_pos_subst [A, B] (call "Pair" [Var "0", Var "1"]))
    (call "Pair" [A, B]);

val _ =
  expect_atom "deref-var-chain-two"
    (deref_var 2 [Bind ("x", Var "y"), Bind ("y", A)] "x")
    A;

val _ =
  expect_atom "deref-var-self-cycle-fuel"
    (deref_var 1 [Bind ("x", Var "x")] "x")
    (Var "x");

val _ =
  expect_bag "collapse-bind-superpose-bind"
    (collapse_bind_like [[Bind ("x", A)], [Bind ("x", B)]] (Var "x"))
    [Expr [A, B]];

val _ =
  if !capacity_failures = 0 then
    print "Capacity prototype tests passed\n"
  else
    (print ("Capacity prototype tests failed: " ^ Int.toString (!capacity_failures) ^ "\n");
     OS.Process.exit OS.Process.failure);
