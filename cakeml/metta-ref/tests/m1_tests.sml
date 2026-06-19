use "sml/metta_m1.sml";

val failures = ref 0;

fun report name ok got expected =
  case ok of
    Yes => print ("PASS " ^ name ^ "\n")
  | No =>
      (failures := !failures + 1;
       print ("FAIL " ^ name ^ "\n");
       print ("  got:      " ^ result_list_to_string got ^ "\n");
       print ("  expected: " ^ result_list_to_string expected ^ "\n"));

fun assert_bag name got expected =
  report name (same_bag got expected) got expected;

fun assert_text name got expected =
  if got = expected then print ("PASS " ^ name ^ "\n")
  else
    (failures := !failures + 1;
     print ("FAIL " ^ name ^ "\n");
     print ("  got:      " ^ got ^ "\n");
     print ("  expected: " ^ expected ^ "\n"));

fun call name args =
  Expr (Sym name :: args);

val A = Sym "A";
val B = Sym "B";
val C = Sym "C";
val P = Sym "P";
val R = Sym "R";
val Good = Sym "Good";
val Bad = Sym "Bad";

val space_facts =
  [call "P" [A],
   call "P" [B],
   call "Q" [call "P" [C]]];

val _ =
  assert_bag "space-match-top-level-only"
    (eval_top 40 space_facts (call "match" [Sym "&self", call "P" [Var "x"], Var "x"]))
    [A, B];

val space_repeated =
  [call "R" [A, A],
   call "R" [A, B]];

val _ =
  assert_bag "repeated-variable-match"
    (eval_top 40 space_repeated (call "match" [Sym "&self", call "R" [Var "x", Var "x"], Var "x"]))
    [A];

val space_rule =
  [Expr [Sym "=", call "id" [Var "x"], Var "x"]];

val typed_space =
  [Expr [Sym ":", Sym "Nat", Sym "Type"],
   Expr [Sym ":", Sym "Z", Sym "Nat"],
   Expr [Sym ":", Sym "F", Expr [Sym "->", Sym "Nat", Sym "Nat"]],
   Expr [Sym ":", Sym "Add", Expr [Sym "->", Sym "Nat", Sym "Nat", Sym "Nat"]],
   Expr [Sym "=", call "Add" [Var "x", Sym "Z"], Var "x"]];

val vec_space =
  [Expr [Sym ":", Sym "Person", Sym "Type"],
   Expr [Sym ":", A, Sym "Person"],
   Expr [Sym ":", Sym "Nil", Expr [Sym "Vec", Sym "Person", Sym "Z"]]];

val _ =
  assert_bag "equality-driven-id"
    (eval_top 40 space_rule (call "id" [A]))
    [A];

val _ =
  assert_bag "unknown-expression-stays-data"
    (eval_top 40 space_rule (call "unknown" [A]))
    [call "unknown" [A]];

val _ =
  assert_bag "minimal-eval-not-reducible"
    (eval_top 40 [] (call "eval" [call "unknown" [A]]))
    [Sym "NotReducible"];

val _ =
  assert_bag "chain-after-eval"
    (eval_top 40 space_rule
      (call "chain" [call "eval" [call "id" [A]], Var "x", call "Pair" [Var "x", B]]))
    [call "Pair" [A, B]];

val _ =
  assert_bag "unify-success"
    (eval_top 40 [] (call "unify" [A, A, Good, Bad]))
    [Good];

val _ =
  assert_bag "unify-failure"
    (eval_top 40 [] (call "unify" [A, B, Good, Bad]))
    [Bad];

val _ =
  assert_bag "decons-atom"
    (eval_top 40 [] (call "decons-atom" [Expr [A, B, C]]))
    [Expr [A, Expr [B, C]]];

val _ =
  assert_bag "cons-atom"
    (eval_top 40 [] (call "cons-atom" [A, Expr [B, C]]))
    [Expr [A, B, C]];

val _ =
  assert_bag "function-return"
    (eval_top 40 [] (call "function" [call "return" [A]]))
    [A];

val _ =
  assert_bag "export-return-fragment-import"
    (import_exported_atom_list
      (export_eval_return_fragment (call "return" [A])))
    [call "return" [A]];

val _ =
  assert_bag "collapse-superpose"
    (eval_top 40 [] (call "collapse" [call "superpose" [Expr [A, B]]]))
    [Expr [A, B]];

val _ =
  assert_bag "let-variable"
    (eval_top 40 [] (call "let" [Var "x", A, call "Pair" [Var "x", B]]))
    [call "Pair" [A, B]];

val _ =
  assert_bag "if-true"
    (eval_top 40 [] (call "if" [Sym "True", Sym "yes", Sym "no"]))
    [Sym "yes"];

val _ =
  assert_bag "integer-primitive"
    (eval_top 40 [] (call "+" [IntLit 2, call "*" [IntLit 3, IntLit 4]]))
    [IntLit 14];

val _ =
  assert_bag "export-add-fragment-import"
    (import_exported_atom_list
      (export_eval_add_fragment 39 []
        (call "+" [IntLit 2, call "*" [IntLit 3, IntLit 4]])))
    [IntLit 14];

val _ =
  assert_bag "export-eval-fragment-import"
    (import_exported_atom_list
      (export_eval_eval_fragment 39 space_rule
        (call "eval" [call "id" [A]])))
    [A];

val _ =
  assert_bag "export-chain-fragment-import"
    (import_exported_atom_list
      (export_eval_chain_fragment 39 space_rule
        (call "chain"
          [call "eval" [call "id" [A]], Var "x",
           call "Pair" [Var "x", B]])))
    [call "Pair" [A, B]];

val _ =
  assert_bag "export-case-fragment-import"
    (import_exported_atom_list
      (export_eval_case_fragment 39 []
        (call "case"
          [call "+" [IntLit 1, IntLit 1],
           Expr [Expr [IntLit 2, Sym "two"],
                  Expr [IntLit 3, Sym "three"]]])))
    [Sym "two"];

val _ =
  assert_bag "get-type-direct"
    (eval_top 40 vec_space (call "get-type" [A]))
    [Sym "Person"];

val _ =
  assert_bag "get-type-add-result"
    (eval_top 40 typed_space (call "get-type" [call "Add" [Sym "Z", Sym "Z"]]))
    [Sym "Nat"];

val _ =
  assert_bag "get-type-dependent-cons"
    (eval_top 40 vec_space (call "get-type" [call "Cons" [A, Sym "Nil"]]))
    [Expr [Sym "Vec", Sym "Person", call "S" [Sym "Z"]]];

val _ =
  case run_program_text 40
      ("!(bind! &ctx (new-space))\n" ^
       "!(add-atom &ctx (= (ctx-fn) ctx-result))\n" ^
       "!(assertEqual (evalc (ctx-fn) &ctx) ctx-result)\n") of
    ProgramOutput text =>
      assert_text "evalc-context-space-runner" text "[()]\n[()]\n[()]\n"
  | ProgramRunError msg =>
      assert_text "evalc-context-space-runner" msg "[()]\n[()]\n[()]\n";

val _ =
  case run_program_text 40
      ("(= (fact-here) found)\n" ^
       "!(match (context-space) (= (fact-here) $x) $x)\n") of
    ProgramOutput text =>
      assert_text "context-space-runner" text "[found]\n"
  | ProgramRunError msg =>
      assert_text "context-space-runner" msg "[found]\n";

val _ =
  assert_bag "export-typed-fragment-import"
    (import_exported_atom_list
      (export_eval_typed_fragment 39 typed_space
        (call "Add" [Sym "Z", Sym "Z"])))
    [Sym "Z"];

val _ =
  assert_bag "export-typed-fragment-bad-arg"
    (import_exported_atom_list
      (export_eval_typed_fragment 39 typed_space
        (call "Add" [Sym "F", Sym "Z"])))
    [error_atom (call "Add" [Sym "F", Sym "Z"]) bad_arg_type_atom];

val _ =
  assert_bag "export-evalc-fragment-import"
    (import_exported_atom_list
      (export_eval_evalc_fragment 39 typed_space
        (call "evalc-type" [call "Add" [Sym "Z", Sym "Z"], Sym "Nat"])))
    [Sym "Z"];

val _ =
  assert_bag "export-evalc-fragment-bad-result-type"
    (import_exported_atom_list
      (export_eval_evalc_fragment 39 typed_space
        (call "evalc-type" [call "Add" [Sym "Z", Sym "Z"], Sym "String"])))
    [error_atom (call "Add" [Sym "Z", Sym "Z"]) bad_arg_type_atom];

val _ =
  assert_bag "export-vec-cons-fragment-import"
    (import_exported_atom_list
      (export_eval_vec_cons_fragment vec_space
        (call "VecConsType" [A, Sym "Nil"])))
    [Expr [Sym "Vec", Sym "Person", call "S" [Sym "Z"]]];

val _ =
  assert_bag "integer-comparison"
    (eval_top 40 [] (call "<" [IntLit 2, IntLit 3]))
    [Sym "True"];

val _ =
  assert_bag "case-variable-branch"
    (eval_top 40 [] (call "case"
      [A, Expr [Expr [Var "x", call "tagged" [Var "x"]]]]))
    [call "tagged" [A]];

val _ =
  assert_bag "switch-direct-branch"
    (eval_top 40 [] (call "switch"
      [B, Expr [Expr [A, Sym "no"], Expr [B, Sym "yes"]]]))
    [Sym "yes"];

val _ =
  assert_bag "switch-variable-branch"
    (eval_top 40 [] (call "switch"
      [call "pair" [A, B],
       Expr [Expr [call "pair" [Var "x", Var "y"],
                   call "tagged" [Var "x", Var "y"]]]]))
    [call "tagged" [A, B]];

val _ =
  assert_bag "switch-evaluates-scrutinee"
    (eval_top 40 [Expr [Sym "=", call "choose-switch" [], A]]
      (call "switch"
        [call "choose-switch" [],
         Expr [Expr [A, Sym "bad"],
                Expr [call "choose-switch" [], Sym "direct"]]]))
    [Sym "bad"];

val _ =
  assert_bag "let-star-sequential"
    (eval_top 40 [] (call "let*"
      [Expr [Expr [Var "x", IntLit 1],
             Expr [Var "y", call "+" [Var "x", IntLit 2]]],
       call "Pair" [Var "x", Var "y"]]))
    [call "Pair" [IntLit 1, IntLit 3]];

val _ =
  assert_bag "call-ml-inc"
    (eval_top 40 [] (call "call-ml" [Sym "inc", IntLit 41]))
    [IntLit 42];

val _ =
  assert_bag "call-native-fronts-call-ml"
    (eval_top 40 [] (call "call-native" [Sym "inc", IntLit 41]))
    [IntLit 42];

val _ =
  assert_bag "call-ml-unknown-not-reducible"
    (eval_top 40 [] (call "call-ml" [Sym "unknown", A]))
    [Sym "NotReducible"];

val _ =
  assert_bag "primitive-type-error"
    (eval_top 40 [] (call "+" [IntLit 2, StrLit "x"]))
    [error_atom (call "+" [IntLit 2, StrLit "x"]) (Sym "BadArgType")];

val space_loop =
  [Expr [Sym "=", call "loop" [], call "loop" []]];

val _ =
  assert_bag "fuel-overflow-error"
    (eval_top 3 space_loop (call "loop" []))
    [error_atom (call "loop" []) (Sym "StackOverflow")];

val _ =
  if !failures = 0 then
    print "M1 SML tests passed\n"
  else
    (print ("M1 SML tests failed: " ^ Int.toString (!failures) ^ "\n");
     OS.Process.exit OS.Process.failure);
