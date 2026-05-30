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
  assert_bag "integer-comparison"
    (eval_top 40 [] (call "<" [IntLit 2, IntLit 3]))
    [Sym "True"];

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
