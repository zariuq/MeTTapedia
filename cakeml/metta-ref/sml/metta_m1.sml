datatype atom =
    Sym of string
  | Var of string
  | IntLit of int
  | StrLit of string
  | Expr of atom list;

datatype exported_atom =
    ESym of string
  | EVar of string
  | EInt of int
  | EStr of string
  | EExpr of exported_atom list;

datatype command =
    Add of atom
  | Run of atom;

datatype binding =
    Bind of string * atom;

datatype lookup_result =
    Found of atom
  | Missing;

datatype match_result =
    Match of binding list
  | NoMatch;

datatype decision =
    Yes
  | No;

fun sym s = Sym s;
fun var s = Var s;
fun int_atom n = IntLit n;
fun str_atom s = StrLit s;
fun expr xs = Expr xs;

fun export_atom atom =
  case atom of
    Sym s => ESym s
  | Var v => EVar v
  | IntLit i => EInt i
  | StrLit s => EStr s
  | Expr xs => EExpr (export_atom_list xs)

and export_atom_list xs =
  case xs of
    [] => []
  | atom :: rest => export_atom atom :: export_atom_list rest;

fun import_exported_atom atom =
  case atom of
    ESym s => Sym s
  | EVar v => Var v
  | EInt i => IntLit i
  | EStr s => StrLit s
  | EExpr xs => Expr (import_exported_atom_list xs)

and import_exported_atom_list xs =
  case xs of
    [] => []
  | atom :: rest => import_exported_atom atom :: import_exported_atom_list rest;

(* BEGIN GENERATED PRE_EVAL_FRAGMENTS *)
fun eval_return_fragment_core_is_return_head atom =
  case atom of
    Sym s => s = "return"
  | _ => false;

fun eval_return_fragment_core_items original xs =
  case xs of
    [] => [original]
  | head :: rest =>
      (case rest of
         [] => [original]
       | value :: rest2 =>
           (case rest2 of
              [] =>
                if eval_return_fragment_core_is_return_head head then
                  [Expr [Sym "return", value]]
                else [original]
            | _ => [original]));

fun eval_return_fragment_core atom =
  case atom of
    Expr xs => eval_return_fragment_core_items atom xs
  | _ => [atom];

fun eval_return_fragment atom =
  eval_return_fragment_core atom;

fun export_eval_return_fragment atom =
  export_atom_list (eval_return_fragment atom);
(* END GENERATED PRE_EVAL_FRAGMENTS *)

val true_atom = Sym "True";
val false_atom = Sym "False";
val empty_atom = Sym "Empty";
val not_reducible_atom = Sym "NotReducible";
val stack_overflow_atom = Sym "StackOverflow";
val no_return_atom = Sym "NoReturn";
val bad_arg_type_atom = Sym "BadArgType";

fun error_atom subject reason =
  Expr [Sym "Error", subject, reason];

fun is_error atom =
  case atom of
    Expr (Sym "Error" :: _) => Yes
  | _ => No;

fun atom_eq a b =
  case (a, b) of
    (Sym x, Sym y) => if x = y then Yes else No
  | (Var x, Var y) => if x = y then Yes else No
  | (IntLit x, IntLit y) => if x = y then Yes else No
  | (StrLit x, StrLit y) => if x = y then Yes else No
  | (Expr xs, Expr ys) => atom_list_eq xs ys
  | _ => No

and atom_list_eq xs ys =
  case (xs, ys) of
    ([], []) => Yes
  | (x :: xr, y :: yr) =>
      (case atom_eq x y of
         Yes => atom_list_eq xr yr
       | No => No)
  | _ => No;

fun lookup_bind v bs =
  case bs of
    [] => Missing
  | Bind (w, a) :: rest =>
      if v = w then Found a else lookup_bind v rest;

fun apply_subst_depth depth bs atom =
  if depth <= 0 then atom else
    case atom of
      Var v =>
        (case lookup_bind v bs of
           Found a => apply_subst_depth (depth - 1) bs a
         | Missing => atom)
    | Expr xs => Expr (apply_subst_list depth bs xs)
    | _ => atom

and apply_subst_list depth bs xs =
  case xs of
    [] => []
  | x :: rest => apply_subst_depth depth bs x :: apply_subst_list depth bs rest;

fun apply_subst bs atom =
  apply_subst_depth 64 bs atom;

fun bind_var v a bs =
  case lookup_bind v bs of
    Missing => Match (Bind (v, a) :: bs)
  | Found old =>
      (case atom_eq (apply_subst bs old) (apply_subst bs a) of
         Yes => Match bs
       | No => NoMatch);

fun match_atom p q bs =
  case (apply_subst bs p, apply_subst bs q) of
    (Var v, a) => bind_var v a bs
  | (a, Var v) => bind_var v a bs
  | (Sym x, Sym y) => if x = y then Match bs else NoMatch
  | (IntLit x, IntLit y) => if x = y then Match bs else NoMatch
  | (StrLit x, StrLit y) => if x = y then Match bs else NoMatch
  | (Expr xs, Expr ys) => match_list xs ys bs
  | _ => NoMatch

and match_list ps qs bs =
  case (ps, qs) of
    ([], []) => Match bs
  | (p :: pr, q :: qr) =>
      (case match_atom p q bs of
         Match bs2 => match_list pr qr bs2
       | NoMatch => NoMatch)
  | _ => NoMatch;

fun append_atom xs x =
  case xs of
    [] => [x]
  | y :: rest => y :: append_atom rest x;

fun append_list xs ys =
  case xs of
    [] => ys
  | x :: rest => x :: append_list rest ys;

fun apply_subst_noquote quote_tag bs atom =
  case atom of
    Var v =>
      (case lookup_bind v bs of
         Found a => a
       | Missing => atom)
  | Expr [Sym tag, body] =>
      if tag = quote_tag then atom
      else Expr (apply_subst_noquote_list quote_tag bs [Sym tag, body])
  | Expr xs => Expr (apply_subst_noquote_list quote_tag bs xs)
  | _ => atom

and apply_subst_noquote_list quote_tag bs xs =
  case xs of
    [] => []
  | x :: rest =>
      apply_subst_noquote quote_tag bs x ::
      apply_subst_noquote_list quote_tag bs rest;

fun apply_token_subst bs stmt =
  case stmt of
    [] => []
  | tok :: rest =>
      (case tok of
         Var v =>
           (case lookup_bind v bs of
              Found (Expr xs) => append_list xs (apply_token_subst bs rest)
            | Found a => a :: apply_token_subst bs rest
            | Missing => tok :: apply_token_subst bs rest)
       | _ => tok :: apply_token_subst bs rest);

fun lookup_nth n xs =
  if n < 0 then Missing else
    case xs of
      [] => Missing
    | x :: rest => if n = 0 then Found x else lookup_nth (n - 1) rest;

datatype index_result =
    IndexFound of int
  | IndexMissing;

fun var_index v =
  if v = "0" then IndexFound 0
  else if v = "1" then IndexFound 1
  else if v = "2" then IndexFound 2
  else if v = "3" then IndexFound 3
  else IndexMissing;

fun apply_pos_subst subs atom =
  case atom of
    Var v =>
      (case var_index v of
         IndexFound n =>
           (case lookup_nth n subs of
              Found a => a
            | Missing => atom)
       | IndexMissing => atom)
  | Expr xs => Expr (apply_pos_subst_list subs xs)
  | _ => atom

and apply_pos_subst_list subs xs =
  case xs of
    [] => []
  | x :: rest => apply_pos_subst subs x :: apply_pos_subst_list subs rest;

fun deref_var fuel bs v =
  if fuel <= 0 then Var v else
    case lookup_bind v bs of
      Missing => Var v
    | Found (Var w) => deref_var (fuel - 1) bs w
    | Found a => a;

datatype token =
    TokLParen
  | TokRParen
  | TokBang
  | TokAtom of atom;

datatype digit_result =
    Digit of int
  | NotDigit;

datatype word_atom_result =
    WordAtom of atom
  | WordError of string;

datatype string_scan_result =
    StringScanned of string * char list
  | StringScanError of string;

datatype word_scan_result =
    WordScanned of char list * char list;

datatype tokenize_result =
    Tokenized of token list
  | TokenizeError of string;

datatype atom_parse_result =
    AtomParsed of atom * token list
  | AtomParseError of string;

datatype command_parse_result =
    CommandParsed of command * token list
  | CommandParseError of string;

datatype parsed_atom_result =
    ParsedAtom of atom
  | ParseAtomError of string;

datatype parsed_command_result =
    ParsedCommand of command
  | ParseCommandError of string;

datatype parsed_program_result =
    ParsedProgram of command list
  | ParseProgramError of string;

fun char_is_space c =
  if c = #" " then true
  else if c = #"\n" then true
  else if c = #"\t" then true
  else if c = #"\r" then true
  else false;

fun char_is_delim c =
  if char_is_space c then true
  else if c = #"(" then true
  else if c = #")" then true
  else if c = #"\"" then true
  else if c = #";" then true
  else false;

fun digit_value c =
  if c = #"0" then Digit 0
  else if c = #"1" then Digit 1
  else if c = #"2" then Digit 2
  else if c = #"3" then Digit 3
  else if c = #"4" then Digit 4
  else if c = #"5" then Digit 5
  else if c = #"6" then Digit 6
  else if c = #"7" then Digit 7
  else if c = #"8" then Digit 8
  else if c = #"9" then Digit 9
  else NotDigit;

fun reverse_chars_acc xs acc =
  case xs of
    [] => acc
  | x :: rest => reverse_chars_acc rest (x :: acc);

fun reverse_chars xs =
  reverse_chars_acc xs [];

fun all_digits chars =
  case chars of
    [] => No
  | c :: rest =>
      (case digit_value c of
         Digit d =>
           (case rest of
              [] => Yes
            | _ => all_digits rest)
       | NotDigit => No);

fun nat_from_digits_acc chars acc =
  case chars of
    [] => acc
  | c :: rest =>
      (case digit_value c of
         Digit d => nat_from_digits_acc rest (acc * 10 + d)
       | NotDigit => acc);

fun atom_from_word_chars chars =
  case chars of
    [] => WordError "empty token"
  | #"$" :: rest =>
      (case rest of
         [] => WordError "empty variable"
       | _ => WordAtom (Var (String.implode rest)))
  | _ =>
      (case all_digits chars of
         Yes => WordAtom (IntLit (nat_from_digits_acc chars 0))
       | No => WordAtom (Sym (String.implode chars)));

fun skip_comment chars =
  case chars of
    [] => []
  | #"\n" :: rest => rest
  | _ :: rest => skip_comment rest;

fun scan_string acc chars =
  case chars of
    [] => StringScanError "unterminated string"
  | #"\"" :: rest => StringScanned (String.implode (reverse_chars acc), rest)
  | c :: rest => scan_string (c :: acc) rest;

fun scan_word acc chars =
  case chars of
    [] => WordScanned (reverse_chars acc, [])
  | c :: rest =>
      if char_is_delim c then WordScanned (reverse_chars acc, chars)
      else scan_word (c :: acc) rest;

fun tokenize_chars chars =
  case chars of
    [] => Tokenized []
  | c :: rest =>
      if char_is_space c then tokenize_chars rest
      else if c = #";" then tokenize_chars (skip_comment rest)
      else if c = #"(" then
        (case tokenize_chars rest of
           Tokenized toks => Tokenized (TokLParen :: toks)
         | TokenizeError msg => TokenizeError msg)
      else if c = #")" then
        (case tokenize_chars rest of
           Tokenized toks => Tokenized (TokRParen :: toks)
         | TokenizeError msg => TokenizeError msg)
      else if c = #"!" then
        (case tokenize_chars rest of
           Tokenized toks => Tokenized (TokBang :: toks)
         | TokenizeError msg => TokenizeError msg)
      else if c = #"\"" then
        (case scan_string [] rest of
           StringScanned (s, rest2) =>
             (case tokenize_chars rest2 of
                Tokenized toks => Tokenized (TokAtom (StrLit s) :: toks)
              | TokenizeError msg => TokenizeError msg)
         | StringScanError msg => TokenizeError msg)
      else
        (case scan_word [c] rest of
           WordScanned (word_chars, rest2) =>
             (case atom_from_word_chars word_chars of
                WordAtom atom =>
                  (case tokenize_chars rest2 of
                     Tokenized toks => Tokenized (TokAtom atom :: toks)
                   | TokenizeError msg => TokenizeError msg)
              | WordError msg => TokenizeError msg));

fun tokenize text =
  tokenize_chars (String.explode text);

fun parse_atom_tokens toks =
  case toks of
    TokAtom atom :: rest => AtomParsed (atom, rest)
  | TokLParen :: rest => parse_expr_items [] rest
  | TokRParen :: rest => AtomParseError "unexpected )"
  | TokBang :: rest => AtomParseError "unexpected !"
  | [] => AtomParseError "expected atom"

and parse_expr_items items toks =
  case toks of
    TokRParen :: rest => AtomParsed (Expr items, rest)
  | [] => AtomParseError "unterminated expression"
  | _ =>
      (case parse_atom_tokens toks of
         AtomParsed (atom, rest) => parse_expr_items (append_atom items atom) rest
       | AtomParseError msg => AtomParseError msg);

fun parse_command_tokens toks =
  case toks of
    TokBang :: rest =>
      (case parse_atom_tokens rest of
         AtomParsed (atom, rest2) => CommandParsed (Run atom, rest2)
       | AtomParseError msg => CommandParseError msg)
  | _ =>
      (case parse_atom_tokens toks of
         AtomParsed (atom, rest) => CommandParsed (Add atom, rest)
       | AtomParseError msg => CommandParseError msg);

fun parse_program_tokens toks =
  case toks of
    [] => ParsedProgram []
  | _ =>
      (case parse_command_tokens toks of
         CommandParsed (cmd, rest) =>
           (case parse_program_tokens rest of
              ParsedProgram cmds => ParsedProgram (cmd :: cmds)
            | ParseProgramError msg => ParseProgramError msg)
       | CommandParseError msg => ParseProgramError msg);

fun parse_atom_from_string text =
  case tokenize text of
    Tokenized toks =>
      (case parse_atom_tokens toks of
         AtomParsed (atom, []) => ParsedAtom atom
       | AtomParsed (atom, _) => ParseAtomError "trailing tokens after atom"
       | AtomParseError msg => ParseAtomError msg)
  | TokenizeError msg => ParseAtomError msg;

fun parse_command_from_string text =
  case tokenize text of
    Tokenized toks =>
      (case parse_command_tokens toks of
         CommandParsed (cmd, []) => ParsedCommand cmd
       | CommandParsed (cmd, _) => ParseCommandError "trailing tokens after command"
       | CommandParseError msg => ParseCommandError msg)
  | TokenizeError msg => ParseCommandError msg;

fun parse_program_from_string text =
  case tokenize text of
    Tokenized toks => parse_program_tokens toks
  | TokenizeError msg => ParseProgramError msg;

fun match_space_entry pattern templ entry =
  case match_atom pattern entry [] of
    Match bs => [apply_subst bs templ]
  | NoMatch => [];

fun match_space_raw space pattern templ =
  case space of
    [] => []
  | entry :: rest =>
      append_list (match_space_entry pattern templ entry)
        (match_space_raw rest pattern templ);

fun atom_to_string atom =
  case atom of
    Sym s => s
  | Var v => "$" ^ v
  | IntLit n => Int.toString n
  | StrLit s => "\"" ^ s ^ "\""
  | Expr xs => "(" ^ atom_list_to_string xs ^ ")"

and atom_list_to_string xs =
  case xs of
    [] => ""
  | [x] => atom_to_string x
  | x :: rest => atom_to_string x ^ " " ^ atom_list_to_string rest;

fun result_list_to_string xs =
  case xs of
    [] => "[]"
  | _ => "[" ^ atom_list_to_string xs ^ "]";

fun visible_results atoms =
  case atoms of
    [] => []
  | Sym "Empty" :: rest => visible_results rest
  | x :: rest => x :: visible_results rest;

fun m1_default_types atom =
  case atom of
    IntLit _ => [Sym "Number"]
  | StrLit _ => [Sym "String"]
  | Sym _ => [Sym "%Undefined%"]
  | Var _ => [Sym "Variable"]
  | Expr _ => [Sym "Expression"];

fun m1_type_matches expected actual =
  case atom_eq expected actual of
    Yes => Yes
  | No =>
      (case (expected, actual) of
         (Sym "Atom", _) => Yes
       | (_, Sym "Atom") => Yes
       | (Sym "%Undefined%", _) => Yes
       | (_, Sym "%Undefined%") => Yes
       | (Var _, _) => Yes
       | (_, Var _) => Yes
       | _ => No);

fun m1_any_type_match expected actuals =
  case actuals of
    [] => No
  | actual :: rest =>
      (case m1_type_matches expected actual of
         Yes => Yes
       | No => m1_any_type_match expected rest);

fun m1_declared_type_lookup space atom =
  case space of
    [] => []
  | Expr [Sym ":", a, typ] :: rest =>
      (case atom_eq atom a of
         Yes => typ :: m1_declared_type_lookup rest atom
       | No => m1_declared_type_lookup rest atom)
  | _ :: rest => m1_declared_type_lookup rest atom;

fun m1_declared_or_default_type_lookup space atom =
  case m1_declared_type_lookup space atom of
    [] => m1_default_types atom
  | types => types;

datatype m1_split_result =
    M1Split of atom list * atom
  | M1NoSplit;

fun m1_split_last xs =
  case xs of
    [] => M1NoSplit
  | [x] => M1Split ([], x)
  | x :: rest =>
      (case m1_split_last rest of
         M1Split (front, last) => M1Split (x :: front, last)
       | M1NoSplit => M1NoSplit);

fun m1_type_of_atom space atom =
  case atom of
    Expr [Sym "Cons", elem, tail] =>
      [m1_dependent_vec_cons_type space elem tail]
  | Expr (head :: args) =>
      (case m1_function_result_types space
          (m1_declared_or_default_type_lookup space head) args of
         [] => [Sym "Expression"]
       | types => types)
  | _ => m1_declared_or_default_type_lookup space atom

and m1_function_result_types space head_types args =
  case head_types of
    [] => []
  | Expr (Sym "->" :: parts) :: rest =>
      (case m1_split_last parts of
         M1Split (arg_types, result_type) =>
           (case m1_all_arg_types_match space arg_types args of
              Yes => result_type :: m1_function_result_types space rest args
            | No => bad_arg_type_atom ::
                m1_function_result_types space rest args)
       | M1NoSplit => bad_arg_type_atom ::
           m1_function_result_types space rest args)
  | _ :: rest => m1_function_result_types space rest args

and m1_all_arg_types_match space expected args =
  case (expected, args) of
    ([], []) => Yes
  | (typ :: typ_rest, arg :: arg_rest) =>
      (case m1_any_type_match typ (m1_type_of_atom space arg) of
         Yes => m1_all_arg_types_match space typ_rest arg_rest
       | No => No)
  | _ => No

and m1_dependent_vec_cons_type space elem tail =
  case m1_type_of_atom space tail of
    Expr [Sym "Vec", elem_type, n] :: _ =>
      (case m1_type_of_atom space elem of
         actual :: _ =>
           (case m1_type_matches elem_type actual of
              Yes => Expr [Sym "Vec", elem_type, Expr [Sym "S", n]]
            | No => bad_arg_type_atom)
       | [] => bad_arg_type_atom)
  | _ => bad_arg_type_atom;

fun m1_has_bad_arg_type types =
  case types of
    [] => No
  | typ :: rest =>
      (case atom_eq typ bad_arg_type_atom of
         Yes => Yes
       | No => m1_has_bad_arg_type rest);

fun m1_evalc_values space original expected vals =
  case vals of
    [] => []
  | value :: rest =>
      (case m1_any_type_match expected (m1_type_of_atom space value) of
         Yes => value :: m1_evalc_values space original expected rest
       | No => error_atom original bad_arg_type_atom ::
           m1_evalc_values space original expected rest);

fun m1_has_type_decl atom typ space =
  case space of
    [] => No
  | Expr [Sym ":", a, declared] :: rest =>
      (case (atom_eq atom a, atom_eq typ declared) of
         (Yes, Yes) => Yes
       | _ => m1_has_type_decl atom typ rest)
  | _ :: rest => m1_has_type_decl atom typ rest;

fun m1_typed_add_bad space atom =
  case atom of
    Expr [Sym "Add", a, b] =>
      (case m1_has_type_decl (Sym "Add")
          (Expr [Sym "->", Sym "Nat", Sym "Nat", Sym "Nat"]) space of
         Yes =>
           (case m1_any_type_match (Sym "Nat") (m1_type_of_atom space a) of
              Yes =>
                (case m1_any_type_match (Sym "Nat") (m1_type_of_atom space b) of
                   Yes => No
                 | No => Yes)
            | No => Yes)
       | No => No)
  | _ => No;

fun eval_args fuel space args =
  case args of
    [] => [Expr []]
  | x :: rest => combine_eval_args (eval fuel space x) (eval_args fuel space rest)

and combine_eval_args xs yss =
  case xs of
    [] => []
  | x :: rest => append_list (prepend_arg x yss) (combine_eval_args rest yss)

and prepend_arg x yss =
  case yss of
    [] => []
  | Expr ys :: rest => Expr (x :: ys) :: prepend_arg x rest
  | _ :: rest => prepend_arg x rest

and eval_int_bin f fuel space a b original =
  eval_int_bin_values f (eval_args (fuel - 1) space [a, b]) original

and eval_int_bin_values f vals original =
  case vals of
    [] => []
  | Expr [IntLit x, IntLit y] :: rest =>
      IntLit (f x y) :: eval_int_bin_values f rest original
  | _ :: rest =>
      error_atom original bad_arg_type_atom :: eval_int_bin_values f rest original

and eval_int_cmp f fuel space a b original =
  eval_int_cmp_values f (eval_args (fuel - 1) space [a, b]) original

and eval_int_cmp_values f vals original =
  case vals of
    [] => []
  | Expr [IntLit x, IntLit y] :: rest =>
      (if f x y then true_atom else false_atom) :: eval_int_cmp_values f rest original
  | _ :: rest =>
      error_atom original bad_arg_type_atom :: eval_int_cmp_values f rest original

and bool_and a b =
  case (a, b) of
    (Yes, Yes) => true
  | _ => false

and bool_or a b =
  case (a, b) of
    (No, No) => false
  | _ => true

and eval_bool_bin f fuel space a b original =
  eval_bool_bin_values f (eval_args (fuel - 1) space [a, b]) original

and eval_bool_bin_values f vals original =
  case vals of
    [] => []
  | Expr [Sym "True", Sym "True"] :: rest =>
      (if f Yes Yes then true_atom else false_atom) :: eval_bool_bin_values f rest original
  | Expr [Sym "True", Sym "False"] :: rest =>
      (if f Yes No then true_atom else false_atom) :: eval_bool_bin_values f rest original
  | Expr [Sym "False", Sym "True"] :: rest =>
      (if f No Yes then true_atom else false_atom) :: eval_bool_bin_values f rest original
  | Expr [Sym "False", Sym "False"] :: rest =>
      (if f No No then true_atom else false_atom) :: eval_bool_bin_values f rest original
  | _ :: rest =>
      error_atom original bad_arg_type_atom :: eval_bool_bin_values f rest original

and eval_not fuel space a original =
  case eval (fuel - 1) space a of
    [Sym "True"] => [false_atom]
  | [Sym "False"] => [true_atom]
  | _ => [error_atom original bad_arg_type_atom]

and eval_if fuel space c t e original =
  eval_if_values fuel space (eval (fuel - 1) space c) t e original

and eval_if_values fuel space vals t e original =
  case vals of
    [] => []
  | Sym "True" :: rest =>
      append_list (eval (fuel - 1) space t) (eval_if_values fuel space rest t e original)
  | Sym "False" :: rest =>
      append_list (eval (fuel - 1) space e) (eval_if_values fuel space rest t e original)
  | _ :: rest =>
      error_atom original bad_arg_type_atom :: eval_if_values fuel space rest t e original

and eval_match fuel space pattern templ =
  eval_each fuel space (match_space_raw space pattern templ)

and eval_each fuel space atoms =
  case atoms of
    [] => []
  | a :: rest => append_list (eval (fuel - 1) space a) (eval_each fuel space rest)

and eval_superpose fuel space atom =
  case atom of
    Expr xs => eval_each (fuel - 1) space xs
  | _ => [atom]

and eval_collapse fuel space atom =
  [Expr (visible_results (eval (fuel - 1) space atom))]

and eval_let fuel space pat value body original =
  case pat of
    Var v => eval_let_values fuel space v (eval (fuel - 1) space value) body
  | _ => [error_atom original bad_arg_type_atom]

and eval_let_values fuel space v vals body =
  case vals of
    [] => []
  | x :: rest =>
      append_list (eval (fuel - 1) space (apply_subst [Bind (v, x)] body))
        (eval_let_values fuel space v rest body)

and eval_unify fuel space atom pattern then_atom else_atom =
  case match_atom atom pattern [] of
    Match bs => eval (fuel - 1) space (apply_subst bs then_atom)
  | NoMatch => eval (fuel - 1) space else_atom

and eval_decons atom original =
  case atom of
    Expr (x :: rest) => [Expr [x, Expr rest]]
  | _ => [error_atom original bad_arg_type_atom]

and eval_cons head tail original =
  case tail of
    Expr xs => [Expr (head :: xs)]
  | _ => [error_atom original bad_arg_type_atom]

and eval_function fuel space body original =
  case eval (fuel - 1) space body of
    Expr [Sym "return", value] :: rest =>
      value :: eval_function_rest rest original
  | [] => [error_atom original no_return_atom]
  | _ => [error_atom original no_return_atom]

and eval_function_rest vals original =
  case vals of
    [] => []
  | Expr [Sym "return", value] :: rest => value :: eval_function_rest rest original
  | _ :: rest => error_atom original no_return_atom :: eval_function_rest rest original

and eval_minimal_eval fuel space atom =
  let
    val rs = eval (fuel - 1) space atom
  in
    case rs of
      [one] => (case atom_eq one atom of Yes => [not_reducible_atom] | No => rs)
    | _ => rs
  end

and eval_call_ml_inc_values vals original =
  case vals of
    [] => []
  | IntLit n :: rest =>
      IntLit (n + 1) :: eval_call_ml_inc_values rest original
  | _ :: rest =>
      error_atom original bad_arg_type_atom :: eval_call_ml_inc_values rest original

and eval_call_ml fuel space name args original =
  case (name, args) of
    (Sym "inc", [arg]) =>
      eval_call_ml_inc_values (eval (fuel - 1) space arg) original
  | _ => [not_reducible_atom]

and eval_chain fuel space nested var_atom templ original =
  case var_atom of
    Var v => eval_chain_values fuel space v (eval (fuel - 1) space nested) templ
  | _ => [error_atom original bad_arg_type_atom]

and eval_chain_values fuel space v vals templ =
  case vals of
    [] => []
  | x :: rest =>
      append_list (eval (fuel - 1) space (apply_subst [Bind (v, x)] templ))
        (eval_chain_values fuel space v rest templ)

and eval_case_one fuel space value branches original =
  case branches of
    [] => []
  | Expr [pattern, body] :: rest =>
      (case match_atom pattern value [] of
         Match bs => eval (fuel - 1) space (apply_subst bs body)
       | NoMatch => eval_case_one fuel space value rest original)
  | _ :: rest => eval_case_one fuel space value rest original

and eval_case_values fuel space vals branches original =
  case vals of
    [] => []
  | value :: rest =>
      append_list (eval_case_one fuel space value branches original)
        (eval_case_values fuel space rest branches original)

and eval_case fuel space scrut branches original =
  eval_case_values fuel space (eval (fuel - 1) space scrut) branches original

and eval_switch_one fuel space value branches original =
  case branches of
    [] => []
  | Expr [pattern, body] :: rest =>
      (case match_atom pattern value [] of
         Match bs => eval (fuel - 1) space (apply_subst bs body)
       | NoMatch => eval_switch_one fuel space value rest original)
  | _ :: rest => eval_switch_one fuel space value rest original

and eval_switch_values fuel space vals branches original =
  case vals of
    [] => []
  | value :: rest =>
      append_list (eval_switch_one fuel space value branches original)
        (eval_switch_values fuel space rest branches original)

and eval_switch fuel space scrut branches original =
  eval_switch_values fuel space (eval (fuel - 1) space scrut) branches original

and subst_let_binding_pair v value pair =
  case pair of
    Expr [Var w, rhs] => Expr [Var w, apply_subst [Bind (v, value)] rhs]
  | other => other

and subst_let_binding_pairs v value pairs =
  case pairs of
    [] => []
  | pair :: rest =>
      subst_let_binding_pair v value pair :: subst_let_binding_pairs v value rest

and eval_let_star fuel space bindings body original =
  case bindings of
    [] => eval (fuel - 1) space body
  | Expr [Var v, value] :: rest =>
      eval_let_star_values fuel space v (eval (fuel - 1) space value) rest body original
  | _ :: _ => [error_atom original bad_arg_type_atom]

and eval_let_star_values fuel space v vals rest body original =
  case vals of
    [] => []
  | value :: more =>
      append_list
        (eval_let_star fuel space
          (subst_let_binding_pairs v value rest)
          (apply_subst [Bind (v, value)] body) original)
        (eval_let_star_values fuel space v more rest body original)

and eval_equalities fuel space atom =
  case space of
    [] => []
  | Expr [Sym "=", lhs, rhs] :: rest =>
      (case match_atom lhs atom [] of
         Match bs =>
           append_list (eval (fuel - 1) space (apply_subst bs rhs))
             (eval_equalities fuel rest atom)
       | NoMatch => eval_equalities fuel rest atom)
  | _ :: rest => eval_equalities fuel rest atom

and eval_eq_values vals original =
  case vals of
    [] => []
  | Expr [x, y] :: rest =>
      (case atom_eq x y of Yes => true_atom | No => false_atom) :: eval_eq_values rest original
  | _ :: rest => error_atom original bad_arg_type_atom :: eval_eq_values rest original

and eval_expr fuel space original xs =
  case xs of
    Sym "+" :: a :: b :: [] => eval_int_bin (fn x => fn y => x + y) fuel space a b original
  | Sym "*" :: a :: b :: [] => eval_int_bin (fn x => fn y => x * y) fuel space a b original
  | Sym "-" :: a :: b :: [] => eval_int_bin (fn x => fn y => x - y) fuel space a b original
  | Sym "<" :: a :: b :: [] => eval_int_cmp (fn x => fn y => x < y) fuel space a b original
  | Sym "==" :: a :: b :: [] => eval_eq_values (eval_args (fuel - 1) space [a, b]) original
  | Sym "and" :: a :: b :: [] => eval_bool_bin bool_and fuel space a b original
  | Sym "or" :: a :: b :: [] => eval_bool_bin bool_or fuel space a b original
  | Sym "not" :: a :: [] => eval_not fuel space a original
  | Sym "if" :: c :: t :: e :: [] => eval_if fuel space c t e original
  | Sym "match" :: Sym "&self" :: pattern :: templ :: [] => eval_match fuel space pattern templ
  | Sym "match" :: Expr [Sym "context-space"] :: pattern :: templ :: [] =>
      eval_match fuel space pattern templ
  | Sym "context-space" :: [] => [Sym "&self"]
  | Sym "collapse" :: atom :: [] => eval_collapse fuel space atom
  | Sym "superpose" :: atom :: [] => eval_superpose fuel space atom
  | Sym "let" :: pat :: value :: body :: [] => eval_let fuel space pat value body original
  | Sym "unify" :: atom :: pattern :: then_atom :: else_atom :: [] =>
      eval_unify fuel space atom pattern then_atom else_atom
  | Sym "decons-atom" :: atom :: [] => eval_decons atom original
  | Sym "cons-atom" :: head :: tail :: [] => eval_cons head tail original
  | Sym "function" :: body :: [] => eval_function fuel space body original
  | Sym "return" :: _ :: [] => [original]
  | Sym "eval" :: atom :: [] => eval_minimal_eval fuel space atom
  | Sym "evalc" :: atom :: Sym "&self" :: [] =>
      visible_results (eval (fuel - 1) space atom)
  | Sym "evalc" :: _ => [error_atom original bad_arg_type_atom]
  | Sym "chain" :: nested :: var_atom :: templ :: [] =>
      eval_chain fuel space nested var_atom templ original
  | Sym "get-type" :: atom :: [] => m1_type_of_atom space atom
  | Sym "evalc-type" :: atom :: expected :: [] =>
      m1_evalc_values space atom expected
        (case m1_typed_add_bad space atom of
           Yes => [error_atom atom bad_arg_type_atom]
         | No => eval (fuel - 1) space atom)
  | Sym "VecConsType" :: elem :: tail :: [] =>
      [m1_dependent_vec_cons_type space elem tail]
  | Sym "case" :: scrut :: Expr branches :: [] =>
      eval_case fuel space scrut branches original
  | Sym "case" :: _ => [error_atom original bad_arg_type_atom]
  | Sym "switch" :: scrut :: Expr branches :: [] =>
      eval_switch fuel space scrut branches original
  | Sym "switch" :: _ => [error_atom original bad_arg_type_atom]
  | Sym "let*" :: Expr bindings :: body :: [] =>
      eval_let_star fuel space bindings body original
  | Sym "let*" :: _ => [error_atom original bad_arg_type_atom]
  | Sym "call-ml" :: name :: args => eval_call_ml fuel space name args original
  | Sym "call-native" :: name :: args => eval_call_ml fuel space name args original
  | _ =>
      (case eval_equalities fuel space original of
         [] => [original]
       | rs => rs)

and eval fuel space atom =
  if fuel <= 0 then [error_atom atom stack_overflow_atom] else
    case is_error atom of
      Yes => [atom]
    | No =>
        (case atom of
           Expr xs => eval_expr fuel space atom xs
         | _ => [atom]);

fun eval_top fuel space atom =
  visible_results (eval fuel space atom);

(* BEGIN GENERATED POST_EVAL_FRAGMENTS *)
fun eval_add_fragment fuel space atom =
  case atom of
    Expr [Sym "+", a, b] =>
      eval_int_bin_values (fn x => fn y => x + y)
        (eval_args fuel space [a, b]) atom
  | _ => [atom];

fun export_eval_add_fragment fuel space atom =
  export_atom_list (eval_add_fragment fuel space atom);

fun eval_eval_fragment fuel space atom =
  case atom of
    Expr [Sym "eval", body] =>
      let
        val rs = eval fuel space body
      in
        case rs of
          [one] => (case atom_eq one body of Yes => [not_reducible_atom] | No => rs)
        | _ => rs
      end
  | _ => [atom];

fun export_eval_eval_fragment fuel space atom =
  export_atom_list (eval_eval_fragment fuel space atom);

fun eval_chain_fragment fuel space atom =
  case atom of
    Expr [Sym "chain", nested, Var v, templ] =>
      eval_chain_values (fuel + 1) space v (eval fuel space nested) templ
  | _ => [atom];

fun export_eval_chain_fragment fuel space atom =
  export_atom_list (eval_chain_fragment fuel space atom);

fun eval_case_fragment fuel space atom =
  case atom of
    Expr [Sym "case", scrut, Expr branches] =>
      eval_case_values (fuel + 1) space (eval fuel space scrut) branches atom
  | _ => [atom];

fun export_eval_case_fragment fuel space atom =
  export_atom_list (eval_case_fragment fuel space atom);

fun m1_typed_eval fuel space atom =
  case m1_typed_add_bad space atom of
    Yes => [error_atom atom bad_arg_type_atom]
  | No => eval fuel space atom;

fun eval_typed_fragment fuel space atom =
  m1_typed_eval fuel space atom;

fun export_eval_typed_fragment fuel space atom =
  export_atom_list (eval_typed_fragment fuel space atom);

fun eval_evalc_fragment fuel space atom =
  case atom of
    Expr [Sym "evalc-type", term, expected] =>
      m1_evalc_values space term expected (m1_typed_eval fuel space term)
  | _ => [atom];

fun export_eval_evalc_fragment fuel space atom =
  export_atom_list (eval_evalc_fragment fuel space atom);

fun eval_vec_cons_fragment space atom =
  case atom of
    Expr [Sym "VecConsType", elem, tail] =>
      [m1_dependent_vec_cons_type space elem tail]
  | _ => [atom];

fun export_eval_vec_cons_fragment space atom =
  export_atom_list (eval_vec_cons_fragment space atom);
(* END GENERATED POST_EVAL_FRAGMENTS *)

fun lookup_named_space name spaces =
  case spaces of
    [] => []
  | (key, stored) :: rest =>
      if name = key then stored else lookup_named_space name rest;

fun named_space_exists name spaces =
  case spaces of
    [] => No
  | (key, stored) :: rest =>
      if name = key then Yes else named_space_exists name rest;

fun set_named_space name stored spaces =
  case spaces of
    [] => [(name, stored)]
  | (key, old) :: rest =>
      if name = key then (name, stored) :: rest
      else (key, old) :: set_named_space name stored rest;

fun expected_result_atoms expected =
  case expected of
    Expr xs => xs
  | atom => [atom];

fun eval_env fuel self spaces atom =
  case atom of
    Expr [Sym "evalc", term, Sym name] =>
      if name = "&self" then eval_top fuel self term
      else
        (case named_space_exists name spaces of
           Yes => eval_top fuel (lookup_named_space name spaces) term
         | No => [error_atom atom bad_arg_type_atom])
  | Expr [Sym "match", Sym name, pattern, templ] =>
      if name = "&self" then eval_match fuel self pattern templ
      else
        (case named_space_exists name spaces of
           Yes => eval_match fuel (lookup_named_space name spaces) pattern templ
         | No => [error_atom atom bad_arg_type_atom])
  | Expr [Sym "assertEqual", lhs, rhs] =>
      (case atom_list_eq
          (eval_env fuel self spaces lhs)
          (eval_env fuel self spaces rhs) of
         Yes => [Expr []]
       | No => [error_atom atom bad_arg_type_atom])
  | Expr [Sym "assertEqualToResult", lhs, expected] =>
      (case atom_list_eq
          (eval_env fuel self spaces lhs)
          (expected_result_atoms expected) of
         Yes => [Expr []]
       | No => [error_atom atom bad_arg_type_atom])
  | _ => eval_top fuel self atom;

fun run_effect fuel self spaces atom =
  case atom of
    Expr [Sym "bind!", Sym name, Expr [Sym "new-space"]] =>
      (self, set_named_space name [] spaces, [Expr []])
  | Expr [Sym "add-atom", Sym "&self", new_atom] =>
      (append_atom self new_atom, spaces, [Expr []])
  | Expr [Sym "add-atom", Sym name, new_atom] =>
      (case named_space_exists name spaces of
         Yes =>
           (self,
            set_named_space name
              (append_atom (lookup_named_space name spaces) new_atom) spaces,
            [Expr []])
       | No => (self, spaces, [error_atom atom bad_arg_type_atom]))
  | _ => (self, spaces, eval_env fuel self spaces atom);

fun run_program_env fuel self spaces commands =
  case commands of
    [] => (self, spaces, [])
  | Add atom :: rest =>
      run_program_env fuel (append_atom self atom) spaces rest
  | Run atom :: rest =>
      let
        val step = run_effect fuel self spaces atom
      in
        case step of
          (self1, spaces1, rs) =>
            (case run_program_env fuel self1 spaces1 rest of
               (self2, spaces2, outs) => (self2, spaces2, rs :: outs))
      end;

fun run_program fuel space commands =
  case run_program_env fuel space [] commands of
    (self, spaces, outs) => (self, outs);

fun result_lines_to_string outs =
  case outs of
    [] => ""
  | x :: rest => result_list_to_string x ^ "\n" ^ result_lines_to_string rest;

datatype program_run_result =
    ProgramOutput of string
  | ProgramRunError of string;

fun run_program_text fuel text =
  case parse_program_from_string text of
    ParsedProgram commands =>
      (case run_program fuel [] commands of
         (space, outs) => ProgramOutput (result_lines_to_string outs))
  | ParseProgramError msg => ProgramRunError msg;

fun contains_atom x xs =
  case xs of
    [] => No
  | y :: rest =>
      (case atom_eq x y of
         Yes => Yes
       | No => contains_atom x rest);

fun remove_one x xs =
  case xs of
    [] => []
  | y :: rest =>
      (case atom_eq x y of
         Yes => rest
       | No => y :: remove_one x rest);

fun same_bag xs ys =
  case xs of
    [] => (case ys of [] => Yes | _ => No)
  | x :: rest =>
      (case contains_atom x ys of
         Yes => same_bag rest (remove_one x ys)
       | No => No);
