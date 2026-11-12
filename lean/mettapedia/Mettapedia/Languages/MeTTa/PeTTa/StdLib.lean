import Mettapedia.Languages.MeTTa.PeTTa.Effects
import Mettapedia.Languages.MeTTa.OSLFCore.ByteString
import Mathlib.Data.List.Sort

/-!
# PeTTa ground primitives

One primitive table serves the executable evaluator. Storage and opaque handles
belong to Effects; source matching belongs to SpaceSemantics. Primitive faults,
False and empty ordered answers remain distinct. The arithmetic profile uses
mathematical integers. `%` takes the sign of the divisor, as Prolog's `mod`
does. `//` is not a PeTTa primitive: upstream PeTTa and CeTTa's PeTTa mode
leave it as data unless the program defines it. The earlier table assigned it
a floor quotient, borrowing an operator from a different arithmetic profile;
that registration and its quotient claims have been removed. The selected MeTTaIL library
derivations are in MinimalInstructions, alongside the rewrite instructions they
derive.

The closed-value profile also includes eager list operations, metatype queries,
ground scalar type queries, and the string operations used by source readers.
Closed string-list and integer-list sorting retain repeated occurrences, as PeTTa's `msort` does;
the order of mixed values is outside this primitive fragment.
Strings retain their exact bytes through the shared ByteString image. Open
membership and non-scalar type inference remain outside this primitive profile.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.StdLib

set_option maxHeartbeats 800000

open Mettapedia.Languages.MeTTa.OSLFCore
open NamedSpaces (Handle Store)
open Effects
open SpaceSemantics (query)

def known (head : String) : Bool :=
  head ∈ ["+", "-", "*", "%", "<", "<=", ">", ">=", "==", "and", "or", "not", "cons", "size-atom",
    "index-atom", "new-space", "add-atom", "remove-atom", "get-atoms", "match",
    "get-state", "change-state!", "reverse", "is-member", "get-metatype", "get-type",
    "str:byte-length", "str:byte-slice", "str:concat", "str:join", "str:from-codepoints",
    "parse", "cons-atom", "union-atom", "sort-atom", "msort", "unique-atom", "superpose"]

/-- Recognize exactly the closed string-list fragment of native sorting. -/
def strings : List Atom → Option (List String)
  | [] => some []
  | .grounded (.string first) :: rest => (first :: ·) <$> strings rest
  | _ => none

def stringAtoms (items : List String) : List Atom := items.map (.grounded ∘ .string)

theorem strings_string_atoms (items : List String) : strings (stringAtoms items) = some items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      change (first :: ·) <$> strings (stringAtoms rest) = some (first :: rest)
      rw [ih]
      rfl

/-- Decode only actual integer values. Boolean and foreign grounded values
do not become integer sort keys merely because a worker has a word encoding. -/
def integers : List Atom → Option (List Int)
  | [] => some []
  | .grounded (.int first) :: rest => (first :: ·) <$> integers rest
  | _ => none

def integerAtoms (items : List Int) : List Atom := items.map (.grounded ∘ .int)

theorem integers_integer_atoms (items : List Int) : integers (integerAtoms items) = some items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      change (first :: ·) <$> integers (integerAtoms rest) = some (first :: rest)
      rw [ih]
      rfl

theorem integers_exact (items : List Atom) (values : List Int) (decoded : integers items = some values) :
    integerAtoms values = items := by
  induction items generalizing values with
  | nil => cases decoded; rfl
  | cons first rest ih =>
      cases first with
      | var _ | symbol _ | expression _ => cases decoded
      | grounded ground =>
        cases ground with
        | int value =>
          change (integers rest).map (value :: ·) = some values at decoded
          obtain ⟨tail, decodedTail, same⟩ := Option.map_eq_some_iff.mp decoded
          cases same
          change .grounded (.int value) :: integerAtoms tail = _
          rw [ih tail decodedTail]
        | string _ | bool _ | custom _ _ => cases decoded

/-- The closed homogeneous fragment of the source's duplicate-preserving
sort. Mixed-value term order is not specified by this partial decoder. -/
def sortClosed (items : List Atom) : Option (List Atom) :=
  match strings items with
  | some texts => some (stringAtoms (texts.mergeSort (· ≤ ·)))
  | none => (integers items).map (fun values => integerAtoms (values.mergeSort (· ≤ ·)))

theorem sortClosed_strings (items : List String) :
    sortClosed (stringAtoms items) = some (stringAtoms (items.mergeSort (· ≤ ·))) := by
  simp only [sortClosed, strings_string_atoms]

theorem sortClosed_integers (items : List Int) :
    sortClosed (integerAtoms items) = some (integerAtoms (items.mergeSort (· ≤ ·))) := by
  cases items with
  | nil => simp [sortClosed, integerAtoms, strings, stringAtoms]
  | cons first rest =>
      have notStrings : strings (integerAtoms (first :: rest)) = none := rfl
      simp only [sortClosed, notStrings, integers_integer_atoms, Option.map_some]

/-- Native argument demand: patterns, templates and stored data are values;
numeric operands and locations are evaluated. -/
def rawArgument (head : String) (index : Nat) : Bool :=
  (head = "match" && index > 0) ||
  ((head = "add-atom" || head = "remove-atom" || head = "change-state!") && index = 1)

/-- Closed membership retains one success per matching occurrence. Failure is
one False answer, including membership in an empty expression. -/
def membershipAnswers (value : Atom) (items : List Atom) : List Atom :=
  match items.filter (· == value) with
  | [] => [boolean false]
  | selected => selected.map fun _ => boolean true

/-- The loaded function registry determines the symbol case of metatype.
Expressions and grounded values retain their structural metatypes. -/
def metatype (state : State) : Atom → Atom
  | .var _ => .symbol "Variable"
  | .expression _ => .symbol "Expression"
  | .grounded _ => .symbol "Grounded"
  | .symbol name =>
      if known name || name ∈ ["let", "let*", "case", "if", "collapse", "superpose",
          "empty", "quote", "eval", "readln!", "println!", "true", "false", "True", "False"] ||
          state.core.any (fun row => match row with
            | .expression [.symbol "=", .expression (.symbol head :: _), _] => head == name
            | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => head == name
            | _ => false) then
        .symbol "Grounded"
      else .symbol "Symbol"

/-- The public string library reports refusals as values carrying the exact
public operation and its arguments. -/
def stringError (head : String) (arguments : List Atom) (reason : Atom) : Atom :=
  .expression [.symbol "Error", .expression (.symbol head :: arguments), reason]

/-- A scalar is either a valid integer codepoint or a one-codepoint String. -/
def codepoint : Atom → Option Char
  | .grounded (.int value) =>
      if 0 ≤ value then
        if valid : Char.isValidCharNat value.toNat then
          some ⟨UInt32.ofNatLT value.toNat (Char.isValidUInt32 _ valid),
            Char.isValidChar_of_isValidCharNat _ valid⟩
        else none
      else none
  | .grounded (.string value) =>
      match value.toList with
      | [character] => some character
      | _ => none
  | _ => none

/-- Retain the first invalid codepoint's position. -/
def codepoints (position : Nat) : List Atom → Except Nat (List Char)
  | [] => .ok []
  | first :: rest =>
      match codepoint first with
      | none => .error position
      | some character => (character :: ·) <$> codepoints (position + 1) rest

def stringOperation (head : String) (arguments : List Atom) : Atom :=
  let failure := stringError head arguments
  let expected := fun message => failure (.symbol message)
  match head, arguments with
  | "str:byte-length", [value] =>
      match ByteString.text value with
      | some bytes => .grounded (.int bytes.length)
      | none => expected "expected text argument"
  | "str:byte-slice", [value, .grounded (.int first), .grounded (.int last)] =>
      match ByteString.text value with
      | some bytes =>
          if first < 0 ∨ last < 0 then
            expected "expected text, non-negative start, non-negative end"
          else if first.toNat ≤ last.toNat ∧ last.toNat ≤ bytes.length then
            ByteString.encode ((bytes.drop first.toNat).take (last.toNat - first.toNat))
          else failure (.expression [.symbol "StrSliceOutsideTextV1", .grounded (.int bytes.length)])
      | none => expected "expected text, non-negative start, non-negative end"
  | "str:concat", [left, right] =>
      match ByteString.text left, ByteString.text right with
      | some first, some second => ByteString.encode (first ++ second)
      | _, _ => expected "expected two text arguments"
  | "str:join", [separator, .expression parts] =>
      match ByteString.text separator, parts.mapM ByteString.text with
      | some between, some chunks => ByteString.encode ((chunks.intersperse between).flatten)
      | _, _ => expected "expected separator and expression of text"
  | "str:from-codepoints", [.expression values] =>
      match codepoints 0 values with
      | .ok characters => .grounded (.string (String.ofList characters))
      | .error position =>
          failure (.expression [.symbol "StrNotACodepointV1", .grounded (.int position)])
  | "str:byte-slice", [_, _, _] =>
      expected "expected text, non-negative start, non-negative end"
  | "str:join", [_, _] => expected "expected separator and expression of text"
  | "str:from-codepoints", [_] => expected "expected a list of codepoints"
  | _, _ => expected "wrong number of arguments"

/-- Reuse the existing reader before its lossy Pattern lowering. Only an exact
single atom is returned; successful source reading is a separate boundary from
native parser correctness. -/
def parseAtom (value : Atom) : Except Fault Atom := do
  let text ← match value with
    | .symbol text | .grounded (.string text) => .ok text
    | .grounded (.int value) => .ok (toString value)
    | _ => .error (.invalidArguments "parse")
  let expression ← (Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
    MeTTailCore.MeTTaSyntax.petta text).mapError fun _ => Fault.invalidArguments "parse"
  SpaceSemantics.readExpression expression |>.mapError fun _ => Fault.invalidArguments "parse"

/-- Dynamic parsing uses the same occurrence-binding boundary as source
loading. A successful result has no unexpanded anonymous marker. -/
theorem parseAtom_no_marker {value atom : Atom} (parsed : parseAtom value = .ok atom) :
    "_" ∉ Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars atom := by
  have text_case (text : String)
      (success : (do
        let expression ← (Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
          MeTTailCore.MeTTaSyntax.petta text).mapError fun _ => Fault.invalidArguments "parse"
        SpaceSemantics.readExpression expression |>.mapError fun _ => Fault.invalidArguments "parse") =
          .ok atom) : "_" ∉ Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars atom := by
    cases lexical : (Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
        MeTTailCore.MeTTaSyntax.petta text).mapError (fun _ => Fault.invalidArguments "parse") with
    | error reason => simp only [lexical,bind,Except.bind] at success; cases success
    | ok expression =>
        simp only [lexical,bind,Except.bind] at success
        cases converted : SpaceSemantics.readExpression expression with
        | error reason => simp only [converted,Except.mapError] at success; cases success
        | ok raw =>
            have same : raw = atom := Except.ok.inj (by
              simpa only [converted,Except.mapError] using success)
            cases same
            exact SpaceSemantics.readExpression_no_marker converted
  cases value with
  | symbol text => exact text_case text parsed
  | var | expression => simp only [parseAtom,bind,Except.bind] at parsed; cases parsed
  | grounded value =>
      cases value with
      | string text => exact text_case text parsed
      | int number => exact text_case (toString number) parsed
      | bool | custom => simp only [parseAtom,bind,Except.bind] at parsed; cases parsed

private def booleanBinary (state : State) (head : String)
    (operation : Bool → Bool → Bool) (arguments : List Atom) : Result :=
  match arguments with
  | [.grounded (.bool left), .grounded (.bool right)] => .ok (state, [boolean (operation left right)])
  | _ => .error (.invalidArguments head)

def apply (state : State) (head : String) (arguments : List Atom) : Result :=
  let answer := fun value => Except.ok (state, [value])
  let bad := Except.error (Fault.invalidArguments head)
  if head == "and" then
    booleanBinary state head (fun left right => left && right) arguments
  else if head == "or" then
    booleanBinary state head (fun left right => left || right) arguments
  else
    match head, arguments with
    | "+", [.grounded (.int left), .grounded (.int right)] =>
        answer (.grounded (.int (left + right)))
    | "-", [.grounded (.int left), .grounded (.int right)] =>
        answer (.grounded (.int (left - right)))
    | "*", [.grounded (.int left), .grounded (.int right)] =>
        answer (.grounded (.int (left * right)))
    | "%", [.grounded (.int left), .grounded (.int right)] =>
        if right = 0 then .error .zeroDivisor else answer (.grounded (.int (left.fmod right)))
    | "<", [.grounded (.int left), .grounded (.int right)] => answer (boolean (left < right))
    | "<=", [.grounded (.int left), .grounded (.int right)] => answer (boolean (left ≤ right))
    | ">", [.grounded (.int left), .grounded (.int right)] => answer (boolean (left > right))
    | ">=", [.grounded (.int left), .grounded (.int right)] => answer (boolean (left ≥ right))
    | "==", [left, right] => answer (boolean (left == right))
    | "not", [.grounded (.bool value)] => answer (boolean (!value))
    | "cons", [first, .expression rest] => answer (.expression (first :: rest))
    | "cons-atom", [first, .expression rest] => answer (.expression (first :: rest))
    | "union-atom", [.expression left, .expression right] =>
        answer (.expression (left ++ right))
    | "unique-atom", [.expression items] => answer (.expression items.eraseDups)
    | "unique-atom", [.symbol _] | "unique-atom", [.grounded _] => answer (.expression [])
    | "superpose", [.expression items] => .ok (state, items)
    | "superpose", [.symbol _] | "superpose", [.grounded _] => .ok (state, [])
    | "sort-atom", [.expression items] | "msort", [.expression items] =>
        match sortClosed items with
        | some sorted => answer (.expression sorted)
        | none => bad
    | "sort-atom", [.symbol _] | "sort-atom", [.grounded _] => answer (.expression [])
    | "size-atom", [.expression items] => answer (.grounded (.int items.length))
    | "size-atom", [_] => answer (.expression [])
    | "index-atom", [.expression items, .grounded (.int index)] =>
        if index < 0 then .ok (state, [])
        else .ok (state, (items[index.toNat]?).toList)
    | "reverse", [.expression items] => answer (.expression items.reverse)
    | "is-member", [value, .expression items] => .ok (state, membershipAnswers value items)
    | "get-metatype", [value] => answer (metatype state value)
    | "get-type", [.grounded (.int _)] => answer (.symbol "Number")
    | "get-type", [.grounded (.string _)] => answer (.symbol "String")
    | "get-type", [.grounded (.bool _)] => answer (.symbol "Bool")
    | "str:byte-length", _ | "str:byte-slice", _ | "str:concat", _
    | "str:join", _ | "str:from-codepoints", _ => answer (stringOperation head arguments)
    | "parse", [value] =>
        match parseAtom value with
        | .ok parsed => answer parsed
        | .error fault => .error fault
    | "new-space", [] =>
        let (handle, after) := state.allocate []
        .ok (after, [handleValue handle])
    | "add-atom", [location, atom] =>
        match readHandle location >>= fun handle => insert state handle atom with
        | some after => .ok (after, [boolean true])
        | none => .error .invalidSpace
    | "remove-atom", [location, atom] =>
        match readHandle location with
        | none => .error .invalidSpace
        | some handle =>
            match state.read handle with
            | none => .error .invalidSpace
            | some _ =>
                match atom with
                | .var _ => answer (boolean true)
                | .expression (_ :: _) =>
                    match erase state handle atom with
                    | some after => .ok (after, [boolean true])
                    | none => .error .invalidSpace
                | _ => .ok (state, [])
    | "get-atoms", [location] =>
        match readHandle location >>= state.read with
        | some rows => .ok (state, rows)
        | none => .error .invalidSpace
    | "match", [location, pattern, template] =>
        match readHandle location >>= state.read with
        | some rows => .ok (state, query rows pattern template)
        | none => .error .invalidSpace
    | "change-state!", [.symbol name, value] =>
        .ok (state.putCell name value, [boolean true])
    | "get-state", [.symbol name] =>
        match state.cells name with
        | some value => answer value
        | none => .error (.missingCell name)
    | _, _ => bad

/-! ## Positive and negative primitive controls -/

theorem structural_equality (state : State) (left right : Atom) :
    apply state "==" [left, right] = .ok (state, [boolean (left == right)]) := rfl

theorem native_cons (state : State) (first : Atom) (rest : List Atom) :
    apply state "cons-atom" [first, .expression rest] = .ok (state, [.expression (first :: rest)]) := rfl

theorem string_list_sort (state : State) (items : List String) :
    apply state "sort-atom" [.expression (stringAtoms items)] =
      .ok (state, [.expression (stringAtoms (items.mergeSort (· ≤ ·)))]) := by
  simp [apply, sortClosed_strings]

theorem integer_list_sort (state : State) (items : List Int) :
    apply state "sort-atom" [.expression (integerAtoms items)] =
      .ok (state, [.expression (integerAtoms (items.mergeSort (· ≤ ·)))]) := by
  simp [apply, sortClosed_integers]

theorem integer_msort (state : State) (items : List Int) :
    apply state "msort" [.expression (integerAtoms items)] =
      .ok (state, [.expression (integerAtoms (items.mergeSort (· ≤ ·)))]) := by
  simp [apply, sortClosed_integers]

theorem msort_registered : known "msort" = true := by decide

theorem boolean_list_not_integer_admission :
    integers [boolean true] = none ∧ sortClosed [boolean true] = none := by decide

theorem integer_sort_keeps_duplicate_values (state : State) :
    apply state "msort" [.expression (integerAtoms [3, -2, 3, 1])] =
      .ok (state, [.expression (integerAtoms [-2, 1, 3, 3])]) := by
  rw [integer_msort]
  have sorted : ([3, -2, 3, 1] : List Int).mergeSort (· ≤ ·) = [-2, 1, 3, 3] := by
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (List.pairwise_mergeSort' (· ≤ ·) _) (by decide)
    exact (List.mergeSort_perm _ _).trans (by decide)
  rw [sorted]

theorem sorting_and_native_cons_registered : known "sort-atom" = true ∧ known "cons-atom" = true := by decide

theorem integer_addition (state : State) (left right : Int) :
    apply state "+" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [.grounded (.int (left + right))]) := rfl

theorem greater_comparison (state : State) (left right : Int) :
    apply state ">" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [boolean (left > right)]) := rfl

theorem greater_equal_comparison (state : State) (left right : Int) :
    apply state ">=" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [boolean (left ≥ right)]) := rfl

theorem greater_comparisons_registered : known ">" = true ∧ known ">=" = true := by decide

theorem strict_comparison_distinguishes_equality (state : State) (value : Int) :
    apply state ">" [.grounded (.int value), .grounded (.int value)] = .ok (state, [boolean false]) ∧
      apply state ">=" [.grounded (.int value), .grounded (.int value)] = .ok (state, [boolean true]) := by
  constructor <;> simp [apply, boolean]

theorem malformed_comparisons_fault (state : State) :
    apply state ">" [.symbol "not-a-number", .grounded (.int 0)] = .error (.invalidArguments ">") ∧
      apply state ">=" [.grounded (.int 0)] = .error (.invalidArguments ">=") := by
  constructor <;> rfl

theorem boolean_and (state : State) (left right : Bool) :
    apply state "and" [boolean left, boolean right] = .ok (state, [boolean (left && right)]) := rfl

theorem boolean_or (state : State) (left right : Bool) :
    apply state "or" [boolean left, boolean right] = .ok (state, [boolean (left || right)]) := rfl

/-- Registered closed-Boolean negation. Relational calls with unbound input
remain outside this ground primitive profile. -/
theorem boolean_not (state : State) (value : Bool) :
    apply state "not" [boolean value] = .ok (state, [boolean (!value)]) := rfl

theorem boolean_not_registered : known "not" = true := by decide

theorem boolean_not_true_is_one_false_answer (state : State) :
    apply state "not" [boolean true] = .ok (state, [boolean false]) ∧
      apply state "not" [boolean true] ≠ .ok (state, []) := by
  constructor
  · rfl
  · simp [boolean_not]

theorem boolean_calls_registered : known "and" = true ∧ known "or" = true := by decide

theorem boolean_malformed_calls_fault (state : State) :
    apply state "and" [boolean false, .grounded (.int 0)] = .error (.invalidArguments "and") ∧
      apply state "or" [boolean true] = .error (.invalidArguments "or") := by
  constructor <;> rfl

theorem reverse_returns_expression (state : State) (items : List Atom) :
    apply state "reverse" [.expression items] = .ok (state, [.expression items.reverse]) := rfl

theorem expression_metatype (state : State) (items : List Atom) :
    apply state "get-metatype" [.expression items] = .ok (state, [.symbol "Expression"]) := rfl

theorem integer_type_is_number (state : State) (value : Int) :
    apply state "get-type" [.grounded (.int value)] = .ok (state, [.symbol "Number"]) := rfl

theorem string_type_is_string (state : State) (value : String) :
    apply state "get-type" [.grounded (.string value)] = .ok (state, [.symbol "String"]) := rfl

theorem empty_membership_is_false (state : State) (value : Atom) :
    apply state "is-member" [value, .expression []] = .ok (state, [boolean false]) := rfl

theorem duplicate_membership_retains_answers (state : State) :
    apply state "is-member" [.grounded (.string "x"),
      .expression [.grounded (.string "x"), .grounded (.string "y"), .grounded (.string "x")]] =
      .ok (state, [boolean true, boolean true]) := rfl

theorem string_byte_length (state : State) (bytes : List UInt8) :
    apply state "str:byte-length" [ByteString.encode bytes] =
      .ok (state, [.grounded (.int bytes.length)]) := by
  simp [apply, stringOperation]

theorem string_byte_slice (state : State) (bytes : List UInt8) (first last : Nat)
    (ordered : first ≤ last) (bounded : last ≤ bytes.length) :
    apply state "str:byte-slice"
      [ByteString.encode bytes, .grounded (.int first), .grounded (.int last)] =
      .ok (state, [ByteString.encode ((bytes.drop first).take (last - first))]) := by
  simp [apply, stringOperation, ordered, bounded]

theorem string_concat_bytes (state : State) (first second : List UInt8) :
    apply state "str:concat" [ByteString.encode first, ByteString.encode second] =
      .ok (state, [ByteString.encode (first ++ second)]) := by
  simp [apply, stringOperation]

theorem string_join_bytes (state : State) (separator : List UInt8) (chunks : List (List UInt8)) :
    apply state "str:join" [ByteString.encode separator, .expression (chunks.map ByteString.encode)] =
      .ok (state, [ByteString.encode ((chunks.intersperse separator).flatten)]) := by
  have decoded : (chunks.map ByteString.encode).mapM ByteString.text = some chunks := by
    induction chunks with
    | nil => rfl
    | cons first rest ih => simp [List.mapM_cons, ih]
  simp [apply, stringOperation, decoded]

theorem partial_utf8_slice_is_preserved (state : State) :
    apply state "str:byte-slice" [.grounded (.string "λ"), .grounded (.int 0), .grounded (.int 1)] =
      .ok (state, [ByteString.encode [0xce]]) := by rfl

theorem multibyte_and_nul_lengths (state : State) :
    apply state "str:byte-length" [.grounded (.string "λ")] =
        .ok (state, [.grounded (.int 2)]) ∧
      apply state "str:byte-length" [.grounded (.string "a\x00b")] =
        .ok (state, [.grounded (.int 3)]) := by constructor <;> rfl

theorem outside_string_slice_is_error (state : State) :
    apply state "str:byte-slice" [.grounded (.string "x"), .grounded (.int 0), .grounded (.int 2)] =
      .ok (state, [stringError "str:byte-slice"
        [.grounded (.string "x"), .grounded (.int 0), .grounded (.int 2)]
        (.expression [.symbol "StrSliceOutsideTextV1", .grounded (.int 1)])]) := rfl

theorem invalid_codepoint_is_error (state : State) :
    apply state "str:from-codepoints" [.expression [.grounded (.int 65), .grounded (.int 0xd800)]] =
      .ok (state, [stringError "str:from-codepoints"
        [.expression [.grounded (.int 65), .grounded (.int 0xd800)]]
        (.expression [.symbol "StrNotACodepointV1", .grounded (.int 1)])]) := rfl

theorem reader_returns_read_expression (state : State) (text : String)
    (expression : Algorithms.MeTTa.Simple.Parser.SExpr) (value : Atom)
    (parsed : Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
      MeTTailCore.MeTTaSyntax.petta text = .ok expression)
    (read : SpaceSemantics.readExpression expression = .ok value) :
    apply state "parse" [.grounded (.string text)] = .ok (state, [value]) := by
  simp [apply, parseAtom, bind, Except.bind, Except.mapError, parsed, read]

theorem reader_refuses_nontext (state : State) (items : List Atom) :
    apply state "parse" [.expression items] = .error (.invalidArguments "parse") := rfl

theorem missing_cell_is_fault (state : State) (name : String)
    (missing : state.cells name = none) :
    apply state "get-state" [.symbol name] = .error (.missingCell name) := by
  simp [apply, missing]

theorem zero_remainder_is_fault (state : State) (left : Int) :
    apply state "%" [.grounded (.int left), .grounded (.int 0)] = .error .zeroDivisor := by
  simp [apply]

theorem stored_false_is_an_answer (state : State) (name : String) :
    apply (state.putCell name (boolean false)) "get-state" [.symbol name] =
      .ok (state.putCell name (boolean false), [boolean false]) := by
  simp [apply]

/-- The remainder takes the divisor's sign, rather than using the nonnegative
Euclidean convention. -/
theorem remainder_takes_divisor_sign (state : State) :
    apply state "%" [.grounded (.int 7), .grounded (.int (-2))] =
        .ok (state, [.grounded (.int (-1))]) ∧
      apply state "%" [.grounded (.int (-7)), .grounded (.int 2)] =
        .ok (state, [.grounded (.int 1)]) := by
  constructor <;> rfl

/-- A spelling used by another dialect does not acquire a primitive meaning. -/
theorem floor_division_is_unregistered : known "//" = false := by
  decide

/-- On naturals with a positive divisor the convention does not matter: the
MM0 service's `mm0:nat-mod` sees ordinary natural-number remainder. Its
`mm0:nat-div` helper needs an authored definition of `//` to compute a quotient. -/
theorem natural_remainder (state : State) (left right : Nat) (positive : 0 < right) :
    apply state "%" [.grounded (.int left), .grounded (.int right)] =
        .ok (state, [.grounded (.int ((left % right : Nat) : Int))]) := by
  have nonzero : right ≠ 0 := positive.ne'
  simp [apply, nonzero, Int.fmod_eq_emod_of_nonneg, Int.natCast_emod]

/-! ## Cell support of successful primitives -/

open NamedSpaces.Store

/-- Successful calls outside the four mutable primitives retain the entire
store, including all private spaces and named cells. -/
theorem successful_apply_state {state after : State} {head : String}
    {arguments answers : List Atom}
    (notNew : head ≠ "new-space") (notAdd : head ≠ "add-atom")
    (notRemove : head ≠ "remove-atom") (notChange : head ≠ "change-state!")
    (returned : apply state head arguments = .ok (after, answers)) : after = state := by
  unfold apply booleanBinary at returned
  repeat' first
    | split at returned
    | contradiction
    | solve
        | cases returned
          rfl

theorem successful_apply_cell_update {state after : State} {head : String}
    {arguments answers : List Atom}
    (returned : apply state head arguments = .ok (after, answers)) :
    after.cells = state.cells ∨ ∃ name value,
      head = "change-state!" ∧ arguments = [.symbol name, value] ∧
        after = state.putCell name value := by
  unfold apply booleanBinary at returned
  repeat' first
    | split at returned
    | contradiction
    | solve
        | cases returned
          exact Or.inl rfl
        | cases returned
          exact Or.inr ⟨_, _, rfl, rfl, rfl⟩
        | exact Or.inl (insert_preserves_cells (by assumption))
        | exact Or.inl (erase_preserves_cells (by assumption))
  all_goals cases returned
  · have same := congrArg (fun pair : NamedSpaces.Handle × State => pair.2.cells)
      (by assumption : state.allocate [] = (_, _))
    exact Or.inl same.symm
  · rename_i location atom _ _ selectedAfter selected
    cases decoded : readHandle location with
    | none => simp [decoded] at selected
    | some handle =>
        simp only [decoded] at selected
        exact Or.inl (insert_preserves_cells selected)
  · exact Or.inl (erase_preserves_cells (by assumption))

theorem successful_apply_cells {state after : State} {head : String}
    {arguments answers : List Atom}
    (returned : apply state head arguments = .ok (after, answers)) :
    after.cells = state.cells ∨ ∃ name value, after = state.putCell name value := by
  rcases successful_apply_cell_update returned with same | ⟨name, value, _, _, updated⟩
  · exact Or.inl same
  · exact Or.inr ⟨name, value, updated⟩

theorem successful_apply_finite_cells {state after : State} {head : String}
    {arguments answers : List Atom} (finite : FiniteCells state)
    (returned : apply state head arguments = .ok (after, answers)) : FiniteCells after := by
  rcases successful_apply_cells returned with same | ⟨name, value, rfl⟩
  · exact finiteCells_of_same_cells finite same
  · exact putCell_finiteCells finite name value

theorem successful_apply_empty_tail {state after : State} {head : String}
    {arguments answers : List Atom} (vacant : EmptyTail state [])
    (returned : apply state head arguments = .ok (after, answers)) : EmptyTail after [] := by
  unfold apply booleanBinary at returned
  repeat' first
    | split at returned
    | contradiction
    | solve
        | cases returned
          exact vacant
        | exact insert_preserves_empty_tail vacant (by assumption)
        | exact erase_preserves_empty_tail vacant (by assumption)
  all_goals cases returned
  · have same := congrArg (fun pair : NamedSpaces.Handle × State => pair.2)
      (by assumption : state.allocate [] = (_, _))
    change (state.allocate []).2 = after at same
    rw [← same]
    exact allocate_emptyTail vacant
  · rename_i location atom _ _ selectedAfter selected
    cases decoded : readHandle location with
    | none => simp [decoded] at selected
    | some handle =>
        simp only [decoded] at selected
        exact insert_preserves_empty_tail vacant selected
  · exact erase_preserves_empty_tail vacant (by assumption)

/-! ## Logical-variable support of primitive replies

These laws belong with the primitive definitions. Their constructor cases are
generated in the defining module, so clients can use the checked law without
regenerating the large dispatcher splitter. Parsing, row enumeration and match
have their own scoped import/unification boundaries in the unifying machine.
-/

open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)

private def VarsWithin (allowed : String → Prop) (term : Atom) : Prop :=
  ∀ key ∈ atomFreeVars term, allowed key

private theorem freeVars_expression_mem {key : String} {items : List Atom} :
    key ∈ atomFreeVars (.expression items) ↔ ∃ item ∈ items, key ∈ atomFreeVars item := by
  simp only [atomFreeVars]
  induction items with
  | nil => simp [atomFreeVars.atomFreeVarsList]
  | cons first rest ih =>
      simp only [atomFreeVars.atomFreeVarsList,List.mem_append,ih,List.mem_cons,exists_eq_or_imp]

theorem variable_support_expression (allowed : String → Prop) (items : List Atom) :
    VarsWithin allowed (.expression items) ↔ ∀ item ∈ items, VarsWithin allowed item := by
  constructor
  · intro all item member key present
    exact all key (freeVars_expression_mem.mpr ⟨item,member,present⟩)
  · intro all key present
    obtain ⟨item,member,present⟩ := freeVars_expression_mem.mp present
    exact all item member key present

@[simp] private theorem variable_support_symbol (allowed : String → Prop) (name : String) :
    VarsWithin allowed (.symbol name) := by simp [VarsWithin,atomFreeVars]

@[simp] private theorem variable_support_grounded (allowed : String → Prop) (value : GroundedValue) :
    VarsWithin allowed (.grounded value) := by simp [VarsWithin,atomFreeVars]

private theorem bool_variable_support (allowed : String → Prop) (value : Bool) :
    VarsWithin allowed (boolean value) := variable_support_grounded _ _

theorem handle_variable_support (allowed : String → Prop) (handle : NamedSpaces.Handle) :
    VarsWithin allowed (handleValue handle) := by cases handle <;> simp [handleValue]

theorem byte_string_variable_support (allowed : String → Prop) (bytes : List UInt8) :
    VarsWithin allowed (ByteString.encode bytes) := by
  unfold ByteString.encode
  split <;> exact variable_support_grounded _ _

theorem metatype_variable_support (allowed : String → Prop) (state : State) (term : Atom) :
    VarsWithin allowed (metatype state term) := by
  cases term <;> simp [metatype]
  split <;> exact variable_support_symbol _ _

theorem string_error_variable_support (allowed : String → Prop) (head : String) (arguments : List Atom)
    (inputs : ∀ term ∈ arguments, VarsWithin allowed term) (reason : Atom) (reasonGood : VarsWithin allowed reason) :
    VarsWithin allowed (stringError head arguments reason) := by
  simpa [stringError,variable_support_expression] using And.intro inputs reasonGood

theorem string_operation_variable_support (allowed : String → Prop) (head : String) (arguments : List Atom)
    (inputs : ∀ term ∈ arguments, VarsWithin allowed term) : VarsWithin allowed (stringOperation head arguments) := by
  unfold stringOperation
  repeat' first
    | split
    | exact variable_support_grounded _ _
    | exact byte_string_variable_support _ _
    | exact string_error_variable_support allowed _ _ inputs _ (variable_support_symbol _ _)
    | solve
        | apply string_error_variable_support allowed _ _ inputs
          simp [variable_support_expression]

theorem membership_variable_support (allowed : String → Prop) (value : Atom) (items : List Atom) :
    ∀ answer ∈ membershipAnswers value items, VarsWithin allowed answer := by
  unfold membershipAnswers
  split <;> simp [boolean]

theorem sorting_variable_support (allowed : String → Prop) (items sorted : List Atom)
    (selected : sortClosed items = some sorted) : ∀ term ∈ sorted, VarsWithin allowed term := by
  unfold sortClosed at selected
  split at selected
  · cases selected
    simp [stringAtoms]
  · obtain ⟨numbers,_,same⟩ := Option.map_eq_some_iff.mp selected
    cases same
    simp [integerAtoms]

private theorem boolean_binary_variable_support (allowed : String → Prop) (state after : State)
    (head : String) (operation : Bool → Bool → Bool) (arguments answers : List Atom)
    (returned : booleanBinary state head operation arguments = .ok (after,answers)) :
    ∀ answer ∈ answers, VarsWithin allowed answer := by
  unfold booleanBinary at returned
  split at returned
  · cases returned
    simp [boolean]
  · cases returned

private theorem append_expression_variable_support (allowed : String → Prop) (left right : List Atom)
    (inputs : ∀ term ∈ [Atom.expression left,Atom.expression right], VarsWithin allowed term) :
    VarsWithin allowed (.expression (left ++ right)) := by
  apply (variable_support_expression allowed _).mpr
  have leftGood := (variable_support_expression allowed left).mp (inputs _ (by simp))
  have rightGood := (variable_support_expression allowed right).mp (inputs _ (by simp))
  intro term member
  rcases List.mem_append.mp member with present | present
  · exact leftGood term present
  · exact rightGood term present

private theorem indexing_variable_support (allowed : String → Prop) (items : List Atom) (index : Nat)
    (itemsGood : ∀ term ∈ items, VarsWithin allowed term) :
    ∀ term ∈ (items[index]?).toList, VarsWithin allowed term := by
  intro term member
  exact itemsGood term (List.mem_of_getElem? (Option.mem_toList.mp member))

theorem successful_apply_variable_support (allowed : String → Prop) (state after : State)
    (head : String) (arguments answers : List Atom)
    (inputs : ∀ term ∈ arguments, VarsWithin allowed term)
    (cells : ∀ name value, state.cells name = some value → VarsWithin allowed value)
    (notParse : head ≠ "parse") (notRows : head ≠ "get-atoms") (notMatch : head ≠ "match")
    (returned : apply state head arguments = .ok (after,answers)) :
    ∀ answer ∈ answers, VarsWithin allowed answer := by
  delta apply at returned
  repeat' first
    | contradiction
    | solve
        | exact boolean_binary_variable_support allowed _ _ _ _ _ _ returned
        | cases returned
          simp_all [variable_support_expression,boolean]
        | cases returned
          exact membership_variable_support _ _ _
        | cases returned
          simpa using metatype_variable_support allowed _ _
        | cases returned
          simpa using string_operation_variable_support allowed _ _ inputs
        | cases returned
          intro value member
          simp only [List.mem_singleton] at member
          subst value
          exact cells _ _ (by assumption)
        | cases returned
          intro value member
          simp only [List.mem_singleton] at member
          subst value
          exact handle_variable_support allowed _
        | cases returned
          intro value member
          simp only [List.mem_singleton] at member
          subst value
          exact (variable_support_expression allowed _).mpr (sorting_variable_support _ _ _ (by assumption))
        | cases returned
          simpa using append_expression_variable_support allowed _ _ inputs
        | cases returned
          exact indexing_variable_support allowed _ _
            ((variable_support_expression allowed _).mp (inputs _ (by simp)))
    | split at returned


end Mettapedia.Languages.MeTTa.PeTTa.StdLib
