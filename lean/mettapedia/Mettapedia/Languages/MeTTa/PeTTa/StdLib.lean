import Mettapedia.Languages.MeTTa.PeTTa.Effects
import Mettapedia.Languages.MeTTa.OSLFCore.ByteString

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
  head ∈ ["+", "-", "*", "%", "<", "<=", "==", "and", "or", "cons", "size-atom",
    "index-atom", "new-space", "add-atom", "remove-atom", "get-atoms", "match",
    "get-state", "change-state!", "reverse", "is-member", "get-metatype", "get-type",
    "str:byte-length", "str:byte-slice", "str:concat", "str:join", "str:from-codepoints",
    "parse"]

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
    | "==", [left, right] => answer (boolean (left == right))
    | "cons", [first, .expression rest] => answer (.expression (first :: rest))
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

theorem boolean_and (state : State) (left right : Bool) :
    apply state "and" [boolean left, boolean right] = .ok (state, [boolean (left && right)]) := rfl

theorem boolean_or (state : State) (left right : Bool) :
    apply state "or" [boolean left, boolean right] = .ok (state, [boolean (left || right)]) := rfl

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

end Mettapedia.Languages.MeTTa.PeTTa.StdLib
