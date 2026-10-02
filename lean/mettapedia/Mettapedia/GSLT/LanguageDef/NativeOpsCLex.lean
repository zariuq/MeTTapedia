import Mettapedia.GSLT.LanguageDef.NativeOpsSyntax

/-!
# Lexing the emitted native C fragment

Tokens retain character lists, avoiding opaque UTF-8 reconstruction during
artifact checking. The fragment includes decimal numerals, identifiers,
punctuation, unescaped quoted include paths and C comments. Unsupported
characters and unfinished quoted paths or comments are refused. This is the
required generated fragment, rather than the whole C preprocessing language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

inductive Token where
  | identifier (characters : List Char)
  | number (characters : List Char)
  | quoted (characters : List Char)
  | punctuation (characters : List Char)
  deriving DecidableEq, Repr

inductive LexFault where
  | character | escape | unfinishedQuoted | unfinishedComment
  deriving DecidableEq, Repr

inductive LexMode where
  | idle | identifier | number | quoted | slash | lineComment | blockComment | commentStar
  | pair (first : Char)
  deriving DecidableEq, Repr

structure LexState where
  mode : LexMode := .idle
  currentRev : List Char := []
  tokensRev : List Token := []
  fault : Option LexFault := none
  deriving DecidableEq, Repr

def initial : LexState := {}

def letter (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '_'

def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def whitespace (c : Char) : Bool := [' ', '\t', '\n', '\r', '\x0b', '\x0c'].contains c

def punctuation (c : Char) : Bool :=
  ['(', ')', '{', '}', '[', ']', '.', ',', ';', ':', '?', '#', '~'].contains c

def pairedFirst (c : Char) : Bool := ['-', '+', '=', '!', '<', '>', '&', '|', '*', '%', '^'].contains c

def pairAllowed (first second : Char) : Bool :=
  ((first == '-' && second == '>') ||
    (first == '+' && second == '+') ||
    (first == '-' && second == '-') ||
    (first == '<' && second == '<') ||
    (first == '>' && second == '>') ||
    (first == '&' && second == '&') ||
    (first == '|' && second == '|') ||
    (['-', '+', '=', '!', '<', '>', '&', '|', '*', '%', '^'].contains first && second == '='))

def emit (state : LexState) (token : Token) : LexState :=
  { state with mode := .idle, currentRev := [], tokensRev := token :: state.tokensRev }

def idle (state : LexState) (c : Char) : LexState :=
  if whitespace c then state
  else if letter c then { state with mode := .identifier, currentRev := [c] }
  else if digit c then { state with mode := .number, currentRev := [c] }
  else if c == '"' then { state with mode := .quoted, currentRev := [] }
  else if c == '/' then { state with mode := .slash }
  else if pairedFirst c then { state with mode := .pair c }
  else if punctuation c then emit state (.punctuation [c])
  else { state with fault := some .character }

def step (state : LexState) (c : Char) : LexState :=
  if state.fault.isSome then state
  else match state.mode with
    | .idle => idle state c
    | .identifier =>
        if letter c || digit c then { state with currentRev := c :: state.currentRev }
        else idle (emit state (.identifier state.currentRev.reverse)) c
    | .number =>
        if state.currentRev.head? == some 'u' || state.currentRev.head? == some 'U' then
          if letter c || digit c then { state with fault := some .character }
          else idle (emit state (.number state.currentRev.reverse)) c
        else if digit c then { state with currentRev := c :: state.currentRev }
        else if c == 'u' || c == 'U' then { state with currentRev := c :: state.currentRev }
        else if letter c then { state with fault := some .character }
        else idle (emit state (.number state.currentRev.reverse)) c
    | .quoted =>
        if c == '"' then emit state (.quoted state.currentRev.reverse)
        else if c == '\\' then { state with fault := some .escape }
        else if c < ' ' then { state with fault := some .character }
        else { state with currentRev := c :: state.currentRev }
    | .slash =>
        if c == '/' then { state with mode := .lineComment }
        else if c == '*' then { state with mode := .blockComment }
        else idle (emit state (.punctuation ['/'])) c
    | .lineComment => if c == '\n' then { state with mode := .idle } else state
    | .blockComment => if c == '*' then { state with mode := .commentStar } else state
    | .commentStar =>
        if c == '/' then { state with mode := .idle }
        else if c == '*' then state
        else { state with mode := .blockComment }
    | .pair first =>
        if pairAllowed first c then emit state (.punctuation [first, c])
        else idle (emit state (.punctuation [first])) c

def finish (state : LexState) : Except LexFault (List Token) :=
  match state.fault with
  | some fault => .error fault
  | none => match state.mode with
    | .idle | .lineComment => .ok state.tokensRev.reverse
    | .identifier => .ok ((.identifier state.currentRev.reverse) :: state.tokensRev).reverse
    | .number => .ok ((.number state.currentRev.reverse) :: state.tokensRev).reverse
    | .pair first => .ok ((.punctuation [first]) :: state.tokensRev).reverse
    | .slash => .ok ((.punctuation ['/']) :: state.tokensRev).reverse
    | .quoted => .error .unfinishedQuoted
    | .blockComment | .commentStar => .error .unfinishedComment

def lex (characters : List Char) : Except LexFault (List Token) :=
  finish (characters.foldl step initial)

theorem unsigned_suffix_retained : lex "0u;0U".toList = .ok
    [.number ['0', 'u'], .punctuation [';'], .number ['0', 'U']] := by decide +kernel

theorem mixed_unsigned_suffix_refused : lex "0u1".toList = .error .character := by decide +kernel

theorem scan_append (state : LexState) (first second : List Char) :
    (first ++ second).foldl step state = second.foldl step (first.foldl step state) :=
  List.foldl_append

theorem failed_step (state : LexState) (fault : LexFault)
    (failed : state.fault = some fault) (c : Char) : step state c = state := by
  simp [step, failed]

theorem failed_scan (state : LexState) (fault : LexFault)
    (failed : state.fault = some fault) (characters : List Char) :
    characters.foldl step state = state := by
  induction characters with
  | nil => rfl
  | cons c rest ih => simpa only [List.foldl_cons, failed_step state fault failed c] using ih

theorem segment_composition (state next final : LexState) (piece rest : List Char)
    (transition : piece.foldl step state = next)
    (tail : rest.foldl step next = final) :
    (piece ++ rest).foldl step state = final := by
  rw [scan_append, transition, tail]

theorem emitted_arrow_guard_tokens : lex "x->y>=UINT64_C(64)".toList = .ok
    [.identifier ['x'], .punctuation ['-', '>'], .identifier ['y'], .punctuation ['>', '='],
      .identifier "UINT64_C".toList, .punctuation ['('], .number ['6', '4'],
      .punctuation [')']] := by decide +kernel

theorem comments_separate_identifiers : lex "x/* kept apart */y// tail".toList =
    .ok [.identifier ['x'], .identifier ['y']] := by decide +kernel

theorem quoted_include_path : lex "#include \"native_ops.h\"".toList = .ok
    [.punctuation ['#'], .identifier "include".toList, .quoted "native_ops.h".toList] :=
  by decide +kernel

theorem unfinished_comment_refused : lex "x/*".toList = .error .unfinishedComment :=
  by decide +kernel

theorem unfinished_quote_refused : lex "\"path".toList = .error .unfinishedQuoted :=
  by decide +kernel

theorem unsupported_escape_refused : lex "\"a\\b\"".toList = .error .escape :=
  by decide +kernel

theorem nondecimal_number_refused : lex "0x10".toList = .error .character :=
  by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
