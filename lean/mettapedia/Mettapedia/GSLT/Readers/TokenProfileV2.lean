import Mettapedia.GSLT.Readers.TokenProfile

/-!
# Token profiles, version 2: delimiters, line comments, first and rest bytes

Version 1 (`TokenProfile`) cuts the source at separator bytes and gives every token sort one byte
set. That fits Metamath, whose tokens are whitespace-separated. MM0's formats need three more
things, all still data in a `.module` message:

* `Delimiters(B)`: a byte of `B` is a token by itself, wherever it stands: `(sort s)` is the four
  tokens `(`, `sort`, `s`, `)`;
* `LineComment(open)`: from `open` at the start of a token to the end of the line is trivia:
  `(sort s) -- note` is the four tokens of `(sort s)`;
* `Quoted(sort, open, close)`: an `open` byte starts a token of `sort` that runs to the next
  `close` byte, both included, whatever lies between: MM0's math strings `$ a -> b $` are one
  token each, and `--` inside them is no comment;
* `Class2(sort, first, rest)` and `Except(sort, spelling, …)`: a token of `sort` is one byte of
  `first`, then bytes of `rest`, and is none of the excepted spellings. MM0's identifiers are
  `Class2(id, [A-Za-z_], [A-Za-z0-9_])` with `Except(id, "_")`: `x1` is one, `1x` and `_` are not.

Version 1 is the special case with no delimiters, no line comment, and every class's first and
rest bytes the same set: `tokenize_ofV1` and `tokenHasSort_ofV1` show that a version-1 profile
read as version 2 gives exactly the same tokens and the same token sorts. So Metamath's reader is
unchanged when its engines move to version 2.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.TokenProfileV2

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet Fault codes dropComments name? byteSet?)

/-- A token sort: a first byte, then rest bytes, and none of the excepted spellings; with `final`,
the token has at least two bytes and its last byte is `final` (a quoted token is closed). -/
structure TokenClass where
  sort : String
  first : ByteSet
  rest : ByteSet
  excluded : List String
  final : Option Nat
  deriving DecidableEq, Repr

/-- A decoded version-2 profile. -/
structure Profile where
  start : String
  admissible : ByteSet
  separator : ByteSet
  delimiters : ByteSet
  lineComment : Option String
  bracketComment : Option (String × String)
  quote : Option (Nat × Nat)
  classes : List TokenClass
  deriving DecidableEq, Repr

/-! ## Reading the profile from the pattern a `.module` message returns -/

/-- One entry after `Start`, `Admissible` and `Separator`. -/
inductive Entry where
  | delimiters (set : ByteSet)
  | lineComment (opener : String)
  | class1 (sort : String) (set : ByteSet)
  | class2 (sort : String) (first rest : ByteSet)
  | except (sort : String) (spellings : List String)
  | comment (opener closer : String)
  | quoted (sort : String) (opener closer : Nat)

def names? : List Pattern → Option (List String)
  | [] => some []
  | p :: ps => do
      let head ← name? p
      let tail ← names? ps
      pure (head :: tail)

def entry? : Pattern → Option Entry
  | .apply "Delimiters" [set] => (byteSet? set).map .delimiters
  | .apply "LineComment" [opener] => (name? opener).map .lineComment
  | .apply "Class" [sort, set] => do
      let sort ← name? sort
      let set ← byteSet? set
      pure (.class1 sort set)
  | .apply "Class2" [sort, first, rest] => do
      let sort ← name? sort
      let first ← byteSet? first
      let rest ← byteSet? rest
      pure (.class2 sort first rest)
  | .apply "Except" (sort :: spellings) => do
      let sort ← name? sort
      let spellings ← names? spellings
      pure (.except sort spellings)
  | .apply "Quoted" [sort, opener, closer] => do
      let sort ← name? sort
      let opener ← name? opener >>= TokenProfile.natOfName?
      let closer ← name? closer >>= TokenProfile.natOfName?
      pure (.quoted sort opener closer)
  | .apply "Comment" [opener, closer] => do
      let opener ← name? opener
      let closer ← name? closer
      pure (.comment opener closer)
  | _ => none

def entries? : List Pattern → Option (List Entry)
  | [] => some []
  | p :: ps => do
      let head ← entry? p
      let tail ← entries? ps
      pure (head :: tail)

/-- The spellings excepted from a sort. -/
def exceptedFor (entries : List Entry) (sort : String) : List String :=
  entries.flatMap fun e => match e with
    | .except s spellings => if s == sort then spellings else []
    | _ => []

/-- The profile the entries describe. -/
def ofEntries (start : String) (admissible separator : ByteSet) (entries : List Entry) : Profile :=
  { start, admissible, separator,
    delimiters := entries.foldl (fun acc e => match e with
      | .delimiters set => .union acc set
      | _ => acc) (.points []),
    lineComment := entries.findSome? fun e => match e with
      | .lineComment opener => some opener
      | _ => none,
    quote := entries.findSome? fun e => match e with
      | .quoted _ opener closer => some (opener, closer)
      | _ => none,
    bracketComment := entries.findSome? fun e => match e with
      | .comment opener closer => some (opener, closer)
      | _ => none,
    classes := entries.filterMap fun e => match e with
      | .class1 sort set => some ⟨sort, set, set, exceptedFor entries sort, none⟩
      | .class2 sort first rest => some ⟨sort, first, rest, exceptedFor entries sort, none⟩
      | .quoted sort opener closer =>
          some ⟨sort, .points [opener], .minus (.union admissible separator) (.points [closer]),
            exceptedFor entries sort, some closer⟩
      | _ => none }

/-- `TokenProfileV2(Start(S), Admissible(B), Separator(B), ENTRY…)`. -/
def profile? : Pattern → Option Profile
  | .apply "TokenProfileV2" (.apply "Start" [start] :: .apply "Admissible" [admissible] ::
      .apply "Separator" [separator] :: rest) => do
      let start ← name? start
      let admissible ← byteSet? admissible
      let separator ← byteSet? separator
      let entries ← entries? rest
      pure (ofEntries start admissible separator entries)
  | _ => none

/-! ## Token sorts -/

def TokenClass.has (c : TokenClass) (token : List Nat) : Bool :=
  match token with
  | [] => false
  | b :: bs => c.first.contains b && !((c.excluded.map codes).contains token) &&
      match c.final with
      | none => bs.all c.rest.contains
      | some f => bs.getLast? == some f && bs.dropLast.all c.rest.contains

def Profile.classOf? (profile : Profile) (sort : String) : Option TokenClass :=
  match profile.classes.filter (fun c => c.sort == sort) with
  | [c] => some c
  | _ => none

def Profile.tokenHasSort (profile : Profile) (sort : String) (token : List Nat) : Bool :=
  match profile.classOf? sort with
  | some c => c.has token
  | none => false

/-! ## The meaning of a profile -/

/-- Cut bytes into tokens: a separator ends a token and is dropped; a delimiter byte ends a
token and is a token itself; a line comment opener at the start of a token makes the rest of the
line trivia (`inLine`). -/
def scan (separator delimiters : ByteSet) (line : List Nat) :
    Bool → Nat → List Nat → List Nat → Nat → List (Nat × List Nat)
  | _, _, current, [], start =>
      if current.isEmpty then [] else [(start, current.reverse)]
  | true, offset, current, byte :: rest, start =>
      if byte == 10 then scan separator delimiters line false (offset + 1) current rest start
      else scan separator delimiters line true (offset + 1) current rest start
  | false, offset, current, byte :: rest, start =>
      if separator.contains byte then
        let tail := scan separator delimiters line false (offset + 1) [] rest (offset + 1)
        if current.isEmpty then tail else (start, current.reverse) :: tail
      else if delimiters.contains byte then
        let here := (offset, [byte]) :: scan separator delimiters line false (offset + 1) [] rest (offset + 1)
        if current.isEmpty then here else (start, current.reverse) :: here
      else if current.isEmpty && !line.isEmpty && line.isPrefixOf (byte :: rest) then
        scan separator delimiters line true (offset + 1) [] rest (offset + 1)
      else
        scan separator delimiters line false (offset + 1) (byte :: current) rest
          (if current.isEmpty then offset else start)

/-- `scan` with quoted tokens (`inQuote`): an opening quote byte ends the current token and starts a
token that runs to the next closing quote byte, both included; inside it no byte is a separator, a
delimiter or a comment opener. With no quote bytes this is `scan` (`scanQ_none`). -/
def scanQ (separator delimiters : ByteSet) (line : List Nat) (quote : Option (Nat × Nat)) :
    Bool → Bool → Nat → List Nat → List Nat → Nat → List (Nat × List Nat)
  | _, _, _, current, [], start =>
      if current.isEmpty then [] else [(start, current.reverse)]
  | true, q, offset, current, byte :: rest, start =>
      if byte == 10 then scanQ separator delimiters line quote false q (offset + 1) current rest start
      else scanQ separator delimiters line quote true q (offset + 1) current rest start
  | false, true, offset, current, byte :: rest, start =>
      if quote.map (·.2) == some byte then
        (start, (byte :: current).reverse) ::
          scanQ separator delimiters line quote false false (offset + 1) [] rest (offset + 1)
      else scanQ separator delimiters line quote false true (offset + 1) (byte :: current) rest start
  | false, false, offset, current, byte :: rest, start =>
      if separator.contains byte then
        let tail := scanQ separator delimiters line quote false false (offset + 1) [] rest (offset + 1)
        if current.isEmpty then tail else (start, current.reverse) :: tail
      else if delimiters.contains byte then
        let here := (offset, [byte]) ::
          scanQ separator delimiters line quote false false (offset + 1) [] rest (offset + 1)
        if current.isEmpty then here else (start, current.reverse) :: here
      else if quote.map (·.1) == some byte then
        let tail := scanQ separator delimiters line quote false true (offset + 1) [byte] rest offset
        if current.isEmpty then tail else (start, current.reverse) :: tail
      else if current.isEmpty && !line.isEmpty && line.isPrefixOf (byte :: rest) then
        scanQ separator delimiters line quote true false (offset + 1) [] rest (offset + 1)
      else
        scanQ separator delimiters line quote false false (offset + 1) (byte :: current) rest
          (if current.isEmpty then offset else start)

theorem scanQ_none (separator delimiters : ByteSet) (line : List Nat) (inLine : Bool) (offset : Nat)
    (current bytes : List Nat) (start : Nat) :
    scanQ separator delimiters line none inLine false offset current bytes start =
      scan separator delimiters line inLine offset current bytes start := by
  induction bytes generalizing inLine offset current start with
  | nil => cases inLine <;> simp [scanQ, scan]
  | cons byte rest ih =>
      cases inLine with
      | true => simp only [scanQ, scan]; split <;> simp [ih]
      | false =>
          simp only [scanQ, scan, Option.map_none]
          split <;> simp [ih]

/-- The first byte that is no separator, no delimiter and not admissible. -/
def firstInadmissible (separator admissible delimiters : ByteSet) : Nat → List Nat → Option (Nat × Nat)
  | _, [] => none
  | offset, byte :: rest =>
      if separator.contains byte || admissible.contains byte || delimiters.contains byte then
        firstInadmissible separator admissible delimiters (offset + 1) rest
      else some (offset, byte)

/-- The significant tokens of a byte list, each with its start offset, or the first fault. -/
def tokenize (profile : Profile) (bytes : List Nat) : Except Fault (List (Nat × List Nat)) :=
  match firstInadmissible profile.separator profile.admissible profile.delimiters 0 bytes with
  | some (offset, byte) => .error (.inadmissibleByte offset byte)
  | none =>
      let tokens := scanQ profile.separator profile.delimiters
        (codes (profile.lineComment.getD "")) profile.quote false false 0 [] bytes 0
      match profile.bracketComment with
      | some (opener, closer) => dropComments (codes opener) (codes closer) false tokens
      | none => .ok tokens

/-! ## Version 1 is the special case -/

/-- A version-1 profile read as version 2. -/
def ofV1 (p : TokenProfile.Profile) : Profile :=
  { start := p.start, admissible := p.admissible, separator := p.separator,
    delimiters := .points [], lineComment := none,
    bracketComment := some (p.commentOpen, p.commentClose), quote := none,
    classes := p.classes.map fun (sort, set) => ⟨sort, set, set, [], none⟩ }

theorem points_nil_contains (b : Nat) : (ByteSet.points []).contains b = false := by
  simp [ByteSet.contains, ByteSet.members]

/-- With no delimiter and no line comment, the scan is version 1's `runs`. -/
theorem scan_eq_runs (separator : ByteSet) (offset : Nat) (current bytes : List Nat) (start : Nat) :
    scan separator (.points []) [] false offset current bytes start =
      TokenProfile.runs separator offset current bytes start := by
  induction bytes generalizing offset current start with
  | nil => simp [scan, TokenProfile.runs]
  | cons byte rest ih =>
      simp only [scan, TokenProfile.runs, points_nil_contains, List.isEmpty_nil, Bool.not_true,
        Bool.and_false, Bool.false_eq_true, if_false]
      split <;> simp [ih]

theorem firstInadmissible_ofV1 (p : TokenProfile.Profile) (offset : Nat) (bytes : List Nat) :
    firstInadmissible p.separator p.admissible (.points []) offset bytes =
      TokenProfile.firstInadmissible p offset bytes := by
  induction bytes generalizing offset with
  | nil => rfl
  | cons byte rest ih =>
      simp only [firstInadmissible, TokenProfile.firstInadmissible, points_nil_contains,
        Bool.or_false]
      split <;> simp_all

/-- A version-1 profile gives the same tokens and faults as version 2. -/
theorem tokenize_ofV1 (p : TokenProfile.Profile) (bytes : List Nat) :
    tokenize (ofV1 p) bytes = TokenProfile.tokenize p bytes := by
  simp only [tokenize, ofV1, TokenProfile.tokenize, firstInadmissible_ofV1, Option.getD_none]
  cases TokenProfile.firstInadmissible p 0 bytes with
  | some pair => rfl
  | none => simp [codes, scanQ_none, scan_eq_runs]

theorem classOf_ofV1 (p : TokenProfile.Profile) (sort : String) :
    (ofV1 p).classOf? sort = (p.classOf? sort).map fun set => ⟨sort, set, set, [], none⟩ := by
  simp only [Profile.classOf?, ofV1, TokenProfile.Profile.classOf?]
  rw [List.filter_map]
  have : ((fun c : TokenClass => c.sort == sort) ∘ fun (x : String × ByteSet) =>
      (⟨x.1, x.2, x.2, [], none⟩ : TokenClass)) = fun entry => entry.1 == sort := rfl
  rw [this]
  split <;> rename_i h
  · simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at h
    obtain ⟨⟨s, set⟩, rest, hl, hc, hr⟩ := h
    subst hr
    simp only [hl, Option.map_some]
    have hs : s = sort := by
      have : (s, set) ∈ List.filter (fun entry => entry.1 == sort) p.classes := by simp [hl]
      simpa using (List.mem_filter.mp this).2
    simp_all
  · split <;> rename_i h'
    · simp_all
    · rfl

/-- A version-1 profile gives every token the same sorts as version 2. -/
theorem tokenHasSort_ofV1 (p : TokenProfile.Profile) (sort : String) (token : List Nat) :
    (ofV1 p).tokenHasSort sort token = p.tokenHasSort sort token := by
  simp only [Profile.tokenHasSort, TokenProfile.Profile.tokenHasSort, classOf_ofV1]
  cases p.classOf? sort with
  | none => rfl
  | some set =>
      cases token with
      | nil => rfl
      | cons b bs => simp [TokenClass.has, List.all_cons]

/-! ## Controls -/

private def demo : Profile :=
  { start := "file", admissible := .range 33 126, separator := .points [32, 10],
    delimiters := .points [40, 41], lineComment := some "--", bracketComment := none,
    quote := some (36, 36),
    classes := [⟨"id", .union (.union (.range 65 90) (.range 97 122)) (.points [95]),
               .union (.union (.union (.range 65 90) (.range 97 122)) (.range 48 57)) (.points [95]),
               ["_"], none⟩,
               ⟨"math", .points [36], .minus (.union (.range 33 126) (.points [32, 10])) (.points [36]), [],
               some 36⟩] }

/-- Positive control: delimiters split, a line comment runs to the end of its line. -/
theorem tokenize_delimiters_and_line_comment :
    tokenize demo (codes "(sort s) -- note\n(x1)") =
      .ok [(0, codes "("), (1, codes "sort"), (6, codes "s"), (7, codes ")"),
           (17, codes "("), (18, codes "x1"), (20, codes ")")] := by decide

/-- Negative control: a tab is no separator here, and not admissible. -/
theorem tokenize_refuses_tab : tokenize demo (codes "(sort\ts)") = .error (.inadmissibleByte 5 9) := by
  decide

/-- Quoted tokens: a math string is one token with its spaces, `--` inside it is no comment, and it
ends a glued identifier; an unclosed one is no token of the quoted sort. -/
theorem tokenize_quoted :
    tokenize demo (codes "ax $ a -- b $;") =
      .ok [(0, codes "ax"), (3, codes "$ a -- b $"), (13, codes ";")] ∧
    tokenize demo (codes "wff$ph$") = .ok [(0, codes "wff"), (3, codes "$ph$")] ∧
    demo.tokenHasSort "math" (codes "$ a -- b $") = true ∧
    demo.tokenHasSort "math" (codes "$ a") = false ∧ demo.tokenHasSort "math" (codes "$") = false := by
  decide

/-- Identifiers: `x1` is one; `1x` (a digit first) and `_` (excepted) are not. -/
theorem identifier_controls :
    demo.tokenHasSort "id" (codes "x1") = true ∧ demo.tokenHasSort "id" (codes "1x") = false ∧
      demo.tokenHasSort "id" (codes "_") = false ∧ demo.tokenHasSort "id" (codes "_a") = true := by
  decide

end Mettapedia.GSLT.Readers.TokenProfileV2
