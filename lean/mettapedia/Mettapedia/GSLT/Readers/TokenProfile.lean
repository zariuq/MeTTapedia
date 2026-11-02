import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Token profiles: the lexical layer of a two-level reader, as data in a `.module`

A two-level reader first cuts the source bytes into tokens and then parses the token list with
the grammar rows. The lexical layer is data that the presentation carries, read by a message
(`ReturnTokenProfile : (GetTokenProfile) ~> "TokenProfileV1"(…)`), in the convention of the
existing `LexicalProfile` theories:

* `Start(S)`: the start sort of the grammar;
* `Admissible(B)`: the bytes that may occur inside a token;
* `Separator(B)`: the bytes that separate tokens;
* `Class(sort, B)`: a token of the token sort `sort` is a nonempty run of bytes of `B`;
* `Comment(open, close)`: tokens from `open` to `close` are trivia; a token inside a comment may
  not contain `open` or `close` (comments do not nest).

A byte set `B` is `Range(lo, hi)`, `Points(b, …)`, `Union(B, …)` or `Minus(B, C)`.

`tokenize` is the meaning of a profile: the significant tokens of a byte list, or the first
lexical fault. Example: under Metamath's profile the bytes of `$( a $) $c x $.` give the tokens
`$c`, `x`, `$.`. Negative example: `$( a $( b $)` is refused (`nestedCommentOpen`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.TokenProfile

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A finite set of bytes, written the way the profile writes it. -/
inductive ByteSet where
  | range (lo hi : Nat)
  | points (members : List Nat)
  | union (left right : ByteSet)
  | minus (base removed : ByteSet)
  deriving DecidableEq, Repr

/-- The members of a byte set, in the order the profile writes them. -/
def ByteSet.members : ByteSet → List Nat
  | .range lo hi => (List.range (hi + 1 - lo)).map (lo + ·)
  | .points members => members
  | .union left right => left.members ++ right.members
  | .minus base removed => base.members.filter (fun b => !(removed.members.contains b))

def ByteSet.contains (set : ByteSet) (byte : Nat) : Bool := set.members.contains byte

/-- A decoded token profile. -/
structure Profile where
  start : String
  admissible : ByteSet
  separator : ByteSet
  classes : List (String × ByteSet)
  commentOpen : String
  commentClose : String
  deriving DecidableEq, Repr

/-! ## Reading the profile from the pattern a `.module` message returns -/

/-- Decimal digits, read without the runtime string-to-number primitive so that the kernel can
evaluate profile facts. -/
def digitsValue : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc => if c.isDigit then digitsValue cs (acc * 10 + (c.toNat - 48)) else none

def natOfName? (name : String) : Option Nat :=
  match name.toList with
  | [] => none
  | cs => digitsValue cs 0

/-- A constant `.apply name []`. -/
def name? : Pattern → Option String
  | .apply name [] => some name
  | _ => none

def naturals? : List Pattern → Option (List Nat)
  | [] => some []
  | p :: ps => do
      let n ← name? p >>= natOfName?
      let rest ← naturals? ps
      pure (n :: rest)

mutual
def byteSet? : Pattern → Option ByteSet
  | .apply "Range" [lo, hi] => do
      let lo ← name? lo >>= natOfName?
      let hi ← name? hi >>= natOfName?
      pure (.range lo hi)
  | .apply "Points" members => (naturals? members).map .points
  | .apply "Union" (first :: rest) => do
      let head ← byteSet? first
      let tail ← byteSets? rest
      pure (tail.foldl .union head)
  | .apply "Minus" [base, removed] => do
      let base ← byteSet? base
      let removed ← byteSet? removed
      pure (.minus base removed)
  | _ => none
def byteSets? : List Pattern → Option (List ByteSet)
  | [] => some []
  | p :: ps => do
      let head ← byteSet? p
      let tail ← byteSets? ps
      pure (head :: tail)
end

def class? : Pattern → Option (String × ByteSet)
  | .apply "Class" [sort, set] => do
      let sort ← name? sort
      let set ← byteSet? set
      pure (sort, set)
  | _ => none

def classes? : List Pattern → Option (List (String × ByteSet))
  | [] => some []
  | p :: ps => do
      let head ← class? p
      let tail ← classes? ps
      pure (head :: tail)

/-- `TokenProfileV1(Start(S), Admissible(B), Separator(B), Class(..)…, Comment(open, close))`. -/
def profile? : Pattern → Option Profile
  | .apply "TokenProfileV1" (.apply "Start" [start] :: .apply "Admissible" [admissible] ::
      .apply "Separator" [separator] :: rest) => do
      let start ← name? start
      let admissible ← byteSet? admissible
      let separator ← byteSet? separator
      match rest.reverse with
      | .apply "Comment" [openTok, closeTok] :: classesRev => do
          let classes ← classes? classesRev.reverse
          let commentOpen ← name? openTok
          let commentClose ← name? closeTok
          pure { start, admissible, separator, classes, commentOpen, commentClose }
      | _ => none
  | _ => none

/-- The byte set of a token sort, when the profile declares exactly one. -/
def Profile.classOf? (profile : Profile) (sort : String) : Option ByteSet :=
  match profile.classes.filter (fun entry => entry.1 == sort) with
  | [(_, set)] => some set
  | _ => none

/-- A token of the token sort: nonempty, and every byte in the sort's set. -/
def Profile.tokenHasSort (profile : Profile) (sort : String) (token : List Nat) : Bool :=
  match profile.classOf? sort with
  | some set => !token.isEmpty && token.all set.contains
  | none => false

/-! ## The meaning of a profile: significant tokens or the first fault -/

inductive Fault where
  | inadmissibleByte (offset byte : Nat)
  | nestedCommentOpen (offset : Nat)
  | commentBracketInsideToken (offset : Nat)
  | unclosedComment
  deriving DecidableEq, Repr

/-- Cut bytes into maximal runs of non-separator bytes, each with its start offset. -/
def runs (separator : ByteSet) : Nat → List Nat → List Nat → Nat → List (Nat × List Nat)
  | _, current, [], start =>
      if current.isEmpty then [] else [(start, current.reverse)]
  | offset, current, byte :: rest, start =>
      if separator.contains byte then
        let tail := runs separator (offset + 1) [] rest (offset + 1)
        if current.isEmpty then tail else (start, current.reverse) :: tail
      else
        runs separator (offset + 1) (byte :: current) rest (if current.isEmpty then offset else start)

/-- The codes of a spelling. Profiles spell brackets in ASCII, where codes and bytes coincide. -/
def codes (text : String) : List Nat := text.toList.map Char.toNat

/-- `needle` occurs in `haystack` as a contiguous piece. -/
def occursIn (needle haystack : List Nat) : Bool :=
  (List.range (haystack.length + 1)).any fun start => (haystack.drop start).take needle.length == needle

/-- Remove comments: from an `open` token to the next `close` token. -/
def dropComments (openTok closeTok : List Nat) :
    Bool → List (Nat × List Nat) → Except Fault (List (Nat × List Nat))
  | false, [] => .ok []
  | true, [] => .error .unclosedComment
  | false, (offset, token) :: rest =>
      if token == openTok then dropComments openTok closeTok true rest
      else do
        let tail ← dropComments openTok closeTok false rest
        pure ((offset, token) :: tail)
  | true, (offset, token) :: rest =>
      if token == closeTok then dropComments openTok closeTok false rest
      else if token == openTok then .error (.nestedCommentOpen offset)
      else if occursIn openTok token || occursIn closeTok token then
        .error (.commentBracketInsideToken offset)
      else dropComments openTok closeTok true rest

/-- The first byte that is neither a separator nor admissible. -/
def firstInadmissible (profile : Profile) : Nat → List Nat → Option (Nat × Nat)
  | _, [] => none
  | offset, byte :: rest =>
      if profile.separator.contains byte || profile.admissible.contains byte then
        firstInadmissible profile (offset + 1) rest
      else some (offset, byte)

/-- The significant tokens of a byte list, each with its start offset. -/
def tokenize (profile : Profile) (bytes : List Nat) : Except Fault (List (Nat × List Nat)) :=
  match firstInadmissible profile 0 bytes with
  | some (offset, byte) => .error (.inadmissibleByte offset byte)
  | none =>
      dropComments (codes profile.commentOpen) (codes profile.commentClose) false
        (runs profile.separator 0 [] bytes 0)

/-! ## Controls -/

private def demoProfile : Profile :=
  { start := "s", admissible := .range 33 126, separator := .points [32, 9, 10],
    classes := [("sym", .minus (.range 33 126) (.points [36]))],
    commentOpen := "$(", commentClose := "$)" }

/-- Positive control: comments are dropped and offsets kept. -/
theorem tokenize_drops_comment :
    tokenize demoProfile (codes "$( a $) $c x $.") =
      .ok [(8, codes "$c"), (11, codes "x"), (13, codes "$.")] := by decide

/-- Negative control: comments do not nest. -/
theorem tokenize_refuses_nested_comment :
    tokenize demoProfile (codes "$( a $( b $)") = .error (.nestedCommentOpen 5) := by decide

/-- Negative control: a comment bracket glued to other bytes inside a comment is refused. -/
theorem tokenize_refuses_glued_bracket :
    tokenize demoProfile (codes "$( a$) $)") = .error (.commentBracketInsideToken 3) := by decide

/-- Negative control: a control byte is not admissible. -/
theorem tokenize_refuses_control_byte :
    tokenize demoProfile [36, 99, 7] = .error (.inadmissibleByte 2 7) := by decide

theorem class_membership : demoProfile.tokenHasSort "sym" (codes "x") = true ∧
    demoProfile.tokenHasSort "sym" (codes "$c") = false := by decide

end Mettapedia.GSLT.Readers.TokenProfile
