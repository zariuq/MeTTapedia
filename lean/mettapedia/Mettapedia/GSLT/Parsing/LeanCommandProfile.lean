import Mettapedia.GSLT.Parsing.BoundedScheduler

/-!
# A declared grammar profile for Lean commands

The source is ordinary syntax-GSLT stream grammar data, compiled by the
existing guarded compiler and executed by its bounded scheduler. Readback
keeps applications, parentheses, arrow spellings, documentation and complete
declaration fields. Identifier reservation is checked against the supplied
token inventory. This profile uses single-line expressions and equally
indented simple structure fields. Unsupported command forms remain outside
this profile.

Scheduler success carries a derivation and replay certificate. An empty
bounded result is not asserted to prove unbounded rejection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LeanCommandProfile

open CompilerCorrespondence (SourceSymbol ParseTree Codepoint)
open GuardCorrespondence

inductive Expression where
  | identifier (name : String)
  | prop
  | type
  | application (function : Expression) (arguments : List Expression)
  | arrow (spelling : String) (domain codomain : Expression)
  | parenthesized (body : Expression)
  deriving Repr

structure Field where
  name : String
  type : Option Expression
  deriving Repr

inductive Command where
  | namespace_ (name : String)
  | section_ (name : Option String)
  | end_ (name : Option String)
  | open_ (isScoped : Bool) (names : List String)
  | import_ (name : String)
  | moduleDoc (text : String)
  | abbrev_ (documentation : Option String) (name : String) (type : Option Expression) (value : Expression)
  | inductive_ (documentation : Option String) (name : String) (type : Option Expression)
      (hasWhere : Bool) (constructors : List Field) (derivingClasses : List String)
  | structure_ (documentation : Option String) (name : String) (type : Option Expression)
      (fields : List Field) (derivingClasses : List String)
  deriving Repr

def scalars (text : String) : List Nat := text.toList.map Char.toNat
def literal (text : String) : List SourceSymbol := (scalars text).map SourceSymbol.exact
def call (name : String) : SourceSymbol := .call name

def rule (name category : String) (symbols : List SourceSymbol) : SourceRule :=
  ⟨name, category, symbols, []⟩

def asciiLetters : List Nat := (List.range 26).map (· + 65) ++ (List.range 26).map (· + 97)
def greekLetters : List Nat := (List.range 17).map (· + 0x391) ++ (List.range 7).map (· + 0x3A3) ++
  (List.range 25).map (· + 0x3B1)
def letters : List Nat := asciiLetters ++ greekLetters
def continuations : List Nat := letters ++ (List.range 10).map (· + 48) ++ [95, 39]

def characterRules (category : String) (characters : List Nat) : List SourceRule :=
  characters.map fun character => rule (category ++ "." ++ toString character) category [.exact character]

def presentation : SourceDefinition where
  start := "root"
  rules :=
    [⟨"root", "root", [call "ws", call "command", call "ws"], [.atEnd]⟩,
     rule "ws.empty" "ws" [],
     rule "ws.more" "ws" [call "space", call "ws"],
     rule "ws.one" "ws1" [call "space", call "ws"],
     rule "segment.letter" "segment" [call "letter", call "tail"],
     rule "segment.underscore" "segment" [.exact 95, call "continuation", call "tail"],
     rule "tail.empty" "tail" [],
     rule "tail.more" "tail" [call "continuation", call "tail"],
     rule "identifier" "identifier" [call "segment", call "qualifiedTail"],
     rule "qualified.empty" "qualifiedTail" [],
     rule "qualified.more" "qualifiedTail" [.exact 46, call "segment", call "qualifiedTail"],
     rule "names" "names" [call "identifier", call "namesTail"],
     rule "names.empty" "namesTail" [],
     rule "names.more" "namesTail" [call "ws1", call "identifier", call "namesTail"],
     rule "comma.empty" "commaNames" [],
     rule "comma.more" "commaNames" ([call "ws"] ++ literal "," ++ [call "ws", call "identifier", call "commaNames"]),
     rule "atom.name" "atom" [call "identifier"],
     rule "atom.prop" "atom" (literal "Prop"),
     rule "atom.type" "atom" (literal "Type"),
     rule "atom.paren" "atom" (literal "(" ++ [call "ws", call "expression", call "ws"] ++ literal ")"),
     rule "application" "application" [call "atom", call "arguments"],
     rule "arguments.empty" "arguments" [],
     rule "arguments.more" "arguments" [call "ws1", call "atom", call "arguments"],
     rule "expression.app" "expression" [call "application"],
     rule "expression.arrow" "expression" ([call "application", call "ws"] ++ literal "→" ++ [call "ws", call "expression"]),
     rule "expression.asciiArrow" "expression" ([call "application", call "ws"] ++ literal "->" ++ [call "ws", call "expression"]),
     rule "signature.empty" "signature" [],
     rule "signature.type" "signature" ([call "ws"] ++ literal ":" ++ [call "ws", call "expression"]),
     rule "comment.empty" "commentChars" [],
     rule "comment.more" "commentChars" [.any, call "commentChars"],
     rule "documentation" "documentation" (literal "/--" ++ [call "ws", call "commentChars"] ++ literal "-/"),
     rule "documented" "command" [call "documentation", call "ws", call "declaration"],
     rule "undocumented" "command" [call "declaration"],
     rule "namespace" "command" (literal "namespace" ++ [call "ws1", call "identifier"]),
     rule "section.empty" "command" (literal "section"),
     rule "section.named" "command" (literal "section" ++ [call "ws1", call "identifier"]),
     rule "end.empty" "command" (literal "end"),
     rule "end.named" "command" (literal "end" ++ [call "ws1", call "identifier"]),
     rule "open" "command" (literal "open" ++ [call "ws1", call "names"]),
     rule "open.scoped" "command" (literal "open" ++ [call "ws1"] ++ literal "scoped" ++ [call "ws1", call "names"]),
     rule "import" "command" (literal "import" ++ [call "ws1", call "identifier"]),
     rule "moduleDoc" "command" (literal "/-!" ++ [call "ws", call "commentChars"] ++ literal "-/"),
     rule "abbrev" "declaration" (literal "abbrev" ++ [call "ws1", call "identifier", call "signature", call "ws"] ++
       literal ":=" ++ [call "ws", call "expression"]),
     rule "where.empty" "where" [],
     rule "where.present" "where" ([call "ws1"] ++ literal "where"),
     rule "constructors.empty" "constructors" [],
     rule "constructors.more" "constructors" [call "ws", call "constructor", call "constructors"],
     rule "constructor" "constructor" (literal "|" ++ [call "ws", call "identifier", call "signature"]),
     rule "fields" "fields" [call "ws1", call "field", call "fieldsTail"],
     rule "fields.empty" "fieldsTail" [],
     rule "fields.more" "fieldsTail" [call "ws1", call "field", call "fieldsTail"],
     rule "field" "field" ([call "identifier", call "ws"] ++ literal ":" ++ [call "ws", call "expression"]),
     rule "deriving.empty" "deriving" [],
     rule "deriving.present" "deriving" ([call "ws1"] ++ literal "deriving" ++
       [call "ws1", call "identifier", call "commaNames"]),
     rule "inductive" "declaration" (literal "inductive" ++
       [call "ws1", call "identifier", call "signature", call "where", call "constructors", call "deriving"]),
     rule "structure" "declaration" (literal "structure" ++
       [call "ws1", call "identifier", call "signature", call "ws1"] ++ literal "where" ++ [call "fields", call "deriving"])] ++
    characterRules "letter" letters ++ characterRules "continuation" continuations ++ characterRules "space" [32, 9, 10, 13]

def grammar : CompiledGrammar := compile presentation

def leaves : ParseTree → List Nat
  | .terminal character => [character]
  | .node _ _ children => children.flatMap leaves

def text (tree : ParseTree) : String := String.ofList ((leaves tree).map Char.ofNat)

def childrenOf (category : String) : List ParseTree → List ParseTree :=
  List.filter fun tree => match tree with | .node _ name _ => name == category | _ => false

def child? (category : String) (children : List ParseTree) : Option ParseTree := (childrenOf category children).head?

mutual
  def expression : Nat → ParseTree → Option Expression
    | 0, _ => none
    | depth + 1, .node label _ children => do
        match label with
        | "atom.name" => return .identifier (text (← child? "identifier" children))
        | "atom.prop" => return .prop
        | "atom.type" => return .type
        | "atom.paren" => return .parenthesized (← expression depth (← child? "expression" children))
        | "application" =>
            let head ← expression depth (← child? "atom" children)
            let rest ← arguments depth (← child? "arguments" children)
            return if rest.isEmpty then head else .application head rest
        | "expression.app" => expression depth (← child? "application" children)
        | "expression.arrow" | "expression.asciiArrow" =>
            return .arrow (if label == "expression.arrow" then "→" else "->")
              (← expression depth (← child? "application" children))
              (← expression depth (← child? "expression" children))
        | _ => none
    | _, _ => none
  def arguments : Nat → ParseTree → Option (List Expression)
    | 0, _ => none
    | _ + 1, .node "arguments.empty" _ _ => some []
    | depth + 1, .node "arguments.more" _ children => do
        return (← expression depth (← child? "atom" children)) ::
          (← arguments depth (← child? "arguments" children))
    | _, _ => none
end

def signature (depth : Nat) : ParseTree → Option (Option Expression)
  | .node "signature.empty" _ _ => some none
  | .node "signature.type" _ children => do return some (← expression depth (← child? "expression" children))
  | _ => none

def names : Nat → ParseTree → Option (List String)
  | 0, _ => none
  | _ + 1, .node "names.empty" _ _ | _ + 1, .node "comma.empty" _ _ => some []
  | depth + 1, .node label _ children => do
      unless ["names", "names.more", "comma.more"].contains label do none
      let name := text (← child? "identifier" children)
      let rest ← names depth (← (child? "namesTail" children).orElse (fun _ => child? "commaNames" children))
      return name :: rest
  | _, _ => none

def fields (depth : Nat) (category : String) : ParseTree → Option (List Field)
  | .node label _ children => do
      if label == "constructors.empty" || label == "fields.empty" then return []
      let field ← child? category children
      let .node _ _ parts := field | none
      let name := text (← child? "identifier" parts)
      let type ← if category == "constructor" then (child? "signature" parts).bind (signature depth)
        else (child? "expression" parts).bind (fun body => (expression depth body).map some)
      let next ← (child? "constructors" children).orElse (fun _ => child? "fieldsTail" children)
      match depth with
      | 0 => none
      | depth + 1 => return ⟨name, type⟩ :: (← fields depth category next)
  | _ => none

def derivingNames (depth : Nat) : ParseTree → Option (List String)
  | .node "deriving.empty" _ _ => some []
  | .node "deriving.present" _ children => do
      return text (← child? "identifier" children) :: (← names depth (← child? "commaNames" children))
  | _ => none

def documentation (tree : ParseTree) : Option String := do
  let .node _ _ children := tree | none
  let body := text (← child? "commentChars" children)
  if body.contains "/-" || body.contains "-/" then none
  else if body != body.trimAsciiStart.toString then none
  else some (body ++ "-/")

def declaration (depth : Nat) (doc : Option String) : ParseTree → Option Command
  | .node label _ children => do
      let name := text (← child? "identifier" children)
      let type ← signature depth (← child? "signature" children)
      match label with
      | "abbrev" => return .abbrev_ doc name type (← expression depth (← child? "expression" children))
      | "inductive" =>
          return .inductive_ doc name type (!(text (← child? "where" children)).isEmpty)
            (← fields depth "constructor" (← child? "constructors" children))
            (← derivingNames depth (← child? "deriving" children))
      | "structure" =>
          return .structure_ doc name type (← fields depth "field" (← child? "fields" children))
            (← derivingNames depth (← child? "deriving" children))
      | _ => none
  | _ => none

def command (depth : Nat) : ParseTree → Option Command
  | .node label _ children => do
      match label with
      | "namespace" => return .namespace_ (text (← child? "identifier" children))
      | "section.empty" => return .section_ none
      | "section.named" => return .section_ (some (text (← child? "identifier" children)))
      | "end.empty" => return .end_ none
      | "end.named" => return .end_ (some (text (← child? "identifier" children)))
      | "open" | "open.scoped" =>
          let opened ← names depth (← child? "names" children)
          if label == "open" && opened.head? == some "scoped" then none
          else return .open_ (label == "open.scoped") opened
      | "import" => return .import_ (text (← child? "identifier" children))
      | "moduleDoc" => return .moduleDoc (← documentation (.node label "command" children))
      | "undocumented" => declaration depth none (← child? "declaration" children)
      | "documented" =>
          declaration depth (some (← documentation (← child? "documentation" children)))
            (← child? "declaration" children)
      | _ => none
  | _ => none

/-- Source-tree lexical guards retain the exact remaining input at each name.
A longer registered symbol may supersede an identifier, not only an equal word. -/
def identifiersValid (tokens : List String) (input : List Nat) : Nat → Nat → ParseTree → Bool
  | _, start, .terminal _ => start < input.length
  | 0, _, .node _ _ _ => false
  | depth + 1, start, .node _ category children =>
      if category == "identifier" then
        let word := children.flatMap leaves
        !tokens.any (fun token => word.length ≤ (scalars token).length &&
          (scalars token).isPrefixOf (input.drop start))
      else
        (children.foldl (fun (state : Nat × Bool) child =>
          (state.1 + (leaves child).length, state.2 && identifiersValid tokens input depth state.1 child))
          (start, true)).2

/-- Source spans of category occurrences, in codepoint coordinates. -/
def spans (category : String) : Nat → Nat → ParseTree → List (Nat × Nat)
  | 0, _, _ | _, _, .terminal _ => []
  | depth + 1, start, .node _ name children =>
      let own := if name == category then [(start, start + (children.flatMap leaves).length)] else []
      own ++ (children.foldl (fun (state : Nat × List (Nat × Nat)) child =>
        (state.1 + (leaves child).length, state.2 ++ spans category depth state.1 child)) (start, [])).2

def column (input : List Nat) (position : Nat) : Nat :=
  (input.take position).foldl (fun col character => if character == 10 then 0 else col + 1) 0

/-- These explicit restrictions keep layout outside the profile from being
silently interpreted as ordinary spaces. They do not assert that Lean itself
requires all expressions to occupy one line. -/
def layoutValid (input : List Nat) (fuel : Nat) (tree : ParseTree) : Bool :=
  let expressions := (spans "expression" fuel 0 tree).all fun (start, stop) =>
    !((input.drop start).take (stop - start)).contains 10
  let fields := spans "field" fuel 0 tree
  let aligned := match fields with
    | [] => true
    | (start, _) :: rest => rest.all fun (next, _) => column input next == column input start
  expressions && aligned

def readback (tokens : List String) (input : String) (fuel : Nat) (tree : ParseTree) : Option Command := do
  unless identifiersValid tokens (scalars input) fuel 0 tree do none
  unless layoutValid (scalars input) fuel tree do none
  let .node "root" _ children := tree | none
  command fuel (← child? "command" children)

def candidates (input : String) (fuel : Nat) : List BoundedScheduler.Candidate :=
  BoundedScheduler.scheduleRoot grammar (scalars input) fuel

def parse (tokens : List String) (input : String) (fuel : Nat) : List Command :=
  (candidates input fuel).filterMap fun candidate => readback tokens input fuel candidate.tree

theorem candidate_sound {input : String} {fuel : Nat} {candidate : BoundedScheduler.Candidate}
    (present : candidate ∈ candidates input fuel) :
    BoundedScheduler.DerivesWithin grammar (scalars input) fuel grammar.start 0 (scalars input).length candidate.tree ∧
      CertificateReplays grammar (scalars input) candidate.certificate grammar.start 0 (scalars input).length candidate.tree :=
  BoundedScheduler.scheduleRoot_sound present

end Mettapedia.GSLT.Parsing.LeanCommandProfile
