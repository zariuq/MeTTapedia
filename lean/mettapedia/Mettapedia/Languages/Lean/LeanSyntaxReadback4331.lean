import Mettapedia.Languages.Lean.LeanSyntaxBootstrap
import Mettapedia.Languages.Lean.CommandProfile4331

/-!
# Lean 4.33.1 readback for the declarative command bootstrap

Only this module constructs host syntax nodes. The grammar and operator
descriptions remain portable data. Readback preserves raw numeral and string
spellings and does not call Lean's parser on a source fragment.
-/

namespace Mettapedia.Languages.Lean.LeanSyntaxReadback4331

open _root_.Lean
open Mettapedia.GSLT.Parsing
open PresentationExprSemantics
open LeanSyntaxBootstrap

def treeText : CST → String
  | .terminal values _ _ => String.ofList (values.map Char.ofNat)
  | .node _ _ _ children => String.join (children.map treeText)

def treeDepth : CST → Nat
  | .terminal .. => 1
  | .node _ _ _ children => 1 + (children.map treeDepth).foldl max 0

def nodeLabel : CST → String
  | .terminal .. => ""
  | .node label .. => label

def childNodes : CST → List CST
  | .terminal .. => []
  | .node _ _ _ children => children

def child (label : String) (tree : CST) : Except String CST :=
  match (childNodes tree).find? (fun value => nodeLabel value == label) with
  | some value => .ok value
  | none => .error ("missing syntax field: " ++ label ++ " in " ++ nodeLabel tree)

def fieldText (label : String) (tree : CST) : Except String String := treeText <$> child label tree

def continuation (cp : Nat) : Bool := GSLT.Parsing.LeanCommandProfile.continuations.contains cp
def identifierStart (cp : Nat) : Bool := GSLT.Parsing.LeanCommandProfile.letters.contains cp || cp == 95

def continuesIdentifier (input : List Nat) (stop : Nat) : Bool :=
  match input[stop]? with
  | none => false
  | some cp => continuation cp ||
      (cp == 46 && (input[stop + 1]?).any identifierStart)

def longerToken (tokens : List String) (input : List Nat) (start width : Nat) (allowEqual : Bool) : Bool :=
  tokens.any fun token =>
    let spelling := token.toList.map Char.toNat
    (if allowEqual then width ≤ spelling.length else width < spelling.length) && spelling.isPrefixOf (input.drop start)

def wordLike (values : List Nat) : Bool :=
  values.head?.any identifierStart && values.all (fun cp => continuation cp || cp == 46)

mutual
  def lexical (tokens : List String) (input : List Nat) : CST → Bool
    | .terminal values start stop =>
        !(longerToken tokens input start values.length false) &&
          !(wordLike values && continuesIdentifier input stop)
    | .node "quoted" _ _ _ => true
    | .node "identifier" start stop children =>
        let width := stop - start
        !(longerToken tokens input start width true) && !(continuesIdentifier input stop) && !children.isEmpty
    | .node "number" _ stop _ =>
        !((input[stop]?).any fun cp => 48 ≤ cp && cp ≤ 57)
    | .node _ _ _ children => lexicalChildren tokens input children
  def lexicalChildren (tokens : List String) (input : List Nat) : List CST → Bool
    | [] => true
    | tree :: rest => lexical tokens input tree && lexicalChildren tokens input rest
end

mutual
  def oldTree : CST → Option CompilerCorrespondence.ParseTree
    | .terminal _ _ _ => none
    | .node label _ _ children => do
        let rule ← LeanCommandProfile.presentation.rules.find? (fun rule => rule.sourceRule == label)
        return .node label rule.category (← oldChildren children)
  def oldChildren : List CST → Option (List CompilerCorrespondence.ParseTree)
    | [] => some []
    | .terminal values _ _ :: rest =>
        (values.map CompilerCorrespondence.ParseTree.terminal ++ ·) <$> oldChildren rest
    | tree :: rest => do return (← oldTree tree) :: (← oldChildren rest)
end

inductive Attribute where
  | global
  | local
  | scoped
  deriving DecidableEq, Repr

structure Header where
  scopeKind : Attribute
  precedence : String
  name : String
  priority : Option String
  deriving Repr

inductive Part where
  | literal (raw : String)
  | category (name precedence : String)
  deriving Repr

inductive Command where
  | existing (command : LeanCommandProfile.Command)
  | mixfix (header : Header) (kind token target : String)
  | syntax_ (header : Header) (parts : List Part) (category : String)
  | notation_ (header : Header) (parts : List Part) (meaning : List String)
  | check (term : CST)
  deriving Repr

def readHeader (tree : CST) : Except String Header := do
  let scopeKind ← match (childNodes tree).find? (fun value => (nodeLabel value).startsWith "attribute.") with
    | some (.node "attribute.global" ..) => pure Attribute.global
    | some (.node "attribute.local" ..) => pure Attribute.local
    | some (.node "attribute.scoped" ..) => pure Attribute.scoped
    | _ => throw "missing declaration attribute"
  let precedence ← fieldText "number" (← child "precedence" tree)
  let name ← fieldText "identifier" (← child "declaration.name" tree)
  let priority ← match (childNodes tree).find? (fun value => (nodeLabel value).startsWith "priority.") with
    | some (.node "priority.default" ..) => pure none
    | some value => some <$> fieldText "number" value
    | none => throw "missing declaration priority"
  return ⟨scopeKind, precedence, name, priority⟩

def readPart (tree : CST) : Except String Part := do
  match nodeLabel tree with
  | "part.literal" => return .literal (← fieldText "quoted" tree)
  | "part.category" =>
      return .category (← fieldText "identifier" tree) (← fieldText "number" (← child "precedence" tree))
  | _ => throw "unknown syntax-declaration part"

def readParts (tree : CST) : Except String (List Part) := do
  (childNodes (← child "parts" tree)).mapM readPart

def readCommand (tree : CST) : Except String Command := do
  match nodeLabel tree with
  | "declaration.infix" =>
      let kind ← match (childNodes tree).find? (fun value => (nodeLabel value).startsWith "infix.") with
        | some value => pure (nodeLabel value)
        | none => throw "missing infix associativity"
      return .mixfix (← readHeader tree) kind (← fieldText "quoted" tree) (← fieldText "identifier" tree)
  | "declaration.syntax" =>
      return .syntax_ (← readHeader tree) (← readParts tree) (← fieldText "identifier" tree)
  | "declaration.notation" =>
      let some parsed := oldTree (← child "names" tree) | throw "malformed notation meaning"
      let some names := LeanCommandProfile.names (treeDepth tree + 4) parsed | throw "malformed notation name list"
      return .notation_ (← readHeader tree) (← readParts tree) names
  | "observe.term" =>
      match childNodes tree with
      | [.terminal .., term] => return .check term
      | _ => throw "malformed term observation"
  | _ =>
      let some parsed := oldTree tree | throw "unknown command production"
      let some command := LeanCommandProfile.command (treeDepth tree + 4) parsed | throw "unsupported scope command"
      return .existing command

def atom := CommandProfile4331.atom
def node := CommandProfile4331.node
def group (children : List Syntax := []) : Syntax := CommandProfile4331.group children
def identifier := CommandProfile4331.identifier
def numeral (raw : String) : Syntax := node "num" [atom raw]
def stringLiteral (raw : String) : Syntax := node "str" [atom raw]
def precedence (raw : String) : Syntax := node "Lean.Parser.precedence" [atom ":", numeral raw]

def attributeSyntax : Attribute → Syntax
  | .global => node "Lean.Parser.Term.attrKind" [group]
  | .local => node "Lean.Parser.Term.attrKind" [group [node "Lean.Parser.Term.local" [atom "local"]]]
  | .scoped => node "Lean.Parser.Term.attrKind" [group [node "Lean.Parser.Term.scoped" [atom "scoped"]]]

def namedName (value : String) : Syntax :=
  group [node "Lean.Parser.Command.namedName" [atom "(", atom "name", atom ":=", identifier value, atom ")"]]

def namedPriority (value : Option String) : Syntax :=
  group (value.toList.map fun value =>
    node "Lean.Parser.Command.namedPrio" [atom "(", atom "priority", atom ":=", numeral value, atom ")"])

def syntaxPart : Part → Syntax
  | .literal raw => node "Lean.Parser.Syntax.atom" [stringLiteral raw]
  | .category name prec => node "Lean.Parser.Syntax.cat" [identifier name, group [precedence prec]]

def notationPart : Part → Syntax
  | .literal raw => stringLiteral raw
  | .category name prec => node "Lean.Parser.Command.identPrec" [identifier name, group [precedence prec]]

def termSyntax (rows : List DynamicRow) : Nat → CST → Except String Syntax
  | 0, _ => .error "term readback depth exhausted"
  | _, .terminal values _ _ => pure (atom (String.ofList (values.map Char.ofNat)))
  | depth + 1, tree@(.node label _ _ children) => do
      if label == "term.number" then return numeral (← fieldText "number" tree)
      else if label == "number" then return numeral (treeText tree)
      else if label == "term.identifier" then return identifier (← fieldText "identifier" tree)
      else if label == "identifier" then return identifier (treeText tree)
      else if label == "group" then return node "group" (← children.mapM (termSyntax rows depth))
      else if label == "selected.choice" then
        return .node .none _root_.Lean.choiceKind (← children.toArray.mapM (termSyntax rows depth))
      else if label == "term.parenthesized" then
        match children with
        | [_, body, _] => do
            let parsedBody ← termSyntax rows depth body
            return node "Lean.Parser.Term.paren"
              [node "Lean.Parser.Term.hygienicLParen" [atom "(", node "hygieneInfo"
                [.ident .none "".toRawSubstring .anonymous []]], parsedBody, atom ")"]
        | _ => throw "malformed parentheses"
      else
        let some row := rows.find? (fun row => row.label == label) | throw ("unknown term production: " ++ label)
        return .node .none (ParserAdapter4331.importName row.row.kind) (← children.toArray.mapM (termSyntax rows depth))

def commandSyntax (rows : List DynamicRow) : Command → Except String Syntax
  | .existing command => pure (CommandProfile4331.command command)
  | .mixfix header kind token target => do
      let spelling ← match kind with
        | "infix.left" => pure "infixl" | "infix.right" => pure "infixr"
        | "infix.none" => pure "infix" | _ => throw "unknown infix kind"
      return node "Lean.Parser.Command.mixfix" [group, group, attributeSyntax header.scopeKind,
        node ("Lean.Parser.Command." ++ spelling) [atom spelling], precedence header.precedence,
        namedName header.name, namedPriority header.priority, stringLiteral token, atom "=>", identifier target]
  | .syntax_ header parts category =>
      pure (node "Lean.Parser.Command.syntax" [group, group, attributeSyntax header.scopeKind, atom "syntax",
        group [precedence header.precedence], namedName header.name, namedPriority header.priority,
        group (parts.map syntaxPart), atom ":", identifier category])
  | .notation_ header parts meaning => do
      let first :: rest := meaning | throw "empty notation meaning"
      let body := if rest.isEmpty then identifier first else
        node "Lean.Parser.Term.app" [identifier first, group (rest.map identifier)]
      return node "Lean.Parser.Command.notation" [group, group, attributeSyntax header.scopeKind, atom "notation",
        group [precedence header.precedence], namedName header.name, namedPriority header.priority,
        group (parts.map notationPart), atom "=>", body]
  | .check tree => do
      return node "Lean.Parser.Command.check" [atom "#check", ← termSyntax rows (treeDepth tree + 1) tree]

end Mettapedia.Languages.Lean.LeanSyntaxReadback4331
