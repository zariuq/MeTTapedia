import Mettapedia.GSLT.Parsing.LeanCommandProfile
import Mettapedia.Languages.Lean.ParserOracle4331

/-!
# Lean 4.33.1 syntax realization of the declared command profile

Only this adapter names host syntax-node layouts. The portable grammar and
command values are independent of those layouts. Comparison omits source
positions but preserves complete node shape, token spellings, structured
names and pre-resolved references. Live comparison supplies qualification;
this module does not claim a complete Lean parser or elaborator.
-/

namespace Mettapedia.Languages.Lean.CommandProfile4331

open _root_.Lean
open Mettapedia.GSLT.Parsing.LeanCommandProfile
open ParserAdapter4331 ParserOracle4331

abbrev ProfileCommand := Mettapedia.GSLT.Parsing.LeanCommandProfile.Command

def atom (text : String) : Syntax := .atom .none text
def identifier (text : String) : Syntax := .ident .none text.toRawSubstring text.toName []
def node (kind : String) (children : List Syntax) : Syntax := .node .none kind.toName children.toArray
def group (children : List Syntax := []) : Syntax := node "null" children

def expression : Expression → Syntax
  | .identifier name => identifier name
  | .prop => node "Lean.Parser.Term.prop" [atom "Prop"]
  | .type => node "Lean.Parser.Term.type" [atom "Type", group]
  | .application function arguments => node "Lean.Parser.Term.app"
      [expression function, group (arguments.map expression)]
  | .arrow spelling domain codomain => node "Lean.Parser.Term.arrow"
      [expression domain, atom spelling, expression codomain]
  | .parenthesized body => node "Lean.Parser.Term.paren"
      [node "Lean.Parser.Term.hygienicLParen" [atom "(", node "hygieneInfo"
        [.ident .none "".toRawSubstring .anonymous []]], expression body, atom ")"]

def modifiers (documentation : Option String) : Syntax :=
  node "Lean.Parser.Command.declModifiers"
    (group (documentation.toList.map fun text => node "Lean.Parser.Command.docComment" [atom "/--", atom text]) ::
      List.replicate 6 group)

def declarationId (name : String) : Syntax := node "Lean.Parser.Command.declId" [identifier name, group]

def signature (type : Option Expression) : Syntax :=
  node "Lean.Parser.Command.optDeclSig" [group,
    group (type.toList.map fun value => node "Lean.Parser.Term.typeSpec" [atom ":", expression value])]

def derivingClause (names : List String) : Syntax :=
  let classes := names.map fun name => node "Lean.Parser.Command.derivingClass" [group, identifier name]
  let separated := classes.intersperse (atom ",")
  node "Lean.Parser.Command.optDeriving" [group (if names.isEmpty then [] else [atom "deriving", group separated])]

def constructor (field : Field) : Syntax := node "Lean.Parser.Command.ctor"
  [group, atom "|", modifiers none, identifier field.name, signature field.type]

def structureField (field : Field) : Syntax := node "Lean.Parser.Command.structSimpleBinder"
  [modifiers none, identifier field.name, signature field.type, group]

def declaration (doc : Option String) (body : Syntax) : Syntax :=
  node "Lean.Parser.Command.declaration" [modifiers doc, body]

def command : ProfileCommand → Syntax
  | .namespace_ name => node "Lean.Parser.Command.namespace" [atom "namespace", identifier name]
  | .section_ name => node "Lean.Parser.Command.section"
      [node "Lean.Parser.Command.sectionHeader" (List.replicate 4 group), atom "section", group (name.toList.map identifier)]
  | .end_ name => node "Lean.Parser.Command.end"
      [atom "end", group (match name with | none => [] | some name => [identifier name, group])]
  | .open_ isScoped names => node "Lean.Parser.Command.open" [atom "open",
      if isScoped then node "Lean.Parser.Command.openScoped" [atom "scoped", group (names.map identifier)]
      else node "Lean.Parser.Command.openSimple" [group (names.map identifier)]]
  | .import_ name => node "Lean.Parser.Module.import" [group, group, atom "import", group, identifier name, group]
  | .moduleDoc text => node "Lean.Parser.Command.moduleDoc" [atom "/-!", atom text]
  | .abbrev_ doc name type value => declaration doc (node "Lean.Parser.Command.abbrev"
      [atom "abbrev", declarationId name, signature type,
       node "Lean.Parser.Command.declValSimple" [atom ":=", expression value,
         node "Lean.Parser.Termination.suffix" [group, group], group]])
  | .inductive_ doc name type hasWhere constructors derivingClasses => declaration doc
      (node "Lean.Parser.Command.inductive" [atom "inductive", declarationId name, signature type,
        group (if hasWhere then [atom "where"] else []), group (constructors.map constructor), group,
        derivingClause derivingClasses])
  | .structure_ doc name type fields derivingClasses => declaration doc
      (node "Lean.Parser.Command.structure" [node "Lean.Parser.Command.structureTk" [atom "structure"],
        declarationId name, signature type, group,
        group [atom "where", group, node "Lean.Parser.Command.structFields" [group (fields.map structureField)]],
        derivingClause derivingClasses])

def observation : Nat → Syntax → Except String Json
  | 0, _ => .error "syntax observation bound exhausted"
  | _ + 1, .missing => pure (toJson (["missing"] : List String))
  | _ + 1, .atom _ text => pure (Json.arr #[toJson "atom", toJson text])
  | _ + 1, .ident _ raw name resolved => pure (Json.arr #[toJson "identifier", toJson raw.toString,
      nameJson (exportName name), Json.arr (resolved.map preresolvedJson).toArray])
  | depth + 1, .node _ kind children => do
      return Json.arr #[toJson "node", nameJson (exportName kind), Json.arr (← children.mapM (observation depth))]

def compare (depth : Nat) (source : Syntax) (parsed : ProfileCommand) : Except String Bool := do
  unless hostSupported do throw "unqualified Lean syntax adapter release"
  return (← observation depth source) == (← observation depth (command parsed))

end Mettapedia.Languages.Lean.CommandProfile4331
