import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.OSLF.MeTTaIL.Export

/-!
# Printing `.module` text

`print` writes a module back in the format: imports, the module's theories and its entry. Rows are
written as `languageDef!` writes them:
- a named binder as `^x.p`, its bound variable by its name; an anonymous binder as `^.p`, its bound variable by index
  (`#0`); an abstraction parameter without a binder name as `^body:[A -> B]`;
- an application of an authored abstraction as `(subst body argument)`, and the substitution for the bound variable
  of an open body as `[argument/#0]body`;
- a nullary constructor as `"Zero"`, a curried binder type as `[A -> B -> C]` (an arrow domain in parentheses);
- a variable name as `? "name"`, retaining punctuation and keywords with the same name resolution as an identifier;
- a separator item as `sep("|")`, a collection constructor's algebra as `![flatten, unit "Nil"]`, and a constructor
  declared bare as `![bare]`;
- an equation under its name, except one with the name the reader gives an unnamed equation and no typing context,
  which is written unnamed.

`#module_roundtrip X` (in `ModuleSource.Commands`) prints `X.module`, reads the text back with the
same syntax and checks that the data is unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.Printer

open Mettapedia.OSLF.MeTTaIL.Syntax

private def quoteChar (character : Char) : List Char :=
  if character = '\n' then ['\\', 'n']
  else if character = '\t' then ['\\', 't']
  else if character = '\\' then ['\\', '\\']
  else if character = '"' then ['\\', '"']
  else if character.toNat ≤ 31 ∨ character.toNat = 127 then
    ['\\', 'x', Nat.digitChar (character.toNat / 16), Nat.digitChar (character.toNat % 16)]
  else [character]

/-- A string literal with explicit escapes for the module reader. -/
def stringLiteral (text : String) : String :=
  String.ofList ('"' :: (text.toList.flatMap quoteChar ++ ['"']))

private def commas (parts : List String) : String := ", ".intercalate parts

/-! ## Rows -/

/-- A type as rows write it: an arrow's codomain without brackets, an arrow domain in parentheses. -/
def type : TypeExpr → String
  | .base name => name
  | .arrow domain codomain =>
      let left := match domain with
        | .arrow _ _ => "(" ++ type domain ++ ")"
        | _ => type domain
      left ++ " -> " ++ type codomain
  | .multiBinder element => type element ++ "*"
  | .collection kind element =>
      let collection := match kind with | .vec => "Vec" | .hashBag => "HashBag" | .hashSet => "HashSet"
      collection ++ "(" ++ type element ++ ")"

/-- A pattern, with the names of the enclosing binders innermost first. Quoted constructor heads retain punctuation,
keywords and escaped literal contents. A named binder is written `^x.p` and its bound variable by its name; an
anonymous binder is written `^.p` and its bound variable by index, `#0`. A binder whose body is a collection writes
a space before the body, `^x. {…}`: `.{` is Lean's token for explicit universes. The substitution of `r` for the
bound variable `#0` of a body `b` is written `[r/#0]b`. -/
def pattern (names : List (Option String)) : Pattern → String
  | .bvar index =>
      match names[index]? with
      | some (some name) => name
      | _ => s!"#{index}"
  | .fvar name => "? " ++ stringLiteral name
  | .apply label [] => stringLiteral label
  | .apply label arguments =>
      if label == Pattern.evalHead then
        "(subst " ++ " ".intercalate (arguments.map (pattern names)) ++ ")"
      else
        stringLiteral label ++ "(" ++ commas (arguments.map (pattern names)) ++ ")"
  | .lambda binder body =>
      let head := match binder with
        | some name => s!"^{name}."
        | none => "^."
      let text := pattern (binder :: names) body
      match body with
      | .collection .. => head ++ " " ++ text
      | _ => head ++ text
  | .multiLambda _ binders body =>
      let text := pattern (binders.reverse.map some ++ names) body
      match body with
      | .collection .. => "^[" ++ ",".intercalate binders ++ "]. " ++ text
      | _ => "^[" ++ ",".intercalate binders ++ "]." ++ text
  | .subst body replacement => "[" ++ pattern names replacement ++ "/#0]" ++ pattern names body
  | .collection kind elements rest =>
      let open_ := match kind with | .hashBag => "{" | .vec => "[" | .hashSet => "#{"
      let close := match kind with | .hashBag => "}" | .vec => "]" | .hashSet => "}"
      let items := elements.map (pattern names) ++ (rest.map (fun name => s!"...{name}")).toList
      open_ ++ commas items ++ close
decreasing_by all_goals sizeOf_pattern_dec

theorem pattern_nullary (names : List (Option String)) (label : String) :
    pattern names (.apply label []) = stringLiteral label := by
  rw [pattern]

theorem pattern_free (names : List (Option String)) (name : String) :
    pattern names (.fvar name) = "? " ++ stringLiteral name := by
  rw [pattern]

theorem pattern_apply_one (names : List (Option String)) (label : String) (child : Pattern)
    (ordinary : label ≠ Pattern.evalHead) :
    pattern names (.apply label [child]) =
      stringLiteral label ++ "(" ++ pattern names child ++ ")" := by
  rw [pattern] <;> simp [ordinary, commas]

def premise : Premise → String
  | .freshness condition =>
      match condition.term with
      | .collection .hashBag [] (some rest) => s!"{condition.varName} # ...{rest}"
      | term => s!"{condition.varName} # {pattern [] term}"
  | .congruence source target => s!"{pattern [] source} ~> {pattern [] target}"
  | .scopedStep step =>
      s!"scopedStep([{commas (step.binders.map type)}], {type step.resultType}, " ++
        s!"{pattern [] step.source}, {pattern [] step.target})"
  | .relationQuery relation arguments => s!"{stringLiteral relation}({commas (arguments.map (pattern []))})"
  | .forAll collection param body => s!"forAll({collection}, {param}, {premise body})"

def termParam : TermParam → String
  | .simple name sort => s!"{name}:{type sort}"
  | .abstractionNamed none name sort => s!"^{name}:[{type sort}]"
  | .abstractionNamed (some binder) name sort => s!"^{binder}.{name}:[{type sort}]"
  | .multiAbstractionNamed binders name sort => s!"^[{",".intercalate binders}].{name}:[{type sort}]"

mutual

def syntaxOp : SyntaxPatternOp → String
  | .var name => name
  | .sep collection separator none => s!"{collection}.*sep({stringLiteral separator})"
  | .sep _ separator (some source) => s!"{syntaxOp source}.*sep({stringLiteral separator})"
  | .zip left right => s!"*zip({left}, {right})"
  | .map source params body => s!"{syntaxOp source}.*map(|{commas params}| {" ".intercalate (body.map syntaxItem)})"
  | .opt inner => s!"*opt({" ".intercalate (inner.map syntaxItem)})"

def syntaxItem : SyntaxItem → String
  | .terminal text => stringLiteral text
  | .nonTerminal name => name
  | .separator text => s!"sep({stringLiteral text})"
  | .delimiter left right => stringLiteral left ++ " " ++ stringLiteral right
  | .op op => syntaxOp op

end

/-- A constructor's syntax: a nonterminal followed by its delimiters is written `n.*delim("(", ")")`, as it is read.
(A delimiter after anything else has no spelling of its own; the reader makes one only after a nonterminal.) -/
def syntaxItems : List SyntaxItem → List String
  | .nonTerminal name :: .delimiter left right :: rest =>
      s!"{name}.*delim({stringLiteral left}, {stringLiteral right})" :: syntaxItems rest
  | item :: rest => syntaxItem item :: syntaxItems rest
  | [] => []

def evalPolicy : Option TermEvalPolicy → String
  | none => ""
  | some .rewrite => " ![rewrite]"
  | some .fold => " ![fold]"
  | some .oracle => " ![oracle]"

/-- A collection constructor's algebra and declared representation: `![flatten]`, `![flatten, unit "Nil"]`,
`![unit "Nil"]`, `![]` for neither law; `bare` first among the words when the constructor is declared bare,
`![bare]` with no algebra. (A constructor declared bare with an algebra of neither law has no spelling.) -/
def algebra (algebra : Option CollectionAlgebra) (bare : Bool := false) : String :=
  let laws := match algebra with
    | none => []
    | some { flatten, unit } => (if flatten then ["flatten"] else []) ++ (if unit.isSome then ["unit"] else [])
  let words := (if bare then ["bare"] else []) ++ laws
  let label := match algebra with
    | some { unit := some unit, .. } => " " ++ stringLiteral unit
    | _ => ""
  if algebra.isNone && !bare then "" else " ![" ++ commas words ++ label ++ "]"

/-- A constructor row; `bare` when the constructor is declared bare. -/
def rule (row : GrammarRule) (bare : Bool := false) : String :=
  let representation := match row.collectionRepresentation with
    | .bare => ""
    | .wrapped => " ![wrapped]"
  s!"{stringLiteral row.label} . {commas (row.params.map termParam)} |- {" ".intercalate (syntaxItems row.syntaxPattern)} : " ++
    s!"{row.category}{evalPolicy row.evalPolicy?}{representation}{algebra row.algebra? bare};"

private def guarded (premises : List Premise) (body : String) : String :=
  if premises.isEmpty then body else s!"if {commas (premises.map premise)} then {body}"

/-- Whether an equation's name is the one the reader gives an unnamed equation, `Theory:equation:i`. -/
def generatedEquationName (name : String) : Bool :=
  match name.splitOn ":equation:" with
  | [owner, index] => !owner.isEmpty && !index.isEmpty && index.all Char.isDigit
  | _ => false

/-- An equation: unnamed, `l == r;`, when its name is the reader's for an unnamed equation and it has no typing
context; otherwise under its name. -/
def equation (row : Equation) : String :=
  if row.typeContext.isEmpty && generatedEquationName row.name then
    guarded row.premises s!"{pattern [] row.left} == {pattern [] row.right};"
  else
    let context := commas (row.typeContext.map fun (name, sort) => s!"{name}:{type sort}")
    let conditions := if row.premises.isEmpty then "" else " | " ++ commas (row.premises.map premise)
    s!"{stringLiteral row.name} . {context}{conditions} |- {pattern [] row.left} = {pattern [] row.right};"

def rewrite (row : RewriteRule) : String :=
  let context := commas (row.typeContext.map fun (name, sort) => s!"{name}:{type sort}")
  let conditions := if row.premises.isEmpty then "" else " | " ++ commas (row.premises.map premise)
  s!"{stringLiteral row.name} . {context}{conditions} |- {pattern [] row.left} ~> {pattern [] row.right};"

/-! ## Modules -/

private def blockLines (title : String) (rows : List String) : List String :=
  [title ++ " {"] ++ rows.map ("  " ++ ·) ++ ["}"]

/-- A type row: the sort, with its carrier when it is not the abstract syntax. CeTTa's core names the builtin
carriers `String`, `Int` and `Bool`; the token carriers keep the names of `languageDef!`. -/
def typeRow (declaration : TypeDecl) : String :=
  match declaration.carrier with
  | .ast => declaration.name ++ ";"
  | .builtinString => declaration.name ++ " = String;"
  | .builtinInt => declaration.name ++ " = Int;"
  | .builtinBool => declaration.name ++ " = Bool;"
  | .tokenLabel => declaration.name ++ " = label;"
  | .tokenRaw => declaration.name ++ " = raw;"
  | .tokenProof => declaration.name ++ " = proofTok;"
  | .tokenPath => declaration.name ++ " = path;"

def block : Block → List String
  | .types declarations => blockLines "Types" (declarations.map typeRow)
  | .exports rows => blockLines "Exports" (rows.map fun row => match row.renamed with
      | none => row.sort ++ ";"
      | some target => s!"{row.sort} => {target};")
  | .terms rows bare => blockLines "Terms" (rows.map fun row => rule row (bare.contains row.label))
  | .replacements rows => blockLines "Replacements" (rows.map fun row => s!"{row.old} => {rule row.rule}")
  | .equations rows => blockLines "Equations" (rows.map equation)
  | .rewrites rows => blockLines "Rewrites" (rows.map rewrite)
  | .inductives families => blockLines "Inductives" (families.map InductiveSyntax.Family.print)

def path (parts : Path) : String := ".".intercalate parts

/-- A theory expression at a precedence: a join is 10, an extension 50, an atom 100. -/
partial def expr (context : Nat) : Expr → List String
  | .ref name => [name]
  | .apply target args => [path target ++ "(" ++ commas (args.map fun arg => " ".intercalate (expr 0 arg)) ++ ")"]
  | .join left right =>
      let text := expr 10 left ++ ["\\/"] ++ expr 11 right
      if context > 10 then ["{"] ++ text ++ ["}"] else text
  | .extend none [] => ["Empty"]
  | .extend base blocks =>
      let text := (base.map (expr 51)).getD [] ++ blocks.flatMap block
      if context > 50 then ["{"] ++ text ++ ["}"] else text
  | .letIn name value body =>
      let text := [s!"let {name} = " ++ " ".intercalate (expr 0 value) ++ " in ("] ++ expr 0 body ++ [")"]
      if context > 0 then ["("] ++ text ++ [")"] else text

def theory (row : Theory) : List String :=
  let params := commas (row.params.map fun param => s!"{param.name}: {path param.theory}")
  ["Theory " ++ row.name ++ "(" ++ params ++ ") {"] ++ (expr 0 row.body).map ("  " ++ ·) ++ ["}"]

/-- **A module as `.module` text.** -/
def print (module : Module) : String :=
  let imports := module.imports.map fun item => s!"import {stringLiteral item.file} as {item.qualifier}"
  let entry := match module.entry with
    | some (target, args) => [s!"theory {path target}(" ++ commas (args.map fun arg => " ".intercalate (expr 0 arg)) ++ ")"]
    | none => []
  let body := module.theories.flatMap theory ++ entry
  "\n".intercalate (imports ++ ["Module " ++ module.name ++ " {"] ++ body.map ("  " ++ ·) ++ ["}"]) ++ "\n"

end Mettapedia.GSLT.LanguageDef.ModuleSource.Printer
