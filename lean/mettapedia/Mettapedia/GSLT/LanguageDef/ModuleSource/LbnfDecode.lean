import Mettapedia.GSLT.LanguageDef.ModuleSource.Syntax
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# `.module` data from a grammar-driven parse

The `.module` grammar (`metta/gslt/module/module_v1.cf`) is LBNF data. CeTTa's grammar library
lowers it and parses `.module` files to labelled syntax trees: a node names its category and
production, a list carries its items, a token its decoded text. `decode` reads such a tree as
`ModuleSource.Module`, the data the Lean commands produce, row for row as `languageDef!` writes
them: a binder's name binds its occurrences by index, `(subst b a)` applies an abstraction, and
equations are named `Theory:equation:i` in order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

abbrev Decode := Except String

/-- Scalar text: `(bnf-v1:text-cons codepoint rest)` ending in `(bnf-v1:text-nil)`. -/
partial def text : Atom → Decode String
  | .expression [.symbol "bnf-v1:text-cons", .grounded (.int point), rest] => do
      pure (String.singleton (Char.ofNat point.toNat) ++ (← text rest))
  | .expression [.symbol "bnf-v1:text-nil"] => pure ""
  | .symbol "bnf-v1:text-nil" => pure ""
  | other => throw s!"not scalar text: {repr other}"

/-- A finite list `(LCons item rest)` ending in `LNil`. -/
partial def items : Atom → Decode (List Atom)
  | .expression [.symbol "LCons", item, rest] => do pure (item :: (← items rest))
  | .symbol "LNil" => pure []
  | other => throw s!"not a list: {repr other}"

/-- A node: its production label and children. -/
def node : Atom → Decode (String × List Atom)
  | .expression [.symbol "LbnfAstNodeV1", _, .grounded (.string label), _, children] => do
      pure (label, ← items children)
  | other => throw s!"not a node: {repr other}"

/-- A list node's items. -/
def list : Atom → Decode (List Atom)
  | .expression [.symbol "LbnfAstListV1", _, _, children] => items children
  | other => throw s!"not a list node: {repr other}"

/-- A token's decoded text. -/
def token : Atom → Decode String
  | .expression [.symbol "LbnfAstTokenV1", _, _, value, _, _, _] => text value
  | other => throw s!"not a token: {repr other}"

partial def path (atom : Atom) : Decode Path := do
  match ← node atom with
  | ("MPathOne", [name]) => pure [← token name]
  | ("MPathMore", [name, rest]) => pure ((← token name) :: (← path rest))
  | (label, _) => throw s!"unexpected path {label}"

/-! ## Rows -/

partial def inductiveTerm (atom : Atom) : Decode InductiveSyntax.Term := do
  match ← node atom with
  | ("ITName", [name]) => pure (.name (← token name))
  | ("ITApp", [function, argument]) => pure (.app (← inductiveTerm function) (← inductiveTerm argument))
  | ("ITArrow", [domain, codomain]) => pure (.arrow (← inductiveTerm domain) (← inductiveTerm codomain))
  | (label, _) => throw s!"unexpected inductive term {label}"

def inductiveBinder (atom : Atom) : Decode InductiveSyntax.Binder := do
  match ← node atom with
  | ("IBinder", [name, type]) => pure ⟨← token name, ← inductiveTerm type⟩
  | (label, _) => throw s!"unexpected inductive binder {label}"

def inductiveConstructor (atom : Atom) : Decode InductiveSyntax.Constructor := do
  match ← node atom with
  | ("IConstructor", [name, fields, result]) =>
      pure ⟨← token name, ← (← list fields).mapM inductiveBinder, ← inductiveTerm result⟩
  | (label, _) => throw s!"unexpected inductive constructor {label}"

def inductiveFamily (atom : Atom) : Decode InductiveSyntax.Family := do
  match ← node atom with
  | ("IFamily", [name, parameters, indices, sort, constructors]) =>
      pure ⟨← token name, ← (← list parameters).mapM inductiveBinder,
        ← (← list indices).mapM inductiveBinder, ← inductiveTerm sort,
        ← (← list constructors).mapM inductiveConstructor⟩
  | (label, _) => throw s!"unexpected inductive family {label}"

partial def typeExpr (atom : Atom) : Decode TypeExpr := do
  match ← node atom with
  | ("TyBase", [name]) => pure (.base (← token name))
  | ("TyColl", [kind, element]) =>
      let kind ← match ← token kind with
        | "HashBag" => pure CollType.hashBag
        | "HashSet" => pure CollType.hashSet
        | "Vec" => pure CollType.vec
        | other => throw s!"unknown collection {other}"
      pure (.collection kind (← typeExpr element))
  | ("TyArrow", [domain, codomain]) => pure (.arrow (← typeExpr domain) (← typeExpr codomain))
  | (label, _) => throw s!"unexpected type {label}"

def termParam (atom : Atom) : Decode TermParam := do
  match ← node atom with
  | ("TPSimple", [name, type]) => pure (.simple (← token name) (← typeExpr type))
  | ("TPBinder", [binder, name, type]) => pure (.abstractionNamed (some (← token binder)) (← token name) (← typeExpr type))
  | ("TPAnon", [name, type]) => pure (.abstractionNamed none (← token name) (← typeExpr type))
  | (label, _) => throw s!"unexpected parameter {label}"

def syntaxItem (atom : Atom) : Decode SyntaxItem := do
  match ← node atom with
  | ("SITerminal", [lexeme]) => pure (.terminal (← token lexeme))
  | ("SIVariable", [name]) => pure (.nonTerminal (← token name))
  | ("SISep", [name, separator]) => pure (.op (.sep (← token name) (← token separator) none))
  | ("SISepItem", [separator]) => pure (.separator (← token separator))
  | (label, _) => throw s!"unexpected syntax item {label}"

/-- A constructor's syntax items: `n.*delim("(", ")")` is the nonterminal followed by its delimiters. -/
def syntaxItemsOf (atoms : List Atom) : Decode (List SyntaxItem) := do
  let items ← atoms.mapM fun item => do
    match ← node item with
    | ("SIDelim", [name, left, right]) =>
        pure [SyntaxItem.nonTerminal (← token name), .delimiter (← token left) (← token right)]
    | _ => pure [← syntaxItem item]
  pure items.flatten

/-- A rule row's items: each category becomes the next parameter, `argument:0`, `argument:1`, …, as `languageDef!`
names them. -/
def ruleItems (atoms : List Atom) : Decode (List TermParam × List SyntaxItem) := do
  let mut params : Array TermParam := #[]
  let mut syntaxItems : Array SyntaxItem := #[]
  for item in atoms do
    match ← node item with
    | ("RITerminal", [lexeme]) => syntaxItems := syntaxItems.push (.terminal (← token lexeme))
    | ("RICategory", [sort]) =>
        let name := s!"argument:{params.size}"
        params := params.push (.simple name (.base (← token sort)))
        syntaxItems := syntaxItems.push (.nonTerminal name)
    | (label, _) => throw s!"unexpected rule item {label}"
  pure (params.toList, syntaxItems.toList)

def evalPolicy (atom : Atom) : Decode TermEvalPolicy := do
  match ← node atom with
  | ("EPRewrite", []) => pure .rewrite
  | ("EPFold", []) => pure .fold
  | ("EPOracle", []) => pure .oracle
  | (label, _) => throw s!"unexpected evaluation policy {label}"

def termDecl (atom : Atom) : Decode GrammarRule := do
  match ← node atom with
  | ("TDecl", [label, params, items, category]) =>
      pure { label := ← token label, category := ← token category,
             params := ← (← list params).mapM termParam, syntaxPattern := ← syntaxItemsOf (← list items) }
  | ("TDeclCore", [label, params, items, category]) =>
      pure { label := ← token label, category := ← token category,
             params := ← (← list params).mapM termParam, syntaxPattern := ← syntaxItemsOf (← list items) }
  | ("TDeclWrapped", [label, params, items, category])
  | ("TDeclCoreWrapped", [label, params, items, category]) =>
      pure { label := ← token label, category := ← token category,
             params := ← (← list params).mapM termParam, syntaxPattern := ← syntaxItemsOf (← list items),
             collectionRepresentation := .wrapped }
  | ("TDeclPolicy", [label, params, items, category, policy])
  | ("TDeclCorePolicy", [label, params, items, category, policy]) =>
      pure { label := ← token label, category := ← token category,
             params := ← (← list params).mapM termParam, syntaxPattern := ← syntaxItemsOf (← list items),
             evalPolicy? := some (← evalPolicy policy) }
  | ("TDeclPolicyWrapped", [label, params, items, category, policy])
  | ("TDeclCorePolicyWrapped", [label, params, items, category, policy]) =>
      pure { label := ← token label, category := ← token category,
             params := ← (← list params).mapM termParam, syntaxPattern := ← syntaxItemsOf (← list items),
             evalPolicy? := some (← evalPolicy policy), collectionRepresentation := .wrapped }
  | ("TRule", [label, category, items]) =>
      let (params, syntaxPattern) ← ruleItems (← list items)
      pure { label := ← token label, category := ← token category, params, syntaxPattern }
  | (label, _) => throw s!"unexpected constructor {label}"

/-- A collection constructor's algebra from its words, as `languageDef!` reads them: `flatten`, `unit` with the
unit's label, and `bare`, which alone states no algebra. -/
def algebraOf (words : List String) (unit : Option String) : Decode (Option CollectionAlgebra) := do
  for word in words do
    unless ["flatten", "unit", "bare"].contains word do throw s!"unexpected constructor word {word}"
  if words.contains "bare" && !words.contains "flatten" && !words.contains "unit" && unit.isNone then
    return none
  match words.contains "unit", unit with
  | true, some label => pure (some { flatten := words.contains "flatten", unit := some label })
  | false, none => pure (some { flatten := words.contains "flatten", unit := none })
  | _, _ => throw "`unit` takes the unit's label"

/-- A constructor, and whether it is declared bare. -/
def termDeclWithBare (atom : Atom) : Decode (GrammarRule × Bool) := do
  let modified (label params items category words : Atom) (unit : Option Atom) : Decode (GrammarRule × Bool) := do
    let words ← (← list words).mapM fun word => do
      match ← node word with
      | ("MWord", [name]) => token name
      | (other, _) => throw s!"unexpected constructor word {other}"
    let unit ← unit.mapM token
    let ruleLabel ← token label
    let ruleCategory ← token category
    let ruleParams ← (← list params).mapM termParam
    let ruleSyntax ← syntaxItemsOf (← list items)
    let ruleAlgebra ← algebraOf words unit
    let rule : GrammarRule :=
      { label := ruleLabel, category := ruleCategory, params := ruleParams, syntaxPattern := ruleSyntax,
        algebra? := ruleAlgebra }
    pure (rule, words.contains "bare")
  match ← node atom with
  | ("TDeclMod", [label, params, items, category, words])
  | ("TDeclCoreMod", [label, params, items, category, words]) =>
      modified label params items category words none
  | ("TDeclModUnit", [label, params, items, category, words, unit])
  | ("TDeclCoreModUnit", [label, params, items, category, words, unit]) =>
      modified label params items category words (some unit)
  | _ => pure (← termDecl atom, false)

/-- A pattern under binders, innermost first. -/
partial def pattern (binders : List String) (atom : Atom) : Decode Pattern := do
  match ← node atom with
  | ("PVar", [name]) | ("PQuotedVar", [name]) =>
      let name ← token name
      pure (match binders.idxOf? name with
        | some index => .bvar index
        | none => .fvar name)
  | ("PApp", [label, arguments]) =>
      let arguments ← (← list arguments).mapM fun argument => do
        match ← node argument with
        | ("AArg", [inner]) => pattern binders inner
        | (label, _) => throw s!"unexpected argument {label}"
      -- `(One)` is the name `One`, resolved against the nullary constructors where the theory is
      -- elaborated, as `languageDef!` reads it.
      let label ← token label
      pure (if arguments.isEmpty then .fvar label else .apply label arguments)
  | ("PSubst", [body, argument]) => pure (.apply Pattern.evalHead [← pattern binders body, ← pattern binders argument])
  | ("PBag", [elements]) => pure (.collection .hashBag (← elementsOf binders elements) none)
  | ("PBagRest", [elements, rest]) => pure (.collection .hashBag (← elementsOf binders elements) (some (← token rest)))
  | ("PRestOnly", [rest]) => pure (.collection .hashBag [] (some (← token rest)))
  | ("PEmpty", []) => pure (.collection .hashBag [] none)
  | ("PVec", [elements]) => pure (.collection .vec (← elementsOf binders elements) none)
  | ("PVecRest", [elements, rest]) => pure (.collection .vec (← elementsOf binders elements) (some (← token rest)))
  | ("PVecRestOnly", [rest]) => pure (.collection .vec [] (some (← token rest)))
  | ("PVecEmpty", []) => pure (.collection .vec [] none)
  | ("PSet", [elements]) => pure (.collection .hashSet (← elementsOf binders elements) none)
  | ("PSetRest", [elements, rest]) => pure (.collection .hashSet (← elementsOf binders elements) (some (← token rest)))
  | ("PSetRestOnly", [rest]) => pure (.collection .hashSet [] (some (← token rest)))
  | ("PSetEmpty", []) => pure (.collection .hashSet [] none)
  | ("PBinder", [binder, body]) =>
      let name ← token binder
      pure (.lambda (some name) (← pattern (name :: binders) body))
  | ("PBinderAnon", [body]) => pure (.lambda none (← pattern ("" :: binders) body))
  | ("PIndex", [index]) =>
      match (← token index).toNat? with
      | some index => pure (.bvar index)
      | none => throw "an index is a number"
  | ("PInstantiate", [replacement, index, body]) =>
      unless (← token index) == "0" do throw "a substitution replaces the bound variable #0 of its body"
      pure (.subst (← pattern ("" :: binders) body) (← pattern binders replacement))
  | ("PCall", [label, arguments]) =>
      pure (.apply (← token label) (← callArguments binders arguments))
  | ("PConst", [label]) => pure (.apply (← token label) [])
  | (label, _) => throw s!"unexpected pattern {label}"
where
  callArguments (binders : List String) (atom : Atom) : Decode (List Pattern) := do
    (← list atom).mapM fun argument => do
      match ← node argument with
      | ("CArg", [inner]) => pattern binders inner
      | (label, _) => throw s!"unexpected argument {label}"
  elementsOf (binders : List String) (atom : Atom) : Decode (List Pattern) := do
    (← list atom).mapM fun element => do
      match ← node element with
      | ("EElem", [inner]) => pattern binders inner
      | (label, _) => throw s!"unexpected element {label}"

partial def premise (atom : Atom) : Decode Premise := do
  match ← node atom with
  | ("PrFresh", [name, term]) => pure (.freshness ⟨← token name, ← pattern [] term⟩)
  | ("PrStep", [source, target]) => pure (.congruence (← pattern [] source) (← pattern [] target))
  | ("PrQuery", [relation, arguments]) =>
      pure (.relationQuery (← token relation) (← pattern.callArguments [] arguments))
  | ("PrNamedQuery", [relation, arguments]) =>
      pure (.relationQuery (← token relation) (← pattern.callArguments [] arguments))
  | ("PrForAll", [collection, parameter, body]) =>
      pure (.forAll (← token collection) (← token parameter) (← premise body))
  | (label, _) => throw s!"unexpected premise {label}"

/-- A typed context of a core row. -/
def bindings (atom : Atom) : Decode (List (String × TypeExpr)) := do
  (← list atom).mapM fun binding => do
    match ← node binding with
    | ("CBinding", [name, type]) => pure (← token name, ← typeExpr type)
    | (label, _) => throw s!"unexpected binding {label}"

/-! ## Theories -/

/-- Equations are numbered within their theory. -/
abbrev Numbered := StateT (String × Nat) Decode

def nextEquation : Numbered String := do
  let (owner, count) ← get
  set (owner, count + 1)
  pure s!"{owner}:equation:{count}"

def equationRow (atom : Atom) : Numbered Equation := do
  match ← node atom with
  | ("EqPlain", [left, right]) =>
      pure { name := ← nextEquation, typeContext := [], premises := [],
             left := ← pattern [] left, right := ← pattern [] right }
  | ("EqIf", [premises, left, right]) =>
      let premises ← ((← list premises).mapM premise : Decode _)
      pure { name := ← nextEquation, typeContext := [], premises,
             left := ← pattern [] left, right := ← pattern [] right }
  | ("EqCore", [label, context, left, right]) =>
      pure { name := ← token label, typeContext := ← bindings context, premises := [],
             left := ← pattern [] left, right := ← pattern [] right }
  | ("EqNamedCore", [label, context, left, right]) =>
      pure { name := ← token label, typeContext := ← bindings context, premises := [],
             left := ← pattern [] left, right := ← pattern [] right }
  | ("EqCoreIf", [label, context, premises, left, right]) =>
      pure { name := ← token label, typeContext := ← bindings context,
             premises := ← ((← list premises).mapM premise : Decode _),
             left := ← pattern [] left, right := ← pattern [] right }
  | ("EqNamedCoreIf", [label, context, premises, left, right]) =>
      pure { name := ← token label, typeContext := ← bindings context,
             premises := ← ((← list premises).mapM premise : Decode _),
             left := ← pattern [] left, right := ← pattern [] right }
  | (label, _) => throw s!"unexpected equation {label}"

def rewriteRow (atom : Atom) : Decode RewriteRule := do
  match ← node atom with
  | ("RwPlain", [label, left, right]) =>
      pure { name := ← token label, typeContext := [], premises := [],
             left := ← pattern [] left, right := ← pattern [] right }
  | ("RwIf", [label, premises, left, right]) =>
      pure { name := ← token label, typeContext := [], premises := ← (← list premises).mapM premise,
             left := ← pattern [] left, right := ← pattern [] right }
  | ("RwCore", [label, context, left, right]) =>
      pure { name := ← token label, typeContext := ← bindings context, premises := [],
             left := ← pattern [] left, right := ← pattern [] right }
  | ("RwNamedCore", [label, context, left, right]) =>
      pure { name := ← token label, typeContext := ← bindings context, premises := [],
             left := ← pattern [] left, right := ← pattern [] right }
  | ("RwCoreIf", [label, context, premises, left, right]) =>
      pure { name := ← token label, typeContext := ← bindings context, premises := ← (← list premises).mapM premise,
             left := ← pattern [] left, right := ← pattern [] right }
  | ("RwNamedCoreIf", [label, context, premises, left, right]) =>
      pure { name := ← token label, typeContext := ← bindings context, premises := ← (← list premises).mapM premise,
             left := ← pattern [] left, right := ← pattern [] right }
  | (label, _) => throw s!"unexpected rewrite {label}"

def block (atom : Atom) : Numbered Block := do
  match ← node atom with
  | ("BTypes", [rows]) =>
      pure (.types (← (← list rows).mapM fun row => do
        match ← node row with
        | ("SRow", [name]) => do pure (TypeDecl.plain (← token name))
        | ("SCarrier", [name, carrier]) => do
            let kind ← match ← token carrier with
              | "String" => pure CarrierKind.builtinString
              | "Int" => pure CarrierKind.builtinInt
              | "Bool" => pure CarrierKind.builtinBool
              | "label" => pure CarrierKind.tokenLabel
              | "raw" => pure CarrierKind.tokenRaw
              | "proofTok" => pure CarrierKind.tokenProof
              | "path" => pure CarrierKind.tokenPath
              | other => throw s!"the carrier `{other}` needs an explicit interpretation"
            pure ⟨← token name, kind⟩
        | (label, _) => throw s!"unexpected sort {label}"))
  | ("BExports", [rows]) =>
      pure (.exports (← (← list rows).mapM fun row => do
        match ← node row with
        | ("ERow", [name]) => pure ⟨← token name, none⟩
        | ("ERename", [name, target]) => pure ⟨← token name, some (← token target)⟩
        | (label, _) => throw s!"unexpected export {label}"))
  | ("BTerms", [rows]) =>
      let rows ← ((← list rows).mapM termDeclWithBare : Decode _)
      pure (.terms (rows.map (·.1)) (rows.filterMap fun (rule, bare) => if bare then some rule.label else none))
  | ("BReplacements", [rows]) =>
      pure (.replacements (← (← list rows).mapM fun row => do
        match ← node row with
        | ("RRow", [old, rule]) => pure ⟨← token old, ← termDecl rule⟩
        | (label, _) => throw s!"unexpected replacement {label}"))
  | ("BEquations", [rows]) => pure (.equations (← (← list rows).mapM equationRow))
  | ("BRewrites", [rows]) => pure (.rewrites (← ((← list rows).mapM rewriteRow : Decode _)))
  | ("BInductives", [rows]) => pure (.inductives (← ((← list rows).mapM inductiveFamily : Decode _)))
  | (label, _) => throw s!"unexpected block {label}"

partial def expr (atom : Atom) : Numbered Expr := do
  match ← node atom with
  | ("MRef", [name]) =>
      -- `Empty` is the empty theory, as the Lean commands read it.
      let name ← token name
      pure (if name == "Empty" then .extend none [] else .ref name)
  | ("MApply", [target, args]) => pure (.apply (← path target) (← (← list args).mapM expr))
  | ("MJoin", [left, right]) => pure (.join (← expr left) (← expr right))
  | ("MLet", [name, value, body]) => pure (.letIn (← token name) (← expr value) (← expr body))
  | ("MExtend", [base, first, rest]) =>
      pure (.extend (some (← expr base)) ((← block first) :: (← (← list rest).mapM block)))
  | ("MBlocks", [first, rest]) => pure (.extend none ((← block first) :: (← (← list rest).mapM block)))
  | (label, _) => throw s!"unexpected expression {label}"

def theory (atom : Atom) : Decode Theory := do
  match ← node atom with
  | ("MTheory", [name, params, body]) =>
      let name ← token name
      let params ← (← list params).mapM fun param => do
        match ← node param with
        | ("MParam", [paramName, target]) => pure ⟨← token paramName, ← path target⟩
        | (label, _) => throw s!"unexpected parameter {label}"
      let (body, _) ← (expr body).run (name, 0)
      pure { name, params, body }
  | (label, _) => throw s!"unexpected theory {label}"

/-- **A parsed `.module` file as module data.** -/
def decode (atom : Atom) : Decode Module := do
  match ← node atom with
  | ("MFile", [imports, name, theories, entry]) =>
      let imports ← (← list imports).mapM fun item => do
        match ← node item with
        | ("MImport", [file, qualifier]) => pure ⟨← token file, ← token qualifier⟩
        | (label, _) => throw s!"unexpected import {label}"
      let entry ← match ← node entry with
        | ("MEntry", [target, args]) => do
            let (args, _) ← ((← list args).mapM expr).run ("entry", 0)
            pure (some (← path target, args))
        | ("MNoEntry", []) => pure none
        | (label, _) => throw s!"unexpected entry {label}"
      pure { imports, name := ← token name, theories := ← (← list theories).mapM theory, entry }
  | (label, _) => throw s!"unexpected module file {label}"

/-- The trees of a `(LangDef:AuthoredParseAccepted …)` result. -/
def acceptedTrees : Atom → Decode (List Atom)
  | .expression (.symbol "LangDef:AuthoredParseAccepted" :: rest) =>
      match rest.getLast? with
      | some (.expression trees) => pure trees
      | _ => throw "no trees in the accepted parse"
  | other => throw s!"not an accepted parse: {repr other}"

end Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
