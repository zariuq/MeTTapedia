import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Resumption
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BackwardReach
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Hints
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ScopedCongruences
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalForms
import Mettapedia.OSLF.NativeTypes.Product.CertifiedForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SortWitnesses
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.StaticDecider
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabels
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartnerAdequacy

/-!
# The command-line front door: queries as text

The `oslf` executable reads a language from a `.module` file and asks the front door a question about a term, at a
list of budgets, resuming the question from one budget to the next.

- **Text** (`SExp`, `readSExp`): atoms, quoted strings and parenthesized lists.
- **Terms** (`patternOf`): an atom is a constant; `(C t₁ … tₙ)` applies a constructor; `(set …)`, `(bag …)`, `(vec …)`
  and `(list …)` are collections, with `...r` last for a rest; `(lam t)` binds a variable, optionally named, `(lams n
  (x …) t)` binds several, `(bvar i)` is the variable bound `i` binders up, `(fvar x)` a free variable and
  `(subst t u)` a substitution.
- **Formulas** (`formulaOf`), in negation normal form with named fixed-point variables, every former of the generated
  language: `top`, `bot`, `(and φ ψ)`, `(or φ ψ)`, `(dia φ)` and `(box φ)` for a step and every step, `(before φ)`
  and `(alwaysBefore φ)` for the past, each optionally with a label after the former (`any`, `(rule R)`,
  `(under R ℓ)`, rules by number or name); `(atLeast n φ)` and `(allButFewer n φ)`, optionally with a direction and a
  label; `(mu X φ)`, `(nu X φ)` and `X`; `(is t)`, `(isNot t)`, `(typed T)`, `(untyped T)`; `(built C φ …)`,
  `(everyBuilt C φ …)`; `(split k φ ψ)`, `(everySplit k φ ψ)`, `(empty k)`, `(nonEmpty k)`, `(single k φ)`,
  `(everySingle k φ)`; `(body φ)`, `(everyBody φ)`, `(multiBody n φ)`, `(everyMultiBody n φ)`, `(bound i)`,
  `(notBound i)`, `(mapsAll φ ψ)`, `(mapsSome φ ψ)`; `(someOf T φ)`, `(everyOf T φ)`; `(inRelation r)`,
  `(notInRelation r)`. Two abbreviations: `(not φ)`, the dual, and `(reach t …)`, the formula of reaching one of the
  terms.
- **Printing** (`patternText`, `typeText`, `formulaText`): the inverse of reading, so that rows checked in the library
  are written out as the executable's matrix.
- **Answers** (`report`): the status at each budget, as the progress of the question resumed from the previous budget
  gives it, which is the answer of asking afresh with that budget (`resumed_answer`). The question's settings are the
  premise fuel and the bound of the finder's hint search (`Settings`), and a language with bags is read through its
  sorted bags (`formsOf`).
-/

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic

/-! ## S-expressions -/

/-- An S-expression: an atom or a list. -/
inductive SExp where
  | atom (text : String)
  | list (items : List SExp)
  deriving Repr, Inhabited

/-- The tokens of a text: parentheses, quoted strings and atoms. -/
partial def tokens (text : String) : List String :=
  let rec go (chars : List Char) (current : List Char) (out : List String) : List String :=
    let flush := if current.isEmpty then out else String.ofList current.reverse :: out
    match chars with
    | [] => flush.reverse
    | '(' :: rest => go rest [] ("(" :: flush)
    | ')' :: rest => go rest [] (")" :: flush)
    | '"' :: rest =>
      let quoted := rest.takeWhile (· != '"')
      go (rest.drop (quoted.length + 1)) [] (String.ofList quoted :: flush)
    | c :: rest => if c.isWhitespace then go rest [] flush else go rest (c :: current) out
  go text.toList [] []

/-- Read one S-expression from tokens. -/
partial def readTokens : List String → Except String (SExp × List String)
  | [] => .error "unexpected end of input"
  | ")" :: _ => .error "unexpected ')'"
  | "(" :: rest => do
    let mut items : Array SExp := #[]
    let mut remaining := rest
    repeat
      match remaining with
      | ")" :: after => return (.list items.toList, after)
      | [] => throw "missing ')'"
      | _ =>
        let (item, after) ← readTokens remaining
        items := items.push item
        remaining := after
    return (.list items.toList, remaining)
  | token :: rest => .ok (.atom token, rest)

/-- **Read an S-expression** from a text. -/
def readSExp (text : String) : Except String SExp := do
  let (expression, rest) ← readTokens (tokens text)
  if rest.isEmpty then pure expression else throw s!"unexpected text after the expression: {rest}"

/-! ## Terms -/

/-- The collection kind an atom names. -/
def kindOf : String → Option CollType
  | "set" => some .hashSet
  | "bag" => some .hashBag
  | "vec" => some .vec
  | "list" => some .vec
  | _ => none

/-- The atom that names a collection kind. -/
def kindName : CollType → String
  | .hashSet => "set"
  | .hashBag => "bag"
  | .vec => "vec"

/-- A rest marker `...r` in a collection: the name of the rest. -/
def restName? : SExp → Option String
  | .atom text => if text.startsWith "..." then some (text.drop 3).toString else none
  | .list _ => none

/-- **A term** from an S-expression. -/
partial def patternOf : SExp → Except String Pattern
  | .atom name => .ok (.apply name [])
  | .list [] => .error "an empty application"
  | .list [.atom "lam", body] => do pure (.lambda none (← patternOf body))
  | .list [.atom "lam", .atom binder, body] => do pure (.lambda (some binder) (← patternOf body))
  | .list [.atom "lams", .atom count, .list binders, body] => do
    let some number := count.toNat? | throw s!"not a count: {count}"
    let names ← binders.mapM fun binder => match binder with
      | .atom name => pure name
      | .list _ => throw "a binder name is an atom"
    pure (.multiLambda number names (← patternOf body))
  | .list [.atom "bvar", .atom index] =>
    match index.toNat? with
    | some number => .ok (.bvar number)
    | none => .error s!"not a de Bruijn index: {index}"
  | .list [.atom "fvar", .atom name] => .ok (.fvar name)
  | .list [.atom "subst", body, argument] => do pure (.subst (← patternOf body) (← patternOf argument))
  | .list (.atom head :: arguments) => do
    match kindOf head with
    | some kind =>
      match arguments.getLast? >>= restName? with
      | some rest => pure (.collection kind (← arguments.dropLast.mapM patternOf) (some rest))
      | none => pure (.collection kind (← arguments.mapM patternOf) none)
    | none => pure (.apply head (← arguments.mapM patternOf))
  | .list _ => .error "an application must start with a constructor name"

/-- Words separated by spaces, in parentheses. -/
def parenthesized (words : List String) : String := "(" ++ " ".intercalate words ++ ")"

/-- **A term as text**, which `patternOf` reads back. -/
def patternText : Pattern → String
  | .bvar index => parenthesized ["bvar", toString index]
  | .fvar name => parenthesized ["fvar", name]
  | .apply head [] => head
  | .apply head arguments => parenthesized (head :: arguments.attach.map fun ⟨argument, _⟩ => patternText argument)
  | .lambda none body => parenthesized ["lam", patternText body]
  | .lambda (some binder) body => parenthesized ["lam", binder, patternText body]
  | .multiLambda count binders body => parenthesized ["lams", toString count, parenthesized binders, patternText body]
  | .subst body argument => parenthesized ["subst", patternText body, patternText argument]
  | .collection kind elements rest =>
    parenthesized (kindName kind :: elements.attach.map (fun ⟨element, _⟩ => patternText element) ++
      (rest.map ("..." ++ ·)).toList)

/-! ## Types -/

/-- **A type** from an S-expression. -/
partial def typeOf : SExp → Except String TypeExpr
  | .atom name => .ok (.base name)
  | .list [.atom "arrow", domain, codomain] => do pure (.arrow (← typeOf domain) (← typeOf codomain))
  | .list [.atom "multi", inner] => do pure (.multiBinder (← typeOf inner))
  | .list [.atom kind, element] => do
    match kindOf kind with
    | some collection => pure (.collection collection (← typeOf element))
    | none => throw s!"unknown type former {kind}"
  | _ => .error "a type is a name, (arrow A B), (multi A) or (set A), (bag A), (vec A)"

/-- **A type as text**, which `typeOf` reads back. -/
def typeText : TypeExpr → String
  | .base name => name
  | .arrow domain codomain => parenthesized ["arrow", typeText domain, typeText codomain]
  | .multiBinder inner => parenthesized ["multi", typeText inner]
  | .collection kind element => parenthesized [kindName kind, typeText element]

/-! ## Labels and directions -/

/-- The index of a rule, by number or by name among the language's rules. -/
def ruleIndex (rules : List String) (text : String) : Except String ℕ :=
  match text.toNat? with
  | some index => .ok index
  | none =>
    match rules.idxOf? text with
    | some index => .ok index
    | none => .error s!"unknown rule {text}"

/-- **A step label**: `any`, `(rule R)` for one rule's steps, `(under R ℓ)` for the steps at the site of rule `R`'s
congruence whose premise step has label `ℓ`, `(in x C ℓ)` for the steps with label `ℓ` of the term placed in the context
`C` at its metavariable `x`; a rule by number or by name. -/
partial def labelOf (rules : List String) : SExp → Except String StepLabel
  | .atom "any" => .ok .any
  | .list [.atom "rule", .atom rule] => do pure (.rule (← ruleIndex rules rule))
  | .list [.atom "under", .atom rule, inner] => do pure (.under (← ruleIndex rules rule) (← labelOf rules inner))
  | .list [.atom "in", .atom hole, context, inner] => do
    pure (.context hole (← patternOf context) (← labelOf rules inner))
  | _ => .error "a label is any, (rule R), (under R label) or (in x context label)"

/-- A label as text, rules by number. -/
def labelText : StepLabel → String
  | .any => "any"
  | .rule index => parenthesized ["rule", toString index]
  | .under index label => parenthesized ["under", toString index, labelText label]
  | .context hole context label => parenthesized ["in", hole, patternText context, labelText label]

/-- A direction: `forward` or `backward`. -/
def directionOf : SExp → Except String Direction
  | .atom "forward" => .ok .forward
  | .atom "backward" => .ok .backward
  | _ => .error "a direction is forward or backward"

/-- A direction as text. -/
def directionText : Direction → String
  | .forward => "forward"
  | .backward => "backward"

/-! ## Formulas -/

/-- The index of a fixed-point variable among the names in scope, innermost first. -/
def variableIndex (names : List String) (name : String) : Option (Fin names.length) :=
  match names.idxOf? name with
  | some index => if h : index < names.length then some ⟨index, h⟩ else none
  | none => none

/-- A collection kind named by an atom. -/
def collectionOf : SExp → Except String CollType
  | .atom kind => match kindOf kind with
    | some collection => .ok collection
    | none => .error s!"unknown collection kind {kind}"
  | .list _ => .error "a collection kind is set, bag or vec"

/-- A number written as an atom. -/
def numberOf : SExp → Except String ℕ
  | .atom text => match text.toNat? with
    | some number => .ok number
    | none => .error s!"not a number: {text}"
  | .list _ => .error "a number is an atom"

mutual
/-- **A formula** from an S-expression, with the language's rule names and the fixed-point variables in scope. -/
partial def formulaOf (rules : List String) (names : List String) : SExp → Except String (Formula names.length)
  | .atom "top" => .ok .top
  | .atom "bot" => .ok .bot
  | .atom name =>
    match variableIndex names name with
    | some index => .ok (.var index)
    | none => .error s!"unknown formula or variable {name}"
  | .list [.atom "and", left, right] => do pure (.and (← formulaOf rules names left) (← formulaOf rules names right))
  | .list [.atom "or", left, right] => do pure (.or (← formulaOf rules names left) (← formulaOf rules names right))
  | .list [.atom "not", inner] => do pure (← formulaOf rules names inner).dual
  | .list [.atom "dia", inner] => do pure (.possibly .any (← formulaOf rules names inner))
  | .list [.atom "dia", label, inner] => do
    pure (.possibly (← labelOf rules label) (← formulaOf rules names inner))
  | .list [.atom "box", inner] => do pure (.necessarily .any (← formulaOf rules names inner))
  | .list [.atom "box", label, inner] => do
    pure (.necessarily (← labelOf rules label) (← formulaOf rules names inner))
  | .list [.atom "before", inner] => do pure (.sometimeBefore .any (← formulaOf rules names inner))
  | .list [.atom "before", label, inner] => do
    pure (.sometimeBefore (← labelOf rules label) (← formulaOf rules names inner))
  | .list [.atom "alwaysBefore", inner] => do pure (.alwaysBefore .any (← formulaOf rules names inner))
  | .list [.atom "alwaysBefore", label, inner] => do
    pure (.alwaysBefore (← labelOf rules label) (← formulaOf rules names inner))
  | .list [.atom "atLeast", count, inner] => do
    pure (.atLeast (← numberOf count) .forward .any (← formulaOf rules names inner))
  | .list [.atom "atLeast", count, direction, label, inner] => do
    pure (.atLeast (← numberOf count) (← directionOf direction) (← labelOf rules label) (← formulaOf rules names inner))
  | .list [.atom "allButFewer", count, inner] => do
    pure (.allButFewer (← numberOf count) .forward .any (← formulaOf rules names inner))
  | .list [.atom "allButFewer", count, direction, label, inner] => do
    pure (.allButFewer (← numberOf count) (← directionOf direction) (← labelOf rules label)
      (← formulaOf rules names inner))
  | .list [.atom "mu", .atom name, body] => do
    let inner ← formulaOf rules (name :: names) body
    pure (.mu inner)
  | .list [.atom "nu", .atom name, body] => do
    let inner ← formulaOf rules (name :: names) body
    pure (.nu inner)
  | .list [.atom "is", term] => do pure (.is (← patternOf term))
  | .list [.atom "isNot", term] => do pure (.isNot (← patternOf term))
  | .list [.atom "typed", type] => do pure (.typed (← typeOf type))
  | .list [.atom "untyped", type] => do pure (.untyped (← typeOf type))
  | .list (.atom "built" :: .atom constructor :: arguments) => do
    pure (.built constructor (← formulasOf rules names arguments))
  | .list (.atom "everyBuilt" :: .atom constructor :: arguments) => do
    pure (.everyBuilt constructor (← formulasOf rules names arguments))
  | .list [.atom "split", kind, left, right] => do
    pure (.split (← collectionOf kind) (← formulaOf rules names left) (← formulaOf rules names right))
  | .list [.atom "everySplit", kind, left, right] => do
    pure (.everySplit (← collectionOf kind) (← formulaOf rules names left) (← formulaOf rules names right))
  | .list [.atom "empty", kind] => do pure (.empty (← collectionOf kind))
  | .list [.atom "nonEmpty", kind] => do pure (.nonEmpty (← collectionOf kind))
  | .list [.atom "single", kind, inner] => do pure (.single (← collectionOf kind) (← formulaOf rules names inner))
  | .list [.atom "everySingle", kind, inner] => do
    pure (.everySingle (← collectionOf kind) (← formulaOf rules names inner))
  | .list [.atom "body", inner] => do pure (.body (← formulaOf rules names inner))
  | .list [.atom "everyBody", inner] => do pure (.everyBody (← formulaOf rules names inner))
  | .list [.atom "multiBody", count, inner] => do pure (.multiBody (← numberOf count) (← formulaOf rules names inner))
  | .list [.atom "everyMultiBody", count, inner] => do
    pure (.everyMultiBody (← numberOf count) (← formulaOf rules names inner))
  | .list [.atom "bound", index] => do pure (.bound (← numberOf index))
  | .list [.atom "notBound", index] => do pure (.notBound (← numberOf index))
  | .list [.atom "mapsAll", argument, result] => do
    pure (.mapsAll (← formulaOf rules names argument) (← formulaOf rules names result))
  | .list [.atom "mapsSome", argument, result] => do
    pure (.mapsSome (← formulaOf rules names argument) (← formulaOf rules names result))
  | .list [.atom "someOf", type, inner] => do pure (.someOf (← typeOf type) (← formulaOf rules names inner))
  | .list [.atom "everyOf", type, inner] => do pure (.everyOf (← typeOf type) (← formulaOf rules names inner))
  | .list [.atom "inRelation", .atom relation] => .ok (.inRelation relation)
  | .list [.atom "notInRelation", .atom relation] => .ok (.notInRelation relation)
  | .list (.atom "reach" :: goals) => do
    let goalTerms ← goals.mapM patternOf
    pure ((reachFormula goalTerms).rename Fin.elim0)
  | other => .error s!"unknown formula: {repr other}"

/-- Formulas for the arguments of a constructor. -/
partial def formulasOf (rules : List String) (names : List String) : List SExp → Except String (Formulas names.length)
  | [] => .ok .nil
  | item :: items => do pure (.cons (← formulaOf rules names item) (← formulasOf rules names items))
end

/-- The name of the fixed-point variable bound at a depth. -/
def variableName (depth : ℕ) : String := s!"X{depth}"

/-- A modality as text: the short form for every step. -/
def modalText (former : String) (label : StepLabel) (inner : String) : String :=
  match label with
  | .any => parenthesized [former, inner]
  | label => parenthesized [former, labelText label, inner]

/-- A counting modality as text: the short form for every step forward. -/
def countingText (former : String) (count : ℕ) (direction : Direction) (label : StepLabel) (inner : String) : String :=
  match direction, label with
  | .forward, .any => parenthesized [former, toString count, inner]
  | direction, label => parenthesized [former, toString count, directionText direction, labelText label, inner]

mutual
/-- **A formula as text**, which `formulaOf` reads back: the fixed-point variable bound at depth `d` is `Xd`, and
rules are named by number. -/
def formulaText : {n : ℕ} → Formula n → String
  | _, .top => "top"
  | _, .bot => "bot"
  | _, .and left right => parenthesized ["and", formulaText left, formulaText right]
  | _, .or left right => parenthesized ["or", formulaText left, formulaText right]
  | n, .var index => variableName (n - 1 - index.val)
  | n, .mu inner => parenthesized ["mu", variableName n, formulaText inner]
  | n, .nu inner => parenthesized ["nu", variableName n, formulaText inner]
  | _, .possibly label inner => modalText "dia" label (formulaText inner)
  | _, .necessarily label inner => modalText "box" label (formulaText inner)
  | _, .sometimeBefore label inner => modalText "before" label (formulaText inner)
  | _, .alwaysBefore label inner => modalText "alwaysBefore" label (formulaText inner)
  | _, .atLeast count direction label inner => countingText "atLeast" count direction label (formulaText inner)
  | _, .allButFewer count direction label inner => countingText "allButFewer" count direction label (formulaText inner)
  | _, .built constructor arguments => parenthesized ("built" :: constructor :: formulasText arguments)
  | _, .everyBuilt constructor arguments => parenthesized ("everyBuilt" :: constructor :: formulasText arguments)
  | _, .split kind left right => parenthesized ["split", kindName kind, formulaText left, formulaText right]
  | _, .everySplit kind left right => parenthesized ["everySplit", kindName kind, formulaText left, formulaText right]
  | _, .empty kind => parenthesized ["empty", kindName kind]
  | _, .nonEmpty kind => parenthesized ["nonEmpty", kindName kind]
  | _, .single kind inner => parenthesized ["single", kindName kind, formulaText inner]
  | _, .everySingle kind inner => parenthesized ["everySingle", kindName kind, formulaText inner]
  | _, .body inner => parenthesized ["body", formulaText inner]
  | _, .everyBody inner => parenthesized ["everyBody", formulaText inner]
  | _, .multiBody count inner => parenthesized ["multiBody", toString count, formulaText inner]
  | _, .everyMultiBody count inner => parenthesized ["everyMultiBody", toString count, formulaText inner]
  | _, .bound index => parenthesized ["bound", toString index]
  | _, .notBound index => parenthesized ["notBound", toString index]
  | _, .typed type => parenthesized ["typed", typeText type]
  | _, .untyped type => parenthesized ["untyped", typeText type]
  | _, .is term => parenthesized ["is", patternText term]
  | _, .isNot term => parenthesized ["isNot", patternText term]
  | _, .mapsAll argument result => parenthesized ["mapsAll", formulaText argument, formulaText result]
  | _, .mapsSome argument result => parenthesized ["mapsSome", formulaText argument, formulaText result]
  | _, .someOf type inner => parenthesized ["someOf", typeText type, formulaText inner]
  | _, .everyOf type inner => parenthesized ["everyOf", typeText type, formulaText inner]
  | _, .inRelation relation => parenthesized ["inRelation", relation]
  | _, .notInRelation relation => parenthesized ["notInRelation", relation]

/-- The arguments of a constructor former as text. -/
def formulasText : {n : ℕ} → Formulas n → List String
  | _, .nil => []
  | _, .cons formula formulas => formulaText formula :: formulasText formulas
end

/-- **A closed formula** from a text, with the language's rule names. -/
def readFormula (rules : List String) (text : String) : Except String (Formula 0) := do
  formulaOf rules [] (← readSExp text)

/-- **A term** from a text. -/
def readPattern (text : String) : Except String Pattern := do
  patternOf (← readSExp text)

/-! ## Answers -/

/-- **Settings of a question**: the premise fuel, and the largest carrier, less one, over which the finder looks for
a certificate hint (none at zero). -/
structure Settings where
  fuel : ℕ := 2
  hintBound : ℕ := 1
  deriving Repr

/-- Settings from words `fuel=N` and `hints=N`. -/
def Settings.read (words : List String) : Except String Settings :=
  words.foldlM (init := {}) fun settings word =>
    match word.splitOn "=" with
    | ["fuel", value] => match value.toNat? with
      | some number => .ok { settings with fuel := number }
      | none => .error s!"not a fuel: {value}"
    | ["hints", value] => match value.toNat? with
      | some number => .ok { settings with hintBound := number }
      | none => .error s!"not a hint bound: {value}"
    | _ => .error s!"unknown setting {word}"

/-- Whether a row writes a binder with a name. -/
def namesBinders (left right : Pattern) (premises : List Premise) : Bool :=
  !(left.hasCanonicalBinderMetadata && right.hasCanonicalBinderMetadata &&
    (premises.flatMap LanguageDef.premisePatterns).all Pattern.hasCanonicalBinderMetadata)

/-- **A language as its rows are written**: a rule or equation with named binders means its core reduction, in which
binder names decide each metavariable's dependencies and arguments (`CoreReduction.reduceRule`); a rule or equation
with anonymous binders means itself. -/
def directReading (language : LanguageDef) : Except Mettapedia.OSLF.MeTTaIL.CoreReduction.Failure LanguageDef := do
  let grammar := Mettapedia.OSLF.MeTTaIL.CoreReduction.canonicalGrammar language
  let equations ← language.equations.mapM fun row =>
    if namesBinders row.left row.right row.premises then
      Mettapedia.OSLF.MeTTaIL.CoreReduction.reduceEquation grammar row
    else pure row
  let rewrites ← language.rewrites.mapM fun row =>
    if namesBinders row.left row.right row.premises then
      Mettapedia.OSLF.MeTTaIL.CoreReduction.reduceRewrite grammar row
    else pure row
  pure { language with «equations» := equations, «rewrites» := rewrites }

/-- **The languages certified in the environment of admitted definitions**: CCS with recursion, whose canonical forms
and decider hold in the environment its definitions serve (`askRecursive`). -/
def certifiedWithDefinitions : List LanguageDef := [Mettapedia.Languages.ProcessCalculi.CCS.Recursive.ccsRecCalc]

/-- **The language a loaded module is read as**: as its rows are written (`directReading`) when that is a language
with certified forms, or certified in the environment of admitted definitions, which their theorems are about as
written; otherwise its core (`LanguageDef.toCore`). -/
def readingOf (loaded : Except Mettapedia.GSLT.LanguageDef.ModuleSource.Error LanguageDef) :
    Except String LanguageDef :=
  match loaded with
  | .error problem => .error s!"the module does not elaborate: {repr problem}"
  | .ok language =>
    let core : Except String LanguageDef :=
      match language.toCore with
      | .ok core => .ok core.language
      | .error problem => .error s!"the language has no core: {repr problem}"
    match directReading language with
    | .ok direct =>
      if certified.any (·.language == direct) || certifiedWithDefinitions.contains direct then .ok direct else core
    | .error _ => core

/-- Whether the language has bags. -/
def hasBags (language : LanguageDef) : Bool := (signatureOf language).contains (.collectionUnit .hashBag)

/-- Sorted bags, for a language with bags, no authored equations, no collection algebra, and rules whose premises
are guards or queries over metavariables. -/
def bagFormsOf (language : LanguageDef) (fuel : ℕ) : Option (CanonicalForms RelationEnv.empty language fuel) :=
  if hasBags language then
    if noEquations : language.equations = [] then
      if noAlgebra : language.hasAlgebraDeclarations = false then
        if guarded : language.rewrites.all (fun rule => rule.premises.all BagForms.guard) = true then
          some (BagForms.forms noEquations noAlgebra guarded fuel)
        else if queried : language.rewrites.all (fun rule => rule.premises.all BagForms.query) = true then
          some (BagForms.formsQueries noEquations noAlgebra queried BagForms.respectsCanon_empty fuel)
        else none
      else none
    else none
  else none

/-- **The canonical forms the executable knows for a language**: the certified forms of a language that has them
(`certifiedFormsOf`); otherwise sorted bags, for a language with bags, no authored equations, no collection algebra,
and rules whose premises are guards or queries over metavariables. Otherwise none, and the language is read as
written. -/
def formsOf (language : LanguageDef) (fuel : ℕ) : Option (CanonicalForms RelationEnv.empty language fuel) :=
  match certifiedFormsOf language fuel with
  | some forms => some forms
  | none => bagFormsOf language fuel

/-- **A certified decider as the last strategy**: an answer the search left open is the decider's, when it gives one. -/
def thenDecide {relEnv : RelationEnv} {reading : LanguageReading} (decider : Decider relEnv language reading)
    (formula : Formula 0)
    (term : Pattern) : Answer → Answer
  | .unknown rounds =>
    match decider.decide formula term with
    | some true => .proved .decided
    | some false => .refuted .decided
    | none => .unknown rounds
  | settled => settled

theorem thenDecide_proved {relEnv : RelationEnv} {reading : LanguageReading} {decider : Decider relEnv language reading}
    {formula : Formula 0} {term : Pattern} {answer : Answer} {evidence : Evidence}
    (searched : ∀ {evidence}, answer = .proved evidence →
      (referenceStructure relEnv language reading).sat Env.closed formula term)
    (answered : thenDecide decider formula term answer = .proved evidence) :
    (referenceStructure relEnv language reading).sat Env.closed formula term := by
  unfold thenDecide at answered
  split at answered
  · split at answered
    · rename_i decided
      exact (decider.exact decided).mpr rfl
    · cases answered
    · cases answered
  · exact searched answered

theorem thenDecide_refuted {relEnv : RelationEnv} {reading : LanguageReading} {decider : Decider relEnv language reading}
    {formula : Formula 0} {term : Pattern} {answer : Answer} {evidence : Evidence}
    (searched : ∀ {evidence}, answer = .refuted evidence →
      ¬ (referenceStructure relEnv language reading).sat Env.closed formula term)
    (answered : thenDecide decider formula term answer = .refuted evidence) :
    ¬ (referenceStructure relEnv language reading).sat Env.closed formula term := by
  unfold thenDecide at answered
  split at answered
  · split at answered
    · cases answered
    · rename_i decided
      exact fun holds => Bool.false_ne_true ((decider.exact decided).mp holds)
    · cases answered
  · exact searched answered

/-- The witness deciders the executable uses, for the sort quantifiers and the past modalities: candidates to depth
three, at most sixty-four of them. -/
def sortsOf (language : LanguageDef) (fuel budget : ℕ) {reading : LanguageReading}
    (forms : Option (CanonicalForms RelationEnv.empty language fuel)) (compatible : FormsFor forms reading) :
    Decider RelationEnv.empty language reading :=
  (sortDecider RelationEnv.empty language (signatureOf language) fuel forms compatible 3 64 budget).orElse
    (predecessorDecider RelationEnv.empty language (signatureOf language) fuel forms compatible 3 64 budget)

/-- **Ask with what the executable knows for a language**: the certified forms of a language that has them, or its
sorted bags' forms; then, for a question the search leaves open, for a certified language, its certified decider and the
witness deciders; for a language with sorted bags whose premises are
guards, the modal decider over its sorted successors, the bag parts decider and named terms by sorted forms; otherwise
the bag parts decider of a language with sorted bags; or, for an equation-free language, the modal decider, which evaluates the connectives and the step modalities, context
labels included, at the listed successors, over the cut decider and the static decider, which decide the structural
formers on closed parts regions and the static formers at the term; and the witness deciders, which search witnesses of
the sort quantifiers and predecessors for the past modalities. The finder's cells are the hint. -/
def askKnown (language : LanguageDef) (fuel : ℕ) (formula : Formula 0) (term : Pattern) (hintBound budget : ℕ) :
    Answer :=
  match certifiedFormsOf language fuel with
  | some forms =>
    thenDecide (((certifiedDeciderOf language forms.reading).getD noDecider).orElse
        (sortsOf language fuel budget (some forms) (rfl : FormsFor (some forms) forms.reading))) formula term
      (askFound RelationEnv.empty language fuel formula term hintBound budget (some forms))
  | none =>
    if hasBags language then
      if noEquations : language.equations = [] then
        if noAlgebra : language.hasAlgebraDeclarations = false then
          if guarded : language.rewrites.all (fun rule => rule.premises.all BagForms.guard) = true then
            thenDecide
              (modalDecider (bagSuccessors fuel noEquations noAlgebra guarded)
                (((partsDecider (fuel := fuel) (presentations := List.singleton) (BagForms.canonical noEquations noAlgebra)
                  (BagForms.coherent noEquations noAlgebra guarded fuel) (BagForms.parts noEquations noAlgebra)
                  budget).orElse (namedDecider _ _ (BagForms.canonical noEquations noAlgebra))).orElse
                  (sortsOf language fuel budget (some (BagForms.forms noEquations noAlgebra guarded fuel)) rfl)))
              formula term
              (askFound RelationEnv.empty language fuel formula term hintBound budget
                (some (BagForms.forms noEquations noAlgebra guarded fuel)))
          else if queried : language.rewrites.all (fun rule => rule.premises.all BagForms.query) = true then
            thenDecide
              ((partsDecider (fuel := fuel) (presentations := List.singleton) (BagForms.canonical noEquations noAlgebra)
                (BagForms.coherentQueries noEquations noAlgebra queried BagForms.respectsCanon_empty fuel)
                (BagForms.parts noEquations noAlgebra) budget).orElse
                (sortsOf language fuel budget
                  (some (BagForms.formsQueries noEquations noAlgebra queried BagForms.respectsCanon_empty fuel)) rfl))
              formula term
              (askFound RelationEnv.empty language fuel formula term hintBound budget
                (some (BagForms.formsQueries noEquations noAlgebra queried BagForms.respectsCanon_empty fuel)))
          else thenDecide (sortsOf language fuel budget none (formsFor_none (reading := .syntax))) formula term
            (askFound RelationEnv.empty language fuel formula term hintBound budget none)
        else thenDecide (sortsOf language fuel budget none (formsFor_none (reading := .syntax))) formula term
          (askFound RelationEnv.empty language fuel formula term hintBound budget none)
      else thenDecide (sortsOf language fuel budget none (formsFor_none (reading := .syntax))) formula term
        (askFound RelationEnv.empty language fuel formula term hintBound budget none)
    else if free : language.isEquationFree = true then
      thenDecide (modalDecider (equationFreeSuccessors fuel free)
          (((equationFreeDecider free fuel budget).orElse (staticDecider free)).orElse
            (sortsOf language fuel budget none (formsFor_none (reading := .syntax)))))
        formula term (askFound RelationEnv.empty language fuel formula term hintBound budget none)
    else thenDecide (sortsOf language fuel budget none (formsFor_none (reading := .syntax))) formula term
      (askFound RelationEnv.empty language fuel formula term hintBound budget none)

/-- **What `askKnown` establishes holds**, in the reading of the forms the executable knows. -/
theorem askKnown_proved {language : LanguageDef} {fuel : ℕ} {formula : Formula 0} {term : Pattern}
    {hintBound budget : ℕ} {evidence : Evidence}
    (answered : askKnown language fuel formula term hintBound budget = .proved evidence) :
    (referenceStructure RelationEnv.empty language (formsReading (formsOf language fuel))).sat Env.closed formula term := by
  unfold askKnown at answered
  unfold formsOf
  split at answered
  · exact thenDecide_proved (fun found => askFound_proved found) answered
  · unfold bagFormsOf
    split at answered
    · rw [if_pos ‹_›]
      split at answered
      · rename_i noEquations
        rw [dif_pos noEquations]
        split at answered
        · rename_i noAlgebra
          rw [dif_pos noAlgebra]
          split at answered
          · rename_i guarded
            rw [dif_pos guarded]
            exact thenDecide_proved (fun found => askFound_proved found) answered
          · rename_i unguarded
            rw [dif_neg unguarded]
            split at answered
            · rename_i queried
              rw [dif_pos queried]
              exact thenDecide_proved (fun found => askFound_proved found) answered
            · rename_i unqueried
              rw [dif_neg unqueried]
              exact thenDecide_proved (fun found => askFound_proved found) answered
        · rename_i algebra
          rw [dif_neg algebra]
          exact thenDecide_proved (fun found => askFound_proved found) answered
      · rename_i equations
        rw [dif_neg equations]
        exact thenDecide_proved (fun found => askFound_proved found) answered
    · rw [if_neg ‹_›]
      split at answered
      · exact thenDecide_proved (fun found => askFound_proved found) answered
      · exact thenDecide_proved (fun found => askFound_proved found) answered

/-- **What `askKnown` refutes fails**, in the reading of the forms the executable knows. -/
theorem askKnown_refuted {language : LanguageDef} {fuel : ℕ} {formula : Formula 0} {term : Pattern}
    {hintBound budget : ℕ} {evidence : Evidence}
    (answered : askKnown language fuel formula term hintBound budget = .refuted evidence) :
    ¬ (referenceStructure RelationEnv.empty language (formsReading (formsOf language fuel))).sat Env.closed formula
      term := by
  unfold askKnown at answered
  unfold formsOf
  split at answered
  · exact thenDecide_refuted (fun found => askFound_refuted found) answered
  · unfold bagFormsOf
    split at answered
    · rw [if_pos ‹_›]
      split at answered
      · rename_i noEquations
        rw [dif_pos noEquations]
        split at answered
        · rename_i noAlgebra
          rw [dif_pos noAlgebra]
          split at answered
          · rename_i guarded
            rw [dif_pos guarded]
            exact thenDecide_refuted (fun found => askFound_refuted found) answered
          · rename_i unguarded
            rw [dif_neg unguarded]
            split at answered
            · rename_i queried
              rw [dif_pos queried]
              exact thenDecide_refuted (fun found => askFound_refuted found) answered
            · rename_i unqueried
              rw [dif_neg unqueried]
              exact thenDecide_refuted (fun found => askFound_refuted found) answered
        · rename_i algebra
          rw [dif_neg algebra]
          exact thenDecide_refuted (fun found => askFound_refuted found) answered
      · rename_i equations
        rw [dif_neg equations]
        exact thenDecide_refuted (fun found => askFound_refuted found) answered
    · rw [if_neg ‹_›]
      split at answered
      · exact thenDecide_refuted (fun found => askFound_refuted found) answered
      · exact thenDecide_refuted (fun found => askFound_refuted found) answered

/-- **The answer** of the front door, with the settings' fuel and hint, and what the executable knows for the
language (`askKnown`). It asks the language with its fitting scoped steps written as congruences (`flattenScoped`),
which has the same native types, so that strategies reading congruences apply to congruences under binders in core
form. -/
def answerWith (settings : Settings) (language : LanguageDef) (formula : Formula 0) (term : Pattern) (budget : ℕ) :
    Answer :=
  askKnown (flattenScoped language) settings.fuel formula term settings.hintBound budget

section Soundness

variable {settings : Settings} {language : LanguageDef} {formula : Formula 0} {term : Pattern} {budget : ℕ}
  {evidence : Evidence}

/-- **What the executable establishes holds of the language read from the file**, in the reading of its forms. -/
theorem answerWith_proved (answered : answerWith settings language formula term budget = .proved evidence)
    (reference : (formsReading (formsOf (flattenScoped language) settings.fuel)).rules = .reference) :
    (referenceStructure RelationEnv.empty language (formsReading (formsOf (flattenScoped language) settings.fuel))).sat
      Env.closed formula term :=
  (sat_flattenScoped_iff RelationEnv.empty language _ reference Env.closed formula term).mp (askKnown_proved answered)

/-- **What the executable refutes fails of the language read from the file**, in the reading of its forms. -/
theorem answerWith_refuted (answered : answerWith settings language formula term budget = .refuted evidence)
    (reference : (formsReading (formsOf (flattenScoped language) settings.fuel)).rules = .reference) :
    ¬ (referenceStructure RelationEnv.empty language (formsReading (formsOf (flattenScoped language) settings.fuel))).sat
      Env.closed formula term := fun holds =>
  askKnown_refuted answered ((sat_flattenScoped_iff RelationEnv.empty language _ reference Env.closed formula term).mpr holds)

end Soundness

/-! ## Languages run in the environment of their definitions -/

open Mettapedia.Languages.ProcessCalculi.CCS.Recursive (Definition admits definitionsEnv ccsRecCalc)

/-- **Ask CCS with recursion in the environment of admitted definitions**: with the canonical forms its theorems
certify, then, for a question the search leaves open, its modal decider, which answers its partners' labels and named
terms. -/
def askRecursive (definitions : List Definition) (admitted : admits definitions = true) (fuel : ℕ) (formula : Formula 0)
    (term : Pattern) (hintBound budget : ℕ) : Answer :=
  thenDecide (CCSRecPartners.decider admitted) formula term
    (askFound (definitionsEnv definitions) ccsRecCalc fuel formula term hintBound budget
      (some (CCSRecForms.forms admitted fuel)))

/-- **What `askRecursive` establishes holds** of CCS with recursion in the environment of the definitions. -/
theorem askRecursive_proved {definitions : List Definition} {admitted : admits definitions = true} {fuel : ℕ}
    {formula : Formula 0} {term : Pattern} {hintBound budget : ℕ} {evidence : Evidence}
    (answered : askRecursive definitions admitted fuel formula term hintBound budget = .proved evidence) :
    (referenceStructure (definitionsEnv definitions) ccsRecCalc CCSRecForms.reading).sat Env.closed formula term :=
  thenDecide_proved (fun found => askFound_proved found) answered

/-- **What `askRecursive` refutes fails** of CCS with recursion in the environment of the definitions. -/
theorem askRecursive_refuted {definitions : List Definition} {admitted : admits definitions = true} {fuel : ℕ}
    {formula : Formula 0} {term : Pattern} {hintBound budget : ℕ} {evidence : Evidence}
    (answered : askRecursive definitions admitted fuel formula term hintBound budget = .refuted evidence) :
    ¬ (referenceStructure (definitionsEnv definitions) ccsRecCalc CCSRecForms.reading).sat Env.closed formula term :=
  thenDecide_refuted (fun found => askFound_refuted found) answered

/-! ## Definitions beside a language

CCS with recursion is asked in the environment of its definitions: a program, given beside the language, not part of
it. A definitions file writes one definition a line: its arity, then its summands in the executable's term syntax, the
parameters as bound variables, `1 | (CAct (bvar 0) (CCall CZ (CArgCons (bvar 0) CArgNil)))`. A call names its constant
by the definition's position, `CZ`, `(CS CZ)`, …. Blank lines and lines starting with `#` are skipped. -/

/-- **Definitions as text**, one a line. -/
def definitionsText (definitions : List Definition) : String :=
  String.join (definitions.map fun definition =>
    " | ".intercalate (toString definition.arity :: definition.guards.map patternText) ++ "\n")

/-- **Definitions from a text**, as `definitionsText` writes them. -/
def readDefinitions (text : String) : Except String (List Definition) :=
  (text.splitOn "\n").filterMap (fun line =>
      let trimmed := line.trimAscii.toString
      if trimmed.isEmpty || trimmed.startsWith "#" then none else some trimmed)
    |>.mapM fun line =>
      match (line.splitOn "|").map (·.trimAscii.toString) with
      | arity :: guards =>
        match arity.toNat? with
        | some arity => do pure ⟨arity, ← guards.mapM readPattern⟩
        | none => .error s!"not an arity: {arity}"
      | [] => .error s!"a definition needs its arity: {line}"

/-- The displayed status of an answer. -/
def display : Answer → String
  | .proved evidence => s!"established, by {Verdicts.describe evidence}"
  | .refuted evidence => s!"refuted, by {Verdicts.describe evidence}"
  | .unknown rounds => s!"suspended after {rounds} rounds"

/-! ## Resumed answers

The search is resumed from one budget to the next with the progress of the question (`Resumption.Progress`), grown
with the canonical forms the executable knows, so that a resumed question answers as asking afresh with all the rounds
(`Resumption.resumed_answer`); then what it leaves open is settled as `askKnown` settles it (`settleKnown`). So each
resumed answer is the executable's answer at its budget (`answers_eq`). -/

section Resumed

variable {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ}
  {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature} {formula : Formula 0} {term : Pattern}

/-- The answers at the budgets that follow, each from the progress resumed to it and settled at it. -/
def resumeAnswers (settle : ℕ → Answer → Answer) (forms : Option (CanonicalForms relEnv language fuel))
    (hint : Option CertificateCandidate) (progress : Progress language signature formula term) :
    List ℕ → List (ℕ × Answer)
  | [] => []
  | budget :: rest =>
    let resumed := progress.resume relEnv fuel (canonOf forms) (presentationsOf forms)
      (budget - progress.rounds) (rulesOf forms)
    (resumed.rounds, settle resumed.rounds (resumed.answer relEnv fuel forms hint)) ::
      resumeAnswers settle forms hint resumed rest

/-- **Each resumed answer is the answer afresh**, from a progress grown with the forms. -/
theorem resumeAnswers_eq (settle : ℕ → Answer → Answer) (forms : Option (CanonicalForms relEnv language fuel))
    (hint : Option CertificateCandidate) :
    ∀ (budgets : List ℕ) (rounds : ℕ) (entry : ℕ × Answer),
      entry ∈ resumeAnswers settle forms hint
        (Progress.at relEnv language fuel signature formula term (canonOf forms) (presentationsOf forms)
          rounds (rulesOf forms)) budgets →
      entry.2 = settle entry.1 (ask relEnv signature language fuel formula term hint entry.1 forms)
  | [], _, _, member => by simp [resumeAnswers] at member
  | budget :: rest, rounds, entry, member => by
    simp only [resumeAnswers, List.mem_cons] at member
    rw [resume_at (rules := rulesOf forms)] at member
    rcases member with rfl | later
    · exact congrArg (settle _) (answer_at _ _ _ _ _)
    · exact resumeAnswers_eq settle forms hint rest _ entry later

end Resumed

/-- **What the executable settles of an answer its search leaves open**, at a budget: the deciders `askKnown` takes for
the language. -/
def settleKnown (language : LanguageDef) (fuel : ℕ) (formula : Formula 0) (term : Pattern) (budget : ℕ) :
    Answer → Answer :=
  match certifiedFormsOf language fuel with
  | some forms =>
    thenDecide (((certifiedDeciderOf language forms.reading).getD noDecider).orElse
        (sortsOf language fuel budget (some forms) (rfl : FormsFor (some forms) forms.reading))) formula term
  | none =>
    if hasBags language then
      if noEquations : language.equations = [] then
        if noAlgebra : language.hasAlgebraDeclarations = false then
          if guarded : language.rewrites.all (fun rule => rule.premises.all BagForms.guard) = true then
            thenDecide
              (modalDecider (bagSuccessors fuel noEquations noAlgebra guarded)
                (((partsDecider (fuel := fuel) (presentations := List.singleton) (BagForms.canonical noEquations noAlgebra)
                  (BagForms.coherent noEquations noAlgebra guarded fuel) (BagForms.parts noEquations noAlgebra)
                  budget).orElse (namedDecider _ _ (BagForms.canonical noEquations noAlgebra))).orElse
                  (sortsOf language fuel budget (some (BagForms.forms noEquations noAlgebra guarded fuel)) rfl)))
              formula term
          else if queried : language.rewrites.all (fun rule => rule.premises.all BagForms.query) = true then
            thenDecide
              ((partsDecider (fuel := fuel) (presentations := List.singleton) (BagForms.canonical noEquations noAlgebra)
                (BagForms.coherentQueries noEquations noAlgebra queried BagForms.respectsCanon_empty fuel)
                (BagForms.parts noEquations noAlgebra) budget).orElse
                (sortsOf language fuel budget
                  (some (BagForms.formsQueries noEquations noAlgebra queried BagForms.respectsCanon_empty fuel)) rfl))
              formula term
          else thenDecide (sortsOf language fuel budget none (formsFor_none (reading := .syntax))) formula term
        else thenDecide (sortsOf language fuel budget none (formsFor_none (reading := .syntax))) formula term
      else thenDecide (sortsOf language fuel budget none (formsFor_none (reading := .syntax))) formula term
    else if free : language.isEquationFree = true then
      thenDecide (modalDecider (equationFreeSuccessors fuel free)
          (((equationFreeDecider free fuel budget).orElse (staticDecider free)).orElse
            (sortsOf language fuel budget none (formsFor_none (reading := .syntax)))))
        formula term
    else thenDecide (sortsOf language fuel budget none (formsFor_none (reading := .syntax))) formula term

/-- **`askKnown` is the search with the forms the executable knows, settled.** -/
theorem askKnown_eq (language : LanguageDef) (fuel : ℕ) (formula : Formula 0) (term : Pattern) (hintBound budget : ℕ) :
    askKnown language fuel formula term hintBound budget =
      settleKnown language fuel formula term budget
        (askFound RelationEnv.empty language fuel formula term hintBound budget (formsOf language fuel)) := by
  unfold askKnown settleKnown formsOf bagFormsOf
  cases certifiedFormsOf language fuel with
  | some forms => rfl
  | none => split_ifs <;> rfl

/-- **Ask the front door** about a term of a language, at each budget in turn, resuming the question's progress from
one budget to the next, grown with the canonical forms the executable knows, and settling each answer as `askKnown`
does. -/
def answers (settings : Settings) (language : LanguageDef) (formula : Formula 0) (term : Pattern) (budgets : List ℕ) :
    List (ℕ × Answer) :=
  let language := flattenScoped language
  let signature := signatureOf language
  let hint := findHint signature language formula term settings.hintBound
  let forms := formsOf language settings.fuel
  let settle := fun budget => settleKnown language settings.fuel formula term budget
  match budgets with
  | [] => []
  | first :: rest =>
    let start := Progress.at RelationEnv.empty language settings.fuel signature formula term (canonOf forms)
      (presentationsOf forms) first (rulesOf forms)
    (first, settle first (start.answer RelationEnv.empty settings.fuel forms hint)) ::
      resumeAnswers settle forms hint start rest

/-- **Every resumed answer is the executable's answer at its budget**: resuming from one budget to the next answers as
asking afresh. -/
theorem answers_eq (settings : Settings) (language : LanguageDef) (formula : Formula 0) (term : Pattern)
    (budgets : List ℕ) :
    ∀ entry ∈ answers settings language formula term budgets,
      entry.2 = answerWith settings language formula term entry.1 := by
  intro entry member
  unfold answers at member
  rw [answerWith, askKnown_eq]
  split at member
  · simp at member
  · simp only [List.mem_cons] at member
    rcases member with rfl | later
    · simp only
      rw [answer_at]
      rfl
    · rw [resumeAnswers_eq _ _ _ _ _ entry later]
      rfl

/-- **Ask CCS with recursion** in the environment of admitted definitions, at each budget in turn, resuming the
question's progress from one budget to the next, grown with the forms certified for that environment, and settling each
answer with its decider, as `askRecursive` does. -/
def answersRecursive (definitions : List Definition) (admitted : admits definitions = true) (settings : Settings)
    (formula : Formula 0) (term : Pattern) (budgets : List ℕ) : List (ℕ × Answer) :=
  let signature := signatureOf ccsRecCalc
  let hint := findHint signature ccsRecCalc formula term settings.hintBound
  let forms := some (CCSRecForms.forms admitted settings.fuel)
  let settle := fun (_ : ℕ) => thenDecide (CCSRecPartners.decider admitted) formula term
  match budgets with
  | [] => []
  | first :: rest =>
    let start := Progress.at (definitionsEnv definitions) ccsRecCalc settings.fuel signature formula term
      (canonOf forms) (presentationsOf forms) first (rulesOf forms)
    (first, settle first (start.answer (definitionsEnv definitions) settings.fuel forms hint)) ::
      resumeAnswers settle forms hint start rest

/-- **Every resumed answer of CCS with recursion is `askRecursive`'s at its budget.** -/
theorem answersRecursive_eq (definitions : List Definition) (admitted : admits definitions = true)
    (settings : Settings) (formula : Formula 0) (term : Pattern) (budgets : List ℕ) :
    ∀ entry ∈ answersRecursive definitions admitted settings formula term budgets,
      entry.2 = askRecursive definitions admitted settings.fuel formula term settings.hintBound entry.1 := by
  intro entry member
  unfold answersRecursive at member
  unfold askRecursive askFound
  split at member
  · simp at member
  · simp only [List.mem_cons] at member
    rcases member with rfl | later
    · simp only
      rw [answer_at]
    · exact resumeAnswers_eq _ _ _ _ _ entry later

/-- The answers CCS with recursion takes from a definitions text. -/
def withDefinitions {α : Type} (definitionsText : Option String)
    (ask : (definitions : List Definition) → admits definitions = true → α) : Except String α :=
  match definitionsText with
  | none => .error "CCS with recursion is asked in the environment of its definitions: give definitions=FILE"
  | some text => do
    let definitions ← readDefinitions text
    if admitted : admits definitions = true then pure (ask definitions admitted)
    else .error "the definitions are not admitted: each summand is a guard over its parameters"

/-- **The executable's answers at each budget**: CCS with recursion in the environment of the definitions given beside
it (`answersRecursive`), every other language in the empty environment (`answers`). -/
def answersFor (settings : Settings) (language : LanguageDef) (formula : Formula 0) (term : Pattern)
    (budgets : List ℕ) (definitionsText : Option String) : Except String (List (ℕ × Answer)) :=
  if language = ccsRecCalc then
    withDefinitions definitionsText fun definitions admitted =>
      answersRecursive definitions admitted settings formula term budgets
  else
    match definitionsText with
    | some _ => .error s!"only CCS with recursion takes definitions, not {language.name}"
    | none => pure (answers settings language formula term budgets)

/-- **The executable's answer at a budget**: as `answersFor`, asked once. -/
def answerFor (settings : Settings) (language : LanguageDef) (formula : Formula 0) (term : Pattern) (budget : ℕ)
    (definitionsText : Option String) : Except String Answer :=
  if language = ccsRecCalc then
    withDefinitions definitionsText fun definitions admitted =>
      askRecursive definitions admitted settings.fuel formula term settings.hintBound budget
  else
    match definitionsText with
    | some _ => .error s!"only CCS with recursion takes definitions, not {language.name}"
    | none => pure (answerWith settings language formula term budget)

/-- **The report** of the command-line front door. -/
def report (loaded : Except Mettapedia.GSLT.LanguageDef.ModuleSource.Error LanguageDef) (formulaText termText : String)
    (budgets : List ℕ) (settingWords : List String := []) (definitionsText : Option String := none) : IO Unit := do
  match readingOf loaded, Settings.read settingWords with
  | .error problem, _ | _, .error problem => throw (IO.userError s!"oslf: {problem}")
  | .ok language, .ok settings =>
    match readFormula (language.rewrites.map fun rule : RewriteRule => rule.name) formulaText, readPattern termText with
    | .error problem, _ | _, .error problem => throw (IO.userError s!"oslf: {problem}")
    | .ok formula, .ok term =>
      IO.println s!"language {language.name}: {language.terms.length} constructors, {language.rewrites.length} rules, {language.equations.length} equations"
      match answersFor settings language formula term budgets definitionsText with
      | .error problem => throw (IO.userError s!"oslf: {problem}")
      | .ok answered =>
        for (budget, answer) in answered do
          IO.println s!"budget {budget}: {display answer}"

/-- The kind of a status: established, refuted or suspended. -/
def statusKind : Answer → String
  | .proved _ => "established"
  | .refuted _ => "refuted"
  | .unknown _ => "suspended"

/-- Whether an answer is as expected: a status (`established`, `refuted`, `suspended`), or an answer in brief (`P`
or `R` with the kind of evidence, or `open`). -/
def asExpected (expected : String) (answer : Answer) : Bool :=
  if ["established", "refuted", "suspended"].contains expected then statusKind answer == expected
  else Verdicts.answerSummary answer == expected

/-- **Check rows of the matrix**: each language, formula, term, budget and settings against the expected answer.
Fails when some row does not answer as expected. -/
def checkRows (rows : List (String × Except Mettapedia.GSLT.LanguageDef.ModuleSource.Error LanguageDef × String ×
    String × ℕ × String × List String × Option String)) : IO Unit := do
  let mut failures := 0
  let mut total := 0
  for (label, loaded, formulaText, termText, budget, expected, settingWords, definitionsText) in rows do
    let read := do
      let language ← readingOf loaded
      let settings ← Settings.read settingWords
      let formula ← readFormula (language.rewrites.map fun rule : RewriteRule => rule.name) formulaText
      let term ← readPattern termText
      pure (language, settings, formula, term)
    match read with
    | .error problem =>
      failures := failures + 1
      IO.println s!"FAIL {label} {formulaText} {termText}: {problem}"
    | .ok (language, settings, formula, term) =>
      let start ← IO.monoNanosNow
      let answered ← IO.lazyPure fun _ => answerFor settings language formula term budget definitionsText
      let time := ((← IO.monoNanosNow) - start) / 1000
      total := total + time
      match answered with
      | .error problem =>
          failures := failures + 1
          IO.println s!"FAIL {label} {formulaText} {termText}: {problem}"
      | .ok answer =>
          if asExpected expected answer then
            IO.println s!"ok   {label} {formulaText} at {termText}: {display answer} [{time} µs]"
          else
            failures := failures + 1
            IO.println s!"FAIL {label} {formulaText} at {termText}: expected {expected}, {display answer} [{time} µs]"
  IO.println s!"{rows.length - failures} of {rows.length} rows as expected, answered in {total / 1000} ms"
  if failures > 0 then throw (IO.userError s!"{failures} rows did not answer as expected")

end Mettapedia.OSLF.NativeTypes.Product
