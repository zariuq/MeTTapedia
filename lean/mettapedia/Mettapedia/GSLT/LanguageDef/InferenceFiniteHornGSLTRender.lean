import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Finite-Horn GSLT projection of inference presentations

This module renders the constructor-only, first-order fragment of an inference
presentation as a `gslt-presentation-v1` artifact.  The artifact is semantic
source data for the staged CeTTa pipeline; it is not an execution trace and it
does not add a runtime checker.

The projection fails closed.  It rejects binders, substitutions, collections,
side conditions, unsafe external names, non-application judgments, and every
positive-arity application absent from the derived signature.  Nullary
constructors remain atoms, as required by the v1 finite-Horn schema.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Characters accepted by the unquoted finite-Horn S-expression carrier. -/
def safeTokenCharacter (character : Char) : Bool :=
  !character.isWhitespace &&
  character != '(' && character != ')' &&
  character != ';' && character != '"'

/-- A nonempty token with no delimiter or comment introducer. -/
def safeToken (value : String) : Bool :=
  !value.isEmpty && value.toList.all safeTokenCharacter

/-- The schema parser treats these spellings as integers rather than symbols. -/
def integerToken (value : String) : Bool :=
  match value.toList with
  | '-' :: digits => !digits.isEmpty && digits.all Char.isDigit
  | characters => !characters.isEmpty && characters.all Char.isDigit

/-- A name that round-trips as a symbol rather than a variable or integer. -/
def safeSymbol (value : String) : Bool :=
  safeToken value && !value.startsWith "?" && !integerToken value

/-- A metavariable name that round-trips after the schema's leading `?`. -/
def safeVariable (value : String) : Bool :=
  safeToken value && value != "_"

abbrev OperatorKey := String × Nat

/-- Positive-arity constructors and judgments form the finite-Horn signature,
in authored order. -/
def operatorSignature (presentation : Presentation) : List OperatorKey :=
  ((presentation.language.terms.map fun declaration =>
      (declaration.label, declaration.params.length)) ++
    (presentation.calculus.judgments.map fun declaration =>
      (declaration.head, declaration.arity))).filter
        (fun declaration => declaration.2 > 0)

/-- Duplicate declarations are rejected rather than silently merged. -/
def noDuplicateOperators : List OperatorKey → Bool
  | [] => true
  | operator :: operators =>
      !operators.contains operator && noDuplicateOperators operators

mutual

/-- Render a pattern in the first-order source fragment. -/
def renderTerm? (signature : List OperatorKey) : Pattern → Option String
  | .fvar name =>
      if safeVariable name then some s!"?{name}" else none
  | .apply head [] =>
      if safeSymbol head then some head else none
  | .apply head arguments => do
      if !safeSymbol head || !signature.contains (head, arguments.length) then
        none
      else
        let rendered ← renderTerms? signature arguments
        some s!"({head} {String.intercalate " " rendered})"
  | _ => none
termination_by pattern => 2 * sizeOf pattern

def renderTerms? (signature : List OperatorKey) :
    List Pattern → Option (List String)
  | [] => some []
  | pattern :: patterns => do
      let head ← renderTerm? signature pattern
      let tail ← renderTerms? signature patterns
      some (head :: tail)
termination_by patterns => 2 * sizeOf patterns + 1

end

/-- V1 rules require applications at the head and every body position. -/
def isApplication : Pattern → Bool
  | .apply _ _ => true
  | _ => false

/-- Render one named Horn rule without manufacturing side-condition evidence. -/
def renderRule? (signature : List OperatorKey) (rule : RuleSchema) :
    Option String := do
  if !safeSymbol rule.id.value ||
      !rule.sideConditions.isEmpty ||
      !(rule.metavariables.all fun formal =>
        formal.2 == 0 && safeVariable formal.1) ||
      !isApplication rule.conclusion ||
      !(rule.premises.all isApplication) then
    none
  else
    let conclusion ← renderTerm? signature rule.conclusion
    let premises ← renderTerms? signature rule.premises
    some s!"    (rule {rule.id.value} (head {conclusion}) (body{if premises.isEmpty then "" else " "}{String.intercalate " " premises}))"

def renderRules? (signature : List OperatorKey) :
    List RuleSchema → Option (List String)
  | [] => some []
  | rule :: rules => do
      let head ← renderRule? signature rule
      let tail ← renderRules? signature rules
      some (head :: tail)

def renderOperator? (operator : OperatorKey) : Option String := do
  if !safeSymbol operator.1 || operator.2 == 0 then
    none
  else
    some s!"    (operator {operator.1} {operator.2})"

def renderOperators? : List OperatorKey → Option (List String)
  | [] => some []
  | operator :: operators => do
      let head ← renderOperator? operator
      let tail ← renderOperators? operators
      some (head :: tail)

/-- Render one complete `gslt-presentation-v1`, retaining authored rule order. -/
def renderPresentation? (presentation : Presentation) : Option String := do
  if !safeSymbol presentation.language.name then
    none
  else
    let signature := operatorSignature presentation
    if !noDuplicateOperators signature then
      none
    else
      let operators ← renderOperators? signature
      let rules ← renderRules? signature presentation.rules
      some <|
        s!"(gslt-presentation-v1 {presentation.language.name}\n" ++
        "  (signature\n" ++ String.intercalate "\n" operators ++ "\n  )\n" ++
        "  (equations)\n" ++
        "  (rewrites\n" ++ String.intercalate "\n" rules ++ "\n  ))\n"

private def positivePresentation : Presentation :=
  { language :=
      { name := "PositiveFiniteHorn"
        types := []
        terms := []
        equations := []
        rewrites := [] }
    calculus :=
      { judgments := [{ head := "holds", arity := 1 }]
        rules :=
          [{ id := ⟨"holds-seed"⟩
             metavariables := []
             premises := []
             conclusion := .apply "holds" [.apply "seed" []] }] } }

/-- Positive canary: a constructor-only judgment becomes a valid finite-Horn
presentation with its judgment operator derived into the signature. -/
theorem positivePresentation_renders :
    (renderPresentation? positivePresentation).isSome = true := by
  simp [renderPresentation?, positivePresentation, operatorSignature,
    renderOperators?, renderOperator?, renderRules?, renderRule?, renderTerm?,
    renderTerms?, safeSymbol, safeVariable, safeToken, safeTokenCharacter,
    integerToken, noDuplicateOperators, isApplication]

private def negativePresentation : Presentation :=
  { language :=
      { name := "NegativeFiniteHorn"
        types := []
        terms := []
        equations := []
        rewrites := [] }
    calculus :=
      { judgments := [{ head := "holds", arity := 1 }]
        rules :=
          [{ id := ⟨"unsafe rule name"⟩
             metavariables := []
             premises := []
             conclusion := .apply "holds" [.apply "seed" []] }] } }

/-- Negative canary: unsafe external names are refused, never quoted into a
different schema object. -/
theorem negativePresentation_is_refused :
    renderPresentation? negativePresentation = none := by
  simp [renderPresentation?, negativePresentation, operatorSignature,
    renderOperators?, renderOperator?, renderRules?, renderRule?, safeSymbol,
    safeVariable, safeToken, safeTokenCharacter, integerToken,
    noDuplicateOperators, isApplication]

end Mettapedia.GSLT.LanguageDef.InferenceFiniteHornGSLTRender
