import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagQuery

/-! A normalization stage for unconditional source equations with one flat
ACU carrier. Other sorts retain their ordinary constructors. Bag variables
denote whole residual payloads, including in nested right-hand-side terms.
Typed context traversal is supplied by the existing execution plan.
Normalization, confluence and source adequacy remain separate certificates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUEquationCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def bagTerm? {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (term : Maude.Term) : Option Pattern := do
  let parts := operation.flatten term
  let names := parts.filterMap ACUBagQuery.componentName?
  let rest ← match names with
    | [] => some none
    | [name] => some (some name)
    | _ => none
  let heads := parts.filter ACUBagQuery.isHead
  if heads.all (ACUBagCompilation.flatToken operation.declaration) then
    some (ACUBagPresentation.pack (ACUBagCompilation.wrapperName operation.declaration) heads rest)
  else none

mutual
  def term? {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
      (context : Maude.VariableContext) (source : Maude.Term) : Option Pattern := do
    let sort ← Maude.inferSort? theory.signature context source
    if sort = operation.declaration.result then bagTerm? operation source else
      match source with
      | .var name => some (.fvar name)
      | .app label arguments => do pure (.apply label (← arguments? operation context arguments))
  termination_by sizeOf source

  def arguments? {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
      (context : Maude.VariableContext) (sources : List Maude.Term) : Option (List Pattern) :=
    match sources with
    | [] => some []
    | first :: rest => do pure ((← term? operation context first) :: (← arguments? operation context rest))
  termination_by sizeOf sources
end

def nativeType (declaration : Maude.Operator) (sort : String) : TypeExpr :=
  if sort = declaration.result then .collection .hashBag (.base (ACUBagCompilation.tokenSort declaration))
  else .base sort

def equationRule? {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (row : Maude.Row) (index : Nat) : Option RewriteRule := do
  if row.conditions.isEmpty && row.inputsBound then
    let sort ← Maude.inferSort? theory.signature row.usedContext row.left
    if sort = operation.declaration.result then
      if row.left.variables.isEmpty && row.right.variables.isEmpty then
        let rule := ACUBagCompilation.compileRule operation row index
        pure {rule with name := "maude:acu:equation:" ++ toString index ++ ":" ++ row.name}
      else none
    else
    pure {
      name := "maude:acu:equation:" ++ toString index ++ ":" ++ row.name
      typeContext := row.usedContext.map fun entry => (entry.1, nativeType operation.declaration entry.2)
      premises := []
      left := ← term? operation row.usedContext row.left
      right := ← term? operation row.usedContext row.right }
  else none

structure Prepared where
  source : Maude.Theory
  language : LanguageDef
  equationOrigins : List Nat

def carrierSupported {theory : Maude.Theory} (operation : Maude.ACUOperation theory []) : Bool :=
  theory.signature.operators.all (fun declaration =>
      if declaration.id == operation.declaration.id then true else
      (!declaration.attributes.associative && !declaration.attributes.commutative && declaration.attributes.identity.isNone) &&
        (declaration.result != operation.declaration.result || declaration.arguments.isEmpty))

def stageLanguage {theory : Maude.Theory} (operation : Maude.ACUOperation theory [])
    (rewrites : List RewriteRule) : LanguageDef :=
  let declarations := theory.signature.operators.filterMap fun declaration =>
    if declaration.id == operation.declaration.id || some (.app declaration.id []) == some operation.unit then none else
    if declaration.result == operation.declaration.result then
      some (ACUBagCompilation.tokenDeclaration operation.declaration declaration)
    else some (operator declaration)
  {
    name := theory.name ++ ":ACU-equations"
    types := theory.signature.sorts.map TypeDecl.plain ++ [TypeDecl.plain (ACUBagCompilation.tokenSort operation.declaration)]
    terms := ACUBagCompilation.wrapperDeclaration operation.declaration :: declarations
    equations := []
    rewrites := rewrites }

def prepare {theory : Maude.Theory} (operation : Maude.ACUOperation theory []) : Except String Prepared := do
  unless theory.check do throw "the source theory is ill-sorted"
  unless carrierSupported operation do throw "the selected normalization stage requires one flat ACU carrier"
  let some equations := theory.equations.zipIdx.mapM (fun (row,index) => equationRule? operation row index)
    | throw "an equation requires a stronger binding or condition realizer"
  let language := stageLanguage operation equations
  unless language.validate.isEmpty do throw "the generated ACU normalization stage is invalid"
  pure ⟨theory, language, List.range theory.equations.length⟩

/-- A derived pointwise normalization step licensed by B B = B. The
physical carrier stays a bag; each firing consumes two equal occurrences. -/
def duplicateRule (declaration : Maude.Operator) (rowName : String) : RewriteRule :=
  let element := "maude:acu:element"
  let rest := ACUBagCompilation.restName
  let bag := fun parts => Pattern.apply (ACUBagCompilation.wrapperName declaration)
    [.collection .hashBag parts (some rest)]
  {
    name := "maude:acu:derived-idempotence:0:" ++ rowName
    typeContext := [(element, .base (ACUBagCompilation.tokenSort declaration)),
      (rest, .collection .hashBag (.base (ACUBagCompilation.tokenSort declaration)))]
    premises := []
    left := bag [.fvar element, .fvar element]
    right := bag [.fvar element] }

def prepareIdempotence {theory : Maude.Theory} (operation : Maude.ACUOperation theory []) : Except String Prepared := do
  unless theory.check && carrierSupported operation do throw "the source needs a different ACU carrier profile"
  let [row] := theory.equations | throw "this stage requires the single authored idempotence equation"
  let .app label [.var first, .var second] := row.left | throw "the equation is not binary idempotence"
  let .var result := row.right | throw "the idempotence result must be its repeated variable"
  unless label == operation.declaration.id && first == second && first == result && row.conditions.isEmpty &&
      row.usedContext == [(first, operation.declaration.result)] do
    throw "the equation does not declare unconditional idempotence on this carrier"
  let language := stageLanguage operation [duplicateRule operation.declaration row.name]
  unless language.validate.isEmpty do throw "the generated idempotence stage is invalid"
  pure ⟨theory, language, [0]⟩

def plan (prepared : Prepared) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    ⟨prepared.language, [], {signatures := [], rows := []}⟩
    {sites := .all, includeDerivedEquations := false}

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUEquationCompilation
