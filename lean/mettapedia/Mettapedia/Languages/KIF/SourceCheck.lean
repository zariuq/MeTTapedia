import Mettapedia.Languages.KIF.DeclarationDecode
import Mettapedia.Languages.KIF.NestingAudit
import Mettapedia.Languages.KIF.LogicalSyntaxAudit
import Mettapedia.Languages.KIF.BindingAudit
import Mettapedia.Languages.KIF.SignatureAudit

/-!
# Command-line structural checker for SUO-KIF sources

This executable reports lexical and parenthesis diagnostics with exact source
locations. It is intentionally only the source-structure layer; logical
elaboration and inference are separate checked stages.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF.SourceCheck

def positionText (position : SourcePos) : String :=
  s!"{position.line}:{position.column}"

def spanText (span : SourceSpan) : String :=
  s!"{positionText span.start}-{positionText span.stop}"

def lexErrorText (failure : LexError) : String :=
  match failure.kind with
  | .unclosedString =>
      s!"{spanText failure.span}: unclosed string literal"
  | .internalFuelExhausted =>
      s!"{spanText failure.span}: internal lexer fuel exhausted"

def parseErrorText (failure : ParseError) : String :=
  match failure.kind with
  | .unexpectedClose =>
      s!"{spanText failure.span}: unmatched closing parenthesis"
  | .unclosedList =>
      s!"{spanText failure.span}: unclosed opening parenthesis"

def declarationErrorText (failure : DeclarationError) : String :=
  let detail :=
    match failure.kind with
    | .wrongArity head expected actual =>
        s!"{head} expects {expected} arguments, received {actual}"
    | .expectedSymbol => "expected a symbol"
    | .expectedNatural => "expected a natural-number argument position"
    | .expectedString => "expected a string literal"
  s!"{spanText failure.span}: {detail}"

def nestingIssueText (issue : NestingIssue) : String :=
  s!"{spanText issue.span}: column-one form begins at nesting depth {issue.enclosingDepth}"

def logicalSyntaxIssueText (issue : LogicalSyntaxIssue) : String :=
  let detail :=
    match issue.kind with
    | .wrongArity head expected actual =>
        s!"logical form {head} expects {expected} arguments, received {actual}"
    | .malformedBinderList quantifier =>
        s!"{quantifier} expects a nonempty list of regular or row variables"
    | .misspelledExists => "unknown logical form `exist`; expected `exists`"
    | .internalFuelExhausted => "internal logical-audit fuel exhausted"
  s!"{spanText issue.span}: {detail}"

def bindingIssueText (issue : BindingIssue) : String :=
  let detail :=
    match issue.kind with
    | .duplicateBinder quantifier variableName =>
        s!"{quantifier} binds {variableName} more than once"
    | .unusedBinder quantifier variableName =>
        s!"{quantifier} binds unused variable {variableName}"
    | .internalFuelExhausted => "internal binding-audit fuel exhausted"
  s!"{spanText issue.span}: {detail}"

def signatureIssueText (issue : SignatureIssue) : String :=
  let detail :=
    match issue.kind with
    | .conflictingFixedArities name arities =>
        s!"{name} inherits conflicting fixed arities {arities}"
    | .wrongApplicationArity name expected actual =>
        s!"{name} expects {expected} arguments, received {actual}"
    | .domainBeyondFixedArity name arity position =>
        s!"{name} has fixed arity {arity} but declares argument {position}"
    | .internalFuelExhausted => "internal signature-audit fuel exhausted"
    | .internalClassClosureFuelExhausted =>
        "internal signature subclass-closure fuel exhausted"
  s!"{spanText issue.span}: {detail}"

def operatorSummaryText (summary : OperatorSummary) : String :=
  s!"{spanText summary.firstSpan}: {summary.name} used at arities {summary.observedArities}"

private structure SourceUnit where
  path : String
  lexed : Lexed
  parsed : Parsed
  inventory : DeclarationInventory

unsafe def readSourceUnit (path : String) : IO (Except String SourceUnit) := do
  let source ← IO.FS.readFile path
  match lex source with
  | .error failure =>
      return .error s!"{path}:{lexErrorText failure}"
  | .ok lexed =>
      let parsed := parse lexed
      return .ok ⟨path, lexed, parsed, declarationInventory parsed⟩

unsafe def readSourceUnits : List String → IO (Except String (List SourceUnit))
  | [] => pure (.ok [])
  | path :: rest => do
      match ← readSourceUnit path with
      | .error message => pure (.error message)
      | .ok source =>
          match ← readSourceUnits rest with
          | .error message => pure (.error message)
          | .ok sources => pure (.ok (source :: sources))

private def sourceUnitValidForDeclarations (source : SourceUnit) : Bool :=
  source.parsed.errors.isEmpty && source.inventory.errors.isEmpty

unsafe def reportImportedSource (source : SourceUnit) : IO Unit := do
  IO.println s!"import source: {source.path}"
  IO.println s!"import top-level forms: {source.parsed.forms.length}"
  IO.println s!"import structural errors: {source.parsed.errors.length}"
  for failure in source.parsed.errors do
    IO.eprintln s!"{source.path}:{parseErrorText failure}"
  IO.println s!"import declarations: {source.inventory.declarations.length}"
  IO.println s!"import declaration errors: {source.inventory.errors.length}"
  for failure in source.inventory.errors do
    IO.eprintln s!"{source.path}:{declarationErrorText failure}"

unsafe def checkFile (path : String) (importPaths : List String) : IO UInt32 := do
  let targetResult ← readSourceUnit path
  let importsResult ← readSourceUnits importPaths
  match targetResult, importsResult with
  | .error message, _ | _, .error message =>
      IO.eprintln message
      return 1
  | .ok target, .ok imports =>
      for imported in imports do
        reportImportedSource imported
      let lexed := target.lexed
      let parsed := target.parsed
      let inventory := target.inventory
      let layoutIssues := nestingIssues lexed
      let logicalIssues :=
        logicalSyntaxIssues (lexed.tokens.length + 1) parsed
      let binderIssues := bindingIssues (lexed.tokens.length + 1) parsed
      let counts := declarationCounts inventory
      let environmentDeclarations :=
        imports.flatMap (·.inventory.declarations) ++ inventory.declarations
      let signatures :=
        signatureAudit (lexed.tokens.length + 1) environmentDeclarations parsed
      IO.println s!"top-level forms: {parsed.forms.length}"
      IO.println s!"structural errors: {parsed.errors.length}"
      for failure in parsed.errors do
        IO.eprintln (parseErrorText failure)
      IO.println s!"suspicious nested column-one forms: {layoutIssues.length}"
      for issue in layoutIssues do
        IO.eprintln (nestingIssueText issue)
      IO.println s!"logical syntax errors: {logicalIssues.length}"
      for issue in logicalIssues do
        IO.eprintln (logicalSyntaxIssueText issue)
      IO.println s!"binding errors: {binderIssues.length}"
      for issue in binderIssues do
        IO.eprintln (bindingIssueText issue)
      IO.println s!"fixed-signature errors: {signatures.issues.length}"
      for issue in signatures.issues do
        IO.eprintln (signatureIssueText issue)
      IO.println s!"unresolved imported operators: {signatures.unresolvedOperators.length}"
      for summary in signatures.unresolvedOperators do
        IO.println (operatorSummaryText summary)
      IO.println s!"operator classes used directly: {signatures.classOperators.length}"
      for summary in signatures.classOperators do
        IO.println (operatorSummaryText summary)
      IO.println s!"subclass declarations: {counts.subclasses}"
      IO.println s!"instance declarations: {counts.instances}"
      IO.println s!"domain declarations: {counts.domains}"
      IO.println s!"domainSubclass declarations: {counts.domainSubclasses}"
      IO.println s!"range declarations: {counts.ranges}"
      IO.println s!"rangeSubclass declarations: {counts.rangeSubclasses}"
      IO.println s!"documentation declarations: {counts.documentation}"
      IO.println s!"other formulas: {inventory.formulas.length}"
      IO.println s!"declaration errors: {inventory.errors.length}"
      for failure in inventory.errors do
        IO.eprintln (declarationErrorText failure)
      let importsValid := imports.all sourceUnitValidForDeclarations
      return if importsValid && parsed.errors.isEmpty && layoutIssues.isEmpty &&
          logicalIssues.isEmpty && binderIssues.isEmpty &&
          signatures.issues.isEmpty && inventory.errors.isEmpty then 0 else 1

end Mettapedia.Languages.KIF.SourceCheck

unsafe def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | path :: imports =>
      Mettapedia.Languages.KIF.SourceCheck.checkFile path imports
  | _ =>
      IO.eprintln "usage: kif-source-check <source.kif> [imported-ontology.kif ...]"
      return 2
