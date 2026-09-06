import Mettapedia.Languages.SUMO.Native.DomainGuardElaboration

/-!
# Command-line direct SUMO elaboration check

This executable reads one or more SUO-KIF sources, derives formula-valued
argument positions and implicit domain restrictions from their combined
declarations, and elaborates every top-level form into the intrinsically
scoped native SUMO calculus.  It retains source and unresolved-domain
failures, but discards successful native trees after checking so a large
ontology need not remain resident twice.
-/

namespace Mettapedia.Languages.SUMO.Native.SourceElaborationCheck

open Mettapedia.Languages.SUMO.Native.SourceElaboration

private structure SourceUnit where
  path : String
  parsed : KIF.Parsed
  declarations : List KIF.SuoDeclaration
  declarationErrors : List KIF.DeclarationError

private def positionText (position : KIF.SourcePos) : String :=
  s!"{position.line}:{position.column}"

private def spanText (span : KIF.SourceSpan) : String :=
  s!"{positionText span.start}-{positionText span.stop}"

private def elaborationText (failure : ElaborationIssue) : String :=
  s!"{spanText failure.span}: {reprStr failure.kind}"

private unsafe def readUnit (path : String) : IO (Except String SourceUnit) := do
  let source <- IO.FS.readFile path
  match KIF.lex source with
  | .error failure =>
      pure (.error s!"{path}:{spanText failure.span}: {reprStr failure.kind}")
  | .ok lexed =>
      let parsed := KIF.parse lexed
      let inventory := KIF.declarationInventory parsed
      pure (.ok ⟨path, parsed, inventory.declarations, inventory.errors⟩)

private unsafe def readUnits : List String -> IO (Except String (List SourceUnit))
  | [] => pure (.ok [])
  | path :: rest => do
      match <- readUnit path with
      | .error message => pure (.error message)
      | .ok unit =>
          match <- readUnits rest with
          | .error message => pure (.error message)
          | .ok units => pure (.ok (unit :: units))

private structure ElaborationCounts where
  accepted : Nat
  failures : List ElaborationIssue
  guardIssues : List (KIF.SourceSpan × DomainGuardElaboration.GuardIssueKind)

private def checkForms (signature : SourceSignature) :
    List KIF.Term -> ElaborationCounts -> ElaborationCounts
  | [], counts => counts
  | source :: rest, counts =>
      match DomainGuardElaboration.elaborateSentence signature source with
      | .ok result =>
          let locatedIssues := result.issues.map fun guardIssue =>
            (source.span, guardIssue)
          checkForms signature rest
            { counts with
              accepted := counts.accepted + 1
              guardIssues := locatedIssues ++ counts.guardIssues }
      | .error failure =>
          checkForms signature rest
            { counts with failures := failure :: counts.failures }

private unsafe def reportUnit
    (signature : SourceSignature) (unit : SourceUnit) : IO Bool := do
  IO.println s!"source: {unit.path}"
  IO.println s!"top-level forms: {unit.parsed.forms.length}"
  IO.println s!"structural errors: {unit.parsed.errors.length}"
  for failure in unit.parsed.errors do
    IO.println s!"{unit.path}:{spanText failure.span}: {reprStr failure.kind}"
  IO.println s!"declaration errors: {unit.declarationErrors.length}"
  for failure in unit.declarationErrors do
    IO.println s!"{unit.path}:{spanText failure.span}: {reprStr failure.kind}"
  let counts := checkForms signature unit.parsed.forms ⟨0, [], []⟩
  let failures := counts.failures.reverse
  let guardIssues := counts.guardIssues.reverse
  IO.println s!"native formulas accepted: {counts.accepted}"
  IO.println s!"native elaboration errors: {failures.length}"
  for failure in failures do
    IO.println s!"{unit.path}:{elaborationText failure}"
  IO.println s!"unresolved domain guards: {guardIssues.length}"
  for (span, guardIssue) in guardIssues do
    IO.println s!"{unit.path}:{spanText span}: {reprStr guardIssue}"
  pure (unit.parsed.errors.isEmpty && unit.declarationErrors.isEmpty &&
    failures.isEmpty && guardIssues.isEmpty)

unsafe def run (paths : List String) : IO UInt32 := do
  match <- readUnits paths with
  | .error message =>
      IO.eprintln message
      pure 1
  | .ok units =>
      let declarations := units.flatMap (·.declarations)
      let forms := units.flatMap fun unit => unit.parsed.forms
      let signature := SourceSignature.ofDeclarationsAndForms declarations forms
      IO.println s!"formula-valued argument positions: {signature.formulaArguments.length}"
      IO.println s!"domain restrictions: {signature.domainRestrictions.length}"
      IO.println s!"subclass edges: {signature.subclassEdges.length}"
      IO.println s!"subrelation edges: {signature.subrelationEdges.length}"
      let mut allAccepted := true
      for unit in units do
        if !(<- reportUnit signature unit) then
          allAccepted := false
      pure (if allAccepted then 0 else 1)

end Mettapedia.Languages.SUMO.Native.SourceElaborationCheck

unsafe def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | [] => do
      IO.eprintln "usage: sumo-native-source-check <source.kif> [source.kif ...]"
      pure 2
  | _ => Mettapedia.Languages.SUMO.Native.SourceElaborationCheck.run arguments
