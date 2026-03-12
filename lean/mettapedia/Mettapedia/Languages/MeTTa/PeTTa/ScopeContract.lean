import Mettapedia.Languages.MeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment

/-!
# PeTTa Scope Contract

First concrete scope-contract instance for the shared MeTTa binder/scope
surface.

This artifact classifies local binder forms and scoped payload forms so Rust
does not have to recover free-variable semantics by head-specific walkers.

Positive example:
- `let`, `chain`, and `let*` expose binder/value/body positions explicitly.
- `add-atom` / `remove-atom` with `(= lhs rhs)` payloads expose a scoped rule
  payload instead of forcing Rust to infer local rule scope from surface syntax.

Negative example:
- this file does not describe executable backend ownership or MM2 text.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.ScopeContract

open Mettapedia.Languages.MeTTa.ScopeContract

private def letTheoremRefs : List String :=
  [ "Algorithms.MeTTa.Simple.Session.evalLetIntrinsic"
  , "Algorithms.MeTTa.Simple.Session.eval"
  ]

private def chainTheoremRefs : List String :=
  [ "Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalChain"
  , "Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalChain_preserves"
  ]

private def letStarTheoremRefs : List String :=
  [ "Algorithms.MeTTa.Simple.Session.evalLetStarDeterministic"
  , "Algorithms.MeTTa.Simple.Session.eval"
  ]

private def lambdaTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions.MeTTaStep.lambdaAbstract"
  , "Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions.lambdaAbstract_betaReduce"
  ]

private def caseTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec.ControlDeclClause.caseSuccessStep"
  , "Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec.ControlDeclClause.caseFailureStep"
  , "Mettapedia.Languages.MeTTa.PeTTa.StdLib.case_single_branch_reduces"
  , "Mettapedia.Languages.MeTTa.PeTTa.StdLib.case_single_branch_failure"
  ]

private def sourceRulePayloadTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_fireSourceRule_mem"
  , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.removeAtom_fireSourceRule_mem"
  ]

def letScopeEntry : ScopeContractEntry where
  head := "let"
  arity := 3
  scopeKind := .letLike
  binderPositions := [0]
  valuePositions := [1]
  bodyPositions := [2]
  sequential := false
  allowsWildcard := true
  theoremRefs := letTheoremRefs

def chainScopeEntry : ScopeContractEntry where
  head := "chain"
  arity := 3
  scopeKind := .chainLike
  binderPositions := [1]
  valuePositions := [0]
  bodyPositions := [2]
  sequential := false
  allowsWildcard := true
  theoremRefs := chainTheoremRefs

def letStarScopeEntry : ScopeContractEntry where
  head := "let*"
  arity := 2
  scopeKind := .letStarLike
  valuePositions := [0]
  bodyPositions := [1]
  sequential := true
  allowsWildcard := true
  theoremRefs := letStarTheoremRefs

def lambdaArrowScopeEntry : ScopeContractEntry where
  head := "|->"
  arity := 2
  scopeKind := .lambdaLike
  binderPositions := [0]
  bodyPositions := [1]
  sequential := false
  allowsWildcard := true
  theoremRefs := lambdaTheoremRefs

def caseScopeEntry : ScopeContractEntry where
  head := "case"
  arity := 2
  scopeKind := .caseLike
  valuePositions := [0]
  bodyPositions := [1]
  sequential := false
  allowsWildcard := true
  theoremRefs := caseTheoremRefs

def addAtomSourceRulePayloadScopeEntry : ScopeContractEntry where
  head := "add-atom"
  arity := 2
  scopeKind := .sourceRulePayload
  bodyPositions := [0]
  scopedPayloadPositions := [1]
  payloadShape := some .rewriteEqRule
  sequential := false
  allowsWildcard := true
  theoremRefs := sourceRulePayloadTheoremRefs

def addAtomBangSourceRulePayloadScopeEntry : ScopeContractEntry where
  head := "add-atom!"
  arity := 2
  scopeKind := .sourceRulePayload
  bodyPositions := [0]
  scopedPayloadPositions := [1]
  payloadShape := some .rewriteEqRule
  sequential := false
  allowsWildcard := true
  theoremRefs := sourceRulePayloadTheoremRefs

def removeAtomSourceRulePayloadScopeEntry : ScopeContractEntry where
  head := "remove-atom"
  arity := 2
  scopeKind := .sourceRulePayload
  bodyPositions := [0]
  scopedPayloadPositions := [1]
  payloadShape := some .rewriteEqRule
  sequential := false
  allowsWildcard := true
  theoremRefs := sourceRulePayloadTheoremRefs

def removeAtomBangSourceRulePayloadScopeEntry : ScopeContractEntry where
  head := "remove-atom!"
  arity := 2
  scopeKind := .sourceRulePayload
  bodyPositions := [0]
  scopedPayloadPositions := [1]
  payloadShape := some .rewriteEqRule
  sequential := false
  allowsWildcard := true
  theoremRefs := sourceRulePayloadTheoremRefs

def pettaScopeContractArtifact : ScopeContractArtifact where
  dialect := "petta"
  wildcardSymbol := "_"
  entries :=
    [ letScopeEntry
    , chainScopeEntry
    , letStarScopeEntry
    , lambdaArrowScopeEntry
    , caseScopeEntry
    , addAtomSourceRulePayloadScopeEntry
    , addAtomBangSourceRulePayloadScopeEntry
    , removeAtomSourceRulePayloadScopeEntry
    , removeAtomBangSourceRulePayloadScopeEntry
    ]

def exportPeTTaScopeContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := pettaScopeContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"petta scope contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "petta.scope_contract.json"
    let checksumPath := outDir / "petta.scope_contract.checksum"
    IO.FS.createDirAll outDir
    IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
    IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
    IO.println s!"exported petta scope contract to {outDir}"
    pure 0

def checkPeTTaScopeContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := pettaScopeContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"petta scope contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "petta.scope_contract.json"
    let checksumPath := outDir / "petta.scope_contract.checksum"
    try
      let jsonText ← IO.FS.readFile jsonPath
      let checksumText ← IO.FS.readFile checksumPath
      let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
      let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
      if jsonOk && checksumOk then
        IO.println s!"[ok] petta scope contract matches at {outDir}"
        pure 0
      else
        if !jsonOk then
          IO.println s!"[drift] petta scope contract json mismatch at {jsonPath}"
        if !checksumOk then
          IO.println s!"[drift] petta scope contract checksum mismatch at {checksumPath}"
        pure 3
    catch e =>
      IO.println s!"petta scope contract check failed: {e}"
      pure 2

section Canaries
#check @pettaScopeContractArtifact
#check @exportPeTTaScopeContract
end Canaries

end Mettapedia.Languages.MeTTa.PeTTa.ScopeContract
