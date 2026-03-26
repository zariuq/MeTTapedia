import Mettapedia.Languages.MeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment
import Mettapedia.OSLF.MeTTaIL.Substitution

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

private def matchTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.PeTTa.Eval.petta_eval_spaceQuery_correct"
  , "Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval.meTTaEval_spaceQuery_to_pettaEval"
  , "Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec.FullDeclClause.match_intro"
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

def matchScopeEntry : ScopeContractEntry where
  head := "match"
  arity := 3
  scopeKind := .matchLike
  binderPositions := [1]
  valuePositions := [0]
  bodyPositions := [2]
  sequential := false
  allowsWildcard := true
  theoremRefs := matchTheoremRefs

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
    , matchScopeEntry
    , lambdaArrowScopeEntry
    , caseScopeEntry
    , addAtomSourceRulePayloadScopeEntry
    , addAtomBangSourceRulePayloadScopeEntry
    , removeAtomSourceRulePayloadScopeEntry
    , removeAtomBangSourceRulePayloadScopeEntry
    ]

private abbrev Pattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

open Mettapedia.OSLF.MeTTaIL.Substitution

private def orderedUniq (xs : List String) : List String :=
  xs.eraseDups

private def wildcardSymbol : String :=
  pettaScopeContractArtifact.wildcardSymbol

private def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

private def isRewriteEqRulePayload : Pattern → Bool
  | .apply "=" [_lhs, _rhs] => true
  | _ => false

private def payloadMatchesShape
    (node : Pattern)
    (shape : Mettapedia.Languages.MeTTa.ExecutionContract.PayloadPatternShapeKind) : Bool :=
  if _h :
      shape =
        Mettapedia.Languages.MeTTa.ExecutionContract.PayloadPatternShapeKind.anyPattern then
    true
  else if _h :
      shape =
        Mettapedia.Languages.MeTTa.ExecutionContract.PayloadPatternShapeKind.nonRewritePattern then
      !isRewriteEqRulePayload node
  else
    isRewriteEqRulePayload node

private def matchingScopeEntry? (ctor : String) (args : List Pattern) :
    Option ScopeContractEntry :=
  pettaScopeContractArtifact.entries.find? fun entry =>
    entry.head = ctor
      && entry.arity = args.length
      && match entry.payloadShape with
        | none => true
        | some shape =>
            entry.scopedPayloadPositions.all fun pos =>
              match listGet? args pos with
              | some arg => payloadMatchesShape arg shape
              | none => false

private def extractTupleElements : Pattern → List Pattern
  | .apply "expr" args => args
  | node => [node]

private def letStarBindingNodes : Pattern → Option (List Pattern)
  | .collection _ elements none => some elements
  | .apply "expr" args => some args
  | _ => none

private def normalizeBinderPattern : Pattern → Pattern
  | .apply ctor [] =>
      if ctor.startsWith "$" then
        .fvar (ctor.drop 1).toString
      else
        .apply ctor []
  | pat => pat

private def letStarBindingParts : Pattern → Option (Pattern × Pattern)
  | .apply ctor [value] =>
      if ctor.startsWith "$" then
        some (.fvar (ctor.drop 1).toString, value)
      else
        none
  | .apply "expr" [binder, value] =>
      some (normalizeBinderPattern binder, value)
  | .apply "pair" [binder, value] =>
      some (normalizeBinderPattern binder, value)
  | .collection _ [binder, value] none =>
      some (normalizeBinderPattern binder, value)
  | _ => none

private def boundNamesFromPattern (bound : List String) (pat : Pattern) : List String :=
  orderedUniq <|
    (freeVars (normalizeBinderPattern pat)).filter fun name =>
      name != wildcardSymbol && !(bound.contains name)

private def patternFuel : Pattern → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .apply _ args =>
      1 + args.foldl (fun acc arg => acc + patternFuel arg) 0
  | .lambda _nm body => 1 + patternFuel body
  | .multiLambda _ _nms body => 1 + patternFuel body
  | .subst body repl => 1 + patternFuel body + patternFuel repl
  | .collection _ elements rest =>
      1 + elements.foldl (fun acc element => acc + patternFuel element) 0
        + match rest with
          | some _ => 1
          | none => 0

private def orderedScopedFreeVarsWithFuel
    (fuel : Nat) (bound : List String) (pat : Pattern) : List String :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match pat with
    | .bvar _ => []
    | .fvar name =>
      if name = wildcardSymbol || bound.contains name then
        []
      else
        [name]
    | .apply ctor args =>
      match matchingScopeEntry? ctor args with
      | some entry =>
          match entry.scopeKind with
          | .letLike
          | .chainLike
          | .matchLike =>
              match listGet? entry.binderPositions 0, listGet? entry.valuePositions 0, listGet? entry.bodyPositions 0 with
              | some binderIdx, some valueIdx, some bodyIdx =>
                  let valueVars :=
                    match listGet? args valueIdx with
                    | some value => orderedScopedFreeVarsWithFuel fuel bound value
                    | none => []
                  let binderVars :=
                    match listGet? args binderIdx with
                    | some binder => boundNamesFromPattern bound binder
                    | none => []
                  let bodyVars :=
                    match listGet? args bodyIdx with
                    | some body =>
                        orderedScopedFreeVarsWithFuel fuel (orderedUniq (bound ++ binderVars)) body
                    | none => []
                  orderedUniq (valueVars ++ bodyVars)
              | _, _, _ =>
                  orderedUniq (args.flatMap (orderedScopedFreeVarsWithFuel fuel bound))
          | .letStarLike =>
              match listGet? entry.valuePositions 0, listGet? entry.bodyPositions 0 with
              | some valuesIdx, some bodyIdx =>
                  match listGet? args valuesIdx with
                  | some values =>
                      match letStarBindingNodes values with
                      | some bindings =>
                          let (bindingVars, finalBound) :=
                            bindings.foldl
                              (fun (acc : List String × List String) binding =>
                                let (accVars, accBound) := acc
                                match letStarBindingParts binding with
                                | some (binder, value) =>
                                    let valueVars :=
                                      orderedScopedFreeVarsWithFuel fuel accBound value
                                    let bound' :=
                                      orderedUniq (accBound ++ boundNamesFromPattern accBound binder)
                                    (orderedUniq (accVars ++ valueVars), bound')
                                | none =>
                                    let bindingVars :=
                                      orderedScopedFreeVarsWithFuel fuel accBound binding
                                    (orderedUniq (accVars ++ bindingVars), accBound))
                              ([], bound)
                          let bodyVars :=
                            match listGet? args bodyIdx with
                            | some body => orderedScopedFreeVarsWithFuel fuel finalBound body
                            | none => []
                          orderedUniq (bindingVars ++ bodyVars)
                      | none =>
                          let valuesVars := orderedScopedFreeVarsWithFuel fuel bound values
                          let bodyVars :=
                            match listGet? args bodyIdx with
                            | some body => orderedScopedFreeVarsWithFuel fuel bound body
                            | none => []
                          orderedUniq (valuesVars ++ bodyVars)
                  | none =>
                      orderedUniq (args.flatMap (orderedScopedFreeVarsWithFuel fuel bound))
              | _, _ =>
                  orderedUniq (args.flatMap (orderedScopedFreeVarsWithFuel fuel bound))
          | .lambdaLike =>
              match listGet? entry.binderPositions 0, listGet? entry.bodyPositions 0 with
              | some binderIdx, some bodyIdx =>
                  let binderVars :=
                    match listGet? args binderIdx with
                    | some binder => boundNamesFromPattern bound binder
                    | none => []
                  match listGet? args bodyIdx with
                  | some body =>
                      orderedScopedFreeVarsWithFuel fuel (orderedUniq (bound ++ binderVars)) body
                  | none => []
              | _, _ =>
                  orderedUniq (args.flatMap (orderedScopedFreeVarsWithFuel fuel bound))
          | .caseLike =>
              match listGet? entry.valuePositions 0, listGet? entry.bodyPositions 0 with
              | some valueIdx, some bodyIdx =>
                  let valueVars :=
                    match listGet? args valueIdx with
                    | some value => orderedScopedFreeVarsWithFuel fuel bound value
                    | none => []
                  let branchVars :=
                    match listGet? args bodyIdx with
                    | some branches =>
                        (extractTupleElements branches).flatMap fun branch =>
                          match extractTupleElements branch with
                          | binder :: body :: [] =>
                              orderedScopedFreeVarsWithFuel
                                fuel
                                (orderedUniq (bound ++ boundNamesFromPattern bound binder))
                                body
                          | _ => orderedScopedFreeVarsWithFuel fuel bound branch
                    | none => []
                  orderedUniq (valueVars ++ branchVars)
              | _, _ =>
                  orderedUniq (args.flatMap (orderedScopedFreeVarsWithFuel fuel bound))
          | .sourceRulePayload =>
              let (vars, _) :=
                args.foldl
                  (fun (acc : List String × Nat) arg =>
                    let (accVars, idx) := acc
                    let here :=
                      if entry.scopedPayloadPositions.contains idx then
                        []
                      else
                        orderedScopedFreeVarsWithFuel fuel bound arg
                    (orderedUniq (accVars ++ here), idx + 1))
                  ([], 0)
              vars
      | none =>
          orderedUniq (args.flatMap (orderedScopedFreeVarsWithFuel fuel bound))
    | .lambda _nm body =>
        orderedScopedFreeVarsWithFuel fuel bound body
    | .multiLambda _ _nms body =>
        orderedScopedFreeVarsWithFuel fuel bound body
    | .subst body repl =>
      orderedUniq
        (orderedScopedFreeVarsWithFuel fuel bound body
          ++ orderedScopedFreeVarsWithFuel fuel bound repl)
    | .collection _ elements rest =>
      let elementVars := orderedUniq (elements.flatMap (orderedScopedFreeVarsWithFuel fuel bound))
      let restVars :=
        match rest with
        | some name =>
            if name = wildcardSymbol || bound.contains name then [] else [name]
        | none => []
      orderedUniq (elementVars ++ restVars)
termination_by fuel

def orderedScopedFreeVars (pat : Pattern) : List String :=
  orderedScopedFreeVarsWithFuel (patternFuel pat) [] pat

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
