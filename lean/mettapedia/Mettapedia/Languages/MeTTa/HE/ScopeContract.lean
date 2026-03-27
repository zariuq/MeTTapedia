import Mettapedia.Languages.MeTTa.ScopeContract

/-!
# HE Scope Contract

Scope-contract artifact for the HE (Hyperon Experimental) MeTTa dialect.

This classifies each HE operator's binder, value, body, and scoped-payload
positions so the MM2/MORK backend does not need head-specific walkers for
variable hygiene and substitution.

## Source of Truth

- MinimalMeTTa.lean: the 13 minimal instructions (chain, unify, etc.)
- EvalSpec.lean: the 6 declarative evaluation relations
- metta.md: the upstream HE spec

## Operator Coverage

Operators with binding scope:
- `chain`: binds result of evaluation into template
- `unify`: binds pattern variables in success branch only
- `match`: binds pattern variables in template
- `case`: scrutinee evaluated, branches bind patterns
- `switch` / `switch-minimal`: same structure as case
- `let`: surface sugar, but scope info needed for hygiene
- `let*`: sequential binding surface sugar

Operators without binding scope (eval, evalc, metta, cons-atom, decons-atom,
collapse-bind, superpose-bind, function, return, context-space, call-native,
assert) do not appear here — they have no binder/body structure.
-/

namespace Mettapedia.Languages.MeTTa.HE.ScopeContract

open Mettapedia.Languages.MeTTa.ScopeContract

/-! ## Theorem References

These reference the HE computable spec and MinimalMeTTa constructors that
establish the binding semantics for each operator. -/

private def chainTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.HE.MinimalStep.chain"
  , "Mettapedia.Languages.MeTTa.HE.MinimalStep.chain_empty"
  ]

private def unifyTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.HE.MinimalStep.unify_match"
  , "Mettapedia.Languages.MeTTa.HE.MinimalStep.unify_no_match"
  ]

private def matchTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.HE.EvalSpec.MettaCall.match_success"
  , "Mettapedia.Languages.MeTTa.HE.EvalSpec.MettaCall.match_empty"
  ]

private def caseTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.HE.EvalSpec.MettaCall.case_branch"
  ]

private def switchTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.HE.EvalSpec.MettaCall.switch_match"
  , "Mettapedia.Languages.MeTTa.HE.EvalSpec.MettaCall.switch_no_match"
  ]

private def letTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.HE.Conformance.eval_symbol_typecast"
  ]

private def letStarTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.HE.Conformance.eval_symbol_typecast"
  ]

/-! ## Scope Entries -/

/-- `(chain <atom> <var> <template>)` — evaluate atom, bind result to var,
    substitute in template. Ref: MinimalMeTTa.lean chain constructor.
    Binder position 1 ($var), value position 0 (atom to evaluate),
    body position 2 (template where $var is in scope). -/
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

/-- `(unify <atom> <pattern> <then> <else>)` — match atom against pattern.
    On success: pattern variables bound in then-branch.
    On failure: else-branch evaluated with original bindings (no new scope).
    Ref: MinimalMeTTa.lean unify_match / unify_no_match.
    Binder position 1 (pattern), value position 0 (atom),
    body position 2 (then-branch, scoped with match bindings).
    Position 3 (else-branch) is NOT scoped by the match — it uses original bindings. -/
def unifyScopeEntry : ScopeContractEntry where
  head := "unify"
  arity := 4
  scopeKind := .matchLike
  binderPositions := [1]
  valuePositions := [0]
  bodyPositions := [2]
  sequential := false
  allowsWildcard := true
  theoremRefs := unifyTheoremRefs

/-- `(match <space> <pattern> <template>)` — query space for pattern matches.
    Pattern variables bound in template.
    Ref: EvalSpec.lean MettaCall match constructors.
    Value position 0 (space ref), binder position 1 (pattern),
    body position 2 (template, scoped with match bindings). -/
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

/-- `(case <scrutinee> <branches>)` — evaluate scrutinee, match against branches.
    Each branch is `(<pattern> <template>)` where pattern variables scope template.
    Ref: EvalSpec.lean MettaCall case constructor.
    Value position 0 (scrutinee), body position 1 (branches list). -/
def caseScopeEntry : ScopeContractEntry where
  head := "case"
  arity := 2
  scopeKind := .caseLike
  valuePositions := [0]
  bodyPositions := [1]
  sequential := false
  allowsWildcard := true
  theoremRefs := caseTheoremRefs

/-- `(switch <scrutinee> <cases>)` — same binding structure as case.
    parseSwitchMinimalCallArgs accepts both "switch" and "switch-minimal". -/
def switchScopeEntry : ScopeContractEntry where
  head := "switch"
  arity := 2
  scopeKind := .caseLike
  valuePositions := [0]
  bodyPositions := [1]
  sequential := false
  allowsWildcard := true
  theoremRefs := switchTheoremRefs

/-- `(switch-minimal <scrutinee> <cases>)` — same as switch. -/
def switchMinimalScopeEntry : ScopeContractEntry where
  head := "switch-minimal"
  arity := 2
  scopeKind := .caseLike
  valuePositions := [0]
  bodyPositions := [1]
  sequential := false
  allowsWildcard := true
  theoremRefs := switchTheoremRefs

/-- `(let <var> <value> <body>)` — surface sugar that desugars to case,
    but scope info is needed for hygiene before desugaring.
    Ref: OpProfile.lean classifies let as surfaceSugar.
    Binder position 0 ($var), value position 1, body position 2. -/
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

/-- `(let* <bindings> <body>)` — sequential binding surface sugar.
    Ref: OpProfile.lean classifies let* as surfaceSugar.
    Value position 0 (bindings list), body position 1. -/
def letStarScopeEntry : ScopeContractEntry where
  head := "let*"
  arity := 2
  scopeKind := .letStarLike
  valuePositions := [0]
  bodyPositions := [1]
  sequential := true
  allowsWildcard := true
  theoremRefs := letStarTheoremRefs

/-! ## Artifact Assembly -/

def heScopeContractArtifact : ScopeContractArtifact where
  dialect := "he"
  wildcardSymbol := "_"
  entries :=
    [ chainScopeEntry
    , unifyScopeEntry
    , matchScopeEntry
    , caseScopeEntry
    , switchScopeEntry
    , switchMinimalScopeEntry
    , letScopeEntry
    , letStarScopeEntry
    ]

/-! ## Export / Check -/

def exportHeScopeContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := heScopeContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"he scope contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "he.scope_contract.json"
    let checksumPath := outDir / "he.scope_contract.checksum"
    IO.FS.createDirAll outDir
    IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
    IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
    IO.println s!"exported he scope contract to {outDir}"
    pure 0

def checkHeScopeContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := heScopeContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"he scope contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "he.scope_contract.json"
    let checksumPath := outDir / "he.scope_contract.checksum"
    try
      let jsonText ← IO.FS.readFile jsonPath
      let checksumText ← IO.FS.readFile checksumPath
      let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
      let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
      if jsonOk && checksumOk then
        IO.println s!"[ok] he scope contract matches at {outDir}"
        pure 0
      else
        if !jsonOk then
          IO.println s!"[drift] he scope contract json mismatch at {jsonPath}"
        if !checksumOk then
          IO.println s!"[drift] he scope contract checksum mismatch at {checksumPath}"
        pure 3
    catch e =>
      IO.println s!"he scope contract check failed: {e}"
      pure 2

section Canaries
#check @heScopeContractArtifact
#check @exportHeScopeContract
#check @checkHeScopeContract
end Canaries

end Mettapedia.Languages.MeTTa.HE.ScopeContract
