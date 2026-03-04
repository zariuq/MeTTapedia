import MeTTailCore
import Mettapedia.Languages.MeTTa.HE.HEPremises

namespace Mettapedia.Languages.MeTTa.HE.LookupPlan

open MeTTailCore.MeTTaIL.LookupPlan
open Mettapedia.OSLF.MeTTaIL.PremiseDatalog

private def argB (pos : Nat) : SignatureArg :=
  { position := pos, mode := .bound }

private def argF (pos : Nat) : SignatureArg :=
  { position := pos, mode := .free }

private def relArity? (prog : PremiseProgram) (name : String) : Option Nat :=
  (prog.relations.find? fun r => r.name == name).map (fun r => r.paramTypes.length)

private def ruleHasComputeManyBuiltin (r : PRule) (builtin : String) : Bool :=
  r.body.any fun
    | .computeMany b _ _ => b == builtin
    | _ => false

private def ruleHasComputeBuiltin (r : PRule) (builtin : String) : Bool :=
  r.body.any fun
    | .compute b _ _ => b == builtin
    | _ => false

private def ruleHasRelQuery (r : PRule) (rel : String) : Bool :=
  r.body.any fun
    | .relQuery qRel _ => qRel == rel
    | _ => false

private def ruleHasNotInRel (r : PRule) (rel : String) : Bool :=
  r.body.any fun
    | .notIn qRel _ => qRel == rel
    | _ => false

private def hasRuleWithComputeMany (prog : PremiseProgram)
    (rel builtin : String) : Bool :=
  (prog.rulesFor rel).any (fun r => ruleHasComputeManyBuiltin r builtin)

private def hasRuleWithCompute (prog : PremiseProgram)
    (rel builtin : String) : Bool :=
  (prog.rulesFor rel).any (fun r => ruleHasComputeBuiltin r builtin)

private def hasRuleWithRelQuery (prog : PremiseProgram)
    (rel depRel : String) : Bool :=
  (prog.rulesFor rel).any (fun r => ruleHasRelQuery r depRel)

private def hasRuleWithNotInRel (prog : PremiseProgram)
    (rel depRel : String) : Bool :=
  (prog.rulesFor rel).any (fun r => ruleHasNotInRel r depRel)

private def mkHeEqQueryFamily (payloadArity : Nat) : LookupFamilyPlan :=
  { family := "eqQuery"
    logicalRelationId := "he.eq_query"
    factRelation := "spaceFact"
    rawRelation := "eqQueryRaw"
    hasRelation := "eqQueryHas"
    resultRelation := some "eqQueryResult"
    queryArity := 2
    payloadArity := payloadArity
    keyPositions := [0, 1]
    demand :=
      [ { relation := "eqQueryResult"
          logicalRelationId := "he.eq_query.result"
          scopeSignature := "b0+b1+f2"
          arity := 3
          args := [argB 0, argB 1, argF 2]
          usageKind := .enumerate
          hotPath := true }
      , { relation := "noEqQuery"
          logicalRelationId := "he.eq_query.fallback"
          scopeSignature := "b0+b1"
          arity := 2
          args := [argB 0, argB 1]
          usageKind := .negatedExists
          negatedTarget := some "eqQueryHas"
          hotPath := true }
      ]
    contracts :=
      { noFalseNegatives := true
        exactResult := false
        stratifiedNegationSafe := true } }

theorem mkHeEqQueryFamily_negatesHas_notResult (payloadArity : Nat) :
    ∃ d ∈ (mkHeEqQueryFamily payloadArity).demand,
      d.relation = "noEqQuery"
        ∧ d.usageKind = .negatedExists
        ∧ d.negatedTarget = some "eqQueryHas" := by
  refine ⟨{ relation := "noEqQuery"
          , logicalRelationId := "he.eq_query.fallback"
          , scopeSignature := "b0+b1"
          , arity := 2
          , args := [argB 0, argB 1]
          , usageKind := .negatedExists
          , negatedTarget := some "eqQueryHas"
          , inRecursiveScc := false
          , hotPath := true }, ?_, ?_⟩
  · simp [mkHeEqQueryFamily]
  · simp

def deriveHeEqQueryFamily? (prog : PremiseProgram) : Except String LookupFamilyPlan := do
  let some rawArity := relArity? prog "eqQueryRaw"
    | throw "missing relation decl: eqQueryRaw"
  let some eqArity := relArity? prog "eqQueryResult"
    | throw "missing relation decl: eqQueryResult"
  let some hasArity := relArity? prog "eqQueryHas"
    | throw "missing relation decl: eqQueryHas"
  let some noEqArity := relArity? prog "noEqQuery"
    | throw "missing relation decl: noEqQuery"
  unless rawArity = 3 do
    throw s!"eqQueryRaw arity mismatch: expected 3, got {rawArity}"
  unless eqArity = 3 do
    throw s!"eqQueryResult arity mismatch: expected 3, got {eqArity}"
  unless hasArity = 2 do
    throw s!"eqQueryHas arity mismatch: expected 2, got {hasArity}"
  unless noEqArity = 2 do
    throw s!"noEqQuery arity mismatch: expected 2, got {noEqArity}"
  unless hasRuleWithComputeMany prog "eqQueryRaw" "queryEquationsInSpace" do
    throw "eqQueryRaw must be driven by computeMany(queryEquationsInSpace)"
  unless hasRuleWithRelQuery prog "eqQueryResult" "eqQueryRaw" do
    throw "eqQueryResult must be derived from relQuery(eqQueryRaw)"
  unless hasRuleWithRelQuery prog "eqQueryHas" "eqQueryRaw" do
    throw "eqQueryHas must be derived from relQuery(eqQueryRaw)"
  unless hasRuleWithNotInRel prog "noEqQuery" "eqQueryHas" do
    throw "noEqQuery must be driven by notIn(eqQueryHas)"
  pure (mkHeEqQueryFamily (eqArity - 2))

def deriveHeLookupPlanArtifact? (prog : PremiseProgram) : Except String LookupPlanArtifact := do
  let fam ← deriveHeEqQueryFamily? prog
  let artifact : LookupPlanArtifact :=
    { schemaVersion := 2
      dialect := "he"
      families := [fam] }
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    throw s!"lookup-plan lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def deriveFromHEPremises? : Except String LookupPlanArtifact :=
  deriveHeLookupPlanArtifact? Mettapedia.Languages.MeTTa.HE.Premises.mettaHEPremises

def derivationIsOk : Bool :=
  match deriveFromHEPremises? with
  | .ok _ => true
  | .error _ => false

#guard derivationIsOk = true

def exportHeLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  match deriveFromHEPremises? with
  | .error err =>
      IO.println s!"he lookup-plan derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "he.lookup_plan.json"
      let checksumPath := outDir / "he.lookup_plan.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported he lookup-plan artifact to {outDir}"
      pure 0

def checkHeLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  match deriveFromHEPremises? with
  | .error err =>
      IO.println s!"he lookup-plan derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "he.lookup_plan.json"
      let checksumPath := outDir / "he.lookup_plan.checksum"
      try
        let jsonText ← IO.FS.readFile jsonPath
        let checksumText ← IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] he lookup-plan artifact matches at {outDir}"
          pure 0
        else
          IO.println s!"[drift] he lookup-plan artifact mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"he lookup-plan check failed: {e}"
        pure 2

end Mettapedia.Languages.MeTTa.HE.LookupPlan
