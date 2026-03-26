import MeTTailCore
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.Languages.MeTTa.PeTTa.ScopeContract
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIRV2
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# PeTTa Rewrite IR Artifact Derivation

Program-parametric rewrite IR for PeTTa spaces. The source of truth is
`pettaSpaceToLangDef s`, matching the formal PeTTa rule compilation used in the
OSLF/GSLT bridge.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.RewriteIR

open MeTTailCore.MeTTaIL.RewriteIR
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Languages.MeTTa.PeTTa.ScopeContract
open Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
open Mettapedia.Languages.MeTTa.PeTTa

private def orderedUniq (xs : List String) : List String :=
  xs.eraseDups

private def orderedUniqNat (xs : List Nat) : List Nat :=
  xs.eraseDups

private def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

private structure DerivedRule where
  ruleId : String
  ruleName : String
  sourceInstr : String
  sourceLabel : String
  priority : Nat
  leftRepr : String
  rightRepr : String
  premiseRelations : List String
  lhsJson : String
  rhsJson : String
  premisesJson : String
  lhsVars : List String
  premiseVarFlow : List MeTTailCore.MeTTaIL.RewriteIRV2.PremiseVarFlow
  rhsVars : List String
  rhsFreshVars : List String
  rhsEvalRequires : List String
  ruleMode : MeTTailCore.MeTTaIL.RewriteIR.RewriteIRRuleMode
  rootUpdate : Option MeTTailCore.MeTTaIL.RewriteIRV2.RootUpdateHint
deriving Repr

private def premiseRelations (rw : RewriteRule) : List String :=
  rw.premises.filterMap fun
    | .relationQuery rel _ => some rel
    | _ => none

private def premiseVars : Premise → List String
  | .freshness fc =>
      orderedUniq (fc.varName :: orderedScopedFreeVars fc.term)
  | .congruence lhs rhs =>
      orderedUniq (orderedScopedFreeVars lhs ++ orderedScopedFreeVars rhs)
  | .relationQuery _ args =>
      orderedUniq (args.flatMap orderedScopedFreeVars)
  | .forAll collection param body =>
      orderedUniq (collection :: param :: premiseVars body)

private def premiseVarFlowAux
    (seen : List String) (idx : Nat) :
    List Premise → List MeTTailCore.MeTTaIL.RewriteIRV2.PremiseVarFlow
  | [] => []
  | prem :: rest =>
      let vars := premiseVars prem
      let introduced := vars.filter (fun x => !(seen.contains x))
      { premiseIndex := idx
        premiseVars := vars
        introducedVars := introduced } ::
        premiseVarFlowAux (seen ++ introduced) (idx + 1) rest

private def derivePremiseVarFlow
    (lhsVars : List String) (premises : List Premise) :
    List MeTTailCore.MeTTaIL.RewriteIRV2.PremiseVarFlow :=
  premiseVarFlowAux lhsVars 0 premises

private def rhsMissingVars
    (lhsVars : List String)
    (premiseVarFlow : List MeTTailCore.MeTTaIL.RewriteIRV2.PremiseVarFlow)
    (rhsVars : List String) : List String :=
  let available := orderedUniq (lhsVars ++ premiseVarFlow.flatMap (·.introducedVars))
  orderedUniq (rhsVars.filter (fun x => !(available.contains x)))

/--
Split RHS vars that are still missing after the ordinary lhs/premise flow.

For premise-free rewrites, the runtime dispatch semantics can still emit a
symbolic RHS when free vars remain after substitution: ordinary rule
enumeration goes through `evalForRuleEnumeration`, and compat-head rewrites use
the same "emit symbolic term if free vars remain" discipline in
`compatFunctionHeadRewrite`.

Premise-bearing rewrites stay conservative for now: if a RHS var is still
missing after lhs/premise-introduced flow, we export it as requiring eager
binding rather than guessing symbolic-output support that Rust/MM2 does not yet
realize generally.
-/
private def splitRhsVarObligations
    (premises : List Premise) (rhsMissing : List String) :
    List String × List String :=
  if premises.isEmpty then
    (rhsMissing, [])
  else
    ([], rhsMissing)

private def rootUpdateHint? :
    Pattern → Pattern → Option MeTTailCore.MeTTaIL.RewriteIRV2.RootUpdateHint
  | .apply lhsCtor lhsArgs, .apply rhsCtor rhsArgs =>
      let shared := Nat.min lhsArgs.length rhsArgs.length
      let positions := List.range shared
      let preserved := positions.filter (fun i => listGet? lhsArgs i = listGet? rhsArgs i)
      let changed := positions.filter (fun i => listGet? lhsArgs i ≠ listGet? rhsArgs i)
      some
        { lhsRootCtor := lhsCtor
          rhsRootCtor := rhsCtor
          lhsArity := lhsArgs.length
          rhsArity := rhsArgs.length
          preservedArgPositions := orderedUniqNat preserved
          changedArgPositions := orderedUniqNat changed }
  | _, _ => none

private def hasCompatHeadConstraintArg : Pattern → Bool
  | .apply _ _ => true
  | .collection _ (_ :: _) _ => true
  | _ => false

private def ruleHasCompatHeadConstraint : Pattern → Bool
  | .apply _ args => args.any hasCompatHeadConstraintArg
  | _ => false

private def ruleModeOf
    (lhs : Pattern) (rhsFreshVars : List String) :
    MeTTailCore.MeTTaIL.RewriteIR.RewriteIRRuleMode :=
  if ruleHasCompatHeadConstraint lhs then
    .compatHead
  else if rhsFreshVars.isEmpty then
    .ordinaryForward
  else
    .symbolicOutput

private def deriveRule (rw : RewriteRule) (idx : Nat) : DerivedRule :=
  let key := sourceKeyOfPattern rw.left
  let premJsonList := rw.premises.map Premise.renderJson
  let lhsVars := orderedUniq (orderedScopedFreeVars rw.left)
  let premiseVarFlow := derivePremiseVarFlow lhsVars rw.premises
  let rhsVars := orderedUniq (orderedScopedFreeVars rw.right)
  let rhsMissing := rhsMissingVars lhsVars premiseVarFlow rhsVars
  let (rhsFreshVars, rhsEvalRequires) := splitRhsVarObligations rw.premises rhsMissing
  { ruleId := s!"R{idx}"
    ruleName := rw.name
    sourceInstr := sourceInstrOfKey key
    sourceLabel := sourceLabelOfKey key
    priority := idx
    leftRepr := reprStr rw.left
    rightRepr := reprStr rw.right
    premiseRelations := premiseRelations rw
    lhsJson := rw.left.renderJson
    rhsJson := rw.right.renderJson
    premisesJson := "[" ++ String.intercalate "," premJsonList ++ "]"
    lhsVars := lhsVars
    premiseVarFlow := premiseVarFlow
    rhsVars := rhsVars
    rhsFreshVars := rhsFreshVars
    rhsEvalRequires := rhsEvalRequires
    ruleMode := ruleModeOf rw.left rhsFreshVars
    rootUpdate := rootUpdateHint? rw.left rw.right }

private def foldRewriteRules
    (rules : List RewriteRule)
    (idx : Nat)
    (acc : List DerivedRule) : List DerivedRule :=
  match rules with
  | [] => acc
  | rw :: rest =>
      let next := acc ++ [deriveRule rw idx]
      foldRewriteRules rest (idx + 1) next

private theorem foldRewriteRules_length
    (rules : List RewriteRule) (idx : Nat) (acc : List DerivedRule) :
    (foldRewriteRules rules idx acc).length = acc.length + rules.length := by
  induction rules generalizing idx acc with
  | nil =>
      simp [foldRewriteRules]
  | cons rw rest ih =>
      let next := acc ++ [deriveRule rw idx]
      have hnext : (foldRewriteRules rest (idx + 1) next).length = next.length + rest.length :=
        ih (idx + 1) next
      calc
        (foldRewriteRules (rw :: rest) idx acc).length
            = (foldRewriteRules rest (idx + 1) next).length := by
                simp [foldRewriteRules, next]
        _ = next.length + rest.length := hnext
        _ = acc.length + (rest.length + 1) := by
              simp [next, List.length_append, Nat.add_left_comm, Nat.add_comm]

private def toArtifactRule (r : DerivedRule) : RewriteIRRule :=
  { ruleId := r.ruleId
    ruleName := r.ruleName
    sourceInstr := r.sourceInstr
    sourceLabel := r.sourceLabel
    priority := r.priority
    leftRepr := r.leftRepr
    rightRepr := r.rightRepr
    premiseRelations := r.premiseRelations
    lhsJson := some r.lhsJson
    rhsJson := some r.rhsJson
    premisesJson := some r.premisesJson
    lhsVars := r.lhsVars
    premiseVarFlow := r.premiseVarFlow
    rhsVars := r.rhsVars
    rhsFreshVars := r.rhsFreshVars
    rhsEvalRequires := r.rhsEvalRequires
    ruleMode := r.ruleMode
    rootUpdate := r.rootUpdate }

def derivePeTTaRewriteIR? (s : PeTTaSpace) : Except String RewriteIRArtifact := do
  let lang := pettaSpaceToLangDef s
  let derived := foldRewriteRules lang.rewrites 0 []
  let artifact : RewriteIRArtifact :=
    { schemaVersion := 2
      dialect := "petta"
      rules := derived.map toArtifactRule }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"PeTTa rewrite-ir lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def exportPeTTaRewriteIR (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  match derivePeTTaRewriteIR? s with
  | .error err =>
      IO.println s!"petta rewrite-ir derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "petta.rewrite_ir.json"
      let checksumPath := outDir / "petta.rewrite_ir.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported petta rewrite-ir artifact to {outDir}"
      pure 0

def checkPeTTaRewriteIR (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  match derivePeTTaRewriteIR? s with
  | .error err =>
      IO.println s!"petta rewrite-ir derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "petta.rewrite_ir.json"
      let checksumPath := outDir / "petta.rewrite_ir.checksum"
      try
        let jsonText ← IO.FS.readFile jsonPath
        let checksumText ← IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] petta rewrite-ir artifacts match at {outDir}"
          pure 0
        else
          IO.println s!"[drift] petta rewrite-ir artifacts mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"petta rewrite-ir artifact check failed: {e}"
        pure 2

theorem derivePeTTaRewriteIR_rule_count
    (s : PeTTaSpace) :
    (foldRewriteRules (pettaSpaceToLangDef s).rewrites 0 []).length = s.rules.length := by
  simpa [pettaSpaceToLangDef] using foldRewriteRules_length s.rules 0 []

private def sampleSpace : PeTTaSpace :=
  { facts := []
    rules :=
      [{ name := "sample_rule"
         typeContext := []
         premises := []
         left := .apply "foo" [.fvar "X"]
         right := .apply "bar" [.fvar "X"] }] }

def sampleDerivationIsOk : Bool :=
  match derivePeTTaRewriteIR? sampleSpace with
  | .ok _ => true
  | .error _ => false

#guard sampleDerivationIsOk = true

private def symbolicOutputSampleSpace : PeTTaSpace :=
  { facts := []
    rules :=
      [{ name := "tail_rule"
         typeContext := []
         premises := []
         left := .apply "tail" [.fvar "xs"]
         right := .apply "cons" [.fvar "x", .fvar "xs"] }] }

def symbolicOutputSampleDerivationIsOk : Bool :=
  match derivePeTTaRewriteIR? symbolicOutputSampleSpace with
  | .ok artifact =>
      match artifact.rules with
      | [rule] =>
          rule.rhsFreshVars = ["x"] &&
          rule.rhsEvalRequires = [] &&
          rule.ruleMode = .symbolicOutput
      | _ => false
  | .error _ => false

#guard symbolicOutputSampleDerivationIsOk = true

private def compatHeadSampleSpace : PeTTaSpace :=
  { facts := []
    rules :=
      [{ name := "use_wrap"
         typeContext := []
         premises := []
         left := .apply "use" [.apply "mk" [.fvar "x"], .fvar "y"]
         right := .apply "pair" [.fvar "x", .fvar "y"] }] }

def compatHeadSampleDerivationIsOk : Bool :=
  match derivePeTTaRewriteIR? compatHeadSampleSpace with
  | .ok artifact =>
      match artifact.rules with
      | [rule] =>
          rule.rhsFreshVars = [] &&
          rule.rhsEvalRequires = [] &&
          rule.ruleMode = .compatHead
      | _ => false
  | .error _ => false

#guard compatHeadSampleDerivationIsOk = true

private def emptySampleSpace : PeTTaSpace :=
  { facts := []
    rules := [] }

def emptySampleDerivationIsOk : Bool :=
  match derivePeTTaRewriteIR? emptySampleSpace with
  | .ok artifact => artifact.rules = []
  | .error _ => false

#guard emptySampleDerivationIsOk = true

end Mettapedia.Languages.MeTTa.PeTTa.RewriteIR
