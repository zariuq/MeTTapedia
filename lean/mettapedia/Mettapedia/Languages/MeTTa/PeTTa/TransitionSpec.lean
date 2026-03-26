import MeTTailCore
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness

/-!
# PeTTa Transition Spec Artifact Derivation

Unlike HE, PeTTa does not currently expose one fixed interpreter `LanguageDef`
whose rewrite graph can be exported once for the whole dialect. The honest
artifact boundary is therefore **program-parametric**:

- input: a specific `PeTTaSpace`
- source language: `pettaSpaceToLangDef s`
- output: a `TransitionSpecArtifact` describing the ordered root-rewrite
  candidates for that space

This is the correct preparation layer for the shared mettail-rust native
contract path: Rust should consume PeTTa transition metadata derived from the
actual lowered PeTTa program, not from an invented HE-style global machine.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec

open MeTTailCore.MeTTaIL.TransitionSpec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Languages.MeTTa.PeTTa

structure SourceKey where
  headTag : String
  arity : Nat
deriving Repr, DecidableEq, BEq

private structure DerivedTransition where
  sourceKey : SourceKey
  sourceInstr : String
  sourceLabel : String
  ruleName : String
  ruleId : String
  priority : Nat
  hasFreshnessPremise : Bool
  hasCongruencePremise : Bool
  premiseRelations : List String
deriving Repr

def sanitizeToken (s : String) : String :=
  let mapped := s.toList.map fun c =>
    if c.isAlphanum then
      String.singleton c
    else
      "_"
  let joined := String.intercalate "" mapped
  if joined.isEmpty then "_" else joined

def sourceKeyOfPattern : Pattern → SourceKey
  | .apply head args => { headTag := head, arity := args.length }
  | .fvar _ => { headTag := "$fvar", arity := 0 }
  | .bvar _ => { headTag := "$bvar", arity := 0 }
  | .lambda _ _ => { headTag := "$lambda", arity := 1 }
  | .multiLambda n _ _ => { headTag := s!"$multiLambda{n}", arity := 1 }
  | .subst _ _ => { headTag := "$subst", arity := 2 }
  | .collection ct elems rest =>
      let collTag :=
        match ct with
        | .vec => "vec"
        | .hashBag => "hashBag"
        | .hashSet => "hashSet"
      let restTag := if rest.isSome then "_rest" else ""
      { headTag := s!"$collection_{collTag}{restTag}", arity := elems.length }

def sourceInstrOfKey (k : SourceKey) : String :=
  s!"C_{sanitizeToken k.headTag}_A{k.arity}"

def sourceLabelOfKey (k : SourceKey) : String :=
  s!"{k.headTag}/{k.arity}"

private def premiseRelations (rw : RewriteRule) : List String :=
  rw.premises.filterMap fun
    | .relationQuery rel _ => some rel
    | _ => none

private def hasFreshnessPremise (rw : RewriteRule) : Bool :=
  rw.premises.any fun
    | .freshness _ => true
    | _ => false

private def hasCongruencePremise (rw : RewriteRule) : Bool :=
  rw.premises.any fun
    | .congruence _ _ => true
    | _ => false

private def addRuleToSource
    (sources : List TransitionSource)
    (sourceInstr sourceLabel ruleId : String) : List TransitionSource :=
  match sources with
  | [] =>
      [{ sourceInstr := sourceInstr
         sourceLabel := sourceLabel
         orderedRules := [ruleId] }]
  | s :: rest =>
      if s.sourceInstr == sourceInstr then
        { s with orderedRules := s.orderedRules ++ [ruleId] } :: rest
      else
        s :: addRuleToSource rest sourceInstr sourceLabel ruleId

private def foldRewriteTransitions
    (rules : List RewriteRule)
    (idx : Nat)
    (acc : List DerivedTransition) : List DerivedTransition :=
  match rules with
  | [] => acc
  | rw :: rest =>
      let key := sourceKeyOfPattern rw.left
      let next := acc ++ [{ sourceKey := key
                            sourceInstr := sourceInstrOfKey key
                            sourceLabel := sourceLabelOfKey key
                            ruleName := rw.name
                            ruleId := s!"R{idx}"
                            priority := idx
                            hasFreshnessPremise := hasFreshnessPremise rw
                            hasCongruencePremise := hasCongruencePremise rw
                            premiseRelations := premiseRelations rw }]
      foldRewriteTransitions rest (idx + 1) next

private theorem foldRewriteTransitions_length
    (rules : List RewriteRule) (idx : Nat) (acc : List DerivedTransition) :
    (foldRewriteTransitions rules idx acc).length = acc.length + rules.length := by
  induction rules generalizing idx acc with
  | nil =>
      simp [foldRewriteTransitions]
  | cons rw rest ih =>
      simp [foldRewriteTransitions]
      let next :=
        acc ++ [{
          sourceKey := sourceKeyOfPattern rw.left
          sourceInstr := sourceInstrOfKey (sourceKeyOfPattern rw.left)
          sourceLabel := sourceLabelOfKey (sourceKeyOfPattern rw.left)
          ruleName := rw.name
          ruleId := s!"R{idx}"
          priority := idx
          hasFreshnessPremise := hasFreshnessPremise rw
          hasCongruencePremise := hasCongruencePremise rw
          premiseRelations := premiseRelations rw
        }]
      calc
        (foldRewriteTransitions rest (idx + 1) next).length
            = next.length + rest.length := ih (idx + 1) next
        _ = acc.length + 1 + rest.length := by
              simp [next, List.length_append, Nat.add_assoc]
        _ = acc.length + (rest.length + 1) := by
              rw [Nat.add_assoc, Nat.add_comm 1 rest.length]

private def sourceInstrClassFor (t : DerivedTransition) : String :=
  if t.sourceKey.headTag.startsWith "$" then
    "pattern_root"
  else
    "apply_head"

private def transitionKindFor (t : DerivedTransition) : String :=
  if !t.premiseRelations.isEmpty then
    "rewrite_with_relation_premises"
  else if t.hasFreshnessPremise then
    "rewrite_with_freshness"
  else if t.hasCongruencePremise then
    "rewrite_with_congruence"
  else
    "rewrite_root"

private def guardFamilyFor (t : DerivedTransition) : String :=
  if t.premiseRelations.contains "spaceMatch" then
    "space_match"
  else if !t.premiseRelations.isEmpty then
    "relation_query"
  else if t.hasFreshnessPremise then
    "freshness"
  else if t.hasCongruencePremise then
    "congruence"
  else
    "pattern_match"

private def effectKindFor (_t : DerivedTransition) : String :=
  "emit_pattern"

private def contractsFor (_t : DerivedTransition) : List TransitionContract :=
  [ TransitionContract.nondeterministic
  , TransitionContract.orderSensitive
  , TransitionContract.memoizationSafe
  , TransitionContract.specializationSafe
  ]

private def toSpecRule (t : DerivedTransition) : TransitionRule :=
  { logicalTransitionId := s!"{t.sourceInstr}:{t.ruleName}"
    sourceInstr := t.sourceInstr
    sourceLabel := t.sourceLabel
    ruleId := t.ruleId
    semKey :=
      { sourceInstrClass := sourceInstrClassFor t
        transitionKind := transitionKindFor t
        guardFamily := guardFamilyFor t
        effectKind := effectKindFor t
        dialectExt := none
        contracts := contractsFor t }
    priority := t.priority }

def derivePeTTaTransitionSpec? (s : PeTTaSpace) : Except String TransitionSpecArtifact := do
  let lang := pettaSpaceToLangDef s
  let derived := foldRewriteTransitions lang.rewrites 0 []
  let sources :=
    derived.foldl
      (fun acc t => addRuleToSource acc t.sourceInstr t.sourceLabel t.ruleId)
      []
  let artifact : TransitionSpecArtifact :=
    { schemaVersion := 2
      dialect := "petta"
      sources := sources
      rules := derived.map toSpecRule }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"PeTTa transition-spec lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def exportPeTTaTransitionSpec (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  match derivePeTTaTransitionSpec? s with
  | .error err =>
      IO.println s!"petta transition-spec derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "petta.transition_spec.json"
      let checksumPath := outDir / "petta.transition_spec.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported petta transition-spec artifact to {outDir}"
      pure 0

def checkPeTTaTransitionSpec (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  match derivePeTTaTransitionSpec? s with
  | .error err =>
      IO.println s!"petta transition-spec derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "petta.transition_spec.json"
      let checksumPath := outDir / "petta.transition_spec.checksum"
      try
        let jsonText ← IO.FS.readFile jsonPath
        let checksumText ← IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] petta transition artifacts match at {outDir}"
          pure 0
        else
          IO.println s!"[drift] petta transition artifacts mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"petta transition artifact check failed: {e}"
        pure 2

theorem derivePeTTaTransitionSpec_rule_count
    (s : PeTTaSpace) :
    (foldRewriteTransitions (pettaSpaceToLangDef s).rewrites 0 []).length = s.rules.length := by
  simpa [pettaSpaceToLangDef] using foldRewriteTransitions_length s.rules 0 []

private def sampleSpace : PeTTaSpace :=
  { facts := []
    rules :=
      [{ name := "sample_rule"
         typeContext := []
         premises := []
         left := .apply "foo" [.fvar "X"]
         right := .apply "bar" [.fvar "X"] }] }

def sampleDerivationIsOk : Bool :=
  match derivePeTTaTransitionSpec? sampleSpace with
  | .ok _ => true
  | .error _ => false

#guard sampleDerivationIsOk = true

private def emptySampleSpace : PeTTaSpace :=
  { facts := []
    rules := [] }

def emptySampleDerivationIsOk : Bool :=
  match derivePeTTaTransitionSpec? emptySampleSpace with
  | .ok artifact => artifact.sources = [] && artifact.rules = []
  | .error _ => false

#guard emptySampleDerivationIsOk = true

end Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
