import MeTTailCore
import Algorithms.MeTTa.Simple.Backend.RuleIndex
import Algorithms.MeTTa.Simple.Backend.SpaceIndex

namespace Algorithms.MeTTa.Simple.Backend.CompiledBundle

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure NormalizedRule where
  ord : Nat := 0
  premiseFree : Bool
  leftNorm : Pattern
  rightNorm : Pattern
deriving Repr

structure IndexedNormalizedRule where
  ord : Nat
  leftNorm : Pattern
  rightNorm : Pattern
deriving Repr

structure PremiseFreeBucket where
  ctor : String
  arity : Nat
  rules : List RewriteRule := []
deriving Repr

structure PremiseFreeNormalizedBucket where
  ctor : String
  arity : Nat
  rules : List IndexedNormalizedRule := []
deriving Repr

private def samePremiseFreeKey
    (row : PremiseFreeBucket) (ctor : String) (arity : Nat) : Bool :=
  decide (row.ctor = ctor ∧ row.arity = arity)

structure View where
  rewrites : List RewriteRule
  normalizedRules : List NormalizedRule
  ruleIndex : List Algorithms.MeTTa.Simple.Backend.RuleIndex.HeadEntry
  premiseFreeByHeadArity : List PremiseFreeBucket
  premiseFreeNormalizedByHeadArity : List PremiseFreeNormalizedBucket
  premiseFreeNormalizedFallback : List IndexedNormalizedRule
  spaceIndex : Algorithms.MeTTa.Simple.Backend.SpaceIndex.View
deriving Repr

def empty : View :=
  { rewrites := []
    normalizedRules := []
    ruleIndex := []
    premiseFreeByHeadArity := []
    premiseFreeNormalizedByHeadArity := []
    premiseFreeNormalizedFallback := []
    spaceIndex := Algorithms.MeTTa.Simple.Backend.SpaceIndex.empty }

private def upsertPremiseFreeBucket
    (rows : List PremiseFreeBucket)
    (ctor : String) (arity : Nat) (rule : RewriteRule) : List PremiseFreeBucket :=
  match rows with
  | [] => [{ ctor := ctor, arity := arity, rules := [rule] }]
  | r :: rs =>
      if samePremiseFreeKey r ctor arity then
        { r with rules := r.rules ++ [rule] } :: rs
      else
        r :: upsertPremiseFreeBucket rs ctor arity rule

private def lookupPremiseFreeBucketRules
    (rows : List PremiseFreeBucket)
    (ctor : String) (arity : Nat) : List RewriteRule :=
  match rows with
  | [] => []
  | r :: rs =>
      if samePremiseFreeKey r ctor arity then
        r.rules
      else
        lookupPremiseFreeBucketRules rs ctor arity

private theorem lookupPremiseFreeBucketRules_upsert
    (rows : List PremiseFreeBucket)
    (insCtor : String) (insArity : Nat) (rule : RewriteRule)
    (ctor : String) (arity : Nat) :
    lookupPremiseFreeBucketRules
      (upsertPremiseFreeBucket rows insCtor insArity rule)
      ctor arity =
      if insCtor = ctor ∧ insArity = arity then
        lookupPremiseFreeBucketRules rows ctor arity ++ [rule]
      else
        lookupPremiseFreeBucketRules rows ctor arity := by
  induction rows with
  | nil =>
      by_cases hTarget : insCtor = ctor ∧ insArity = arity
      · simp [upsertPremiseFreeBucket, lookupPremiseFreeBucketRules, samePremiseFreeKey, hTarget]
      · simp [upsertPremiseFreeBucket, lookupPremiseFreeBucketRules, samePremiseFreeKey, hTarget]
  | cons r rs ih =>
      by_cases hRowIns : r.ctor = insCtor ∧ r.arity = insArity
      · by_cases hTarget : insCtor = ctor ∧ insArity = arity
        · simp [upsertPremiseFreeBucket, lookupPremiseFreeBucketRules, samePremiseFreeKey,
            hRowIns, hTarget]
        · simp [upsertPremiseFreeBucket, lookupPremiseFreeBucketRules, samePremiseFreeKey,
            hRowIns, hTarget]
      · by_cases hRowTarget : r.ctor = ctor ∧ r.arity = arity
        · have hTargetFalse : ¬ (insCtor = ctor ∧ insArity = arity) := by
            intro hTarget
            apply hRowIns
            exact ⟨hRowTarget.1.trans hTarget.1.symm, hRowTarget.2.trans hTarget.2.symm⟩
          have hHeadIns : samePremiseFreeKey r insCtor insArity = false := by
            simp [samePremiseFreeKey, hRowIns]
          have hHeadTarget : samePremiseFreeKey r ctor arity = true := by
            simp [samePremiseFreeKey, hRowTarget]
          calc
            lookupPremiseFreeBucketRules
                (upsertPremiseFreeBucket (r :: rs) insCtor insArity rule)
                ctor arity
                =
                lookupPremiseFreeBucketRules
                  (r :: upsertPremiseFreeBucket rs insCtor insArity rule)
                  ctor arity := by
                    simp [upsertPremiseFreeBucket, hHeadIns]
            _ = r.rules := by
                  simp [lookupPremiseFreeBucketRules, hHeadTarget]
            _ =
                (if insCtor = ctor ∧ insArity = arity then
                  lookupPremiseFreeBucketRules (r :: rs) ctor arity ++ [rule]
                else
                  lookupPremiseFreeBucketRules (r :: rs) ctor arity) := by
                    simp [hTargetFalse, lookupPremiseFreeBucketRules, hHeadTarget]
        · by_cases hTarget : insCtor = ctor ∧ insArity = arity
          · rcases hTarget with ⟨hCtor, hArity⟩
            subst hCtor
            subst hArity
            simp [upsertPremiseFreeBucket, lookupPremiseFreeBucketRules, samePremiseFreeKey,
              hRowIns, ih]
          · simp [upsertPremiseFreeBucket, lookupPremiseFreeBucketRules, samePremiseFreeKey,
              hRowIns, hRowTarget, hTarget, ih]

private def buildPremiseFreeBucketsStep
    (rows : List PremiseFreeBucket) (rule : RewriteRule) : List PremiseFreeBucket :=
  if rule.premises.isEmpty then
    match rule.left with
    | .apply ctor args =>
        upsertPremiseFreeBucket rows ctor args.length rule
    | _ =>
        rows
  else
    rows

private def buildPremiseFreeBuckets (rewrites : List RewriteRule) : List PremiseFreeBucket :=
  rewrites.foldl buildPremiseFreeBucketsStep []

private def scanPremiseFreeRulesStep
    (ctor : String) (arity : Nat)
    (acc : List RewriteRule) (rule : RewriteRule) : List RewriteRule :=
  if rule.premises.isEmpty then
    match rule.left with
    | .apply lCtor lArgs =>
        if lCtor = ctor ∧ lArgs.length = arity then
          acc ++ [rule]
        else
          acc
    | _ => acc
  else
    acc

def scanPremiseFreeRulesForHeadArity
    (rewrites : List RewriteRule) (ctor : String) (arity : Nat) : List RewriteRule :=
  rewrites.foldl (scanPremiseFreeRulesStep ctor arity) []

private theorem lookupPremiseFreeBucketRules_buildStep
    (rows : List PremiseFreeBucket) (rule : RewriteRule)
    (ctor : String) (arity : Nat) :
    lookupPremiseFreeBucketRules
      (buildPremiseFreeBucketsStep rows rule)
      ctor arity =
      scanPremiseFreeRulesStep ctor arity
        (lookupPremiseFreeBucketRules rows ctor arity)
        rule := by
  by_cases hPrem : rule.premises.isEmpty
  · cases hLeft : rule.left with
    | fvar x =>
        simp [buildPremiseFreeBucketsStep, scanPremiseFreeRulesStep, hPrem, hLeft]
    | bvar n =>
        simp [buildPremiseFreeBucketsStep, scanPremiseFreeRulesStep, hPrem, hLeft]
    | apply lCtor lArgs =>
        simpa [buildPremiseFreeBucketsStep, scanPremiseFreeRulesStep, hPrem, hLeft] using
          (lookupPremiseFreeBucketRules_upsert rows lCtor lArgs.length rule ctor arity)
    | lambda body =>
        simp [buildPremiseFreeBucketsStep, scanPremiseFreeRulesStep, hPrem, hLeft]
    | multiLambda n body =>
        simp [buildPremiseFreeBucketsStep, scanPremiseFreeRulesStep, hPrem, hLeft]
    | subst body repl =>
        simp [buildPremiseFreeBucketsStep, scanPremiseFreeRulesStep, hPrem, hLeft]
    | collection ct elems rest =>
        simp [buildPremiseFreeBucketsStep, scanPremiseFreeRulesStep, hPrem, hLeft]
  · simp [buildPremiseFreeBucketsStep, scanPremiseFreeRulesStep, hPrem]

private theorem lookupPremiseFreeBucketRules_buildPremiseFreeBuckets_foldl
    (rows : List PremiseFreeBucket) (rewrites : List RewriteRule)
    (ctor : String) (arity : Nat) :
    lookupPremiseFreeBucketRules
      (rewrites.foldl buildPremiseFreeBucketsStep rows)
      ctor arity =
      rewrites.foldl
        (scanPremiseFreeRulesStep ctor arity)
        (lookupPremiseFreeBucketRules rows ctor arity) := by
  induction rewrites generalizing rows with
  | nil =>
      simp
  | cons rule rest ih =>
      simp [List.foldl]
      have hStep :=
        lookupPremiseFreeBucketRules_buildStep rows rule ctor arity
      simpa [hStep, List.foldl] using ih (rows := buildPremiseFreeBucketsStep rows rule)

private def upsertPremiseFreeNormalizedBucket
    (rows : List PremiseFreeNormalizedBucket)
    (ctor : String) (arity : Nat) (rule : IndexedNormalizedRule) :
    List PremiseFreeNormalizedBucket :=
  match rows with
  | [] => [{ ctor := ctor, arity := arity, rules := [rule] }]
  | r :: rs =>
      if r.ctor == ctor && r.arity == arity then
        { r with rules := r.rules ++ [rule] } :: rs
      else
        r :: upsertPremiseFreeNormalizedBucket rs ctor arity rule

private def buildPremiseFreeNormalizedIndex
    (normalizedRules : List NormalizedRule) :
    List PremiseFreeNormalizedBucket × List IndexedNormalizedRule :=
  normalizedRules.foldl
    (fun acc norm =>
      if norm.premiseFree then
        let idxRule : IndexedNormalizedRule :=
          { ord := norm.ord, leftNorm := norm.leftNorm, rightNorm := norm.rightNorm }
        match norm.leftNorm with
        | .apply ctor args =>
            if ctor.startsWith "$" then
              (acc.1, acc.2 ++ [idxRule])
            else
              (upsertPremiseFreeNormalizedBucket acc.1 ctor args.length idxRule, acc.2)
        | _ =>
            (acc.1, acc.2 ++ [idxRule])
      else
        acc)
    ([], [])

def build (normalizePattern : Pattern → Pattern)
    (rewrites : List RewriteRule)
    (selfFacts : List Pattern := []) : View :=
  let rec buildNormalizedRules (ord : Nat) : List RewriteRule → List NormalizedRule
    | [] => []
    | rule :: rest =>
        { ord := ord
          premiseFree := rule.premises.isEmpty
          leftNorm := normalizePattern rule.left
          rightNorm := normalizePattern rule.right } ::
        buildNormalizedRules (ord + 1) rest
  let normalizedRules :=
    buildNormalizedRules 0 rewrites
  let ruleIndex := Algorithms.MeTTa.Simple.Backend.RuleIndex.build rewrites
  let premiseFreeByHeadArity := buildPremiseFreeBuckets rewrites
  let (premiseFreeNormalizedByHeadArity, premiseFreeNormalizedFallback) :=
    buildPremiseFreeNormalizedIndex normalizedRules
  let spaceIndex := Algorithms.MeTTa.Simple.Backend.SpaceIndex.build selfFacts
  { rewrites := rewrites
    normalizedRules := normalizedRules
    ruleIndex := ruleIndex
    premiseFreeByHeadArity := premiseFreeByHeadArity
    premiseFreeNormalizedByHeadArity := premiseFreeNormalizedByHeadArity
    premiseFreeNormalizedFallback := premiseFreeNormalizedFallback
    spaceIndex := spaceIndex }

private partial def mergeByOrd
    (xs ys : List IndexedNormalizedRule) : List IndexedNormalizedRule :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xt, y :: yt =>
      if x.ord <= y.ord then
        x :: mergeByOrd xt ys
      else
        y :: mergeByOrd xs yt

private def findPremiseFreeNormalizedBucket
    (view : View) (ctor : String) (arity : Nat) : List IndexedNormalizedRule :=
  match view.premiseFreeNormalizedByHeadArity.find? (fun r => r.ctor == ctor && r.arity == arity) with
  | some r => r.rules
  | none => []

private def firstReductionFromIndexedRules?
    (rules : List IndexedNormalizedRule)
    (matchPattern : Pattern → Pattern → List Bindings)
    (applyBindings : Bindings → Pattern → Pattern)
    (term : Pattern) : Option Pattern :=
  rules.findSome? (fun rule =>
    match matchPattern rule.leftNorm term with
    | [] => none
    | bs :: _ => some (applyBindings bs rule.rightNorm))

def firstPremiseFreeReduction?
    (view : View)
    (matchPattern : Pattern → Pattern → List Bindings)
    (applyBindings : Bindings → Pattern → Pattern)
    (term : Pattern) : Option Pattern :=
  match term with
  | .apply ctor args =>
      if ctor.startsWith "$" then
        let allPremiseFree :=
          view.normalizedRules.foldl
            (fun acc r =>
              if r.premiseFree then
                acc ++ [{ ord := r.ord, leftNorm := r.leftNorm, rightNorm := r.rightNorm }]
              else
                acc)
            []
        firstReductionFromIndexedRules? allPremiseFree matchPattern applyBindings term
      else
        let byHead := findPremiseFreeNormalizedBucket view ctor args.length
        let merged := mergeByOrd byHead view.premiseFreeNormalizedFallback
        firstReductionFromIndexedRules? merged matchPattern applyBindings term
  | _ =>
      firstReductionFromIndexedRules?
        view.premiseFreeNormalizedFallback
        matchPattern
        applyBindings
        term

def rewriteAritiesForHead (view : View) (ctor : String) : List Nat :=
  Algorithms.MeTTa.Simple.Backend.RuleIndex.aritiesForHead view.ruleIndex ctor

def rewriteCountForHeadArity (view : View) (ctor : String) (arity : Nat) : Nat :=
  Algorithms.MeTTa.Simple.Backend.RuleIndex.rewriteCountForHeadArity view.ruleIndex ctor arity

def hasRuleHead (view : View) (ctor : String) : Bool :=
  Algorithms.MeTTa.Simple.Backend.RuleIndex.hasHead view.ruleIndex ctor

def hasCompatHeadConstraintRule (view : View) (ctor : String) (arity : Nat) : Bool :=
  Algorithms.MeTTa.Simple.Backend.RuleIndex.hasCompatHeadConstraintRule view.ruleIndex ctor arity

def premiseFreeRulesForHeadArity (view : View) (ctor : String) (arity : Nat) : List RewriteRule :=
  lookupPremiseFreeBucketRules view.premiseFreeByHeadArity ctor arity

theorem premiseFreeRulesForHeadArity_build_eq_scan
    (normalizePattern : Pattern → Pattern)
    (rewrites : List RewriteRule)
    (selfFacts : List Pattern)
    (ctor : String) (arity : Nat) :
    premiseFreeRulesForHeadArity (build normalizePattern rewrites selfFacts) ctor arity =
      scanPremiseFreeRulesForHeadArity rewrites ctor arity := by
  simp [premiseFreeRulesForHeadArity, build, buildPremiseFreeBuckets,
    scanPremiseFreeRulesForHeadArity]
  simpa using
    lookupPremiseFreeBucketRules_buildPremiseFreeBuckets_foldl
      (rows := [])
      (rewrites := rewrites)
      (ctor := ctor)
      (arity := arity)

def candidateSelfFacts (view : View) (pat : Pattern) : List Pattern :=
  Algorithms.MeTTa.Simple.Backend.SpaceIndex.candidateSelfFacts view.spaceIndex pat

def candidateSelfTypeEntries (view : View) (x : Pattern) : List (Pattern × Pattern) :=
  Algorithms.MeTTa.Simple.Backend.SpaceIndex.candidateSelfTypeEntries view.spaceIndex x

def typeCandidatesForSelf (view : View)
    (matchPattern : Pattern → Pattern → List Bindings)
    (x : Pattern) : List Pattern :=
  Algorithms.MeTTa.Simple.Backend.SpaceIndex.typeCandidatesForSelf
    view.spaceIndex
    matchPattern
    x

def premiseFreeRuleBindings (view : View)
    (matchPattern : Pattern → Pattern → List Bindings)
    (pat : Pattern) : List Bindings :=
  view.rewrites.foldl
    (fun acc rule =>
      if rule.premises.isEmpty then
        acc ++ matchPattern pat rule.left
      else
        acc)
    []

end Algorithms.MeTTa.Simple.Backend.CompiledBundle
