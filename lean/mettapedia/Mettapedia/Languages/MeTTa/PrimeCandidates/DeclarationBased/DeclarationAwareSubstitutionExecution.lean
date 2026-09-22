import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionReflection
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Execution of the authored canonical binding rules

The existing substitution calculus is oriented by its input/output modes.
Its premises become recursive congruence calls in the ordinary `LanguageDef`
interpreter.  There is no substitution callback and no supplied proof tree.
The term representation remains the existing canonical first-order codec.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef
open DeclarationAwareSubstitutionLanguage
open DeclarationAwarePatternCodec
open DeclarationAwareSubstitutionSemantics
open DeclarationAwareSubstitutionCompiler

/-- An order query returns the existing zero datum when its relation holds.
This is an operation result, not an object-theory truth value. -/
def accepted : Pattern := zero

def weaken (cutoff source : Pattern) : Pattern :=
  .apply "prime-tm-weakens-at" [cutoff, source]

def substitute (index replacement source : Pattern) : Pattern :=
  .apply "prime-tm-substitutes-at" [index, replacement, source]

def beta (source : Pattern) : Pattern :=
  .apply "prime-tm-root-beta" [source]

/-- Explicit modes for the four existing judgments.  The input and output
are obtained from the authored judgment, rather than from a second rule table. -/
def orientJudgment : Pattern → Option (Pattern × Pattern)
  | .apply "prime-index-lt" [left, right] =>
      some (indexLt left right, accepted)
  | .apply "prime-tm-weakens-at" [cutoff, source, target] =>
      some (weaken cutoff source, target)
  | .apply "prime-tm-substitutes-at" [index, replacement, source, target] =>
      some (substitute index replacement source, target)
  | .apply "prime-tm-root-beta" [source, target] =>
      some (beta source, target)
  | _ => none

def orientPremises : List Pattern → Option (List Premise)
  | [] => some []
  | premise :: rest => do
      let (source, target) ← orientJudgment premise
      let tail ← orientPremises rest
      pure (.congruence source target :: tail)

/-- Only the empty-side-condition fragment is oriented here.  An unsupported
judgment or condition is refused, never silently dropped. -/
def orientRule (schema : RuleSchema) : Option RewriteRule := do
  if !schema.sideConditions.isEmpty then none else do
    let (source, target) ← orientJudgment schema.conclusion
    let premises ← orientPremises schema.premises
    pure { name := schema.id.value
           typeContext := []
           premises
           left := source
           right := target }

def rules : List RewriteRule := allRules.filterMap orientRule

def language : LanguageDef :=
  { DeclarationAwareDataLanguage.language with
    name := "prime-canonical-binding-execution-v1"
    terms := DeclarationAwareDataLanguage.language.terms ++
      [("prime-index-lt", 2), ("prime-tm-weakens-at", 2),
       ("prime-tm-substitutes-at", 3), ("prime-tm-root-beta", 1)].map
        (fun specification => DeclarationAwareDataLanguage.dataConstructor
          specification.1 specification.2)
    rewrites := rules }

def execute (fuel : Nat) (source : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises RelationEnv.empty) language fuel source

/-- Every original schema has an executable orientation. -/
theorem every_schema_oriented :
    ∀ schema ∈ allRules, (orientRule schema).isSome = true := by
  decide

/-- No authored case disappears during orientation. -/
theorem rule_count : rules.length = 30 := by decide

/-- Rule identity and occurrence order survive the orientation. -/
theorem rule_names : rules.map (·.name) = allRules.map (·.id.value) := by
  decide

def lessAt : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | _ + 1, 0, _ + 1 => true
  | fuel + 1, left + 1, right + 1 => lessAt fuel left right
  | _ + 1, _, _ => false

private theorem execute_zero (source : Pattern) : execute 0 source = [] := rfl

theorem execute_succ (fuel : Nat) (source : Pattern) :
    execute (fuel + 1) source = rules.flatMap
      (fun rule => applyRuleUsing (engineBasePremises RelationEnv.empty)
        language (execute fuel) rule source) := rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
theorem execute_indexLt (fuel left right : Nat) :
    execute fuel (indexLt (encodeNat left) (encodeNat right)) =
      if lessAt fuel left right then [accepted] else [] := by
  induction fuel generalizing left right with
  | zero => simp [execute, rewriteAt, lessAt]
  | succ fuel ih =>
    cases left <;> cases right <;>
      simp [execute_succ, rules,
        allRules, orientRule, orientPremises, orientJudgment,
        ltZeroSuccRule, ltSuccSuccRule,
        weakenVarBelowRule, weakenVarAtOrAboveRule,
        weakenConstRule, weakenHeadRule, weakenPiRule, weakenSigmaRule,
        weakenIdRule, weakenLamRule, weakenAppRule, weakenPairRule,
        weakenFstRule, weakenSndRule, weakenReflRule,
        substVarEqualRule, substVarBelowRule, substVarAboveRule,
        substConstRule, substHeadRule, substPiRule, substSigmaRule,
        substIdRule, substLamRule, substAppRule, substPairRule,
        substFstRule, substSndRule, substReflRule, rootBetaRule,
        rule, ruleId, m, indexLt, weakensAt, substitutesAt,
        DeclarationAwareSubstitutionLanguage.rootBeta,
        weaken, substitute, beta, zero, succ, tmVar, tmConst, tmHead,
        tmPi, tmSigma, tmId, tmLam, tmApp, tmPair, tmFst, tmSnd, tmRefl,
        applyRuleUsing, matchPatternForRule_eq_syntactic,
        matchPattern, matchArgs, mergeBindings, premisesUsing,
        premiseStepUsing, applyBindingsForRule, applyRuleBindings, applyBindings,
        Bindings.lookup, encodeNat, accepted, lessAt]
    rename_i left right
    have recursive := ih left right
    simp only [indexLt, accepted, zero] at recursive
    rw [recursive]
    split <;> simp_all [matchPattern, matchArgs, mergeBindings]

theorem lessAt_sound {fuel left right : Nat}
    (accepted : lessAt fuel left right = true) : left < right := by
  induction fuel generalizing left right with
  | zero => simp [lessAt] at accepted
  | succ fuel ih =>
    cases left <;> cases right <;> simp [lessAt] at accepted ⊢
    exact ih accepted

theorem lessAt_complete (left right fuel : Nat)
    (less : left < right) (enough : left < fuel) :
    lessAt fuel left right = true := by
  induction fuel generalizing left right with
  | zero => omega
  | succ fuel ih =>
    cases left <;> cases right <;> simp [lessAt] <;> try omega
    apply ih <;> omega

theorem indexLt_exact (left right : Nat) :
    (∃ fuel, accepted ∈ execute fuel
      (indexLt (encodeNat left) (encodeNat right))) ↔ left < right := by
  constructor
  · rintro ⟨fuel, member⟩
    rw [execute_indexLt] at member
    split at member
    · exact lessAt_sound (by assumption)
    · simp at member
  · intro less
    refine ⟨left + 1, ?_⟩
    rw [execute_indexLt, lessAt_complete left right (left + 1) less (by omega)]
    simp

theorem indexLt_rejects_irreflexive (index fuel : Nat) :
    execute fuel (indexLt (encodeNat index) (encodeNat index)) = [] := by
  rw [execute_indexLt]
  split
  · exact False.elim (Nat.lt_irrefl index (lessAt_sound (by assumption)))
  · rfl

/-- A depth-bounded independent evaluator.  Failure here means that this
particular contextual-depth bound does not yet contain a complete derivation. -/
def weakenFuel : Nat → Nat → RawTerm → Option RawTerm
  | 0, _, _ => none
  | fuel + 1, cutoff, .var index =>
      if lessAt fuel index cutoff then some (.var index)
      else if lessAt fuel cutoff (index + 1) then some (.var (index + 1))
      else none
  | _ + 1, _, .const name => some (.const name)
  | _ + 1, _, .head head => some (.head head)
  | fuel + 1, cutoff, .pi domain body => do
      let domain' ← weakenFuel fuel cutoff domain
      let body' ← weakenFuel fuel (cutoff + 1) body
      pure (.pi domain' body')
  | fuel + 1, cutoff, .sigma domain body => do
      let domain' ← weakenFuel fuel cutoff domain
      let body' ← weakenFuel fuel (cutoff + 1) body
      pure (.sigma domain' body')
  | fuel + 1, cutoff, .id type left right => do
      let type' ← weakenFuel fuel cutoff type
      let left' ← weakenFuel fuel cutoff left
      let right' ← weakenFuel fuel cutoff right
      pure (.id type' left' right')
  | fuel + 1, cutoff, .lam body => do
      let body' ← weakenFuel fuel (cutoff + 1) body
      pure (.lam body')
  | fuel + 1, cutoff, .app function argument => do
      let function' ← weakenFuel fuel cutoff function
      let argument' ← weakenFuel fuel cutoff argument
      pure (.app function' argument')
  | fuel + 1, cutoff, .pair first second => do
      let first' ← weakenFuel fuel cutoff first
      let second' ← weakenFuel fuel cutoff second
      pure (.pair first' second')
  | fuel + 1, cutoff, .fst pair => do
      let pair' ← weakenFuel fuel cutoff pair
      pure (.fst pair')
  | fuel + 1, cutoff, .snd pair => do
      let pair' ← weakenFuel fuel cutoff pair
      pure (.snd pair')
  | fuel + 1, cutoff, .refl term => do
      let term' ← weakenFuel fuel cutoff term
      pure (.refl term')

def resultPatterns (result : Option RawTerm) : List Pattern :=
  result.toList.map encodeRaw

theorem weakenFuel_sound {fuel cutoff : Nat} {term output : RawTerm}
    (evidence : weakenFuel fuel cutoff term = some output) :
    output = weakenAt cutoff term := by
  induction fuel generalizing cutoff term output with
  | zero => simp [weakenFuel] at evidence
  | succ fuel ih =>
    cases term <;> simp only [weakenFuel] at evidence
    case var index =>
      split at evidence
      next low =>
        cases evidence
        simp [weakenAt, lessAt_sound low]
      next notLow =>
        split at evidence
        next high =>
          cases evidence
          have bound := lessAt_sound high
          simp [weakenAt, show ¬ index < cutoff by omega]
        next => cases evidence
    case const name => cases evidence; rfl
    case head head => cases evidence; rfl
    all_goals
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at evidence
      first
      | obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := evidence
        simp [weakenAt, ih ha, ih hb, ih hc]
      | obtain ⟨a, ha, b, hb, rfl⟩ := evidence
        simp [weakenAt, ih ha, ih hb]
      | obtain ⟨a, ha, rfl⟩ := evidence
        simp [weakenAt, ih ha]

/-- An explicit sufficient derivation depth, including the index comparison
needed at variables and the shifted cutoff under each binder. -/
def weakenDepth (cutoff : Nat) : RawTerm → Nat
  | .var index => max index cutoff + 2
  | .const _ | .head _ => 1
  | .pi domain body | .sigma domain body =>
      max (weakenDepth cutoff domain) (weakenDepth (cutoff + 1) body) + 1
  | .id type left right =>
      max (weakenDepth cutoff type)
        (max (weakenDepth cutoff left) (weakenDepth cutoff right)) + 1
  | .lam body => weakenDepth (cutoff + 1) body + 1
  | .app left right | .pair left right =>
      max (weakenDepth cutoff left) (weakenDepth cutoff right) + 1
  | .fst pair | .snd pair => weakenDepth cutoff pair + 1
  | .refl term => weakenDepth cutoff term + 1

theorem weakenDepth_positive (cutoff : Nat) (term : RawTerm) :
    0 < weakenDepth cutoff term := by
  cases term <;> simp [weakenDepth]

theorem weakenFuel_complete (term : RawTerm) (cutoff fuel : Nat)
    (enough : weakenDepth cutoff term ≤ fuel) :
    weakenFuel fuel cutoff term = some (weakenAt cutoff term) := by
  induction term generalizing cutoff fuel with
  | var index =>
    cases fuel with
    | zero => simp [weakenDepth] at enough
    | succ fuel =>
      simp only [weakenDepth] at enough
      by_cases low : index < cutoff
      · have accepted := lessAt_complete index cutoff fuel low (by omega)
        simp [weakenFuel, weakenAt, accepted, low]
      · have high : cutoff < index + 1 := by omega
        have accepted := lessAt_complete cutoff (index + 1) fuel high (by omega)
        have rejected : lessAt fuel index cutoff = false := by
          cases result : lessAt fuel index cutoff
          · rfl
          · exact False.elim (low (lessAt_sound result))
        simp [weakenFuel, weakenAt, accepted, rejected, low]
  | const name =>
    cases fuel <;> simp_all [weakenDepth, weakenFuel, weakenAt]
  | head head =>
    cases fuel <;> simp_all [weakenDepth, weakenFuel, weakenAt]
  | pi domain body domainIH bodyIH
  | sigma domain body domainIH bodyIH =>
    cases fuel with
    | zero => simp [weakenDepth] at enough
    | succ fuel =>
      simp only [weakenDepth] at enough
      simp [weakenFuel, weakenAt, domainIH cutoff fuel (by omega),
        bodyIH (cutoff + 1) fuel (by omega)]
  | id type left right typeIH leftIH rightIH =>
    cases fuel with
    | zero => simp [weakenDepth] at enough
    | succ fuel =>
      simp only [weakenDepth] at enough
      simp [weakenFuel, weakenAt, typeIH cutoff fuel (by omega),
        leftIH cutoff fuel (by omega), rightIH cutoff fuel (by omega)]
  | lam body bodyIH =>
    cases fuel with
    | zero => simp [weakenDepth] at enough
    | succ fuel =>
      simp only [weakenDepth] at enough
      simp [weakenFuel, weakenAt, bodyIH (cutoff + 1) fuel (by omega)]
  | app left right leftIH rightIH
  | pair left right leftIH rightIH =>
    cases fuel with
    | zero => simp [weakenDepth] at enough
    | succ fuel =>
      simp only [weakenDepth] at enough
      simp [weakenFuel, weakenAt, leftIH cutoff fuel (by omega),
        rightIH cutoff fuel (by omega)]
  | fst term ih | snd term ih | refl term ih =>
    cases fuel with
    | zero => simp [weakenDepth] at enough
    | succ fuel =>
      simp only [weakenDepth] at enough
      simp [weakenFuel, weakenAt, ih cutoff fuel (by omega)]

theorem fold_encodeNat_succ (index : Nat) :
    Pattern.apply "prime-nat-succ" [encodeNat index] = encodeNat (index + 1) := rfl

macro "unfold_binding_execution" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 })
    [execute_succ, rules, allRules, orientRule, orientPremises, orientJudgment,
     ltZeroSuccRule, ltSuccSuccRule,
     weakenVarBelowRule, weakenVarAtOrAboveRule,
     weakenConstRule, weakenHeadRule, weakenPiRule, weakenSigmaRule,
     weakenIdRule, weakenLamRule, weakenAppRule, weakenPairRule,
     weakenFstRule, weakenSndRule, weakenReflRule,
     substVarEqualRule, substVarBelowRule, substVarAboveRule,
     substConstRule, substHeadRule, substPiRule, substSigmaRule,
     substIdRule, substLamRule, substAppRule, substPairRule,
     substFstRule, substSndRule, substReflRule, rootBetaRule,
     rule, ruleId, m, indexLt, weakensAt, substitutesAt,
     DeclarationAwareSubstitutionLanguage.rootBeta,
     weaken, substitute, beta, zero, succ, tmVar, tmConst, tmHead,
     tmPi, tmSigma, tmId, tmLam, tmApp, tmPair, tmFst, tmSnd, tmRefl,
     applyRuleUsing, matchPatternForRule_eq_syntactic,
     matchPattern, matchArgs, mergeBindings, premisesUsing,
     premiseStepUsing, applyBindingsForRule,
     Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings, applyBindings,
     Bindings.lookup, encodeRaw, encode, encodeNat, accepted])

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
set_option linter.unusedSimpArgs false in
theorem execute_weaken (fuel cutoff : Nat) (term : RawTerm) :
    execute fuel (weaken (encodeNat cutoff) (encodeRaw term)) =
      resultPatterns (weakenFuel fuel cutoff term) := by
  induction fuel generalizing cutoff term with
  | zero => rfl
  | succ fuel ih =>
    have lt := execute_indexLt fuel
    simp only [indexLt, accepted, zero] at lt
    simp only [weaken, encodeRaw] at ih
    cases term <;> unfold_binding_execution
    all_goals simp only [ih, lt, weakenFuel, resultPatterns]
    all_goals simp [List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
      fold_encodeNat_succ, ih, lt, resultPatterns, Option.toList_bind,
      Function.comp_def, encodeRaw, encode]
    rename_i index
    by_cases low : lessAt fuel index cutoff = true
    · have high : lessAt fuel cutoff (index + 1) = false := by
        cases result : lessAt fuel cutoff (index + 1)
        · rfl
        · have lower := lessAt_sound low
          have upper := lessAt_sound result
          omega
      simp [low, high, matchPattern, matchArgs, mergeBindings, encodeRaw, encode,
        Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings]
    · by_cases high : lessAt fuel cutoff (index + 1) = true <;>
        simp [low, high, matchPattern, matchArgs, mergeBindings, encodeRaw, encode, encodeNat]

theorem execute_weaken_exact (cutoff : Nat) (term : RawTerm) (output : Pattern) :
    (∃ fuel, output ∈ execute fuel (weaken (encodeNat cutoff) (encodeRaw term))) ↔
      output = encodeRaw (weakenAt cutoff term) := by
  constructor
  · rintro ⟨fuel, member⟩
    rw [execute_weaken] at member
    simp only [resultPatterns, List.mem_map, Option.mem_toList] at member
    obtain ⟨raw, evidence, rfl⟩ := member
    rw [weakenFuel_sound evidence]
  · rintro rfl
    refine ⟨weakenDepth cutoff term, ?_⟩
    rw [execute_weaken, weakenFuel_complete term cutoff _ (by rfl)]
    simp [resultPatterns]

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecution
