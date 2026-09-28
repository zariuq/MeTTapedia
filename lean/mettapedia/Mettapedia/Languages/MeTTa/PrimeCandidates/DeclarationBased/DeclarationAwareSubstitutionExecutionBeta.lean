import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecution
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareErasureNaturality
import Mettapedia.OSLF.MeTTaIL.ContextualStepFuel

/-!
# Capture-avoiding substitution and beta through authored rule execution

The canonical binding schema orientations are executed by the generic
contextual interpreter, then compared with the intrinsic native operation.
No proof certificate or native substitution callback is an input.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecution

open Mettapedia.OSLF.MeTTaIL Syntax Match ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open DeclarationAwareSubstitutionLanguage DeclarationAwarePatternCodec
open DeclarationAwareSubstitutionSemantics DeclarationAwareSubstitutionCompiler

def substituteFuel : Nat → Nat → RawTerm → RawTerm → Option RawTerm
  | 0, _, _, _ => none
  | fuel + 1, index, replacement, .var variableIndex =>
      if variableIndex = index then some replacement
      else if lessAt fuel variableIndex index then some (.var variableIndex)
      else if lessAt fuel index variableIndex then some (.var (variableIndex - 1))
      else none
  | _ + 1, _, _, .const name => some (.const name)
  | _ + 1, _, _, .head head => some (.head head)
  | fuel + 1, index, replacement, .pi domain body => do
      let domain' ← substituteFuel fuel index replacement domain
      let lifted ← weakenFuel fuel 0 replacement
      let body' ← substituteFuel fuel (index + 1) lifted body
      pure (.pi domain' body')
  | fuel + 1, index, replacement, .sigma domain body => do
      let domain' ← substituteFuel fuel index replacement domain
      let lifted ← weakenFuel fuel 0 replacement
      let body' ← substituteFuel fuel (index + 1) lifted body
      pure (.sigma domain' body')
  | fuel + 1, index, replacement, .id type left right => do
      let type' ← substituteFuel fuel index replacement type
      let left' ← substituteFuel fuel index replacement left
      let right' ← substituteFuel fuel index replacement right
      pure (.id type' left' right')
  | fuel + 1, index, replacement, .lam body => do
      let lifted ← weakenFuel fuel 0 replacement
      let body' ← substituteFuel fuel (index + 1) lifted body
      pure (.lam body')
  | fuel + 1, index, replacement, .app function argument => do
      let function' ← substituteFuel fuel index replacement function
      let argument' ← substituteFuel fuel index replacement argument
      pure (.app function' argument')
  | fuel + 1, index, replacement, .pair first second => do
      let first' ← substituteFuel fuel index replacement first
      let second' ← substituteFuel fuel index replacement second
      pure (.pair first' second')
  | fuel + 1, index, replacement, .fst pair => do
      let pair' ← substituteFuel fuel index replacement pair
      pure (.fst pair')
  | fuel + 1, index, replacement, .snd pair => do
      let pair' ← substituteFuel fuel index replacement pair
      pure (.snd pair')
  | fuel + 1, index, replacement, .refl term => do
      let term' ← substituteFuel fuel index replacement term
      pure (.refl term')

private theorem fold_encodeNat_zero :
    Pattern.apply "prime-nat-zero" [] = encodeNat 0 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
set_option linter.unusedSimpArgs false in
theorem execution_language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites <;> try decide
  change ∀ rewrite ∈ rules, language.validateRewrite rewrite = []
  unfold_binding_execution
  repeat' apply And.intro
  all_goals simp (config := { maxSteps := 1000000 })
    [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
     LanguageDef.validatePatternConstructors, LanguageDef.patternBinderNames,
     LanguageDef.patternFvarNames, LanguageDef.premiseFvarNames,
     LanguageDef.premiseProducedFvarNames, LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped,
    LanguageDef.premisePatterns,
     LanguageDef.premiseForAllParams, Pattern.freeFvarNames,
     Pattern.constructorRefs, Pattern.constructorRefsList,
     Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
     language, DeclarationAwareDataLanguage.language, DeclarationAwareDataLanguage.definition,
     DeclarationAwareDataLanguage.constructorArities, DeclarationAwareDataLanguage.dataConstructor]
theorem intrinsic_weaken_exact {n : Nat}
    (term : Presentation.Tower.Tm n) (output : Pattern) :
    (∃ fuel, output ∈ execute fuel
      (weaken (encodeNat 0) (encodeTm towerHeadCodec term))) ↔
      output = encodeTm towerHeadCodec (Presentation.rename Presentation.wk term) := by
  simpa only [encodeRaw, ← DeclarationAwareErasureNaturality.erase_rename_wk,
    encode_erase] using execute_weaken_exact 0 (erase term) output

theorem substituteFuel_sound {fuel index : Nat} {replacement term output : RawTerm}
    (evidence : substituteFuel fuel index replacement term = some output) :
    output = substituteAt index replacement term := by
  induction fuel generalizing index replacement term output with
  | zero => simp [substituteFuel] at evidence
  | succ fuel ih =>
    cases term <;> simp only [substituteFuel] at evidence
    case var variableIndex =>
      split at evidence
      next equal =>
        cases evidence
        simp [substituteAt, equal]
      next notEqual =>
        split at evidence
        next low =>
          cases evidence
          simp [substituteAt, notEqual, lessAt_sound low]
        next notLow =>
          split at evidence
          next high =>
            cases evidence
            have bound := lessAt_sound high
            simp [substituteAt, notEqual, show ¬ variableIndex < index by omega]
          next => cases evidence
    case const name => cases evidence; rfl
    case head head => cases evidence; rfl
    case pi domain body | sigma domain body =>
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at evidence
      obtain ⟨domain', domainStep, lifted, liftStep, body', bodyStep, rfl⟩ := evidence
      have liftedEq := weakenFuel_sound liftStep
      rw [liftedEq] at bodyStep
      simp [substituteAt, ih domainStep, ih bodyStep]
    case lam body =>
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at evidence
      obtain ⟨lifted, liftStep, body', bodyStep, rfl⟩ := evidence
      have liftedEq := weakenFuel_sound liftStep
      rw [liftedEq] at bodyStep
      simp [substituteAt, ih bodyStep]
    all_goals
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at evidence
      first
      | obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := evidence
        simp [substituteAt, ih ha, ih hb, ih hc]
      | obtain ⟨a, ha, b, hb, rfl⟩ := evidence
        simp [substituteAt, ih ha, ih hb]
      | obtain ⟨a, ha, rfl⟩ := evidence
        simp [substituteAt, ih ha]

def substituteDepth (index : Nat) (replacement : RawTerm) : RawTerm → Nat
  | .var variableIndex => max variableIndex index + 2
  | .const _ | .head _ => 1
  | .pi domain body | .sigma domain body =>
      max (substituteDepth index replacement domain)
        (max (weakenDepth 0 replacement)
          (substituteDepth (index + 1) (weakenAt 0 replacement) body)) + 1
  | .id type left right =>
      max (substituteDepth index replacement type)
        (max (substituteDepth index replacement left)
          (substituteDepth index replacement right)) + 1
  | .lam body =>
      max (weakenDepth 0 replacement)
        (substituteDepth (index + 1) (weakenAt 0 replacement) body) + 1
  | .app left right | .pair left right =>
      max (substituteDepth index replacement left)
        (substituteDepth index replacement right) + 1
  | .fst pair | .snd pair => substituteDepth index replacement pair + 1
  | .refl term => substituteDepth index replacement term + 1

theorem substituteFuel_complete (term replacement : RawTerm) (index fuel : Nat)
    (enough : substituteDepth index replacement term ≤ fuel) :
    substituteFuel fuel index replacement term = some (substituteAt index replacement term) := by
  induction term generalizing index replacement fuel with
  | var variableIndex =>
    cases fuel with
    | zero => simp [substituteDepth] at enough
    | succ fuel =>
      simp only [substituteDepth] at enough
      by_cases equal : variableIndex = index
      · simp [substituteFuel, substituteAt, equal]
      · by_cases low : variableIndex < index
        · have accepted := lessAt_complete variableIndex index fuel low (by omega)
          simp [substituteFuel, substituteAt, equal, accepted, low]
        · have high : index < variableIndex := by omega
          have accepted := lessAt_complete index variableIndex fuel high (by omega)
          have rejected : lessAt fuel variableIndex index = false := by
            cases result : lessAt fuel variableIndex index
            · rfl
            · exact False.elim (low (lessAt_sound result))
          simp [substituteFuel, substituteAt, equal, accepted, rejected, low]
  | const name =>
    cases fuel <;> simp_all [substituteDepth, substituteFuel, substituteAt]
  | head head =>
    cases fuel <;> simp_all [substituteDepth, substituteFuel, substituteAt]
  | pi domain body domainIH bodyIH
  | sigma domain body domainIH bodyIH =>
    cases fuel with
    | zero => simp [substituteDepth] at enough
    | succ fuel =>
      simp only [substituteDepth] at enough
      simp [substituteFuel, substituteAt, domainIH replacement index fuel (by omega),
        weakenFuel_complete replacement 0 fuel (by omega),
        bodyIH (weakenAt 0 replacement) (index + 1) fuel (by omega)]
  | id type left right typeIH leftIH rightIH =>
    cases fuel with
    | zero => simp [substituteDepth] at enough
    | succ fuel =>
      simp only [substituteDepth] at enough
      simp [substituteFuel, substituteAt, typeIH replacement index fuel (by omega),
        leftIH replacement index fuel (by omega), rightIH replacement index fuel (by omega)]
  | lam body bodyIH =>
    cases fuel with
    | zero => simp [substituteDepth] at enough
    | succ fuel =>
      simp only [substituteDepth] at enough
      simp [substituteFuel, substituteAt, weakenFuel_complete replacement 0 fuel (by omega),
        bodyIH (weakenAt 0 replacement) (index + 1) fuel (by omega)]
  | app left right leftIH rightIH
  | pair left right leftIH rightIH =>
    cases fuel with
    | zero => simp [substituteDepth] at enough
    | succ fuel =>
      simp only [substituteDepth] at enough
      simp [substituteFuel, substituteAt, leftIH replacement index fuel (by omega),
        rightIH replacement index fuel (by omega)]
  | fst term ih | snd term ih | refl term ih =>
    cases fuel with
    | zero => simp [substituteDepth] at enough
    | succ fuel =>
      simp only [substituteDepth] at enough
      simp [substituteFuel, substituteAt, ih replacement index fuel (by omega)]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
set_option linter.unusedSimpArgs false in
theorem execute_substitute_var (fuel index variableIndex : Nat) (replacement : RawTerm) :
    execute (fuel + 1)
      (substitute (encodeNat index) (encodeRaw replacement) (encodeRaw (.var variableIndex))) =
      resultPatterns (substituteFuel (fuel + 1) index replacement (.var variableIndex)) := by
  have lt := execute_indexLt fuel
  simp only [indexLt, accepted, zero] at lt
  cases variableIndex <;> unfold_binding_execution
  all_goals simp [List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    fold_encodeNat_succ, fold_encodeNat_zero, lt, substituteFuel,
    resultPatterns, Option.toList_bind, Function.comp_def, encodeRaw, encode,
    encodeNat_injective.eq_iff, mergeBindings, matchPattern, matchArgs,
    List.foldlM, bind, pure]
  case zero =>
    have zeroRight : lessAt fuel index 0 = false := by
      cases result : lessAt fuel index 0
      · rfl
      · have impossible := lessAt_sound result
        omega
    by_cases equal : index = 0
    · subst index
      simp [zeroRight, matchPattern, matchArgs, mergeBindings, encodeNat,
        List.foldlM, bind, pure, encodeRaw]
    · have different : encodeNat index ≠ Pattern.apply "prime-nat-zero" [] :=
        fun same => equal (encodeNat_injective same)
      by_cases low : lessAt fuel 0 index = true <;>
        simp [equal, Ne.symm equal, different, low, zeroRight, matchPattern, matchArgs,
          mergeBindings, encodeNat, List.foldlM, bind, pure, encodeRaw, encode]
  case succ predecessor =>
    by_cases equal : index = predecessor + 1
    · subst index
      have self : lessAt fuel (predecessor + 1) (predecessor + 1) = false := by
        cases result : lessAt fuel (predecessor + 1) (predecessor + 1)
        · rfl
        · exact False.elim (Nat.lt_irrefl _ (lessAt_sound result))
      simp [self, matchPattern, matchArgs, mergeBindings, List.foldlM,
        bind, pure, encodeRaw]
    · have different : encodeNat index ≠
          Pattern.apply "prime-nat-succ" [encodeNat predecessor] :=
        fun same => equal (encodeNat_injective same)
      by_cases low : lessAt fuel (predecessor + 1) index = true
      · have high : lessAt fuel index (predecessor + 1) = false := by
          cases result : lessAt fuel index (predecessor + 1)
          · rfl
          · have lower := lessAt_sound low
            have upper := lessAt_sound result
            omega
        simp [equal, Ne.symm equal, different, low, high, matchPattern, matchArgs,
          mergeBindings, List.foldlM, bind, pure, encodeRaw, encode, encodeNat]
      · by_cases high : lessAt fuel index (predecessor + 1) = true <;>
          simp [equal, Ne.symm equal, different, low, high, matchPattern, matchArgs,
            mergeBindings, List.foldlM, bind, pure, encodeRaw, encode, encodeNat]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
set_option linter.unusedSimpArgs false in
theorem execute_substitute (fuel index : Nat) (replacement term : RawTerm) :
    execute fuel (substitute (encodeNat index) (encodeRaw replacement) (encodeRaw term)) =
      resultPatterns (substituteFuel fuel index replacement term) := by
  induction fuel generalizing index replacement term with
  | zero => rfl
  | succ fuel ih =>
    have lt := execute_indexLt fuel
    have weak := execute_weaken fuel
    simp only [indexLt, accepted, zero] at lt
    simp only [weaken, encodeRaw] at weak
    simp only [substitute, encodeRaw] at ih
    cases term
    case var variableIndex => exact execute_substitute_var fuel index variableIndex replacement
    all_goals unfold_binding_execution
    all_goals simp only [ih, weak, lt, substituteFuel, resultPatterns]
    all_goals simp [List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
      fold_encodeNat_succ, fold_encodeNat_zero, ih, weak, lt,
      resultPatterns, Option.toList_bind, Function.comp_def, encodeRaw, encode,
      encodeNat_injective.eq_iff]

theorem execute_substitute_exact (index : Nat) (replacement term : RawTerm) (output : Pattern) :
    (∃ fuel, output ∈ execute fuel
      (substitute (encodeNat index) (encodeRaw replacement) (encodeRaw term))) ↔
      output = encodeRaw (substituteAt index replacement term) := by
  constructor
  · rintro ⟨fuel, member⟩
    rw [execute_substitute] at member
    simp only [resultPatterns, List.mem_map, Option.mem_toList] at member
    obtain ⟨raw, evidence, rfl⟩ := member
    rw [substituteFuel_sound evidence]
  · rintro rfl
    refine ⟨substituteDepth index replacement term, ?_⟩
    rw [execute_substitute, substituteFuel_complete term replacement index _ (by rfl)]
    simp [resultPatterns]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 3000000 in
set_option linter.unusedSimpArgs false in
theorem execute_beta_succ (fuel : Nat) (body argument : RawTerm) :
    execute (fuel + 1) (beta (encodeRaw (.app (.lam body) argument))) =
      execute fuel (substitute (encodeNat 0) (encodeRaw argument) (encodeRaw body)) := by
  unfold_binding_execution
  simp [List.map_flatMap]

theorem execute_beta_exact (body argument : RawTerm) (output : Pattern) :
    (∃ fuel, output ∈ execute fuel (beta (encodeRaw (.app (.lam body) argument)))) ↔
      output = encodeRaw (substituteAt 0 argument body) := by
  constructor
  · rintro ⟨fuel, member⟩
    cases fuel with
    | zero => cases member
    | succ fuel =>
      rw [execute_beta_succ] at member
      exact (execute_substitute_exact 0 argument body output).mp ⟨fuel, member⟩
  · intro target
    obtain ⟨fuel, member⟩ := (execute_substitute_exact 0 argument body output).mpr target
    exact ⟨fuel + 1, by simpa only [execute_beta_succ] using member⟩

/-- The computed substitution is exactly native scoped instantiation, not
generic `Pattern` binder substitution on its first-order encoding. -/
theorem intrinsic_beta_exact {n : Nat}
    (body : Presentation.Tower.Tm (n + 1)) (argument : Presentation.Tower.Tm n)
    (output : Pattern) :
    (∃ fuel, output ∈ execute fuel
      (beta (encodeTm towerHeadCodec (.app (.lam body) argument)))) ↔
      output = encodeTm towerHeadCodec (Presentation.inst0 argument body) := by
  have exact := execute_beta_exact (erase body) (erase argument) output
  simpa only [encodeRaw, ← DeclarationAwareErasureNaturality.erase_inst0,
    ← erase.eq_8, ← erase.eq_7, encode_erase] using exact

theorem intrinsic_beta_step_exact {n : Nat}
    (body : Presentation.Tower.Tm (n + 1)) (argument : Presentation.Tower.Tm n)
    (output : Pattern) :
    ContextualStep.Step (ContextualStep.engineBasePremises Engine.RelationEnv.empty)
      language (beta (encodeTm towerHeadCodec (.app (.lam body) argument))) output ↔
      output = encodeTm towerHeadCodec (Presentation.inst0 argument body) := by
  rw [← ContextualStep.exists_mem_rewriteAt_iff_step]
  exact intrinsic_beta_exact body argument output

theorem capture_avoiding_beta :
    ∃ fuel, encodeRaw (.lam (.var 1)) ∈ execute fuel
      (beta (encodeRaw (.app (.lam (.lam (.var 1))) (.var 0)))) := by
  apply (execute_beta_exact _ _ _).mpr
  rfl

theorem captured_variable_never_returned :
    ¬ ∃ fuel, encodeRaw (.lam (.var 0)) ∈ execute fuel
      (beta (encodeRaw (.app (.lam (.lam (.var 1))) (.var 0)))) := by
  rw [execute_beta_exact]
  decide

#print axioms execution_language_validate
#print axioms every_schema_oriented
#print axioms rule_names
#print axioms execute_indexLt
#print axioms indexLt_exact
#print axioms execute_weaken
#print axioms weakenFuel_sound
#print axioms weakenFuel_complete
#print axioms execute_weaken_exact
#print axioms intrinsic_weaken_exact
#print axioms substituteFuel_sound
#print axioms substituteFuel_complete
#print axioms execute_substitute
#print axioms execute_substitute_exact
#print axioms execute_beta_succ
#print axioms execute_beta_exact
#print axioms intrinsic_beta_exact
#print axioms intrinsic_beta_step_exact
#print axioms capture_avoiding_beta
#print axioms captured_variable_never_returned

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwareSubstitutionExecution
