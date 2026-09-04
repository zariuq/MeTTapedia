import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileQueryExact
import Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.PredFiniteSufficient

/-!
# Canonical codec for the PeTTa call-guard compiler language

The cold compiler `LanguageDef` operates on symbolic `Pattern`s, while its
independent reference machine operates on `CompileLanguageControl`.  This
module gives that representation boundary a complete structural decoder.

The raw decoder is intentionally tolerant because the shared binary-natural
decoder accepts representation aliases.  `compileControlCodec` is therefore
not the public identity boundary.  `canonicalCompileControlCodec` restricts
it to the exact image of `encodeCompileLanguageControl`; transition meaning
continues to come only from `compileLanguageStep?`.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Bindings

set_option autoImplicit false

/-! ## Structural decoders -/

def decodeDeclaration? : Pattern → Option ArrowDeclaration
  | .apply "petta-call-guard:declaration"
      [occurrence, function, inputs, output] => do
      let decodedOccurrence ← decodeNat? occurrence
      let decodedFunction ← decodeName? function
      let decodedInputs ← decodeTerms? inputs
      let decodedOutput ← decodeTerm? output
      pure {
        occurrence := decodedOccurrence
        function := decodedFunction
        inputTypes := decodedInputs
        outputType := decodedOutput }
  | _ => none

def decodeDeclarations? : Pattern → Option (List ArrowDeclaration)
  | .apply "petta-call-guard:declarations-nil" [] => some []
  | .apply "petta-call-guard:declarations-cons" [head, tail] => do
      let decodedHead ← decodeDeclaration? head
      let decodedTail ← decodeDeclarations? tail
      pure (decodedHead :: decodedTail)
  | _ => none

def decodeOwner? : Pattern → Option SpaceOwner
  | .apply "petta-call-guard:owner" [token] => do
      let decodedToken ← decodeNat? token
      pure ⟨decodedToken⟩
  | _ => none

def decodeArgMode? : Pattern → Option ArgMode
  | .apply "petta-call-guard:arg-raw" [] => some .rawAtom
  | .apply "petta-call-guard:arg-unchecked" [] => some .evalUnchecked
  | .apply "petta-call-guard:arg-checked" [expected] =>
      (decodeTerm? expected).map ArgMode.evalSoftcutType
  | _ => none

/-- Argument modes are encoded by a left fold of `snoc`; decoding therefore
reconstructs the authored order by appending the final mode. -/
def decodeArgModes? : Pattern → Option (List ArgMode)
  | .apply "petta-call-guard:arg-modes-nil" [] => some []
  | .apply "petta-call-guard:arg-modes-snoc" [modes, mode] => do
      let decodedModes ← decodeArgModes? modes
      let decodedMode ← decodeArgMode? mode
      pure (decodedModes ++ [decodedMode])
  | _ => none

def decodeResultMode? : Pattern → Option ResultMode
  | .apply "petta-call-guard:result-unchecked" [] =>
      some .resultUnchecked
  | .apply "petta-call-guard:result-checked" [expected] =>
      (decodeTerm? expected).map ResultMode.resultSoftcutType
  | _ => none

def decodePlan? : Pattern → Option GuardPlan
  | .apply "petta-call-guard:plan"
      [occurrence, modes, result, declaration] => do
      let decodedOccurrence ← decodeNat? occurrence
      let decodedModes ← decodeArgModes? modes
      let decodedResult ← decodeResultMode? result
      let decodedDeclaration ← decodeDeclaration? declaration
      pure {
        declarationOccurrence := decodedOccurrence
        argumentModes := decodedModes
        resultMode := decodedResult
        declaration := decodedDeclaration }
  | _ => none

/-- Plans use the same authored-order `snoc` representation as modes. -/
def decodePlans? : Pattern → Option (List GuardPlan)
  | .apply "petta-call-guard:plans-nil" [] => some []
  | .apply "petta-call-guard:plans-snoc" [plans, plan] => do
      let decodedPlans ← decodePlans? plans
      let decodedPlan ← decodePlan? plan
      pure (decodedPlans ++ [decodedPlan])
  | _ => none

def decodeFamily? : Pattern → Option CompiledGuardFamily
  | .apply "petta-call-guard:family"
      [owner, revision, head, arity, plans] => do
      let decodedOwner ← decodeOwner? owner
      let decodedRevision ← decodeNat? revision
      let decodedHead ← decodeName? head
      let decodedArity ← decodeNat? arity
      let decodedPlans ← decodePlans? plans
      pure {
        owner := decodedOwner
        revision := decodedRevision
        head := decodedHead
        arity := decodedArity
        plans := decodedPlans }
  | _ => none

def decodeCompilationResult? : Pattern → Option CompilationResult
  | .apply "petta-call-guard:compiled" [family] =>
      (decodeFamily? family).map CompilationResult.compiled
  | .apply "petta-call-guard:outside-fragment" [] =>
      some .outsideFragment
  | _ => none

/-- Tolerant structural decoder for the complete cold compiler carrier. -/
def decodeCompileLanguageControl? : Pattern → Option CompileLanguageControl
  | .apply "petta-call-guard:compile-running"
      [owner, revision, head, arity, remaining, accepted] => do
      let decodedOwner ← decodeOwner? owner
      let decodedRevision ← decodeNat? revision
      let decodedHead ← decodeName? head
      let decodedArity ← decodeNat? arity
      let decodedRemaining ← decodeDeclarations? remaining
      let decodedAccepted ← decodePlans? accepted
      pure (.running decodedOwner decodedRevision decodedHead decodedArity
        decodedRemaining decodedAccepted)
  | .apply "petta-call-guard:compile-arguments"
      [owner, revision, head, arity, declaration, remaining, inputCursor,
        modes, accepted] => do
      let decodedOwner ← decodeOwner? owner
      let decodedRevision ← decodeNat? revision
      let decodedHead ← decodeName? head
      let decodedArity ← decodeNat? arity
      let decodedDeclaration ← decodeDeclaration? declaration
      let decodedRemaining ← decodeDeclarations? remaining
      let decodedInputCursor ← decodeTerms? inputCursor
      let decodedModes ← decodeArgModes? modes
      let decodedAccepted ← decodePlans? accepted
      pure (.arguments decodedOwner decodedRevision decodedHead decodedArity
        decodedDeclaration decodedRemaining decodedInputCursor decodedModes
        decodedAccepted)
  | .apply "petta-call-guard:compile-result"
      [owner, revision, head, arity, declaration, remaining, modes,
        accepted] => do
      let decodedOwner ← decodeOwner? owner
      let decodedRevision ← decodeNat? revision
      let decodedHead ← decodeName? head
      let decodedArity ← decodeNat? arity
      let decodedDeclaration ← decodeDeclaration? declaration
      let decodedRemaining ← decodeDeclarations? remaining
      let decodedModes ← decodeArgModes? modes
      let decodedAccepted ← decodePlans? accepted
      pure (.result decodedOwner decodedRevision decodedHead decodedArity
        decodedDeclaration decodedRemaining decodedModes decodedAccepted)
  | .apply "petta-call-guard:compile-halted" [result] =>
      (decodeCompilationResult? result).map CompileLanguageControl.halted
  | _ => none

/-! ## Round trips -/

@[simp] theorem decodeDeclaration_encodeDeclaration
    (declaration : ArrowDeclaration) :
    decodeDeclaration? (encodeDeclaration declaration) = some declaration := by
  cases declaration
  simp [decodeDeclaration?, encodeDeclaration, declarationPattern, a]

@[simp] theorem decodeDeclarations_encodeDeclarations
    (declarations : List ArrowDeclaration) :
    decodeDeclarations? (encodeDeclarations declarations) = some declarations := by
  induction declarations with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [encodeDeclarations, declarationsCons, a, decodeDeclarations?,
        inductionHypothesis]

@[simp] theorem decodeOwner_encodeOwner (owner : SpaceOwner) :
    decodeOwner? (encodeOwner owner) = some owner := by
  cases owner
  simp [decodeOwner?, encodeOwner, ownerPattern, a]

@[simp] theorem decodeArgMode_encodeArgMode (mode : ArgMode) :
    decodeArgMode? (encodeArgMode mode) = some mode := by
  cases mode <;>
    simp [decodeArgMode?, encodeArgMode, rawArgMode, uncheckedArgMode,
      checkedArgMode, a]

@[simp] theorem decodeArgModes_encodeArgModes (modes : List ArgMode) :
    decodeArgModes? (encodeArgModes modes) = some modes := by
  induction modes using List.reverseRecOn with
  | nil => rfl
  | append_singleton modes mode inductionHypothesis =>
      simp [encodeArgModes_append_singleton, argModesSnoc, a,
        decodeArgModes?, inductionHypothesis]

@[simp] theorem decodeResultMode_encodeResultMode (mode : ResultMode) :
    decodeResultMode? (encodeResultMode mode) = some mode := by
  cases mode <;>
    simp [decodeResultMode?, encodeResultMode, uncheckedResultMode,
      checkedResultMode, a]

@[simp] theorem decodePlan_encodePlan (plan : GuardPlan) :
    decodePlan? (encodePlan plan) = some plan := by
  cases plan
  simp [decodePlan?, encodePlan, planPattern, a]

@[simp] theorem decodePlans_encodePlans (plans : List GuardPlan) :
    decodePlans? (encodePlans plans) = some plans := by
  induction plans using List.reverseRecOn with
  | nil => rfl
  | append_singleton plans plan inductionHypothesis =>
      simp [encodePlans_append_singleton, plansSnoc, a, decodePlans?,
        inductionHypothesis]

@[simp] theorem decodeFamily_encodeFamily (family : CompiledGuardFamily) :
    decodeFamily? (encodeFamily family) = some family := by
  cases family
  simp [decodeFamily?, encodeFamily, familyPattern, a]

@[simp] theorem decodeCompilationResult_encodeCompilationResult
    (result : CompilationResult) :
    decodeCompilationResult? (encodeCompilationResult result) = some result := by
  cases result <;>
    simp [decodeCompilationResult?, encodeCompilationResult, compiledPattern,
      outsideFragmentPattern, a]

@[simp] theorem decodeCompileLanguageControl_encode
    (control : CompileLanguageControl) :
    decodeCompileLanguageControl? (encodeCompileLanguageControl control) =
      some control := by
  cases control <;>
    simp [decodeCompileLanguageControl?, encodeCompileLanguageControl,
      compileRunning, compileArguments, compileResult, compileHalted, a]

theorem encodeTerm_injective : Function.Injective encodeTerm := by
  intro left right equal
  have decoded := congrArg decodeTerm? equal
  simpa using decoded

@[simp] theorem encodeNat_isMatchCorrectAux (value : Nat) :
    isMatchCorrectAux (encodeNat value) = true := by
  induction value using Nat.binaryRec' with
  | zero =>
      simp [encodeNat, natZero, a, isMatchCorrectAux,
        isMatchCorrectListAux]
  | bit bit value canonical inductionHypothesis =>
      rw [encodeNat, Nat.binaryRec'_eq _ _ canonical]
      cases bit
      · change isMatchCorrectAux (natBitZero (encodeNat value)) = true
        simpa [natBitZero, a, isMatchCorrectAux,
          isMatchCorrectListAux] using inductionHypothesis
      · change isMatchCorrectAux (natBitOne (encodeNat value)) = true
        simpa [natBitOne, a, isMatchCorrectAux,
          isMatchCorrectListAux] using inductionHypothesis

@[simp] theorem encodeChars_isMatchCorrectAux (characters : List Char) :
    isMatchCorrectAux (encodeChars characters) = true := by
  induction characters with
  | nil =>
      simp [encodeChars, charsNil, a, isMatchCorrectAux,
        isMatchCorrectListAux]
  | cons head tail inductionHypothesis =>
      simp [encodeChars, charsCons, charPattern, a, isMatchCorrectAux,
        isMatchCorrectListAux, inductionHypothesis]

@[simp] theorem encodeName_isMatchCorrectAux (name : String) :
    isMatchCorrectAux (encodeName name) = true := by
  simp [encodeName, namePattern, a, isMatchCorrectAux,
    isMatchCorrectListAux]

mutual
  @[simp] theorem encodeTerm_isMatchCorrectAux (term : Term) :
      isMatchCorrectAux (encodeTerm term) = true := by
    cases term <;>
      simp [encodeTerm, termVariable, termNumber, termString, termAtom,
        termList, a, isMatchCorrectAux, isMatchCorrectListAux,
        encodeTerms_isMatchCorrectAux]

  @[simp] theorem encodeTerms_isMatchCorrectAux (terms : List Term) :
      isMatchCorrectAux (encodeTerms terms) = true := by
    cases terms with
    | nil =>
        simp [encodeTerms, termsNil, a, isMatchCorrectAux,
          isMatchCorrectListAux]
    | cons head tail =>
        simp [encodeTerms, termsCons, a, isMatchCorrectAux,
          isMatchCorrectListAux, encodeTerm_isMatchCorrectAux,
          encodeTerms_isMatchCorrectAux]
end

theorem fixedInput_left_isMatchCorrect
    (ruleName : String) (fixedExpected : Term) (fixedMode : ArgMode) :
    Pattern.isMatchCorrect
        (inputStepTransition ruleName (encodeTerm fixedExpected)
          (encodeArgMode fixedMode) []).left = true := by
  simp [Pattern.isMatchCorrect, inputStepTransition, compileArguments,
    declarationPattern, termsCons, a, v, isMatchCorrectAux,
    isMatchCorrectListAux]

theorem fixedResult_left_isMatchCorrect
    (ruleName : String) (fixedExpected : Term) (fixedMode : ResultMode) :
    Pattern.isMatchCorrect
        (resultStepTransition ruleName (encodeTerm fixedExpected)
          (encodeResultMode fixedMode) []).left = true := by
  simp [Pattern.isMatchCorrect, resultStepTransition, compileResult,
    declarationPattern, a, v, isMatchCorrectAux, isMatchCorrectListAux]

/-! ## Closed canonical encodings -/

@[simp] theorem encodeDeclaration_closedSkeleton
    (declaration : ArrowDeclaration) :
    patternClosedSkeleton (encodeDeclaration declaration) = true := by
  cases declaration
  simp [encodeDeclaration, declarationPattern, a, patternClosedSkeleton,
    patternsClosedSkeleton, encodeNat_closedSkeleton,
    encodeName_closedSkeleton, encodeTerms_closedSkeleton,
    encodeTerm_closedSkeleton]

@[simp] theorem encodeDeclarations_closedSkeleton
    (declarations : List ArrowDeclaration) :
    patternClosedSkeleton (encodeDeclarations declarations) = true := by
  induction declarations with
  | nil =>
      simp [encodeDeclarations, declarationsNil, a, patternClosedSkeleton,
        patternsClosedSkeleton]
  | cons head tail inductionHypothesis =>
      simp [encodeDeclarations, declarationsCons, a, patternClosedSkeleton,
        patternsClosedSkeleton, inductionHypothesis]

@[simp] theorem encodeOwner_closedSkeleton (owner : SpaceOwner) :
    patternClosedSkeleton (encodeOwner owner) = true := by
  cases owner
  simp [encodeOwner, ownerPattern, a, patternClosedSkeleton,
    patternsClosedSkeleton, encodeNat_closedSkeleton]

@[simp] theorem encodeArgModes_closedSkeleton (modes : List ArgMode) :
    patternClosedSkeleton (encodeArgModes modes) = true := by
  induction modes using List.reverseRecOn with
  | nil =>
      simp [encodeArgModes, argModesNil, a, patternClosedSkeleton,
        patternsClosedSkeleton]
  | append_singleton modes mode inductionHypothesis =>
      simp [encodeArgModes_append_singleton, argModesSnoc, a,
        patternClosedSkeleton, patternsClosedSkeleton, inductionHypothesis]

@[simp] theorem encodePlan_closedSkeleton (plan : GuardPlan) :
    patternClosedSkeleton (encodePlan plan) = true := by
  cases plan
  simp [encodePlan, planPattern, a, patternClosedSkeleton,
    patternsClosedSkeleton, encodeNat_closedSkeleton,
    encodeArgModes_closedSkeleton, encodeResultMode_closedSkeleton,
    encodeDeclaration_closedSkeleton]

@[simp] theorem encodePlans_closedSkeleton (plans : List GuardPlan) :
    patternClosedSkeleton (encodePlans plans) = true := by
  induction plans using List.reverseRecOn with
  | nil =>
      simp [encodePlans, plansNil, a, patternClosedSkeleton,
        patternsClosedSkeleton]
  | append_singleton plans plan inductionHypothesis =>
      simp [encodePlans_append_singleton, plansSnoc, a,
        patternClosedSkeleton, patternsClosedSkeleton, inductionHypothesis]

@[simp] theorem encodeFamily_closedSkeleton (family : CompiledGuardFamily) :
    patternClosedSkeleton (encodeFamily family) = true := by
  cases family
  simp [encodeFamily, familyPattern, a, patternClosedSkeleton,
    patternsClosedSkeleton, encodeOwner_closedSkeleton,
    encodeNat_closedSkeleton, encodeName_closedSkeleton,
    encodePlans_closedSkeleton]

@[simp] theorem encodeCompilationResult_closedSkeleton
    (result : CompilationResult) :
    patternClosedSkeleton (encodeCompilationResult result) = true := by
  cases result <;>
    simp [encodeCompilationResult, compiledPattern, outsideFragmentPattern,
      a, patternClosedSkeleton, patternsClosedSkeleton,
      encodeFamily_closedSkeleton]

@[simp] theorem encodeCompileLanguageControl_closedSkeleton
    (control : CompileLanguageControl) :
    patternClosedSkeleton (encodeCompileLanguageControl control) = true := by
  cases control <;>
    simp [encodeCompileLanguageControl, compileRunning, compileArguments,
      compileResult, compileHalted, a, patternClosedSkeleton,
      patternsClosedSkeleton, encodeOwner_closedSkeleton,
      encodeNat_closedSkeleton, encodeName_closedSkeleton,
      encodeDeclaration_closedSkeleton, encodeDeclarations_closedSkeleton,
      encodeTerms_closedSkeleton, encodeArgModes_closedSkeleton,
      encodePlans_closedSkeleton, encodeCompilationResult_closedSkeleton]

private theorem closedSkeleton_ne_fvar {pattern : Pattern}
    (closed : patternClosedSkeleton pattern = true) (name : String) :
    pattern ≠ .fvar name := by
  intro equal
  subst pattern
  simp [patternClosedSkeleton] at closed

/-- A correct match against a known canonical instance recovers the exact
value of every source metavariable. -/
private theorem lookup_eq_of_applyBindings_eq
    {pattern : Pattern}
    (correct : Pattern.isMatchCorrect pattern = true)
    {bindings ambient : Bindings}
    (same : applyBindings bindings pattern = applyBindings ambient pattern)
    {name : String} {value : Pattern}
    (nameFree : name ∈ freeVars pattern)
    (ambientLookup : lookup ambient name = some value)
    (valueNotFree : value ≠ .fvar name) :
    lookup bindings name = some value := by
  have observed := applyBindings_injective_isMatchCorrect
    correct same name nameFree
  have rightObserved : lookupOrFvar ambient name = value := by
    unfold lookupOrFvar
    rw [Mettapedia.GSLT.LanguageDef.CertificateGSLT.applyBindings_fvar,
      ambientLookup]
    rfl
  cases actualLookup : lookup bindings name with
  | none =>
      have leftObserved : lookupOrFvar bindings name = .fvar name := by
        unfold lookupOrFvar
        rw [Mettapedia.GSLT.LanguageDef.CertificateGSLT.applyBindings_fvar,
          actualLookup]
        rfl
      exact False.elim (valueNotFree ((leftObserved.symm.trans
        (observed.trans rightObserved)).symm))
  | some actual =>
      have leftObserved : lookupOrFvar bindings name = actual := by
        unfold lookupOrFvar
        rw [Mettapedia.GSLT.LanguageDef.CertificateGSLT.applyBindings_fvar,
          actualLookup]
        rfl
      exact congrArg some (leftObserved.symm.trans
        (observed.trans rightObserved))

private theorem applyBindings_fvar_eq
    {bindings : Bindings} {name : String} {value : Pattern}
    (found : lookup bindings name = some value) :
    applyBindings bindings (.fvar name) = value := by
  rw [Mettapedia.GSLT.LanguageDef.CertificateGSLT.applyBindings_fvar, found]
  rfl

/-! ## Public exact-image boundary -/

/-- Complete but tolerant structural codec.  It is useful for ingress and for
local rule inversion, but its decoder image is intentionally not the public
identity boundary. -/
def compileControlCodec : PartialCodec CompileLanguageControl Pattern where
  encode := encodeCompileLanguageControl
  decode := decodeCompileLanguageControl?
  decode_encode := decodeCompileLanguageControl_encode

/-- Public compiler-control codec: accepted patterns are exactly canonical
encodings of reference controls. -/
def canonicalCompileControlCodec :
    PartialCodec CompileLanguageControl Pattern :=
  canonicalize compileControlCodec

@[simp] theorem canonical_decode_encode (control : CompileLanguageControl) :
    canonicalCompileControlCodec.decode
        (canonicalCompileControlCodec.encode control) = some control :=
  canonicalCompileControlCodec.decode_encode control

theorem encodeCompileLanguageControl_injective :
    Function.Injective encodeCompileLanguageControl :=
  compileControlCodec.encode_injective

/-- Exact-image characterization used by all later reflection theorems. -/
theorem canonical_decode_isSome_iff_image (wire : Pattern) :
    (canonicalCompileControlCodec.decode wire).isSome = true ↔
      ∃ control, encodeCompileLanguageControl control = wire := by
  exact decodeCanonical?_isSome_iff_exists_encode_eq compileControlCodec wire

theorem canonical_decode_eq_some_iff
    (wire : Pattern) (control : CompileLanguageControl) :
    canonicalCompileControlCodec.decode wire = some control ↔
      decodeCompileLanguageControl? wire = some control ∧
        encodeCompileLanguageControl control = wire := by
  exact decodeCanonical?_eq_some_iff compileControlCodec wire control

/-! ## Rule-local reflection -/

/-- The terminal compiler rule preserves every family coordinate and the
authored accepted-plan order. -/
theorem finish_rule_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) {initial final : Bindings} {target : Pattern}
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language finishTransition
        (encodeCompileLanguageControl
          (.running owner revision head arity [] accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        finishTransition.premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language finishTransition final = target) :
    target = encodeCompileLanguageControl
      (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩)) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have correct : Pattern.isMatchCorrect finishTransition.left = true := by
    decide
  have reconstructed := matchPattern_correct matched correct
  have structural := reconstructed
  simp [finishTransition, compileRunning, encodeCompileLanguageControl,
    encodeDeclarations, declarationsNil, a, v, applyBindings] at structural
  have finalEq : final = initial := by
    simpa [finishTransition,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv] using premises
  subst final
  rw [← targetEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    finishTransition, compileHalted, compiledPattern, familyPattern,
    applyBindings, structural, encodeCompileLanguageControl,
    encodeCompilationResult, encodeFamily]

private def runningDeclarationAmbient
    (owner revision head arity occurrence declarationHead inputs output
      remaining accepted : Pattern) : Bindings := [
  ("owner", owner), ("revision", revision), ("head", head),
  ("arity", arity), ("occurrence", occurrence),
  ("declarationHead", declarationHead), ("inputs", inputs),
  ("output", output), ("remaining", remaining), ("accepted", accepted)]

/-- Any successful application of the authored skip-head rule to a canonical
running state proves the independent head-inequality condition and reconstructs
the exact independent successor. -/
theorem skipHead_rule_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) {initial final : Bindings} {target : Pattern}
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language skipHeadTransition
        (encodeCompileLanguageControl
          (.running owner revision head arity (declaration :: remaining)
            accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        skipHeadTransition.premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language skipHeadTransition final = target) :
    declaration.function ≠ head ∧
      target = encodeCompileLanguageControl
        (.running owner revision head arity remaining accepted) := by
  let ambient := runningDeclarationAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName head) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodePlans accepted)
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have correct : Pattern.isMatchCorrect skipHeadTransition.left = true := by
    decide
  have reconstructed := matchPattern_correct matched correct
  have ambientReconstructed :
      applyBindings ambient skipHeadTransition.left =
        encodeCompileLanguageControl
          (.running owner revision head arity (declaration :: remaining)
            accepted) := by
    simp [ambient, runningDeclarationAmbient, skipHeadTransition,
      encodeCompileLanguageControl, compileRunning, encodeDeclarations,
      encodeDeclaration, declarationsCons, declarationPattern, a, v,
      applyBindings]
  have same : applyBindings initial skipHeadTransition.left =
      applyBindings ambient skipHeadTransition.left :=
    reconstructed.trans ambientReconstructed.symm
  have ownerLookup : lookup initial "owner" = some (encodeOwner owner) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipHeadTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeOwner_closedSkeleton owner) _
  have revisionLookup : lookup initial "revision" = some (encodeNat revision) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipHeadTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeNat_closedSkeleton revision) _
  have headLookup : lookup initial "head" = some (encodeName head) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipHeadTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeName_closedSkeleton head) _
  have arityLookup : lookup initial "arity" = some (encodeNat arity) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipHeadTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeNat_closedSkeleton arity) _
  have declarationHeadLookup : lookup initial "declarationHead" =
      some (encodeName declaration.function) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipHeadTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeName_closedSkeleton declaration.function) _
  have remainingLookup : lookup initial "remaining" =
      some (encodeDeclarations remaining) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipHeadTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeDeclarations_closedSkeleton remaining) _
  have acceptedLookup : lookup initial "accepted" =
      some (encodePlans accepted) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipHeadTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodePlans_closedSkeleton accepted) _
  have queryExact := premiseStep_notEqual_bound_eq initial
    "declarationHead" "head" declaration.function head
    declarationHeadLookup headLookup
  have different : declaration.function ≠ head := by
    intro equal
    have queryEmpty :
        premiseStepWithEnv relationEnv language initial
            (.relationQuery notEqualRelation
              [.fvar "declarationHead", .fvar "head"]) = [] := by
      rw [queryExact]
      simp [equal]
    simp [skipHeadTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, queryEmpty] at premises
  have querySuccess :
      premiseStepWithEnv relationEnv language initial
          (.relationQuery notEqualRelation
            [.fvar "declarationHead", .fvar "head"]) = [initial] := by
    rw [queryExact]
    simp [different]
  have finalEq : final = initial := by
    simpa [skipHeadTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, querySuccess] using premises
  subst final
  constructor
  · exact different
  · rw [← targetEq]
    simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
      skipHeadTransition, compileRunning, applyBindings,
      Mettapedia.GSLT.LanguageDef.CertificateGSLT.applyBindings_fvar,
      ownerLookup, revisionLookup, headLookup, arityLookup, remainingLookup,
      acceptedLookup, encodeCompileLanguageControl]

/-- Any successful application of the authored skip-arity rule to a canonical
running state proves both relevant coordinates of the independent branch and
reconstructs its exact successor. -/
theorem skipArity_rule_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) {initial final : Bindings} {target : Pattern}
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language skipArityTransition
        (encodeCompileLanguageControl
          (.running owner revision head arity (declaration :: remaining)
            accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        skipArityTransition.premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language skipArityTransition final = target) :
    declaration.function = head ∧
      declaration.inputTypes.length ≠ arity ∧
      target = encodeCompileLanguageControl
        (.running owner revision head arity remaining accepted) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have correct : Pattern.isMatchCorrect skipArityTransition.left = true := by
    decide
  have reconstructed := matchPattern_correct matched correct
  have structural := reconstructed
  simp [skipArityTransition, compileRunning, encodeCompileLanguageControl,
    encodeDeclarations, encodeDeclaration, declarationsCons,
    declarationPattern, a, v, applyBindings] at structural
  have atHead := structural.2.2.1
  have atDeclaration := structural.2.2.2.2.1.1.2.1
  have sameHead : declaration.function = head :=
    encodeName_injective (atDeclaration.symm.trans atHead)
  subst head
  let ambient := runningDeclarationAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName declaration.function) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodePlans accepted)
  have ambientReconstructed :
      applyBindings ambient skipArityTransition.left =
        encodeCompileLanguageControl
          (.running owner revision declaration.function arity
            (declaration :: remaining) accepted) := by
    simp [ambient, runningDeclarationAmbient, skipArityTransition,
      encodeCompileLanguageControl, compileRunning, encodeDeclarations,
      encodeDeclaration, declarationsCons, declarationPattern, a, v,
      applyBindings]
  have same : applyBindings initial skipArityTransition.left =
      applyBindings ambient skipArityTransition.left :=
    reconstructed.trans ambientReconstructed.symm
  have ownerLookup : lookup initial "owner" = some (encodeOwner owner) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipArityTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeOwner_closedSkeleton owner) _
  have revisionLookup : lookup initial "revision" = some (encodeNat revision) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipArityTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeNat_closedSkeleton revision) _
  have declarationHeadLookup : lookup initial "declarationHead" =
      some (encodeName declaration.function) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipArityTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeName_closedSkeleton declaration.function) _
  have arityLookup : lookup initial "arity" = some (encodeNat arity) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipArityTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeNat_closedSkeleton arity) _
  have inputsLookup : lookup initial "inputs" =
      some (encodeTerms declaration.inputTypes) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipArityTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeTerms_closedSkeleton declaration.inputTypes) _
  have remainingLookup : lookup initial "remaining" =
      some (encodeDeclarations remaining) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipArityTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeDeclarations_closedSkeleton remaining) _
  have acceptedLookup : lookup initial "accepted" =
      some (encodePlans accepted) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [skipArityTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodePlans_closedSkeleton accepted) _
  have queryExact := premiseStep_arityDiffers_bound_eq initial
    declaration.inputTypes arity inputsLookup arityLookup
  have differentArity : declaration.inputTypes.length ≠ arity := by
    intro equalArity
    have queryEmpty :
        premiseStepWithEnv relationEnv language initial
            (.relationQuery arityDiffersRelation
              [.fvar "inputs", .fvar "arity"]) = [] := by
      rw [queryExact]
      simp [equalArity]
    simp [skipArityTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, queryEmpty] at premises
  have querySuccess :
      premiseStepWithEnv relationEnv language initial
          (.relationQuery arityDiffersRelation
            [.fvar "inputs", .fvar "arity"]) = [initial] := by
    rw [queryExact]
    simp [differentArity]
  have finalEq : final = initial := by
    simpa [skipArityTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, querySuccess] using premises
  subst final
  refine ⟨rfl, differentArity, ?_⟩
  rw [← targetEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    skipArityTransition, compileRunning, applyBindings,
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.applyBindings_fvar,
    ownerLookup, revisionLookup, declarationHeadLookup, arityLookup,
    remainingLookup, acceptedLookup, encodeCompileLanguageControl]

/-- Any successful application of the authored begin-declaration rule to a
canonical running state proves relevance and reconstructs the exact argument
cursor chosen by the independent compiler. -/
theorem beginDeclaration_rule_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) {initial final : Bindings} {target : Pattern}
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language beginDeclarationTransition
        (encodeCompileLanguageControl
          (.running owner revision head arity (declaration :: remaining)
            accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        beginDeclarationTransition.premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language beginDeclarationTransition final = target) :
    declaration.function = head ∧
      declaration.inputTypes.length = arity ∧
      target = encodeCompileLanguageControl
        (.arguments owner revision head arity declaration remaining
          declaration.inputTypes [] accepted) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have correct : Pattern.isMatchCorrect beginDeclarationTransition.left = true := by
    decide
  have reconstructed := matchPattern_correct matched correct
  have structural := reconstructed
  simp [beginDeclarationTransition, compileRunning,
    encodeCompileLanguageControl, encodeDeclarations, encodeDeclaration,
    declarationsCons, declarationPattern, a, v, applyBindings] at structural
  have atHead := structural.2.2.1
  have atDeclaration := structural.2.2.2.2.1.1.2.1
  have sameHead : declaration.function = head :=
    encodeName_injective (atDeclaration.symm.trans atHead)
  subst head
  let ambient := runningDeclarationAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName declaration.function) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodePlans accepted)
  have ambientReconstructed :
      applyBindings ambient beginDeclarationTransition.left =
        encodeCompileLanguageControl
          (.running owner revision declaration.function arity
            (declaration :: remaining) accepted) := by
    simp [ambient, runningDeclarationAmbient, beginDeclarationTransition,
      encodeCompileLanguageControl, compileRunning, encodeDeclarations,
      encodeDeclaration, declarationsCons, declarationPattern, a, v,
      applyBindings]
  have same : applyBindings initial beginDeclarationTransition.left =
      applyBindings ambient beginDeclarationTransition.left :=
    reconstructed.trans ambientReconstructed.symm
  have ownerLookup : lookup initial "owner" = some (encodeOwner owner) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [beginDeclarationTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeOwner_closedSkeleton owner) _
  have revisionLookup : lookup initial "revision" = some (encodeNat revision) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [beginDeclarationTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeNat_closedSkeleton revision) _
  have declarationHeadLookup : lookup initial "declarationHead" =
      some (encodeName declaration.function) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [beginDeclarationTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeName_closedSkeleton declaration.function) _
  have arityLookup : lookup initial "arity" = some (encodeNat arity) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [beginDeclarationTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeNat_closedSkeleton arity) _
  have occurrenceLookup : lookup initial "occurrence" =
      some (encodeNat declaration.occurrence) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [beginDeclarationTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeNat_closedSkeleton declaration.occurrence) _
  have inputsLookup : lookup initial "inputs" =
      some (encodeTerms declaration.inputTypes) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [beginDeclarationTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeTerms_closedSkeleton declaration.inputTypes) _
  have outputLookup : lookup initial "output" =
      some (encodeTerm declaration.outputType) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [beginDeclarationTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeTerm_closedSkeleton declaration.outputType) _
  have remainingLookup : lookup initial "remaining" =
      some (encodeDeclarations remaining) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [beginDeclarationTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeDeclarations_closedSkeleton remaining) _
  have acceptedLookup : lookup initial "accepted" =
      some (encodePlans accepted) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [beginDeclarationTransition, compileRunning, declarationsCons,
        declarationPattern, freeVars, a, v]
    · simp [ambient, runningDeclarationAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodePlans_closedSkeleton accepted) _
  have queryExact := premiseStep_arityMatches_bound_eq initial
    declaration.inputTypes arity inputsLookup arityLookup
  have sameArity : declaration.inputTypes.length = arity := by
    by_contra differentArity
    have queryEmpty :
        premiseStepWithEnv relationEnv language initial
            (.relationQuery arityMatchesRelation
              [.fvar "inputs", .fvar "arity"]) = [] := by
      rw [queryExact]
      simp [differentArity]
    simp [beginDeclarationTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, queryEmpty] at premises
  have querySuccess :
      premiseStepWithEnv relationEnv language initial
          (.relationQuery arityMatchesRelation
            [.fvar "inputs", .fvar "arity"]) = [initial] := by
    rw [queryExact]
    simp [sameArity]
  have finalEq : final = initial := by
    simpa [beginDeclarationTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, querySuccess] using premises
  subst final
  refine ⟨rfl, sameArity, ?_⟩
  rw [← targetEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    beginDeclarationTransition, compileArguments, declarationPattern,
    argModesNil, applyBindings,
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.applyBindings_fvar,
    ownerLookup, revisionLookup, declarationHeadLookup, arityLookup,
    occurrenceLookup, inputsLookup, outputLookup, remainingLookup,
    acceptedLookup, encodeCompileLanguageControl, encodeDeclaration,
    encodeArgModes]

/-- The premise-free argument-completion rule cannot alter any declaration or
cursor coordinate while moving the independent compiler to result checking. -/
theorem argumentsFinished_rule_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    {initial final : Bindings} {target : Pattern}
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language argumentsFinishedTransition
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining [] modes
            accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        argumentsFinishedTransition.premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language argumentsFinishedTransition final = target) :
    target = encodeCompileLanguageControl
      (.result owner revision head arity declaration remaining modes
        accepted) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have correct : Pattern.isMatchCorrect argumentsFinishedTransition.left = true := by
    decide
  have reconstructed := matchPattern_correct matched correct
  have structural := reconstructed
  simp [argumentsFinishedTransition, compileArguments,
    encodeCompileLanguageControl, encodeDeclaration, encodeTerms,
    declarationPattern, termsNil, a, v, applyBindings] at structural
  have finalEq : final = initial := by
    simpa [argumentsFinishedTransition,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv] using premises
  subst final
  rw [← targetEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    argumentsFinishedTransition, compileResult, declarationPattern,
    applyBindings, structural, encodeCompileLanguageControl,
    encodeDeclaration]

private def argumentControlAmbient
    (owner revision head arity occurrence declarationHead inputs output
      remaining inputCursor modes accepted expected : Pattern) : Bindings := [
  ("owner", owner), ("revision", revision), ("head", head),
  ("arity", arity), ("occurrence", occurrence),
  ("declarationHead", declarationHead), ("inputs", inputs),
  ("output", output), ("remaining", remaining),
  ("inputCursor", inputCursor), ("modes", modes),
  ("accepted", accepted), ("expected", expected)]

/-- Shared reverse boundary for the three literal input-mode rules.  The rule
itself fixes the expected term and mode; a successful match therefore recovers
both rather than merely producing an extensionally equal target. -/
theorem fixedInput_rule_reflects
    (ruleName : String) (fixedExpected : Term) (fixedMode : ArgMode)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) {initial final : Bindings} {target : Pattern}
    (correct :
      Pattern.isMatchCorrect
          (inputStepTransition ruleName (encodeTerm fixedExpected)
            (encodeArgMode fixedMode) []).left = true)
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language
        (inputStepTransition ruleName (encodeTerm fixedExpected)
          (encodeArgMode fixedMode) [])
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (expected :: inputCursor) modes accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        (inputStepTransition ruleName (encodeTerm fixedExpected)
          (encodeArgMode fixedMode) []).premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language
          (inputStepTransition ruleName (encodeTerm fixedExpected)
            (encodeArgMode fixedMode) []) final = target) :
    expected = fixedExpected ∧
      target = encodeCompileLanguageControl
        (.arguments owner revision head arity declaration remaining inputCursor
          (modes ++ [fixedMode]) accepted) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have reconstructed := matchPattern_correct matched correct
  have structural := reconstructed
  simp [inputStepTransition, compileArguments, encodeCompileLanguageControl,
    encodeDeclaration, encodeTerms, declarationPattern, termsCons, a, v,
    applyBindings] at structural
  have expectedEncoded : encodeTerm fixedExpected = encodeTerm expected := by
    aesop
  have expectedEq : expected = fixedExpected :=
    encodeTerm_injective expectedEncoded.symm
  subst expected
  have finalEq : final = initial := by
    simpa [inputStepTransition,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv] using premises
  subst final
  constructor
  · rfl
  · rw [← targetEq]
    simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
      inputStepTransition, compileArguments, declarationPattern,
      argModesSnoc, applyBindings, structural, encodeCompileLanguageControl,
      encodeDeclaration, encodeArgModes_append_singleton]

/-- A successful checked-input rewrite is possible exactly when the
independent compiler constructs the soft-cut mode carried by that expected
type, and its target is the corresponding independent cursor. -/
theorem checkedInput_rule_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) {initial final : Bindings} {target : Pattern}
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language checkedInputTransition
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (expected :: inputCursor) modes accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        checkedInputTransition.premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language checkedInputTransition final = target) :
    compileArgMode expected = some (.evalSoftcutType expected) ∧
      target = encodeCompileLanguageControl
        (.arguments owner revision head arity declaration remaining inputCursor
          (modes ++ [.evalSoftcutType expected]) accepted) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have correct : Pattern.isMatchCorrect checkedInputTransition.left = true := by
    decide
  have reconstructed := matchPattern_correct matched correct
  have structural := reconstructed
  simp [checkedInputTransition, inputStepTransition, compileArguments,
    encodeCompileLanguageControl, encodeDeclaration, encodeTerms,
    declarationPattern, termsCons, a, v, applyBindings] at structural
  let ambient := argumentControlAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName head) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodeTerms inputCursor)
    (encodeArgModes modes) (encodePlans accepted) (encodeTerm expected)
  have ambientReconstructed :
      applyBindings ambient checkedInputTransition.left =
        encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (expected :: inputCursor) modes accepted) := by
    simp [ambient, argumentControlAmbient, checkedInputTransition,
      inputStepTransition, encodeCompileLanguageControl, compileArguments,
      encodeDeclaration, encodeTerms, declarationPattern, termsCons, a, v,
      applyBindings]
  have same : applyBindings initial checkedInputTransition.left =
      applyBindings ambient checkedInputTransition.left :=
    reconstructed.trans ambientReconstructed.symm
  have expectedLookup : lookup initial "expected" =
      some (encodeTerm expected) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [checkedInputTransition, inputStepTransition, compileArguments,
        declarationPattern, termsCons, freeVars, a, v]
    · simp [ambient, argumentControlAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeTerm_closedSkeleton expected) _
  have queryExact := premiseStep_checkedInput_bound_eq initial expected
    expectedLookup
  have checked :
      isCheckedArgumentClass (argumentModeClass (encodeTerm expected)) = true := by
    by_contra notChecked
    have queryEmpty :
        premiseStepWithEnv relationEnv language initial
            (.relationQuery checkedInputRelation [.fvar "expected"]) = [] := by
      rw [queryExact]
      simp [notChecked]
    simp [checkedInputTransition, inputStepTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, queryEmpty] at premises
  have compiled :
      compileArgMode expected = some (.evalSoftcutType expected) :=
    (checkedArgumentClass_encode_iff expected).mp checked
  have querySuccess :
      premiseStepWithEnv relationEnv language initial
          (.relationQuery checkedInputRelation [.fvar "expected"]) =
        [initial] := by
    rw [queryExact]
    simp [checked]
  have finalEq : final = initial := by
    simpa [checkedInputTransition, inputStepTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, querySuccess] using premises
  subst final
  refine ⟨compiled, ?_⟩
  rw [← targetEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    checkedInputTransition, inputStepTransition, compileArguments,
    declarationPattern, checkedArgMode, argModesSnoc, applyBindings, structural,
    encodeCompileLanguageControl, encodeDeclaration,
    encodeArgMode, encodeArgModes_append_singleton]

/-- The open-input rule is an all-or-decline branch: it fires exactly when the
independent argument compiler returns no mode, and its only target is the
explicit outside-fragment result. -/
theorem openInput_rule_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) {initial final : Bindings} {target : Pattern}
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language openInputTransition
        (encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (expected :: inputCursor) modes accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        openInputTransition.premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language openInputTransition final = target) :
    compileArgMode expected = none ∧
      target = encodeCompileLanguageControl (.halted .outsideFragment) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have correct : Pattern.isMatchCorrect openInputTransition.left = true := by
    decide
  have reconstructed := matchPattern_correct matched correct
  let ambient := argumentControlAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName head) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodeTerms inputCursor)
    (encodeArgModes modes) (encodePlans accepted) (encodeTerm expected)
  have ambientReconstructed :
      applyBindings ambient openInputTransition.left =
        encodeCompileLanguageControl
          (.arguments owner revision head arity declaration remaining
            (expected :: inputCursor) modes accepted) := by
    simp [ambient, argumentControlAmbient, openInputTransition,
      encodeCompileLanguageControl, compileArguments, encodeDeclaration,
      encodeTerms, declarationPattern, termsCons, a, v, applyBindings]
  have same : applyBindings initial openInputTransition.left =
      applyBindings ambient openInputTransition.left :=
    reconstructed.trans ambientReconstructed.symm
  have expectedLookup : lookup initial "expected" =
      some (encodeTerm expected) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [openInputTransition, compileArguments, declarationPattern,
        termsCons, freeVars, a, v]
    · simp [ambient, argumentControlAmbient, lookup]
    · exact closedSkeleton_ne_fvar (encodeTerm_closedSkeleton expected) _
  have queryExact := premiseStep_openInput_bound_eq initial expected
    expectedLookup
  have openClass : argumentModeClass (encodeTerm expected) = some none := by
    by_contra notOpen
    have queryEmpty :
        premiseStepWithEnv relationEnv language initial
            (.relationQuery openInputRelation [.fvar "expected"]) = [] := by
      rw [queryExact]
      simp [notOpen]
    simp [openInputTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, queryEmpty] at premises
  have compiled : compileArgMode expected = none :=
    (openArgumentClass_encode_iff expected).mp openClass
  have querySuccess :
      premiseStepWithEnv relationEnv language initial
          (.relationQuery openInputRelation [.fvar "expected"]) =
        [initial] := by
    rw [queryExact]
    simp [openClass]
  have finalEq : final = initial := by
    simpa [openInputTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, querySuccess] using premises
  subst final
  refine ⟨compiled, ?_⟩
  rw [← targetEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    openInputTransition, compileHalted, outsideFragmentPattern, a,
    applyBindings, encodeCompileLanguageControl, encodeCompilationResult]

private def resultControlAmbient
    (owner revision head arity occurrence declarationHead inputs output
      remaining modes accepted : Pattern) : Bindings := [
  ("owner", owner), ("revision", revision), ("head", head),
  ("arity", arity), ("occurrence", occurrence),
  ("declarationHead", declarationHead), ("inputs", inputs),
  ("output", output), ("remaining", remaining), ("modes", modes),
  ("accepted", accepted)]

/-- Shared reverse boundary for the three literal result-mode rules. -/
theorem fixedResult_rule_reflects
    (ruleName : String) (fixedExpected : Term) (fixedMode : ResultMode)
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    {initial final : Bindings} {target : Pattern}
    (correct :
      Pattern.isMatchCorrect
          (resultStepTransition ruleName (encodeTerm fixedExpected)
            (encodeResultMode fixedMode) []).left = true)
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language
        (resultStepTransition ruleName (encodeTerm fixedExpected)
          (encodeResultMode fixedMode) [])
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        (resultStepTransition ruleName (encodeTerm fixedExpected)
          (encodeResultMode fixedMode) []).premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language
          (resultStepTransition ruleName (encodeTerm fixedExpected)
            (encodeResultMode fixedMode) []) final = target) :
    declaration.outputType = fixedExpected ∧
      target = encodeCompileLanguageControl
        (.running owner revision head arity remaining
          (accepted ++ [{
            declarationOccurrence := declaration.occurrence
            argumentModes := modes
            resultMode := fixedMode
            declaration := declaration }])) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have reconstructed := matchPattern_correct matched correct
  have structural := reconstructed
  simp [resultStepTransition, compileResult, encodeCompileLanguageControl,
    encodeDeclaration, declarationPattern, a, v, applyBindings] at structural
  have outputEncoded : encodeTerm fixedExpected =
      encodeTerm declaration.outputType := by
    aesop
  have outputEq : declaration.outputType = fixedExpected :=
    encodeTerm_injective outputEncoded.symm
  subst fixedExpected
  have finalEq : final = initial := by
    simpa [resultStepTransition,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv] using premises
  subst final
  constructor
  · rfl
  · rw [← targetEq]
    simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
      resultStepTransition, compileRunning, declarationPattern, plansSnoc,
      planPattern, applyBindings, structural, encodeCompileLanguageControl,
      encodePlan, encodeDeclaration,
      encodePlans_append_singleton]

/-- A checked-result rewrite is exactly the successful soft-cut result-mode
branch of the independent compiler and appends exactly one authored plan. -/
theorem checkedResult_rule_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    {initial final : Bindings} {target : Pattern}
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language checkedResultTransition
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        checkedResultTransition.premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language checkedResultTransition final = target) :
    compileResultMode declaration.outputType =
        some (.resultSoftcutType declaration.outputType) ∧
      target = encodeCompileLanguageControl
        (.running owner revision head arity remaining
          (accepted ++ [{
            declarationOccurrence := declaration.occurrence
            argumentModes := modes
            resultMode := .resultSoftcutType declaration.outputType
            declaration := declaration }])) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have correct : Pattern.isMatchCorrect checkedResultTransition.left = true := by
    decide
  have reconstructed := matchPattern_correct matched correct
  have structural := reconstructed
  simp [checkedResultTransition, resultStepTransition, compileResult,
    encodeCompileLanguageControl, encodeDeclaration, declarationPattern,
    a, v, applyBindings] at structural
  let ambient := resultControlAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName head) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodeArgModes modes)
    (encodePlans accepted)
  have ambientReconstructed :
      applyBindings ambient checkedResultTransition.left =
        encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted) := by
    simp [ambient, resultControlAmbient, checkedResultTransition,
      resultStepTransition, encodeCompileLanguageControl, compileResult,
      encodeDeclaration, declarationPattern, a, v, applyBindings]
  have same : applyBindings initial checkedResultTransition.left =
      applyBindings ambient checkedResultTransition.left :=
    reconstructed.trans ambientReconstructed.symm
  have outputLookup : lookup initial "output" =
      some (encodeTerm declaration.outputType) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [checkedResultTransition, resultStepTransition, compileResult,
        declarationPattern, freeVars, a, v]
    · simp [ambient, resultControlAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeTerm_closedSkeleton declaration.outputType) _
  have queryExact := premiseStep_checkedResult_bound_eq initial
    declaration.outputType outputLookup
  have checked : isCheckedResultClass
      (resultModeClass (encodeTerm declaration.outputType)) = true := by
    by_contra notChecked
    have queryEmpty :
        premiseStepWithEnv relationEnv language initial
            (.relationQuery checkedResultRelation [.fvar "output"]) = [] := by
      rw [queryExact]
      simp [notChecked]
    simp [checkedResultTransition, resultStepTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, queryEmpty] at premises
  have compiled : compileResultMode declaration.outputType =
      some (.resultSoftcutType declaration.outputType) :=
    (checkedResultClass_encode_iff declaration.outputType).mp checked
  have querySuccess :
      premiseStepWithEnv relationEnv language initial
          (.relationQuery checkedResultRelation [.fvar "output"]) =
        [initial] := by
    rw [queryExact]
    simp [checked]
  have finalEq : final = initial := by
    simpa [checkedResultTransition, resultStepTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, querySuccess] using premises
  subst final
  refine ⟨compiled, ?_⟩
  rw [← targetEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    checkedResultTransition, resultStepTransition, compileRunning,
    declarationPattern, checkedResultMode, plansSnoc, planPattern,
    applyBindings, structural, encodeCompileLanguageControl, encodePlan,
    encodeResultMode, encodeDeclaration, encodePlans_append_singleton]

/-- The open-result rule is the exact result-compiler failure branch and
cannot manufacture a partial plan. -/
theorem openResult_rule_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    {initial final : Bindings} {target : Pattern}
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language openResultTransition
        (encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted)))
    (premises : final ∈
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relationEnv language
        openResultTransition.premises initial)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language openResultTransition final = target) :
    compileResultMode declaration.outputType = none ∧
      target = encodeCompileLanguageControl (.halted .outsideFragment) := by
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    at matched
  have correct : Pattern.isMatchCorrect openResultTransition.left = true := by
    decide
  have reconstructed := matchPattern_correct matched correct
  let ambient := resultControlAmbient (encodeOwner owner)
    (encodeNat revision) (encodeName head) (encodeNat arity)
    (encodeNat declaration.occurrence) (encodeName declaration.function)
    (encodeTerms declaration.inputTypes) (encodeTerm declaration.outputType)
    (encodeDeclarations remaining) (encodeArgModes modes)
    (encodePlans accepted)
  have ambientReconstructed :
      applyBindings ambient openResultTransition.left =
        encodeCompileLanguageControl
          (.result owner revision head arity declaration remaining modes
            accepted) := by
    simp [ambient, resultControlAmbient, openResultTransition,
      encodeCompileLanguageControl, compileResult, encodeDeclaration,
      declarationPattern, a, v, applyBindings]
  have same : applyBindings initial openResultTransition.left =
      applyBindings ambient openResultTransition.left :=
    reconstructed.trans ambientReconstructed.symm
  have outputLookup : lookup initial "output" =
      some (encodeTerm declaration.outputType) := by
    apply lookup_eq_of_applyBindings_eq correct same
    · simp [openResultTransition, compileResult, declarationPattern,
        freeVars, a, v]
    · simp [ambient, resultControlAmbient, lookup]
    · exact closedSkeleton_ne_fvar
        (encodeTerm_closedSkeleton declaration.outputType) _
  have queryExact := premiseStep_openResult_bound_eq initial
    declaration.outputType outputLookup
  have openClass : resultModeClass
      (encodeTerm declaration.outputType) = some none := by
    by_contra notOpen
    have queryEmpty :
        premiseStepWithEnv relationEnv language initial
            (.relationQuery openResultRelation [.fvar "output"]) = [] := by
      rw [queryExact]
      simp [notOpen]
    simp [openResultTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, queryEmpty] at premises
  have compiled : compileResultMode declaration.outputType = none :=
    (openResultClass_encode_iff declaration.outputType).mp openClass
  have querySuccess :
      premiseStepWithEnv relationEnv language initial
          (.relationQuery openResultRelation [.fvar "output"]) =
        [initial] := by
    rw [queryExact]
    simp [openClass]
  have finalEq : final = initial := by
    simpa [openResultTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      v, querySuccess] using premises
  subst final
  refine ⟨compiled, ?_⟩
  rw [← targetEq]
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    openResultTransition, compileHalted, outsideFragmentPattern, a,
    applyBindings, encodeCompileLanguageControl, encodeCompilationResult]

/-! ## State-family reflection -/

/-- Every authored language step from a canonical running state is exactly the
independent compiler's next step. -/
theorem running_step_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    {wire : Pattern}
    (step : Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
      relationEnv language
      (encodeCompileLanguageControl
        (.running owner revision head arity remaining accepted)) wire) :
    ∃ target, compileLanguageStep?
        (.running owner revision head arity remaining accepted) = some target ∧
      wire = encodeCompileLanguageControl target := by
  rw [language_step_iff_rootStep] at step
  obtain ⟨rule, ruleMember, initial, matched, final, premises, targetEq⟩ := step
  change rule ∈ transitions at ruleMember
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false]
    at ruleMember
  rcases ruleMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  · cases remaining with
    | nil =>
        have reflected := finish_rule_reflects owner revision head arity
          accepted matched premises targetEq
        refine ⟨.halted (.compiled ⟨owner, revision, head, arity, accepted⟩),
          ?_, reflected⟩
        rfl
    | cons declaration trailing =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [finishTransition, compileRunning, encodeCompileLanguageControl,
          encodeDeclarations, declarationsNil, declarationsCons, a,
          matchPattern, matchArgs] at matched
  · cases remaining with
    | nil =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [skipHeadTransition, compileRunning, encodeCompileLanguageControl,
          encodeDeclarations, declarationsNil, declarationsCons, a,
          matchPattern, matchArgs] at matched
    | cons declaration trailing =>
        have reflected := skipHead_rule_reflects owner revision head arity
          declaration trailing accepted matched premises targetEq
        refine ⟨.running owner revision head arity trailing accepted, ?_,
          reflected.2⟩
        simp [compileLanguageStep?, Relevant, reflected.1]
  · cases remaining with
    | nil =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [skipArityTransition, compileRunning, encodeCompileLanguageControl,
          encodeDeclarations, declarationsNil, declarationsCons, a,
          matchPattern, matchArgs] at matched
    | cons declaration trailing =>
        have reflected := skipArity_rule_reflects owner revision head arity
          declaration trailing accepted matched premises targetEq
        refine ⟨.running owner revision head arity trailing accepted, ?_,
          reflected.2.2⟩
        simp [compileLanguageStep?, Relevant, reflected.1, reflected.2.1]
  · cases remaining with
    | nil =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [beginDeclarationTransition, compileRunning,
          encodeCompileLanguageControl, encodeDeclarations, declarationsNil,
          declarationsCons, a, matchPattern, matchArgs] at matched
    | cons declaration trailing =>
        have reflected := beginDeclaration_rule_reflects owner revision head
          arity declaration trailing accepted matched premises targetEq
        refine ⟨.arguments owner revision head arity declaration trailing
          declaration.inputTypes [] accepted, ?_, reflected.2.2⟩
        simp [compileLanguageStep?, Relevant, reflected.1, reflected.2.1]
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [argumentsFinishedTransition, compileArguments, compileRunning,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [rawInputTransition, inputStepTransition, compileArguments,
      compileRunning, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [undefinedInputTransition, inputStepTransition, compileArguments,
      compileRunning, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [holeInputTransition, inputStepTransition, compileArguments,
      compileRunning, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [checkedInputTransition, inputStepTransition, compileArguments,
      compileRunning, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [openInputTransition, compileArguments, compileRunning,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [undefinedResultTransition, resultStepTransition, compileResult,
      compileRunning, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [holeResultTransition, resultStepTransition, compileResult,
      compileRunning, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [atomResultTransition, resultStepTransition, compileResult,
      compileRunning, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [checkedResultTransition, resultStepTransition, compileResult,
      compileRunning, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [openResultTransition, compileResult, compileRunning,
      encodeCompileLanguageControl, a, matchPattern] at matched

/-- Every authored language step from a canonical argument cursor is exactly
the independent compiler's next step. -/
theorem arguments_step_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) {wire : Pattern}
    (step : Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
      relationEnv language
      (encodeCompileLanguageControl
        (.arguments owner revision head arity declaration remaining
          inputCursor modes accepted)) wire) :
    ∃ target, compileLanguageStep?
        (.arguments owner revision head arity declaration remaining
          inputCursor modes accepted) = some target ∧
      wire = encodeCompileLanguageControl target := by
  rw [language_step_iff_rootStep] at step
  obtain ⟨rule, ruleMember, initial, matched, final, premises, targetEq⟩ := step
  change rule ∈ transitions at ruleMember
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false]
    at ruleMember
  rcases ruleMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [finishTransition, compileRunning, compileArguments,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [skipHeadTransition, compileRunning, compileArguments,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [skipArityTransition, compileRunning, compileArguments,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [beginDeclarationTransition, compileRunning, compileArguments,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · cases inputCursor with
    | nil =>
        have reflected := argumentsFinished_rule_reflects owner revision head
          arity declaration remaining modes accepted matched premises targetEq
        refine ⟨.result owner revision head arity declaration remaining modes
          accepted, ?_, reflected⟩
        rfl
    | cons expected trailing =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [argumentsFinishedTransition, compileArguments,
          encodeCompileLanguageControl, encodeTerms, termsNil, termsCons, a,
          matchPattern, matchArgs] at matched
  · cases inputCursor with
    | nil =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [rawInputTransition, inputStepTransition, compileArguments,
          encodeCompileLanguageControl, encodeTerms, termsNil, termsCons, a,
          matchPattern, matchArgs] at matched
    | cons expected trailing =>
        have reflected := fixedInput_rule_reflects
          "petta-call-guard-compile-input-raw" atomType .rawAtom owner revision
          head arity declaration remaining expected trailing modes accepted
          (fixedInput_left_isMatchCorrect _ _ _) matched premises targetEq
        refine ⟨.arguments owner revision head arity declaration remaining
          trailing (modes ++ [.rawAtom]) accepted, ?_, reflected.2⟩
        rw [reflected.1]
        rfl
  · cases inputCursor with
    | nil =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [undefinedInputTransition, inputStepTransition, compileArguments,
          encodeCompileLanguageControl, encodeTerms, termsNil, termsCons, a,
          matchPattern, matchArgs] at matched
    | cons expected trailing =>
        have reflected := fixedInput_rule_reflects
          "petta-call-guard-compile-input-undefined" undefinedType
          .evalUnchecked owner revision head arity declaration remaining
          expected trailing modes accepted
          (fixedInput_left_isMatchCorrect _ _ _) matched premises targetEq
        refine ⟨.arguments owner revision head arity declaration remaining
          trailing (modes ++ [.evalUnchecked]) accepted, ?_, reflected.2⟩
        rw [reflected.1]
        rfl
  · cases inputCursor with
    | nil =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [holeInputTransition, inputStepTransition, compileArguments,
          encodeCompileLanguageControl, encodeTerms, termsNil, termsCons, a,
          matchPattern, matchArgs] at matched
    | cons expected trailing =>
        have reflected := fixedInput_rule_reflects
          "petta-call-guard-compile-input-hole" holeType .evalUnchecked owner
          revision head arity declaration remaining expected trailing modes
          accepted (fixedInput_left_isMatchCorrect _ _ _) matched premises
          targetEq
        refine ⟨.arguments owner revision head arity declaration remaining
          trailing (modes ++ [.evalUnchecked]) accepted, ?_, reflected.2⟩
        rw [reflected.1]
        rfl
  · cases inputCursor with
    | nil =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [checkedInputTransition, inputStepTransition, compileArguments,
          encodeCompileLanguageControl, encodeTerms, termsNil, termsCons, a,
          matchPattern, matchArgs] at matched
    | cons expected trailing =>
        have reflected := checkedInput_rule_reflects owner revision head arity
          declaration remaining expected trailing modes accepted matched
          premises targetEq
        refine ⟨.arguments owner revision head arity declaration remaining
          trailing (modes ++ [.evalSoftcutType expected]) accepted, ?_,
          reflected.2⟩
        simp [compileLanguageStep?, reflected.1]
  · cases inputCursor with
    | nil =>
        rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
          at matched
        simp [openInputTransition, compileArguments, encodeCompileLanguageControl,
          encodeTerms, termsNil, termsCons, a, matchPattern, matchArgs]
          at matched
    | cons expected trailing =>
        have reflected := openInput_rule_reflects owner revision head arity
          declaration remaining expected trailing modes accepted matched
          premises targetEq
        refine ⟨.halted .outsideFragment, ?_, reflected.2⟩
        simp [compileLanguageStep?, reflected.1]
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [undefinedResultTransition, resultStepTransition, compileResult,
      compileArguments, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [holeResultTransition, resultStepTransition, compileResult,
      compileArguments, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [atomResultTransition, resultStepTransition, compileResult,
      compileArguments, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [checkedResultTransition, resultStepTransition, compileResult,
      compileArguments, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [openResultTransition, compileResult, compileArguments,
      encodeCompileLanguageControl, a, matchPattern] at matched

/-- Every authored language step from a canonical result cursor is exactly
the independent compiler's next step. -/
theorem result_step_reflects
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan) {wire : Pattern}
    (step : Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
      relationEnv language
      (encodeCompileLanguageControl
        (.result owner revision head arity declaration remaining modes
          accepted)) wire) :
    ∃ target, compileLanguageStep?
        (.result owner revision head arity declaration remaining modes
          accepted) = some target ∧
      wire = encodeCompileLanguageControl target := by
  rw [language_step_iff_rootStep] at step
  obtain ⟨rule, ruleMember, initial, matched, final, premises, targetEq⟩ := step
  change rule ∈ transitions at ruleMember
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false]
    at ruleMember
  rcases ruleMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [finishTransition, compileRunning, compileResult,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [skipHeadTransition, compileRunning, compileResult,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [skipArityTransition, compileRunning, compileResult,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [beginDeclarationTransition, compileRunning, compileResult,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [argumentsFinishedTransition, compileArguments, compileResult,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [rawInputTransition, inputStepTransition, compileArguments,
      compileResult, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [undefinedInputTransition, inputStepTransition, compileArguments,
      compileResult, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [holeInputTransition, inputStepTransition, compileArguments,
      compileResult, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [checkedInputTransition, inputStepTransition, compileArguments,
      compileResult, encodeCompileLanguageControl, a, matchPattern] at matched
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
    simp [openInputTransition, compileArguments, compileResult,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · have reflected := fixedResult_rule_reflects
      "petta-call-guard-compile-result-undefined" undefinedType
      .resultUnchecked owner revision head arity declaration remaining modes
      accepted (fixedResult_left_isMatchCorrect _ _ _) matched premises targetEq
    refine ⟨.running owner revision head arity remaining
      (accepted ++ [{
        declarationOccurrence := declaration.occurrence
        argumentModes := modes
        resultMode := .resultUnchecked
        declaration := declaration }]), ?_, reflected.2⟩
    simp [compileLanguageStep?, compileResultMode, reflected.1]
  · have reflected := fixedResult_rule_reflects
      "petta-call-guard-compile-result-hole" holeType .resultUnchecked owner
      revision head arity declaration remaining modes accepted
      (fixedResult_left_isMatchCorrect _ _ _) matched premises targetEq
    refine ⟨.running owner revision head arity remaining
      (accepted ++ [{
        declarationOccurrence := declaration.occurrence
        argumentModes := modes
        resultMode := .resultUnchecked
        declaration := declaration }]), ?_, reflected.2⟩
    simp [compileLanguageStep?, compileResultMode, reflected.1]
  · have reflected := fixedResult_rule_reflects
      "petta-call-guard-compile-result-atom" atomType .resultUnchecked owner
      revision head arity declaration remaining modes accepted
      (fixedResult_left_isMatchCorrect _ _ _) matched premises targetEq
    refine ⟨.running owner revision head arity remaining
      (accepted ++ [{
        declarationOccurrence := declaration.occurrence
        argumentModes := modes
        resultMode := .resultUnchecked
        declaration := declaration }]), ?_, reflected.2⟩
    simp [compileLanguageStep?, compileResultMode, reflected.1]
  · have reflected := checkedResult_rule_reflects owner revision head arity
      declaration remaining modes accepted matched premises targetEq
    refine ⟨.running owner revision head arity remaining
      (accepted ++ [{
        declarationOccurrence := declaration.occurrence
        argumentModes := modes
        resultMode := .resultSoftcutType declaration.outputType
        declaration := declaration }]), ?_, reflected.2⟩
    simp [compileLanguageStep?, reflected.1]
  · have reflected := openResult_rule_reflects owner revision head arity
      declaration remaining modes accepted matched premises targetEq
    refine ⟨.halted .outsideFragment, ?_, reflected.2⟩
    simp [compileLanguageStep?, reflected.1]

theorem halted_has_no_language_step
    (result : CompilationResult) {wire : Pattern}
    (step : Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
      relationEnv language
      (encodeCompileLanguageControl (.halted result)) wire) : False := by
  rw [language_step_iff_rootStep] at step
  obtain ⟨rule, ruleMember, initial, matched, final, premises, targetEq⟩ := step
  change rule ∈ transitions at ruleMember
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false]
    at ruleMember
  rcases ruleMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
      at matched
  · simp [finishTransition, compileRunning, compileHalted,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [skipHeadTransition, compileRunning, compileHalted,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [skipArityTransition, compileRunning, compileHalted,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [beginDeclarationTransition, compileRunning, compileHalted,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [argumentsFinishedTransition, compileArguments, compileHalted,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [rawInputTransition, inputStepTransition, compileArguments,
      compileHalted, encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [undefinedInputTransition, inputStepTransition, compileArguments,
      compileHalted, encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [holeInputTransition, inputStepTransition, compileArguments,
      compileHalted, encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [checkedInputTransition, inputStepTransition, compileArguments,
      compileHalted, encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [openInputTransition, compileArguments, compileHalted,
      encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [undefinedResultTransition, resultStepTransition, compileResult,
      compileHalted, encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [holeResultTransition, resultStepTransition, compileResult,
      compileHalted, encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [atomResultTransition, resultStepTransition, compileResult,
      compileHalted, encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [checkedResultTransition, resultStepTransition, compileResult,
      compileHalted, encodeCompileLanguageControl, a, matchPattern] at matched
  · simp [openResultTransition, compileResult, compileHalted,
      encodeCompileLanguageControl, a, matchPattern] at matched

/-- Canonical source-state reflection: the authored `LanguageDef` cannot take
any step other than the independent cold compiler's unique next step. -/
theorem language_step_reflects
    (source : CompileLanguageControl) {wire : Pattern}
    (step : Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
      relationEnv language (encodeCompileLanguageControl source) wire) :
    ∃ target, compileLanguageStep? source = some target ∧
      wire = encodeCompileLanguageControl target := by
  cases source with
  | running owner revision head arity remaining accepted =>
      exact running_step_reflects owner revision head arity remaining accepted
        step
  | arguments owner revision head arity declaration remaining inputCursor
      modes accepted =>
      exact arguments_step_reflects owner revision head arity declaration
        remaining inputCursor modes accepted step
  | result owner revision head arity declaration remaining modes accepted =>
      exact result_step_reflects owner revision head arity declaration
        remaining modes accepted step
  | halted result =>
      exact False.elim (halted_has_no_language_step result step)

/-- Exact one-step representation theorem on the canonical compiler image.
The forward direction reconstructs an independent target from an arbitrary
wire; the reverse direction is the already-proved authored completeness edge. -/
theorem language_step_iff_compileLanguageStep
    (source : CompileLanguageControl) (wire : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
        relationEnv language (encodeCompileLanguageControl source) wire ↔
      ∃ target, compileLanguageStep? source = some target ∧
        wire = encodeCompileLanguageControl target := by
  constructor
  · exact language_step_reflects source
  · rintro ⟨target, step, rfl⟩
    exact language_step_complete step

/-! ## Finite-path and terminal reflection -/

/-- Empty authored equations make the compiler language's exact reduction
compatible with its generated equation theory. -/
def languageReductionLaws :
    Mettapedia.GSLT.LanguageDef.TotalGSLT.ReductionRespectsEquationsUsing
      relationEnv language :=
  Mettapedia.GSLT.LanguageDef.TotalGSLT.ReductionRespectsEquationsUsing.of_equation_free
    relationEnv (by rfl)

/-- The ordinary authored compiler presentation regarded through the shared
`LanguageDef`-to-`GSLT` construction. -/
def compileLanguagePresentationGSLT : Mettapedia.GSLT.GSLT :=
  Mettapedia.GSLT.LanguageDef.TotalGSLT.languageGSLTUsing
    relationEnv language languageReductionLaws

/-- The canonical `E;R;E` presentation has exactly the authored compiler
steps because this language's equation theory is proved trivial.  All
finite-path arguments below cross this theorem rather than treating a raw
rewrite witness as a semantic GSLT step definitionally. -/
@[simp]
theorem compileLanguagePresentationGSLT_step_iff
    (source target : Pattern) :
    compileLanguagePresentationGSLT.Step source target ↔
      Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
        relationEnv language source target := by
  exact
    Mettapedia.GSLT.LanguageDef.TotalGSLT.languageGSLTUsing_step
      relationEnv language languageReductionLaws source target

/-- Every finite source-machine computation is represented by the authored
compiler presentation. -/
theorem language_multiStep_complete :
    ∀ {source target : CompileLanguageControl},
      compileLanguageGSLT.MultiStep source target →
        compileLanguagePresentationGSLT.MultiStep
          (encodeCompileLanguageControl source)
          (encodeCompileLanguageControl target)
  | _, _, .refl _ => .refl _
  | _, _, .step one rest =>
      .step
        ((compileLanguagePresentationGSLT_step_iff _ _).2
          (language_step_complete one))
        (language_multiStep_complete rest)

/-- Every finite authored computation from a canonical source reconstructs a
finite computation of the independent compiler machine and an exact canonical
target. -/
theorem language_multiStep_reflects :
    ∀ {source : CompileLanguageControl} {wire : Pattern},
      compileLanguagePresentationGSLT.MultiStep
          (encodeCompileLanguageControl source) wire →
        ∃ target,
          compileLanguageGSLT.MultiStep source target ∧
            wire = encodeCompileLanguageControl target := by
  intro source wire steps
  let motive : ∀ (first last : Pattern),
      compileLanguagePresentationGSLT.MultiStep first last → Prop :=
    fun first last _ => ∀ representedSource : CompileLanguageControl,
      first = encodeCompileLanguageControl representedSource →
        ∃ representedTarget,
          compileLanguageGSLT.MultiStep representedSource representedTarget ∧
            last = encodeCompileLanguageControl representedTarget
  refine Mettapedia.GSLT.GSLT.MultiStep.rec (motive := motive) ?_ ?_
    steps source rfl
  · intro term representedSource sourceExact
    subst term
    exact ⟨representedSource, .refl _, rfl⟩
  · intro first middle last firstStep _ inductionHypothesis
      representedSource sourceExact
    subst first
    obtain ⟨representedMiddle, sourceStep, middleExact⟩ :=
      language_step_reflects representedSource
        ((compileLanguagePresentationGSLT_step_iff _ _).1 firstStep)
    obtain ⟨representedTarget, targetSteps, lastExact⟩ :=
      inductionHypothesis representedMiddle middleExact
    exact ⟨representedTarget, .step sourceStep targetSteps, lastExact⟩

/-- Exact finite-path representation on the canonical compiler image. -/
theorem language_multiStep_iff_compileLanguageMultiStep
    (source : CompileLanguageControl) (wire : Pattern) :
    compileLanguagePresentationGSLT.MultiStep
        (encodeCompileLanguageControl source) wire ↔
      ∃ target,
        compileLanguageGSLT.MultiStep source target ∧
          wire = encodeCompileLanguageControl target := by
  constructor
  · exact language_multiStep_reflects
  · rintro ⟨target, steps, rfl⟩
    exact language_multiStep_complete steps

/-- A canonical compiler state is terminal in the authored presentation
exactly when the independent compiler state is halted. -/
theorem language_normal_iff_halted (source : CompileLanguageControl) :
    compileLanguagePresentationGSLT.IsNormalForm
        (encodeCompileLanguageControl source) ↔
      ∃ result, source = .halted result := by
  constructor
  · intro normal
    cases next : compileLanguageStep? source with
    | none =>
        exact (compileLanguageStep?_none_iff_halted source).1 next
    | some target =>
        exfalso
        exact normal ⟨encodeCompileLanguageControl target,
          (compileLanguagePresentationGSLT_step_iff _ _).2
            (language_step_complete next)⟩
  · rintro ⟨result, rfl⟩ redex
    obtain ⟨wire, step⟩ := redex
    exact halted_has_no_language_step result
      ((compileLanguagePresentationGSLT_step_iff _ _).1 step)

/-- The authored compiler presentation reaches the exact independently
specified compilation result. -/
theorem language_total_exact (owned : OwnedSnapshot) (head : String)
    (arity : Nat) :
    compileLanguagePresentationGSLT.MultiStep
      (encodeCompileLanguageControl (compileLanguageStart owned head arity))
      (encodeCompileLanguageControl
        (.halted (compileGuards owned head arity))) :=
  language_multiStep_complete
    (compileLanguageGSLT_total_exact owned head arity)

/-- A terminating authored run from the canonical start cannot invent a
different compilation result. -/
theorem language_halted_result_unique (owned : OwnedSnapshot) (head : String)
    (arity : Nat) (result : CompilationResult)
    (steps : compileLanguagePresentationGSLT.MultiStep
      (encodeCompileLanguageControl (compileLanguageStart owned head arity))
      (encodeCompileLanguageControl (.halted result))) :
    result = compileGuards owned head arity := by
  obtain ⟨target, sourceSteps, targetExact⟩ :=
    language_multiStep_reflects steps
  have haltedExact : target = .halted result :=
    (encodeCompileLanguageControl_injective targetExact).symm
  subst target
  exact (compileLanguageGSLT_multiStep_denote_preserved sourceSteps).symm.trans
    (compileLanguageStart_denote_exact owned head arity)

/-! ## Alias canary -/

/-- The tolerant binary decoder recognizes this noncanonical zero alias. -/
def aliasedZero : Pattern := natBitZero natZero

/-- A raw compiler state containing the alias decodes successfully. -/
def aliasedRunning : Pattern :=
  compileRunning (ownerPattern aliasedZero) aliasedZero (encodeName "f")
    aliasedZero declarationsNil plansNil

theorem tolerant_control_decoder_accepts_alias :
    decodeCompileLanguageControl? aliasedRunning =
      some (.running ⟨0⟩ 0 "f" 0 [] []) := by
  rfl

/-- Canonical decoding rejects the same alias because re-encoding yields the
unique binary zero representation. -/
theorem canonical_control_decoder_rejects_alias :
    canonicalCompileControlCodec.decode aliasedRunning = none := by
  rfl

#print axioms decodeCompileLanguageControl_encode
#print axioms encodeCompileLanguageControl_injective
#print axioms canonical_decode_isSome_iff_image
#print axioms canonical_decode_eq_some_iff
#print axioms encodeTerm_injective
#print axioms finish_rule_reflects
#print axioms skipHead_rule_reflects
#print axioms skipArity_rule_reflects
#print axioms beginDeclaration_rule_reflects
#print axioms argumentsFinished_rule_reflects
#print axioms fixedInput_rule_reflects
#print axioms checkedInput_rule_reflects
#print axioms openInput_rule_reflects
#print axioms fixedResult_rule_reflects
#print axioms checkedResult_rule_reflects
#print axioms openResult_rule_reflects
#print axioms running_step_reflects
#print axioms arguments_step_reflects
#print axioms result_step_reflects
#print axioms halted_has_no_language_step
#print axioms language_step_reflects
#print axioms language_step_iff_compileLanguageStep
#print axioms language_multiStep_complete
#print axioms language_multiStep_reflects
#print axioms language_multiStep_iff_compileLanguageMultiStep
#print axioms language_normal_iff_halted
#print axioms language_total_exact
#print axioms language_halted_result_unique
#print axioms tolerant_control_decoder_accepts_alias
#print axioms canonical_control_decoder_rejects_alias

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
