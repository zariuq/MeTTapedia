import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
import Mettapedia.GSLT.LanguageDef.CanonicalPartialCodec
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
  have headApplied := applyBindings_fvar_eq headLookup
  have declarationHeadApplied := applyBindings_fvar_eq declarationHeadLookup
  have different : declaration.function ≠ head := by
    intro equal
    have encodedEqual : encodeName declaration.function = encodeName head :=
      congrArg encodeName equal
    simp [skipHeadTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv,
      Mettapedia.OSLF.MeTTaIL.Engine.relationQueryStep, relationEnv,
      Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples,
      notEqualRelation, arityMatchesRelation, arityDiffersRelation,
      checkedInputRelation, openInputRelation, checkedResultRelation,
      openResultRelation, rowWhen,
      declarationHeadApplied, headApplied, encodedEqual, mergeBindings]
      at premises
  have finalEq : final = initial := by
    simp [skipHeadTransition, query,
      Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv,
      Mettapedia.OSLF.MeTTaIL.Engine.relationQueryStep, relationEnv,
      Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples,
      notEqualRelation, arityMatchesRelation, arityDiffersRelation,
      checkedInputRelation, openInputRelation, checkedResultRelation,
      openResultRelation, rowWhen,
      declarationHeadApplied, headApplied, declarationHeadLookup, headLookup,
      Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgs,
      Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgument,
      mergeBindings] at premises
    exact premises.2.symm
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
#print axioms skipHead_rule_reflects
#print axioms tolerant_control_decoder_accepts_alias
#print axioms canonical_control_decoder_rejects_alias

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
