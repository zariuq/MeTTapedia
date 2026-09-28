import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayComputedArgumentControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayUniverseModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedLambdaApplicationCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBetaPath

/-!
# Different retained domains consume the same computed universe program

At any finite nesting depth, the argument is a checked series of identity
applications rather than a variable. Lower and upper universe certificates
for the resulting pair-producing application have different retained
domains. The general qualified-application comparison obtains the needed
membership from the checked argument trees.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedApplicationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayComputedArgumentControls (program lowerCode raisedLowerCode upperCode
  lower_checked raised_lower_checked upper_checked lower_assembles raised_lower_assembles
  upper_assembles programMeaning iterated_value_of_member)
open ZFSetReplayApplicationComparisonControls (context contextCode context_checked context_assembles
  valid pairType body lowerFormation upperFormation lowerBodyCode upperBodyCode
  formationMeaning bodyMeaning)
open ZFSetDependentProducts (sigmaSet)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev familyLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev equalityJoined : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev lowerLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))
private abbrev upperLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def pairProgram (depth : Nat) : Tower.Tm 1 := .app (.lam body) (program depth)

def lowerApplicationCode (depth : Nat) : Replay 1 :=
  .appElim (.head zero) pairType (.lamIntro lowerLevel lowerFormation lowerBodyCode)
    (lowerCode depth)

def upperApplicationCode (depth : Nat) : Replay 1 :=
  .appElim (.head one) pairType (.lamIntro upperLevel upperFormation upperBodyCode)
    (upperCode depth)

/-- Depth zero recovers the existing variable-argument controls exactly. -/
theorem lower_zero_is_existing_code :
    lowerApplicationCode 0 = ZFSetReplayApplicationComparisonControls.lowerCode := rfl

theorem upper_zero_is_existing_code :
    upperApplicationCode 0 = ZFSetReplayApplicationComparisonControls.upperCode := rfl

theorem lower_application_checked (depth : Nat) :
    check Tower.rules noConversionCheck context (pairProgram depth) pairType
      (lowerApplicationCode depth) = true := by
  change ((true && check Tower.rules noConversionCheck context (program depth)
    (.head zero) (lowerCode depth)) && true) = true
  simpa only [Bool.true_and, Bool.and_true] using lower_checked depth

theorem upper_application_checked (depth : Nat) :
    check Tower.rules noConversionCheck context (pairProgram depth) pairType
      (upperApplicationCode depth) = true := by
  change ((true && check Tower.rules noConversionCheck context (program depth)
    (.head one) (upperCode depth)) && true) = true
  simpa only [Bool.true_and, Bool.and_true] using upper_checked depth

/-- Erasing the certificate of a computed argument is not an admissible
replacement, even when beta reduction will eventually return the variable. -/
theorem erased_computed_argument_rejected (depth : Nat) :
    check Tower.rules noConversionCheck context (pairProgram (depth + 1)) pairType
      (.appElim (.head zero) pairType
        (.lamIntro lowerLevel lowerFormation lowerBodyCode) (.var : Replay 1)) = false := by
  rfl

theorem lower_argument_qualified (depth : Nat) :
    (lowerCode depth).resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      contextCode (program depth) (.head zero) = true := by
  induction depth with
  | zero => decide
  | succ depth ih =>
      change (true && (true && (lowerCode depth).resultFormationsNeutral Tower.rules
        TowerDecisions.headTarget contextCode (program depth) (.head zero))) = true
      simp only [ih, Bool.true_and]

theorem upper_argument_qualified (depth : Nat) :
    (upperCode depth).resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      contextCode (program depth) (.head one) = true := by
  induction depth with
  | zero => decide
  | succ depth ih =>
      change (true && (true && (upperCode depth).resultFormationsNeutral Tower.rules
        TowerDecisions.headTarget contextCode (program depth) (.head one))) = true
      simp only [ih, Bool.true_and]

/-- Every lower-universe argument certificate carries a finite, exact
contraction path to the original context variable. -/
theorem lower_argument_path (depth : Nat) :
    QualifiedBetaPath Tower.rules TowerDecisions.headTarget contextCode (.head zero)
      (program depth) (lowerCode depth) (.var 0) .var := by
  induction depth with
  | zero => exact .terminal _ _ rfl
  | succ depth ih =>
      exact .contraction (lower_argument_qualified (depth + 1))
        (ZFSetReplayComputedArgumentControls.lower_contracts depth) ih

/-- The upper-universe route ends at the same raw variable but retains its
own cumulative terminal certificate. -/
theorem upper_argument_path (depth : Nat) :
    QualifiedBetaPath Tower.rules TowerDecisions.headTarget contextCode (.head one)
      (program depth) (upperCode depth) (.var 0) (.cumul zero .var) := by
  induction depth with
  | zero => exact .terminal _ _ rfl
  | succ depth ih =>
      exact .contraction (upper_argument_qualified (depth + 1))
        (ZFSetReplayComputedArgumentControls.upper_contracts depth) ih

theorem raised_lower_argument_qualified (depth : Nat) :
    (raisedLowerCode depth).resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      contextCode (program depth) (.head one) = true := by
  change (lowerCode depth).resultFormationsNeutral Tower.rules TowerDecisions.headTarget
    contextCode (program depth) (.head zero) = true
  exact lower_argument_qualified depth

/-- Cumulative promotion changes the displayed type and retained tree but
preserves the lower computation's exact path to the common variable. -/
theorem raised_lower_argument_path (depth : Nat) :
    QualifiedBetaPath Tower.rules TowerDecisions.headTarget contextCode (.head one)
      (program depth) (raisedLowerCode depth) (.var 0) (.cumul zero .var) := by
  induction depth with
  | zero => exact .terminal _ _ rfl
  | succ depth ih =>
      exact .contraction (raised_lower_argument_qualified (depth + 1))
        (by rfl) ih

/-- The computed program itself is consumed by a checked dependent equality
witness. The two certificates may differ, but both are checked at U₁; semantic
membership in that universe is proved from the actual valid input. -/
theorem computed_equality_witness_checks_and_inhabits (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    (CoherenceWitness.code two equalityJoined (.head one) .headType
      (raisedLowerCode depth) (upperCode depth)).resultFormation
      noConversionRename noConversionSubstitute TowerDecisions.headTarget contextCode
      (CoherenceWitness.term (program depth))
      (CoherenceWitness.type (.head one) (program depth)) =
        some (equalityJoined, CoherenceWitness.formation two .headType
          (raisedLowerCode depth) (upperCode depth)) ∧
    checkJudgment Tower.rules noConversionCheck context
      (CoherenceWitness.term (program depth))
      (CoherenceWitness.type (.head one) (program depth))
      contextCode (CoherenceWitness.code two equalityJoined (.head one) .headType
        (raisedLowerCode depth) (upperCode depth)) = true ∧
    ∃ witness formed,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (CoherenceWitness.code two equalityJoined (.head one) .headType
          (raisedLowerCode depth) (upperCode depth))
        (CoherenceWitness.term (program depth))
        (CoherenceWitness.type (.head one) (program depth)) = some witness ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (CoherenceWitness.formation two .headType (raisedLowerCode depth)
          (upperCode depth))
        (CoherenceWitness.type (.head one) (program depth)) (.head equalityJoined) =
          some formed ∧
      ∀ env, valid h env → witness.value env ∈ formed.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  let domain : Meaning.{u} 1 := .plain (fun _ => universeSet h ∅ 1)
  have domainChecked : check Tower.rules noConversionCheck context
      (.head one) (.head two) (.headType : Replay 1) = true := by decide
  have atDomain : assemble heads constants (.headType : Replay 1) (.head one)
      (.head two) = some domain := by rfl
  obtain ⟨extracted, checked, witness, formed, atWitness, atFormed, member⟩ :=
    qualified_paths_dependent_equality_witness heads constants Tower.rules
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
      (empty_constants_model heads constants) contextCode context_checked
      (context_assembles h constants) two equalityJoined (by decide) (by decide)
      (by decide) (.head one) (program depth) (.var 0) (.headType : Replay 1)
      (raisedLowerCode depth) (upperCode depth) (.cumul zero .var) (.cumul zero .var)
      domainChecked (raised_lower_checked depth) (upper_checked depth)
      (raised_lower_argument_path depth) (upper_argument_path depth)
      domain (programMeaning h 0 depth) (programMeaning h 1 depth)
      atDomain (raised_lower_assembles h constants depth) (upper_assembles h constants depth)
  refine ⟨extracted, checked, witness, formed, atWitness, atFormed, ?_⟩
  intro env admitted
  apply member env admitted
  change ZFSetReplayComputedArgumentControls.iteratedValue h 0 depth (env 0) ∈
    universeSet h ∅ 1
  rw [iterated_value_of_member h 0 depth (env 0) admitted.2]
  exact universeSet_subset_next h ∅ 0 admitted.2

/-- Outside the source context, the lower and upper computations can differ.
The corresponding dependent equality witness therefore fails semantic
membership, even though its structural checker tree is accepted. -/
theorem computed_equality_witness_invalid_input_rejected
    (h : CofinalInaccessibles.{u}) :
    let env : Environment.{u} 1 := fun _ => universeSet h ∅ 0
    (CoherenceWitness.termMeaning (programMeaning h 0 1)).value env ∉
      (CoherenceWitness.typeMeaning
        (.plain (fun _ => universeSet h ∅ 1) : Meaning.{u} 1)
        (programMeaning h 0 1) (programMeaning h 1 1)).value env := by
  exact CoherenceWitness.unequal_values_reject_witness _ _ _ _
    (ZFSetReplayComputedArgumentControls.invalid_input_distinguishes h)

/-- The positive side is inhabited: the concrete two-element code supplies
a valid input on which the checked computed equality witness belongs to its
exact extracted result formation. -/
theorem computed_equality_witness_two_code_input (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    let env : Environment.{u} 1 := fun _ => (twoCode h).1
    ∃ witness formed,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (CoherenceWitness.code two equalityJoined (.head one) .headType
          (raisedLowerCode depth) (upperCode depth))
        (CoherenceWitness.term (program depth))
        (CoherenceWitness.type (.head one) (program depth)) = some witness ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (CoherenceWitness.formation two .headType (raisedLowerCode depth)
          (upperCode depth))
        (CoherenceWitness.type (.head one) (program depth)) (.head equalityJoined) =
          some formed ∧
      witness.value env ∈ formed.value env := by
  obtain ⟨_, _, witness, formed, atWitness, atFormed, member⟩ :=
    computed_equality_witness_checks_and_inhabits h constants depth
  exact ⟨witness, formed, atWitness, atFormed, member _
    (ZFSetReplayApplicationComparisonControls.nonempty_input_valid h)⟩

/-- The existing checked lower and upper computations agree at every valid
environment by their actual beta paths, despite having different displayed
universe types. The common terminal variable is structural. -/
theorem computed_values_agree_via_qualified_paths (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat)
    (env : Environment.{u} 1) (admitted : valid h env) :
    (programMeaning h 0 depth).value env = (programMeaning h 1 depth).value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  exact qualified_paths_supported_terminal_values heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
    (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) contextCode
    (lower_argument_path depth) (upper_argument_path depth)
    context_checked (lower_checked depth) (upper_checked depth)
    (context_assembles h constants)
    (programMeaning h 0 depth) (programMeaning h 1 depth)
    (lower_assembles h constants depth) (upper_assembles h constants depth)
    rfl env admitted

/-- A dependent family whose domain is the computed image and whose second
component is an identity fibre over a point of that domain. -/
def proofCarryingImageFamily : Tower.Tm 1 :=
  .sigma (.var 0) (.id (.var 1) (.var 0) (.var 0))

theorem proofCarryingImageFamily_supported :
    ZFSetTypeExpressionInterpretation.supported proofCarryingImageFamily = true := by
  decide

def proofFamilySourceContext : Tower.Ctx 1 := .snoc .nil (.head one)
def proofFamilySourceContextCode : ContextCode Tower.Head NoConversion 1 :=
  .snoc .nil two .headType

theorem proofFamilySourceContext_checked :
    checkContext Tower.rules noConversionCheck proofFamilySourceContext
      proofFamilySourceContextCode = true := by
  decide

def proofCarryingImageFamilyCode : Replay 1 :=
  .sigmaForm one one .var (.idForm one .var .var .var)

/-- The dependent family itself has a checked formation at the joined level in a source
context whose variable is a U₁ code. This is separate from the two later
computed-image substitutions. -/
theorem proofCarryingImageFamily_checked :
    check Tower.rules noConversionCheck proofFamilySourceContext
      proofCarryingImageFamily (.head familyLevel) proofCarryingImageFamilyCode = true := by
  decide

theorem proofCarryingImageFamily_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      proofCarryingImageFamilyCode proofCarryingImageFamily (.head familyLevel) =
      some (.plain (fun env : Environment.{u} 1 =>
        sigmaSet (env 0) (fun point => truthCode (point = point)))) := by
  rfl

/-- The source family is instantiated with a computed term, not merely with
the terminal variable exposed by beta reduction. -/
def proofFamilyProgram (depth : Nat) : Sub Tower.Head 1 1 := fun _ => program depth

def lowerProofFamilyImages (depth : Nat) : Fin 1 → Replay 1 :=
  fun _ => raisedLowerCode depth

def upperProofFamilyImages (depth : Nat) : Fin 1 → Replay 1 :=
  fun _ => upperCode depth

def lowerComputedProofFamilyCode (depth : Nat) : Replay 1 :=
  proofCarryingImageFamilyCode.substitute noConversionRename noConversionSubstitute
    (proofFamilyProgram depth) (lowerProofFamilyImages depth)
    proofCarryingImageFamily (.head familyLevel)

def upperComputedProofFamilyCode (depth : Nat) : Replay 1 :=
  proofCarryingImageFamilyCode.substitute noConversionRename noConversionSubstitute
    (proofFamilyProgram depth) (upperProofFamilyImages depth)
    proofCarryingImageFamily (.head familyLevel)

theorem proofFamilyImages_checked (depth : Nat) :
    (∀ index : Fin 1,
      check Tower.rules noConversionCheck context (proofFamilyProgram depth index)
        (subst (proofFamilyProgram depth) (proofFamilySourceContext.lookup index))
        (lowerProofFamilyImages depth index) = true) ∧
    (∀ index : Fin 1,
      check Tower.rules noConversionCheck context (proofFamilyProgram depth index)
        (subst (proofFamilyProgram depth) (proofFamilySourceContext.lookup index))
        (upperProofFamilyImages depth index) = true) := by
  constructor
  · intro index
    fin_cases index
    simpa [proofFamilyProgram, lowerProofFamilyImages, proofFamilySourceContext,
      Ctx.lookup, subst, rename] using raised_lower_checked depth
  · intro index
    fin_cases index
    simpa [proofFamilyProgram, upperProofFamilyImages, proofFamilySourceContext,
      Ctx.lookup, subst, rename] using upper_checked depth

/-- Both distinct evidence trees really check the same computed family. -/
theorem computed_proof_family_formations_checked (depth : Nat) :
    check Tower.rules noConversionCheck context
      (subst (proofFamilyProgram depth) proofCarryingImageFamily)
      (.head familyLevel) (lowerComputedProofFamilyCode depth) = true ∧
    check Tower.rules noConversionCheck context
      (subst (proofFamilyProgram depth) proofCarryingImageFamily)
      (.head familyLevel) (upperComputedProofFamilyCode depth) = true := by
  constructor
  · apply check_substitute noConversionRename noConversionSubstitute Tower.rules
      noConversionCheck (fun _ impossible => nomatch impossible)
      (fun _ impossible => nomatch impossible) proofCarryingImageFamilyCode
      proofCarryingImageFamily_checked (proofFamilyProgram depth)
      (lowerProofFamilyImages depth)
    exact (proofFamilyImages_checked depth).1
  · apply check_substitute noConversionRename noConversionSubstitute Tower.rules
      noConversionCheck (fun _ impossible => nomatch impossible)
      (fun _ impossible => nomatch impossible) proofCarryingImageFamilyCode
      proofCarryingImageFamily_checked (proofFamilyProgram depth)
      (upperProofFamilyImages depth)
    exact (proofFamilyImages_checked depth).2

/-- Retain both independent checked paths for the computed image used by the
dependent family. Their Π-domains and displayed universe levels differ. -/
noncomputable def computedImagePaths (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    QualifiedImagePaths (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      Tower.rules TowerDecisions.headTarget context contextCode
      (programMeaning h 0 depth) (programMeaning h 1 depth) :=
  { leftDisplayed := .head zero
    rightDisplayed := .head one
    leftTerm := program depth
    rightTerm := program depth
    terminalTerm := .var 0
    leftCode := lowerCode depth
    rightCode := upperCode depth
    leftTerminal := .var
    rightTerminal := .cumul zero .var
    leftPath := lower_argument_path depth
    rightPath := upper_argument_path depth
    leftChecked := lower_checked depth
    rightChecked := upper_checked depth
    atLeft := lower_assembles h constants depth
    atRight := upper_assembles h constants depth
    terminalSupported := rfl }

/-- Every finite-depth computed input gives the same interpreted dependent
family under the lower and upper retained computation routes. The generic
image theorem reads their actual paths at the family's free variable. -/
theorem computed_proof_family_values_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat)
    (env : Environment.{u} 1) (admitted : valid h env) :
    ZFSetTypeExpressionInterpretation.interpret
      (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCarryingImageFamily
      proofCarryingImageFamily_supported
      (imageEnvironment (fun _ : Fin 1 => programMeaning h 0 depth) env) =
    ZFSetTypeExpressionInterpretation.interpret
      (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCarryingImageFamily
      proofCarryingImageFamily_supported
      (imageEnvironment (fun _ : Fin 1 => programMeaning h 1 depth) env) := by
  exact qualified_image_paths_supported_expression_values
    (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model _ constants) contextCode context_checked
    (context_assembles h constants) proofCarryingImageFamily
    proofCarryingImageFamily_supported
    (fun _ : Fin 1 => programMeaning h 0 depth)
    (fun _ : Fin 1 => programMeaning h 1 depth)
    (fun _ _ => computedImagePaths h constants depth) env admitted

/-- The two generated formation certificates are independently assembled.
Their meanings agree on valid environments because their checked image paths
converge at the only free variable of the source family. -/
theorem checked_computed_proof_family_meanings_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ left right,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerComputedProofFamilyCode depth)
        (subst (proofFamilyProgram depth) proofCarryingImageFamily)
        (.head familyLevel) = some left ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (upperComputedProofFamilyCode depth)
        (subst (proofFamilyProgram depth) proofCarryingImageFamily)
        (.head familyLevel) = some right ∧
      (∀ env, left.value env =
        ZFSetTypeExpressionInterpretation.interpret
          (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCarryingImageFamily
          proofCarryingImageFamily_supported
          (imageEnvironment (fun _ : Fin 1 => programMeaning h 0 depth) env)) ∧
      (∀ env, right.value env =
        ZFSetTypeExpressionInterpretation.interpret
          (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCarryingImageFamily
          proofCarryingImageFamily_supported
          (imageEnvironment (fun _ : Fin 1 => programMeaning h 1 depth) env)) ∧
      ∀ env, valid h env → left.value env = right.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  let sourceMeaning : Meaning 1 :=
    .plain (fun env => sigmaSet (env 0) (fun point => truthCode (point = point)))
  have lowerChecks := (proofFamilyImages_checked depth).1
  have upperChecks := (proofFamilyImages_checked depth).2
  have lowerImages : ∀ index : Fin 1,
      assemble heads constants (lowerProofFamilyImages depth index)
        (proofFamilyProgram depth index)
        (subst (proofFamilyProgram depth) (proofFamilySourceContext.lookup index)) =
          some (programMeaning h 0 depth) := by
    intro index
    fin_cases index
    simpa [heads, proofFamilyProgram, lowerProofFamilyImages,
      proofFamilySourceContext, Ctx.lookup, subst, rename] using
      raised_lower_assembles h constants depth
  have upperImages : ∀ index : Fin 1,
      assemble heads constants (upperProofFamilyImages depth index)
        (proofFamilyProgram depth index)
        (subst (proofFamilyProgram depth) (proofFamilySourceContext.lookup index)) =
          some (programMeaning h 1 depth) := by
    intro index
    fin_cases index
    simpa [heads, proofFamilyProgram, upperProofFamilyImages,
      proofFamilySourceContext, Ctx.lookup, subst, rename] using
      upper_assembles h constants depth
  obtain ⟨_, _, left, right, atLeft, atRight, leftValues, rightValues, equalValues⟩ :=
    qualified_image_paths_checked_substituted_family_values heads constants Tower.rules
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
      (empty_constants_model heads constants) contextCode context_checked
      (context_assembles h constants) proofCarryingImageFamilyCode
      proofCarryingImageFamily_supported proofCarryingImageFamily_checked
      sourceMeaning (proofCarryingImageFamily_assembles h constants)
      (proofFamilyProgram depth) (lowerProofFamilyImages depth)
      (upperProofFamilyImages depth)
      (fun _ : Fin 1 => programMeaning h 0 depth)
      (fun _ : Fin 1 => programMeaning h 1 depth)
      lowerChecks upperChecks lowerImages upperImages
      (fun _ _ => computedImagePaths h constants depth)
  exact ⟨left, right, atLeft, atRight, leftValues, rightValues, equalValues⟩

/-- Any member of the computed input receives reflexivity evidence in the
same dependent family on both independently checked computation routes. -/
theorem computed_proof_family_member (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat)
    (env : Environment.{u} 1) (admitted : valid h env)
    (point : ZFSet.{u}) (inside : point ∈ (programMeaning h 0 depth).value env) :
    ZFSet.pair point ∅ ∈
      ZFSetTypeExpressionInterpretation.interpret
        (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCarryingImageFamily
        proofCarryingImageFamily_supported
        (imageEnvironment (fun _ : Fin 1 => programMeaning h 0 depth) env) ∧
    ZFSet.pair point ∅ ∈
      ZFSetTypeExpressionInterpretation.interpret
        (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCarryingImageFamily
        proofCarryingImageFamily_supported
        (imageEnvironment (fun _ : Fin 1 => programMeaning h 1 depth) env) := by
  have leftMember : ZFSet.pair point ∅ ∈
      ZFSetTypeExpressionInterpretation.interpret
        (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCarryingImageFamily
        proofCarryingImageFamily_supported
        (imageEnvironment (fun _ : Fin 1 => programMeaning h 0 depth) env) := by
    change ZFSet.pair point ∅ ∈ sigmaSet ((programMeaning h 0 depth).value env)
      (fun candidate => truthCode (candidate = candidate))
    exact ZFSetDependentProducts.mem_sigmaSet.mpr
      ⟨point, inside, ∅, (mem_truthCode _ _).mpr ⟨rfl, rfl⟩, rfl⟩
  refine ⟨leftMember, ?_⟩
  rw [← computed_proof_family_values_agree h constants depth env admitted]
  exact leftMember

/-- A computed point and its reflexivity witness inhabit both actually
checked and assembled formations. The two certificates are retained rather
than reconstructed from the common erased family expression. -/
theorem checked_computed_proof_family_member (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat)
    (env : Environment.{u} 1) (admitted : valid h env)
    (point : ZFSet.{u}) (inside : point ∈ (programMeaning h 0 depth).value env) :
    ∃ left right,
      check Tower.rules noConversionCheck context
        (subst (proofFamilyProgram depth) proofCarryingImageFamily)
        (.head familyLevel) (lowerComputedProofFamilyCode depth) = true ∧
      check Tower.rules noConversionCheck context
        (subst (proofFamilyProgram depth) proofCarryingImageFamily)
        (.head familyLevel) (upperComputedProofFamilyCode depth) = true ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerComputedProofFamilyCode depth)
        (subst (proofFamilyProgram depth) proofCarryingImageFamily)
        (.head familyLevel) = some left ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (upperComputedProofFamilyCode depth)
        (subst (proofFamilyProgram depth) proofCarryingImageFamily)
        (.head familyLevel) = some right ∧
      left.value env = right.value env ∧
      ZFSet.pair point ∅ ∈ left.value env ∧
      ZFSet.pair point ∅ ∈ right.value env := by
  obtain ⟨left, right, atLeft, atRight, leftValues, rightValues, equalValues⟩ :=
    checked_computed_proof_family_meanings_agree h constants depth
  obtain ⟨leftMember, rightMember⟩ :=
    computed_proof_family_member h constants depth env admitted point inside
  refine ⟨left, right, (computed_proof_family_formations_checked depth).1,
    (computed_proof_family_formations_checked depth).2,
    atLeft, atRight, equalValues env admitted, ?_, ?_⟩
  · rw [leftValues]
    exact leftMember
  · rw [rightValues]
    exact rightMember

/-- A computed program cannot be substituted using the terminal variable's
certificate; replay checks the actual unreduced input. -/
theorem erased_proof_family_image_rejected (depth : Nat) :
    check Tower.rules noConversionCheck context (program (depth + 1))
      (.head one) (.cumul zero (.var : Replay 1)) = false := by
  rfl

/-- At the inhabited two-element-code input, the interpreted dependent
family contains an actual pair of a point and reflexivity evidence on both
independently checked computed-image routes. -/
theorem computed_proof_family_two_code_member (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    let env : Environment.{u} 1 := fun _ => (twoCode h).1
    ZFSet.pair (∅ : ZFSet.{u}) ∅ ∈
      ZFSetTypeExpressionInterpretation.interpret
        (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCarryingImageFamily
        proofCarryingImageFamily_supported
        (imageEnvironment (fun _ : Fin 1 => programMeaning h 0 depth) env) ∧
    ZFSet.pair (∅ : ZFSet.{u}) ∅ ∈
      ZFSetTypeExpressionInterpretation.interpret
        (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants proofCarryingImageFamily
        proofCarryingImageFamily_supported
        (imageEnvironment (fun _ : Fin 1 => programMeaning h 1 depth) env) := by
  let env : Environment.{u} 1 := fun _ => (twoCode h).1
  have inputValue : (programMeaning h 0 depth).value env = (twoCode h).1 := by
    exact iterated_value_of_member h 0 depth (twoCode h).1 (twoCode h).2
  apply computed_proof_family_member h constants depth env
    (ZFSetReplayApplicationComparisonControls.nonempty_input_valid h)
    ∅
  rw [inputValue]
  exact ZFSetDependentProducts.Controls.empty_mem_two

theorem lower_formation_checked :
    check Tower.rules noConversionCheck context (.pi (.head zero) pairType)
      (.head lowerLevel) lowerFormation = true := by decide

theorem upper_formation_checked :
    check Tower.rules noConversionCheck context (.pi (.head one) pairType)
      (.head upperLevel) upperFormation = true := by decide

/-- At every finite depth, two accepted certificates with distinct retained
domains give equal values to the same computed, pair-producing application.
The general cross-domain theorem derives the body relation from the supported
raw body; qualified finite beta paths compare the computed arguments, and
each argument's own typing tree supplies membership in its retained domain. -/
theorem computed_pair_values_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ lower upper : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerApplicationCode depth) (pairProgram depth) pairType = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (upperApplicationCode depth) (pairProgram depth) pairType = some upper ∧
      ∀ env : Environment.{u} 1, valid h env → lower.value env = upper.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  have bodySupported : ZFSetTypeExpressionInterpretation.supported body = true := by decide
  exact qualified_cross_domain_lambda_applications_coherent heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) context contextCode context_checked
    (context_assembles h constants) (.head zero) (.head one) pairType pairType body
    lowerLevel upperLevel lowerFormation upperFormation (lowerCode depth)
    (upperCode depth) lowerBodyCode upperBodyCode (program depth) (program depth)
    (.var 0) .var (.cumul zero .var) (lower_application_checked depth)
    (upper_application_checked depth) (lower_argument_qualified depth)
    (upper_argument_qualified depth) (lower_argument_path depth)
    (upper_argument_path depth) rfl bodySupported

/-- The valid-context premise of computed application comparison is real:
at an input outside the lower universe, the two checked applications retain
different meanings even though both return a pair. -/
theorem computed_pair_invalid_input_values_differ (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    let env : Environment.{u} 1 := fun _ => universeSet h ∅ 0
    ∃ lower upper : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerApplicationCode 1) (pairProgram 1) pairType = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (upperApplicationCode 1) (pairProgram 1) pairType = some upper ∧
      ¬ valid h env ∧ lower.value env ≠ upper.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  let env : Environment.{u} 1 := fun _ => universeSet h ∅ 0
  obtain ⟨invalid, lowerInput, upperInput⟩ :=
    ZFSetReplayComputedArgumentControls.invalid_input_values h
  obtain ⟨lower, atLower, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck (lowerApplicationCode 1) (lower_application_checked 1)
  obtain ⟨upper, atUpper, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck (upperApplicationCode 1) (upper_application_checked 1)
  have lowerInside : (programMeaning h 0 1).value env ∈ universeSet h ∅ 0 := by
    rw [lowerInput]
    exact seed_mem_zero h ∅
  have upperInside : (programMeaning h 1 1).value env ∈ universeSet h ∅ 1 := by
    rw [upperInput]
    exact universeSet_mem_next h ∅ 0
  have lowerValue : lower.value env =
      ZFSet.pair ((programMeaning h 0 1).value env) ∅ := by
    rw [application_lambda_value heads constants lowerLevel (.head zero) pairType body
      (program 1) lowerFormation (lowerCode 1) lowerBodyCode
      (formationMeaning h 0) (programMeaning h 0 1) lower bodyMeaning
      (fun _ => universeSet h ∅ 0) rfl rfl rfl (lower_assembles h constants 1)
      atLower env lowerInside]
    rfl
  have upperValue : upper.value env =
      ZFSet.pair ((programMeaning h 1 1).value env) ∅ := by
    rw [application_lambda_value heads constants upperLevel (.head one) pairType body
      (program 1) upperFormation (upperCode 1) upperBodyCode
      (formationMeaning h 1) (programMeaning h 1 1) upper bodyMeaning
      (fun _ => universeSet h ∅ 1) rfl rfl rfl (upper_assembles h constants 1)
      atUpper env upperInside]
    rfl
  refine ⟨lower, upper, atLower, atUpper, invalid, ?_⟩
  rw [lowerValue, upperValue, lowerInput, upperInput]
  intro equal
  have first := (ZFSet.pair_inj.mp equal).1
  have member := seed_mem_zero h (∅ : ZFSet.{u})
  rw [← first] at member
  exact ZFSet.notMem_empty _ member

/-- The compared result is not merely equal across certificates: it returns
the computed input in the first projection and a reflexivity witness in the
dependent second fibre. -/
theorem lower_result_computes (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) (result : Meaning.{u} 1)
    (atResult : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (lowerApplicationCode depth) (pairProgram depth) pairType = some result)
    (env : Environment.{u} 1) (admitted : valid h env) :
    result.value env = ZFSet.pair (env 0) ∅ := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  have inside := qualified_argument_in_product_domain heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
    (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) context contextCode (valid h)
    context_checked (context_assembles h constants) lowerLevel (.head zero) pairType
    lowerFormation (formationMeaning h 0) (fun _ => universeSet h ∅ 0)
    lower_formation_checked rfl rfl (program depth) (lowerCode depth)
    (programMeaning h 0 depth) (lower_checked depth) (lower_argument_qualified depth)
    (lower_assembles h constants depth) env admitted
  rw [application_lambda_value heads constants lowerLevel (.head zero) pairType body
    (program depth) lowerFormation (lowerCode depth) lowerBodyCode
    (formationMeaning h 0) (programMeaning h 0 depth) result bodyMeaning
    (fun _ => universeSet h ∅ 0) rfl rfl rfl (lower_assembles h constants depth)
    atResult env inside]
  change ZFSet.pair ((programMeaning h 0 depth).value env) ∅ = ZFSet.pair (env 0) ∅
  have computed : (programMeaning h 0 depth).value env = env 0 :=
    iterated_value_of_member h 0 depth (env 0) admitted.2
  rw [computed]

theorem lower_result_member (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) (result : Meaning.{u} 1)
    (atResult : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (lowerApplicationCode depth) (pairProgram depth) pairType = some result)
    (env : Environment.{u} 1) (admitted : valid h env) :
    result.value env ∈ sigmaSet (universeSet h ∅ 1) (fun x => truthCode (x = x)) := by
  rw [lower_result_computes h constants depth result atResult env admitted]
  exact ZFSetDependentProducts.mem_sigmaSet.mpr
    ⟨env 0, universeSet_subset_next h ∅ 0 admitted.2, ∅,
      (mem_truthCode _ _).mpr ⟨rfl, rfl⟩, rfl⟩

/-- The comparison has a witnessed nonempty environment and a result in
the independently formed dependent pair type. -/
theorem computed_pair_two_code_consumed (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ lower upper : Meaning.{u} 1,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (lowerApplicationCode depth) (pairProgram depth) pairType = some lower ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (upperApplicationCode depth) (pairProgram depth) pairType = some upper ∧
      lower.value (fun _ => (twoCode h).1) = upper.value (fun _ => (twoCode h).1) ∧
      lower.value (fun _ => (twoCode h).1) ∈
        sigmaSet (universeSet h ∅ 1) (fun x => truthCode (x = x)) := by
  obtain ⟨lower, upper, atLower, atUpper, agree⟩ :=
    computed_pair_values_agree h constants depth
  exact ⟨lower, upper, atLower, atUpper,
    agree _ (ZFSetReplayApplicationComparisonControls.nonempty_input_valid h),
    lower_result_member h constants depth lower atLower _
      (ZFSetReplayApplicationComparisonControls.nonempty_input_valid h)⟩

#print axioms lower_argument_qualified
#print axioms upper_argument_qualified
#print axioms lower_argument_path
#print axioms upper_argument_path
#print axioms raised_lower_argument_path
#print axioms computed_equality_witness_checks_and_inhabits
#print axioms computed_equality_witness_invalid_input_rejected
#print axioms computed_equality_witness_two_code_input
#print axioms computed_values_agree_via_qualified_paths
#print axioms computed_proof_family_values_agree
#print axioms proofCarryingImageFamily_checked
#print axioms computed_proof_family_formations_checked
#print axioms checked_computed_proof_family_meanings_agree
#print axioms computed_proof_family_member
#print axioms checked_computed_proof_family_member
#print axioms erased_proof_family_image_rejected
#print axioms computed_proof_family_two_code_member
#print axioms lower_application_checked
#print axioms upper_application_checked
#print axioms erased_computed_argument_rejected
#print axioms computed_pair_values_agree
#print axioms computed_pair_invalid_input_values_differ
#print axioms lower_result_computes
#print axioms lower_result_member
#print axioms computed_pair_two_code_consumed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayQualifiedApplicationControls
