import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContextSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayInterpretationControls

/-!
# Dependent substitution with computed telescope entries

The source telescope contains an object and its identity witness. Its object
image computes a first projection of an applied pair-producing function; its
proof image is reflexivity at that computed object. The generic context and
membership transport laws check the actual substituted term and formation
certificates, including redexes in the dependent result type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayContextSubstitutionControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls (twoCode)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (sigmaSet)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayInterpretationControls

universe u

private def zero : Tower.Head := .sort Tower.zero
private def pairLevel : Tower.Head := .sort (.max Tower.zero Tower.zero)
private def ground {n : Nat} : Tower.Tm n := .head .legacyGround
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def targetContext : Ctx Tower.Head 1 := .snoc .nil ground
def targetContextCode : ContextCode Tower.Head NoConversion 1 := .snoc .nil zero .headType

def sourcePair : Tower.Tm 2 := .pair (.var 1) (.var 0)
def sourcePairType : Tower.Tm 2 := .sigma ground (.id ground (.var 2) (.var 0))
def sourcePairFormation : Replay 2 :=
  .sigmaForm zero zero .headType (.idForm zero .headType .var .var)
def sourcePairCode : Replay 2 := .pairIntro pairLevel sourcePairFormation .var .var

theorem source_pair_checked : check Tower.rules noConversionCheck identityContext
    sourcePair sourcePairType sourcePairCode = true := by decide

theorem source_pair_formation_checked : check Tower.rules noConversionCheck identityContext
    sourcePairType (.head pairLevel) sourcePairFormation = true := by decide

def objectImage : Tower.Tm 1 := .fst anchorApplication
def proofImage : Tower.Tm 1 := .refl objectImage
def dependentSubstitution : Sub Tower.Head 2 1 := Fin.cases proofImage (fun _ => objectImage)
def imageCodes : Fin 2 → Replay 1 :=
  Fin.cases (.reflIntro ground anchorFirstCode) (fun _ => anchorFirstCode)

theorem image_codes_checked : ∀ index,
    check Tower.rules noConversionCheck targetContext (dependentSubstitution index)
      (subst dependentSubstitution (identityContext.lookup index)) (imageCodes index) = true := by
  intro index
  fin_cases index <;> decide

/-- A ground variable is not an identity witness, even though the object
component of the substitution legitimately comes from this context. -/
theorem wrong_proof_image_rejected :
    check Tower.rules noConversionCheck targetContext (.var 0)
      (subst dependentSubstitution (identityContext.lookup 0)) (Code.var : Replay 1) = false := by
  decide

def substitutedPair : Tower.Tm 1 := subst dependentSubstitution sourcePair
def substitutedPairType : Tower.Tm 1 := subst dependentSubstitution sourcePairType
def substitutedPairCode : Replay 1 := sourcePairCode.substitute noConversionRename
  noConversionSubstitute dependentSubstitution imageCodes sourcePair sourcePairType
def substitutedPairFormation : Replay 1 := sourcePairFormation.substitute noConversionRename
  noConversionSubstitute dependentSubstitution imageCodes sourcePairType (.head pairLevel)

theorem substituted_pair_syntax : substitutedPair = .pair objectImage proofImage := rfl

theorem type_support_boundary :
    ZFSetTypeExpressionInterpretation.supported sourcePairType = true ∧
      ZFSetTypeExpressionInterpretation.supported substitutedPairType = false := by
  exact ⟨rfl, rfl⟩

noncomputable def sourceValid (h : CofinalInaccessibles.{u}) : Environment.{u} 2 → Prop :=
  fun env => (True ∧ env 1 ∈ (twoCode h).1) ∧ env 0 ∈ truthCode (env 1 = env 1)

noncomputable def targetValid (h : CofinalInaccessibles.{u}) : Environment.{u} 1 → Prop :=
  fun env => True ∧ env 0 ∈ (twoCode h).1

noncomputable def objectMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 1 :=
  .plain (fun env => Mettapedia.SetTheory.ZFSetOrderedPair.first
    ((anchorApplicationMeaning h).value env))

noncomputable def imageMeanings (h : CofinalInaccessibles.{u}) : Fin 2 → Meaning.{u} 1 :=
  Fin.cases (.plain (fun _ => ∅)) (fun _ => objectMeaning h)

noncomputable def sourceMeaning : Meaning.{u} 2 :=
  .plain (fun env => ZFSet.pair (env 1) (env 0))

noncomputable def sourceTypeMeaning (h : CofinalInaccessibles.{u}) : Meaning.{u} 2 :=
  .plain (fun env => sigmaSet (twoCode h).1 (fun x => truthCode (env 1 = x)))

theorem source_context_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      identityContextCode identityContext = some (sourceValid h) := rfl

theorem target_context_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      targetContextCode targetContext = some (targetValid h) := rfl

theorem image_meanings_assemble (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) : ∀ index,
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants (imageCodes index)
      (dependentSubstitution index) (subst dependentSubstitution (identityContext.lookup index)) =
      some (imageMeanings h index) := by
  intro index
  fin_cases index <;> rfl

theorem source_pair_member (h : CofinalInaccessibles.{u}) (env : Environment.{u} 2)
    (admitted : sourceValid h env) : sourceMeaning.value env ∈ (sourceTypeMeaning h).value env := by
  exact ZFSetDependentProducts.mem_sigmaSet.mpr
    ⟨env 1, admitted.1.2, env 0, admitted.2, rfl⟩

/-- The source telescope is satisfied by the computed images. Object
membership uses the previously established application/projection theorem;
the dependent proof slot uses the identity interpretation, not an assumed
soundness theorem for arbitrary derivations. -/
theorem image_environment_valid (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (env : Environment.{u} 1)
    (admitted : targetValid h env) : sourceValid h (imageEnvironment (imageMeanings h) env) := by
  refine ⟨⟨True.intro, ?_⟩, ?_⟩
  · exact (anchor_first_member h constants env admitted.2).2
  · exact (mem_truthCode _ _).mpr ⟨rfl, rfl⟩

/-- Both substituted certificates are checked and their assembled values
satisfy semantic typing over the target telescope. The type contains the
computed projection, so the theorem is not restricted to structural types. -/
theorem substituted_pair_membership (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    check Tower.rules noConversionCheck targetContext substitutedPair substitutedPairType
      substitutedPairCode = true ∧
    check Tower.rules noConversionCheck targetContext substitutedPairType (.head pairLevel)
      substitutedPairFormation = true ∧
    ∃ result resultType,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        substitutedPairCode substitutedPair substitutedPairType = some result ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        substitutedPairFormation substitutedPairType (.head pairLevel) = some resultType ∧
      ∀ env, targetValid h env → result.value env ∈ resultType.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨types, atTypes, validity⟩ := substitution_valid_iff noConversionRename heads constants
    noConversionSubstitute Tower.rules noConversionCheck (fun _ impossible => nomatch impossible)
    identityContext identityContextCode (sourceValid h) identity_context_checked
    (source_context_assembles h constants) dependentSubstitution imageCodes (imageMeanings h)
    (image_meanings_assemble h constants)
  exact substitute_membership noConversionRename heads constants noConversionSubstitute
    Tower.rules noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible)
    identityContext identityContextCode targetContext (sourceValid h) (targetValid h)
    sourcePair sourcePairType pairLevel sourcePairCode sourcePairFormation sourceMeaning
    (sourceTypeMeaning h) identity_context_checked source_pair_checked source_pair_formation_checked
    (source_context_assembles h constants) rfl rfl (source_pair_member h)
    dependentSubstitution imageCodes (imageMeanings h) types image_codes_checked
    (image_meanings_assemble h constants) atTypes
    (fun env admitted => (validity env).mp (image_environment_valid h constants env admitted))

/-- The target telescope has a nonempty ground value. The transported
dependent result is therefore inhabited at a concrete input. -/
theorem nonempty_input_membership (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ result resultType,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        substitutedPairCode substitutedPair substitutedPairType = some result ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        substitutedPairFormation substitutedPairType (.head pairLevel) = some resultType ∧
      result.value (fun _ => ZFSet.powerset ∅) ∈ resultType.value (fun _ => ZFSet.powerset ∅) := by
  obtain ⟨_, _, result, resultType, atResult, atType, member⟩ :=
    substituted_pair_membership h constants
  exact ⟨result, resultType, atResult, atType,
    member _ ⟨True.intro, ZFSetDependentProducts.Controls.power_empty_mem_two⟩⟩

/-- The same generated certificate whose membership was transported computes
the input object paired with the reflexivity value. -/
theorem substituted_pair_computes (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (result : Meaning.{u} 1)
    (assembled : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      substitutedPairCode substitutedPair substitutedPairType = some result)
    (env : Environment.{u} 1) (admitted : targetValid h env) :
    result.value env = ZFSet.pair (env 0) ∅ := by
  have expected : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      substitutedPairCode substitutedPair substitutedPairType =
      some (.plain (fun env => ZFSet.pair ((objectMeaning h).value env) ∅)) := rfl
  rw [expected] at assembled
  cases Option.some.inj assembled
  change ZFSet.pair (Mettapedia.SetTheory.ZFSetOrderedPair.first
    (ZFSetTraceProducts.traceApp ((anchorMeaning h).value Fin.elim0) (env 0))) ∅ = _
  rw [anchor_computes h constants (anchorMeaning h) (anchor_assembles h constants) (env 0) admitted.2,
    Mettapedia.SetTheory.ZFSetOrderedPair.first_pair]

/-- A legitimate ground object still cannot replace the telescope's proof
slot. Context validity enforces this before the dependent pair is consumed. -/
theorem nonproof_environment_rejected (h : CofinalInaccessibles.{u}) :
    ¬ sourceValid h (fun _ => ZFSet.powerset ∅) := by
  intro admitted
  have equal := ((mem_truthCode _ _).mp admitted.2).1
  change ZFSet.powerset (∅ : ZFSet.{u}) = ∅ at equal
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := by simp
  rw [equal] at member
  exact ZFSet.notMem_empty _ member

#print axioms substituted_pair_membership
#print axioms nonempty_input_membership
#print axioms substituted_pair_computes
#print axioms wrong_proof_image_rejected
#print axioms nonproof_environment_rejected
#print axioms type_support_boundary

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayContextSubstitutionControls
