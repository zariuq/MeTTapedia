import Mettapedia.GSLT.LanguageDef.BiformTheory
import Mettapedia.GSLT.LanguageDef.HOLHenkinBiformCanary

/-!
# A proof-sensitive biform-route canary

One Henkin theorem is paired with a proof-relevant loop carrying two Boolean
occurrences.  Two biform endomorphisms have the same native logical map and the
same event meaning, but one retains occurrence tags while the other flips
them.  The logical projection identifies the routes; the operational
projection separates them.

This is the smallest checked reason not to infer algorithm identity from
theorem identity.  The biform category itself retains the full algorithms;
consumer-specific erasure is performed only by an explicit projection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BiformTheoryCanary

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.BiformTheory
open Mettapedia.GSLT.LanguageDef.HOLHenkinBiformCanary
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.HenkinInstitution
open Mettapedia.Logic.HOL.HenkinInstitution.Canary

/-- One logical theorem paired with two retained occurrences over one
extensional step. -/
def occurrenceBiform : BiformTheory henkinConsequence where
  logical := targetLogical
  algorithm := Canary.boolSystem
  meaning := fun _ => targetEquation
  meaning_sound := fun _ => targetEquation_valid

/-- Flip the Boolean occurrence tag while leaving terms and extensional steps
fixed. -/
def flipOccurrences : Translation Canary.boolSystem Canary.boolSystem where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapEvidence := fun evidence => !evidence
  liftEvidence := by
    intro sourceTerm targetTerm evidence
    exact ⟨targetTerm, !evidence, ⟨⟨rfl⟩⟩⟩

/-- The route that retains each occurrence tag. -/
def retainRoute : BiformTheory.Hom occurrenceBiform occurrenceBiform :=
  BiformTheory.Hom.identity occurrenceBiform

/-- A distinct biform route with the same logical map and meaning theorem. -/
def flipRoute : BiformTheory.Hom occurrenceBiform occurrenceBiform where
  logical := PiInstitution.TheoryHom.identity targetLogical
  operational := flipOccurrences
  meaning_natural := by
    intro event
    change henkinConsequence.sentence.map
      (CategoryTheory.CategoryStruct.id targetSignature) targetEquation =
        targetEquation
    exact henkinConsequence.sentence.map_id_apply targetSignature targetEquation

/-- The two routes agree after logical projection. -/
theorem logical_images_equal :
    BiformTheory.logicalProjection.map retainRoute =
      BiformTheory.logicalProjection.map flipRoute := by
  rfl

/-- The proof-relevant operational projection still sees the flipped
occurrence. -/
theorem operational_images_distinct :
    BiformTheory.operationalProjection.map retainRoute ≠
      BiformTheory.operationalProjection.map flipRoute := by
  intro equalRoutes
  change retainRoute.operational = flipRoute.operational at equalRoutes
  have equalEvidence := congrArg
    (fun route : Translation Canary.boolSystem Canary.boolSystem =>
      route.mapEvidence (sourceTerm := ()) (sourceTarget := ()) false)
    equalRoutes
  change false = true at equalEvidence
  exact Bool.false_ne_true equalEvidence

/-- Negative control: native theorem translation does not determine the
proof-relevant biform route. -/
theorem logical_projection_not_injective :
    ¬Function.Injective
      (fun route : BiformTheory.Hom occurrenceBiform occurrenceBiform =>
        BiformTheory.logicalProjection.map route) := by
  intro injective
  have equalRoutes := injective logical_images_equal
  exact operational_images_distinct
    (congrArg BiformTheory.operationalProjection.map equalRoutes)

/-! ## The operational projection also forgets native-theory motion -/

/-- Exchange the two source constants while retaining their types. -/
def swapTwoConstants : sourceSignature ⟶ sourceSignature where
  map
    | .left => .right
    | .right => .left

/-- The empty-axiom Henkin theory on the two-constant signature. -/
def structuralLogical : PiInstitution.TheoryObject henkinConsequence :=
  PiInstitution.generatedTheory henkinConsequence sourceSignature ∅

/-- Signature translation preserves every theorem of the empty-axiom theory. -/
def swapLogical :
    PiInstitution.TheoryHom structuralLogical structuralLogical where
  mapSignature := swapTwoConstants
  preserves := by
    intro formula theoremhood
    exact PiInstitution.map_theorem henkinConsequence swapTwoConstants theoremhood

/-- A biform theory whose event meaning is the constant-free truth formula. -/
def structuralBiform : BiformTheory henkinConsequence where
  logical := structuralLogical
  algorithm := Canary.boolSystem
  meaning := fun _ => (.top : ClosedFormula TwoConstants)
  meaning_sound := by
    intro event
    change (institution Unit).Entails sourceSignature ∅
      (.top : ClosedFormula TwoConstants)
    intro model _modelsEmpty
    exact model.as.henkin.models_top

/-- Keep both the signature and operational occurrence unchanged. -/
def structuralIdentityRoute :
    BiformTheory.Hom structuralBiform structuralBiform :=
  BiformTheory.Hom.identity structuralBiform

/-- Move the native signature while leaving the proof-relevant machine fixed. -/
def structuralSwapRoute :
    BiformTheory.Hom structuralBiform structuralBiform where
  logical := swapLogical
  operational := Translation.id Canary.boolSystem
  meaning_natural := by
    intro event
    change henkinConsequence.sentence.map swapTwoConstants
      (.top : ClosedFormula TwoConstants) = .top
    rfl

theorem swapTwoConstants_ne_identity :
    swapTwoConstants ≠
      CategoryTheory.CategoryStruct.id sourceSignature := by
  intro equalMaps
  have atLeft := congrArg
    (fun translation : sourceSignature ⟶ sourceSignature =>
      translation.map TwoConstants.left)
    equalMaps
  change TwoConstants.right = TwoConstants.left at atLeft
  cases atLeft

/-- The two routes have genuinely different native logical maps. -/
theorem structural_logical_images_distinct :
    BiformTheory.logicalProjection.map structuralIdentityRoute ≠
      BiformTheory.logicalProjection.map structuralSwapRoute := by
  intro equalRoutes
  apply swapTwoConstants_ne_identity
  exact (congrArg PiInstitution.TheoryHom.mapSignature equalRoutes).symm

/-- Their proof-relevant operational maps are nevertheless identical. -/
theorem structural_operational_images_equal :
    BiformTheory.operationalProjection.map structuralIdentityRoute =
      BiformTheory.operationalProjection.map structuralSwapRoute := by
  rfl

/-- Negative control: the operational algorithm does not determine the native
theory translation of a biform route. -/
theorem operational_projection_not_injective :
    ¬Function.Injective
      (fun route : BiformTheory.Hom structuralBiform structuralBiform =>
        BiformTheory.operationalProjection.map route) := by
  intro injective
  have equalRoutes := injective structural_operational_images_equal
  exact structural_logical_images_distinct
    (congrArg BiformTheory.logicalProjection.map equalRoutes)

/-! ## Compatibility, rather than the whole product, is the image -/

def doubledTruth : ClosedFormula TwoConstants :=
  .and .top .top

/-- Both formulas are admitted explicitly so the negative result below is
about the commuting meaning square, not failure of theoremhood. -/
def tagLogical : PiInstitution.TheoryObject henkinConsequence :=
  PiInstitution.generatedTheory henkinConsequence sourceSignature
    {(.top : ClosedFormula TwoConstants), doubledTruth}

def tagMeaning (event : Canary.boolSystem.Event) :
    ClosedFormula TwoConstants :=
  match (show Bool from event.evidence) with
  | false => .top
  | true => doubledTruth

theorem tagMeaning_sound :
    MeaningSound henkinConsequence tagLogical Canary.boolSystem tagMeaning := by
  intro event
  apply PiInstitution.derives_of_mem henkinConsequence sourceSignature
  rcases event with ⟨source, target, evidence⟩
  change Bool at evidence
  cases evidence
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

def tagSensitiveBiform : BiformTheory henkinConsequence where
  logical := tagLogical
  algorithm := Canary.boolSystem
  meaning := tagMeaning
  meaning_sound := tagMeaning_sound

/-- The logical identity paired with occurrence flipping is a perfectly good
pair of independent maps, but it changes the theorem assigned to an event. -/
def incompatiblePair :
    PiInstitution.TheoryHom tagLogical tagLogical ×
      Translation Canary.boolSystem Canary.boolSystem :=
  (PiInstitution.TheoryHom.identity tagLogical, flipOccurrences)

theorem incompatiblePair_not_compatible :
    ¬BiformTheory.Compatible
      (source := tagSensitiveBiform) (target := tagSensitiveBiform)
      incompatiblePair := by
  intro compatible
  let falseEvent : Canary.boolSystem.Event :=
    ⟨(), (), false⟩
  have changedMeaning := compatible falseEvent
  have impossible : (.top : ClosedFormula TwoConstants) = doubledTruth := by
    dsimp [falseEvent, incompatiblePair, tagSensitiveBiform, tagMeaning,
      flipOccurrences, Translation.mapEvent] at changedMeaning
    change henkinConsequence.sentence.map
      (CategoryTheory.CategoryStruct.id sourceSignature)
        (.top : ClosedFormula TwoConstants) = doubledTruth at changedMeaning
    rw [henkinConsequence.sentence.map_id_apply] at changedMeaning
    exact changedMeaning
  cases impossible

/-- A pair of logical and operational maps lifts to a biform route exactly
when it commutes with event meaning; this pair therefore has no lift. -/
theorem incompatiblePair_not_in_joint_image :
    ¬∃ route : BiformTheory.Hom tagSensitiveBiform tagSensitiveBiform,
      BiformTheory.routePair route = incompatiblePair := by
  rw [BiformTheory.jointProjection_map_range_iff_compatible]
  exact incompatiblePair_not_compatible

#print axioms logical_images_equal
#print axioms operational_images_distinct
#print axioms logical_projection_not_injective
#print axioms structural_logical_images_distinct
#print axioms structural_operational_images_equal
#print axioms operational_projection_not_injective
#print axioms tagMeaning_sound
#print axioms incompatiblePair_not_compatible
#print axioms incompatiblePair_not_in_joint_image

end Mettapedia.GSLT.LanguageDef.BiformTheoryCanary
