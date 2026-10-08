import Mettapedia.TypeTheory.PresheafNativePropositionReadout
import Mettapedia.TypeTheory.PresheafNativeLogicalCells
import Mettapedia.TypeTheory.PresheafNativeClosedSubstitution

/-!
# Ordinary native propositions under theory restriction

The canonical inverse-image-of-sieves map acts on the chosen ordinary
native proposition type. It transports characteristic sections and their
predicate readouts through the actual local contextual action. The
comparison is invertible for an equivalence of theories; general theory
cells retain their lax sieve comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.PresheafNativePropositionRestriction

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Topos
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafTheoryTransformation
open ContextualLocalUniverses NativeLocalTypeFormers
open NativeLocalTheoryRestriction NativeLocalTheoryTransformation NativeLocalDisplayComparisons
open PresheafNativeLogicalAction PresheafNativeLogicalCells PresheafNativePropositionReadout

universe u
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
variable {P : Dᵒᵖ ⥤ Type u}

local instance decodedCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} ((presheafCwf.{u, u, u} C).Ty P) :=
  inferInstanceAs (Category.{u} (DisplayedFamily.{u, u, u, u} P))

local instance nativeDisplayCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} (TypeOver (localCwf (presheafCwf.{u, u, u} C)) P) :=
  TypeOver.instCategory (C := localCwf (presheafCwf.{u, u, u} C)) (Γ := P)

/-- This is the actual chosen native Ω comparison; its components are
the canonical sieve inverse images, including all admitted future arrows. -/
def comparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    (show DisplayedFamily (F.op ⋙ P) from (restrict F (nativeOmega P)).decoded) ⟶
      (show DisplayedFamily (F.op ⋙ P) from (nativeOmega (F.op ⋙ P)).decoded) where
  app _point := TypeCat.ofHom (Sieve.functorPullback F)
  naturality _first _second arrow :=
    (DisplayedPresheafClassifierCoherence.comparison F P).naturality arrow

def displayComparison (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    (⟨restrict F (nativeOmega P)⟩ : TypeOver (nativeLocalModel C).toCwf (F.op ⋙ P)) ⟶
      ⟨nativeOmega (F.op ⋙ P)⟩ := displayHom _ _ (comparison F P)

theorem comparison_identity (P : Dᵒᵖ ⥤ Type u) :
    comparison (𝟭 D) P = 𝟙 (nativeOmega P).decoded := by
  ext point sieve
  apply Sieve.ext
  intro future arrow
  rfl

theorem comparison_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) :
    comparison (F ⋙ G) P =
      (restrictionFunctor F (G.op ⋙ P)).map (comparison G P) ≫ comparison F (G.op ⋙ P) := by
  ext point sieve
  apply Sieve.ext
  intro future arrow
  rfl

theorem display_identity (P : Dᵒᵖ ⥤ Type u) :
    displayComparison (𝟭 D) P = 𝟙 (⟨nativeOmega P⟩ :
      TypeOver (nativeLocalModel D).toCwf P) := by
  unfold displayComparison
  rw [comparison_identity]
  exact displayHom_identity _

theorem display_composition (F : C ⥤ D) (G : D ⥤ E)
    (P : Eᵒᵖ ⥤ Type u) :
    displayComparison (F ⋙ G) P =
      ((localMorphism F).mapTypeFunctor (G.op ⋙ P)).map (displayComparison G P) ≫
        displayComparison F (G.op ⋙ P) := by
  unfold displayComparison
  rw [action_displayHom, ← displayHom_composition, comparison_composition]
  rfl

/-- The inverse is earned from the canonical full, faithful and
essentially-surjective sieve comparison. -/
noncomputable def comparisonIso (F : C ⥤ D) [F.IsEquivalence]
    (P : Dᵒᵖ ⥤ Type u) :
    (show DisplayedFamily (F.op ⋙ P) from (restrict F (nativeOmega P)).decoded) ≅
      (show DisplayedFamily (F.op ⋙ P) from (nativeOmega (F.op ⋙ P)).decoded) :=
  NatIso.ofComponents (fun point =>
    (ClassifierRestriction.componentEquiv F point.1.unop).toIso)
    (by intro first second arrow; exact (comparison F P).naturality arrow)

theorem comparisonIso_hom (F : C ⥤ D) [F.IsEquivalence] (P : Dᵒᵖ ⥤ Type u) :
    (comparisonIso F P).hom = comparison F P := rfl

noncomputable def displayIso (F : C ⥤ D) [F.IsEquivalence] (P : Dᵒᵖ ⥤ Type u) :
    (⟨restrict F (nativeOmega P)⟩ : TypeOver (nativeLocalModel C).toCwf (F.op ⋙ P)) ≅
      ⟨nativeOmega (F.op ⋙ P)⟩ :=
  NativeLocalDisplayComparisons.displayIso _ _ (comparisonIso F P)

theorem displayIso_hom (F : C ⥤ D) [F.IsEquivalence] (P : Dᵒᵖ ⥤ Type u) :
    (displayIso F P).hom = displayComparison F P := rfl

/-- First apply the actual native local type action to the supplied
section, then the canonical chosen-Ω comparison. -/
noncomputable def termAction (F : C ⥤ D) (term : (nativeOmega P).decoded.sections) :
    (nativeOmega (F.op ⋙ P)).decoded.sections :=
  (Functor.sectionsFunctor (F.op ⋙ P).Elements).map (comparison F P)
    (ContextualLocalUniversesMorphism.termAction
      (DisplayedPresheafTheoryCwf.strictMorphism F) term)

theorem quote_action (F : C ⥤ D) (selected : Subfunctor P) :
    termAction F (nativeQuote selected) =
      nativeQuote (LogicalTransport.restrictPredicate F selected) := by
  apply (nativeTermEquiv (F.op ⋙ P)).injective
  apply (sectionCharacteristicEquiv (F.op ⋙ P)).injective
  change Functor.whiskerLeft F.op (characteristic selected) ≫
      ClassifierRestriction.comparison F =
    characteristic (LogicalTransport.restrictPredicate F selected)
  exact ClassifierRestriction.characteristic F P selected

theorem holds_action (F : C ⥤ D) (term : (nativeOmega P).decoded.sections) :
    nativeHolds (termAction F term) = LogicalTransport.restrictPredicate F (nativeHolds term) := by
  conv_lhs => rw [← nativeQuote_nativeHolds term]
  rw [quote_action, nativeHolds_nativeQuote]

/-- The general corrected theory cell is lax on contextual sieves,
including the complete native program-and-proposition receipt. -/
theorem cell_lax {F G : C ⥤ D} (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u)
    (world : Cᵒᵖ) (receipt : (totalSpace (restrict G (nativeOmega P)).decoded).obj world) :
    @LE.le (Sieve world.unop) inferInstance
      ((displayComparison G P).substitution.app world receipt).2
      ((displayComparison F P).substitution.app world
        ((completeCell change P (nativeOmega P)).app world receipt)).2 :=
  DisplayedPresheafClassifierCoherence.transformation_le change P
    ⟨world, receipt.1⟩ receipt.2

/-- Rebuilt ordinary propositions follow the actual native context
extension substitution. The sieve value is retained at the same world. -/
def propositionCell {F G : C ⥤ D} (change : F ⟶ G) (P : Dᵒᵖ ⥤ Type u) :
    totalSpace (nativeOmega (G.op ⋙ P)).decoded ⟶
      totalSpace (nativeOmega (F.op ⋙ P)).decoded :=
  TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf)
    (baseMap change P) (nativeOmega (F.op ⋙ P))

/-- Invertible theory cells recover equality of the full chosen native
proposition square, with the actual program substitution retained. -/
theorem cell_iso_square {F G : C ⥤ D} (change : F ≅ G) (P : Dᵒᵖ ⥤ Type u) :
    (displayComparison G P).substitution ≫ propositionCell change.hom P =
      completeCell change.hom P (nativeOmega P) ≫
        (displayComparison F P).substitution := by
  ext world receipt
  change (⟨(baseMap change.hom P).app world receipt.1,
      (comparison G P).app ⟨world, receipt.1⟩ receipt.2⟩ :
      (totalSpace (nativeOmega (F.op ⋙ P)).decoded).obj world) =
    ⟨(baseMap change.hom P).app world receipt.1,
      (comparison F P).app ⟨world, (baseMap change.hom P).app world receipt.1⟩
        ((familyMap change.hom P (nativeOmega P).decoded).app
          ⟨world, receipt.1⟩ receipt.2)⟩
  have compared := (ConcreteCategory.congr_hom (NatTrans.congr_app
    (DisplayedPresheafClassifierCoherence.transformation_iso change P)
    ⟨world, receipt.1⟩) receipt.2).symm
  exact congrArg (fun sieve : Sieve world.unop =>
    (⟨(baseMap change.hom P).app world receipt.1, sieve⟩ :
      (totalSpace (nativeOmega (F.op ⋙ P)).decoded).obj world)) compared

theorem term_identity (term : (nativeOmega P).decoded.sections) :
    termAction (𝟭 D) term = term := by
  rw [← nativeQuote_nativeHolds term, quote_action]
  rfl

theorem term_composition (F : C ⥤ D) (G : D ⥤ E)
    {P : Eᵒᵖ ⥤ Type u} (term : (nativeOmega P).decoded.sections) :
    termAction (F ⋙ G) term = termAction F (termAction G term) := by
  rw [← nativeQuote_nativeHolds term, quote_action, quote_action, quote_action]
  rfl

end Mettapedia.TypeTheory.PresheafNativePropositionRestriction
