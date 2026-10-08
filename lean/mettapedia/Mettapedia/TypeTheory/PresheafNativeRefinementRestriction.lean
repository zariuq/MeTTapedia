import Mettapedia.TypeTheory.PresheafNativeStableRefinement
import Mettapedia.TypeTheory.PresheafNativeLogicalCells

/-!
# Chosen native refinement under theory restriction

Theory restriction retains the selected original inhabitant. Its native
dependent-sum/truth presentation is compared with the chosen refinement of
the restricted native family. The comparison is a genuine display
isomorphism over the actual restricted program context; no inverse for the
general truth-object or dependent-product comparison is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.PresheafNativeRefinementRestriction

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Topos
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open DisplayedPresheafCwf DisplayedPresheafTheoryRestriction
open DisplayedPresheafTheoryRestrictionAction DisplayedPresheafTheoryTransformation
open ContextualLocalUniverses NativeLocalTypeFormers
open NativeLocalTheoryRestriction NativeLocalTheoryTransformation NativeLocalDisplayComparisons
open PresheafNativeLogicalAction PresheafNativeLogicalCells

universe u
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
variable {P : Dᵒᵖ ⥤ Type u}

local instance decodedCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} ((presheafCwf.{u, u, u} C).Ty P) :=
  inferInstanceAs (Category.{u} (DisplayedFamily.{u, u, u, u} P))

local instance nativeDisplayCategory (P : Cᵒᵖ ⥤ Type u) :
    Category.{u} (TypeOver (localCwf (presheafCwf.{u, u, u} C)) P) :=
  TypeOver.instCategory (C := localCwf (presheafCwf.{u, u, u} C)) (Γ := P)

attribute [local irreducible] NativeLocalTypeFormers.sigma PresheafNativeStableRefinement.chosen

/-- The restricted predicate is expressed on the complete comprehension
of the actual restricted native type. -/
def predicate (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    Subfunctor (totalSpace (restrict F A).decoded) :=
  (LogicalTransport.restrictPredicate F selected).preimage
    (totalComparison F P A.decoded).hom

theorem predicate_identity (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    predicate (𝟭 D) A selected = selected := by
  ext world value
  rfl

theorem predicate_composition (F : C ⥤ D) (G : D ⥤ E)
    {P : Eᵒᵖ ⥤ Type u} (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    predicate (F ⋙ G) A selected = predicate F (restrict G A) (predicate G A selected) := by
  ext world value
  rfl

/-- The direct satisfying-inhabitant families compare before choosing
native presentations. Both directions retain the supplied inhabitant. -/
def subtypeIso (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    restrictFamily F P (PresheafNativePredicateRefinement.displayed A.decoded selected) ≅
      PresheafNativePredicateRefinement.displayed (restrict F A).decoded
        (predicate F A selected) :=
  NatIso.ofComponents (fun point =>
    (show _ ≃ _ from
      { toFun := fun value => ⟨value.val, value.property⟩
        invFun := fun value => ⟨value.val, value.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).toIso) (by
      intro first second arrow
      ext value
      apply Subtype.ext
      rfl)

/-- The comparison applies to the chosen native dependent sum with the
fixed truth-proof family, not merely an independently presented subtype. -/
noncomputable def comparison (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (show DisplayedFamily (F.op ⋙ P) from
      (restrict F (PresheafNativeStableRefinement.chosen A selected)).decoded) ≅
      (show DisplayedFamily (F.op ⋙ P) from
        (PresheafNativeStableRefinement.chosen (restrict F A)
          (predicate F A selected)).decoded) :=
  eqToIso (C := DisplayedFamily (F.op ⋙ P))
      (decode_restriction F (PresheafNativeStableRefinement.chosen A selected)) ≪≫
    (restrictionFunctor F P).mapIso (PresheafNativeStableRefinement.decodeIso A selected) ≪≫
    subtypeIso F A selected ≪≫
    (PresheafNativeStableRefinement.decodeIso (restrict F A) (predicate F A selected)).symm

noncomputable def displayComparison (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (⟨restrict F (PresheafNativeStableRefinement.chosen A selected)⟩ :
      TypeOver (nativeLocalModel C).toCwf (F.op ⋙ P)) ≅
        ⟨PresheafNativeStableRefinement.chosen (restrict F A) (predicate F A selected)⟩ :=
  displayIso _ _ (comparison F A selected)

/-- Decoding the whole comparison recovers the selected original
inhabitant, with its complete predicate membership. -/
theorem decoder_square (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (comparison F A selected).hom ≫
        (PresheafNativeStableRefinement.decodeIso (restrict F A)
          (predicate F A selected)).hom =
      (restrictionFunctor F P).map (PresheafNativeStableRefinement.decodeIso A selected).hom ≫
        (subtypeIso F A selected).hom := by
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Functor.mapIso_hom, restriction_cast_hom,
    Category.id_comp]

theorem forget_family_square (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (comparison F A selected).hom ≫
        (PresheafNativeStableRefinement.decodeIso (restrict F A)
          (predicate F A selected)).hom ≫
        PresheafNativePredicateRefinement.forgetFamily (restrict F A).decoded
          (predicate F A selected) =
      (restrictionFunctor F P).map
        ((PresheafNativeStableRefinement.decodeIso A selected).hom ≫
          PresheafNativePredicateRefinement.forgetFamily A.decoded selected) := by
  rw [← Category.assoc, decoder_square, Category.assoc, Functor.map_comp]
  ext point value
  rfl

/-- The actual native forgetful display arrow commutes with the native
contextual action, including its complete substitution. -/
theorem forget_display_square (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (displayComparison F A selected).hom ≫
        PresheafNativeStableRefinement.forgetNativeDisplay (restrict F A)
          (predicate F A selected) =
      ((localMorphism F).mapTypeFunctor P).map
        (PresheafNativeStableRefinement.forgetNativeDisplay A selected) := by
  change displayHom _ _ _ ≫ displayHom _ _ _ =
    ((localMorphism F).mapTypeFunctor P).map
      (displayHom (PresheafNativeStableRefinement.chosen A selected) A
        ((PresheafNativeStableRefinement.decodeIso A selected).hom ≫
          PresheafNativePredicateRefinement.forgetFamily A.decoded selected))
  rw [← displayHom_composition, action_displayHom]
  exact congrArg (displayHom _ _) (forget_family_square F A selected)

/-- The complete comprehension inclusion agrees through the actual
theory action on the original native forgetful arrow. -/
theorem forget_complete_square (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (displayComparison F A selected).hom.substitution ≫
        PresheafNativeStableRefinement.forgetComplete (restrict F A)
          (predicate F A selected) =
      (((localMorphism F).mapTypeFunctor P).map
          (PresheafNativeStableRefinement.forgetNativeDisplay A selected)).substitution := by
  rw [← PresheafNativeStableRefinement.forgetNativeDisplay_substitution]
  exact congrArg (fun arrow => arrow.substitution) (forget_display_square F A selected)

theorem action_forget_total (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (((localMorphism F).mapTypeFunctor P).map
      (PresheafNativeStableRefinement.forgetNativeDisplay A selected)).substitution =
    totalHom ((restrictionFunctor F P).map
      ((PresheafNativeStableRefinement.decodeIso A selected).hom ≫
        PresheafNativePredicateRefinement.forgetFamily A.decoded selected)) := by
  have action := action_displayHom F P (PresheafNativeStableRefinement.chosen A selected) A
    ((PresheafNativeStableRefinement.decodeIso A selected).hom ≫
      PresheafNativePredicateRefinement.forgetFamily A.decoded selected)
  exact congrArg (fun arrow => arrow.substitution) action

theorem comparison_identity (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (comparison (𝟭 D) A selected).hom =
      𝟙 (PresheafNativeStableRefinement.chosen A selected).decoded := by
  apply (Iso.cancel_iso_hom_right _ _
    (PresheafNativeStableRefinement.decodeIso A selected)).mp
  have square := decoder_square (𝟭 D) A selected
  exact square.trans (by
    ext point value
    rfl)

theorem comparison_composition (F : C ⥤ D) (G : D ⥤ E)
    {P : Eᵒᵖ ⥤ Type u} (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (comparison (F ⋙ G) A selected).hom =
      (restrictionFunctor F (G.op ⋙ P)).map (comparison G A selected).hom ≫
        (comparison F (restrict G A) (predicate G A selected)).hom := by
  apply (Iso.cancel_iso_hom_right _ _
    (PresheafNativeStableRefinement.decodeIso (restrict (F ⋙ G) A)
      (predicate (F ⋙ G) A selected))).mp
  have staged := decoder_square F (restrict G A) (predicate G A selected)
  have first := decoder_square G A selected
  have direct := decoder_square (F ⋙ G) A selected
  change _ = (restrictionFunctor F (G.op ⋙ P)).map
    (comparison G A selected).hom ≫
      ((comparison F (restrict G A) (predicate G A selected)).hom ≫
        (PresheafNativeStableRefinement.decodeIso (restrict F (restrict G A))
          (predicate F (restrict G A) (predicate G A selected))).hom)
  rw [staged, ← Category.assoc, ← Functor.map_comp, first, Functor.map_comp, direct]
  ext point value
  rfl

theorem display_identity (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (displayComparison (𝟭 D) A selected).hom =
      𝟙 (⟨PresheafNativeStableRefinement.chosen A selected⟩ :
        TypeOver (nativeLocalModel D).toCwf P) := by
  change displayHom _ _ (comparison (𝟭 D) A selected).hom = _
  rw [comparison_identity]
  exact displayHom_identity _

theorem display_composition (F : C ⥤ D) (G : D ⥤ E)
    {P : Eᵒᵖ ⥤ Type u} (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) :
    (displayComparison (F ⋙ G) A selected).hom =
      ((localMorphism F).mapTypeFunctor (G.op ⋙ P)).map
          (displayComparison G A selected).hom ≫
        (displayComparison F (restrict G A) (predicate G A selected)).hom := by
  change displayHom _ _ (comparison (F ⋙ G) A selected).hom =
    ((localMorphism F).mapTypeFunctor (G.op ⋙ P)).map
      (displayHom _ _ (comparison G A selected).hom) ≫ displayHom _ _ _
  rw [action_displayHom]
  apply TypeOver.Hom.ext
  change totalHom (comparison (F ⋙ G) A selected).hom =
    totalHom ((restrictionFunctor F (G.op ⋙ P)).map (comparison G A selected).hom) ≫
      totalHom (comparison F (restrict G A) (predicate G A selected)).hom
  rw [comparison_composition]
  exact totalHom_composition _ _

/-- Supplied native sections follow the actual local theory action and
then the complete chosen-refinement comparison. -/
noncomputable def termAction (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded))
    (term : (PresheafNativeStableRefinement.chosen A selected).decoded.sections) :
    (PresheafNativeStableRefinement.chosen (restrict F A)
      (predicate F A selected)).decoded.sections :=
  (Functor.sectionsFunctor (F.op ⋙ P).Elements).map (comparison F A selected).hom
    (ContextualLocalUniversesMorphism.termAction
      (DisplayedPresheafTheoryCwf.strictMorphism F) term)

/-- Forgetting the restricted selected section recovers the exact
restriction of its original native inhabitant. -/
theorem forget_term_action (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded))
    (term : (PresheafNativeStableRefinement.chosen A selected).decoded.sections) :
    PresheafNativeStableRefinement.forget (restrict F A) (predicate F A selected)
        (termAction F A selected term) =
      ContextualLocalUniversesMorphism.termAction
        (DisplayedPresheafTheoryCwf.strictMorphism F)
        (PresheafNativeStableRefinement.forget A selected term) := by
  apply Subtype.ext
  funext point
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (forget_family_square F A selected) point)
    ((ContextualLocalUniversesMorphism.termAction
      (DisplayedPresheafTheoryCwf.strictMorphism F) term).val point)

/-- A native introduction restricts with its supplied argument. The
target membership is earned by the native comparison, not selected from
an erased support predicate. -/
theorem introduction_action (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) (term : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ selected.obj world) :
    PresheafNativeStableRefinement.forget (restrict F A) (predicate F A selected)
        (termAction F A selected (PresheafNativeStableRefinement.intro A selected term satisfies)) =
      ContextualLocalUniversesMorphism.termAction
        (DisplayedPresheafTheoryCwf.strictMorphism F) term := by
  rw [forget_term_action, PresheafNativeStableRefinement.beta]

theorem restricted_satisfaction (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) (term : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ selected.obj world) :
    ∀ world (base : (F.op ⋙ P).obj world),
      (⟨base, (ContextualLocalUniversesMorphism.termAction
        (DisplayedPresheafTheoryCwf.strictMorphism F) term).val ⟨world, base⟩⟩ :
          (totalSpace (restrict F A).decoded).obj world) ∈ (predicate F A selected).obj world :=
  fun world base => satisfies (F.op.obj world) base

theorem introduction_square (F : C ⥤ D) (A : NativeType P)
    (selected : Subfunctor (totalSpace A.decoded)) (term : A.decoded.sections)
    (satisfies : ∀ world (base : P.obj world),
      (⟨base, term.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ selected.obj world) :
    termAction F A selected (PresheafNativeStableRefinement.intro A selected term satisfies) =
      PresheafNativeStableRefinement.intro (restrict F A) (predicate F A selected)
        (ContextualLocalUniversesMorphism.termAction
          (DisplayedPresheafTheoryCwf.strictMorphism F) term)
        (restricted_satisfaction F A selected term satisfies) := by
  apply PresheafNativeStableRefinement.forget_injective
  rw [introduction_action, PresheafNativeStableRefinement.beta]

theorem term_identity (A : NativeType P) (selected : Subfunctor (totalSpace A.decoded))
    (term : (PresheafNativeStableRefinement.chosen A selected).decoded.sections) :
    termAction (𝟭 D) A selected term = term := by
  apply PresheafNativeStableRefinement.forget_injective
  rw [forget_term_action]
  apply Subtype.ext
  funext point
  rfl

theorem term_composition (F : C ⥤ D) (G : D ⥤ E) {P : Eᵒᵖ ⥤ Type u}
    (A : NativeType P) (selected : Subfunctor (totalSpace A.decoded))
    (term : (PresheafNativeStableRefinement.chosen A selected).decoded.sections) :
    termAction (F ⋙ G) A selected term =
      termAction F (restrict G A) (predicate G A selected) (termAction G A selected term) := by
  apply PresheafNativeStableRefinement.forget_injective
  rw [forget_term_action]
  change ContextualLocalUniversesMorphism.termAction
      (DisplayedPresheafTheoryCwf.strictMorphism (F ⋙ G))
      (PresheafNativeStableRefinement.forget A selected term) =
    PresheafNativeStableRefinement.forget (restrict F (restrict G A))
      (predicate F (restrict G A) (predicate G A selected))
      (termAction F (restrict G A) (predicate G A selected) (termAction G A selected term))
  rw [forget_term_action, forget_term_action]
  apply Subtype.ext
  funext point
  rfl

end Mettapedia.TypeTheory.PresheafNativeRefinementRestriction
