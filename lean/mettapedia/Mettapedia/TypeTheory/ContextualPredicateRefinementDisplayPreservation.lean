import Mettapedia.TypeTheory.ContextualPredicateRefinementDisplay
import Mettapedia.TypeTheory.ContextualPredicateScopeMorphism

/-!
# Refined display arrows under actual contextual model maps

The image of a refinement predicate is retyped by the selected context
extension equation. Local predicate naturality, refinement formation and
forgetting then earn the complete display comparison square. This transports
target monicity to the actual mapped source arrow, and determines any context
transformation component once its ambient display component is fixed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateRefinementDisplayPreservation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateMorphism
open ContextualComprehensionMorphism ContextualPredicateRefinementDisplay
open ContextualPredicateScopeMorphism (substituted_predicate_heq)

universe c s t m p q
variable {C D : CwfWithTerminal.{c,s,t,m}}
variable {mapping : StrictCwfMorphism C D}
variable {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
variable {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
variable {predicates : DoctrinePreservation mapping source target}
variable {sourceOperations : RefinementOperations source}
variable {targetOperations : RefinementOperations target}

def imagePredicate {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type)) :
    target.Predicate (D.toCwf.ext (context mapping Γ) (mapping.toFamilyMorphism.mapType type)) :=
  cast (congrArg target.Predicate (context_ext mapping Γ type))
    (predicates.hom (C.toCwf.ext Γ type) predicate)

theorem imagePredicate_heq {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type)) :
    HEq (imagePredicate (predicates := predicates) type predicate)
      (predicates.hom (C.toCwf.ext Γ type) predicate) := cast_heq _ _

theorem forget_images_heq
    (preserved : RefinementPreservation predicates sourceOperations targetOperations)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context mapping Γ = Γ')
    {type : C.toCwf.Ty Γ} {type' : D.toCwf.Ty Γ'}
    (types : HEq (mapping.toFamilyMorphism.mapType type) type')
    {predicate : source.Predicate (C.toCwf.ext Γ type)}
    {predicate' : target.Predicate (D.toCwf.ext Γ' type')}
    (predicateValues : HEq (predicates.hom (C.toCwf.ext Γ type) predicate) predicate')
    {value : C.toCwf.Tm Γ (sourceOperations.refined type predicate)}
    {value' : D.toCwf.Tm Γ' (targetOperations.refined type' predicate')}
    (values : HEq (mapping.toFamilyMorphism.mapTerm value) value') :
    HEq (mapping.toFamilyMorphism.mapTerm (sourceOperations.forget type predicate value))
      (targetOperations.forget type' predicate' value') := by
  cases contexts
  cases eq_of_heq types
  exact preserved.forget type predicate predicate' predicateValues value value' values

variable (preserved : RefinementPreservation predicates sourceOperations targetOperations)
include preserved

theorem refinement_image {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type)) :
    mapping.toFamilyMorphism.mapType (sourceOperations.refined type predicate) =
      targetOperations.refined (mapping.toFamilyMorphism.mapType type)
        (imagePredicate (predicates := predicates) type predicate) :=
  preserved.formation type predicate _ (imagePredicate_heq type predicate).symm

theorem refined_context_image {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type)) :
    mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ (sourceOperations.refined type predicate)⟩ =
      (⟨D.toCwf.ext (context mapping Γ)
        (targetOperations.refined (mapping.toFamilyMorphism.mapType type)
          (imagePredicate (predicates := predicates) type predicate))⟩ : D.toCwf.base.Context) :=
  ContextualBase.Context.ext (extension_images mapping rfl (heq_of_eq (refinement_image preserved type predicate)))

/-- Both the substituted ambient annotation and the retained generic
refinement section are compared before forgetting. -/
theorem forgetGeneric_image_heq {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type)) :
    HEq (mapping.toFamilyMorphism.mapTerm (forgetGeneric sourceOperations type predicate))
      (forgetGeneric targetOperations (mapping.toFamilyMorphism.mapType type)
        (imagePredicate (predicates := predicates) type predicate)) := by
  let refined := sourceOperations.refined type predicate
  let targetType := mapping.toFamilyMorphism.mapType type
  let targetPredicate := imagePredicate (predicates := predicates) type predicate
  let targetRefined := targetOperations.refined targetType targetPredicate
  have formed : mapping.toFamilyMorphism.mapType refined = targetRefined := refinement_image preserved type predicate
  have contexts := extension_images mapping rfl (heq_of_eq formed)
  have weakenings : HEq (mapping.toFamilyMorphism.base.map (C.toCwf.wk refined))
      (D.toCwf.wk targetRefined) :=
    (projection_heq mapping Γ refined).trans (wk_heq rfl (heq_of_eq formed))
  have shiftedTypes := substituted_type_heq mapping contexts rfl
    (A := type) (A' := targetType) HEq.rfl weakenings
  have shiftedContexts := extension_images mapping contexts shiftedTypes
  have lifts := lifted_substitution_heq mapping contexts rfl
    (A := type) (A' := targetType) HEq.rfl (C.toCwf.wk refined) (D.toCwf.wk targetRefined) weakenings
  have shiftedPredicates := substituted_predicate_heq predicates shiftedContexts
    (context_ext mapping Γ type) (imagePredicate_heq type predicate).symm lifts
  have retained :
      HEq (mapping.toFamilyMorphism.mapTerm (genericRefined sourceOperations type predicate))
        (genericRefined targetOperations targetType targetPredicate) :=
    (mapping.mapTerm_heq
      (sourceOperations.formation_substitution (C.toCwf.wk refined) type predicate).symm
      (genericRefined_heq sourceOperations type predicate)).trans
      ((variable_heq mapping Γ refined).trans
        ((vz_heq rfl (heq_of_eq formed)).trans
          (genericRefined_heq targetOperations targetType targetPredicate).symm))
  exact forget_images_heq preserved contexts shiftedTypes shiftedPredicates retained

theorem forgetDisplay_image_heq {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type)) :
    HEq (mapping.toFamilyMorphism.base.map (forgetDisplay sourceOperations type predicate))
      (forgetDisplay targetOperations (mapping.toFamilyMorphism.mapType type)
        (imagePredicate (predicates := predicates) type predicate)) := by
  have formed := refinement_image preserved type predicate
  have contexts := extension_images mapping rfl (heq_of_eq formed)
  have weakenings := (projection_heq mapping Γ (sourceOperations.refined type predicate)).trans
    (wk_heq rfl (heq_of_eq formed))
  exact pairing_images_heq mapping contexts rfl
    (A := type) (A' := mapping.toFamilyMorphism.mapType type) HEq.rfl
    _ _ weakenings _ _ (forgetGeneric_image_heq preserved type predicate)

/-- The comparison is a square of actual complete substitutions. -/
theorem forgetDisplay_image_square {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type)) :
    mapping.toFamilyMorphism.base.map (forgetDisplay sourceOperations type predicate) ≫
        eqToHom (mapping.extension_preserved Γ type) =
      eqToHom (refined_context_image preserved type predicate) ≫
        (show D.toCwf.Sub
          (D.toCwf.ext (context mapping Γ)
            (targetOperations.refined (mapping.toFamilyMorphism.mapType type)
              (imagePredicate (predicates := predicates) type predicate)))
          (D.toCwf.ext (context mapping Γ) (mapping.toFamilyMorphism.mapType type)) from
          forgetDisplay targetOperations (mapping.toFamilyMorphism.mapType type)
            (imagePredicate (predicates := predicates) type predicate)) :=
  diagram_of_heq (refined_context_image preserved type predicate) (mapping.extension_preserved Γ type)
    _ _ (forgetDisplay_image_heq preserved type predicate)

/-- The actual mapped forgetting arrow is monic, since its comparison is
made with the independently constructed target forgetting arrow. -/
theorem mapped_forgetDisplay_injective {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type)) (object : D.toCwf.base.Context) :
    Function.Injective (fun arrow : object ⟶
      mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ (sourceOperations.refined type predicate)⟩ =>
        arrow ≫ mapping.toFamilyMorphism.base.map (forgetDisplay sourceOperations type predicate)) := by
  intro first second equal
  have compared := congrArg
    (fun arrow => arrow ≫ eqToHom (mapping.extension_preserved Γ type)) equal
  rw [Category.assoc, Category.assoc, forgetDisplay_image_square preserved] at compared
  rw [← Category.assoc, ← Category.assoc] at compared
  have retained := forgetDisplay_monic targetOperations (mapping.toFamilyMorphism.mapType type)
    (imagePredicate (predicates := predicates) type predicate) compared
  exact (cancel_mono (eqToHom (refined_context_image preserved type predicate))).mp retained

/-- Naturality and the earned mapped monicity determine the refined
component from the ambient display component. -/
theorem refined_fixed
    (cell : mapping.toFamilyMorphism.base ⟶ mapping.toFamilyMorphism.base)
    {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type))
    (ambientFixed : cell.app ⟨C.toCwf.ext Γ type⟩ =
      𝟙 (mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ type⟩)) :
    cell.app ⟨C.toCwf.ext Γ (sourceOperations.refined type predicate)⟩ =
      𝟙 (mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ (sourceOperations.refined type predicate)⟩) := by
  apply mapped_forgetDisplay_injective preserved type predicate
    (mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ (sourceOperations.refined type predicate)⟩)
  have natural := cell.naturality
    (show (⟨C.toCwf.ext Γ (sourceOperations.refined type predicate)⟩ : C.toCwf.base.Context) ⟶
      ⟨C.toCwf.ext Γ type⟩ from forgetDisplay sourceOperations type predicate)
  rw [ambientFixed, Category.comp_id] at natural
  simpa only [Category.id_comp] using natural.symm

end Mettapedia.TypeTheory.ContextualPredicateRefinementDisplayPreservation
