import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftCoherence

/-!
# Arbitrary parameter substitution for the actual set-model lift

Parameter functors may inhabit independent wider universes, and their maps
may identify different original values. Both member families are formed
over the actual retained parameter comprehension. Substitution recomputes
these families and their natural decoder maps, rather than assuming a
chosen family or an inverse for the parameter map.

Whole compatible sections have constructed inverse comparisons. Restricting
a section along any parameter map commutes with the upper member decoder,
and identity and composition preserve the complete section values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftSubstitution

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftCoherence

universe u v w z
variable {D : Type u} [Category.{u} D]
variable {P : UpperSite (D := D) ⥤ Type v} {Q : UpperSite (D := D) ⥤ Type w}
variable {R : UpperSite (D := D) ⥤ Type z}

noncomputable def sectionsUnder (parent : NaturalHom P source) :
    (lowerUnder parent).sections ≃ (upperUnder parent).sections where
  toFun := (forwardUnder parent).mapSection
  invFun := (backwardUnder parent).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (codeEquiv ((ContextualSmallFamilyUniverse.elementMap parent).obj point)).symm_apply_apply
      (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (codeEquiv ((ContextualSmallFamilyUniverse.elementMap parent).obj point)).apply_symm_apply
      (term.val point)

theorem lower_substitution (parent : NaturalHom P source) (change : NaturalHom Q P) :
    lowerUnder (change.comp parent) = ContextualSmallFamilyUniverse.restrict
      (ContextualSmallFamilyUniverse.elementMap change) (lowerUnder parent) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem upper_substitution (parent : NaturalHom P source) (change : NaturalHom Q P) :
    upperUnder (change.comp parent) = ContextualSmallFamilyUniverse.restrict
      (ContextualSmallFamilyUniverse.elementMap change) (upperUnder parent) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

noncomputable def lowerSectionChange (parent : NaturalHom P source) (change : NaturalHom Q P)
    (term : (lowerUnder parent).sections) : (lowerUnder (change.comp parent)).sections :=
  ⟨fun point => term.val ((ContextualSmallFamilyUniverse.elementMap change).obj point), by
    intro _ _ step
    exact term.property ((ContextualSmallFamilyUniverse.elementMap change).map step)⟩

noncomputable def upperSectionChange (parent : NaturalHom P source) (change : NaturalHom Q P)
    (term : (upperUnder parent).sections) : (upperUnder (change.comp parent)).sections :=
  ⟨fun point => term.val ((ContextualSmallFamilyUniverse.elementMap change).obj point), by
    intro _ _ step
    exact term.property ((ContextualSmallFamilyUniverse.elementMap change).map step)⟩

theorem forward_substitution (parent : NaturalHom P source) (change : NaturalHom Q P)
    (point : Q.Elements) (code : (lowerUnder (change.comp parent)).obj point) :
    (forwardUnder (change.comp parent)).app point code =
      (forwardUnder parent).app ((ContextualSmallFamilyUniverse.elementMap change).obj point) code := rfl

theorem backward_substitution (parent : NaturalHom P source) (change : NaturalHom Q P)
    (point : Q.Elements) (code : (upperUnder (change.comp parent)).obj point) :
    (backwardUnder (change.comp parent)).app point code =
      (backwardUnder parent).app ((ContextualSmallFamilyUniverse.elementMap change).obj point) code := rfl

theorem section_substitution (parent : NaturalHom P source) (change : NaturalHom Q P)
    (term : (lowerUnder parent).sections) :
    sectionsUnder (change.comp parent) (lowerSectionChange parent change term) =
      upperSectionChange parent change (sectionsUnder parent term) := by
  apply Subtype.ext
  funext point
  exact forward_substitution parent change point _

theorem inverse_section_substitution (parent : NaturalHom P source) (change : NaturalHom Q P)
    (term : (upperUnder parent).sections) :
    (sectionsUnder (change.comp parent)).symm (upperSectionChange parent change term) =
      lowerSectionChange parent change ((sectionsUnder parent).symm term) := by
  apply Subtype.ext
  funext point
  exact backward_substitution parent change point _

def parameterIdentity (parameters : UpperSite (D := D) ⥤ Type v) : NaturalHom parameters parameters where
  app _ value := value
  naturality _ _ := rfl

theorem lowerSectionChange_identity (parent : NaturalHom P source) (term : (lowerUnder parent).sections) :
    lowerSectionChange parent (parameterIdentity P) term = term := by
  apply Subtype.ext
  funext point
  rfl

theorem upperSectionChange_identity (parent : NaturalHom P source) (term : (upperUnder parent).sections) :
    upperSectionChange parent (parameterIdentity P) term = term := by
  apply Subtype.ext
  funext point
  rfl

theorem lowerSectionChange_comp (parent : NaturalHom P source)
    (first : NaturalHom R Q) (later : NaturalHom Q P) (term : (lowerUnder parent).sections) :
    lowerSectionChange parent (first.comp later) term =
      lowerSectionChange (later.comp parent) first (lowerSectionChange parent later term) := by
  apply Subtype.ext
  funext point
  rfl

theorem upperSectionChange_comp (parent : NaturalHom P source)
    (first : NaturalHom R Q) (later : NaturalHom Q P) (term : (upperUnder parent).sections) :
    upperSectionChange parent (first.comp later) term =
      upperSectionChange (later.comp parent) first (upperSectionChange parent later term) := by
  apply Subtype.ext
  funext point
  rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftSubstitution
