import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyIdentityControls

/-!
# Growing upper identity motives and material collision controls

The upper motive gains a new native value at every natural stage. Its J
returns the retained endpoint and preserves a cyclic-versus-terminal
material reading. Distinct positive endpoints still have matching material
readings while their actual native identity carrier has no member.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftIdentityControls

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyIdentity ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphMaterialFamilies ContextualGraphMaterialLift
open ContextualGraphMaterialLiftIdentity
open ContextualGraphFamilyControls (unitBase growing)

def domain : Family unitBase := ⟨growing, ContextualGraphFamilyBodyControls.reading⟩

abbrev motive := endpointMotive (native domain)
abbrev method := endpointMethod (native domain)
abbrev result := J (native domain) motive method

def motiveReading : NaturalHom (total motive) (values (Upper (D := Nat))) :=
  ContextualGraphFamilyBodySubstitution.readingUnder (secondFamily (native domain))
    (ContextualGraphFamilyBodySubstitution.readingUnder (native domain)
      (ContextualGraphMaterialLift.reading domain) (projection (native domain)))
    (readLeft (native domain))

def endpointPoint (stage : Nat) (term : Fin (stage+1)) : (identityContext (native domain)).Elements :=
  ⟨PresheafSiteLift.Site.upFunctor.obj stage,
    ⟨⟨⟨ULift.up PUnit.unit, ULift.up term⟩, ULift.up term⟩, PresheafIdentityWitness.encode rfl⟩⟩

def stageStep (stage : Nat) :
    endpointPoint stage ⟨0, Nat.succ_pos _⟩ ⟶ endpointPoint (stage+1) ⟨0, Nat.succ_pos _⟩ :=
  ⟨PresheafSiteLift.Site.upFunctor.map (homOfLE (Nat.le_succ stage)), by
    apply receipt_ext (native domain) <;> rfl⟩

theorem motive_grows_at_every_stage (stage : Nat) :
    ¬ ∃ earlier : motive.obj (endpointPoint stage ⟨0, Nat.succ_pos _⟩),
      motive.map (stageStep stage) earlier = ULift.up ⟨stage+1, Nat.lt_succ_self _⟩ := by
  rintro ⟨earlier, same⟩
  exact (Nat.ne_of_lt earlier.down.isLt) (congrArg (fun term => term.down.val) same)

theorem J_returns_endpoint (point : (identityContext (native domain)).Elements) :
    result.val point = point.2.1.1.2 := J_endpoint_value (native domain) point

theorem J_independent_upper_lower : result =
    sectionCast (motive_roundtrip domain motive)
      (pullSection (lowerIdentityFunctor domain) (lowerMotive domain motive)
        (J domain.native (lowerMotive domain motive) (lowerMethod domain motive method))) :=
  J_comparison domain motive method

theorem J_material_value (stage : Nat) (term : Fin (stage+1)) :
    motiveReading.app (PresheafSiteLift.Site.upFunctor.obj stage)
      ⟨(endpointPoint stage term).2, result.val (endpointPoint stage term)⟩ =
      ContextualGraphUniverseLift.value (point := PresheafSiteLift.Site.upFunctor.obj stage)
        (ContextualGraphFamilyBodyControls.material stage term) :=
  congrArg (fun value => motiveReading.app (PresheafSiteLift.Site.upFunctor.obj stage)
    ⟨(endpointPoint stage term).2, value⟩) (J_returns_endpoint (endpointPoint stage term))

theorem J_material_is_nonconstant :
    ¬ Nonempty (Equal
      (motiveReading.app (PresheafSiteLift.Site.upFunctor.obj 1)
        ⟨(endpointPoint 1 ⟨0, by decide⟩).2, result.val (endpointPoint 1 ⟨0, by decide⟩)⟩)
      (motiveReading.app (PresheafSiteLift.Site.upFunctor.obj 1)
        ⟨(endpointPoint 1 ⟨1, by decide⟩).2, result.val (endpointPoint 1 ⟨1, by decide⟩)⟩)) := by
  rw [J_material_value, J_material_value]
  rintro ⟨same⟩
  exact (by decide : ¬ (1 : Nat) = 0)
    (ContextualGraphFamilyBodyControls.matching_preserves_zero 1 _ _
      (ContextualGraphUniverseLift.reflect same) rfl)

def parameter (stage : Nat) : (base unitBase).Elements :=
  (elementsUp unitBase).obj (ContextualGraphFamilyControls.parameter stage)

def positive_bodies_match :
    Equal
      (ContextualGraphMaterialFamilies.termValue (raise domain) (parameter 2) (ULift.up ⟨1, by decide⟩))
      (ContextualGraphMaterialFamilies.termValue (raise domain) (parameter 2) (ULift.up ⟨2, by decide⟩)) :=
  ContextualGraphUniverseLift.preserve
    (ContextualGraphFamilyBodyControls.terminalEquality 2 ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide))

theorem matching_does_not_form_upper_identity :
    ¬ ∃ element : Value (Upper (D := Nat)) (parameter 2).1,
      Nonempty (Member element (ContextualGraphFamilyBodyIdentity.identityCarrier (native domain)
        (parameter 2) (ULift.up ⟨1, by decide⟩) (ULift.up ⟨2, by decide⟩))) := by
  intro belongs
  have same := (ContextualGraphFamilyBodyIdentity.identity_material_nonempty_iff (native domain)
    (parameter 2) (ULift.up ⟨1, by decide⟩) (ULift.up ⟨2, by decide⟩)).mp belongs
  exact (by decide : ¬ (1 : Nat) = 2) (congrArg (fun term => term.down.val) same)

def reflexive_carrier_comparison (stage : Nat) (term : Fin (stage+1)) :
    Equal (ContextualGraphUniverseLift.value
      (ContextualGraphFamilyBodyIdentity.identityCarrier domain.native
        (ContextualGraphFamilyControls.parameter stage) term term))
      (ContextualGraphFamilyBodyIdentity.identityCarrier (native domain) (parameter stage)
        (ULift.up term) (ULift.up term)) :=
  identityCarrierComparison domain (parameter stage) (ULift.up term) (ULift.up term)

theorem J_computation : reindexSection (diagonal (native domain)) motive result = method :=
  J_beta (native domain) motive method

theorem J_substitution_with_retained_argument :
    reindexSection (identityReindex (projection (native domain)) (native domain)) motive
      (sectionCast (motive_roundtrip domain motive)
        (pullSection (lowerIdentityFunctor domain) (lowerMotive domain motive)
          (J domain.native (lowerMotive domain motive) (lowerMethod domain motive method)))) =
    J (ContextualSmallFamilyIdentity.reindex (native domain) (projection (native domain)))
      (ContextualSmallFamilyIdentity.reindex motive
        (identityReindex (projection (native domain)) (native domain)))
      (reindexMethod (projection (native domain)) (native domain) motive method) :=
  J_comparison_substitution domain motive method (projection (native domain))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftIdentityControls
