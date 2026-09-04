import Mettapedia.TypeTheory.UniversalDependentFamilyDescent

/-!
# Joint observation and dependent-family descent

Several individually lossy observations may jointly retain every source
distinction.  This module states that boundary without privileging one view.

For an arbitrary observation, its compatible image consists only of target
views which actually arise from a source.  The induced source-to-image map is
split surjective.  It is exact precisely when the observation is injective,
and every dependent family descends through it precisely at the same
boundary.

An indexed family of observations is jointly separating when its combined
dependent-function observation is injective.  Hence all source-indexed
families descend to the compatible joint view exactly when the observations
are jointly separating.  Individual observations need not be injective.

This gives a non-collapse criterion for plural semantic faces.  It does not
claim that every family of views is jointly conservative, that compatible
views fill the unrestricted product of targets, or that a jointly separating
family supplies an object-language type theory without substitution and
naturality laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.JointObservationDependentDescent

open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.IdentityObservationComparison
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.UniversalDependentFamilyDescent

universe uSource uTarget uIndex uFibre

/-! ## The compatible image of one observation -/

/-- The target values which are genuinely realized by an observation. -/
def CompatibleImage {Source : Type uSource} {Target : Type uTarget}
    (observe : Source -> Target) : Type uTarget :=
  { target : Target // ∃ source, observe source = target }

/-- Every observation is split surjective onto its compatible image.  The
representative is selected only from the existence witness carried by the
image element. -/
noncomputable def imageReadout
    {Source : Type uSource} {Target : Type uTarget}
    (observe : Source -> Target) :
    SplitReadout Source (CompatibleImage observe) where
  observe source := ⟨observe source, ⟨source, rfl⟩⟩
  representative target := Classical.choose target.property
  observe_representative target := by
    change
      (⟨observe (Classical.choose target.property),
          ⟨Classical.choose target.property, rfl⟩⟩ :
          CompatibleImage observe) =
        target
    apply Subtype.ext
    exact Classical.choose_spec target.property

/-- Injectivity is unchanged by restricting the codomain to the compatible
image. -/
theorem imageReadout_faithful_iff_injective
    {Source : Type uSource} {Target : Type uTarget}
    (observe : Source -> Target) :
    (imageReadout observe).Faithful <-> Function.Injective observe := by
  constructor
  · intro faithful left right sameObservation
    apply faithful
    change
      (⟨observe left, left, rfl⟩ : CompatibleImage observe) =
        ⟨observe right, right, rfl⟩
    exact Subtype.ext sameObservation
  · intro injective left right sameImage
    apply injective
    change
      (⟨observe left, left, rfl⟩ : CompatibleImage observe) =
        ⟨observe right, right, rfl⟩ at sameImage
    exact congrArg Subtype.val sameImage

/-- Exactness of the compatible-image readout is exactly injectivity of the
original observation.  Surjectivity alone was supplied by image
compatibility. -/
theorem imageReadout_exact_iff_injective
    {Source : Type uSource} {Target : Type uTarget}
    (observe : Source -> Target) :
    (imageReadout observe).Exact <-> Function.Injective observe := by
  rw [(imageReadout observe).exact_iff_faithful]
  exact imageReadout_faithful_iff_injective observe

/-- Every dependent family descends to compatible observations exactly when
the observation separates source values. -/
theorem image_allFamiliesDescend_iff_injective
    {Source : Type uSource} {Target : Type uTarget}
    (observe : Source -> Target) :
    AllFamiliesDescend.{uSource, uTarget, uFibre}
        (imageReadout observe) <->
      Function.Injective observe := by
  rw [<- exact_iff_allFamiliesDescend.{uSource,
    uTarget, uFibre} (imageReadout observe)]
  exact imageReadout_exact_iff_injective observe

/-! ## Indexed families of observations -/

/-- Heterogeneous observations of one source carrier. -/
structure ObservationFamily (Source : Type uSource) where
  Index : Type uIndex
  Target : Index -> Type uTarget
  observe : (index : Index) -> Source -> Target index

namespace ObservationFamily

variable {Source : Type uSource}

/-- The joint observation retains every indexed view at once. -/
def joint (family : ObservationFamily.{uSource, uIndex, uTarget} Source) :
    Source -> ((index : family.Index) -> family.Target index) :=
  fun source index => family.observe index source

/-- The observation family is jointly separating when equal views at every
index force equality of their common source. -/
def JointlySeparating
    (family : ObservationFamily.{uSource, uIndex, uTarget} Source) : Prop :=
  Function.Injective family.joint

/-- A single selected observation separates the source. -/
def SeparatesAt
    (family : ObservationFamily.{uSource, uIndex, uTarget} Source)
    (index : family.Index) : Prop :=
  Function.Injective (family.observe index)

/-- The split readout into jointly compatible views.  Its target contains
only view families realized by one common source. -/
noncomputable def compatibleReadout
    (family : ObservationFamily.{uSource, uIndex, uTarget} Source) :
    SplitReadout Source (CompatibleImage family.joint) :=
  imageReadout family.joint

/-- One individually separating observation is sufficient for joint
separation; the other observations may remain lossy. -/
theorem jointlySeparating_of_separatesAt
    (family : ObservationFamily.{uSource, uIndex, uTarget} Source)
    (index : family.Index) (separates : family.SeparatesAt index) :
    family.JointlySeparating := by
  intro left right sameJoint
  apply separates
  exact congrFun sameJoint index

/-- Exactness of the compatible joint view is precisely joint separation. -/
theorem compatibleReadout_exact_iff_jointlySeparating
    (family : ObservationFamily.{uSource, uIndex, uTarget} Source) :
    family.compatibleReadout.Exact <-> family.JointlySeparating :=
  imageReadout_exact_iff_injective family.joint

/-- **Joint dependent-descent criterion.**  Arbitrary source-indexed families
descend through the compatible family of views exactly when those views
jointly separate source values. -/
theorem allFamiliesDescend_iff_jointlySeparating
    (family : ObservationFamily.{uSource, uIndex, uTarget} Source) :
    AllFamiliesDescend.{uSource,
        max uIndex uTarget, uFibre}
        family.compatibleReadout <->
      family.JointlySeparating := by
  exact image_allFamiliesDescend_iff_injective family.joint

/-- Exact comparison of ordinary source equality reaches the same joint
separation boundary. -/
theorem ordinaryIdentityExact_iff_jointlySeparating
    (family : ObservationFamily.{uSource, uIndex, uTarget} Source) :
    (ordinaryIdentityComparison family.compatibleReadout).Exact <->
      family.JointlySeparating := by
  rw [ordinaryIdentityComparison_exact_iff_readout_exact]
  exact family.compatibleReadout_exact_iff_jointlySeparating

/-- Jointly separating endpoint views do not by themselves collapse
proof-relevant identity routes.  Exact comparison of a route family with
equality of compatible joint views additionally requires route UIP. -/
theorem routeComparison_exact_iff_jointlySeparating_and_routeUIP
    {layer : Layer.{uSource, uFibre} Source}
    (reflects : EndpointReflection layer)
    (family : ObservationFamily.{uSource, uIndex, uTarget} Source) :
    (ofEndpointReflection reflects family.compatibleReadout.observe).Exact <->
      family.JointlySeparating ∧ RouteUIP layer := by
  rw [splitReadout_exactComparison_iff reflects family.compatibleReadout]
  exact and_congr
    family.compatibleReadout_exact_iff_jointlySeparating Iff.rfl

end ObservationFamily

/-! ## Positive and adversarial controls -/

namespace Canary

open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

inductive Coordinate where
  | left
  | right
deriving DecidableEq, Repr

/-- The two coordinate projections of a Boolean pair. -/
def coordinates : ObservationFamily (Bool × Bool) where
  Index := Coordinate
  Target _ := Bool
  observe
    | .left => Prod.fst
    | .right => Prod.snd

theorem coordinates_left_not_separating :
    ¬ coordinates.SeparatesAt .left := by
  intro separates
  have same : (false, false) = (false, true) := separates rfl
  exact Bool.false_ne_true (congrArg Prod.snd same)

theorem coordinates_right_not_separating :
    ¬ coordinates.SeparatesAt .right := by
  intro separates
  have same : (false, false) = (true, false) := separates rfl
  exact Bool.false_ne_true (congrArg Prod.fst same)

/-- Neither coordinate is faithful alone, but together they separate every
Boolean pair. -/
theorem coordinates_jointlySeparating : coordinates.JointlySeparating := by
  intro first second sameViews
  apply Prod.ext
  · exact congrFun sameViews .left
  · exact congrFun sameViews .right

theorem coordinates_allFamiliesDescend :
    AllFamiliesDescend.{0, 0, uFibre} coordinates.compatibleReadout := by
  exact
    (ObservationFamily.allFamiliesDescend_iff_jointlySeparating
      coordinates).2 coordinates_jointlySeparating

/-- Repeating one lossy coordinate does not create joint faithfulness. -/
def duplicateLeft : ObservationFamily (Bool × Bool) where
  Index := Coordinate
  Target _ := Bool
  observe _ := Prod.fst

theorem duplicateLeft_not_jointlySeparating :
    ¬ duplicateLeft.JointlySeparating := by
  intro separates
  have sameViews : duplicateLeft.joint (false, false) =
      duplicateLeft.joint (false, true) := by
    funext coordinate
    cases coordinate <;> rfl
  have same := separates sameViews
  exact Bool.false_ne_true (congrArg Prod.snd same)

theorem duplicateLeft_not_allFamiliesDescend :
    ¬ AllFamiliesDescend.{0, 0, uFibre}
        duplicateLeft.compatibleReadout := by
  rw [ObservationFamily.allFamiliesDescend_iff_jointlySeparating
    duplicateLeft]
  exact duplicateLeft_not_jointlySeparating

/-- Extensional behavior and a retained route/provenance tag as two views of
the route-sensitive simple function carrier. -/
def behaviorAndRoute :
    ObservationFamily simpleRouteSensitive.Function where
  Index := Coordinate
  Target _ := Bool
  observe
    | .left => simpleBehavior
    | .right => simpleRouteTag

theorem behaviorAndRoute_behavior_not_separating :
    ¬ behaviorAndRoute.SeparatesAt .left := by
  intro separates
  have same : (false, false) = (false, true) := separates rfl
  exact Bool.false_ne_true (congrArg Prod.snd same)

theorem behaviorAndRoute_route_not_separating :
    ¬ behaviorAndRoute.SeparatesAt .right := by
  intro separates
  have same : (false, false) = (true, false) := separates rfl
  exact Bool.false_ne_true (congrArg Prod.fst same)

/-- The extensional and operational views jointly reconstruct the carrier
without identifying the two roles. -/
theorem behaviorAndRoute_jointlySeparating :
    behaviorAndRoute.JointlySeparating := by
  intro first second sameViews
  apply Prod.ext
  · exact congrFun sameViews .left
  · exact congrFun sameViews .right

theorem behaviorAndRoute_allFamiliesDescend :
    AllFamiliesDescend.{0, 0, uFibre}
        behaviorAndRoute.compatibleReadout := by
  exact
    (ObservationFamily.allFamiliesDescend_iff_jointlySeparating
      behaviorAndRoute).2
        behaviorAndRoute_jointlySeparating

/-! ### Joint endpoints still do not erase plural routes -/

open Mettapedia.TypeTheory.IdentityRouteCapabilities.Canary

/-- The sole Unit endpoint is perfectly observed. -/
def unitView : ObservationFamily Unit where
  Index := Unit
  Target _ := Unit
  observe _ := id

theorem unitView_jointlySeparating : unitView.JointlySeparating := by
  intro first second _sameViews
  exact Subsingleton.elim first second

/-- The endpoint observation is jointly separating, but the plural route
layer has two distinct self-routes and therefore is not represented exactly
by observed equality. -/
theorem unitView_pluralIdentity_not_exact :
    ¬ (ofEndpointReflection reflectedPlural_reflects
      unitView.compatibleReadout.observe).Exact := by
  rw [ObservationFamily.routeComparison_exact_iff_jointlySeparating_and_routeUIP
    reflectedPlural_reflects unitView]
  intro exact
  exact reflectedPlural_not_uip exact.2

/-- Paired control: plural views can be jointly sufficient, while duplicated
lossy views remain insufficient. -/
theorem jointObservation_boundary :
    (¬ coordinates.SeparatesAt .left) ∧
      (¬ coordinates.SeparatesAt .right) ∧
      coordinates.JointlySeparating ∧
      AllFamiliesDescend.{0, 0, uFibre} coordinates.compatibleReadout ∧
      (¬ duplicateLeft.JointlySeparating) ∧
      (¬ AllFamiliesDescend.{0, 0, uFibre}
        duplicateLeft.compatibleReadout) ∧
      (¬ behaviorAndRoute.SeparatesAt .left) ∧
      (¬ behaviorAndRoute.SeparatesAt .right) ∧
      behaviorAndRoute.JointlySeparating ∧
      AllFamiliesDescend.{0, 0, uFibre}
        behaviorAndRoute.compatibleReadout ∧
      unitView.JointlySeparating ∧
      (¬ (ofEndpointReflection reflectedPlural_reflects
        unitView.compatibleReadout.observe).Exact) :=
  ⟨coordinates_left_not_separating,
    coordinates_right_not_separating,
    coordinates_jointlySeparating,
    coordinates_allFamiliesDescend,
    duplicateLeft_not_jointlySeparating,
    duplicateLeft_not_allFamiliesDescend,
    behaviorAndRoute_behavior_not_separating,
    behaviorAndRoute_route_not_separating,
    behaviorAndRoute_jointlySeparating,
    behaviorAndRoute_allFamiliesDescend,
    unitView_jointlySeparating,
    unitView_pluralIdentity_not_exact⟩

end Canary

#print axioms imageReadout_faithful_iff_injective
#print axioms imageReadout_exact_iff_injective
#print axioms image_allFamiliesDescend_iff_injective
#print axioms ObservationFamily.allFamiliesDescend_iff_jointlySeparating
#print axioms ObservationFamily.ordinaryIdentityExact_iff_jointlySeparating
#print axioms ObservationFamily.routeComparison_exact_iff_jointlySeparating_and_routeUIP
#print axioms Canary.coordinates_allFamiliesDescend
#print axioms Canary.duplicateLeft_not_allFamiliesDescend
#print axioms Canary.behaviorAndRoute_allFamiliesDescend
#print axioms Canary.unitView_pluralIdentity_not_exact
#print axioms Canary.jointObservation_boundary

end Mettapedia.TypeTheory.JointObservationDependentDescent
