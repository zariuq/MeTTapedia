import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedMemberSuccessorUniverse

/-!
# Successor decoding, comprehension and formation coherence

Raising parameter maps commutes with the actual inverse wrapper. The lower
and upper comprehension presheaves have explicitly inverse coordinate
maps. Transported dependent bodies therefore live on the genuine upper
comprehension, where upper type formers are independently constructed.
Sums, identity and W have whole decoded-family comparisons; products have
natural inverse maps and complete section comparisons.

The lifted lower recipe and a freshly formed upper recipe remain distinct.
These semantic laws do not introduce a code equation or identify the
fixed-site code successor with a material-set or site universe lift.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedMemberSuccessorCoherence

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualHypersetFamilyClosure
open HostChoiceContextualGeneratedMemberSuccessorUniverse

universe u v w
variable {D : Type u} [Category.{u} D]

abbrev LowerCode (parameters : LowerParameters.{u,v} (D := D)) :=
  HostChoiceContextualGeneratedHypersetFamilies.Code.{u,v} parameters

def lowerFamily {parameters : LowerParameters.{u,v} (D := D)} (code : LowerCode parameters) :
    parameters.Elements ⥤ Type u := HostChoiceContextualGeneratedHypersetFamilies.decodeFamily code

def changeUp {parameters other : LowerParameters.{u,v} (D := D)} (change : NaturalHom other parameters) :
    NaturalHom (parametersUp other) (parametersUp parameters) where
  app point value := ULift.up (change.app point value.down)
  naturality step value := congrArg ULift.up (change.naturality step value.down)

theorem change_down_square {parameters other : LowerParameters.{u,v} (D := D)}
    (change : NaturalHom other parameters) :
    (changeUp change).comp (parametersDown parameters) = (parametersDown other).comp change := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem changeUp_id (parameters : LowerParameters.{u,v} (D := D)) :
    changeUp (ContextualSmallMapConstructions.identity parameters) =
      ContextualSmallMapConstructions.identity (parametersUp parameters) := by
  apply NaturalHom.ext
  intro _ value
  cases value
  rfl

theorem changeUp_comp {parameters other third : LowerParameters.{u,v} (D := D)}
    (earlier : NaturalHom third other) (later : NaturalHom other parameters) :
    changeUp (earlier.comp later) = (changeUp earlier).comp (changeUp later) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem lift_substitution_family {parameters other : LowerParameters.{u,v} (D := D)}
    (code : LowerCode parameters) (change : NaturalHom other parameters) :
    decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.substitute code change)) =
      decodeFamily (substitute (liftCode code) (changeUp change)) := by
  change ContextualSmallFamilyUniverse.substitutedFamily
      (ContextualSmallFamilyUniverse.substitutedFamily (lowerFamily code) change) (parametersDown other) =
    ContextualSmallFamilyUniverse.substitutedFamily
      (ContextualSmallFamilyUniverse.substitutedFamily (lowerFamily code) (parametersDown parameters)) (changeUp change)
  rw [ContextualSmallFamilyUniverse.substitutedFamily_comp,
    ContextualSmallFamilyUniverse.substitutedFamily_comp, change_down_square]

def substitutionSections {parameters other : LowerParameters.{u,v} (D := D)}
    (code : LowerCode parameters) (change : NaturalHom other parameters) :
    (decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.substitute code change))).sections ≃
      (decodeFamily (substitute (liftCode code) (changeUp change))).sections :=
  ContextualSmallFamilyUniverse.typeEqualityEquiv
    (congrArg (fun family : (parametersUp other).Elements ⥤ Type u =>
      (family.sections : Type ((max (u+1) v)+1))) (lift_substitution_family code change))

theorem sectionEqualityEquiv_value {E : Type w} [Category.{u} E] {first second : E ⥤ Type u}
    (same : first = second) (term : first.sections) (point : E) :
    HEq ((ContextualSmallFamilyUniverse.typeEqualityEquiv
      (congrArg (fun family : E ⥤ Type u => (family.sections : Type (max u w))) same) term).val point)
      (term.val point) := by
  cases same
  rfl

theorem piFamilyEquality_value {base : D ⥤ Type w} (domain : base.Elements ⥤ Type u)
    {first second : domain.Elements ⥤ Type u} (same : first = second) (point : base.Elements)
    (term : (ContextualSmallFamilyTypeFormers.pi domain first).obj point)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain domain point).Elements) :
    HEq (((familyEqHom (congrArg (ContextualSmallFamilyTypeFormers.pi domain) same)).app point term).val argument)
      (term.val argument) := by
  cases same
  rfl

theorem piSectionFamilyEquality_value {base : D ⥤ Type w} (domain : base.Elements ⥤ Type u)
    {first second : domain.Elements ⥤ Type u} (same : first = second)
    (term : (ContextualSmallFamilyTypeFormers.pi domain first).sections) (point : base.Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain domain point).Elements) :
    HEq (((ContextualSmallFamilyUniverse.typeEqualityEquiv
      (congrArg (fun family : base.Elements ⥤ Type u => (family.sections : Type (max u w)))
        (congrArg (ContextualSmallFamilyTypeFormers.pi domain) same)) term).val point).val argument)
      ((term.val point).val argument) := by
  cases same
  rfl

theorem substitutionSections_value {parameters other : LowerParameters.{u,v} (D := D)}
    (code : LowerCode parameters) (change : NaturalHom other parameters)
    (term : (decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.substitute code change))).sections)
    (point : (parametersUp other).Elements) :
    HEq ((substitutionSections code change term).val point) (term.val point) :=
  sectionEqualityEquiv_value (lift_substitution_family code change) term point

variable {parameters : LowerParameters.{u,v} (D := D)}

def comprehensionDown (family : parameters.Elements ⥤ Type u) :
    NaturalHom (ContextualSmallFamilyUniverse.total (familyUp family))
      (parametersUp (ContextualSmallFamilyUniverse.total family)) :=
  (ContextualSmallFamilyComprehension.totalChange family (parametersDown parameters)).comp
    (parametersRaise (ContextualSmallFamilyUniverse.total family))

def comprehensionUp (family : parameters.Elements ⥤ Type u) :
    NaturalHom (parametersUp (ContextualSmallFamilyUniverse.total family))
      (ContextualSmallFamilyUniverse.total (familyUp family)) where
  app _ receipt := ⟨ULift.up receipt.down.1, receipt.down.2⟩
  naturality _ _ := rfl

theorem comprehension_down_up (family : parameters.Elements ⥤ Type u) :
    (comprehensionDown family).comp (comprehensionUp family) =
      ContextualSmallMapConstructions.identity (ContextualSmallFamilyUniverse.total (familyUp family)) := by
  apply NaturalHom.ext
  intro _ receipt
  rcases receipt with ⟨⟨parameter⟩, argument⟩
  rfl

theorem comprehension_up_down (family : parameters.Elements ⥤ Type u) :
    (comprehensionUp family).comp (comprehensionDown family) =
      ContextualSmallMapConstructions.identity (parametersUp (ContextualSmallFamilyUniverse.total family)) := by
  apply NaturalHom.ext
  intro _ receipt
  rcases receipt with ⟨⟨parameter, argument⟩⟩
  rfl

theorem comprehension_projection (family : parameters.Elements ⥤ Type u) :
    (comprehensionDown family).comp (changeUp (ContextualSmallFamilyUniverse.projection family)) =
      (ContextualSmallFamilyUniverse.projection (familyUp family)).comp
        (ContextualSmallMapConstructions.identity (parametersUp parameters)) := by
  apply NaturalHom.ext
  intro _ _
  rfl

variable (input : LowerCode parameters)
variable (output : LowerCode.{u,v} (ContextualSmallFamilyUniverse.total (lowerFamily input)))

def liftBody : Code.{u,v} (ContextualSmallFamilyUniverse.total (decodeFamily (liftCode input))) :=
  substitute (liftCode output) (comprehensionDown (lowerFamily input))

theorem liftBody_family : decodeFamily (liftBody input output) =
    ContextualSmallFamilyUniverse.substitutedFamily (lowerFamily output)
      (ContextualSmallFamilyComprehension.totalChange (lowerFamily input) (parametersDown parameters)) := by
  change ContextualSmallFamilyUniverse.substitutedFamily
    (ContextualSmallFamilyUniverse.substitutedFamily (lowerFamily output)
      (parametersDown (ContextualSmallFamilyUniverse.total (lowerFamily input))))
    (comprehensionDown (lowerFamily input)) = _
  rw [ContextualSmallFamilyUniverse.substitutedFamily_comp]
  apply congrArg (ContextualSmallFamilyUniverse.substitutedFamily (lowerFamily output))
  apply NaturalHom.ext
  intro _ _
  rfl

theorem indexed_body_comparison :
    ContextualSmallFamilyComprehension.indexedBody (decodeFamily (liftCode input)) (decodeFamily (liftBody input output)) =
      ContextualSmallFamilyTypeFormerCoherence.bodyUnder (parametersDown parameters) (lowerFamily input)
        (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output)) := by
  rw [liftBody_family]
  exact ContextualSmallFamilyComprehension.indexedBody_substitution _ _ _

def upperSigma : Code (parametersUp parameters) := sigmaCode (liftCode input) (liftBody input output)
def upperPi : Code (parametersUp parameters) := piCode (liftCode input) (liftBody input output)
noncomputable def upperW : Code (parametersUp parameters) := wCode (liftCode input) (liftBody input output)

theorem sigma_family_comparison : decodeFamily (upperSigma input output) =
    decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.sigmaCode input output)) := by
  change ContextualSmallFamilyTypeFormers.sigma _ _ = _
  rw [indexed_body_comparison]
  exact ContextualSmallFamilyTypeFormerCoherence.sigma_substitution _ _ _

theorem w_family_comparison :
    decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.wCode input output)) =
      decodeFamily (upperW input output) := by
  change _ = ContextualSmallFamilyWTypes.w _ _
  rw [indexed_body_comparison]
  exact ContextualSmallFamilyWSubstitutionCoherence.w_substitution_eq _ _ _

theorem upperPi_family_eq : decodeFamily (upperPi input output) =
    ContextualSmallFamilyTypeFormers.pi (familyUp (lowerFamily input))
      (ContextualSmallFamilyTypeFormerCoherence.bodyUnder (parametersDown parameters) (lowerFamily input)
        (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output))) :=
  congrArg (ContextualSmallFamilyTypeFormers.pi (familyUp (lowerFamily input)))
    (indexed_body_comparison input output)

def piComparison : NatTrans
    (decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.piCode input output)))
    (decodeFamily (upperPi input output)) :=
  ContextualSmallFamilyTypeFormers.composeNat
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution (parametersDown parameters) (lowerFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output)))
    (familyEqHom (upperPi_family_eq input output).symm)

def piComparisonInverse : NatTrans (decodeFamily (upperPi input output))
    (decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.piCode input output))) :=
  ContextualSmallFamilyTypeFormers.composeNat
    (familyEqHom (upperPi_family_eq input output))
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitutionInverse (parametersDown parameters) (lowerFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output)))

set_option maxHeartbeats 1000000 in
theorem piComparison_value (point : (parametersUp parameters).Elements)
    (term : (decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.piCode input output))).obj point)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain (decodeFamily (liftCode input)) point).Elements) :
    HEq (((piComparison input output).app point term).val argument)
      (term.val ((ContextualSmallFamilyTypeFormerCoherence.futureArgumentChange
        (parametersDown parameters) (lowerFamily input) point).obj argument)) :=
  (piFamilyEquality_value (familyUp (lowerFamily input))
    (indexed_body_comparison input output).symm point
    ((ContextualSmallFamilyTypeFormerCoherence.piSubstitution (parametersDown parameters) (lowerFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output))).app point term)
    argument).trans
      (ContextualSmallFamilyTypeFormerCoherence.productComparison_value
        (parametersDown parameters) (lowerFamily input)
        (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output)) point term argument)

theorem piComparison_left : ContextualSmallFamilyTypeFormers.composeNat
    (piComparison input output) (piComparisonInverse input output) =
      ContextualSmallFamilyTypeFormers.identityNat
        (decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.piCode input output))) :=
  inverseAfterFamilyEquality (upperPi_family_eq input output) _ _
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution_left (parametersDown parameters) (lowerFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output)))

theorem piComparison_right : ContextualSmallFamilyTypeFormers.composeNat
    (piComparisonInverse input output) (piComparison input output) =
      ContextualSmallFamilyTypeFormers.identityNat (decodeFamily (upperPi input output)) :=
  equalityAfterInverse (upperPi_family_eq input output) _ _
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution_right (parametersDown parameters) (lowerFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output)))

def piSectionComparison :
    (decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.piCode input output))).sections ≃
      (decodeFamily (upperPi input output)).sections :=
  (ContextualSmallFamilyTypeFormerCoherence.productSectionComparison (parametersDown parameters) (lowerFamily input)
    (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output))).trans
    (ContextualSmallFamilyUniverse.typeEqualityEquiv
      (congrArg (fun family : (parametersUp parameters).Elements ⥤ Type u =>
        (family.sections : Type ((max (u+1) v)+1))) (upperPi_family_eq input output).symm))

set_option maxHeartbeats 1000000 in
theorem piSectionComparison_value
    (term : (decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.piCode input output))).sections)
    (point : (parametersUp parameters).Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain (decodeFamily (liftCode input)) point).Elements) :
    HEq (((piSectionComparison input output term).val point).val argument)
      ((term.val point).val ((ContextualSmallFamilyTypeFormerCoherence.futureArgumentChange
        (parametersDown parameters) (lowerFamily input) point).obj argument)) :=
  (piSectionFamilyEquality_value (familyUp (lowerFamily input))
    (indexed_body_comparison input output).symm
    (ContextualSmallFamilyTypeFormerCoherence.productSectionComparison
      (parametersDown parameters) (lowerFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output)) term)
    point argument).trans
      (ContextualSmallFamilyTypeFormerCoherence.productComparison_value
        (parametersDown parameters) (lowerFamily input)
        (ContextualSmallFamilyComprehension.indexedBody (lowerFamily input) (lowerFamily output))
        point (term.val point) argument)

def upperIdentity (left right : (lowerFamily input).sections) : Code (parametersUp parameters) :=
  identityCode (liftCode input) (sectionEquiv input left) (sectionEquiv input right)

theorem identity_family_comparison (left right : (lowerFamily input).sections) :
    decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.identityCode input left right)) =
      decodeFamily (upperIdentity input left right) :=
  ContextualSmallFamilyIdentity.identityFamily_substitution _ _ _ _

theorem sigma_recipes_distinct :
    liftCode (HostChoiceContextualGeneratedHypersetFamilies.sigmaCode input output) ≠ upperSigma input output := by
  intro same
  have heads := congrArg (fun code : Code (parametersUp parameters) => (origin code).isSome) same
  change true = false at heads
  cases heads

theorem pi_recipes_distinct :
    liftCode (HostChoiceContextualGeneratedHypersetFamilies.piCode input output) ≠ upperPi input output := by
  intro same
  have heads := congrArg (fun code : Code (parametersUp parameters) => (origin code).isSome) same
  change true = false at heads
  cases heads

theorem w_recipes_distinct :
    liftCode (HostChoiceContextualGeneratedHypersetFamilies.wCode input output) ≠ upperW input output := by
  intro same
  have heads := congrArg (fun code : Code (parametersUp parameters) => (origin code).isSome) same
  change true = false at heads
  cases heads

theorem identity_recipes_distinct (left right : (lowerFamily input).sections) :
    liftCode (HostChoiceContextualGeneratedHypersetFamilies.identityCode input left right) ≠ upperIdentity input left right := by
  intro same
  have heads := congrArg (fun code : Code (parametersUp parameters) => (origin code).isSome) same
  change true = false at heads
  cases heads

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedMemberSuccessorCoherence
