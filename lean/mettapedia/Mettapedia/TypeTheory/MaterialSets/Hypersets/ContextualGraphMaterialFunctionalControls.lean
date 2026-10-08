import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalSubstitution
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalApplication
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialObservedControls

/-!
# Growing observed compatible and incompatible material functions

The body is the actual index-bounded growing observed family. Identity and
occurrence-flipping sections are both compatible and have equal material
function graphs, while their native application receipts differ. The
sensitive section which sends one terminal receipt to a cycle is excluded
by the constructed compatible classifier.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalControls

open CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension
open ContextualGraphDiagrams ContextualRealizedGraphs ContextualGraphMaterialFamilies
open ContextualGraphMaterialProducts ContextualGraphMaterialFunctionalProducts
open ContextualGraphMaterialObservedControls
open PowerClassPresheafDescent.Controls ConstructiveObservedMaterialControls

def identityCertificate (point : parameters.Elements) :
    FullData domainFamily bodyFamily point.1 ⟨point.2, identityFunction.val point⟩ :=
  wholeData domainFamily bodyFamily identityFunction identityCompatible point

def compatibleIdentity : (compatibleNative domainFamily bodyFamily).sections :=
  classifySection domainFamily bodyFamily identityFunction identityCompatible

def identityLiteral : (literal (functionalPi domainFamily bodyFamily)).sections :=
  (sectionDecoder (functionalPi domainFamily bodyFamily)).symm compatibleIdentity

theorem identity_classified_at_every_stage (stage : Nat) :
    Nonempty ((compatibleNative domainFamily bodyFamily).obj (parameter stage)) :=
  ⟨compatibleIdentity.val (parameter stage)⟩

def flip : NaturalHom raw raw where
  app _ argument := ⟨argument.1, !argument.2⟩
  naturality _ _ := Prod.ext (Fin.ext rfl) rfl

def flipBody : bodyFamily.native.sections :=
  ⟨fun point => ⟨flip.app point.1 point.2.2, Nat.le_add_right _ _⟩, by
    intro first second step
    apply Subtype.ext
    have arguments : raw.map step.1 first.2.2 = second.2.2 :=
      eq_of_heq (Sigma.mk.inj_iff.mp step.2).2
    exact (flip.naturality step.1 first.2.2).trans (congrArg (flip.app second.1) arguments)⟩

def flipFunction : (nativeProduct domainFamily bodyFamily).sections :=
  ContextualGraphFamilyProducts.nativeLambda domainFamily.native bodyFamily.native flipBody

theorem flip_evaluation (point : parameters.Elements) (argument : domainFamily.native.obj point) :
    evaluated domainFamily bodyFamily point (flipFunction.val point) argument =
      ⟨flip.app point.1 argument, Nat.le_add_right _ _⟩ :=
  ContextualGraphMaterialSections.native_lambda_evaluation domainFamily bodyFamily flipBody point argument

def indexMatching (point : Stagesᵒᵖ) (first second : raw.obj point)
    (same : first.1.val = second.1.val) :
    Equal (ContextualObservedGraphControls.modelReadout.app point first)
      (ContextualObservedGraphControls.modelReadout.app point second) :=
  Equal.ofEq ((ContextualObservedGraphFamilies.literal_kernel worlds arrows dynamics atoms atomCoding
    point first second).mpr (equal_indices_observed point first second same))

def flipResult (point : parameters.Elements) (argument : domainFamily.native.obj point) :
    Equal (resultValue domainFamily bodyFamily point (flipFunction.val point) argument)
      (termValue domainFamily point argument) :=
  (Equal.ofEq (congrArg (termValue bodyFamily ((flatten domainFamily.native).obj ⟨point, argument⟩))
    (flip_evaluation point argument))).trans (indexMatching point.1 (flip.app point.1 argument) argument rfl)

def flipCompatible (point : parameters.Elements) :
    ApplicationCompatible domainFamily bodyFamily point (flipFunction.val point) :=
  fun first second same => (flipResult point first).trans (same.trans (flipResult point second).symm)

def compatibleFlip : (compatibleNative domainFamily bodyFamily).sections :=
  classifySection domainFamily bodyFamily flipFunction flipCompatible

def identityFlipPointwise (point : parameters.Elements) :
    PointwiseData domainFamily bodyFamily point (identityFunction.val point) (flipFunction.val point) := by
  intro future argument
  let next := futurePoint point future
  let step := futureStep point future
  have identityFuture := identityFunction.property step
  have flipFuture := flipFunction.property step
  exact (Equal.ofEq (congrArg (fun function => resultValue domainFamily bodyFamily next function argument)
    identityFuture)).trans
    ((Equal.ofEq (congrArg (termValue bodyFamily ((flatten domainFamily.native).obj ⟨next, argument⟩))
      (identity_evaluation next argument))).trans
      ((flipResult next argument).symm.trans
        (Equal.ofEq (congrArg (fun function => resultValue domainFamily bodyFamily next function argument)
          flipFuture)).symm))

def identityFlipMatching (point : parameters.Elements) :
    Equal (termValue (functionalPi domainFamily bodyFamily) point (compatibleIdentity.val point))
      (termValue (functionalPi domainFamily bodyFamily) point (compatibleFlip.val point)) :=
  graphFromPointwise domainFamily bodyFamily point (identityFunction.val point) (flipFunction.val point)
    (identityFlipPointwise point)

theorem identity_flip_whole_observation :
    (observe (functionalPi domainFamily bodyFamily)).mapSection compatibleIdentity =
      (observe (functionalPi domainFamily bodyFamily)).mapSection compatibleFlip :=
  (observed_section_kernel domainFamily bodyFamily compatibleIdentity compatibleFlip).mpr
    (fun point => ⟨identityFlipPointwise point⟩)

theorem compatible_receipts_distinct : compatibleIdentity.val (parameter 0) ≠ compatibleFlip.val (parameter 0) := by
  intro same
  let argument := stageValue 0 0 (by omega) false
  have evaluatedSame := congrArg
    (fun function : (compatibleNative domainFamily bodyFamily).obj (parameter 0) =>
      (evaluated domainFamily bodyFamily (parameter 0) function.val argument).val.2) same
  have left := congrArg (fun result : bodyFamily.native.obj ((flatten domainFamily.native).obj ⟨parameter 0, argument⟩) => result.val.2)
    (identity_evaluation (parameter 0) argument)
  have right := congrArg (fun result : bodyFamily.native.obj ((flatten domainFamily.native).obj ⟨parameter 0, argument⟩) => result.val.2)
    (flip_evaluation (parameter 0) argument)
  exact Bool.false_ne_true (left.symm.trans (evaluatedSame.trans right))

theorem incompatible_section_excluded :
    ¬ ∃ function : (compatibleNative domainFamily bodyFamily).obj (parameter 3),
      function.val = sensitiveFunction.val (parameter 3) := by
  rintro ⟨function, same⟩
  apply sensitive_not_material_compatible
  exact function.property.elim (fun certificate =>
    ⟨cast (congrArg (ApplicationCompatible domainFamily bodyFamily (parameter 3)) same)
      (currentData domainFamily bodyFamily (world 3) ⟨PUnit.unit, function.val⟩ certificate)⟩)

def actual_single_valued (stage : Nat) (argument firstResult secondResult : Value Stagesᵒᵖ (world stage))
    (first : Member (ContextualGraphOrderedPairs.orderedPair argument firstResult)
      (productElement domainFamily bodyFamily (parameter stage) (identityFunction.val (parameter stage))))
    (second : Member (ContextualGraphOrderedPairs.orderedPair argument secondResult)
      (productElement domainFamily bodyFamily (parameter stage) (identityFunction.val (parameter stage)))) :
    Equal firstResult secondResult :=
  singleValued domainFamily bodyFamily (parameter stage) (identityFunction.val (parameter stage))
    (identityCertificate (parameter stage)) argument firstResult secondResult first second

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialFunctionalControls
