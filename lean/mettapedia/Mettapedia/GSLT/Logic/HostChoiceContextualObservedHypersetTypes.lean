import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetTriangle

/-!
# Actual dependent member types of the structured execution interpretation

The retained observed class and actual set coordinate form one parameter
presheaf over the original site. Actual set membership constructs its
small family and the arbitrary-argument selected-set body. Singleton of
the selected member gives a second genuine dependent body.

Sums, complete future products, discrete identity and contextual W are
constructed and classified by the full small-family universe. The native
product adjunction applies to arbitrary wider consumers. Pulling these
families back along the actual execution readout compares independently
formed source types and their complete sections, rather than only support.
Internal set values, external type codes and observed recipe provenance
remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HostChoiceContextualObservedHypersetTypes

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualHypersetModel HostChoiceContextualHypersetFamilyClosure
open ContextualCoalgebraLabelledGraph ContextualObservedCoalgebra
open HostChoiceContextualObservedHypersetTriangle

universe u v h
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}

theorem smallLambda_beta {P : D ⥤ Type v} (input : P.Elements ⥤ Type u)
    (output : input.Elements ⥤ Type u) {consumer : P.Elements ⥤ Type u}
    (operation : NatTrans (ContextualSmallFamilyTypeFormers.overArguments input consumer) output)
    (point : P.Elements) (value : consumer.obj point) (argument : input.obj point) :
    ContextualSmallFamilyTypeFormers.evaluateValue input output point
      ((ContextualSmallFamilyTypeFormers.piCurry input output operation).app point value) argument =
        operation.app ⟨point, argument⟩ value :=
  congrArg (fun map : NatTrans (ContextualSmallFamilyTypeFormers.overArguments input consumer) output =>
    map.app ⟨point, argument⟩ value)
    (ContextualSmallFamilyTypeFormers.pi_uncurry_curry input output operation)

variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (atomCoding : ArgumentCoding Atom)

abbrev parameters := structured source atoms worlds arrows atomCoding
abbrev parent := materialProjection source atoms worlds arrows atomCoding
noncomputable abbrev members := domain (parent source atoms worlds arrows atomCoding)

noncomputable def selectedSet : NaturalHom (ContextualSmallFamilyUniverse.total
    (members source atoms worlds arrows atomCoding)) sets :=
  argumentReading (parent source atoms worlds arrows atomCoding)

noncomputable def singletonOfSelected : NaturalHom (ContextualSmallFamilyUniverse.total
    (members source atoms worlds arrows atomCoding)) sets :=
  (selectedSet source atoms worlds arrows atomCoding).comp singletonSet

noncomputable abbrev selectedBody := body (parent source atoms worlds arrows atomCoding)
  (selectedSet source atoms worlds arrows atomCoding)

noncomputable abbrev singletonBody := body (parent source atoms worlds arrows atomCoding)
  (singletonOfSelected source atoms worlds arrows atomCoding)

noncomputable def memberCode : NaturalHom (parameters source atoms worlds arrows atomCoding)
    ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier (members source atoms worlds arrows atomCoding)

theorem memberCode_full_family : ContextualSmallFamilyUniverse.decodedFamily
    (memberCode source atoms worlds arrows atomCoding) = members source atoms worlds arrows atomCoding :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

noncomputable def actualMembers (point : (parameters source atoms worlds arrows atomCoding).Elements) :
    (members source atoms worlds arrows atomCoding).obj point ≃
      ActualMember ((ContextualSmallFamilyUniverse.elementMap (parent source atoms worlds arrows atomCoding)).obj point) :=
  memberDecoder _

theorem actualMembers_restriction {first second : (parameters source atoms worlds arrows atomCoding).Elements}
    (step : first ⟶ second) (code : (members source atoms worlds arrows atomCoding).obj first) :
    sets.map step.1 (actualMembers source atoms worlds arrows atomCoding first code).val =
      (actualMembers source atoms worlds arrows atomCoding second
        ((members source atoms worlds arrows atomCoding).map step code)).val :=
  memberDecoder_restriction_value ((ContextualSmallFamilyUniverse.elementMap
    (parent source atoms worlds arrows atomCoding)).map step) code

theorem selectedBody_member_iff (point : (members source atoms worlds arrows atomCoding).Elements)
    (child : sets.obj point.1.1) :
    Member point.1.1 child ((selectedSet source atoms worlds arrows atomCoding).app point.1.1
      ⟨point.1.2, point.2⟩) ↔
      Member point.1.1 child (actualMembers source atoms worlds arrows atomCoding point.1 point.2).val := Iff.rfl

theorem singletonBody_member_iff (point : (members source atoms worlds arrows atomCoding).Elements)
    (child : sets.obj point.1.1) :
    Member point.1.1 child ((singletonOfSelected source atoms worlds arrows atomCoding).app point.1.1
      ⟨point.1.2, point.2⟩) ↔
      (actualMembers source atoms worlds arrows atomCoding point.1 point.2).val = child :=
  member_singleton _ _ _

noncomputable def sumFamily := sigmaFamily (parent source atoms worlds arrows atomCoding)
  (selectedSet source atoms worlds arrows atomCoding)
noncomputable def productFamily := piFamily (parent source atoms worlds arrows atomCoding)
  (selectedSet source atoms worlds arrows atomCoding)
noncomputable def treeFamily := wFamily (parent source atoms worlds arrows atomCoding)
  (selectedSet source atoms worlds arrows atomCoding)
noncomputable def singletonProductFamily := piFamily (parent source atoms worlds arrows atomCoding)
  (singletonOfSelected source atoms worlds arrows atomCoding)

noncomputable def sumDecoder (point : (parameters source atoms worlds arrows atomCoding).Elements) :
    (sumFamily source atoms worlds arrows atomCoding).obj point ≃
      (Σ argument : (members source atoms worlds arrows atomCoding).obj point,
        (literalBody (parent source atoms worlds arrows atomCoding)
          (selectedSet source atoms worlds arrows atomCoding)).obj ⟨point, argument⟩) :=
  sigmaDecoder _ _ point

noncomputable def fullProductDecoder (point : (parameters source atoms worlds arrows atomCoding).Elements) :
    (productFamily source atoms worlds arrows atomCoding).obj point ≃
      (futureLiteralBody (parent source atoms worlds arrows atomCoding)
        (selectedSet source atoms worlds arrows atomCoding) point).sections :=
  piDecoder _ _ point

noncomputable def nativeProductDecoder (point : (parameters source atoms worlds arrows atomCoding).Elements) :
    WiderPresheafDependentFunctions.DependentSection (members source atoms worlds arrows atomCoding)
      (selectedBody source atoms worlds arrows atomCoding) point ≃
      (futureLiteralBody (parent source atoms worlds arrows atomCoding)
        (selectedSet source atoms worlds arrows atomCoding) point).sections :=
  nativePiDecoder _ _ point

noncomputable def productWholeSections : (productFamily source atoms worlds arrows atomCoding).sections ≃
    LiteralProducts (parent source atoms worlds arrows atomCoding) (selectedSet source atoms worlds arrows atomCoding) :=
  piSectionDecoder _ _

noncomputable def nativeProductHom (consumer : (parameters source atoms worlds arrows atomCoding).Elements ⥤ Type h) :
    WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over (members source atoms worlds arrows atomCoding) consumer)
      (selectedBody source atoms worlds arrows atomCoding) ≃
    WiderPresheafDependentFunctions.Hom consumer (productFamily source atoms worlds arrows atomCoding) :=
  piHomEquiv _ _ consumer

theorem nativeProduct_beta (consumer : (parameters source atoms worlds arrows atomCoding).Elements ⥤ Type h)
    (operation : WiderPresheafDependentFunctions.Hom
      (WiderPresheafDependentFunctions.over (members source atoms worlds arrows atomCoding) consumer)
      (selectedBody source atoms worlds arrows atomCoding)) :
    ContextualSmallFamilyNativeAdjunction.smallUncurry (members source atoms worlds arrows atomCoding)
      (selectedBody source atoms worlds arrows atomCoding)
      (nativeProductHom source atoms worlds arrows atomCoding consumer operation) = operation :=
  pi_beta _ _ consumer operation

theorem nativeProduct_eta (consumer : (parameters source atoms worlds arrows atomCoding).Elements ⥤ Type h)
    (operation : WiderPresheafDependentFunctions.Hom consumer (productFamily source atoms worlds arrows atomCoding)) :
    nativeProductHom source atoms worlds arrows atomCoding consumer
      (ContextualSmallFamilyNativeAdjunction.smallUncurry (members source atoms worlds arrows atomCoding)
        (selectedBody source atoms worlds arrows atomCoding) operation) = operation :=
  pi_eta _ _ consumer operation

theorem formed_whole_classifiers :
    ContextualSmallFamilyUniverse.decodedFamily (ContextualSmallFamilyUniverse.classifier
      (sumFamily source atoms worlds arrows atomCoding)) = sumFamily source atoms worlds arrows atomCoding ∧
    ContextualSmallFamilyUniverse.decodedFamily (ContextualSmallFamilyUniverse.classifier
      (productFamily source atoms worlds arrows atomCoding)) = productFamily source atoms worlds arrows atomCoding ∧
    ContextualSmallFamilyUniverse.decodedFamily (ContextualSmallFamilyUniverse.classifier
      (treeFamily source atoms worlds arrows atomCoding)) = treeFamily source atoms worlds arrows atomCoding :=
  ⟨ContextualSmallFamilyUniverse.decoded_classifier_eq _,
    ContextualSmallFamilyUniverse.decoded_classifier_eq _, ContextualSmallFamilyUniverse.decoded_classifier_eq _⟩

theorem source_member_triangle : domain (setReadout source) = ContextualSmallFamilyUniverse.substitutedFamily
    (members source atoms worlds arrows atomCoding) (structuredReadout source atoms worlds arrows atomCoding) := by
  rw [← structured_material_square source atoms worlds arrows atomCoding]
  exact member_formation_substitution _ _

theorem class_member_triangle : domain (classSetReadout source atoms worlds arrows atomCoding) =
    ContextualSmallFamilyUniverse.substitutedFamily (members source atoms worlds arrows atomCoding)
      (retain source atoms worlds arrows atomCoding) := by
  rw [← retain_material source atoms worlds arrows atomCoding]
  exact member_formation_substitution _ _

noncomputable def sourceProductComparison : NatTrans
    (ContextualSmallFamilyUniverse.substitutedFamily (productFamily source atoms worlds arrows atomCoding)
      (structuredReadout source atoms worlds arrows atomCoding))
    (freshPi (parent source atoms worlds arrows atomCoding) (selectedSet source atoms worlds arrows atomCoding)
      (structuredReadout source atoms worlds arrows atomCoding)) :=
  piSubstitution _ _ _

noncomputable def sourceProductInverse : NatTrans
    (freshPi (parent source atoms worlds arrows atomCoding) (selectedSet source atoms worlds arrows atomCoding)
      (structuredReadout source atoms worlds arrows atomCoding))
    (ContextualSmallFamilyUniverse.substitutedFamily (productFamily source atoms worlds arrows atomCoding)
      (structuredReadout source atoms worlds arrows atomCoding)) :=
  piSubstitutionInverse _ _ _

theorem sourceProduct_left : ContextualSmallFamilyTypeFormers.composeNat
    (sourceProductComparison source atoms worlds arrows atomCoding) (sourceProductInverse source atoms worlds arrows atomCoding) =
      ContextualSmallFamilyTypeFormers.identityNat (ContextualSmallFamilyUniverse.substitutedFamily
        (productFamily source atoms worlds arrows atomCoding) (structuredReadout source atoms worlds arrows atomCoding)) :=
  piSubstitution_left _ _ _

theorem sourceProduct_right : ContextualSmallFamilyTypeFormers.composeNat
    (sourceProductInverse source atoms worlds arrows atomCoding) (sourceProductComparison source atoms worlds arrows atomCoding) =
      ContextualSmallFamilyTypeFormers.identityNat (freshPi (parent source atoms worlds arrows atomCoding)
        (selectedSet source atoms worlds arrows atomCoding) (structuredReadout source atoms worlds arrows atomCoding)) :=
  piSubstitution_right _ _ _

noncomputable def sourceProductSections :
    (ContextualSmallFamilyUniverse.substitutedFamily (productFamily source atoms worlds arrows atomCoding)
      (structuredReadout source atoms worlds arrows atomCoding)).sections ≃
    (freshPi (parent source atoms worlds arrows atomCoding) (selectedSet source atoms worlds arrows atomCoding)
      (structuredReadout source atoms worlds arrows atomCoding)).sections :=
  piSubstitutionSections _ _ _

theorem source_sum_family : freshSigma (parent source atoms worlds arrows atomCoding)
    (selectedSet source atoms worlds arrows atomCoding) (structuredReadout source atoms worlds arrows atomCoding) =
      ContextualSmallFamilyUniverse.substitutedFamily (sumFamily source atoms worlds arrows atomCoding)
        (structuredReadout source atoms worlds arrows atomCoding) := sigma_substitution _ _ _

theorem source_tree_family : ContextualSmallFamilyUniverse.substitutedFamily
    (treeFamily source atoms worlds arrows atomCoding) (structuredReadout source atoms worlds arrows atomCoding) =
      freshW (parent source atoms worlds arrows atomCoding) (selectedSet source atoms worlds arrows atomCoding)
        (structuredReadout source atoms worlds arrows atomCoding) := w_substitution _ _ _

theorem identity_material_iff (left right : (members source atoms worlds arrows atomCoding).sections)
    (point : (parameters source atoms worlds arrows atomCoding).Elements) :
    Nonempty ((identityFamily (parent source atoms worlds arrows atomCoding) left right).obj point) ↔
      (actualMembers source atoms worlds arrows atomCoding point (left.val point)).val =
        (actualMembers source atoms worlds arrows atomCoding point (right.val point)).val :=
  identity_literal_values _ left right point

theorem actual_J_beta
    (motive : (ContextualSmallFamilyIdentity.identityContext (members source atoms worlds arrows atomCoding)).Elements ⥤ Type h)
    (method : (ContextualSmallFamilyIdentity.reindex motive
      (ContextualSmallFamilyIdentity.diagonal (members source atoms worlds arrows atomCoding))).sections) :
    ContextualSmallFamilyIdentity.reindexSection (ContextualSmallFamilyIdentity.diagonal
      (members source atoms worlds arrows atomCoding)) motive
      (ContextualSmallFamilyIdentity.J (members source atoms worlds arrows atomCoding) motive method) = method :=
  identity_J_beta _ motive method

theorem actual_W_initiality (target : (parameters source atoms worlds arrows atomCoding).Elements ⥤ Type u)
    (algebra : ContextualSmallFamilyWAlgebra.Algebra (members source atoms worlds arrows atomCoding)
      (selectedBody source atoms worlds arrows atomCoding) (target := target)) :
    ∃! operation : NatTrans (treeFamily source atoms worlds arrows atomCoding) target,
      ∀ point (node : ContextualSmallFamilyWPolynomial.At (members source atoms worlds arrows atomCoding)
        (selectedBody source atoms worlds arrows atomCoding) (treeFamily source atoms worlds arrows atomCoding) point),
        operation.app point (ContextualSmallFamilyWAlgebra.constructorValue (members source atoms worlds arrows atomCoding)
          (selectedBody source atoms worlds arrows atomCoding) point node) =
        algebra.app point (ContextualSmallFamilyWAction.mapValue (members source atoms worlds arrows atomCoding)
          (selectedBody source atoms worlds arrows atomCoding) operation point node) :=
  w_initiality _ _ target algebra

end Mettapedia.GSLT.HostChoiceContextualObservedHypersetTypes
