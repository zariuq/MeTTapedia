import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedEnclosure
import Mettapedia.TypeTheory.ContextualSmallFamilyUniverseCoherence

/-!
# Generated material members classified by the actual future-family universe

The enlarged material comprehension is naturally isomorphic to the
pullback of the constructed universal small family. Its maps decode and
encode actual members, retaining their parameter. Thus original-small
recursive recipes, complete future codes, and the larger material
enclosure participate in one proved interpretation.

The classifier describes a whole native family. Its material dictionary
and generation recipe remain explicit additional data; neither is
reconstructed from a bare present carrier or a mere smallness assertion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedClassification

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualAuthoredMaterialFamilies ContextualAuthoredGeneratedFamilies
open ContextualSmallFamilyUniverse

universe u v w
variable {D : Type u} [Category.{u} D]
variable {worlds : ArgumentCoding D} {arrows : (first second : D) → ArgumentCoding (first ⟶ second)}
variable {seeds : (base : D ⥤ Type (max u v)) → Type (max (u+1) v)}
variable {seedModel : (base : D ⥤ Type (max u v)) → seeds base → Family base}
variable {base : D ⥤ Type (max u v)}
variable (code : ContextualAuthoredGeneratedFamilies.Code worlds arrows seeds seedModel base)

def classifier : NaturalHom base universeFamily := ContextualSmallFamilyUniverse.classifier code.decode.native

theorem decoded_classifier : decodedFamily (classifier code) = code.decode.native :=
  decoded_classifier_eq code.decode.native

abbrev enlargedFamily :=
  ContextualFamilyEnlargement.members.{u,max (u+1) (v+1)} code.decode.native code.decode.models

abbrev materialTotal := total (enlargedFamily code)

def decodeTotal : NaturalHom (materialTotal code) code.decode.extension where
  app _ receipt := ⟨receipt.1,
    ((ContextualFamilyEnlargement.model (code.decode.models _)).decode receipt.2).down⟩
  naturality {first second} step receipt := by
    change (⟨base.map step receipt.1,
      code.decode.native.map (CategoryOfElements.homMk _ _ step rfl)
        (((ContextualFamilyEnlargement.model (code.decode.models ⟨first, receipt.1⟩)).decode receipt.2).down)⟩ :
        TotalAt code.decode.native second) =
      ⟨base.map step receipt.1,
        ((ContextualFamilyEnlargement.model (code.decode.models ⟨second, base.map step receipt.1⟩)).decode
          ((enlargedFamily code).map (CategoryOfElements.homMk _ _ step rfl) receipt.2)).down⟩
    exact congrArg (fun term => (⟨base.map step receipt.1, term⟩ : TotalAt code.decode.native second))
      (congrArg ULift.down
        (ContextualFamilyEnlargement.member_decode.{u,max (u+1) (v+1)} code.decode.native code.decode.models
          (CategoryOfElements.homMk (F := base) ⟨first, receipt.1⟩
            ⟨second, base.map step receipt.1⟩ step rfl) receipt.2)).symm

def encodeTotal : NaturalHom code.decode.extension (materialTotal code) where
  app _ receipt := ⟨receipt.1,
    (ContextualFamilyEnlargement.model (code.decode.models _)).decode.symm (ULift.up receipt.2)⟩
  naturality {first second} step receipt := by
    change (⟨base.map step receipt.1,
      (enlargedFamily code).map (CategoryOfElements.homMk _ _ step rfl)
        ((ContextualFamilyEnlargement.model (code.decode.models ⟨first, receipt.1⟩)).decode.symm (ULift.up receipt.2))⟩ :
      TotalAt (enlargedFamily code) second) =
      ⟨base.map step receipt.1,
        (ContextualFamilyEnlargement.model (code.decode.models ⟨second, base.map step receipt.1⟩)).decode.symm
          (ULift.up (code.decode.native.map (CategoryOfElements.homMk _ _ step rfl) receipt.2))⟩
    exact congrArg (fun term => (⟨base.map step receipt.1, term⟩ : TotalAt (enlargedFamily code) second))
      (ContextualFamilyEnlargement.member_encode.{u,max (u+1) (v+1)} code.decode.native code.decode.models
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1⟩
          ⟨second, base.map step receipt.1⟩ step rfl) receipt.2)

theorem decode_encode (point : D) (receipt : code.decode.extension.obj point) :
    (decodeTotal code).app point ((encodeTotal code).app point receipt) = receipt := by
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    exact congrArg ULift.down
      ((ContextualFamilyEnlargement.model (code.decode.models ⟨point, receipt.1⟩)).decode.apply_symm_apply
        (ULift.up receipt.2))

theorem encode_decode (point : D) (receipt : (materialTotal code).obj point) :
    (encodeTotal code).app point ((decodeTotal code).app point receipt) = receipt := by
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    exact (ContextualFamilyEnlargement.model (code.decode.models ⟨point, receipt.1⟩)).decode.symm_apply_apply receipt.2

def toPullback : NaturalHom (materialTotal code) (GenericPullback (classifier code)) :=
  (decodeTotal code).comp (classificationForward code.decode.native)

def fromPullback : NaturalHom (GenericPullback (classifier code)) (materialTotal code) :=
  (classificationBackward code.decode.native).comp (encodeTotal code)

theorem from_to (point : D) (receipt : (materialTotal code).obj point) :
    (fromPullback code).app point ((toPullback code).app point receipt) = receipt :=
  (congrArg ((encodeTotal code).app point)
    (classification_left code.decode.native point ((decodeTotal code).app point receipt))).trans
      (encode_decode code point receipt)

theorem to_from (point : D) (receipt : (GenericPullback (classifier code)).obj point) :
    (toPullback code).app point ((fromPullback code).app point receipt) = receipt :=
  (congrArg ((classificationForward code.decode.native).app point)
    (decode_encode code point ((classificationBackward code.decode.native).app point receipt))).trans
      (classification_right code.decode.native point receipt)

def pullbackEquiv (point : D) :
    (materialTotal code).obj point ≃ (GenericPullback (classifier code)).obj point where
  toFun := (toPullback code).app point
  invFun := (fromPullback code).app point
  left_inv := from_to code point
  right_inv := to_from code point

def pullbackSections : (materialTotal code).sections ≃ (GenericPullback (classifier code)).sections where
  toFun := (toPullback code).mapSection
  invFun := (fromPullback code).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact from_to code point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact to_from code point (term.val point)

theorem toPullback_parameter (point : D) (receipt : (materialTotal code).obj point) :
    ((toPullback code).app point receipt).val.2 = receipt.1 := rfl

theorem fromPullback_parameter (point : D) (receipt : (GenericPullback (classifier code)).obj point) :
    ((fromPullback code).app point receipt).1 = receipt.val.2 := rfl

theorem encodeTotal_value (point : D) (receipt : code.decode.extension.obj point) :
    ((encodeTotal code).app point receipt).2.val =
      HSet.enlarge.{u,max (u+1) (v+1)} ((code.decode.models ⟨point, receipt.1⟩).value receipt.2) := rfl

theorem material_value_recovered (point : D) (receipt : (materialTotal code).obj point) :
    HSet.enlarge.{u,max (u+1) (v+1)} ((code.decode.models ⟨point, receipt.1⟩).value ((decodeTotal code).app point receipt).2) =
      receipt.2.val :=
  congrArg (fun value : (materialTotal code).obj point => value.2.val) (encode_decode code point receipt)

theorem material_type_enclosed (point : D) (receipt : (materialTotal code).obj point) :
    ContextualAuthoredGeneratedEnclosure.reading worlds arrows seeds seedModel code ⟨point, receipt.1⟩ ∈
      ContextualAuthoredGeneratedEnclosure.enclosure worlds arrows seeds seedModel ⟨point, receipt.1⟩ :=
  ContextualAuthoredGeneratedEnclosure.code_enclosed worlds arrows seeds seedModel code _

/-- The interpreted complete code and its selected term in the constructed
universal small family. This retains future restrictions, not just support. -/
def interpreted : NaturalHom (materialTotal code) universalTotal :=
  (decodeTotal code).comp (ContextualSmallFamilyUniverse.classified code.decode.native)

theorem interpreted_code (point : D) (receipt : (materialTotal code).obj point) :
    ((interpreted code).app point receipt).1 = (classifier code).app point receipt.1 := rfl

theorem interpreted_term (point : D) (receipt : (materialTotal code).obj point) :
    HEq ((interpreted code).app point receipt).2 ((decodeTotal code).app point receipt).2 :=
  ContextualSmallFamilyUniverse.classified_value_heq code.decode.native point
    ((decodeTotal code).app point receipt)

section Substitution

variable {other middle : D ⥤ Type (max u v)} (change : NaturalHom other base)

theorem classifier_substitution : classifier (code.reindex change) = change.comp (classifier code) :=
  ContextualSmallFamilyUniverse.classifier_parameter_substitution code.decode.native change

theorem classifier_substitution_comp (earlier : NaturalHom middle other) :
    classifier ((code.reindex change).reindex earlier) =
      earlier.comp (change.comp (classifier code)) := by
  rw [classifier_substitution, classifier_substitution]

def materialChange : NaturalHom (materialTotal (code.reindex change)) (materialTotal code) where
  app point receipt := ⟨change.app point receipt.1, receipt.2⟩
  naturality {first second} step receipt := by
    apply Sigma.ext (change.naturality step receipt.1)
    have target : (⟨second, change.app second (other.map step receipt.1)⟩ : base.Elements) =
        ⟨second, base.map step (change.app first receipt.1)⟩ :=
      Sigma.ext rfl (heq_of_eq (change.naturality step receipt.1).symm)
    exact (ContextualSmallFamilyUniverse.familyMap_heq (enlargedFamily code) rfl target
      ((ContextualSmallFamilyUniverse.elementMap change).map
        (CategoryOfElements.homMk (F := other) ⟨first, receipt.1⟩
          ⟨second, other.map step receipt.1⟩ step rfl))
      (CategoryOfElements.homMk (F := base) ⟨first, change.app first receipt.1⟩
        ⟨second, base.map step (change.app first receipt.1)⟩ step rfl)
      (ContextualSmallFamilyUniverse.elementsArrow_heq rfl target _ _ HEq.rfl)
      receipt.2 receipt.2 HEq.rfl).symm

theorem decodeTotal_substitution (point : D) (receipt : (materialTotal (code.reindex change)).obj point) :
    (decodeTotal code).app point ((materialChange code change).app point receipt) =
      ⟨change.app point receipt.1, ((decodeTotal (code.reindex change)).app point receipt).2⟩ := rfl

/-- Decoding, material parameter transport and full future classification
commute as natural maps, including noninjective substitutions. -/
theorem interpreted_substitution :
    (materialChange code change).comp (interpreted code) = interpreted (code.reindex change) := by
  apply NaturalHom.ext
  intro point receipt
  exact congrArg (fun operation => operation.app point ((decodeTotal (code.reindex change)).app point receipt))
    (ContextualSmallFamilyUniverse.classified_substitution code.decode.native change)

end Substitution

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedClassification
