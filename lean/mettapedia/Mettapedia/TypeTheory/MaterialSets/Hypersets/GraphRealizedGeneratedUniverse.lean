import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedContextualFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedClassification

/-!
# Generated graph receipts in the constructed family universe

The actual literal-child graph family, its native comprehension, the
enlarged material-member comprehension and the universal-family pullback
form a natural diagram with constructed inverse maps. Complete sections
and arbitrary parameter substitutions follow the same diagram. The graph
observation agrees with the independent material dictionary at every
point; its type carrier belongs to the generated enclosure.

The generated recipe and whole native family remain retained data. This
construction does not recover them from a present material carrier or
assert internally small code universes or transfinite closure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedUniverse

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualAuthoredMaterialFamilies ContextualSmallFamilyUniverse

universe u v q r
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type (max u v)}

abbrev receipts (domain : Family base) := GraphRealizedContextualFamilies.family domain
abbrev receiptTotal (domain : Family base) := total (receipts domain)

def toNative (domain : Family base) : NaturalHom (receiptTotal domain) domain.extension where
  app point receipt := ⟨receipt.1, GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1⟩ receipt.2⟩
  naturality {first second} step receipt := by
    exact (congrArg (fun value => (⟨base.map step receipt.1, value⟩ : domain.extension.obj second))
      (GraphRealizedContextualFamilies.restriction_decode domain
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1⟩
          ⟨second, base.map step receipt.1⟩ step rfl) receipt.2)).symm

def fromNative (domain : Family base) : NaturalHom domain.extension (receiptTotal domain) where
  app point receipt := ⟨receipt.1, (GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1⟩).symm receipt.2⟩
  naturality {first second} step receipt := by
    exact congrArg (fun value =>
      (⟨base.map step receipt.1,
        (GraphRealizedContextualFamilies.decode domain ⟨second, base.map step receipt.1⟩).symm
          (domain.native.map (CategoryOfElements.homMk (F := base) ⟨first, receipt.1⟩
            ⟨second, base.map step receipt.1⟩ step rfl) value)⟩ : (receiptTotal domain).obj second))
      ((GraphRealizedContextualFamilies.decode domain ⟨first, receipt.1⟩).apply_symm_apply receipt.2)

theorem native_receipt (domain : Family base) (point : D) (receipt : (receiptTotal domain).obj point) :
    (fromNative domain).app point ((toNative domain).app point receipt) = receipt :=
  congrArg (fun value => (⟨receipt.1, value⟩ : (receiptTotal domain).obj point))
    ((GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1⟩).symm_apply_apply receipt.2)

theorem receipt_native (domain : Family base) (point : D) (receipt : domain.extension.obj point) :
    (toNative domain).app point ((fromNative domain).app point receipt) = receipt :=
  congrArg (fun value => (⟨receipt.1, value⟩ : domain.extension.obj point))
    ((GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1⟩).apply_symm_apply receipt.2)

theorem native_receipt_map (domain : Family base) :
    (toNative domain).comp (fromNative domain) = ContextualSmallMapConstructions.identity (receiptTotal domain) := by
  apply NaturalHom.ext
  exact native_receipt domain

theorem receipt_native_map (domain : Family base) :
    (fromNative domain).comp (toNative domain) = ContextualSmallMapConstructions.identity domain.extension := by
  apply NaturalHom.ext
  exact receipt_native domain

def receiptChange (domain : Family base) {other : D ⥤ Type (max u v)}
    (change : NaturalHom other base) : NaturalHom (receiptTotal (domain.reindex change)) (receiptTotal domain) :=
  substitutedTotalMap (receipts domain) change

theorem native_substitution_square (domain : Family base) {other : D ⥤ Type (max u v)}
    (change : NaturalHom other base) :
    (receiptChange domain change).comp (toNative domain) =
      (toNative (domain.reindex change)).comp (substitutedTotalMap domain.native change) := by
  apply NaturalHom.ext
  intro _ _
  rfl

section Generated

variable {worlds : ArgumentCoding D} {arrows : (first second : D) → ArgumentCoding (first ⟶ second)}
variable {seeds : (base : D ⥤ Type (max u v)) → Type (max (u+1) v)}
variable {seedModel : (base : D ⥤ Type (max u v)) → seeds base → Family base}
variable (code : ContextualAuthoredGeneratedFamilies.Code worlds arrows seeds seedModel base)

def toMaterial : NaturalHom (receiptTotal code.decode)
    (ContextualAuthoredGeneratedClassification.materialTotal code) :=
  (toNative code.decode).comp (ContextualAuthoredGeneratedClassification.encodeTotal code)

def fromMaterial : NaturalHom (ContextualAuthoredGeneratedClassification.materialTotal code)
    (receiptTotal code.decode) :=
  (ContextualAuthoredGeneratedClassification.decodeTotal code).comp (fromNative code.decode)

theorem material_receipt (point : D) (receipt : (receiptTotal code.decode).obj point) :
    (fromMaterial code).app point ((toMaterial code).app point receipt) = receipt :=
  (congrArg ((fromNative code.decode).app point)
    (ContextualAuthoredGeneratedClassification.decode_encode code point
      ((toNative code.decode).app point receipt))).trans (native_receipt code.decode point receipt)

theorem receipt_material (point : D)
    (receipt : (ContextualAuthoredGeneratedClassification.materialTotal code).obj point) :
    (toMaterial code).app point ((fromMaterial code).app point receipt) = receipt :=
  (congrArg ((ContextualAuthoredGeneratedClassification.encodeTotal code).app point)
    (receipt_native code.decode point ((ContextualAuthoredGeneratedClassification.decodeTotal code).app point receipt))).trans
      (ContextualAuthoredGeneratedClassification.encode_decode code point receipt)

theorem material_receipt_map :
    (toMaterial code).comp (fromMaterial code) =
      ContextualSmallMapConstructions.identity (receiptTotal code.decode) := by
  apply NaturalHom.ext
  exact material_receipt code

theorem receipt_material_map :
    (fromMaterial code).comp (toMaterial code) =
      ContextualSmallMapConstructions.identity (ContextualAuthoredGeneratedClassification.materialTotal code) := by
  apply NaturalHom.ext
  exact receipt_material code

def toUniversalPullback : NaturalHom (receiptTotal code.decode)
    (GenericPullback (ContextualAuthoredGeneratedClassification.classifier code)) :=
  (toMaterial code).comp (ContextualAuthoredGeneratedClassification.toPullback code)

def fromUniversalPullback : NaturalHom
    (GenericPullback (ContextualAuthoredGeneratedClassification.classifier code)) (receiptTotal code.decode) :=
  (ContextualAuthoredGeneratedClassification.fromPullback code).comp (fromMaterial code)

theorem universal_receipt (point : D) (receipt : (receiptTotal code.decode).obj point) :
    (fromUniversalPullback code).app point ((toUniversalPullback code).app point receipt) = receipt :=
  (congrArg ((fromMaterial code).app point)
    (ContextualAuthoredGeneratedClassification.from_to code point ((toMaterial code).app point receipt))).trans
      (material_receipt code point receipt)

theorem receipt_universal (point : D)
    (receipt : (GenericPullback (ContextualAuthoredGeneratedClassification.classifier code)).obj point) :
    (toUniversalPullback code).app point ((fromUniversalPullback code).app point receipt) = receipt :=
  (congrArg ((ContextualAuthoredGeneratedClassification.toPullback code).app point)
    (receipt_material code point ((ContextualAuthoredGeneratedClassification.fromPullback code).app point receipt))).trans
      (ContextualAuthoredGeneratedClassification.to_from code point receipt)

def universalSections : (receiptTotal code.decode).sections ≃
    (GenericPullback (ContextualAuthoredGeneratedClassification.classifier code)).sections where
  toFun := (toUniversalPullback code).mapSection
  invFun := (fromUniversalPullback code).mapSection
  left_inv term := Subtype.ext (funext fun point => universal_receipt code point (term.val point))
  right_inv term := Subtype.ext (funext fun point => receipt_universal code point (term.val point))

def materialSections : (receipts code.decode).sections ≃
    (ContextualAuthoredGeneratedClassification.enlargedFamily code).sections :=
  (GraphRealizedContextualFamilies.sectionEquiv code.decode).trans
    (ContextualAuthoredGeneratedEnclosure.memberSections worlds arrows seeds seedModel code)

/-- Material growth acts on the same complete literal section. The
comparison uses the constructed inverse at the earlier bound. -/
theorem materialSections_cumulative (term : (receipts code.decode).sections) :
    ContextualFamilyEnlargement.cumulativeSections.{u,max (u+1) (v+1),max u v,u,q}
      code.decode.native code.decode.models (materialSections code term) =
        ContextualFamilyEnlargement.sectionEquiv.{u,max (max (u+1) (v+1)) q}
          code.decode.native code.decode.models
          (GraphRealizedContextualFamilies.sectionEquiv code.decode term) := by
  change ContextualFamilyEnlargement.sectionEquiv _ _
    ((ContextualFamilyEnlargement.sectionEquiv _ _).symm
      (ContextualFamilyEnlargement.sectionEquiv _ _
        (GraphRealizedContextualFamilies.sectionEquiv code.decode term))) = _
  rw [Equiv.symm_apply_apply]

theorem materialSections_cumulative_comp (term : (receipts code.decode).sections) :
    ContextualFamilyEnlargement.cumulativeSections.{u,max (max (u+1) (v+1)) q,max u v,u,r}
      code.decode.native code.decode.models
      (ContextualFamilyEnlargement.cumulativeSections.{u,max (u+1) (v+1),max u v,u,q}
        code.decode.native code.decode.models (materialSections code term)) =
      ContextualFamilyEnlargement.cumulativeSections.{u,max (u+1) (v+1),max u v,u,max q r}
        code.decode.native code.decode.models (materialSections code term) :=
  ContextualFamilyEnlargement.cumulativeSections_comp code.decode.native code.decode.models _

theorem material_value (point : D) (receipt : (receiptTotal code.decode).obj point) :
    ((toMaterial code).app point receipt).2.val =
      HSet.enlarge.{u,max (u+1) (v+1)}
        (HSet.mk ((GraphRealizedContextualFamilies.graph code.decode ⟨point, receipt.1⟩).repoint receipt.2.val)) :=
  congrArg HSet.enlarge.{u,max (u+1) (v+1)}
    (GraphRealizedContextualFamilies.receipt_value code.decode ⟨point, receipt.1⟩ receipt.2).symm

theorem materialSections_value (term : (receipts code.decode).sections) (point : base.Elements) :
    ((materialSections code term).val point).val =
      HSet.enlarge.{u,max (u+1) (v+1)}
        (HSet.mk ((GraphRealizedContextualFamilies.graph code.decode point).repoint (term.val point).val)) :=
  congrArg HSet.enlarge.{u,max (u+1) (v+1)}
    (GraphRealizedContextualFamilies.receipt_value code.decode point (term.val point)).symm

theorem graph_enclosed (point : base.Elements) :
    HSet.enlarge.{u,max (u+1) (v+1)} (HSet.mk (GraphRealizedContextualFamilies.graph code.decode point)) ∈
      ContextualAuthoredGeneratedEnclosure.enclosure worlds arrows seeds seedModel point := by
  rw [GraphRealizedContextualFamilies.graph_carrier]
  exact ContextualAuthoredGeneratedEnclosure.code_enclosed worlds arrows seeds seedModel code point

theorem universal_interpretation_square :
    (toMaterial code).comp (ContextualAuthoredGeneratedClassification.interpreted code) =
      (toNative code.decode).comp (ContextualSmallFamilyUniverse.classified code.decode.native) := by
  apply NaturalHom.ext
  intro point receipt
  exact congrArg ((ContextualSmallFamilyUniverse.classified code.decode.native).app point)
    (ContextualAuthoredGeneratedClassification.decode_encode code point ((toNative code.decode).app point receipt))

variable {other : D ⥤ Type (max u v)} (change : NaturalHom other base)

theorem material_substitution_square :
    (receiptChange code.decode change).comp (toMaterial code) =
      (toMaterial (code.reindex change)).comp
        (ContextualAuthoredGeneratedClassification.materialChange code change) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem interpreted_substitution :
    (receiptChange code.decode change).comp
        ((toMaterial code).comp (ContextualAuthoredGeneratedClassification.interpreted code)) =
      (toMaterial (code.reindex change)).comp
        (ContextualAuthoredGeneratedClassification.interpreted (code.reindex change)) := by
  rw [universal_interpretation_square, universal_interpretation_square]
  apply NaturalHom.ext
  intro point receipt
  exact congrArg (fun operation => operation.app point ((toNative (code.reindex change).decode).app point receipt))
    (ContextualSmallFamilyUniverse.classified_substitution code.decode.native change)

end Generated

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedUniverse
