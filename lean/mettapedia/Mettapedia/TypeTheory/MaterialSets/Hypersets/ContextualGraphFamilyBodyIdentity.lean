import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodySubstitution
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedIdentity

/-!
# Dependent identity elimination with actual attached material bodies

The native discrete identity context and its literal attached receipt
context have inverse natural decoders. Arbitrary dependent motives carry
their actual natural material readings. Their receipt J commutes with
the native J, its computation rule, and parameter substitution on whole
sections. Material matching is used only to compare declared readouts;
it is not the identity type used by the eliminator.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyIdentity

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyIdentity
open ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFamilyBodies ContextualGraphFamilyBodySubstitution

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u)

section Domain
variable (domainReading : NaturalHom (total domain) (values D))

def totalDecoder : NaturalHom (total (literal domain domainReading)) (total domain) where
  app point receipt := ⟨receipt.1, decode domain domainReading ⟨point, receipt.1⟩ receipt.2⟩
  naturality {first second} step receipt :=
    (congrArg (fun value => (⟨base.map step receipt.1, value⟩ : (total domain).obj second))
      (decode_naturality domain domainReading
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1⟩
          ⟨second, base.map step receipt.1⟩ step rfl) receipt.2)).symm

def toNativeIdentity : NaturalHom (identityContext (literal domain domainReading)) (identityContext domain) where
  app point receipt :=
    ⟨⟨⟨receipt.1.1.1, decode domain domainReading ⟨point, receipt.1.1.1⟩ receipt.1.1.2⟩,
      decode domain domainReading ⟨point, receipt.1.1.1⟩ receipt.1.2⟩,
      PresheafIdentityWitness.encode (congrArg (decode domain domainReading ⟨point, receipt.1.1.1⟩)
        (PresheafIdentityWitness.decode receipt.2))⟩
  naturality {first second} step receipt := by
    refine receipt_ext domain _ _ rfl ?_ ?_
    · exact heq_of_eq (decode_naturality domain domainReading
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.1.2).symm
    · exact heq_of_eq (decode_naturality domain domainReading
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.2).symm

def fromNativeIdentity : NaturalHom (identityContext domain) (identityContext (literal domain domainReading)) where
  app point receipt :=
    ⟨⟨⟨receipt.1.1.1, encode domain domainReading ⟨point, receipt.1.1.1⟩ receipt.1.1.2⟩,
      encode domain domainReading ⟨point, receipt.1.1.1⟩ receipt.1.2⟩,
      PresheafIdentityWitness.encode (congrArg (encode domain domainReading ⟨point, receipt.1.1.1⟩)
        (PresheafIdentityWitness.decode receipt.2))⟩
  naturality {first second} step receipt := by
    refine receipt_ext (literal domain domainReading) _ _ rfl ?_ ?_
    · exact heq_of_eq (encode_naturality domain domainReading
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.1.2)
    · exact heq_of_eq (encode_naturality domain domainReading
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.2)

theorem identity_decoder_inverse :
    (toNativeIdentity domain domainReading).comp (fromNativeIdentity domain domainReading) =
      ContextualSmallMapConstructions.identity (identityContext (literal domain domainReading)) := by
  apply NaturalHom.ext
  intro point receipt
  refine receipt_ext (literal domain domainReading) _ _ rfl ?_ ?_
  · exact heq_of_eq (encode_decode domain domainReading ⟨point, receipt.1.1.1⟩ receipt.1.1.2)
  · exact heq_of_eq (encode_decode domain domainReading ⟨point, receipt.1.1.1⟩ receipt.1.2)

theorem identity_encoder_inverse :
    (fromNativeIdentity domain domainReading).comp (toNativeIdentity domain domainReading) =
      ContextualSmallMapConstructions.identity (identityContext domain) := by
  apply NaturalHom.ext
  intro point receipt
  refine receipt_ext domain _ _ rfl ?_ ?_ <;> exact HEq.rfl

theorem diagonal_decoder_square :
    (diagonal (literal domain domainReading)).comp (toNativeIdentity domain domainReading) =
      (totalDecoder domain domainReading).comp (diagonal domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem readLeft_decoder_square : (toNativeIdentity domain domainReading).comp (readLeft domain) =
    (readLeft (literal domain domainReading)).comp (totalDecoder domain domainReading) := by
  apply NaturalHom.ext
  intro _ _
  rfl

end Domain

section DiscreteFormation

/-- The declared material body of a discrete identity witness is empty.
The endpoint condition remains in the actual native witness family. -/
def witnessDiagram : Diagram D where
  nodes := {
    obj _ := PUnit.{u+1}
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge _ _ _ := False
  edge_transport := fun {_ _} _ {_ _} impossible => impossible

def witnessValue (point : D) : Value D point := ⟨witnessDiagram, PUnit.unit⟩

def witnessReading : NaturalHom (total (witnessFamily domain)) (values D) where
  app point _ := witnessValue point
  naturality _ _ := rfl

def identityCarrier (point : base.Elements) (left right : domain.obj point) : Value D point.1 :=
  carrier (witnessFamily domain) (witnessReading domain) point.1 ⟨⟨point.2, left⟩, right⟩

def reflexivityReceipt (point : base.Elements) (term : domain.obj point) :
    (literal (witnessFamily domain) (witnessReading domain)).obj ⟨point.1, ⟨⟨point.2, term⟩, term⟩⟩ :=
  encode _ _ _ (PresheafIdentityWitness.encode rfl)

theorem witness_receipt_endpoints (point : base.Elements) (left right : domain.obj point)
    (receipt : (literal (witnessFamily domain) (witnessReading domain)).obj ⟨point.1, ⟨⟨point.2, left⟩, right⟩⟩) :
    left = right := PresheafIdentityWitness.decode (decode _ _ _ receipt)

theorem identity_membership_iff (point : base.Elements) (left right : domain.obj point) (element : Value D point.1) :
    Nonempty (Member element (identityCarrier domain point left right)) ↔
      left = right ∧ Nonempty (Equal element (witnessValue point.1)) := by
  constructor
  · rintro ⟨membership⟩
    let decoded := ContextualGraphFamilyBodyComparison.memberDecode
      (witnessFamily domain) (witnessReading domain) ⟨point.1, ⟨⟨point.2, left⟩, right⟩⟩ element membership
    exact ⟨PresheafIdentityWitness.decode decoded.1, ⟨decoded.2⟩⟩
  · rintro ⟨same, ⟨matching⟩⟩
    exact ⟨ContextualGraphFamilyBodyComparison.memberIntro (witnessFamily domain) (witnessReading domain)
      ⟨point.1, ⟨⟨point.2, left⟩, right⟩⟩ element (PresheafIdentityWitness.encode same) matching⟩

theorem identity_material_nonempty_iff (point : base.Elements) (left right : domain.obj point) :
    (∃ element : Value D point.1, Nonempty (Member element (identityCarrier domain point left right))) ↔ left = right :=
  ⟨fun ⟨element, belongs⟩ => ((identity_membership_iff domain point left right element).mp belongs).1,
    fun same => ⟨witnessValue point.1,
      (identity_membership_iff domain point left right _).mpr ⟨same, ⟨Equal.refl _⟩⟩⟩⟩

end DiscreteFormation

section Elimination
variable (motive : (identityContext domain).Elements ⥤ Type u)
variable (motiveReading : NaturalHom (total motive) (values D))

abbrev methodFamily := ContextualSmallFamilyIdentity.reindex motive (diagonal domain)
abbrev methodReading := readingUnder motive motiveReading (diagonal domain)

def literalMethod (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections) :
    (ContextualSmallFamilyIdentity.reindex (literal motive motiveReading) (diagonal domain)).sections :=
  (ContextualGraphFamilyBodySubstitution.sectionComparison motive motiveReading (diagonal domain)).symm method

def receiptJ (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections) :
    (literal motive motiveReading).sections :=
  J domain (literal motive motiveReading) (literalMethod domain motive motiveReading method)

def decoderHom : WiderPresheafDependentFunctions.Hom (literal motive motiveReading) motive where
  app := decode motive motiveReading
  naturality step receipt := (decode_naturality motive motiveReading step receipt).symm

theorem receiptJ_native (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections) :
    sectionDecoder motive motiveReading (receiptJ domain motive motiveReading method) =
      J domain motive (sectionDecoder (methodFamily domain motive) (methodReading domain motive motiveReading) method) := by
  have natural := GraphRealizedGeneratedIdentity.J_naturality domain (decoderHom domain motive motiveReading)
    (literalMethod domain motive motiveReading method)
  refine natural.trans (congrArg (J domain motive) ?_)
  apply Subtype.ext
  funext point
  change decode motive motiveReading ((elementMap (diagonal domain)).obj point)
      ((ContextualGraphFamilyBodySubstitution.backward motive motiveReading (diagonal domain)).app point (method.val point)) = _
  exact decode_encode motive motiveReading ((elementMap (diagonal domain)).obj point)
    (decode (methodFamily domain motive) (methodReading domain motive motiveReading) point (method.val point))

theorem receiptJ_beta (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections) :
    substituteSection motive motiveReading (diagonal domain) (receiptJ domain motive motiveReading method) = method := by
  apply (sectionDecoder (methodFamily domain motive) (methodReading domain motive motiveReading)).injective
  exact (decoder_substitution motive motiveReading (diagonal domain) (receiptJ domain motive motiveReading method)).trans
    ((congrArg (reindexSection (diagonal domain) motive) (receiptJ_native domain motive motiveReading method)).trans
      (J_beta domain motive (sectionDecoder _ _ method)))

/-- The result of dependent elimination retains the actual declared
material body of the native eliminated term at every identity receipt. -/
def receiptJ_material (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections)
    (point : (identityContext domain).Elements) :
    Equal (motiveReading.app point.1 ⟨point.2,
      (J domain motive (sectionDecoder (methodFamily domain motive) (methodReading domain motive motiveReading) method)).val point⟩)
      ((ContextualGraphReceiptFamilies.sectionReading (parent motive motiveReading)
        (receiptJ domain motive motiveReading method)).app point.1 point.2) :=
  (Equal.ofEq (congrArg (fun result : motive.sections => motiveReading.app point.1 ⟨point.2, result.val point⟩)
    (receiptJ_native domain motive motiveReading method).symm)).trans
    (ContextualGraphFamilyBodyComparison.sectionComparison motive motiveReading
      (receiptJ domain motive motiveReading method) point)

variable {other : D ⥤ Type u} (change : NaturalHom other base)

abbrev substitutedMotive := ContextualSmallFamilyIdentity.reindex motive (identityReindex change domain)
abbrev substitutedReading := readingUnder motive motiveReading (identityReindex change domain)

def substitutedMethod (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections) :
    (literal (methodFamily (ContextualSmallFamilyIdentity.reindex domain change) (substitutedMotive domain motive change))
      (methodReading (ContextualSmallFamilyIdentity.reindex domain change) (substitutedMotive domain motive change)
        (substitutedReading domain motive motiveReading change))).sections :=
  (sectionDecoder _ _).symm (reindexMethod change domain motive
    (sectionDecoder (methodFamily domain motive) (methodReading domain motive motiveReading) method))

theorem receiptJ_substitution (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections) :
    substituteSection motive motiveReading (identityReindex change domain) (receiptJ domain motive motiveReading method) =
      receiptJ (ContextualSmallFamilyIdentity.reindex domain change) (substitutedMotive domain motive change)
        (substitutedReading domain motive motiveReading change) (substitutedMethod domain motive motiveReading change method) := by
  apply (sectionDecoder (substitutedMotive domain motive change) (substitutedReading domain motive motiveReading change)).injective
  exact (decoder_substitution motive motiveReading (identityReindex change domain) (receiptJ domain motive motiveReading method)).trans
    ((congrArg (reindexSection (identityReindex change domain) motive) (receiptJ_native domain motive motiveReading method)).trans
      ((J_substitution change domain motive (sectionDecoder _ _ method)).trans
        ((congrArg (J (ContextualSmallFamilyIdentity.reindex domain change) (substitutedMotive domain motive change))
          ((sectionDecoder _ _).apply_symm_apply _).symm).trans (receiptJ_native _ _ _ _).symm)))

theorem receiptJ_beta_substitution (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections) :
    substituteSection (substitutedMotive domain motive change) (substitutedReading domain motive motiveReading change)
      (diagonal (ContextualSmallFamilyIdentity.reindex domain change))
      (substituteSection motive motiveReading (identityReindex change domain) (receiptJ domain motive motiveReading method)) =
        substitutedMethod domain motive motiveReading change method := by
  rw [receiptJ_substitution]
  exact receiptJ_beta _ _ _ _

end Elimination

variable (domainReading : NaturalHom (total domain) (values D))
variable (motive : (identityContext domain).Elements ⥤ Type u)
variable (motiveReading : NaturalHom (total motive) (values D))

abbrev pulledMotive := ContextualSmallFamilyIdentity.reindex motive (toNativeIdentity domain domainReading)
abbrev pulledReading := readingUnder motive motiveReading (toNativeIdentity domain domainReading)

def changedMethod (method : (ContextualSmallFamilyIdentity.reindex motive (diagonal domain)).sections) :
    (ContextualSmallFamilyIdentity.reindex (pulledMotive domain domainReading motive)
      (diagonal (literal domain domainReading))).sections :=
  reindexSection (totalDecoder domain domainReading) (ContextualSmallFamilyIdentity.reindex motive (diagonal domain)) method

theorem J_decoder_square (method : (ContextualSmallFamilyIdentity.reindex motive (diagonal domain)).sections) :
    reindexSection (toNativeIdentity domain domainReading) motive (J domain motive method) =
      J (literal domain domainReading) (pulledMotive domain domainReading motive)
        (changedMethod domain domainReading motive method) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  exact (J_value_heq domain motive method ((elementMap (toNativeIdentity domain domainReading)).obj point)).trans
    (J_value_heq (literal domain domainReading) (pulledMotive domain domainReading motive)
      (changedMethod domain domainReading motive method) point).symm

def nativeReceiptJ (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections) :
    (literal (pulledMotive domain domainReading motive) (pulledReading domain domainReading motive motiveReading)).sections :=
  receiptJ (literal domain domainReading) (pulledMotive domain domainReading motive)
    (pulledReading domain domainReading motive motiveReading)
    ((sectionDecoder _ _).symm (changedMethod domain domainReading motive (sectionDecoder _ _ method)))

/-- A single whole-section diagram joins the actual attached domain,
its identity context, the dependent motive reading, and native J. -/
theorem nativeReceiptJ_square (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections) :
    sectionDecoder (pulledMotive domain domainReading motive) (pulledReading domain domainReading motive motiveReading)
        (nativeReceiptJ domain domainReading motive motiveReading method) =
      reindexSection (toNativeIdentity domain domainReading) motive
        (J domain motive (sectionDecoder (methodFamily domain motive) (methodReading domain motive motiveReading) method)) :=
  (receiptJ_native (literal domain domainReading) (pulledMotive domain domainReading motive)
    (pulledReading domain domainReading motive motiveReading) _).trans
    ((congrArg (J (literal domain domainReading) (pulledMotive domain domainReading motive))
      ((sectionDecoder _ _).apply_symm_apply _)).trans
      (J_decoder_square domain domainReading motive _).symm)

def nativeReceiptJ_material
    (method : (literal (methodFamily domain motive) (methodReading domain motive motiveReading)).sections)
    (point : (identityContext (literal domain domainReading)).Elements) :
    Equal (motiveReading.app point.1 ⟨(toNativeIdentity domain domainReading).app point.1 point.2,
      (J domain motive (sectionDecoder (methodFamily domain motive) (methodReading domain motive motiveReading) method)).val
        ((elementMap (toNativeIdentity domain domainReading)).obj point)⟩)
      ((ContextualGraphReceiptFamilies.sectionReading
        (parent (pulledMotive domain domainReading motive) (pulledReading domain domainReading motive motiveReading))
        (nativeReceiptJ domain domainReading motive motiveReading method)).app point.1 point.2) :=
  (Equal.ofEq (congrArg
    (fun result : (pulledMotive domain domainReading motive).sections =>
      (pulledReading domain domainReading motive motiveReading).app point.1 ⟨point.2, result.val point⟩)
    (nativeReceiptJ_square domain domainReading motive motiveReading method).symm)).trans
      (ContextualGraphFamilyBodyComparison.sectionComparison
        (pulledMotive domain domainReading motive) (pulledReading domain domainReading motive motiveReading)
        (nativeReceiptJ domain domainReading motive motiveReading method) point)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyIdentity
