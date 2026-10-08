import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilySubstitution
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedIdentity

/-!
# Dependent identity elimination through constructed contextual receipts

The actual nested identity contexts retain both literal endpoints and the
discrete identity witness. Their decoder is naturally invertible and
commutes with the reflexivity diagonal. Arbitrary dependent motives are
represented by newly constructed graphs; dependent J, computation and
substitution commute on whole sections through those receipt decoders.
Graph matching is not used as native identity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyIdentity

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyIdentity
open ContextualGraphFamilyRepresentation ContextualGraphFamilySubstitution

universe u
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type u}
variable (domain : base.Elements ⥤ Type u)

abbrev nativeContext := identityContext domain
abbrev receiptContext := identityContext (literal domain)

def toNativeIdentity : NaturalHom (receiptContext domain) (nativeContext domain) where
  app point receipt :=
    ⟨⟨⟨receipt.1.1.1, decode domain ⟨point, receipt.1.1.1⟩ receipt.1.1.2⟩,
      decode domain ⟨point, receipt.1.1.1⟩ receipt.1.2⟩,
      PresheafIdentityWitness.encode (congrArg (decode domain ⟨point, receipt.1.1.1⟩)
        (PresheafIdentityWitness.decode receipt.2))⟩
  naturality {first second} step receipt := by
    refine receipt_ext domain _ _ rfl ?_ ?_
    · exact heq_of_eq (decode_naturality domain
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.1.2).symm
    · exact heq_of_eq (decode_naturality domain
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.2).symm

def fromNativeIdentity : NaturalHom (nativeContext domain) (receiptContext domain) where
  app point receipt :=
    ⟨⟨⟨receipt.1.1.1, encode domain ⟨point, receipt.1.1.1⟩ receipt.1.1.2⟩,
      encode domain ⟨point, receipt.1.1.1⟩ receipt.1.2⟩,
      PresheafIdentityWitness.encode (congrArg (encode domain ⟨point, receipt.1.1.1⟩)
        (PresheafIdentityWitness.decode receipt.2))⟩
  naturality {first second} step receipt := by
    refine receipt_ext (literal domain) _ _ rfl ?_ ?_
    · exact heq_of_eq (encode_naturality domain
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.1.2)
    · exact heq_of_eq (encode_naturality domain
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.2)

theorem identity_decoder_inverse : (toNativeIdentity domain).comp (fromNativeIdentity domain) =
    ContextualSmallMapConstructions.identity (receiptContext domain) := by
  apply NaturalHom.ext
  intro point receipt
  refine receipt_ext (literal domain) _ _ rfl ?_ ?_
  · exact heq_of_eq (encode_decode domain ⟨point, receipt.1.1.1⟩ receipt.1.1.2)
  · exact heq_of_eq (encode_decode domain ⟨point, receipt.1.1.1⟩ receipt.1.2)

theorem identity_encoder_inverse : (fromNativeIdentity domain).comp (toNativeIdentity domain) =
    ContextualSmallMapConstructions.identity (nativeContext domain) := by
  apply NaturalHom.ext
  intro point receipt
  refine receipt_ext domain _ _ rfl ?_ ?_ <;> exact HEq.rfl

theorem diagonal_decoder_square :
    (diagonal (literal domain)).comp (toNativeIdentity domain) =
      (totalToNative domain).comp (diagonal domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem readLeft_decoder_square : (toNativeIdentity domain).comp (readLeft domain) =
    (readLeft (literal domain)).comp (totalToNative domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

section Elimination
variable (motive : (identityContext domain).Elements ⥤ Type u)

def literalMethod (method : (literal (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).sections) :
    (ContextualSmallFamilyIdentity.reindex (literal motive) (diagonal domain)).sections :=
  (sectionComparison motive (diagonal domain)).symm method

def receiptJ (method : (literal (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).sections) :
    (literal motive).sections :=
  J domain (literal motive) (literalMethod domain motive method)

def decoderHom : WiderPresheafDependentFunctions.Hom (literal motive) motive where
  app := decode motive
  naturality step receipt := (decode_naturality motive step receipt).symm

theorem receiptJ_native (method : (literal (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).sections) :
    sectionDecoder motive (receiptJ domain motive method) =
      J domain motive (sectionDecoder (ContextualSmallFamilyIdentity.reindex motive (diagonal domain)) method) := by
  exact GraphRealizedGeneratedIdentity.J_naturality domain (decoderHom domain motive)
    (literalMethod domain motive method)

theorem receiptJ_beta (method : (literal (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).sections) :
    substituteSection motive (diagonal domain) (receiptJ domain motive method) = method := by
  apply (sectionDecoder (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).injective
  exact (decoder_substitution motive (diagonal domain) (receiptJ domain motive method)).trans
    ((congrArg (reindexSection (diagonal domain) motive) (receiptJ_native domain motive method)).trans
      (J_beta domain motive (sectionDecoder _ method)))

variable {other : D ⥤ Type u} (change : NaturalHom other base)

def substitutedMethod (method : (literal (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).sections) :
    (literal (ContextualSmallFamilyIdentity.reindex (ContextualSmallFamilyIdentity.reindex motive (identityReindex change domain))
      (diagonal (ContextualSmallFamilyIdentity.reindex domain change)))).sections :=
  (sectionDecoder _).symm (reindexMethod change domain motive
    (sectionDecoder (ContextualSmallFamilyIdentity.reindex motive (diagonal domain)) method))

theorem receiptJ_substitution (method : (literal (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).sections) :
    substituteSection motive (identityReindex change domain) (receiptJ domain motive method) =
      receiptJ (ContextualSmallFamilyIdentity.reindex domain change) (ContextualSmallFamilyIdentity.reindex motive (identityReindex change domain))
        (substitutedMethod domain motive change method) := by
  apply (sectionDecoder (ContextualSmallFamilyIdentity.reindex motive (identityReindex change domain))).injective
  exact (decoder_substitution motive (identityReindex change domain) (receiptJ domain motive method)).trans
    ((congrArg (reindexSection (identityReindex change domain) motive) (receiptJ_native domain motive method)).trans
      ((J_substitution change domain motive (sectionDecoder _ method)).trans
        ((congrArg (J (ContextualSmallFamilyIdentity.reindex domain change)
          (ContextualSmallFamilyIdentity.reindex motive (identityReindex change domain)))
          ((sectionDecoder _).apply_symm_apply _).symm).trans
            (receiptJ_native _ _ _).symm)))

theorem receiptJ_beta_substitution (method : (literal (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).sections) :
    substituteSection (ContextualSmallFamilyIdentity.reindex motive (identityReindex change domain)) (diagonal (ContextualSmallFamilyIdentity.reindex domain change))
      (substituteSection motive (identityReindex change domain) (receiptJ domain motive method)) =
        substitutedMethod domain motive change method := by
  rw [receiptJ_substitution]
  exact receiptJ_beta _ _ _

end Elimination

variable (motive : (nativeContext domain).Elements ⥤ Type u)

abbrev pulledMotive := ContextualSmallFamilyIdentity.reindex motive (toNativeIdentity domain)

def changedMethod (method : (ContextualSmallFamilyIdentity.reindex motive (diagonal domain)).sections) :
    (ContextualSmallFamilyIdentity.reindex (pulledMotive domain motive) (diagonal (literal domain))).sections :=
  reindexSection (totalToNative domain) (ContextualSmallFamilyIdentity.reindex motive (diagonal domain)) method

theorem J_decoder_square (method : (ContextualSmallFamilyIdentity.reindex motive (diagonal domain)).sections) :
    reindexSection (toNativeIdentity domain) motive (J domain motive method) =
      J (literal domain) (pulledMotive domain motive) (changedMethod domain motive method) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  exact (J_value_heq domain motive method ((elementMap (toNativeIdentity domain)).obj point)).trans
    (J_value_heq (literal domain) (pulledMotive domain motive) (changedMethod domain motive method) point).symm

/-- Both the domain and arbitrary dependent motive use actual graph
receipts. The method is re-expressed over the actual receipt diagonal. -/
def nativeReceiptJ (method : (literal (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).sections) :
    (literal (pulledMotive domain motive)).sections :=
  receiptJ (literal domain) (pulledMotive domain motive)
    ((sectionDecoder _).symm (changedMethod domain motive (sectionDecoder _ method)))

/-- The full dependent identity diagram commutes on complete sections,
including all future restriction maps and the retained identity context. -/
theorem nativeReceiptJ_square (method : (literal (ContextualSmallFamilyIdentity.reindex motive (diagonal domain))).sections) :
    sectionDecoder (pulledMotive domain motive) (nativeReceiptJ domain motive method) =
      reindexSection (toNativeIdentity domain) motive
        (J domain motive (sectionDecoder (ContextualSmallFamilyIdentity.reindex motive (diagonal domain)) method)) := by
  rw [nativeReceiptJ, receiptJ_native, Equiv.apply_symm_apply, J_decoder_square]

def reflexivityReceipt (point : base.Elements) (term : domain.obj point) :
    (literal (witnessFamily domain)).obj ⟨point.1, ⟨⟨point.2, term⟩, term⟩⟩ :=
  encode _ _ (PresheafIdentityWitness.encode rfl)

theorem witness_receipt_endpoints (point : base.Elements) (left right : domain.obj point)
    (receipt : (literal (witnessFamily domain)).obj ⟨point.1, ⟨⟨point.2, left⟩, right⟩⟩) : left = right :=
  PresheafIdentityWitness.decode (decode _ _ receipt)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyIdentity
