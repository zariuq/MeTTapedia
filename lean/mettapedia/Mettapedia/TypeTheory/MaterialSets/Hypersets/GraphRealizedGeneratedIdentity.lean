import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedUniverse
import Mettapedia.TypeTheory.ContextualSmallFamilyIdentityExt

/-!
# Discrete dependent identity through the actual graph receipt decoder

Literal receipts and their decoded native values have constructed inverse
maps between their full nested identity contexts. The diagonal and the
left-endpoint projection commute with those maps. Arbitrary natural
motives, complete methods and dependent J therefore follow the same
diagram, with computation and parameter substitution.

This is the discrete set-valued identity interpretation. Graph matching
realizers are not its identity witnesses and do not supply dependent J.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedIdentity

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualAuthoredMaterialFamilies ContextualSmallFamilyUniverse
open ContextualSmallFamilyIdentity GraphRealizedGeneratedUniverse

universe u v w z
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type (max u v)}
variable (domain : Family base)

abbrev nativeContext := identityContext domain.native
abbrev receiptContext := identityContext (receipts domain)

def toNativeIdentity : NaturalHom (receiptContext domain) (nativeContext domain) where
  app point receipt :=
    ⟨⟨⟨receipt.1.1.1,
      GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩ receipt.1.1.2⟩,
      GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩ receipt.1.2⟩,
      PresheafIdentityWitness.encode (congrArg
        (GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩)
        (PresheafIdentityWitness.decode receipt.2))⟩
  naturality {first second} step receipt := by
    refine receipt_ext domain.native _ _ rfl ?_ ?_
    · exact heq_of_eq (GraphRealizedContextualFamilies.restriction_decode domain
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.1.2).symm
    · exact heq_of_eq (GraphRealizedContextualFamilies.restriction_decode domain
        (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
          ⟨second, base.map step receipt.1.1.1⟩ step rfl) receipt.1.2).symm

def fromNativeIdentity : NaturalHom (nativeContext domain) (receiptContext domain) where
  app point receipt :=
    ⟨⟨⟨receipt.1.1.1,
      (GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩).symm receipt.1.1.2⟩,
      (GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩).symm receipt.1.2⟩,
      PresheafIdentityWitness.encode (congrArg
        (GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩).symm
        (PresheafIdentityWitness.decode receipt.2))⟩
  naturality {first second} step receipt := by
    refine receipt_ext (receipts domain) _ _ rfl ?_ ?_
    · exact heq_of_eq (congrArg (fun value =>
        (GraphRealizedContextualFamilies.decode domain ⟨second, base.map step receipt.1.1.1⟩).symm
          (domain.native.map (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
            ⟨second, base.map step receipt.1.1.1⟩ step rfl) value))
        ((GraphRealizedContextualFamilies.decode domain ⟨first, receipt.1.1.1⟩).apply_symm_apply receipt.1.1.2))
    · exact heq_of_eq (congrArg (fun value =>
        (GraphRealizedContextualFamilies.decode domain ⟨second, base.map step receipt.1.1.1⟩).symm
          (domain.native.map (CategoryOfElements.homMk (F := base) ⟨first, receipt.1.1.1⟩
            ⟨second, base.map step receipt.1.1.1⟩ step rfl) value))
        ((GraphRealizedContextualFamilies.decode domain ⟨first, receipt.1.1.1⟩).apply_symm_apply receipt.1.2))

theorem identity_native_receipt :
    (toNativeIdentity domain).comp (fromNativeIdentity domain) =
      ContextualSmallMapConstructions.identity (receiptContext domain) := by
  apply NaturalHom.ext
  intro point receipt
  refine receipt_ext (receipts domain) _ _ rfl ?_ ?_
  · exact heq_of_eq ((GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩).symm_apply_apply receipt.1.1.2)
  · exact heq_of_eq ((GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩).symm_apply_apply receipt.1.2)

theorem identity_receipt_native :
    (fromNativeIdentity domain).comp (toNativeIdentity domain) =
      ContextualSmallMapConstructions.identity (nativeContext domain) := by
  apply NaturalHom.ext
  intro point receipt
  refine receipt_ext domain.native _ _ rfl ?_ ?_
  · exact heq_of_eq ((GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩).apply_symm_apply receipt.1.1.2)
  · exact heq_of_eq ((GraphRealizedContextualFamilies.decode domain ⟨point, receipt.1.1.1⟩).apply_symm_apply receipt.1.2)

theorem diagonal_decoder_square :
    (diagonal (receipts domain)).comp (toNativeIdentity domain) =
      (toNative domain).comp (diagonal domain.native) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem readLeft_decoder_square :
    (toNativeIdentity domain).comp (readLeft domain.native) =
      (readLeft (receipts domain)).comp (toNative domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl

section GeneralElimination

variable {parameter : D ⥤ Type (max u v)} (family : parameter.Elements ⥤ Type u)

/-- The inverse diagonal makes restriction injective on complete sections. -/
theorem J_eta (motive : (identityContext family).Elements ⥤ Type w) (term : motive.sections) :
    J family motive (reindexSection (diagonal family) motive term) = term := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  have unchanged : HEq (term.val ((elementMap (diagonal family)).obj
      ((elementMap (readLeft family)).obj point))) (term.val point) := by
    have same := diagonal_readLeft_point family point
    generalize (elementMap (diagonal family)).obj ((elementMap (readLeft family)).obj point) = other at same ⊢
    cases same
    rfl
  exact (J_value_heq family motive (reindexSection (diagonal family) motive term) point).trans unchanged

theorem diagonal_section_injective (motive : (identityContext family).Elements ⥤ Type w) :
    Function.Injective (reindexSection (diagonal family) motive) := by
  intro first second same
  exact (J_eta family motive first).symm.trans
    ((congrArg (J family motive) same).trans (J_eta family motive second))

def methodHom {first : (identityContext family).Elements ⥤ Type w}
    {second : (identityContext family).Elements ⥤ Type z}
    (operation : WiderPresheafDependentFunctions.Hom first second) :
    WiderPresheafDependentFunctions.Hom (ContextualSmallFamilyIdentity.reindex first (diagonal family)) (ContextualSmallFamilyIdentity.reindex second (diagonal family)) where
  app point := operation.app ((elementMap (diagonal family)).obj point)
  naturality step term := operation.naturality ((elementMap (diagonal family)).map step) term

/-- A natural map of genuine dependent motives commutes with J on whole
sections. Neither the motive nor its map is reduced to a constant family. -/
theorem J_naturality {first : (identityContext family).Elements ⥤ Type w}
    {second : (identityContext family).Elements ⥤ Type z}
    (operation : WiderPresheafDependentFunctions.Hom first second)
    (method : (ContextualSmallFamilyIdentity.reindex first (diagonal family)).sections) :
    operation.mapSection (J family first method) =
      J family second ((methodHom family operation).mapSection method) := by
  apply diagonal_section_injective family second
  change (methodHom family operation).mapSection
      (reindexSection (diagonal family) first (J family first method)) =
    reindexSection (diagonal family) second
      (J family second ((methodHom family operation).mapSection method))
  rw [J_beta, J_beta]

end GeneralElimination

def changedMethod (motive : (nativeContext domain).Elements ⥤ Type w)
    (method : (ContextualSmallFamilyIdentity.reindex motive (diagonal domain.native)).sections) :
    (ContextualSmallFamilyIdentity.reindex (ContextualSmallFamilyIdentity.reindex motive (toNativeIdentity domain)) (diagonal (receipts domain))).sections :=
  reindexSection (toNative domain) (ContextualSmallFamilyIdentity.reindex motive (diagonal domain.native)) method

/-- The actual inverse endpoint diagram transports arbitrary dependent
elimination, with no assumption that the motive ignores its witness. -/
theorem J_decoder_square (motive : (nativeContext domain).Elements ⥤ Type w)
    (method : (ContextualSmallFamilyIdentity.reindex motive (diagonal domain.native)).sections) :
    reindexSection (toNativeIdentity domain) motive (J domain.native motive method) =
      J (receipts domain) (ContextualSmallFamilyIdentity.reindex motive (toNativeIdentity domain)) (changedMethod domain motive method) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  exact (J_value_heq domain.native motive method ((elementMap (toNativeIdentity domain)).obj point)).trans
    (J_value_heq (receipts domain) (ContextualSmallFamilyIdentity.reindex motive (toNativeIdentity domain))
      (changedMethod domain motive method) point).symm

def literalDecoder {context : D ⥤ Type (max u v)} (motive : Family context) :
    WiderPresheafDependentFunctions.Hom
      (GraphRealizedContextualFamilies.family motive) motive.native where
  app point := GraphRealizedContextualFamilies.decode motive point
  naturality step term := (GraphRealizedContextualFamilies.restriction_decode motive step term).symm

variable (motive : Family (nativeContext domain))

abbrev pulledMotive := motive.reindex (toNativeIdentity domain)

def literalMethod
    (method : (GraphRealizedContextualFamilies.family (motive.reindex (diagonal domain.native))).sections) :
    (ContextualSmallFamilyIdentity.reindex (GraphRealizedContextualFamilies.family (pulledMotive domain motive))
      (diagonal (receipts domain))).sections :=
  GraphRealizedContextualFamilies.restrictSection (motive.reindex (diagonal domain.native))
    (toNative domain) method

/-- Dependent J acts on literal graph-receipt motives over the actual
receipt identity context. -/
def literalJ
    (method : (GraphRealizedContextualFamilies.family (motive.reindex (diagonal domain.native))).sections) :
    (GraphRealizedContextualFamilies.family (pulledMotive domain motive)).sections :=
  J (receipts domain) (GraphRealizedContextualFamilies.family (pulledMotive domain motive))
    (literalMethod domain motive method)

theorem literalJ_beta
    (method : (GraphRealizedContextualFamilies.family (motive.reindex (diagonal domain.native))).sections) :
    reindexSection (diagonal (receipts domain))
      (GraphRealizedContextualFamilies.family (pulledMotive domain motive)) (literalJ domain motive method) =
        literalMethod domain motive method := J_beta _ _ _

theorem literalJ_native
    (method : (GraphRealizedContextualFamilies.family (motive.reindex (diagonal domain.native))).sections) :
    GraphRealizedContextualFamilies.sectionEquiv (pulledMotive domain motive) (literalJ domain motive method) =
      reindexSection (toNativeIdentity domain) motive.native
        (J domain.native motive.native
          (GraphRealizedContextualFamilies.sectionEquiv (motive.reindex (diagonal domain.native)) method)) := by
  have natural := J_naturality (receipts domain)
    (literalDecoder (pulledMotive domain motive))
    (literalMethod domain motive method)
  exact natural.trans (J_decoder_square domain motive.native
    (GraphRealizedContextualFamilies.sectionEquiv (motive.reindex (diagonal domain.native)) method)).symm

section Substitution

variable {other : D ⥤ Type (max u v)} (change : NaturalHom other base)

theorem identity_decoder_substitution_square :
    (identityReindex change (receipts domain)).comp (toNativeIdentity domain) =
      (toNativeIdentity (domain.reindex change)).comp (identityReindex change domain.native) := by
  apply NaturalHom.ext
  intro _ _
  rfl

def substituteMethod
    (method : (GraphRealizedContextualFamilies.family (motive.reindex (diagonal domain.native))).sections) :
    (GraphRealizedContextualFamilies.family
      ((motive.reindex (identityReindex change domain.native)).reindex
        (diagonal (domain.reindex change).native))).sections :=
  reindexMethod change domain.native (GraphRealizedContextualFamilies.family motive) method

/-- Parameter substitution and literal-receipt elimination commute on
complete dependent sections, retaining both substituted endpoints. -/
theorem literalJ_substitution
    (method : (GraphRealizedContextualFamilies.family (motive.reindex (diagonal domain.native))).sections) :
    reindexSection (identityReindex change (receipts domain))
        (GraphRealizedContextualFamilies.family (pulledMotive domain motive))
        (literalJ domain motive method) =
      literalJ (domain.reindex change) (motive.reindex (identityReindex change domain.native))
        (substituteMethod domain motive change method) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  have first := J_value_heq (receipts domain)
    (GraphRealizedContextualFamilies.family (pulledMotive domain motive))
    (literalMethod domain motive method)
    ((elementMap (identityReindex change (receipts domain))).obj point)
  have second := J_value_heq (receipts (domain.reindex change))
    (GraphRealizedContextualFamilies.family
      (pulledMotive (domain.reindex change) (motive.reindex (identityReindex change domain.native))))
    (literalMethod (domain.reindex change) (motive.reindex (identityReindex change domain.native))
      (substituteMethod domain motive change method)) point
  have castValue := ContextualSmallFamilyComprehension.sectionCast_value
    (reflexiveMotive_reindex change domain.native (GraphRealizedContextualFamilies.family motive))
    (reindexSection (totalReindex change domain.native)
      (ContextualSmallFamilyIdentity.reindex (GraphRealizedContextualFamilies.family motive)
        (diagonal domain.native)) method)
    ((elementMap (toNative (domain.reindex change))).obj
      ((elementMap (readLeft (receipts (domain.reindex change)))).obj point))
  exact first.trans (second.trans castValue).symm

theorem literalJ_beta_substitution
    (method : (GraphRealizedContextualFamilies.family (motive.reindex (diagonal domain.native))).sections) :
    reindexSection (diagonal (receipts (domain.reindex change)))
      (GraphRealizedContextualFamilies.family
        (pulledMotive (domain.reindex change) (motive.reindex (identityReindex change domain.native))))
      (reindexSection (identityReindex change (receipts domain))
        (GraphRealizedContextualFamilies.family (pulledMotive domain motive))
        (literalJ domain motive method)) =
      literalMethod (domain.reindex change) (motive.reindex (identityReindex change domain.native))
        (substituteMethod domain motive change method) := by
  rw [literalJ_substitution]
  exact literalJ_beta _ _ _

end Substitution

section Generated

variable {worlds : ArgumentCoding D} {arrows : (first second : D) → ArgumentCoding (first ⟶ second)}
variable {seeds : (base : D ⥤ Type (max u v)) → Type (max (u+1) v)}
variable {seedModel : (base : D ⥤ Type (max u v)) → seeds base → Family base}
variable (code : ContextualAuthoredGeneratedFamilies.Code worlds arrows seeds seedModel base)

/-- The two genuine dependent reindexings build the endpoint family;
identity formation is then an original generated recipe over that context. -/
def witnessCode : ContextualAuthoredGeneratedFamilies.Code worlds arrows seeds seedModel
    (endpoints code.decode.native) :=
  let second := code.reindex (projection code.decode.native)
  let endpoint := second.reindex (projection second.decode.native)
  endpoint.identity (leftEndpoint code.decode.native) (rightEndpoint code.decode.native)

def reflexivityReceipt (point : base.Elements) (argument : code.decode.native.obj point) :
    (receipts (witnessCode code).decode).obj ⟨point.1, ⟨⟨point.2, argument⟩, argument⟩⟩ :=
  (GraphRealizedContextualFamilies.decode (witnessCode code).decode _).symm
    (PresheafIdentityWitness.encode rfl)

theorem reflexivityReceipt_decodes (point : base.Elements) (argument : code.decode.native.obj point) :
    GraphRealizedContextualFamilies.decode (witnessCode code).decode
        ⟨point.1, ⟨⟨point.2, argument⟩, argument⟩⟩ (reflexivityReceipt code point argument) =
      PresheafIdentityWitness.encode rfl :=
  (GraphRealizedContextualFamilies.decode (witnessCode code).decode _).apply_symm_apply _

theorem witnessReceiptEndpoints (point : base.Elements) (left right : code.decode.native.obj point)
    (receipt : (receipts (witnessCode code).decode).obj ⟨point.1, ⟨⟨point.2, left⟩, right⟩⟩) :
    left = right :=
  PresheafIdentityWitness.decode (GraphRealizedContextualFamilies.decode (witnessCode code).decode _ receipt)

theorem witnessGraph_enclosed (point : (endpoints code.decode.native).Elements) :
    HSet.enlarge.{u,max (u+1) (v+1)}
        (HSet.mk (GraphRealizedContextualFamilies.graph (witnessCode code).decode point)) ∈
      ContextualAuthoredGeneratedEnclosure.enclosure worlds arrows seeds seedModel point :=
  graph_enclosed (witnessCode code) point

variable (motiveCode : ContextualAuthoredGeneratedFamilies.Code worlds arrows seeds seedModel
  (nativeContext code.decode))

/-- The same complete literal J section decodes through the constructed
material enclosure to native J for the independently decoded generated
motive. The original-small motive and its generated substitution recipe
are retained throughout. -/
theorem literalJ_material
    (method : (receipts (motiveCode.decode.reindex (diagonal code.decode.native))).sections) :
    materialSections (motiveCode.reindex (toNativeIdentity code.decode))
        (literalJ code.decode motiveCode.decode method) =
      ContextualAuthoredGeneratedEnclosure.memberSections worlds arrows seeds seedModel
        (motiveCode.reindex (toNativeIdentity code.decode))
        (reindexSection (toNativeIdentity code.decode) motiveCode.decode.native
          (J code.decode.native motiveCode.decode.native
            (GraphRealizedContextualFamilies.sectionEquiv
              (motiveCode.decode.reindex (diagonal code.decode.native)) method))) :=
  congrArg
    (ContextualAuthoredGeneratedEnclosure.memberSections worlds arrows seeds seedModel
      (motiveCode.reindex (toNativeIdentity code.decode)))
    (literalJ_native code.decode motiveCode.decode method)

theorem literalJ_material_value
    (method : (receipts (motiveCode.decode.reindex (diagonal code.decode.native))).sections)
    (point : (receiptContext code.decode).Elements) :
    ((materialSections (motiveCode.reindex (toNativeIdentity code.decode))
      (literalJ code.decode motiveCode.decode method)).val point).val =
        HSet.enlarge.{u,max (u+1) (v+1)}
          (HSet.mk ((GraphRealizedContextualFamilies.graph
            (pulledMotive code.decode motiveCode.decode) point).repoint
              ((literalJ code.decode motiveCode.decode method).val point).val)) :=
  materialSections_value (motiveCode.reindex (toNativeIdentity code.decode)) _ point

end Generated

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedGeneratedIdentity
