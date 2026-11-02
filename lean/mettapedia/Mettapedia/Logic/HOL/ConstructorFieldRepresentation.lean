import Mettapedia.Logic.HOL.FiniteConstructorFieldProjection
import Mettapedia.Logic.HOL.MixedConstructorPayloadMaps
import Mettapedia.Logic.HOL.ConstructorInjectivity

/-!
# Concrete field representation in a constructor carrier

An element is stored in the middle field of an encoded payload at a fixed
tag, with fixed recursive branches. The decoder first projects the payload
from the constructor and then selects its original middle field. Retained
proofs establish recovery from the constructor and selection laws.

The payload element type is independent of the recursive carrier. Neither
countability nor injectivity of the entire payload space into that carrier
is an assumption of this construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorFieldRepresentation
open MixedConstructorPayloadMaps
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {number element branches carrier : Ty Base} {Δ : List (Formula Const Γ)}

abbrev Raw (number element branches carrier : Ty Base) :=
  ConstructorProjections.Constructor number (Payload number element) branches carrier

def value (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
    (field : Term Const Γ element) : Term Const Γ carrier :=
  ConstructorProjections.apply raw marker (pack marker field marker) fixedBranches

def embedding (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches) : Term Const Γ (element ⇒ carrier) :=
  .lam (value (weaken raw) (weaken marker) (weaken fixedBranches) (.var .vz))

def decoder (raw : Term Const Γ (Raw number element branches carrier))
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element)) : Term Const Γ (carrier ⇒ element) :=
  .lam (.app
    (FiniteConstructorFieldProjection.projection [[number,element,number]] ⟨0,Nat.zero_lt_succ 0⟩ (.vs .vz) (weaken fieldSelection))
    (.app (ConstructorProjections.secondProjection (weaken payloadSelection) (weaken raw)) (.var .vz)))

theorem value_subst (images : Subst Const Γ Ξ)
    (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches) (field : Term Const Γ element) :
    subst images (value raw marker fixedBranches field) =
      value (subst images raw) (subst images marker) (subst images fixedBranches) (subst images field) := by
  simp only [value, ConstructorProjections.apply, subst, pack_subst]

theorem embedding_subst (images : Subst Const Γ Ξ)
    (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches) :
    subst images (embedding raw marker fixedBranches) =
      embedding (subst images raw) (subst images marker) (subst images fixedBranches) := by
  simp only [embedding, subst, value_subst, subst_weaken, Subst.lift]

theorem decoder_subst (images : Subst Const Γ Ξ)
    (raw : Term Const Γ (Raw number element branches carrier))
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element)) :
    subst images (decoder raw payloadSelection fieldSelection) =
      decoder (subst images raw) (subst images payloadSelection) (subst images fieldSelection) := by
  simp only [decoder, subst, FiniteConstructorFieldProjection.projection_subst,
    ConstructorProjections.subst_secondProjection, subst_weaken, Subst.lift]

def embedding_apply (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches) (field : Term Const Γ element) :
    ProofSyntax Const Δ (.eq (.app (embedding raw marker fixedBranches) field) (value raw marker fixedBranches field)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta field (value (weaken raw) (weaken marker) (weaken fixedBranches) (.var .vz)))
  simp only [instantiate, value_subst, subst, Subst.single]
  rw [show subst (Subst.single field) (weaken raw) = raw from instantiate_weaken field raw,
    show subst (Subst.single field) (weaken marker) = marker from instantiate_weaken field marker,
    show subst (Subst.single field) (weaken fixedBranches) = fixedBranches from instantiate_weaken field fixedBranches]
  rfl

def decoder_apply (raw : Term Const Γ (Raw number element branches carrier))
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element)) (stored : Term Const Γ carrier) :
    ProofSyntax Const Δ (.eq (.app (decoder raw payloadSelection fieldSelection) stored)
      (.app (FiniteConstructorFieldProjection.projection [[number,element,number]] ⟨0,Nat.zero_lt_succ 0⟩ (.vs .vz) fieldSelection)
        (.app (ConstructorProjections.secondProjection payloadSelection raw) stored))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta stored
    (.app (FiniteConstructorFieldProjection.projection [[number,element,number]] ⟨0,Nat.zero_lt_succ 0⟩ (.vs .vz) (weaken fieldSelection))
      (.app (ConstructorProjections.secondProjection (weaken payloadSelection) (weaken raw)) (.var .vz))))
  simp only [instantiate, subst, FiniteConstructorFieldProjection.projection_subst,
    ConstructorProjections.subst_secondProjection, Subst.single]
  rw [show subst (Subst.single stored) (weaken raw) = raw from instantiate_weaken stored raw,
    show subst (Subst.single stored) (weaken payloadSelection) = payloadSelection from instantiate_weaken stored payloadSelection,
    show subst (Subst.single stored) (weaken fieldSelection) = fieldSelection from instantiate_weaken stored fieldSelection]
  rfl

def roundtrip (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element)) (field : Term Const Γ element)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw)) :
    ProofSyntax Const Δ (.eq (.app (decoder raw payloadSelection fieldSelection)
      (.app (embedding raw marker fixedBranches) field)) field) :=
  .eqTrans (.eqAppArg (decoder raw payloadSelection fieldSelection) (embedding_apply raw marker fixedBranches field))
    (.eqTrans (decoder_apply raw payloadSelection fieldSelection (value raw marker fixedBranches field))
      (.eqTrans (.eqAppArg (FiniteConstructorFieldProjection.projection [[number,element,number]] ⟨0,Nat.zero_lt_succ 0⟩ (.vs .vz) fieldSelection)
        (ConstructorProjections.second_at payloadSelection raw marker (pack marker field marker) fixedBranches payloadChoice injectivity))
        (FiniteConstructorFieldProjection.projection_at [[number,element,number]] ⟨0,Nat.zero_lt_succ 0⟩ (.vs .vz)
          fieldSelection (marker,field,marker,PUnit.unit) fieldChoice)))

def leftInverse (encode : Term Const Γ (element ⇒ carrier)) (decode : Term Const Γ (carrier ⇒ element)) : Formula Const Γ :=
  .all (.eq (.app (weaken decode) (.app (weaken encode) (.var .vz))) (.var .vz))

theorem leftInverse_rename (ρ : Rename Base Γ Ξ)
    (encode : Term Const Γ (element ⇒ carrier)) (decode : Term Const Γ (carrier ⇒ element)) :
    rename ρ (leftInverse encode decode) = leftInverse (rename ρ encode) (rename ρ decode) := by
  simp [leftInverse, rename, weaken, rename_comp, Rename.lift, Rename.weaken]

def roundtrip_law (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element))
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw)) :
    ProofSyntax Const Δ (leftInverse (embedding raw marker fixedBranches) (decoder raw payloadSelection fieldSelection)) := by
  apply ProofSyntax.allI (σ := element)
  have pc : ProofSyntax Const (weakenHyps (σ := element) Δ) (SelectionProofs.principle (weaken payloadSelection)) :=
    .castIndices rfl (ConstructorProjections.rename_selection Rename.weaken payloadSelection) (payloadChoice.rename Rename.weaken)
  have fc : ProofSyntax Const (weakenHyps (σ := element) Δ) (SelectionProofs.principle (weaken fieldSelection)) :=
    .castIndices rfl (ConstructorProjections.rename_selection Rename.weaken fieldSelection) (fieldChoice.rename Rename.weaken)
  have ci : ProofSyntax Const (weakenHyps (σ := element) Δ) (ConstructorProjections.fieldInjective (weaken raw)) :=
    .castIndices rfl (ConstructorProjections.rename_fieldInjective Rename.weaken raw) (injectivity.rename Rename.weaken)
  apply ProofSyntax.castIndices rfl ?_ (roundtrip (weaken raw) (weaken marker) (weaken fixedBranches)
    (weaken payloadSelection) (weaken fieldSelection) (.var .vz) pc fc ci)
  simp only [weaken, ← subst_ofRename, embedding_subst, decoder_subst]

#print axioms roundtrip
#print axioms roundtrip_law

def leftInverse_at (encode : Term Const Γ (element ⇒ carrier)) (decode : Term Const Γ (carrier ⇒ element))
    (field : Term Const Γ element) (law : ProofSyntax Const Δ (leftInverse encode decode)) :
    ProofSyntax Const Δ (.eq (.app decode (.app encode field)) field) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE field law)
  simp only [instantiate, subst, Subst.single]
  rw [show subst (Subst.single field) (weaken decode) = decode from instantiate_weaken field decode,
    show subst (Subst.single field) (weaken encode) = encode from instantiate_weaken field encode]

def imageBody (encode : Term Const Γ (element ⇒ carrier)) (stored : Term Const Γ carrier) : Formula Const Γ :=
  .ex (.eq (.app (weaken encode) (.var .vz)) (weaken stored))

def image (encode : Term Const Γ (element ⇒ carrier)) : Term Const Γ (carrier ⇒ .prop) :=
  .lam (imageBody (weaken encode) (.var .vz))

theorem imageBody_subst (images : Subst Const Γ Ξ) (encode : Term Const Γ (element ⇒ carrier))
    (stored : Term Const Γ carrier) :
    subst images (imageBody encode stored) = imageBody (subst images encode) (subst images stored) := by
  simp only [imageBody, subst, subst_weaken, Subst.lift]

theorem image_subst (images : Subst Const Γ Ξ) (encode : Term Const Γ (element ⇒ carrier)) :
    subst images (image encode) = image (subst images encode) := by
  simp only [image, subst, imageBody_subst, subst_weaken, Subst.lift]

def image_apply (encode : Term Const Γ (element ⇒ carrier)) (stored : Term Const Γ carrier) :
    ProofSyntax Const Δ (.eq (.app (image encode) stored) (imageBody encode stored)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta stored (imageBody (weaken encode) (.var .vz)))
  simp only [instantiate, imageBody_subst, subst, Subst.single]
  rw [show subst (Subst.single stored) (weaken encode) = encode from instantiate_weaken stored encode]
  rfl

def image_introduce (encode : Term Const Γ (element ⇒ carrier)) (field : Term Const Γ element) :
    ProofSyntax Const Δ (.app (image encode) (.app encode field)) := by
  apply ProofSyntax.impE (.eqPropER (image_apply encode (.app encode field)))
  apply ProofSyntax.exI field
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl (.app encode field))
  simp only [instantiate, subst, Subst.single]
  rw [show subst (Subst.single field) (weaken encode) = encode from instantiate_weaken field encode,
    show subst (Subst.single field) (weaken (.app encode field)) = .app encode field from instantiate_weaken field (.app encode field)]

def image_recovery (encode : Term Const Γ (element ⇒ carrier)) (decode : Term Const Γ (carrier ⇒ element))
    (stored : Term Const Γ carrier) (law : ProofSyntax Const Δ (leftInverse encode decode))
    (member : ProofSyntax Const Δ (.app (image encode) stored)) :
    ProofSyntax Const Δ (.eq (.app encode (.app decode stored)) stored) := by
  have existsField := ProofSyntax.impE (.eqPropEL (image_apply encode stored)) member
  apply ProofSyntax.exE existsField
  let witness := Term.eq (.app (weaken encode) (.var .vz)) (weaken stored)
  have law' : ProofSyntax Const (witness :: weakenHyps (σ := element) Δ)
      (leftInverse (weaken encode) (weaken decode)) :=
    .castIndices rfl (leftInverse_rename Rename.weaken encode decode)
      ((law.rename Rename.weaken).prepend witness)
  have same : ProofSyntax Const (witness :: weakenHyps (σ := element) Δ)
      (.eq (.app (weaken encode) (.var .vz)) (weaken stored)) := .hyp 0
  exact .eqTrans (.eqAppArg (weaken encode)
    (.eqTrans (.eqAppArg (weaken decode) (.eqSymm same))
      (leftInverse_at (weaken encode) (weaken decode) (.var .vz) law'))) same

/-- The guard is the actual represented image; the premise is recovery of
original fields, not the guarded conclusion being constructed. -/
def image_retraction (encode : Term Const Γ (element ⇒ carrier)) (decode : Term Const Γ (carrier ⇒ element))
    (law : ProofSyntax Const Δ (leftInverse encode decode)) :
    ProofSyntax Const Δ (GuardedRetraction.law decode encode (image encode)) := by
  apply ProofSyntax.allI (σ := carrier)
  apply ProofSyntax.impI
  have law' : ProofSyntax Const
      (.app (weaken (image encode)) (.var .vz) :: weakenHyps (σ := carrier) Δ)
      (leftInverse (weaken encode) (weaken decode)) :=
    .castIndices rfl (leftInverse_rename Rename.weaken encode decode)
      ((law.rename Rename.weaken).prepend _)
  have valid : ProofSyntax Const
      (.app (weaken (image encode)) (.var .vz) :: weakenHyps (σ := carrier) Δ)
      (.app (image (weaken encode)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp 0)
    change Term.app (weaken (image encode)) (.var .vz) = Term.app (image (weaken encode)) (.var .vz)
    apply congrArg (fun predicate => Term.app predicate (.var .vz))
    simpa only [weaken, subst_ofRename] using image_subst (Subst.ofRename (Rename.weaken (σ := carrier))) encode
  exact image_recovery (weaken encode) (weaken decode) (.var .vz) law' valid

theorem embedding_apply_free (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches) (field : Term Const Γ element) :
    (embedding_apply (Δ := Δ) raw marker fixedBranches field).FunctionExtensionalityFree := by
  simp only [embedding_apply, ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.FunctionExtensionalityFree]

theorem decoder_apply_free (raw : Term Const Γ (Raw number element branches carrier))
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element)) (stored : Term Const Γ carrier) :
    (decoder_apply (Δ := Δ) raw payloadSelection fieldSelection stored).FunctionExtensionalityFree := by
  simp only [decoder_apply, ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.FunctionExtensionalityFree]

theorem roundtrip_free (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element)) (field : Term Const Γ element)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (pcFree : payloadChoice.FunctionExtensionalityFree) (fcFree : fieldChoice.FunctionExtensionalityFree)
    (ciFree : injectivity.FunctionExtensionalityFree) :
    (roundtrip raw marker fixedBranches payloadSelection fieldSelection field payloadChoice fieldChoice injectivity).FunctionExtensionalityFree := by
  exact ⟨embedding_apply_free _ _ _ _, ⟨decoder_apply_free _ _ _ _,
    ⟨ConstructorProjections.second_at_free _ _ _ _ _ _ _ pcFree ciFree,
      FiniteConstructorFieldProjection.projection_at_free _ _ _ _ _ _ fcFree⟩⟩⟩

theorem roundtrip_law_free (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element))
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (pcFree : payloadChoice.FunctionExtensionalityFree) (fcFree : fieldChoice.FunctionExtensionalityFree)
    (ciFree : injectivity.FunctionExtensionalityFree) :
    (roundtrip_law raw marker fixedBranches payloadSelection fieldSelection payloadChoice fieldChoice injectivity).FunctionExtensionalityFree := by
  unfold roundtrip_law
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply roundtrip_free
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr pcFree)
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr fcFree)
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr ciFree)

theorem leftInverse_at_free (encode : Term Const Γ (element ⇒ carrier)) (decode : Term Const Γ (carrier ⇒ element))
    (field : Term Const Γ element) (law : ProofSyntax Const Δ (leftInverse encode decode))
    (free : law.FunctionExtensionalityFree) : (leftInverse_at encode decode field law).FunctionExtensionalityFree := by
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

theorem image_apply_free (encode : Term Const Γ (element ⇒ carrier)) (stored : Term Const Γ carrier) :
    (image_apply (Δ := Δ) encode stored).FunctionExtensionalityFree := by
  simp only [image_apply, ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.FunctionExtensionalityFree]

theorem image_introduce_free (encode : Term Const Γ (element ⇒ carrier)) (field : Term Const Γ element) :
    (image_introduce (Δ := Δ) encode field).FunctionExtensionalityFree := by
  simp only [image_introduce, ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.FunctionExtensionalityFree]
  exact ⟨image_apply_free _ _, True.intro⟩

theorem image_recovery_free (encode : Term Const Γ (element ⇒ carrier)) (decode : Term Const Γ (carrier ⇒ element))
    (stored : Term Const Γ carrier) (law : ProofSyntax Const Δ (leftInverse encode decode))
    (member : ProofSyntax Const Δ (.app (image encode) stored))
    (lawFree : law.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (image_recovery encode decode stored law member).FunctionExtensionalityFree := by
  unfold image_recovery
  constructor
  · exact ⟨image_apply_free _ _, memberFree⟩
  · change (_ ∧ _) ∧ _
    refine ⟨⟨True.intro, ?_⟩, True.intro⟩
    apply leftInverse_at_free
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_rename] using lawFree

theorem image_retraction_free (encode : Term Const Γ (element ⇒ carrier)) (decode : Term Const Γ (carrier ⇒ element))
    (law : ProofSyntax Const Δ (leftInverse encode decode)) (free : law.FunctionExtensionalityFree) :
    (image_retraction encode decode law).FunctionExtensionalityFree := by
  unfold image_retraction
  apply image_recovery_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_rename] using free
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

#print axioms image_retraction
#print axioms roundtrip_free

end Mettapedia.Logic.HOL.ConstructorFieldRepresentation
