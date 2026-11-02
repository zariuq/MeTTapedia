import Mettapedia.Logic.HOL.ConstructorPredicateRepresentation

/-!
# A selected field embedded through a complete constructor inventory

The carrier constructor and its payload projection use the same finite
signature. Other fields of the selected row are supplied explicitly; the
selected field itself needs no default value. Recovery follows from the
constructor-field law and the two retained selection principles.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorFieldEmbedding
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {element number branches carrier : Ty Base} {Δ : List (Formula Const Γ)}

def remainingFields : {fields : List (Ty Base)} → Var fields element → List (Ty Base)
  | _ :: rest, .vz => rest
  | first :: _, .vs prior => first :: remainingFields prior

def insertField {fields : List (Ty Base)} (index : Var fields element)
    (field : Term Const Γ element) (fillers : Arguments Const Γ (remainingFields index)) :
    Arguments Const Γ fields :=
  match index with
  | .vz => (field,fillers)
  | .vs prior => (fillers.1,insertField prior field fillers.2)

theorem insertedField {fields : List (Ty Base)} (index : Var fields element)
    (field : Term Const Γ element) (fillers : Arguments Const Γ (remainingFields index)) :
    argumentAt index (insertField index field fillers) = field := by
  induction index with
  | vz => rfl
  | vs prior previous => exact previous field fillers.2

theorem insertField_subst (images : Subst Const Γ Ξ) {fields : List (Ty Base)}
    (index : Var fields element) (field : Term Const Γ element)
    (fillers : Arguments Const Γ (remainingFields index)) :
    substituteArguments images fields (insertField index field fillers) =
      insertField index (subst images field) (substituteArguments images (remainingFields index) fillers) := by
  induction index with
  | vz => rfl
  | vs prior previous => exact congrArg (Prod.mk (subst images fillers.1)) (previous field fillers.2)

theorem insertField_weaken {fields : List (Ty Base)} (index : Var fields element)
    (field : Term Const Γ element) (fillers : Arguments Const Γ (remainingFields index)) {bound : Ty Base} :
    weakenArguments bound fields (insertField index field fillers) =
      insertField index (weaken field) (weakenArguments bound (remainingFields index) fillers) := by
  induction index with
  | vz => rfl
  | vs prior previous => exact congrArg (Prod.mk (weaken fillers.1)) (previous field fillers.2)

variable (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
  (index : Var (signature.get occurrence) element)
  (raw : Term Const Γ (ConstructorProjections.Constructor number (payloadType signature) branches carrier))
  (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
  (fillers : Arguments Const Γ (remainingFields index))
  (payloadSelection : Term Const Γ (SelectionProofs.Selection (payloadType signature)))
  (fieldSelection : Term Const Γ (SelectionProofs.Selection element))

def value (field : Term Const Γ element) : Term Const Γ carrier :=
  ConstructorProjections.apply raw marker (encode signature occurrence (insertField index field fillers)) fixedBranches

def embedding : Term Const Γ (element ⇒ carrier) :=
  .lam (value signature occurrence index (weaken raw) (weaken marker) (weaken fixedBranches)
    (weakenArguments element (remainingFields index) fillers) (.var .vz))

def decoder : Term Const Γ (carrier ⇒ element) :=
  .lam (.app (FiniteConstructorFieldProjection.projection signature occurrence index (weaken fieldSelection))
    (.app (ConstructorProjections.secondProjection (weaken payloadSelection) (weaken raw)) (.var .vz)))

theorem value_subst (images : Subst Const Γ Ξ) (field : Term Const Γ element) :
    subst images (value signature occurrence index raw marker fixedBranches fillers field) =
      value signature occurrence index (subst images raw) (subst images marker) (subst images fixedBranches)
        (substituteArguments images (remainingFields index) fillers) (subst images field) := by
  simp only [value,ConstructorProjections.subst_apply,encode_subst,insertField_subst]

theorem embedding_subst (images : Subst Const Γ Ξ) :
    subst images (embedding signature occurrence index raw marker fixedBranches fillers) =
      embedding signature occurrence index (subst images raw) (subst images marker) (subst images fixedBranches)
        (substituteArguments images (remainingFields index) fillers) := by
  simp only [embedding,subst,value_subst,subst_weaken,Subst.lift]
  apply congrArg (fun other => Term.lam
    (value signature occurrence index (weaken (subst images raw)) (weaken (subst images marker))
      (weaken (subst images fixedBranches)) other (.var .vz)))
  exact substituteArguments_weaken images element (remainingFields index) fillers

theorem decoder_subst (images : Subst Const Γ Ξ) :
    subst images (decoder signature occurrence index raw payloadSelection fieldSelection) =
      decoder signature occurrence index (subst images raw) (subst images payloadSelection) (subst images fieldSelection) := by
  simp only [decoder,subst,FiniteConstructorFieldProjection.projection_subst,
    ConstructorProjections.subst_secondProjection,subst_weaken,Subst.lift]

def embedding_apply (field : Term Const Γ element) :
    ProofSyntax Const Δ (.eq (.app (embedding signature occurrence index raw marker fixedBranches fillers) field)
      (value signature occurrence index raw marker fixedBranches fillers field)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta field
    (value signature occurrence index (weaken raw) (weaken marker) (weaken fixedBranches)
      (weakenArguments element (remainingFields index) fillers) (.var .vz)))
  simp only [instantiate,value_subst,subst,Subst.single]
  rw [show subst (Subst.single field) (weaken raw) = raw from instantiate_weaken field raw,
    show subst (Subst.single field) (weaken marker) = marker from instantiate_weaken field marker,
    show subst (Subst.single field) (weaken fixedBranches) = fixedBranches from instantiate_weaken field fixedBranches]
  rw [substituteArguments_single]
  rfl

def decoder_apply (stored : Term Const Γ carrier) :
    ProofSyntax Const Δ (.eq (.app (decoder signature occurrence index raw payloadSelection fieldSelection) stored)
      (.app (FiniteConstructorFieldProjection.projection signature occurrence index fieldSelection)
        (.app (ConstructorProjections.secondProjection payloadSelection raw) stored))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta stored
    (.app (FiniteConstructorFieldProjection.projection signature occurrence index (weaken fieldSelection))
      (.app (ConstructorProjections.secondProjection (weaken payloadSelection) (weaken raw)) (.var .vz))))
  simp only [instantiate,subst,FiniteConstructorFieldProjection.projection_subst,
    ConstructorProjections.subst_secondProjection,Subst.single]
  rw [show subst (Subst.single stored) (weaken raw) = raw from instantiate_weaken stored raw,
    show subst (Subst.single stored) (weaken payloadSelection) = payloadSelection from instantiate_weaken stored payloadSelection,
    show subst (Subst.single stored) (weaken fieldSelection) = fieldSelection from instantiate_weaken stored fieldSelection]
  rfl

variable (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle payloadSelection))
  (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle fieldSelection))
  (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))

def roundtrip (field : Term Const Γ element) :
    ProofSyntax Const Δ (.eq (.app (decoder signature occurrence index raw payloadSelection fieldSelection)
      (.app (embedding signature occurrence index raw marker fixedBranches fillers) field)) field) := by
  apply ProofSyntax.eqTrans
    (.eqAppArg (decoder signature occurrence index raw payloadSelection fieldSelection)
      (embedding_apply signature occurrence index raw marker fixedBranches fillers field))
  apply ProofSyntax.eqTrans (decoder_apply signature occurrence index raw payloadSelection fieldSelection
    (value signature occurrence index raw marker fixedBranches fillers field))
  apply ProofSyntax.eqTrans
    (.eqAppArg (FiniteConstructorFieldProjection.projection signature occurrence index fieldSelection)
      (ConstructorProjections.second_at payloadSelection raw marker
        (encode signature occurrence (insertField index field fillers)) fixedBranches payloadChoice injectivity))
  exact ProofSyntax.castIndices rfl (congrArg (Term.eq _) (insertedField index field fillers))
    (FiniteConstructorFieldProjection.projection_at signature occurrence index fieldSelection
      (insertField index field fillers) fieldChoice)

def roundtripLaw :
    ProofSyntax Const Δ (ConstructorFieldRepresentation.leftInverse
      (embedding signature occurrence index raw marker fixedBranches fillers)
      (decoder signature occurrence index raw payloadSelection fieldSelection)) := by
  apply ProofSyntax.allI (σ := element)
  have pc : ProofSyntax Const (weakenHyps (σ := element) Δ) (SelectionProofs.principle (weaken payloadSelection)) :=
    .castIndices rfl (ConstructorProjections.rename_selection Rename.weaken payloadSelection) (payloadChoice.rename Rename.weaken)
  have fc : ProofSyntax Const (weakenHyps (σ := element) Δ) (SelectionProofs.principle (weaken fieldSelection)) :=
    .castIndices rfl (ConstructorProjections.rename_selection Rename.weaken fieldSelection) (fieldChoice.rename Rename.weaken)
  have ci : ProofSyntax Const (weakenHyps (σ := element) Δ) (ConstructorProjections.fieldInjective (weaken raw)) :=
    .castIndices rfl (ConstructorProjections.rename_fieldInjective Rename.weaken raw) (injectivity.rename Rename.weaken)
  apply ProofSyntax.castIndices rfl ?_ (roundtrip signature occurrence index (weaken raw) (weaken marker) (weaken fixedBranches)
    (weakenArguments element (remainingFields index) fillers) (weaken payloadSelection) (weaken fieldSelection) pc fc ci (.var .vz))
  simp only [weaken,← subst_ofRename,embedding_subst,decoder_subst,
    FiniteConstructorFieldProjection.substituteArguments_shift]

theorem embedding_apply_free (field : Term Const Γ element) :
    (embedding_apply (Δ := Δ) signature occurrence index raw marker fixedBranches fillers field).FunctionExtensionalityFree := by
  simp only [embedding_apply,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]

theorem decoder_apply_free (stored : Term Const Γ carrier) :
    (decoder_apply (Δ := Δ) signature occurrence index raw payloadSelection fieldSelection stored).FunctionExtensionalityFree := by
  simp only [decoder_apply,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]

theorem roundtrip_free
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (constructorFree : injectivity.FunctionExtensionalityFree) (field : Term Const Γ element) :
    (roundtrip signature occurrence index raw marker fixedBranches fillers payloadSelection fieldSelection
      payloadChoice fieldChoice injectivity field).FunctionExtensionalityFree := by
  exact ⟨embedding_apply_free _ _ _ _ _ _ _ _, ⟨decoder_apply_free _ _ _ _ _ _ _,
    ⟨ConstructorProjections.second_at_free _ _ _ _ _ _ _ payloadFree constructorFree,
      (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        (FiniteConstructorFieldProjection.projection_at_free _ _ _ _ _ _ fieldFree)⟩⟩⟩

theorem roundtripLaw_free
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (constructorFree : injectivity.FunctionExtensionalityFree) :
    (roundtripLaw signature occurrence index raw marker fixedBranches fillers payloadSelection fieldSelection
      payloadChoice fieldChoice injectivity).FunctionExtensionalityFree := by
  unfold roundtripLaw
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply roundtrip_free
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr payloadFree)
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr fieldFree)
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_rename _ _).mpr constructorFree)

def predicateRecovery (predicate : Term Const Γ (element ⇒ .prop)) (stored : Term Const Γ carrier)
    (member : ProofSyntax Const Δ (.app (ConstructorPredicateRepresentation.lift
      (embedding signature occurrence index raw marker fixedBranches fillers) predicate) stored)) :
    ProofSyntax Const Δ (.eq
      (.app (embedding signature occurrence index raw marker fixedBranches fillers)
        (.app (decoder signature occurrence index raw payloadSelection fieldSelection) stored)) stored) :=
  ConstructorPredicateRepresentation.recover _ _ predicate stored
    (roundtripLaw signature occurrence index raw marker fixedBranches fillers payloadSelection fieldSelection
      payloadChoice fieldChoice injectivity) member

theorem predicateRecovery_free
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (constructorFree : injectivity.FunctionExtensionalityFree)
    (predicate : Term Const Γ (element ⇒ .prop)) (stored : Term Const Γ carrier)
    (member : ProofSyntax Const Δ (.app (ConstructorPredicateRepresentation.lift
      (embedding signature occurrence index raw marker fixedBranches fillers) predicate) stored))
    (memberFree : member.FunctionExtensionalityFree) :
    (predicateRecovery signature occurrence index raw marker fixedBranches fillers payloadSelection fieldSelection
      payloadChoice fieldChoice injectivity predicate stored member).FunctionExtensionalityFree :=
  ConstructorPredicateRepresentation.recover_free _ _ predicate stored _ member
    (roundtripLaw_free signature occurrence index raw marker fixedBranches fillers payloadSelection fieldSelection
      payloadChoice fieldChoice injectivity payloadFree fieldFree constructorFree) memberFree

#print axioms roundtrip
#print axioms roundtripLaw
#print axioms roundtripLaw_free
#print axioms predicateRecovery
#print axioms predicateRecovery_free
end Mettapedia.Logic.HOL.FiniteConstructorFieldEmbedding
