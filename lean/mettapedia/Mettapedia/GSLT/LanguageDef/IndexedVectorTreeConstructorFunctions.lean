import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilySolved
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyBranch
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyTransport
import Mettapedia.Logic.HOL.PredicateProductAbstraction

/-!
# Constructor function programs for the derived Vector-tree family

The programs abstract the actual stored constructor values. Predicate-product
membership is constructed from their original field and Vector evidence.
This is a HOL program and guard interface, not a source DTT substitution or
a global source-universe interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorFunctions
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open FiniteConstructorEncoding IndexedConstructorGuards
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {N A E : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
  (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
  (tags : Nat → Term Const Γ N) (bottom : Term Const Γ E)
  {Δ : List (Formula Const Γ)}

theorem solvedValue_subst (images : Subst Const Γ Ξ) (field : Term Const Γ E) :
    HOL.subst images (IndexedVectorTreeStoredFamilySolved.value given source numbers zero one tags bottom field) =
      IndexedVectorTreeStoredFamilySolved.value (given.substitute images)
        (HOL.subst images source) (HOL.subst images numbers) zero one
        (fun i => HOL.subst images (tags i)) (HOL.subst images bottom) (HOL.subst images field) := by
  change Term.app (.app (.app (HOL.subst images (IndexedVectorTreeStoredFamily.construct given))
    (HOL.subst images (tags 0)))
    (HOL.subst images (encode (VectorTreeFieldEmbedding.storedSignature N E)
      (IndexedVectorTreeStoredFamilySolved.occurrence (N := N) (E := E)) (field,PUnit.unit))))
    (HOL.subst images (.lam (weaken bottom))) = _
  rw [show HOL.subst images (IndexedVectorTreeStoredFamily.construct given) =
    IndexedVectorTreeStoredFamily.construct (given.substitute images) from
    IndexedVectorTreeStoredConstructorRecovery.storedConstructor_subst given images]
  rw [encode_subst]
  simp only [HOL.subst, subst_weaken]
  rfl

theorem image_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (given.predicate source) =
      (given.substitute (Subst.ofRename rho)).predicate (HOL.rename rho source) := by
  simpa only [subst_ofRename] using given.predicate_subst (Subst.ofRename rho) source

def solvedBody : Term Const (E :: Γ) E :=
  IndexedVectorTreeStoredFamilySolved.value
    (given.substitute (Subst.ofRename (Rename.weaken (σ := E))))
    (weaken source) (weaken numbers) zero one (fun i => weaken (tags i)) (weaken bottom) (.var .vz)

def solved : Term Const Γ (E ⇒ E) := .lam (solvedBody given source numbers zero one tags bottom)

private theorem cancelInputs {domain : Ty Base} (argument : Term Const Γ domain) :
    (given.substitute (Subst.ofRename (Rename.weaken (σ := domain)))).substitute (Subst.single argument) = given := by
  cases given
  simp only [VectorTreeFieldEmbedding.Inputs.substitute, subst_ofRename]
  congr 1 <;> exact instantiate_weaken argument _

theorem solvedBody_instantiate (field : Term Const Γ E) :
    instantiate field (solvedBody given source numbers zero one tags bottom) =
      IndexedVectorTreeStoredFamilySolved.value given source numbers zero one tags bottom field := by
  have moved := solvedValue_subst
    (given.substitute (Subst.ofRename (Rename.weaken (σ := E))))
    (weaken source) (weaken numbers) zero one (fun i => weaken (tags i)) (weaken bottom)
    (Subst.single field) (.var .vz)
  simpa only [solvedBody, instantiate, cancelInputs, PredicateFixedPoint.subst_single_weaken,
    HOL.subst, Subst.single] using moved

@[irreducible] def solved_apply (field : Term Const Γ E) : ProofSyntax Const Δ
    (.eq (.app (solved given source numbers zero one tags bottom) field)
      (IndexedVectorTreeStoredFamilySolved.value given source numbers zero one tags bottom field)) :=
  .castIndices rfl (congrArg (Term.eq (.app (solved given source numbers zero one tags bottom) field))
    (solvedBody_instantiate given source numbers zero one tags bottom field))
    (.beta field (solvedBody given source numbers zero one tags bottom))

theorem solved_apply_free (field : Term Const Γ E) :
    (solved_apply given source numbers zero one tags bottom (Δ := Δ) field).FunctionExtensionalityFree := by
  unfold solved_apply
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

def solvedGuard : Term Const Γ ((E ⇒ E) ⇒ .prop) :=
  PredicateProducts.pi (given.predicate source)
    (weaken (IndexedVectorTreeStoredFamily.family given source numbers zero one successor tags bottom))

private def solvedField : ProofSyntax Const
    (.app (weaken (given.predicate source)) (.var .vz) :: weakenHyps (σ := E) Δ)
    (.app ((given.substitute (Subst.ofRename (Rename.weaken (σ := E)))).predicate (weaken source)) (.var .vz)) :=
  .castIndices rfl (congrArg (fun predicate => Term.app predicate (.var .vz))
    (image_rename given source (Rename.weaken (σ := E)))) (.hyp 0)

private theorem solvedField_free :
    (solvedField given source (Δ := Δ)).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

@[irreducible] private def solvedBodyMember : ProofSyntax Const
    (.app (weaken (given.predicate source)) (.var .vz) :: weakenHyps (σ := E) Δ)
    (.app (weaken (IndexedVectorTreeStoredFamily.family given source numbers zero one successor tags bottom))
      (solvedBody given source numbers zero one tags bottom)) :=
  .castIndices rfl (congrArg (fun predicate => Term.app predicate (solvedBody given source numbers zero one tags bottom))
    (IndexedVectorTreeStoredFamilyTransport.family_rename given source numbers zero one successor tags bottom
      (Rename.weaken (σ := E))).symm)
    (IndexedVectorTreeStoredFamilySolved.member
      (given.substitute (Subst.ofRename (Rename.weaken (σ := E))))
      (weaken source) (weaken numbers) zero one successor (fun i => weaken (tags i)) (weaken bottom)
      (.var .vz) (solvedField given source))

theorem solvedBodyMember_free :
    (solvedBodyMember given source numbers zero one successor tags bottom (Δ := Δ)).FunctionExtensionalityFree := by
  have free := IndexedVectorTreeStoredFamilySolved.member_free
    (given.substitute (Subst.ofRename (Rename.weaken (σ := E))))
    (weaken source) (weaken numbers) zero one successor (fun i => weaken (tags i)) (weaken bottom)
    (.var .vz) (solvedField given source (Δ := Δ)) (solvedField_free given source)
  simpa only [solvedBodyMember, ProofSyntax.functionExtensionalityFree_castIndices] using free

@[irreducible] def solvedMember : ProofSyntax Const Δ
    (.app (solvedGuard given source numbers zero one successor tags bottom)
      (solved given source numbers zero one tags bottom)) :=
  PredicateProducts.lambdaMember (given.predicate source)
    (weaken (IndexedVectorTreeStoredFamily.family given source numbers zero one successor tags bottom))
    (solvedBody given source numbers zero one tags bottom)
    (solvedBodyMember given source numbers zero one successor tags bottom)

theorem solvedMember_free :
    (solvedMember given source numbers zero one successor tags bottom (Δ := Δ)).FunctionExtensionalityFree := by
  unfold solvedMember
  exact PredicateProducts.lambdaMember_free _ _ _ _
    (solvedBodyMember_free given source numbers zero one successor tags bottom)

namespace Native
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
variable (original : NativeVectorComputationRows.Operations Base Const) {W : Ty Base}
  (selection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.vector ⇒ W ⇒ .prop)))
  (elementSelection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.element)))
  (arraySelection : ClosedTerm Const (SelectionProofs.Selection
    (original.number ⇒ original.vector ⇒ original.number ⇒ original.element)))
  (input : VectorTreeFieldEmbedding.Inputs Const Γ original.number A original.element)
  (answer : Term Const Γ (A ⇒ .prop)) (natural : Term Const Γ (original.number ⇒ .prop))
  (unitCode : ClosedTerm Const original.number) (ordinals : Nat → Term Const Γ original.number)
  (padding : Term Const Γ original.element)

abbrev arrays := IndexedVectorTreeStoredFamilyBranch.ReaderGuard.arrays original elementSelection arraySelection

def numberRecognition {type : Ty Base} (predicate : Term Const Γ (type ⇒ .prop)) : Formula Const Γ :=
  .all (.app (weaken predicate) (.var .vz))

theorem numberRecognition_subst {type : Ty Base} (images : Subst Const Γ Ξ)
    (predicate : Term Const Γ (type ⇒ .prop)) :
    HOL.subst images (numberRecognition predicate) = numberRecognition (HOL.subst images predicate) := by
  simp only [numberRecognition,HOL.subst,subst_weaken,Subst.lift]

theorem numberRecognition_rename {type : Ty Base} (rho : Rename Base Γ Ξ)
    (predicate : Term Const Γ (type ⇒ .prop)) :
    HOL.rename rho (numberRecognition predicate) = numberRecognition (HOL.rename rho predicate) := by
  simpa only [subst_ofRename] using numberRecognition_subst (Subst.ofRename rho) predicate

private theorem vectorCode_rename (rho : Rename Base Γ Ξ)
    (predicate : Term Const Γ original.elementPredicate) (index : Term Const Γ original.number) :
    HOL.rename rho (NativeVectorAll.Reading.vectorCode original selection predicate index) =
      NativeVectorAll.Reading.vectorCode original selection (HOL.rename rho predicate) (HOL.rename rho index) := by
  simp only [NativeVectorAll.Reading.vectorCode,HOL.rename,rename_weakenCtx]

private def raiseTwo {X Y : Ty Base} : Rename Base Γ (Y :: X :: Γ) :=
  fun {_type} index => .vs (.vs index)

private theorem weakenTwice {X Y T : Ty Base} (term : Term Const Γ T) :
    weaken (σ := Y) (weaken (σ := X) term) = HOL.rename raiseTwo term := by
  simp only [weaken, HOL.rename_comp]
  rfl

def branchFamily : Term Const Γ (original.element ⇒ .prop) :=
  IndexedVectorTreeStoredFamily.family input answer natural original.zero unitCode original.successor ordinals padding

def branchBody : Term Const (original.vector :: original.number :: Γ) original.element :=
  IndexedVectorTreeStoredFamilyBranch.ReaderGuard.value original elementSelection arraySelection
    (input.substitute (Subst.ofRename raiseTwo)) (HOL.rename raiseTwo answer) (HOL.rename raiseTwo natural)
    unitCode (fun i => HOL.rename raiseTwo (ordinals i)) (HOL.rename raiseTwo padding) (.var (.vs .vz)) (.var .vz)

def branch : Term Const Γ (original.number ⇒ original.vector ⇒ original.element) :=
  .lam (.lam (branchBody original elementSelection arraySelection input answer natural unitCode ordinals padding))

theorem branchValue_subst (images : Subst Const Γ Ξ)
    (n : Term Const Γ original.number) (vector : Term Const Γ original.vector) :
    HOL.subst images (IndexedVectorTreeStoredFamilyBranch.ReaderGuard.value original elementSelection arraySelection
      input answer natural unitCode ordinals padding n vector) =
    IndexedVectorTreeStoredFamilyBranch.ReaderGuard.value original elementSelection arraySelection
      (input.substitute images) (HOL.subst images answer) (HOL.subst images natural) unitCode
      (fun i => HOL.subst images (ordinals i)) (HOL.subst images padding) (HOL.subst images n) (HOL.subst images vector) := by
  change Term.app (.app (.app (HOL.subst images (IndexedVectorTreeStoredFamily.construct input))
    (HOL.subst images (ordinals 1)))
    (HOL.subst images (encode (VectorTreeFieldEmbedding.storedSignature original.number original.element)
      (IndexedVectorTreeStoredFamilyBranch.occurrence (arrays original elementSelection arraySelection))
      (n,weakenCtx Γ original.zero,PUnit.unit))))
    (HOL.subst images ((arrays original elementSelection arraySelection).single n vector padding)) = _
  rw [show HOL.subst images (IndexedVectorTreeStoredFamily.construct input) =
    IndexedVectorTreeStoredFamily.construct (input.substitute images) from
    IndexedVectorTreeStoredConstructorRecovery.storedConstructor_subst input images]
  rw [encode_subst,VectorChildArrays.Operations.single_subst]
  have mapped : substituteArguments images
      ((VectorTreeFieldEmbedding.storedSignature original.number original.element).get
        (IndexedVectorTreeStoredFamilyBranch.occurrence (arrays original elementSelection arraySelection)))
      (n,weakenCtx Γ original.zero,PUnit.unit) =
      (HOL.subst images n,weakenCtx Ξ original.zero,PUnit.unit) := by
    change (HOL.subst images n,HOL.subst images (weakenCtx Γ original.zero),PUnit.unit) = _
    rw [subst_weakenCtx]
  rw [mapped]
  rfl

private theorem cancelTwo {X Y T : Ty Base} (first : Term Const Γ X) (second : Term Const Γ Y)
    (term : Term Const Γ T) :
    HOL.subst (Subst.cons second (Subst.single first)) (HOL.rename raiseTwo term) = term := by
  rw [HOL.subst_rename]
  change HOL.subst Subst.id term = term
  exact subst_id term

private theorem cancelInputsTwo (n : Term Const Γ original.number) (vector : Term Const Γ original.vector) :
    (input.substitute (Subst.ofRename raiseTwo)).substitute (Subst.cons vector (Subst.single n)) = input := by
  cases input
  simp only [VectorTreeFieldEmbedding.Inputs.substitute,subst_ofRename]
  congr 1 <;> exact cancelTwo n vector _

theorem branchBody_instantiate (n : Term Const Γ original.number) (vector : Term Const Γ original.vector) :
    HOL.subst (Subst.cons vector (Subst.single n))
      (branchBody original elementSelection arraySelection input answer natural unitCode ordinals padding) =
    IndexedVectorTreeStoredFamilyBranch.ReaderGuard.value original elementSelection arraySelection
      input answer natural unitCode ordinals padding n vector := by
  have moved := branchValue_subst original elementSelection arraySelection
    (input.substitute (Subst.ofRename raiseTwo)) (HOL.rename raiseTwo answer) (HOL.rename raiseTwo natural)
    unitCode (fun i => HOL.rename raiseTwo (ordinals i)) (HOL.rename raiseTwo padding)
    (Subst.cons vector (Subst.single n)) (.var (.vs .vz)) (.var .vz)
  simpa only [branchBody,cancelInputsTwo,cancelTwo,HOL.subst,Subst.cons,Subst.single] using moved

@[irreducible] def branch_apply (n : Term Const Γ original.number) (vector : Term Const Γ original.vector) :
    ProofSyntax Const Δ (.eq
      (.app (.app (branch original elementSelection arraySelection input answer natural unitCode ordinals padding) n) vector)
      (IndexedVectorTreeStoredFamilyBranch.ReaderGuard.value original elementSelection arraySelection
        input answer natural unitCode ordinals padding n vector)) :=
  .castIndices rfl (congrArg (Term.eq
    (.app (.app (branch original elementSelection arraySelection input answer natural unitCode ordinals padding) n) vector))
      ((instantiate_subst_lift vector (Subst.single n)
        (branchBody original elementSelection arraySelection input answer natural unitCode ordinals padding)).trans
        (branchBody_instantiate original elementSelection arraySelection input answer natural unitCode ordinals padding n vector)))
    (CurriedGuardProgramProofs.beta2
      (branchBody original elementSelection arraySelection input answer natural unitCode ordinals padding) n vector)

theorem branch_apply_free (n : Term Const Γ original.number) (vector : Term Const Γ original.vector) :
    (branch_apply original elementSelection arraySelection input answer natural unitCode ordinals padding
      (Δ := Δ) n vector).FunctionExtensionalityFree := by
  unfold branch_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

def vectorPredicate : Term Const (original.number :: Γ) (original.vector ⇒ .prop) :=
  NativeVectorAll.Reading.vectorCode original selection
    (weaken (branchFamily original input answer natural unitCode ordinals padding)) (.var .vz)

def branchGuard : Term Const Γ ((original.number ⇒ original.vector ⇒ original.element) ⇒ .prop) :=
  PredicateProducts.pi (PredicateProducts.full original.number)
    (PredicateProducts.pi (vectorPredicate original selection input answer natural unitCode ordinals padding)
      (weaken (weaken (branchFamily original input answer natural unitCode ordinals padding))))

private def numberArgument : Formula Const (original.number :: Γ) :=
  .app (PredicateProducts.full original.number) (.var .vz)

private def vectorArgument : Formula Const (original.vector :: original.number :: Γ) :=
  .app (weaken (vectorPredicate original selection input answer natural unitCode ordinals padding)) (.var .vz)

private def numberHypotheses := numberArgument original :: weakenHyps (σ := original.number) Δ
private def vectorHypotheses := vectorArgument original selection input answer natural unitCode ordinals padding ::
  weakenHyps (σ := original.vector) (numberHypotheses original (Δ := Δ))

private def raiseProof {B : Type u} {C : Ty B → Type v} {Ω : Ctx B} {T : Ty B}
    {assumptions : List (Formula C Ω)} {claim : Formula C Ω}
    (proof : ProofSyntax C assumptions claim) (guard : Formula C (T :: Ω)) :
    ProofSyntax C (guard :: weakenHyps assumptions) (weaken claim) :=
  (proof.renameShared Rename.weaken).prepend guard

private theorem raiseProof_free {B : Type u} {C : Ty B → Type v} {Ω : Ctx B} {T : Ty B}
    {assumptions : List (Formula C Ω)} {claim : Formula C Ω}
    (proof : ProofSyntax C assumptions claim) (guard : Formula C (T :: Ω))
    (free : proof.FunctionExtensionalityFree) : (raiseProof proof guard).FunctionExtensionalityFree := by
  simpa only [raiseProof,ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,
    ProofSyntax.renameShared_eq,ProofSyntax.functionExtensionalityFree_rename] using free

private def allGuardAt {B : Type u} {C : Ty B → Type v} {Ω : Ctx B} {T : Ty B}
    {assumptions : List (Formula C Ω)} (predicate : Term C Ω (T ⇒ .prop)) (argument : Term C Ω T)
    (proof : ProofSyntax C assumptions (.all (.app (weaken predicate) (.var .vz)))) :
    ProofSyntax C assumptions (.app predicate argument) :=
  .castIndices rfl (congrArg (fun code => Term.app code argument) (instantiate_weaken argument predicate))
    (.allE argument proof)

private theorem allGuardAt_free {B : Type u} {C : Ty B → Type v} {Ω : Ctx B} {T : Ty B}
    {assumptions : List (Formula C Ω)} (predicate : Term C Ω (T ⇒ .prop)) (argument : Term C Ω T)
    (proof : ProofSyntax C assumptions (.all (.app (weaken predicate) (.var .vz))))
    (free : proof.FunctionExtensionalityFree) :
    (allGuardAt predicate argument proof).FunctionExtensionalityFree := by
  unfold allGuardAt
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

private def numeric (recognition : ProofSyntax Const Δ (numberRecognition natural)) :
    ProofSyntax Const (vectorHypotheses original selection input answer natural unitCode ordinals padding (Δ := Δ))
      (.app (HOL.rename raiseTwo natural) (.var (.vs .vz))) :=
  allGuardAt (HOL.rename raiseTwo natural) (.var (.vs .vz))
    (.castIndices rfl (by
      rw [weakenTwice,numberRecognition_rename]
      rfl)
      (raiseProof (raiseProof recognition (numberArgument original))
        (vectorArgument original selection input answer natural unitCode ordinals padding)))

private theorem numeric_free (recognition : ProofSyntax Const Δ (numberRecognition natural))
    (free : recognition.FunctionExtensionalityFree) :
    (numeric original selection input answer natural unitCode ordinals padding recognition).FunctionExtensionalityFree := by
  unfold numeric
  apply allGuardAt_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact raiseProof_free _ _ (raiseProof_free _ _ free)

private theorem familyAtTwo :
    weaken (σ := original.vector) (weaken (σ := original.number)
      (branchFamily original input answer natural unitCode ordinals padding)) =
    IndexedVectorTreeStoredFamily.family (input.substitute (Subst.ofRename raiseTwo))
      (HOL.rename raiseTwo answer) (HOL.rename raiseTwo natural) original.zero unitCode original.successor
      (fun i => HOL.rename raiseTwo (ordinals i)) (HOL.rename raiseTwo padding) :=
  (weakenTwice _).trans (IndexedVectorTreeStoredFamilyTransport.family_rename
    input answer natural original.zero unitCode original.successor ordinals padding raiseTwo)

@[irreducible] private def vectorEvidence : ProofSyntax Const
    (vectorHypotheses original selection input answer natural unitCode ordinals padding (Δ := Δ))
    (.app (NativeVectorAll.Reading.vectorCode original selection
      (IndexedVectorTreeStoredFamily.family (input.substitute (Subst.ofRename raiseTwo))
        (HOL.rename raiseTwo answer) (HOL.rename raiseTwo natural) original.zero unitCode original.successor
        (fun i => HOL.rename raiseTwo (ordinals i)) (HOL.rename raiseTwo padding)) (.var (.vs .vz))) (.var .vz)) :=
  .castIndices rfl (by
    have moved : weaken (σ := original.vector)
        (vectorPredicate original selection input answer natural unitCode ordinals padding) =
        NativeVectorAll.Reading.vectorCode original selection
          (IndexedVectorTreeStoredFamily.family (input.substitute (Subst.ofRename raiseTwo))
            (HOL.rename raiseTwo answer) (HOL.rename raiseTwo natural) original.zero unitCode original.successor
            (fun i => HOL.rename raiseTwo (ordinals i)) (HOL.rename raiseTwo padding)) (.var (.vs .vz)) := by
      change HOL.rename Rename.weaken
        (NativeVectorAll.Reading.vectorCode original selection
          (weaken (branchFamily original input answer natural unitCode ordinals padding)) (.var .vz)) = _
      rw [vectorCode_rename]
      exact congrArg (fun predicate => NativeVectorAll.Reading.vectorCode original selection predicate (.var (.vs .vz)))
        (familyAtTwo original input answer natural unitCode ordinals padding)
    exact congrArg (fun predicate => Term.app predicate (.var .vz)) moved)
    (.hyp (Δ := vectorArgument original selection input answer natural unitCode ordinals padding ::
      weakenHyps (σ := original.vector) (numberHypotheses original (Δ := Δ))) 0)

private theorem vectorEvidence_free :
    (vectorEvidence original selection input answer natural unitCode ordinals padding (Δ := Δ)).FunctionExtensionalityFree := by
  unfold vectorEvidence
  simp only [ProofSyntax.functionExtensionalityFree_castIndices]
  trivial

@[irreducible] private def branchBodyMember
    (recognition : ProofSyntax Const Δ (numberRecognition natural))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ) :
    ProofSyntax Const (vectorHypotheses original selection input answer natural unitCode ordinals padding (Δ := Δ))
      (.app (weaken (σ := original.vector) (weaken (σ := original.number)
        (branchFamily original input answer natural unitCode ordinals padding)))
        (branchBody original elementSelection arraySelection input answer natural unitCode ordinals padding)) :=
  .castIndices rfl (congrArg (fun code => Term.app code
    (branchBody original elementSelection arraySelection input answer natural unitCode ordinals padding))
      (familyAtTwo original input answer natural unitCode ordinals padding).symm)
    (IndexedVectorTreeStoredFamilyBranch.ReaderGuard.member original selection elementSelection arraySelection
      (input.substitute (Subst.ofRename raiseTwo)) (HOL.rename raiseTwo answer) (HOL.rename raiseTwo natural)
      unitCode (fun i => HOL.rename raiseTwo (ordinals i)) (HOL.rename raiseTwo padding)
      (.var (.vs .vz)) (.var .vz)
      (numeric original selection input answer natural unitCode ordinals padding recognition)
      (((premises.weaken original.number).prepend (numberArgument original)).weaken original.vector |>.prepend
        (vectorArgument original selection input answer natural unitCode ordinals padding))
      (((arithmetic.rename (Rename.weaken (σ := original.number))).prepend (numberArgument original)).rename
        (Rename.weaken (σ := original.vector)) |>.prepend
          (vectorArgument original selection input answer natural unitCode ordinals padding))
      (vectorEvidence original selection input answer natural unitCode ordinals padding))

private theorem branchBodyMember_free
    (recognition : ProofSyntax Const Δ (numberRecognition natural))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (recognitionFree : recognition.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free) :
    (branchBodyMember original selection elementSelection arraySelection input answer natural unitCode ordinals padding
      recognition premises arithmetic).FunctionExtensionalityFree := by
  let guardN := numberArgument original (Γ := Γ)
  let guardV := vectorArgument original selection input answer natural unitCode ordinals padding
  let first := (premises.weaken original.number).prepend guardN
  let second := (first.weaken original.vector).prepend guardV
  have firstFree : first.FunctionExtensionalityFree :=
    (premises.weaken original.number).prepend_free guardN (premises.weaken_free original.number premisesFree)
  have secondFree : second.FunctionExtensionalityFree :=
    (first.weaken original.vector).prepend_free guardV (first.weaken_free original.vector firstFree)
  let arithN := (arithmetic.rename (Rename.weaken (σ := original.number))).prepend guardN
  let arithV := (arithN.rename (Rename.weaken (σ := original.vector))).prepend guardV
  have arithNFree : arithN.Free :=
    (arithmetic.rename (Rename.weaken (σ := original.number))).prepend_free guardN
      (arithmetic.rename_free Rename.weaken arithmeticFree)
  have arithVFree : arithV.Free :=
    (arithN.rename (Rename.weaken (σ := original.vector))).prepend_free guardV
      (arithN.rename_free Rename.weaken arithNFree)
  have result := IndexedVectorTreeStoredFamilyBranch.ReaderGuard.member_free original selection elementSelection arraySelection
    (input.substitute (Subst.ofRename raiseTwo)) (HOL.rename raiseTwo answer) (HOL.rename raiseTwo natural)
    unitCode (fun i => HOL.rename raiseTwo (ordinals i)) (HOL.rename raiseTwo padding) (.var (.vs .vz)) (.var .vz)
    (numeric original selection input answer natural unitCode ordinals padding recognition) second arithV
    (vectorEvidence original selection input answer natural unitCode ordinals padding)
    (numeric_free original selection input answer natural unitCode ordinals padding recognition recognitionFree)
    secondFree arithVFree (vectorEvidence_free original selection input answer natural unitCode ordinals padding)
  simpa only [branchBodyMember,ProofSyntax.functionExtensionalityFree_castIndices,second,first,arithV,arithN,guardN,guardV] using result

@[irreducible] def branchMember
    (recognition : ProofSyntax Const Δ (numberRecognition natural))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ) :
    ProofSyntax Const Δ (.app (branchGuard original selection input answer natural unitCode ordinals padding)
      (branch original elementSelection arraySelection input answer natural unitCode ordinals padding)) :=
  PredicateProducts.lambdaMember (PredicateProducts.full original.number)
    (PredicateProducts.pi (vectorPredicate original selection input answer natural unitCode ordinals padding)
      (weaken (weaken (branchFamily original input answer natural unitCode ordinals padding))))
    (.lam (branchBody original elementSelection arraySelection input answer natural unitCode ordinals padding))
    (PredicateProducts.lambdaMember (vectorPredicate original selection input answer natural unitCode ordinals padding)
      (weaken (weaken (branchFamily original input answer natural unitCode ordinals padding)))
      (branchBody original elementSelection arraySelection input answer natural unitCode ordinals padding)
      (branchBodyMember original selection elementSelection arraySelection input answer natural unitCode ordinals padding
        recognition premises arithmetic))

theorem branchMember_free
    (recognition : ProofSyntax Const Δ (numberRecognition natural))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (recognitionFree : recognition.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free) :
    (branchMember original selection elementSelection arraySelection input answer natural unitCode ordinals padding
      recognition premises arithmetic).FunctionExtensionalityFree := by
  unfold branchMember
  apply PredicateProducts.lambdaMember_free
  apply PredicateProducts.lambdaMember_free
  exact branchBodyMember_free original selection elementSelection arraySelection input answer natural unitCode ordinals padding
    recognition premises arithmetic recognitionFree premisesFree arithmeticFree

def fullNumberRecognition {type : Ty Base} :
    ProofSyntax Const Δ (numberRecognition (PredicateProducts.full type)) :=
  .allI (.impE (.eqPropER (.beta (.var .vz) .top)) .topI)

theorem fullNumberRecognition_free {type : Ty Base} :
    (fullNumberRecognition (Const := Const) (type := type) (Δ := Δ)).FunctionExtensionalityFree := by trivial

#print axioms branchMember
#print axioms branchMember_free
#print axioms branch_apply_free
end Native

#print axioms solvedValue_subst
#print axioms solvedMember
#print axioms solvedMember_free
#print axioms solved_apply_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorFunctions
