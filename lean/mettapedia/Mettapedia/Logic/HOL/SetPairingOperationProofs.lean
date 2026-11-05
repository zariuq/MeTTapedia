import Mettapedia.Logic.HOL.SetPairingSchemas
import Mettapedia.Logic.HOL.PairingReconstructionSchemas
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Explicit operation abstraction for constructed set pairs

The closed binary operator reduces to the existing unordered construction.
Its membership schema is derived from actual retained set-law proofs.
Ordered applications convert explicitly to the original Kuratowski terms.
No pairing axiom or implicit beta conversion is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetPairingOperationProofs
open SetComprehensionProofs SetMembershipProofs SetPairingProofs ContextualTrinity
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}

def operator : ClosedTerm Const (object ⇒ object ⇒ object) :=
  .lam (.lam (unordered core epsilon (.var (.vs .vz)) (.var .vz)))

def applied (left right : Term Const Γ object) : Term Const Γ object :=
  .app (.app (weakenCtx Γ (operator core epsilon)) left) right

theorem operatorForm (context : Ctx Unit) : weakenCtx context (operator core epsilon) =
    .lam (.lam (unordered core epsilon (.var (.vs .vz)) (.var .vz))) := by
  induction context with
  | nil => rfl
  | cons type context ih =>
      rw [weakenCtx_cons,ih]
      simp only [HOL.weaken,HOL.rename,rename_unordered,Rename.lift]

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.weaken term) = term := instantiate_weaken point term

def beta (left right : Term Const Γ object) :
    ProofSyntax Const Δ (.eq (applied core epsilon left right) (unordered core epsilon left right)) := by
  have first : ProofSyntax Const Δ (.eq
      (applied core epsilon left right)
      (.app (.lam (unordered core epsilon (HOL.weaken left) (.var .vz))) right)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.eqApp right (ProofSyntax.beta left
      (.lam (unordered core epsilon (.var (.vs .vz)) (.var .vz)))))
    simp only [applied,operatorForm,instantiate,HOL.subst,subst_unordered,Subst.lift,Subst.single,HOL.weaken]
  have second : ProofSyntax Const Δ (.eq
      (.app (.lam (unordered core epsilon (HOL.weaken left) (.var .vz))) right)
      (unordered core epsilon left right)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta right
      (unordered core epsilon (HOL.weaken left) (.var .vz)))
    simp only [instantiate,subst_unordered,HOL.subst,Subst.single,substituteWeak]
  exact .eqTrans first second

theorem beta_free (left right : Term Const Γ object) :
    (beta (Δ := Δ) core epsilon left right).FunctionExtensionalityFree := by
  simp [beta,ProofSyntax.FunctionExtensionalityFree]

def unorderedCongr {left left' right right' : Term Const Γ object}
    (first : ProofSyntax Const Δ (.eq left left')) (second : ProofSyntax Const Δ (.eq right right')) :
    ProofSyntax Const Δ (.eq (unordered core epsilon left right) (unordered core epsilon left' right')) := by
  have leftPart : ProofSyntax Const Δ (.eq (unordered core epsilon left right) (unordered core epsilon left' right)) := by
    apply ProofSyntax.castIndices rfl ?_
      (holeCongr (unordered core epsilon (.var .vz) (HOL.weaken right)) first)
    simp only [instantiate,subst_unordered,HOL.subst,Subst.single,substituteWeak]
  have rightPart : ProofSyntax Const Δ (.eq (unordered core epsilon left' right) (unordered core epsilon left' right')) := by
    apply ProofSyntax.castIndices rfl ?_
      (holeCongr (unordered core epsilon (HOL.weaken left') (.var .vz)) second)
    simp only [instantiate,subst_unordered,HOL.subst,Subst.single,substituteWeak]
  exact .eqTrans leftPart rightPart

theorem unorderedCongr_free {left left' right right' : Term Const Γ object}
    (first : ProofSyntax Const Δ (.eq left left')) (second : ProofSyntax Const Δ (.eq right right'))
    (firstFree : first.FunctionExtensionalityFree) (secondFree : second.FunctionExtensionalityFree) :
    (unorderedCongr core epsilon first second).FunctionExtensionalityFree := by
  simp [unorderedCongr,holeCongr,ProofSyntax.FunctionExtensionalityFree,firstFree,secondFree]

def orderedApplication (left right : Term Const Γ object) : Term Const Γ object :=
  PairingReconstruction.orderedBy (applied core epsilon) left right

def orderedBeta (left right : Term Const Γ object) :
    ProofSyntax Const Δ (.eq (orderedApplication core epsilon left right) (ordered core epsilon left right)) :=
  .eqTrans (beta core epsilon (applied core epsilon left left) (applied core epsilon left right))
    (unorderedCongr core epsilon (beta core epsilon left left) (beta core epsilon left right))

theorem orderedBeta_free (left right : Term Const Γ object) :
    (orderedBeta (Δ := Δ) core epsilon left right).FunctionExtensionalityFree :=
  ⟨beta_free core epsilon _ _,unorderedCongr_free core epsilon _ _
    (beta_free core epsilon _ _) (beta_free core epsilon _ _)⟩

def membershipProof (left right point : Term Const Γ object) (laws : Laws core epsilon Δ) :
    ProofSyntax Const Δ (.and
      (.imp (member core point (applied core epsilon left right)) (.or (.eq point left) (.eq point right)))
      (.imp (.or (.eq point left) (.eq point right)) (member core point (applied core epsilon left right)))) :=
  .andI
    (.impI (unorderedElim core epsilon left right point (laws.prepend _)
      (transportBound core point (beta core epsilon left right) (.hyp 0))))
    (.impI (transportBound core point (.eqSymm (beta core epsilon left right))
      (unorderedIntro core epsilon left right point (laws.prepend _) (.hyp 0))))

theorem membershipProof_free (left right point : Term Const Γ object) (laws : Laws core epsilon Δ)
    (free : laws.Free) : (membershipProof core epsilon left right point laws).FunctionExtensionalityFree :=
  ⟨unorderedElim_free core epsilon left right point _ _ (laws.prepend_free _ free)
    ⟨beta_free core epsilon _ _,trivial⟩,
   ⟨beta_free core epsilon _ _,unorderedIntro_free core epsilon left right point _ _ (laws.prepend_free _ free) trivial⟩⟩

def membershipOperation : ClosedTerm Const (object ⇒ object ⇒ .prop) := .const (core .member)
def schema : ClosedFormula Const :=
  PairingReconstructionSchemas.membershipStatement (membershipOperation core) (operator core epsilon)

def schemaProof {theory : List (ClosedFormula Const)} (laws : Laws core epsilon theory) :
    ProofSyntax Const theory (schema core epsilon) :=
  .allI (.allI (.allI (membershipProof core epsilon (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)
    (((laws.weaken object).weaken object).weaken object))))

theorem schemaProof_free {theory : List (ClosedFormula Const)} (laws : Laws core epsilon theory) (free : laws.Free) :
    (schemaProof core epsilon laws).FunctionExtensionalityFree :=
  membershipProof_free core epsilon _ _ _ _
    (Laws.weaken_free ((laws.weaken object).weaken object) object
      (Laws.weaken_free (laws.weaken object) object (laws.weaken_free object free)))

def applicationClaim (left right first second : Term Const Γ object) : Formula Const Γ :=
  .imp (.eq (orderedApplication core epsilon left right) (orderedApplication core epsilon first second))
    (.and (.eq left first) (.eq right second))

def rawClaim (left right first second : Term Const Γ object) : Formula Const Γ :=
  .imp (.eq (ordered core epsilon left right) (ordered core epsilon first second))
    (.and (.eq left first) (.eq right second))

def convert (left right first second : Term Const Γ object)
    (proof : ProofSyntax Const Δ (applicationClaim core epsilon left right first second)) :
    ProofSyntax Const Δ (rawClaim core epsilon left right first second) :=
  .impE (.eqPropEL (ProofSyntax.impCongr
    (ProofSyntax.eqCongr (orderedBeta core epsilon left right) (orderedBeta core epsilon first second))
    (.eqRefl _))) proof

theorem convert_free (left right first second : Term Const Γ object)
    (proof : ProofSyntax Const Δ (applicationClaim core epsilon left right first second))
    (free : proof.FunctionExtensionalityFree) :
    (convert core epsilon left right first second proof).FunctionExtensionalityFree := by
  simp only [convert,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.impCongr_free,ProofSyntax.eqCongr_free]
  exact ⟨⟨⟨orderedBeta_free core epsilon _ _,orderedBeta_free core epsilon _ _⟩,trivial⟩,free⟩

def separateSecond (left right first second : Term Const Γ object)
    (injection : ProofSyntax Const Δ (rawClaim core epsilon left right first second))
    (apart : ProofSyntax Const Δ (.not (.eq right second))) :
    ProofSyntax Const Δ (.not (.eq (ordered core epsilon left right) (ordered core epsilon first second))) :=
  .notI (.notE (apart.prepend _) (.andER (.impE (injection.prepend _) (.hyp 0))))

theorem separateSecond_free (left right first second : Term Const Γ object)
    (injection : ProofSyntax Const Δ (rawClaim core epsilon left right first second))
    (apart : ProofSyntax Const Δ (.not (.eq right second)))
    (injectionFree : injection.FunctionExtensionalityFree) (apartFree : apart.FunctionExtensionalityFree) :
    (separateSecond core epsilon left right first second injection apart).FunctionExtensionalityFree := by
  simp [separateSecond,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.prepend,injectionFree,apartFree]

end Mettapedia.Logic.HOL.SetPairingOperationProofs

