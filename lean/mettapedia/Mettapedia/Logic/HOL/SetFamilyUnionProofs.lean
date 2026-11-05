import Mettapedia.Logic.HOL.SetMembershipProofs

/-!
# Retained witnesses for unions of indexed families

A family-union member yields its actual index and membership in that fibre.
Both existential witnesses retain their typed binder scopes. No choice or
semantic proof extraction is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetFamilyUnionProofs
open SetComprehensionProofs SetMembershipProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (set mapping unionLaw replacementLaw)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

def witness (domain : Term Const Γ set) (family : Term Const Γ mapping) (point : Term Const Γ set) : Formula Const Γ :=
  .ex (.and (member core (.var .vz) (HOL.weaken domain))
    (member core (HOL.weaken point) (.app (HOL.weaken family) (.var .vz))))

@[simp] theorem subst_witness (theta : Subst Const Γ Ξ) (domain : Term Const Γ set)
    (family : Term Const Γ mapping) (point : Term Const Γ set) :
    HOL.subst theta (witness core domain family point) =
      witness core (HOL.subst theta domain) (HOL.subst theta family) (HOL.subst theta point) := by
  simp only [witness,member,HOL.subst,HOL.subst_weaken,Subst.lift]

theorem rename_witness (rho : Rename Unit Γ Ξ) (domain : Term Const Γ set)
    (family : Term Const Γ mapping) (point : Term Const Γ set) :
    HOL.rename rho (witness core domain family point) =
      witness core (HOL.rename rho domain) (HOL.rename rho family) (HOL.rename rho point) := by
  simpa only [HOL.subst_ofRename] using subst_witness core (Subst.ofRename rho) domain family point

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.weaken term) = term := instantiate_weaken point term

def unionIntro (bound index point : Term Const Γ set)
    (law : ProofSyntax Const Δ (lawAt core unionLaw))
    (inBound : ProofSyntax Const Δ (member core index bound))
    (inIndex : ProofSyntax Const Δ (member core point index)) :
    ProofSyntax Const Δ (member core point (.app (.const (core .union)) bound)) := by
  apply ProofSyntax.impE (.andER (SetComprehensionProofs.union core bound point law))
  apply ProofSyntax.exI index
  apply ProofSyntax.castIndices rfl ?_ (.andI inBound inIndex)
  simp only [instantiate,member,HOL.subst,Subst.single,substituteWeak]

def unionElim (bound point : Term Const Γ set)
    (law : ProofSyntax Const Δ (lawAt core unionLaw))
    (admitted : ProofSyntax Const Δ (member core point (.app (.const (core .union)) bound))) :
    ProofSyntax Const Δ (.ex (.and (member core (.var .vz) (HOL.weaken bound))
      (member core (HOL.weaken point) (.var .vz)))) :=
  .impE (.andEL (SetComprehensionProofs.union core bound point law)) admitted

def eliminate (domain : Term Const Γ set) (family : Term Const Γ mapping) (point : Term Const Γ set)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (replacementProof : ProofSyntax Const Δ (lawAt core replacementLaw))
    (admitted : ProofSyntax Const Δ (member core point (familyUnion core domain family))) :
    ProofSyntax Const Δ (witness core domain family point) := by
  have first := unionElim core (image core domain family) point unionProof admitted
  refine ProofSyntax.exE first ?_
  let firstBody : Formula Const (set :: Γ) :=
    .and (member core (.var .vz) (HOL.weaken (image core domain family)))
      (member core (HOL.weaken point) (.var .vz))
  let firstAssumptions := firstBody :: weakenHyps (σ := set) Δ
  have firstWitness : ProofSyntax Const firstAssumptions firstBody := .hyp 0
  have imageProof : ProofSyntax Const firstAssumptions
      (member core (.var .vz) (image core (HOL.weaken domain) (HOL.weaken family))) := .andEL firstWitness
  have second := ProofSyntax.impE
    (.andEL (SetComprehensionProofs.replacement core (HOL.weaken domain) (HOL.weaken family) (.var .vz)
      ((weakenLaw core _ replacementProof).prepend firstBody))) imageProof
  refine ProofSyntax.exE second ?_
  let secondBody : Formula Const (set :: set :: Γ) :=
    .and (member core (.var .vz) (HOL.weaken (HOL.weaken domain)))
      (.eq (.app (HOL.weaken (HOL.weaken family)) (.var .vz)) (.var (.vs .vz)))
  let secondAssumptions := secondBody :: weakenHyps (σ := set) firstAssumptions
  have secondWitness : ProofSyntax Const secondAssumptions secondBody := .hyp 0
  have pointInSelected : ProofSyntax Const secondAssumptions
      (member core (HOL.weaken (HOL.weaken point)) (.var (.vs .vz))) := .andER (.hyp 1)
  have result : ProofSyntax Const secondAssumptions
      (.and (member core (.var .vz) (HOL.weaken (HOL.weaken domain)))
        (member core (HOL.weaken (HOL.weaken point))
          (.app (HOL.weaken (HOL.weaken family)) (.var .vz)))) :=
    .andI (.andEL secondWitness)
      (transportBound core _ (.eqSymm (.andER secondWitness)) pointInSelected)
  have retained : ProofSyntax Const secondAssumptions
      (witness core (HOL.weaken (HOL.weaken domain)) (HOL.weaken (HOL.weaken family))
        (HOL.weaken (HOL.weaken point))) := by
    apply ProofSyntax.exI (.var .vz)
    apply ProofSyntax.castIndices rfl ?_ result
    simp only [instantiate,HOL.subst,member,Subst.single,substituteWeak]
  apply ProofSyntax.castIndices rfl ?_ retained
  simp only [HOL.weaken,rename_witness]

theorem unionIntro_free (bound index point : Term Const Γ set)
    (law : ProofSyntax Const Δ (lawAt core unionLaw))
    (inBound : ProofSyntax Const Δ (member core index bound))
    (inIndex : ProofSyntax Const Δ (member core point index))
    (lawFree : law.FunctionExtensionalityFree) (boundFree : inBound.FunctionExtensionalityFree)
    (indexFree : inIndex.FunctionExtensionalityFree) :
    (unionIntro core bound index point law inBound inIndex).FunctionExtensionalityFree := by
  simp [unionIntro,SetComprehensionProofs.union,ProofSyntax.FunctionExtensionalityFree,lawFree,boundFree,indexFree]

theorem introduce_free (domain : Term Const Γ set) (family : Term Const Γ mapping) (index point : Term Const Γ set)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (replacementProof : ProofSyntax Const Δ (lawAt core replacementLaw))
    (inDomain : ProofSyntax Const Δ (member core index domain))
    (inFibre : ProofSyntax Const Δ (member core point (.app family index)))
    (unionFree : unionProof.FunctionExtensionalityFree) (replacementFree : replacementProof.FunctionExtensionalityFree)
    (domainFree : inDomain.FunctionExtensionalityFree) (fibreFree : inFibre.FunctionExtensionalityFree) :
    (familyUnionIntro core domain family index point unionProof replacementProof inDomain inFibre).FunctionExtensionalityFree := by
  simp [familyUnionIntro,SetComprehensionProofs.union,imageIntro,SetComprehensionProofs.replacement,
    ProofSyntax.FunctionExtensionalityFree,unionFree,replacementFree,domainFree,fibreFree]

theorem eliminate_free (domain : Term Const Γ set) (family : Term Const Γ mapping) (point : Term Const Γ set)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (replacementProof : ProofSyntax Const Δ (lawAt core replacementLaw))
    (admitted : ProofSyntax Const Δ (member core point (familyUnion core domain family)))
    (unionFree : unionProof.FunctionExtensionalityFree) (replacementFree : replacementProof.FunctionExtensionalityFree)
    (admittedFree : admitted.FunctionExtensionalityFree) :
    (eliminate core domain family point unionProof replacementProof admitted).FunctionExtensionalityFree := by
  simp [eliminate,unionElim,SetComprehensionProofs.union,SetComprehensionProofs.replacement,
    transportBound,boundCongr,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.prepend,
    weakenLaw_free,unionFree,replacementFree,admittedFree]

end Mettapedia.Logic.HOL.SetFamilyUnionProofs

