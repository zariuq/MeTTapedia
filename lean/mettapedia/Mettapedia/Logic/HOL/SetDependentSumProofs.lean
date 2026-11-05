import Mettapedia.Logic.HOL.SetFamilyUnionProofs
import Mettapedia.Logic.HOL.SetGraphProofs

/-!
# Retained dependent sums built from indexed unions

The sum is the union, over the domain, of images of each fibre under ordered
pairing. Its pair-membership law derives both the index guard and the fibre
guard. The same set construction is the trace of a functional graph.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetDependentSumProofs
open SetComprehensionProofs SetMembershipProofs SetPairingProofs ContextualTrinity
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (mapping unionLaw)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

def fibreMap (point : Term Const Γ object) : Term Const Γ mapping :=
  .lam (ordered core epsilon (HOL.weaken point) (.var .vz))

def pairImage (point fibre : Term Const Γ object) : Term Const Γ object :=
  image core fibre (fibreMap core epsilon point)

def familyMap (family : Term Const Γ mapping) : Term Const Γ mapping :=
  .lam (pairImage core epsilon (.var .vz) (.app (HOL.weaken family) (.var .vz)))

def sum (domain : Term Const Γ object) (family : Term Const Γ mapping) : Term Const Γ object :=
  familyUnion core domain (familyMap core epsilon family)

@[simp] theorem subst_fibreMap (theta : Subst Const Γ Ξ) (point : Term Const Γ object) :
    HOL.subst theta (fibreMap core epsilon point) = fibreMap core epsilon (HOL.subst theta point) := by
  simp only [fibreMap,HOL.subst,subst_ordered,HOL.subst_weaken,Subst.lift]

@[simp] theorem subst_pairImage (theta : Subst Const Γ Ξ) (point fibre : Term Const Γ object) :
    HOL.subst theta (pairImage core epsilon point fibre) =
      pairImage core epsilon (HOL.subst theta point) (HOL.subst theta fibre) := by
  simp only [pairImage,image,HOL.subst,subst_fibreMap]

@[simp] theorem subst_familyMap (theta : Subst Const Γ Ξ) (family : Term Const Γ mapping) :
    HOL.subst theta (familyMap core epsilon family) = familyMap core epsilon (HOL.subst theta family) := by
  simp only [familyMap,HOL.subst,subst_pairImage,HOL.subst_weaken,Subst.lift]

@[simp] theorem subst_sum (theta : Subst Const Γ Ξ) (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.subst theta (sum core epsilon domain family) =
      sum core epsilon (HOL.subst theta domain) (HOL.subst theta family) := by
  simp only [sum,familyUnion,image,HOL.subst,subst_familyMap]

theorem rename_fibreMap (rho : Rename Unit Γ Ξ) (point : Term Const Γ object) :
    HOL.rename rho (fibreMap core epsilon point) = fibreMap core epsilon (HOL.rename rho point) := by
  simpa only [HOL.subst_ofRename] using subst_fibreMap core epsilon (Subst.ofRename rho) point

theorem rename_familyMap (rho : Rename Unit Γ Ξ) (family : Term Const Γ mapping) :
    HOL.rename rho (familyMap core epsilon family) = familyMap core epsilon (HOL.rename rho family) := by
  simpa only [HOL.subst_ofRename] using subst_familyMap core epsilon (Subst.ofRename rho) family

theorem rename_sum (rho : Rename Unit Γ Ξ) (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.rename rho (sum core epsilon domain family) =
      sum core epsilon (HOL.rename rho domain) (HOL.rename rho family) := by
  simpa only [HOL.subst_ofRename] using subst_sum core epsilon (Subst.ofRename rho) domain family

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.weaken term) = term := instantiate_weaken point term

def fibreBeta (point value : Term Const Γ object) :
    ProofSyntax Const Δ (.eq (.app (fibreMap core epsilon point) value) (ordered core epsilon point value)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta value (ordered core epsilon (HOL.weaken point) (.var .vz)))
  simp only [fibreMap,instantiate,subst_ordered,HOL.subst,Subst.single,substituteWeak]

def familyBeta (family : Term Const Γ mapping) (point : Term Const Γ object) :
    ProofSyntax Const Δ (.eq (.app (familyMap core epsilon family) point)
      (pairImage core epsilon point (.app family point))) := by
  apply ProofSyntax.castIndices rfl ?_
    (.beta point (pairImage core epsilon (.var .vz) (.app (HOL.weaken family) (.var .vz))))
  simp only [familyMap,instantiate,subst_pairImage,HOL.subst,Subst.single,substituteWeak]

def introduce (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (inDomain : ProofSyntax Const Δ (member core point domain))
    (inFibre : ProofSyntax Const Δ (member core value (.app family point))) :
    ProofSyntax Const Δ (member core (ordered core epsilon point value) (sum core epsilon domain family)) := by
  have inImage := transportValue core _ (fibreBeta core epsilon point value)
    (imageIntro core (.app family point) (fibreMap core epsilon point) value laws.replacement inFibre)
  have inApplication := transportBound core _ (.eqSymm (familyBeta core epsilon family point)) inImage
  exact familyUnionIntro core domain (familyMap core epsilon family) point (ordered core epsilon point value)
    unionProof laws.replacement inDomain inApplication

def eliminate (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (admitted : ProofSyntax Const Δ (member core (ordered core epsilon point value) (sum core epsilon domain family))) :
    ProofSyntax Const Δ (.and (member core point domain) (member core value (.app family point))) := by
  have first := SetFamilyUnionProofs.eliminate core domain (familyMap core epsilon family)
    (ordered core epsilon point value) unionProof laws.replacement admitted
  refine ProofSyntax.exE first ?_
  let firstBody : Formula Const (object :: Γ) :=
    .and (member core (.var .vz) (HOL.weaken domain))
      (member core (HOL.weaken (ordered core epsilon point value))
        (.app (HOL.weaken (familyMap core epsilon family)) (.var .vz)))
  let firstAssumptions := firstBody :: weakenHyps (σ := object) Δ
  let firstLaws := (laws.weaken object).prepend firstBody
  have firstWitness : ProofSyntax Const firstAssumptions firstBody := .hyp 0
  have familyEquation : ProofSyntax Const firstAssumptions
      (.eq (.app (HOL.weaken (familyMap core epsilon family)) (.var .vz))
        (pairImage core epsilon (.var .vz) (.app (HOL.weaken family) (.var .vz)))) := by
    apply ProofSyntax.castIndices rfl ?_ (familyBeta core epsilon (HOL.weaken family) (.var .vz))
    simp only [HOL.weaken,rename_familyMap]
  have inImage := transportBound core _ familyEquation (.andER firstWitness)
  have second := ProofSyntax.impE
    (.andEL (SetComprehensionProofs.replacement core (.app (HOL.weaken family) (.var .vz))
      (fibreMap core epsilon (.var .vz)) (HOL.weaken (ordered core epsilon point value)) firstLaws.replacement)) inImage
  refine ProofSyntax.exE second ?_
  let secondBody : Formula Const (object :: object :: Γ) :=
    .and (member core (.var .vz) (.app (HOL.weaken (HOL.weaken family)) (.var (.vs .vz))))
      (.eq (.app (HOL.weaken (fibreMap core epsilon (.var .vz))) (.var .vz))
        (HOL.weaken (HOL.weaken (ordered core epsilon point value))))
  let secondAssumptions := secondBody :: weakenHyps (σ := object) firstAssumptions
  let secondLaws := (firstLaws.weaken object).prepend secondBody
  have secondWitness : ProofSyntax Const secondAssumptions secondBody := .hyp 0
  have pairEqual : ProofSyntax Const secondAssumptions
      (.eq (ordered core epsilon (.var (.vs .vz)) (.var .vz))
        (ordered core epsilon (HOL.weaken (HOL.weaken point)) (HOL.weaken (HOL.weaken value)))) := by
    apply ProofSyntax.eqTrans (ProofSyntax.eqSymm (fibreBeta core epsilon (.var (.vs .vz)) (.var .vz)))
    apply ProofSyntax.castIndices rfl ?_ (.andER secondWitness)
    simp only [HOL.weaken,rename_fibreMap,rename_ordered,HOL.rename,Rename.weaken]
  have fields := orderedInjective core epsilon (.var (.vs .vz)) (.var .vz)
    (HOL.weaken (HOL.weaken point)) (HOL.weaken (HOL.weaken value)) secondLaws pairEqual
  have inDomain : ProofSyntax Const secondAssumptions
      (member core (.var (.vs .vz)) (HOL.weaken (HOL.weaken domain))) := .andEL (.hyp 1)
  have fibreValue := transportValue core _ (.andER fields) (.andEL secondWitness)
  have selected := transportBound core _ (.eqAppArg (HOL.weaken (HOL.weaken family)) (.andEL fields)) fibreValue
  change ProofSyntax Const secondAssumptions
    (.and (member core (HOL.weaken (HOL.weaken point)) (HOL.weaken (HOL.weaken domain)))
      (member core (HOL.weaken (HOL.weaken value))
        (.app (HOL.weaken (HOL.weaken family)) (HOL.weaken (HOL.weaken point)))))
  exact .andI (transportValue core _ (.andEL fields) inDomain) selected

def membership (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw)) :
    ProofSyntax Const Δ (.and
      (.imp (member core (ordered core epsilon point value) (sum core epsilon domain family))
        (.and (member core point domain) (member core value (.app family point))))
      (.imp (.and (member core point domain) (member core value (.app family point)))
        (member core (ordered core epsilon point value) (sum core epsilon domain family)))) :=
  .andI (.impI (eliminate core epsilon domain family point value (laws.prepend _) (unionProof.prepend _) (.hyp 0)))
    (.impI (introduce core epsilon domain family point value (laws.prepend _) (unionProof.prepend _)
      (.andEL (.hyp 0)) (.andER (.hyp 0))))

theorem fibreBeta_free (point value : Term Const Γ object) :
    (fibreBeta (Δ := Δ) core epsilon point value).FunctionExtensionalityFree := by
  simp [fibreBeta,ProofSyntax.FunctionExtensionalityFree]

theorem familyBeta_free (family : Term Const Γ mapping) (point : Term Const Γ object) :
    (familyBeta (Δ := Δ) core epsilon family point).FunctionExtensionalityFree := by
  simp [familyBeta,ProofSyntax.FunctionExtensionalityFree]

theorem introduce_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (inDomain : ProofSyntax Const Δ (member core point domain))
    (inFibre : ProofSyntax Const Δ (member core value (.app family point)))
    (lawsFree : laws.Free) (unionFree : unionProof.FunctionExtensionalityFree)
    (domainFree : inDomain.FunctionExtensionalityFree) (fibreFree : inFibre.FunctionExtensionalityFree) :
    (introduce core epsilon domain family point value laws unionProof inDomain inFibre).FunctionExtensionalityFree := by
  apply SetFamilyUnionProofs.introduce_free core _ _ _ _ _ _ _ _ unionFree lawsFree.replacement domainFree
  exact ⟨familyBeta_free core epsilon _ _,⟨fibreBeta_free core epsilon _ _,
    imageIntro_free core _ _ _ _ _ lawsFree.replacement fibreFree⟩⟩

theorem eliminate_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (admitted : ProofSyntax Const Δ (member core (ordered core epsilon point value) (sum core epsilon domain family)))
    (lawsFree : laws.Free) (unionFree : unionProof.FunctionExtensionalityFree)
    (admittedFree : admitted.FunctionExtensionalityFree) :
    (eliminate core epsilon domain family point value laws unionProof admitted).FunctionExtensionalityFree := by
  simp [eliminate,ProofSyntax.FunctionExtensionalityFree,transportValue,valueCongr,transportBound,boundCongr,
    SetComprehensionProofs.replacement,familyBeta,fibreBeta,
    SetFamilyUnionProofs.eliminate_free,lawsFree.replacement,unionFree,admittedFree]
  constructor
  · exact ((laws.weaken object).prepend_free _ (laws.weaken_free object lawsFree)).replacement
  apply orderedInjective_free
  · exact (((laws.weaken object).prepend _).weaken object).prepend_free _
      (Laws.weaken_free ((laws.weaken object).prepend _) object
        ((laws.weaken object).prepend_free _ (laws.weaken_free object lawsFree)))
  · simp [ProofSyntax.FunctionExtensionalityFree]

theorem membership_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (lawsFree : laws.Free) (unionFree : unionProof.FunctionExtensionalityFree) :
    (membership core epsilon domain family point value laws unionProof).FunctionExtensionalityFree := by
  simp only [membership,ProofSyntax.FunctionExtensionalityFree]
  exact ⟨eliminate_free core epsilon _ _ _ _ _ _ _ (laws.prepend_free _ lawsFree)
      (by simpa [ProofSyntax.prepend] using unionFree) trivial,
    introduce_free core epsilon _ _ _ _ _ _ _ _ (laws.prepend_free _ lawsFree)
      (by simpa [ProofSyntax.prepend] using unionFree) trivial trivial⟩

def outsideFibre (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (absent : ProofSyntax Const Δ (.not (member core value (.app family point)))) :
    ProofSyntax Const Δ (.not (member core (ordered core epsilon point value) (sum core epsilon domain family))) :=
  .notI (.notE (absent.prepend _) (.andER
    (eliminate core epsilon domain family point value (laws.prepend _) (unionProof.prepend _) (.hyp 0))))

theorem outsideFibre_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (absent : ProofSyntax Const Δ (.not (member core value (.app family point))))
    (lawsFree : laws.Free) (unionFree : unionProof.FunctionExtensionalityFree)
    (absentFree : absent.FunctionExtensionalityFree) :
    (outsideFibre core epsilon domain family point value laws unionProof absent).FunctionExtensionalityFree :=
  ⟨by simpa [ProofSyntax.prepend] using absentFree,
   eliminate_free core epsilon _ _ _ _ _ _ _ (laws.prepend_free _ lawsFree)
     (by simpa [ProofSyntax.prepend] using unionFree) trivial⟩

end Mettapedia.Logic.HOL.SetDependentSumProofs

