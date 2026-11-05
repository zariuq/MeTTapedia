import Mettapedia.Logic.HOL.SetPairProjectionProofs

/-!
# Retained typed projections for dependent set sums

A sum-membership proof supplies actual ordered-pair witnesses. Selection
reconstructs that value, and the sum law types both selected fields.
The domain and fibre guards remain part of the retained result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetSumProjectionProofs
open SetComprehensionProofs SetMembershipProofs SetPairingProofs SetDependentSumProofs SetPairProjectionProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (mapping unionLaw)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}

def existsPair (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (pair : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (admitted : ProofSyntax Const Δ (member core pair (sum core epsilon domain family))) :
    ProofSyntax Const Δ (pairExists core epsilon pair) := by
  have firstWitness := SetFamilyUnionProofs.eliminate core domain (familyMap core epsilon family)
    pair unionProof laws.replacement admitted
  refine ProofSyntax.exE firstWitness ?_
  let firstBody : Formula Const (object :: Γ) :=
    .and (member core (.var .vz) (HOL.weaken domain))
      (member core (HOL.weaken pair) (.app (HOL.weaken (familyMap core epsilon family)) (.var .vz)))
  let firstAssumptions := firstBody :: weakenHyps (σ := object) Δ
  let firstLaws := (laws.weaken object).prepend firstBody
  have firstGiven : ProofSyntax Const firstAssumptions firstBody := .hyp 0
  have familyEquation : ProofSyntax Const firstAssumptions
      (.eq (.app (HOL.weaken (familyMap core epsilon family)) (.var .vz))
        (pairImage core epsilon (.var .vz) (.app (HOL.weaken family) (.var .vz)))) := by
    apply ProofSyntax.castIndices rfl ?_ (familyBeta core epsilon (HOL.weaken family) (.var .vz))
    simp only [HOL.weaken,rename_familyMap]
  have inImage := transportBound core _ familyEquation (.andER firstGiven)
  have secondWitness := ProofSyntax.impE
    (.andEL (SetComprehensionProofs.replacement core (.app (HOL.weaken family) (.var .vz))
      (fibreMap core epsilon (.var .vz)) (HOL.weaken pair) firstLaws.replacement)) inImage
  refine ProofSyntax.exE secondWitness ?_
  let secondBody : Formula Const (object :: object :: Γ) :=
    .and (member core (.var .vz) (.app (HOL.weaken (HOL.weaken family)) (.var (.vs .vz))))
      (.eq (.app (HOL.weaken (fibreMap core epsilon (.var .vz))) (.var .vz)) (HOL.weaken (HOL.weaken pair)))
  let secondAssumptions := secondBody :: weakenHyps (σ := object) firstAssumptions
  have secondGiven : ProofSyntax Const secondAssumptions secondBody := .hyp 0
  have pairEqual : ProofSyntax Const secondAssumptions
      (.eq (ordered core epsilon (.var (.vs .vz)) (.var .vz)) (HOL.weaken (HOL.weaken pair))) := by
    apply ProofSyntax.eqTrans (ProofSyntax.eqSymm (fibreBeta core epsilon (.var (.vs .vz)) (.var .vz)))
    apply ProofSyntax.castIndices rfl ?_ (.andER secondGiven)
    simp only [HOL.weaken,rename_fibreMap,HOL.rename,Rename.weaken]
  have retained := existsOfEquality core epsilon (.var (.vs .vz)) (.var .vz) (HOL.weaken (HOL.weaken pair)) pairEqual
  apply ProofSyntax.castIndices rfl ?_ retained
  simp only [HOL.weaken,rename_pairExists]

def typedFields (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (pair : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (admitted : ProofSyntax Const Δ (member core pair (sum core epsilon domain family))) :
    ProofSyntax Const Δ (.and
      (member core (first core epsilon pair) domain)
      (.and (member core (second core epsilon pair) (.app family (first core epsilon pair)))
        (.eq (ordered core epsilon (first core epsilon pair) (second core epsilon pair)) pair))) := by
  have reconstruction := reconstruct core epsilon pair laws.selection
    (existsPair core epsilon domain family pair laws unionProof admitted)
  have asPair := transportValue core _ (.eqSymm reconstruction) admitted
  have fields := SetDependentSumProofs.eliminate core epsilon domain family
    (first core epsilon pair) (second core epsilon pair) laws unionProof asPair
  exact .andI (.andEL fields) (.andI (.andER fields) reconstruction)

theorem existsPair_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (pair : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (admitted : ProofSyntax Const Δ (member core pair (sum core epsilon domain family)))
    (lawsFree : laws.Free) (unionFree : unionProof.FunctionExtensionalityFree)
    (admittedFree : admitted.FunctionExtensionalityFree) :
    (existsPair core epsilon domain family pair laws unionProof admitted).FunctionExtensionalityFree := by
  simp [existsPair,ProofSyntax.FunctionExtensionalityFree,SetFamilyUnionProofs.eliminate_free,
    transportBound,boundCongr,SetComprehensionProofs.replacement,familyBeta,fibreBeta,
    existsOfEquality_free,unionFree,lawsFree.replacement,admittedFree]
  exact ((laws.weaken object).prepend_free _ (laws.weaken_free object lawsFree)).replacement

theorem typedFields_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (pair : Term Const Γ object) (laws : Laws core epsilon Δ)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (admitted : ProofSyntax Const Δ (member core pair (sum core epsilon domain family)))
    (lawsFree : laws.Free) (unionFree : unionProof.FunctionExtensionalityFree)
    (admittedFree : admitted.FunctionExtensionalityFree) :
    (typedFields core epsilon domain family pair laws unionProof admitted).FunctionExtensionalityFree := by
  have existenceFree := existsPair_free core epsilon domain family pair laws unionProof admitted lawsFree unionFree admittedFree
  let reconstruction := reconstruct core epsilon pair laws.selection
    (existsPair core epsilon domain family pair laws unionProof admitted)
  let asPair := transportValue core (sum core epsilon domain family) (.eqSymm reconstruction) admitted
  have reconstructionFree : reconstruction.FunctionExtensionalityFree :=
    reconstruct_free core epsilon pair laws.selection _ lawsFree.selection existenceFree
  have asPairFree : asPair.FunctionExtensionalityFree := ⟨reconstructionFree,admittedFree⟩
  have fieldsFree := SetDependentSumProofs.eliminate_free core epsilon domain family
    (first core epsilon pair) (second core epsilon pair) laws unionProof asPair lawsFree unionFree asPairFree
  simp only [typedFields,ProofSyntax.FunctionExtensionalityFree]
  exact ⟨fieldsFree,fieldsFree,reconstructionFree⟩

end Mettapedia.Logic.HOL.SetSumProjectionProofs

