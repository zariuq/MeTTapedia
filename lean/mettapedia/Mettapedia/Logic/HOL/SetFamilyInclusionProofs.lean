import Mettapedia.Logic.HOL.SetInclusionProofs
import Mettapedia.Logic.HOL.SetSumProjectionProofs
import Mettapedia.Logic.HOL.SetTraceProofs

/-!
# Guarded family inclusion and dependent sums

Fibre inclusion is required only at indices belonging to the source domain.
Dependent sum inclusion transports the actual first and second fields of a
member and reconstructs the same ordered pair in the destination sum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetFamilyInclusionProofs
open SetComprehensionProofs SetMembershipProofs SetInclusionProofs
open Embedding.ZFSetHenkinInterpretation (set mapping)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

private theorem substituteWeak {type added : Ty Unit} (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.weaken term) = term := instantiate_weaken point term

def familyIncluded (domain : Term Const Γ set) (before after : Term Const Γ mapping) : Formula Const Γ :=
  .all (.imp (member core (.var .vz) (HOL.weaken domain))
    (included core (.app (HOL.weaken before) (.var .vz)) (.app (HOL.weaken after) (.var .vz))))

theorem subst_familyIncluded (theta : Subst Const Γ Ξ) (domain : Term Const Γ set) (before after : Term Const Γ mapping) :
    HOL.subst theta (familyIncluded core domain before after) =
      familyIncluded core (HOL.subst theta domain) (HOL.subst theta before) (HOL.subst theta after) := by
  simp only [familyIncluded,HOL.subst,member,HOL.subst_weaken,Subst.lift,subst_included]

theorem rename_familyIncluded (rho : Rename Unit Γ Ξ) (domain : Term Const Γ set) (before after : Term Const Γ mapping) :
    HOL.rename rho (familyIncluded core domain before after) =
      familyIncluded core (HOL.rename rho domain) (HOL.rename rho before) (HOL.rename rho after) := by
  simpa only [HOL.subst_ofRename] using subst_familyIncluded core (Subst.ofRename rho) domain before after

def weakenFamily {added : Ty Unit} (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (proof : ProofSyntax Const Δ (familyIncluded core domain before after)) :
    ProofSyntax Const (weakenHyps (σ := added) Δ)
      (familyIncluded core (HOL.weaken domain) (HOL.weaken before) (HOL.weaken after)) :=
  .castIndices rfl (rename_familyIncluded core Rename.weaken domain before after) (PredicateFixedPoint.weakenProof proof)

def familyAt (domain : Term Const Γ set) (before after : Term Const Γ mapping) (point : Term Const Γ set)
    (proof : ProofSyntax Const Δ (familyIncluded core domain before after))
    (present : ProofSyntax Const Δ (member core point domain)) :
    ProofSyntax Const Δ (included core (.app before point) (.app after point)) := by
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ (.allE point proof)) present
  simp only [instantiate,HOL.subst,member,subst_included,Subst.single,substituteWeak]

variable (epsilon : ClosedTerm Const (SelectionProofs.Selection set))

def sumAt (beforeDomain afterDomain : Term Const Γ set) (beforeFamily afterFamily : Term Const Γ mapping)
    (point : Term Const Γ set) (laws : SetTraceProofs.Laws core epsilon Δ)
    (domain : ProofSyntax Const Δ (included core beforeDomain afterDomain))
    (fibres : ProofSyntax Const Δ (familyIncluded core beforeDomain beforeFamily afterFamily))
    (received : ProofSyntax Const Δ (member core point (SetDependentSumProofs.sum core epsilon beforeDomain beforeFamily))) :
    ProofSyntax Const Δ (member core point (SetDependentSumProofs.sum core epsilon afterDomain afterFamily)) := by
  let first := SetPairProjectionProofs.first core epsilon point
  let second := SetPairProjectionProofs.second core epsilon point
  have fields := SetSumProjectionProofs.typedFields core epsilon beforeDomain beforeFamily point laws.pairing laws.union received
  have firstTyped := subsetElim core beforeDomain afterDomain first domain (.andEL fields)
  have fibre := familyAt core beforeDomain beforeFamily afterFamily first fibres (.andEL fields)
  have secondTyped := subsetElim core (.app beforeFamily first) (.app afterFamily first) second fibre (.andEL (.andER fields))
  have reconstructed := SetDependentSumProofs.introduce core epsilon afterDomain afterFamily first second
    laws.pairing laws.union firstTyped secondTyped
  exact transportValue core _ (.andER (.andER fields)) reconstructed

def sumInclusion (beforeDomain afterDomain : Term Const Γ set) (beforeFamily afterFamily : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ)
    (domain : ProofSyntax Const Δ (included core beforeDomain afterDomain))
    (fibres : ProofSyntax Const Δ (familyIncluded core beforeDomain beforeFamily afterFamily)) :
    ProofSyntax Const Δ (included core (SetDependentSumProofs.sum core epsilon beforeDomain beforeFamily)
      (SetDependentSumProofs.sum core epsilon afterDomain afterFamily)) := by
  have body : ProofSyntax Const (weakenHyps (σ := set) Δ) (.imp
      (member core (.var .vz) (SetDependentSumProofs.sum core epsilon (HOL.weaken beforeDomain) (HOL.weaken beforeFamily)))
      (member core (.var .vz) (SetDependentSumProofs.sum core epsilon (HOL.weaken afterDomain) (HOL.weaken afterFamily)))) :=
    .impI (sumAt core epsilon (HOL.weaken beforeDomain) (HOL.weaken afterDomain) (HOL.weaken beforeFamily) (HOL.weaken afterFamily)
      (.var .vz) ((laws.weaken set).prepend _)
      ((weakenInclusion core beforeDomain afterDomain domain).prepend _)
      ((weakenFamily core beforeDomain beforeFamily afterFamily fibres).prepend _) (.hyp 0))
  apply ProofSyntax.castIndices rfl ?_ (.allI body)
  simp only [included,HOL.weaken,SetDependentSumProofs.rename_sum]

theorem weakenFamily_free {added : Ty Unit} (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (proof : ProofSyntax Const Δ (familyIncluded core domain before after)) (free : proof.FunctionExtensionalityFree) :
    (weakenFamily (added := added) core domain before after proof).FunctionExtensionalityFree := by
  simpa [weakenFamily,PredicateFixedPoint.weakenProof] using free

theorem familyAt_free (domain : Term Const Γ set) (before after : Term Const Γ mapping) (point : Term Const Γ set)
    (proof : ProofSyntax Const Δ (familyIncluded core domain before after))
    (present : ProofSyntax Const Δ (member core point domain))
    (proofFree : proof.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (familyAt core domain before after point proof present).FunctionExtensionalityFree := by
  simp only [familyAt,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices]
  exact ⟨proofFree,presentFree⟩

theorem sumAt_free (beforeDomain afterDomain : Term Const Γ set) (beforeFamily afterFamily : Term Const Γ mapping)
    (point : Term Const Γ set) (laws : SetTraceProofs.Laws core epsilon Δ)
    (domain : ProofSyntax Const Δ (included core beforeDomain afterDomain))
    (fibres : ProofSyntax Const Δ (familyIncluded core beforeDomain beforeFamily afterFamily))
    (received : ProofSyntax Const Δ (member core point (SetDependentSumProofs.sum core epsilon beforeDomain beforeFamily)))
    (lawsFree : laws.Free) (domainFree : domain.FunctionExtensionalityFree) (fibresFree : fibres.FunctionExtensionalityFree)
    (receivedFree : received.FunctionExtensionalityFree) :
    (sumAt core epsilon beforeDomain afterDomain beforeFamily afterFamily point laws domain fibres received).FunctionExtensionalityFree := by
  have fieldsFree := SetSumProjectionProofs.typedFields_free core epsilon beforeDomain beforeFamily point
    laws.pairing laws.union received lawsFree.pairing lawsFree.union receivedFree
  unfold sumAt
  apply transportValue_free
  · exact fieldsFree
  · apply SetDependentSumProofs.introduce_free
    · exact lawsFree.pairing
    · exact lawsFree.union
    · exact eliminate_free core _ _ _ domain _ domainFree fieldsFree
    · apply eliminate_free
      · exact familyAt_free core _ _ _ _ fibres _ fibresFree fieldsFree
      · exact fieldsFree

theorem sumInclusion_free (beforeDomain afterDomain : Term Const Γ set) (beforeFamily afterFamily : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ)
    (domain : ProofSyntax Const Δ (included core beforeDomain afterDomain))
    (fibres : ProofSyntax Const Δ (familyIncluded core beforeDomain beforeFamily afterFamily))
    (lawsFree : laws.Free) (domainFree : domain.FunctionExtensionalityFree) (fibresFree : fibres.FunctionExtensionalityFree) :
    (sumInclusion core epsilon beforeDomain afterDomain beforeFamily afterFamily laws domain fibres).FunctionExtensionalityFree := by
  unfold sumInclusion
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply sumAt_free
  · exact (laws.weaken set).prepend_free _ (laws.weaken_free set lawsFree)
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core _ _ domain domainFree)
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenFamily_free core _ _ _ fibres fibresFree)
  · trivial

end Mettapedia.Logic.HOL.SetFamilyInclusionProofs
