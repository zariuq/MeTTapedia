import Mettapedia.Logic.HOL.SetFamilyInclusionProofs

/-!
# Retained monotonicity of unions and indexed unions

Union membership is transported through its actual witness. For an indexed
union, domain inclusion and guarded fibre inclusion transport the chosen
index and its membership, then introduce that witness in the destination.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetUnionInclusionProofs
open SetComprehensionProofs SetMembershipProofs SetInclusionProofs SetFamilyInclusionProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (set mapping unionLaw replacementLaw)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
variable {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}

def unionAt (before after point : Term Const Γ set)
    (law : ProofSyntax Const Δ (lawAt core unionLaw))
    (inclusion : ProofSyntax Const Δ (included core before after))
    (received : ProofSyntax Const Δ (member core point (.app (.const (core .union)) before))) :
    ProofSyntax Const Δ (member core point (.app (.const (core .union)) after)) := by
  have witness := SetFamilyUnionProofs.unionElim core before point law received
  refine ProofSyntax.exE witness ?_
  let body : Formula Const (set :: Γ) := .and (member core (.var .vz) (HOL.weaken before))
    (member core (HOL.weaken point) (.var .vz))
  let assumptions := body :: weakenHyps (σ := set) Δ
  have given : ProofSyntax Const assumptions body := .hyp 0
  exact SetFamilyUnionProofs.unionIntro core (HOL.weaken after) (.var .vz) (HOL.weaken point)
    ((weakenLaw core unionLaw law).prepend body)
    (subsetElim core (HOL.weaken before) (HOL.weaken after) (.var .vz)
      ((weakenInclusion core before after inclusion).prepend body) (.andEL given)) (.andER given)

def unionInclusion (before after : Term Const Γ set)
    (law : ProofSyntax Const Δ (lawAt core unionLaw))
    (inclusion : ProofSyntax Const Δ (included core before after)) :
    ProofSyntax Const Δ (included core (.app (.const (core .union)) before) (.app (.const (core .union)) after)) :=
  .allI (.impI (unionAt core (HOL.weaken before) (HOL.weaken after) (.var .vz)
    ((weakenLaw core unionLaw law).prepend _) ((weakenInclusion core before after inclusion).prepend _) (.hyp 0)))

def familyUnionAt (beforeDomain afterDomain : Term Const Γ set) (beforeFamily afterFamily : Term Const Γ mapping)
    (point : Term Const Γ set)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (replacementProof : ProofSyntax Const Δ (lawAt core replacementLaw))
    (domain : ProofSyntax Const Δ (included core beforeDomain afterDomain))
    (fibres : ProofSyntax Const Δ (familyIncluded core beforeDomain beforeFamily afterFamily))
    (received : ProofSyntax Const Δ (member core point (familyUnion core beforeDomain beforeFamily))) :
    ProofSyntax Const Δ (member core point (familyUnion core afterDomain afterFamily)) := by
  have witness := SetFamilyUnionProofs.eliminate core beforeDomain beforeFamily point unionProof replacementProof received
  refine ProofSyntax.exE witness ?_
  let body : Formula Const (set :: Γ) := .and (member core (.var .vz) (HOL.weaken beforeDomain))
    (member core (HOL.weaken point) (.app (HOL.weaken beforeFamily) (.var .vz)))
  let assumptions := body :: weakenHyps (σ := set) Δ
  have given : ProofSyntax Const assumptions body := .hyp 0
  have destinationIndex := subsetElim core (HOL.weaken beforeDomain) (HOL.weaken afterDomain) (.var .vz)
    ((weakenInclusion core beforeDomain afterDomain domain).prepend body) (.andEL given)
  have fibre := familyAt core (HOL.weaken beforeDomain) (HOL.weaken beforeFamily) (HOL.weaken afterFamily) (.var .vz)
    ((weakenFamily core beforeDomain beforeFamily afterFamily fibres).prepend body) (.andEL given)
  have destinationMember := subsetElim core (.app (HOL.weaken beforeFamily) (.var .vz))
    (.app (HOL.weaken afterFamily) (.var .vz)) (HOL.weaken point) fibre (.andER given)
  exact familyUnionIntro core (HOL.weaken afterDomain) (HOL.weaken afterFamily) (.var .vz) (HOL.weaken point)
    ((weakenLaw core unionLaw unionProof).prepend body) ((weakenLaw core replacementLaw replacementProof).prepend body)
    destinationIndex destinationMember

def familyUnionInclusion (beforeDomain afterDomain : Term Const Γ set) (beforeFamily afterFamily : Term Const Γ mapping)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (replacementProof : ProofSyntax Const Δ (lawAt core replacementLaw))
    (domain : ProofSyntax Const Δ (included core beforeDomain afterDomain))
    (fibres : ProofSyntax Const Δ (familyIncluded core beforeDomain beforeFamily afterFamily)) :
    ProofSyntax Const Δ (included core (familyUnion core beforeDomain beforeFamily) (familyUnion core afterDomain afterFamily)) :=
  .allI (.impI (familyUnionAt core (HOL.weaken beforeDomain) (HOL.weaken afterDomain)
    (HOL.weaken beforeFamily) (HOL.weaken afterFamily) (.var .vz)
    ((weakenLaw core unionLaw unionProof).prepend _) ((weakenLaw core replacementLaw replacementProof).prepend _)
    ((weakenInclusion core beforeDomain afterDomain domain).prepend _)
    ((weakenFamily core beforeDomain beforeFamily afterFamily fibres).prepend _) (.hyp 0)))

theorem unionAt_free (before after point : Term Const Γ set)
    (law : ProofSyntax Const Δ (lawAt core unionLaw))
    (inclusion : ProofSyntax Const Δ (included core before after))
    (received : ProofSyntax Const Δ (member core point (.app (.const (core .union)) before)))
    (lawFree : law.FunctionExtensionalityFree) (inclusionFree : inclusion.FunctionExtensionalityFree)
    (receivedFree : received.FunctionExtensionalityFree) :
    (unionAt core before after point law inclusion received).FunctionExtensionalityFree := by
  unfold unionAt
  constructor
  · simpa [SetFamilyUnionProofs.unionElim,SetComprehensionProofs.union,ProofSyntax.FunctionExtensionalityFree]
      using (And.intro lawFree receivedFree)
  · apply SetFamilyUnionProofs.unionIntro_free
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenLaw_free core _ law lawFree)
    · apply SetInclusionProofs.eliminate_free
      · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core _ _ inclusion inclusionFree)
      · trivial
    · trivial

theorem unionInclusion_free (before after : Term Const Γ set)
    (law : ProofSyntax Const Δ (lawAt core unionLaw))
    (inclusion : ProofSyntax Const Δ (included core before after))
    (lawFree : law.FunctionExtensionalityFree) (inclusionFree : inclusion.FunctionExtensionalityFree) :
    (unionInclusion core before after law inclusion).FunctionExtensionalityFree := by
  unfold unionInclusion
  apply unionAt_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenLaw_free core _ law lawFree)
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core _ _ inclusion inclusionFree)
  · trivial

theorem familyUnionAt_free (beforeDomain afterDomain : Term Const Γ set) (beforeFamily afterFamily : Term Const Γ mapping)
    (point : Term Const Γ set)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (replacementProof : ProofSyntax Const Δ (lawAt core replacementLaw))
    (domain : ProofSyntax Const Δ (included core beforeDomain afterDomain))
    (fibres : ProofSyntax Const Δ (familyIncluded core beforeDomain beforeFamily afterFamily))
    (received : ProofSyntax Const Δ (member core point (familyUnion core beforeDomain beforeFamily)))
    (unionFree : unionProof.FunctionExtensionalityFree) (replacementFree : replacementProof.FunctionExtensionalityFree)
    (domainFree : domain.FunctionExtensionalityFree) (fibresFree : fibres.FunctionExtensionalityFree)
    (receivedFree : received.FunctionExtensionalityFree) :
    (familyUnionAt core beforeDomain afterDomain beforeFamily afterFamily point unionProof replacementProof domain fibres received).FunctionExtensionalityFree := by
  unfold familyUnionAt
  constructor
  · exact SetFamilyUnionProofs.eliminate_free core _ _ _ _ _ _ unionFree replacementFree receivedFree
  · apply SetFamilyUnionProofs.introduce_free
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenLaw_free core _ unionProof unionFree)
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenLaw_free core _ replacementProof replacementFree)
    · apply SetInclusionProofs.eliminate_free
      · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core _ _ domain domainFree)
      · trivial
    · apply SetInclusionProofs.eliminate_free
      · apply familyAt_free
        · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenFamily_free core _ _ _ fibres fibresFree)
        · trivial
      · trivial

theorem familyUnionInclusion_free (beforeDomain afterDomain : Term Const Γ set) (beforeFamily afterFamily : Term Const Γ mapping)
    (unionProof : ProofSyntax Const Δ (lawAt core unionLaw))
    (replacementProof : ProofSyntax Const Δ (lawAt core replacementLaw))
    (domain : ProofSyntax Const Δ (included core beforeDomain afterDomain))
    (fibres : ProofSyntax Const Δ (familyIncluded core beforeDomain beforeFamily afterFamily))
    (unionFree : unionProof.FunctionExtensionalityFree) (replacementFree : replacementProof.FunctionExtensionalityFree)
    (domainFree : domain.FunctionExtensionalityFree) (fibresFree : fibres.FunctionExtensionalityFree) :
    (familyUnionInclusion core beforeDomain afterDomain beforeFamily afterFamily unionProof replacementProof domain fibres).FunctionExtensionalityFree := by
  unfold familyUnionInclusion
  apply familyUnionAt_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenLaw_free core _ unionProof unionFree)
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenLaw_free core _ replacementProof replacementFree)
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core _ _ domain domainFree)
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenFamily_free core _ _ _ fibres fibresFree)
  · trivial

end Mettapedia.Logic.HOL.SetUnionInclusionProofs
