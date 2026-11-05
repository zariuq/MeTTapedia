import Mettapedia.Logic.HOL.SetUnionInclusionProofs
import Mettapedia.Logic.HOL.SetTraceProductProofs

/-!
# Retained fibre covariance for dependent trace products

Fibre inclusion transports the indexed union of possible outputs, its union
of trace values and the resulting pair support. A stored trace keeps both its
support bound and its application guard in the enlarged product.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetTraceProductInclusionProofs
open SetComprehensionProofs SetMembershipProofs SetInclusionProofs SetFamilyInclusionProofs
open SetUnionInclusionProofs SetTraceProductProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (set mapping)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection set))
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

theorem renameValues (rho : Rename Unit Γ Ξ) (domain : Term Const Γ set) (family : Term Const Γ mapping) :
    HOL.rename rho (values core domain family) = values core (HOL.rename rho domain) (HOL.rename rho family) := by
  simpa only [HOL.subst_ofRename] using subst_values core (Subst.ofRename rho) domain family

theorem renameSupportFamily (rho : Rename Unit Γ Ξ) (domain : Term Const Γ set) (family : Term Const Γ mapping) :
    HOL.rename rho (supportFamily core domain family) = supportFamily core (HOL.rename rho domain) (HOL.rename rho family) := by
  simpa only [HOL.subst_ofRename] using subst_supportFamily core (Subst.ofRename rho) domain family

def valuesInclusion (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ)
    (fibres : ProofSyntax Const Δ (familyIncluded core domain before after)) :
    ProofSyntax Const Δ (included core (values core domain before) (values core domain after)) :=
  unionInclusion core _ _ laws.union
    (familyUnionInclusion core domain domain before after laws.union laws.pairing.replacement (reflexive core domain) fibres)

def supportFamilies (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (received : ProofSyntax Const Δ (included core (values core domain before) (values core domain after))) :
    ProofSyntax Const Δ (familyIncluded core domain (supportFamily core domain before) (supportFamily core domain after)) := by
  have body : ProofSyntax Const (weakenHyps (σ := set) Δ) (.imp (member core (.var .vz) (HOL.weaken domain))
      (included core (.app (supportFamily core (HOL.weaken domain) (HOL.weaken before)) (.var .vz))
        (.app (supportFamily core (HOL.weaken domain) (HOL.weaken after)) (.var .vz)))) :=
    .impI (transportEndpoints core (.eqSymm (supportBeta core (HOL.weaken domain) (HOL.weaken before) (.var .vz)))
      (.eqSymm (supportBeta core (HOL.weaken domain) (HOL.weaken after) (.var .vz)))
      ((weakenInclusion core _ _ received).prepend _))
  apply ProofSyntax.castIndices rfl ?_ (.allI body)
  simp only [familyIncluded,HOL.weaken,renameSupportFamily]

def supportInclusion (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ)
    (fibres : ProofSyntax Const Δ (familyIncluded core domain before after)) :
    ProofSyntax Const Δ (included core (support core epsilon domain before) (support core epsilon domain after)) :=
  sumInclusion core epsilon domain domain _ _ laws (reflexive core domain)
    (supportFamilies core domain before after (valuesInclusion core epsilon domain before after laws fibres))

def weakenGuard {added : Ty Unit} (domain : Term Const Γ set) (family : Term Const Γ mapping) (relation : Term Const Γ set)
    (proof : ProofSyntax Const Δ (guard core epsilon domain family relation)) :
    ProofSyntax Const (weakenHyps (σ := added) Δ) (guard core epsilon (HOL.weaken domain) (HOL.weaken family) (HOL.weaken relation)) :=
  .castIndices rfl (rename_guard core epsilon Rename.weaken domain family relation) (PredicateFixedPoint.weakenProof proof)

def guardTransport (domain : Term Const Γ set) (before after : Term Const Γ mapping) (relation : Term Const Γ set)
    (fibres : ProofSyntax Const Δ (familyIncluded core domain before after))
    (received : ProofSyntax Const Δ (guard core epsilon domain before relation)) :
    ProofSyntax Const Δ (guard core epsilon domain after relation) := by
  have body : ProofSyntax Const (weakenHyps (σ := set) Δ) (.imp (member core (.var .vz) (HOL.weaken domain))
      (member core (SetTraceProofs.application core epsilon (HOL.weaken relation) (.var .vz))
        (.app (HOL.weaken after) (.var .vz)))) :=
    .impI (subsetElim core (.app (HOL.weaken before) (.var .vz)) (.app (HOL.weaken after) (.var .vz)) _
      (familyAt core (HOL.weaken domain) (HOL.weaken before) (HOL.weaken after) (.var .vz)
        ((weakenFamily core domain before after fibres).prepend _) (.hyp 0))
      (guardAt core epsilon (HOL.weaken domain) (HOL.weaken before) (HOL.weaken relation) (.var .vz)
        ((weakenGuard core epsilon domain before relation received).prepend _) (.hyp 0)))
  exact .allI body

def productAt (domain : Term Const Γ set) (before after : Term Const Γ mapping) (relation : Term Const Γ set)
    (laws : SetTraceProofs.Laws core epsilon Δ)
    (fibres : ProofSyntax Const Δ (familyIncluded core domain before after))
    (received : ProofSyntax Const Δ (member core relation (product core epsilon domain before))) :
    ProofSyntax Const Δ (member core relation (product core epsilon domain after)) :=
  introduce core epsilon domain after relation laws
    (transitive core relation (support core epsilon domain before) (support core epsilon domain after)
      (productBound core epsilon domain before relation laws received) (supportInclusion core epsilon domain before after laws fibres))
    (guardTransport core epsilon domain before after relation fibres (productGuard core epsilon domain before relation laws received))

@[irreducible] def productInclusion (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ)
    (fibres : ProofSyntax Const Δ (familyIncluded core domain before after)) :
    ProofSyntax Const Δ (included core (product core epsilon domain before) (product core epsilon domain after)) := by
  have body : ProofSyntax Const (weakenHyps (σ := set) Δ) (.imp
      (member core (.var .vz) (product core epsilon (HOL.weaken domain) (HOL.weaken before)))
      (member core (.var .vz) (product core epsilon (HOL.weaken domain) (HOL.weaken after)))) :=
    .impI (productAt core epsilon (HOL.weaken domain) (HOL.weaken before) (HOL.weaken after) (.var .vz)
      ((laws.weaken set).prepend _) ((weakenFamily core domain before after fibres).prepend _) (.hyp 0))
  apply ProofSyntax.castIndices rfl ?_ (.allI body)
  simp only [included,HOL.weaken,rename_product]

theorem valuesInclusion_free (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ) (fibres : ProofSyntax Const Δ (familyIncluded core domain before after))
    (lawsFree : laws.Free) (fibresFree : fibres.FunctionExtensionalityFree) :
    (valuesInclusion core epsilon domain before after laws fibres).FunctionExtensionalityFree :=
  unionInclusion_free core _ _ _ _ lawsFree.union
    (familyUnionInclusion_free core _ _ _ _ _ _ _ _ lawsFree.union lawsFree.pairing.replacement (reflexive_free core domain) fibresFree)

theorem supportFamilies_free (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (received : ProofSyntax Const Δ (included core (values core domain before) (values core domain after)))
    (free : received.FunctionExtensionalityFree) : (supportFamilies core domain before after received).FunctionExtensionalityFree := by
  unfold supportFamilies
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply transportEndpoints_free
  · exact supportBeta_free core _ _ _
  · exact supportBeta_free core _ _ _
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core _ _ received free)

theorem supportInclusion_free (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ) (fibres : ProofSyntax Const Δ (familyIncluded core domain before after))
    (lawsFree : laws.Free) (fibresFree : fibres.FunctionExtensionalityFree) :
    (supportInclusion core epsilon domain before after laws fibres).FunctionExtensionalityFree :=
  sumInclusion_free core epsilon _ _ _ _ laws _ _ lawsFree (reflexive_free core domain)
    (supportFamilies_free core _ _ _ _ (valuesInclusion_free core epsilon _ _ _ laws fibres lawsFree fibresFree))

theorem weakenGuard_free {added : Ty Unit} (domain : Term Const Γ set) (family : Term Const Γ mapping) (relation : Term Const Γ set)
    (proof : ProofSyntax Const Δ (guard core epsilon domain family relation)) (free : proof.FunctionExtensionalityFree) :
    (weakenGuard (added := added) core epsilon domain family relation proof).FunctionExtensionalityFree := by
  simpa [weakenGuard,PredicateFixedPoint.weakenProof] using free

theorem guardTransport_free (domain : Term Const Γ set) (before after : Term Const Γ mapping) (relation : Term Const Γ set)
    (fibres : ProofSyntax Const Δ (familyIncluded core domain before after))
    (received : ProofSyntax Const Δ (guard core epsilon domain before relation))
    (fibresFree : fibres.FunctionExtensionalityFree) (receivedFree : received.FunctionExtensionalityFree) :
    (guardTransport core epsilon domain before after relation fibres received).FunctionExtensionalityFree := by
  unfold guardTransport
  apply SetInclusionProofs.eliminate_free
  · apply familyAt_free
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenFamily_free core _ _ _ fibres fibresFree)
    · trivial
  · apply guardAt_free
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenGuard_free core epsilon _ _ _ received receivedFree)
    · trivial

theorem productAt_free (domain : Term Const Γ set) (before after : Term Const Γ mapping) (relation : Term Const Γ set)
    (laws : SetTraceProofs.Laws core epsilon Δ) (fibres : ProofSyntax Const Δ (familyIncluded core domain before after))
    (received : ProofSyntax Const Δ (member core relation (product core epsilon domain before)))
    (lawsFree : laws.Free) (fibresFree : fibres.FunctionExtensionalityFree) (receivedFree : received.FunctionExtensionalityFree) :
    (productAt core epsilon domain before after relation laws fibres received).FunctionExtensionalityFree :=
  introduce_free core epsilon domain after relation laws _ _ lawsFree
    (transitive_free core _ _ _ _ _ (productBound_free core epsilon _ _ _ laws received lawsFree receivedFree)
      (supportInclusion_free core epsilon _ _ _ laws fibres lawsFree fibresFree))
    (guardTransport_free core epsilon _ _ _ _ fibres _ fibresFree (productGuard_free core epsilon _ _ _ laws received lawsFree receivedFree))

theorem productInclusion_free (domain : Term Const Γ set) (before after : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ) (fibres : ProofSyntax Const Δ (familyIncluded core domain before after))
    (lawsFree : laws.Free) (fibresFree : fibres.FunctionExtensionalityFree) :
    (productInclusion core epsilon domain before after laws fibres).FunctionExtensionalityFree := by
  unfold productInclusion
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply productAt_free
  · exact (laws.weaken set).prepend_free _ (laws.weaken_free set lawsFree)
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenFamily_free core _ _ _ fibres fibresFree)
  · trivial

end Mettapedia.Logic.HOL.SetTraceProductInclusionProofs
