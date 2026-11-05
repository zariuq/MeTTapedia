import Mettapedia.Logic.HOL.SetUniverseProofs
import Mettapedia.Logic.HOL.SetTraceProductProofs

/-!
# Retained universe formation for constructed pairs, sums and products

The primitive closure proofs are specialized through the actual set
constructions. Pairing uses the existing decided-index replacement program;
dependent sums use indexed replacement and union; trace products use bounded
separation. No derived formation statement is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetUniverseFormationProofs
open SetComprehensionProofs SetMembershipProofs SetPairingProofs SetUniverseProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (mapping)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}

def indexClosed (universeSet anchor : Term Const Γ object)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (anchorMember : ProofSyntax Const Δ (member core anchor universeSet)) :
    ProofSyntax Const Δ (member core (index core) universeSet) :=
  separationClosed core universeSet _ _ closure sets.pairing.power sets.pairing.separation
    (unaryAt core universeSet (.const (core .power)) _ closure.power
      (unaryAt core universeSet (.const (core .power)) _ closure.power
        (emptyClosed core universeSet anchor closure sets.pairing.empty sets.pairing.power anchorMember)))

def unorderedClosed (universeSet left right : Term Const Γ object)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (leftMember : ProofSyntax Const Δ (member core left universeSet))
    (rightMember : ProofSyntax Const Δ (member core right universeSet)) :
    ProofSyntax Const Δ (member core (unordered core epsilon left right) universeSet) := by
  apply replacementAt core universeSet (index core) (send core epsilon left right) closure
    (indexClosed core epsilon universeSet left closure sets leftMember)
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let premise : Formula Const (object :: Γ) := member core (.var .vz) (index core)
  let localSets := ((sets.weaken object).prepend premise).pairing
  have leftRaised := (PredicateFixedPoint.weakenProof leftMember).prepend premise
  have rightRaised := (PredicateFixedPoint.weakenProof rightMember).prepend premise
  have decided := indexDecided core epsilon (.var .vz) localSets (.hyp 0)
  have choices := chooseSpec epsilon (condition core (.var .vz)) (HOL.weaken left) (HOL.weaken right)
    localSets.selection decided
  have chosen : ProofSyntax Const (premise :: weakenHyps (σ := object) Δ)
      (member core (choose epsilon (condition core (.var .vz)) (HOL.weaken left) (HOL.weaken right))
        (HOL.weaken universeSet)) :=
    .orE choices
      (transportValue core _ (.eqSymm (.andER (.hyp 0))) (leftRaised.prepend _))
      (transportValue core _ (.eqSymm (.andER (.hyp 0))) (rightRaised.prepend _))
  have retained := transportValue core (HOL.weaken universeSet)
    (.eqSymm (sendBeta core epsilon (HOL.weaken left) (HOL.weaken right) (.var .vz))) chosen
  apply ProofSyntax.castIndices rfl ?_ retained
  simp only [weaken_send]

def orderedClosed (universeSet left right : Term Const Γ object)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (leftMember : ProofSyntax Const Δ (member core left universeSet))
    (rightMember : ProofSyntax Const Δ (member core right universeSet)) :
    ProofSyntax Const Δ (member core (ordered core epsilon left right) universeSet) :=
  unorderedClosed core epsilon universeSet _ _ closure sets
    (unorderedClosed core epsilon universeSet left left closure sets leftMember leftMember)
    (unorderedClosed core epsilon universeSet left right closure sets leftMember rightMember)

def familyUnionClosed (universeSet domain : Term Const Γ object) (family : Term Const Γ mapping)
    (closure : SetUniverseProofs.Laws core universeSet Δ)
    (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (familyMembers : ProofSyntax Const Δ (mapsInto core universeSet domain family)) :
    ProofSyntax Const Δ (member core (familyUnion core domain family) universeSet) :=
  unaryAt core universeSet (.const (core .union)) _ closure.union
    (replacementAt core universeSet domain family closure domainMember familyMembers)

def pairImageClosed (universeSet point fibre : Term Const Γ object)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (pointMember : ProofSyntax Const Δ (member core point universeSet))
    (fibreMember : ProofSyntax Const Δ (member core fibre universeSet)) :
    ProofSyntax Const Δ (member core (SetDependentSumProofs.pairImage core epsilon point fibre) universeSet) := by
  apply replacementAt core universeSet fibre (SetDependentSumProofs.fibreMap core epsilon point) closure fibreMember
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let premise := member core (.var .vz) (HOL.weaken fibre)
  let localClosure := (closure.weaken object).prepend premise
  let localSets := (sets.weaken object).prepend premise
  have pointRaised := (PredicateFixedPoint.weakenProof pointMember).prepend premise
  have fibreRaised := (PredicateFixedPoint.weakenProof fibreMember).prepend premise
  have elementMember := transitiveAt core (HOL.weaken universeSet) (HOL.weaken fibre) (.var .vz)
    localClosure fibreRaised (.hyp 0)
  have pairMember := orderedClosed core epsilon (HOL.weaken universeSet) (HOL.weaken point) (.var .vz)
    localClosure localSets pointRaised elementMember
  have retained := transportValue core (HOL.weaken universeSet)
    (.eqSymm (SetDependentSumProofs.fibreBeta core epsilon (HOL.weaken point) (.var .vz))) pairMember
  apply ProofSyntax.castIndices rfl ?_ retained
  simp only [HOL.weaken,SetDependentSumProofs.rename_fibreMap,member]

def sumClosed (universeSet domain : Term Const Γ object) (family : Term Const Γ mapping)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (familyMembers : ProofSyntax Const Δ (mapsInto core universeSet domain family)) :
    ProofSyntax Const Δ (member core (SetDependentSumProofs.sum core epsilon domain family) universeSet) := by
  apply familyUnionClosed core universeSet domain (SetDependentSumProofs.familyMap core epsilon family) closure domainMember
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let premise := member core (.var .vz) (HOL.weaken domain)
  let localClosure := (closure.weaken object).prepend premise
  let localSets := (sets.weaken object).prepend premise
  have domainRaised := (PredicateFixedPoint.weakenProof domainMember).prepend premise
  have familyRaised := (weakenMapsInto core universeSet domain family familyMembers).prepend premise
  have pointMember := transitiveAt core (HOL.weaken universeSet) (HOL.weaken domain) (.var .vz)
    localClosure domainRaised (.hyp 0)
  have fibreMember := mapsIntoAt core (HOL.weaken universeSet) (HOL.weaken domain) (HOL.weaken family)
    (.var .vz) familyRaised (.hyp 0)
  have imageMember := pairImageClosed core epsilon (HOL.weaken universeSet) (.var .vz)
    (.app (HOL.weaken family) (.var .vz)) localClosure localSets pointMember fibreMember
  have retained := transportValue core (HOL.weaken universeSet)
    (.eqSymm (SetDependentSumProofs.familyBeta core epsilon (HOL.weaken family) (.var .vz))) imageMember
  apply ProofSyntax.castIndices rfl ?_ retained
  simp only [HOL.weaken,SetDependentSumProofs.rename_familyMap,member]

private theorem weakenSupportFamily (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.weaken (σ := object) (SetTraceProductProofs.supportFamily core domain family) =
      SetTraceProductProofs.supportFamily core (HOL.weaken domain) (HOL.weaken family) := by
  simpa only [HOL.subst_ofRename,HOL.weaken] using
    SetTraceProductProofs.subst_supportFamily core (Subst.ofRename (Rename.weaken (σ := object))) domain family

def supportClosed (universeSet domain : Term Const Γ object) (family : Term Const Γ mapping)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (familyMembers : ProofSyntax Const Δ (mapsInto core universeSet domain family)) :
    ProofSyntax Const Δ (member core (SetTraceProductProofs.support core epsilon domain family) universeSet) := by
  have valuesMember := unaryAt core universeSet (.const (core .union)) _ closure.union
    (familyUnionClosed core universeSet domain family closure domainMember familyMembers)
  apply sumClosed core epsilon universeSet domain (SetTraceProductProofs.supportFamily core domain family) closure sets domainMember
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let premise : Formula Const (object :: Γ) := member core (.var .vz) (HOL.weaken domain)
  have retained : ProofSyntax Const (premise :: weakenHyps (σ := object) Δ)
      (member core (.app (SetTraceProductProofs.supportFamily core (HOL.weaken domain) (HOL.weaken family)) (.var .vz))
        (HOL.weaken universeSet)) := transportValue core (HOL.weaken universeSet)
    (.eqSymm (SetTraceProductProofs.supportBeta core (HOL.weaken domain) (HOL.weaken family) (.var .vz)))
    ((PredicateFixedPoint.weakenProof valuesMember).prepend premise)
  apply ProofSyntax.castIndices rfl ?_ retained
  simp only [weakenSupportFamily,member]

def productClosed (universeSet domain : Term Const Γ object) (family : Term Const Γ mapping)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (familyMembers : ProofSyntax Const Δ (mapsInto core universeSet domain family)) :
    ProofSyntax Const Δ (member core (SetTraceProductProofs.product core epsilon domain family) universeSet) :=
  separationClosed core universeSet _ _ closure sets.pairing.power sets.pairing.separation
    (unaryAt core universeSet (.const (core .power)) _ closure.power
      (supportClosed core epsilon universeSet domain family closure sets domainMember familyMembers))

private theorem raised_free {conclusion : Formula Const Γ} (proof : ProofSyntax Const Δ conclusion)
    (premise : Formula Const (object :: Γ)) (free : proof.FunctionExtensionalityFree) :
    ((PredicateFixedPoint.weakenProof (σ := object) proof).prepend premise).FunctionExtensionalityFree := by
  simpa [ProofSyntax.prepend,PredicateFixedPoint.weakenProof] using free

theorem indexClosed_free (universeSet anchor : Term Const Γ object)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (anchorMember : ProofSyntax Const Δ (member core anchor universeSet))
    (closureFree : closure.Free) (setsFree : sets.Free) (anchorFree : anchorMember.FunctionExtensionalityFree) :
    (indexClosed core epsilon universeSet anchor closure sets anchorMember).FunctionExtensionalityFree :=
  separationClosed_free core universeSet _ _ closure _ _ _ closureFree setsFree.pairing.power setsFree.pairing.separation
    (unaryAt_free core universeSet _ _ _ _ closureFree.power
      (unaryAt_free core universeSet _ _ _ _ closureFree.power
        (emptyClosed_free core universeSet anchor closure _ _ anchorMember closureFree
          setsFree.pairing.empty setsFree.pairing.power anchorFree)))

theorem unorderedClosed_free (universeSet left right : Term Const Γ object)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (leftMember : ProofSyntax Const Δ (member core left universeSet))
    (rightMember : ProofSyntax Const Δ (member core right universeSet))
    (closureFree : closure.Free) (setsFree : sets.Free)
    (leftFree : leftMember.FunctionExtensionalityFree) (rightFree : rightMember.FunctionExtensionalityFree) :
    (unorderedClosed core epsilon universeSet left right closure sets leftMember rightMember).FunctionExtensionalityFree := by
  unfold unorderedClosed
  apply replacementAt_free
  · exact closureFree
  · exact indexClosed_free core epsilon universeSet left closure sets leftMember closureFree setsFree leftFree
  · simp only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
    apply transportValue_free
    · exact sendBeta_free core epsilon _ _ _
    · refine ⟨?_,?_,?_⟩
      · apply chooseSpec_free
        · exact ((sets.weaken object).prepend_free _ (sets.weaken_free object setsFree)).pairing.selection
        · exact indexDecided_free core epsilon _ _ _
            ((sets.weaken object).prepend_free _ (sets.weaken_free object setsFree)).pairing trivial
      · apply transportValue_free
        · trivial
        · simpa [ProofSyntax.prepend] using
            raised_free leftMember (member core (.var .vz) (index core)) leftFree
      · apply transportValue_free
        · trivial
        · simpa [ProofSyntax.prepend] using
            raised_free rightMember (member core (.var .vz) (index core)) rightFree

theorem orderedClosed_free (universeSet left right : Term Const Γ object)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (leftMember : ProofSyntax Const Δ (member core left universeSet))
    (rightMember : ProofSyntax Const Δ (member core right universeSet))
    (closureFree : closure.Free) (setsFree : sets.Free)
    (leftFree : leftMember.FunctionExtensionalityFree) (rightFree : rightMember.FunctionExtensionalityFree) :
    (orderedClosed core epsilon universeSet left right closure sets leftMember rightMember).FunctionExtensionalityFree :=
  unorderedClosed_free core epsilon universeSet _ _ closure sets _ _ closureFree setsFree
    (unorderedClosed_free core epsilon universeSet left left closure sets leftMember leftMember closureFree setsFree leftFree leftFree)
    (unorderedClosed_free core epsilon universeSet left right closure sets leftMember rightMember closureFree setsFree leftFree rightFree)

theorem familyUnionClosed_free (universeSet domain : Term Const Γ object) (family : Term Const Γ mapping)
    (closure : SetUniverseProofs.Laws core universeSet Δ)
    (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (familyMembers : ProofSyntax Const Δ (mapsInto core universeSet domain family))
    (closureFree : closure.Free) (domainFree : domainMember.FunctionExtensionalityFree)
    (familyFree : familyMembers.FunctionExtensionalityFree) :
    (familyUnionClosed core universeSet domain family closure domainMember familyMembers).FunctionExtensionalityFree :=
  unaryAt_free core universeSet _ _ _ _ closureFree.union
    (replacementAt_free core universeSet domain family closure domainMember familyMembers closureFree domainFree familyFree)

theorem pairImageClosed_free (universeSet point fibre : Term Const Γ object)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (pointMember : ProofSyntax Const Δ (member core point universeSet))
    (fibreMember : ProofSyntax Const Δ (member core fibre universeSet))
    (closureFree : closure.Free) (setsFree : sets.Free)
    (pointFree : pointMember.FunctionExtensionalityFree) (fibreFree : fibreMember.FunctionExtensionalityFree) :
    (pairImageClosed core epsilon universeSet point fibre closure sets pointMember fibreMember).FunctionExtensionalityFree := by
  unfold pairImageClosed
  apply replacementAt_free
  · exact closureFree
  · exact fibreFree
  · simp only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
    apply transportValue_free
    · exact SetDependentSumProofs.fibreBeta_free core epsilon _ _
    · apply orderedClosed_free
      · exact (closure.weaken object).prepend_free _ (closure.weaken_free object closureFree)
      · exact (sets.weaken object).prepend_free _ (sets.weaken_free object setsFree)
      · exact raised_free pointMember _ pointFree
      · apply transitiveAt_free
        · exact (closure.weaken object).prepend_free _ (closure.weaken_free object closureFree)
        · exact raised_free fibreMember _ fibreFree
        · trivial

theorem sumClosed_free (universeSet domain : Term Const Γ object) (family : Term Const Γ mapping)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (familyMembers : ProofSyntax Const Δ (mapsInto core universeSet domain family))
    (closureFree : closure.Free) (setsFree : sets.Free)
    (domainFree : domainMember.FunctionExtensionalityFree) (familyFree : familyMembers.FunctionExtensionalityFree) :
    (sumClosed core epsilon universeSet domain family closure sets domainMember familyMembers).FunctionExtensionalityFree := by
  unfold sumClosed
  apply familyUnionClosed_free
  · exact closureFree
  · exact domainFree
  · simp only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
    apply transportValue_free
    · exact SetDependentSumProofs.familyBeta_free core epsilon _ _
    · apply pairImageClosed_free
      · exact (closure.weaken object).prepend_free _ (closure.weaken_free object closureFree)
      · exact (sets.weaken object).prepend_free _ (sets.weaken_free object setsFree)
      · apply transitiveAt_free
        · exact (closure.weaken object).prepend_free _ (closure.weaken_free object closureFree)
        · exact raised_free domainMember _ domainFree
        · trivial
      · apply mapsIntoAt_free
        · simpa [ProofSyntax.prepend] using weakenMapsInto_free core universeSet domain family familyMembers familyFree
        · trivial

theorem supportClosed_free (universeSet domain : Term Const Γ object) (family : Term Const Γ mapping)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (familyMembers : ProofSyntax Const Δ (mapsInto core universeSet domain family))
    (closureFree : closure.Free) (setsFree : sets.Free)
    (domainFree : domainMember.FunctionExtensionalityFree) (familyFree : familyMembers.FunctionExtensionalityFree) :
    (supportClosed core epsilon universeSet domain family closure sets domainMember familyMembers).FunctionExtensionalityFree := by
  have valuesFree := unaryAt_free core universeSet (.const (core .union)) _ closure.union _ closureFree.union
    (familyUnionClosed_free core universeSet domain family closure domainMember familyMembers closureFree domainFree familyFree)
  unfold supportClosed
  apply sumClosed_free
  · exact closureFree
  · exact setsFree
  · exact domainFree
  · simp only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
    apply transportValue_free
    · exact SetTraceProductProofs.supportBeta_free core _ _ _
    · exact raised_free _ _ valuesFree

theorem productClosed_free (universeSet domain : Term Const Γ object) (family : Term Const Γ mapping)
    (closure : SetUniverseProofs.Laws core universeSet Δ) (sets : SetTraceProofs.Laws core epsilon Δ)
    (domainMember : ProofSyntax Const Δ (member core domain universeSet))
    (familyMembers : ProofSyntax Const Δ (mapsInto core universeSet domain family))
    (closureFree : closure.Free) (setsFree : sets.Free)
    (domainFree : domainMember.FunctionExtensionalityFree) (familyFree : familyMembers.FunctionExtensionalityFree) :
    (productClosed core epsilon universeSet domain family closure sets domainMember familyMembers).FunctionExtensionalityFree :=
  separationClosed_free core universeSet _ _ closure _ _ _ closureFree setsFree.pairing.power setsFree.pairing.separation
    (unaryAt_free core universeSet _ _ _ _ closureFree.power
      (supportClosed_free core epsilon universeSet domain family closure sets domainMember familyMembers
        closureFree setsFree domainFree familyFree))

end Mettapedia.Logic.HOL.SetUniverseFormationProofs
