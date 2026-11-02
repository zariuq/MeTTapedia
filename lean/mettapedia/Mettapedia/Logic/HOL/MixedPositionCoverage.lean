import Mettapedia.Logic.HOL.SuccessorOrderCoverage
import Mettapedia.Logic.HOL.SuccessorOrderOffsetWitnesses

/-!
# Inactive positions outside a leading/vector/trailing prefix

Three checked region introductions suffice to turn an inactive-position proof
into a concrete suffix address. Natural induction and zero/successor separation
remain explicit. The resulting existential keeps the absolute-position equality
and the successor-offset sum together. Source compilers must construct the
region-introduction proofs; they are not replaced by a padding assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
    (successor : ClosedTerm Const (number ⇒ number)) (zero : ClosedTerm Const number)
    {Δ : List (Formula Const Γ)}

def interiorCoverage (active : Term Const Γ (number ⇒ .prop)) (length : Term Const Γ number) : Formula Const Γ :=
  .all (.imp (.app (.app (weakenCtx _ (less successor)) (.var .vz)) (weaken length))
    (.app (weaken active) (.app (weakenCtx _ successor) (.var .vz))))

@[simp] theorem interiorCoverage_subst (images : Subst Const Γ Ξ)
    (active : Term Const Γ (number ⇒ .prop)) (length : Term Const Γ number) :
    HOL.subst images (interiorCoverage successor active length) =
      interiorCoverage successor (HOL.subst images active) (HOL.subst images length) := by
  simp only [interiorCoverage, HOL.subst, subst_weakenCtx, subst_weaken, Subst.lift]

@[simp] theorem interiorCoverage_rename (rho : Rename Base Γ Ξ)
    (active : Term Const Γ (number ⇒ .prop)) (length : Term Const Γ number) :
    HOL.rename rho (interiorCoverage successor active length) =
      interiorCoverage successor (HOL.rename rho active) (HOL.rename rho length) := by
  simpa only [subst_ofRename] using interiorCoverage_subst successor (Subst.ofRename rho) active length

structure MixedCoverage (active : Term Const Γ (number ⇒ .prop)) (length : Term Const Γ number)
    (assumptions : List (Formula Const Γ)) where
  first : ProofSyntax Const assumptions (.app active (weakenCtx Γ zero))
  interior : ProofSyntax Const assumptions (interiorCoverage successor active length)
  last : ProofSyntax Const assumptions (.app active (.app (weakenCtx Γ successor) length))

namespace MixedCoverage
variable {successor zero} {active : Term Const Γ (number ⇒ .prop)} {length : Term Const Γ number}

def rename (coverage : MixedCoverage successor zero active length Δ) (rho : Rename Base Γ Ξ) :
    MixedCoverage successor zero (HOL.rename rho active) (HOL.rename rho length) (Δ.map (HOL.rename rho)) where
  first := ProofSyntax.castIndices rfl (by simp only [HOL.rename, rename_weakenCtx]) (coverage.first.rename rho)
  interior := ProofSyntax.castIndices rfl (interiorCoverage_rename successor rho active length) (coverage.interior.rename rho)
  last := ProofSyntax.castIndices rfl (by simp only [HOL.rename, rename_weakenCtx]) (coverage.last.rename rho)

def prepend (coverage : MixedCoverage successor zero active length Δ) (formula : Formula Const Γ) :
    MixedCoverage successor zero active length (formula :: Δ) where
  first := coverage.first.prepend formula
  interior := coverage.interior.prepend formula
  last := coverage.last.prepend formula

def Free (coverage : MixedCoverage successor zero active length Δ) : Prop :=
  coverage.first.FunctionExtensionalityFree ∧ coverage.interior.FunctionExtensionalityFree ∧ coverage.last.FunctionExtensionalityFree

theorem rename_free (coverage : MixedCoverage successor zero active length Δ) (rho : Rename Base Γ Ξ)
    (free : coverage.Free) : (coverage.rename rho).Free := by
  simpa only [Free,rename,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.functionExtensionalityFree_rename] using free

theorem prepend_free (coverage : MixedCoverage successor zero active length Δ) (formula : Formula Const Γ)
    (free : coverage.Free) : (coverage.prepend formula).Free := by
  simpa only [Free,prepend,ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using free
end MixedCoverage

def interiorAt (active : Term Const Γ (number ⇒ .prop)) (length position : Term Const Γ number)
    (given : ProofSyntax Const Δ (interiorCoverage successor active length)) :
    ProofSyntax Const Δ (.imp (.app (.app (weakenCtx Γ (less successor)) position) length)
      (.app active (.app (weakenCtx Γ successor) position))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE position given)
  simp only [instantiate,HOL.subst,subst_weakenCtx,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem interiorAt_free (active : Term Const Γ (number ⇒ .prop)) (length position : Term Const Γ number)
    (given : ProofSyntax Const Δ (interiorCoverage successor active length)) (free : given.FunctionExtensionalityFree) :
    (interiorAt successor active length position given).FunctionExtensionalityFree := by
  simpa only [interiorAt,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree] using free

def inactiveAtEqual (active : Term Const Γ (number ⇒ .prop)) (first second : Term Const Γ number)
    (equal : ProofSyntax Const Δ (.eq first second)) (inactive : ProofSyntax Const Δ (.not (.app active first))) :
    ProofSyntax Const Δ (.not (.app active second)) :=
  .notI (.notE (inactive.prepend _) (.impE (.eqPropER (.eqAppArg active (equal.prepend _))) (.hyp 0)))

theorem inactiveAtEqual_free (active : Term Const Γ (number ⇒ .prop)) (first second : Term Const Γ number)
    (equal : ProofSyntax Const Δ (.eq first second)) (inactive : ProofSyntax Const Δ (.not (.app active first)))
    (equalFree : equal.FunctionExtensionalityFree) (inactiveFree : inactive.FunctionExtensionalityFree) :
    (inactiveAtEqual active first second equal inactive).FunctionExtensionalityFree := by
  simp only [inactiveAtEqual,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.prepend,
    ProofSyntax.functionExtensionalityFree_mono,equalFree,inactiveFree,and_self]

def inactivePastZero (active : Term Const Γ (number ⇒ .prop)) (length slot : Term Const Γ number)
    (coverage : MixedCoverage successor zero active length Δ)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (inactive : ProofSyntax Const Δ (.not (.app active slot))) :
    ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) (weakenCtx Γ zero)) slot) :=
  comparisonOtherwise successor zero (weakenCtx Γ zero) slot principle
    (.notI (.notE (inactive.prepend _) (.impE (.eqPropEL (.eqAppArg active (.hyp 0))) (coverage.first.prepend _))))
    (.notI (lessZeroRefute successor zero slot (separate.prepend _) (.hyp 0)))

theorem inactivePastZero_free (active : Term Const Γ (number ⇒ .prop)) (length slot : Term Const Γ number)
    (coverage : MixedCoverage successor zero active length Δ)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (inactive : ProofSyntax Const Δ (.not (.app active slot))) (coverageFree : coverage.Free)
    (principleFree : principle.FunctionExtensionalityFree) (separateFree : separate.FunctionExtensionalityFree)
    (inactiveFree : inactive.FunctionExtensionalityFree) :
    (inactivePastZero successor zero active length slot coverage principle separate inactive).FunctionExtensionalityFree := by
  unfold inactivePastZero
  apply comparisonOtherwise_free
  · exact principleFree
  · simp only [ProofSyntax.FunctionExtensionalityFree,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,inactiveFree,coverageFree.1,and_self]
  · apply lessZeroRefute_free
    · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using separateFree
    · trivial

def inactivePastLength (active : Term Const Γ (number ⇒ .prop)) (length position : Term Const Γ number)
    (coverage : MixedCoverage successor zero active length Δ)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (inactive : ProofSyntax Const Δ (.not (.app active (.app (weakenCtx Γ successor) position)))) :
    ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) length) position) :=
  comparisonOtherwise successor zero length position principle
    (.notI (.notE (inactive.prepend _)
      (.impE (.eqPropEL (.eqAppArg active (.eqAppArg (weakenCtx Γ successor) (.hyp 0)))) (coverage.last.prepend _))))
    (.notI (.notE (inactive.prepend _)
      (.impE (interiorAt successor active length position (coverage.interior.prepend _)) (.hyp 0))))

theorem inactivePastLength_free (active : Term Const Γ (number ⇒ .prop)) (length position : Term Const Γ number)
    (coverage : MixedCoverage successor zero active length Δ)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (inactive : ProofSyntax Const Δ (.not (.app active (.app (weakenCtx Γ successor) position))))
    (coverageFree : coverage.Free) (principleFree : principle.FunctionExtensionalityFree)
    (inactiveFree : inactive.FunctionExtensionalityFree) :
    (inactivePastLength successor zero active length position coverage principle inactive).FunctionExtensionalityFree := by
  unfold inactivePastLength
  apply comparisonOtherwise_free
  · exact principleFree
  · simp only [ProofSyntax.FunctionExtensionalityFree,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,inactiveFree,coverageFree.2.2,and_self]
  · refine ⟨?_,?_,True.intro⟩
    · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using inactiveFree
    · apply interiorAt_free
      simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using coverageFree.2.1

def paddingAddress (length slot : Term Const Γ number) : Formula Const Γ :=
  .ex (.and (.eq (weaken slot) (.app (weakenCtx _ successor) (.var .vz)))
    (successorOffsetSum successor zero (weaken length) (.var .vz)))

@[simp] theorem paddingAddress_subst (images : Subst Const Γ Ξ) (length slot : Term Const Γ number) :
    HOL.subst images (paddingAddress successor zero length slot) =
      paddingAddress successor zero (HOL.subst images length) (HOL.subst images slot) := by
  simp only [paddingAddress,HOL.subst,successorOffsetSum_subst,subst_weaken,subst_weakenCtx,Subst.lift]

@[simp] theorem paddingAddress_rename (rho : Rename Base Γ Ξ) (length slot : Term Const Γ number) :
    HOL.rename rho (paddingAddress successor zero length slot) =
      paddingAddress successor zero (HOL.rename rho length) (HOL.rename rho slot) := by
  simpa only [subst_ofRename] using paddingAddress_subst successor zero (Subst.ofRename rho) length slot

def paddingAddressIntro (length slot predecessor : Term Const Γ number)
    (position : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ successor) predecessor)))
    (offset : ProofSyntax Const Δ (successorOffsetSum successor zero length predecessor)) :
    ProofSyntax Const Δ (paddingAddress successor zero length slot) := by
  apply ProofSyntax.exI predecessor
  apply ProofSyntax.castIndices rfl ?_ (.andI position offset)
  simp only [instantiate,HOL.subst,successorOffsetSum_subst,subst_weakenCtx,Subst.single,
    PredicateFixedPoint.subst_single_weaken]

theorem paddingAddressIntro_free (length slot predecessor : Term Const Γ number)
    (position : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ successor) predecessor)))
    (offset : ProofSyntax Const Δ (successorOffsetSum successor zero length predecessor))
    (positionFree : position.FunctionExtensionalityFree) (offsetFree : offset.FunctionExtensionalityFree) :
    (paddingAddressIntro successor zero length slot predecessor position offset).FunctionExtensionalityFree := by
  unfold paddingAddressIntro
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨positionFree,offsetFree⟩

def inactiveAddress (active : Term Const Γ (number ⇒ .prop)) (length slot : Term Const Γ number)
    (coverage : MixedCoverage successor zero active length Δ)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (inactive : ProofSyntax Const Δ (.not (.app active slot))) :
    ProofSyntax Const Δ (paddingAddress successor zero length slot) := by
  have positive := inactivePastZero successor zero active length slot coverage principle separate inactive
  have address := less_has_successorOffset successor zero (weakenCtx Γ zero) slot positive
  apply ProofSyntax.exE address
  let body : Formula Const (number :: Γ) :=
    .app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (weakenCtx Γ zero)))
      (.app (weakenCtx _ successor) (.var .vz))) (weaken slot)
  let assumptions := body :: weakenHyps Δ
  have supplied : ProofSyntax Const assumptions body := .hyp 0
  have currentSum : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weakenCtx _ zero))
        (.app (weakenCtx _ successor) (.var .vz))) (weaken slot)) := by
    apply ProofSyntax.castIndices rfl ?_ supplied
    simp only [body,weaken,rename_weakenCtx]
  have position : ProofSyntax Const assumptions (.eq (weaken slot) (.app (weakenCtx _ successor) (.var .vz))) :=
    .eqSymm (sumZeroReflect successor zero (.app (weakenCtx _ successor) (.var .vz)) (weaken slot) currentSum)
  have old : ProofSyntax Const assumptions (.not (.app (weaken active) (weaken slot))) :=
    (inactive.rename Rename.weaken).prepend body
  have currentInactive := inactiveAtEqual (weaken active) (weaken slot) (.app (weakenCtx _ successor) (.var .vz)) position old
  have past := inactivePastLength successor zero (weaken active) (weaken length) (.var .vz)
    ((coverage.rename Rename.weaken).prepend body)
    ((inductionRename successor zero principle Rename.weaken).prepend body) currentInactive
  have offset := less_has_successorOffset successor zero (weaken length) (.var .vz) past
  apply ProofSyntax.castIndices rfl ?_
    (paddingAddressIntro successor zero (weaken length) (weaken slot) (.var .vz) position offset)
  simp only [weaken,paddingAddress_rename]

theorem inactiveAddress_free (active : Term Const Γ (number ⇒ .prop)) (length slot : Term Const Γ number)
    (coverage : MixedCoverage successor zero active length Δ)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (inactive : ProofSyntax Const Δ (.not (.app active slot))) (coverageFree : coverage.Free)
    (principleFree : principle.FunctionExtensionalityFree) (separateFree : separate.FunctionExtensionalityFree)
    (inactiveFree : inactive.FunctionExtensionalityFree) :
    (inactiveAddress successor zero active length slot coverage principle separate inactive).FunctionExtensionalityFree := by
  unfold inactiveAddress
  refine ⟨less_has_successorOffset_free _ _ _ _ _
    (inactivePastZero_free _ _ _ _ _ coverage principle separate inactive coverageFree principleFree separateFree inactiveFree), ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply paddingAddressIntro_free
  · apply sumZeroReflect_free
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · apply less_has_successorOffset_free
    apply inactivePastLength_free
    · exact (coverage.rename Rename.weaken).prepend_free _ (coverage.rename_free Rename.weaken coverageFree)
    · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using
        inductionRename_free successor zero principle Rename.weaken principleFree
    · apply inactiveAtEqual_free
      · apply sumZeroReflect_free
        apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial
      · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,
          ProofSyntax.functionExtensionalityFree_rename] using inactiveFree

#print axioms inactivePastLength_free
#print axioms paddingAddressIntro_free
#print axioms inactiveAddress_free
end Mettapedia.Logic.HOL.SuccessorOrder
