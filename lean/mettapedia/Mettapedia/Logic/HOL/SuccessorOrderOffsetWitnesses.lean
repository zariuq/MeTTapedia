import Mettapedia.Logic.HOL.SuccessorOrderPrefixSums

/-!
# Successor-offset witnesses from successor-closure order

A proof of lower < upper yields an explicit sum witness whose offset is a
successor. This is positive offset in the natural-number profile. The generic
construction uses the two least closure relations and requires no separate
induction, injectivity or separation premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
    (successor : ClosedTerm Const (number ⇒ number)) (zero : ClosedTerm Const number)
    {Δ : List (Formula Const Γ)}

def successorOffsetSum (first result : Term Const Γ number) : Formula Const Γ :=
  .ex (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first))
    (.app (weakenCtx _ successor) (.var .vz))) (weaken result))

@[simp] theorem successorOffsetSum_subst (images : Subst Const Γ Ξ) (first result : Term Const Γ number) :
    HOL.subst images (successorOffsetSum successor zero first result) =
      successorOffsetSum successor zero (HOL.subst images first) (HOL.subst images result) := by
  simp only [successorOffsetSum, HOL.subst, subst_weakenCtx, subst_weaken, Subst.lift]

@[simp] theorem successorOffsetSum_rename (rho : Rename Base Γ Ξ) (first result : Term Const Γ number) :
    HOL.rename rho (successorOffsetSum successor zero first result) =
      successorOffsetSum successor zero (HOL.rename rho first) (HOL.rename rho result) := by
  simpa only [subst_ofRename] using successorOffsetSum_subst successor zero (Subst.ofRename rho) first result

def successorOffsetProgram (first : Term Const Γ number) : Term Const Γ (number ⇒ .prop) :=
  .lam (successorOffsetSum successor zero (weaken first) (.var .vz))

@[simp] theorem successorOffsetProgram_rename (rho : Rename Base Γ Ξ) (first : Term Const Γ number) :
    HOL.rename rho (successorOffsetProgram successor zero first) =
      successorOffsetProgram successor zero (HOL.rename rho first) := by
  simp only [successorOffsetProgram, HOL.rename, successorOffsetSum_rename, ExtDerivation.rename_weaken, Rename.lift]

def successorOffsetProgram_beta (first result : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (.app (successorOffsetProgram successor zero first) result)
      (successorOffsetSum successor zero first result)) := by
  have cancel : HOL.subst (Subst.single result) (weaken first) = first := instantiate_weaken result first
  apply ProofSyntax.castIndices rfl ?_ (.beta result (successorOffsetSum successor zero (weaken first) (.var .vz)))
  simp only [successorOffsetProgram, instantiate, successorOffsetSum_subst, cancel, HOL.subst, Subst.single]

theorem successorOffsetProgram_beta_free (first result : Term Const Γ number) :
    (successorOffsetProgram_beta (Δ := Δ) successor zero first result).FunctionExtensionalityFree := by
  simp [successorOffsetProgram_beta, ProofSyntax.FunctionExtensionalityFree]

def successorOffsetIntro (first result offset : Term Const Γ number)
    (present : ProofSyntax Const Δ (.app (.app (.app (weakenCtx Γ (sum zero successor)) first)
      (.app (weakenCtx Γ successor) offset)) result)) :
    ProofSyntax Const Δ (successorOffsetSum successor zero first result) := by
  apply ProofSyntax.exI offset
  apply ProofSyntax.castIndices rfl ?_ present
  simp only [instantiate, HOL.subst, subst_weakenCtx, Subst.single, PredicateFixedPoint.subst_single_weaken]

theorem successorOffsetIntro_free (first result offset : Term Const Γ number)
    (present : ProofSyntax Const Δ (.app (.app (.app (weakenCtx Γ (sum zero successor)) first)
      (.app (weakenCtx Γ successor) offset)) result)) (free : present.FunctionExtensionalityFree) :
    (successorOffsetIntro successor zero first result offset present).FunctionExtensionalityFree := by
  unfold successorOffsetIntro
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

def successorOffsetStep (first result : Term Const Γ number)
    (present : ProofSyntax Const Δ (successorOffsetSum successor zero first result)) :
    ProofSyntax Const Δ (successorOffsetSum successor zero first (.app (weakenCtx Γ successor) result)) := by
  apply ProofSyntax.exE present
  let body : Formula Const (number :: Γ) :=
    .app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first))
      (.app (weakenCtx _ successor) (.var .vz))) (weaken result)
  have previous : ProofSyntax Const (body :: weakenHyps Δ) body := .hyp 0
  have next := sumStep successor zero (weaken first) (.app (weakenCtx _ successor) (.var .vz)) (weaken result) previous
  apply ProofSyntax.castIndices rfl ?_
    (successorOffsetIntro successor zero (weaken first) (.app (weakenCtx _ successor) (weaken result))
      (.app (weakenCtx _ successor) (.var .vz)) next)
  simp only [weaken, successorOffsetSum_rename, HOL.rename, rename_weakenCtx]

theorem successorOffsetStep_free (first result : Term Const Γ number)
    (present : ProofSyntax Const Δ (successorOffsetSum successor zero first result)) (free : present.FunctionExtensionalityFree) :
    (successorOffsetStep successor zero first result present).FunctionExtensionalityFree := by
  unfold successorOffsetStep
  refine ⟨free, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact successorOffsetIntro_free _ _ _ _ _ _ (sumStep_free _ _ _ _ _ _ True.intro)

def successorOffsetClosed (first : Term Const Γ number) :
    ProofSyntax Const Δ (successorClosed successor (successorOffsetProgram successor zero first)) := by
  refine .allI (.impI ?_)
  let premise := Term.app (weaken (successorOffsetProgram successor zero first)) (.var .vz)
  have supplied : ProofSyntax Const (premise :: weakenHyps Δ)
      (.app (successorOffsetProgram successor zero (weaken first)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := premise :: weakenHyps Δ) 0)
    change premise = _
    simp only [premise, weaken, successorOffsetProgram_rename]
  have previous := ProofSyntax.impE (.eqPropEL (successorOffsetProgram_beta successor zero (weaken first) (.var .vz))) supplied
  have next := successorOffsetStep successor zero (weaken first) (.var .vz) previous
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (successorOffsetProgram_beta successor zero (weaken first)
      (.app (weakenCtx _ successor) (.var .vz)))) next)
  simp only [weaken,successorOffsetProgram_rename]

theorem successorOffsetClosed_free (first : Term Const Γ number) :
    (successorOffsetClosed (Δ := Δ) successor zero first).FunctionExtensionalityFree := by
  unfold successorOffsetClosed
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨successorOffsetProgram_beta_free _ _ _ _, ?_⟩
  apply successorOffsetStep_free
  refine ⟨successorOffsetProgram_beta_free _ _ _ _, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def less_has_successorOffset (first result : Term Const Γ number)
    (present : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) first) result)) :
    ProofSyntax Const Δ (successorOffsetSum successor zero first result) :=
  .impE (.eqPropEL (successorOffsetProgram_beta successor zero first result))
    (lessEliminate successor first result (successorOffsetProgram successor zero first) present
      (.impE (.eqPropER (successorOffsetProgram_beta successor zero first (.app (weakenCtx Γ successor) first)))
        (successorOffsetIntro successor zero first (.app (weakenCtx Γ successor) first) (weakenCtx Γ zero)
          (sumStep successor zero first (weakenCtx Γ zero) first (sumZero successor zero first))))
      (successorOffsetClosed successor zero first))

theorem less_has_successorOffset_free (first result : Term Const Γ number)
    (present : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) first) result))
    (free : present.FunctionExtensionalityFree) :
    (less_has_successorOffset successor zero first result present).FunctionExtensionalityFree := by
  unfold less_has_successorOffset
  refine ⟨successorOffsetProgram_beta_free _ _ _ _, ?_⟩
  apply lessEliminate_free
  · exact free
  · exact ⟨successorOffsetProgram_beta_free _ _ _ _,successorOffsetIntro_free _ _ _ _ _ _
      (sumStep_free _ _ _ _ _ _ (sumZero_free _ _ _))⟩
  · exact successorOffsetClosed_free _ _ _

#print axioms less_has_successorOffset
#print axioms less_has_successorOffset_free
end Mettapedia.Logic.HOL.SuccessorOrder
