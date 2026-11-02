import Mettapedia.Logic.HOL.SuccessorOrderPositionBounds

/-!
# Comparison coverage for the successor-closure relation

The covering disjunction distinguishes less, equality and reverse less.
Natural induction is explicit. Coverage does not assert that the branches
are disjoint: injectivity and zero/successor separation are separate laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
    (successor : ClosedTerm Const (number ⇒ number)) (zero : ClosedTerm Const number)
    {Δ : List (Formula Const Γ)}

def comparisonCases (first second : Term Const Γ number) : Formula Const Γ :=
  .or (.app (.app (weakenCtx Γ (less successor)) first) second)
    (.or (.eq first second) (.app (.app (weakenCtx Γ (less successor)) second) first))

@[simp] theorem comparisonCases_subst (images : Subst Const Γ Ξ) (first second : Term Const Γ number) :
    HOL.subst images (comparisonCases successor first second) =
      comparisonCases successor (HOL.subst images first) (HOL.subst images second) := by
  simp only [comparisonCases, HOL.subst, subst_weakenCtx]

@[simp] theorem comparisonCases_rename (rho : Rename Base Γ Ξ) (first second : Term Const Γ number) :
    HOL.rename rho (comparisonCases successor first second) =
      comparisonCases successor (HOL.rename rho first) (HOL.rename rho second) := by
  simpa only [subst_ofRename] using comparisonCases_subst successor (Subst.ofRename rho) first second

def comparisonRight (first : Term Const Γ number) : Term Const Γ (number ⇒ .prop) :=
  .lam (comparisonCases successor (weaken first) (.var .vz))

@[simp] theorem comparisonRight_subst (images : Subst Const Γ Ξ) (first : Term Const Γ number) :
    HOL.subst images (comparisonRight successor first) = comparisonRight successor (HOL.subst images first) := by
  simp only [comparisonRight, HOL.subst, comparisonCases_subst, subst_weaken, Subst.lift]

@[simp] theorem comparisonRight_rename (rho : Rename Base Γ Ξ) (first : Term Const Γ number) :
    HOL.rename rho (comparisonRight successor first) = comparisonRight successor (HOL.rename rho first) := by
  simpa only [subst_ofRename] using comparisonRight_subst successor (Subst.ofRename rho) first

def comparisonAll (first : Term Const Γ number) : Formula Const Γ :=
  .all (comparisonCases successor (weaken first) (.var .vz))

@[simp] theorem comparisonAll_subst (images : Subst Const Γ Ξ) (first : Term Const Γ number) :
    HOL.subst images (comparisonAll successor first) = comparisonAll successor (HOL.subst images first) := by
  simp only [comparisonAll, HOL.subst, comparisonCases_subst, subst_weaken, Subst.lift]

@[simp] theorem comparisonAll_rename (rho : Rename Base Γ Ξ) (first : Term Const Γ number) :
    HOL.rename rho (comparisonAll successor first) = comparisonAll successor (HOL.rename rho first) := by
  simpa only [subst_ofRename] using comparisonAll_subst successor (Subst.ofRename rho) first

def comparisonMotive : Term Const Γ (number ⇒ .prop) := .lam (comparisonAll successor (.var .vz))

@[simp] theorem comparisonMotive_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (comparisonMotive (Γ := Γ) successor) = comparisonMotive (Γ := Ξ) successor := by
  simp only [comparisonMotive, HOL.rename, comparisonAll_rename, Rename.lift]

def comparisonRight_beta (first second : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (.app (comparisonRight successor first) second) (comparisonCases successor first second)) := by
  have cancel : HOL.subst (Subst.single second) (weaken first) = first := instantiate_weaken second first
  apply ProofSyntax.castIndices rfl ?_ (.beta second (comparisonCases successor (weaken first) (.var .vz)))
  simp only [comparisonRight, instantiate, comparisonCases_subst, cancel, HOL.subst, Subst.single]

theorem comparisonRight_beta_free (first second : Term Const Γ number) :
    (comparisonRight_beta (Δ := Δ) successor first second).FunctionExtensionalityFree := by
  simp [comparisonRight_beta, ProofSyntax.FunctionExtensionalityFree]

def comparisonMotive_beta (first : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (.app (comparisonMotive successor) first) (comparisonAll successor first)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta first (comparisonAll successor (.var .vz)))
  simp only [comparisonMotive, instantiate, comparisonAll_subst, HOL.subst, Subst.single]

theorem comparisonMotive_beta_free (first : Term Const Γ number) :
    (comparisonMotive_beta (Δ := Δ) successor first).FunctionExtensionalityFree := by
  simp [comparisonMotive_beta, ProofSyntax.FunctionExtensionalityFree]

def comparisonAt (first second : Term Const Γ number) (given : ProofSyntax Const Δ (comparisonAll successor first)) :
    ProofSyntax Const Δ (comparisonCases successor first second) := by
  have cancel : HOL.subst (Subst.single second) (weaken first) = first := instantiate_weaken second first
  apply ProofSyntax.castIndices rfl ?_ (.allE second given)
  simp only [instantiate, comparisonCases_subst, cancel, HOL.subst, Subst.single]

theorem comparisonAt_free (first second : Term Const Γ number) (given : ProofSyntax Const Δ (comparisonAll successor first))
    (free : given.FunctionExtensionalityFree) : (comparisonAt successor first second given).FunctionExtensionalityFree := by
  simpa only [comparisonAt, ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.FunctionExtensionalityFree] using free

def inductionRename (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) (rho : Rename Base Γ Ξ) :
    ProofSyntax Const (Δ.map (HOL.rename rho))
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Ξ zero) (weakenCtx Ξ successor)) :=
  ProofSyntax.castIndices rfl
    (by simpa only [subst_ofRename] using inductionPrinciple_subst successor zero (Subst.ofRename rho))
    (principle.rename rho)

theorem inductionRename_free (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) (rho : Rename Base Γ Ξ)
    (free : principle.FunctionExtensionalityFree) : (inductionRename successor zero principle rho).FunctionExtensionalityFree := by
  simpa only [inductionRename, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free

def comparisonAdvance (first second : Term Const Γ number)
    (given : ProofSyntax Const Δ (comparisonCases successor first second)) :
    ProofSyntax Const Δ (comparisonCases successor (.app (weakenCtx Γ successor) first) (.app (weakenCtx Γ successor) second)) :=
  .orE given (.orIL (lessSuccessorMap successor first second (.hyp 0)))
    (.orE (.hyp 0) (.orIR (.orIL (.eqAppArg (weakenCtx Γ successor) (.hyp 0))))
      (.orIR (.orIR (lessSuccessorMap successor second first (.hyp 0)))))

theorem comparisonAdvance_free (first second : Term Const Γ number)
    (given : ProofSyntax Const Δ (comparisonCases successor first second)) (free : given.FunctionExtensionalityFree) :
    (comparisonAdvance successor first second given).FunctionExtensionalityFree := by
  simp [comparisonAdvance, ProofSyntax.FunctionExtensionalityFree, lessSuccessorMap_free, free]

def comparisonZeroStep (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (successorClosed successor (comparisonRight successor (weakenCtx Γ zero))) := by
  refine .allI (.impI ?_)
  let premise := Term.app (weaken (comparisonRight successor (weakenCtx Γ zero))) (.var .vz)
  have current := (inductionRename successor zero principle (Rename.weaken (σ := number))).prepend premise
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (comparisonRight_beta successor (weakenCtx (number :: Γ) zero)
      (.app (weakenCtx _ successor) (.var .vz)))) (.orIL (zeroLessSuccessor successor zero (.var .vz) current)))
  simp only [weaken, comparisonRight_rename, rename_weakenCtx]

theorem comparisonZeroStep_free (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) : (comparisonZeroStep successor zero principle).FunctionExtensionalityFree := by
  unfold comparisonZeroStep
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨comparisonRight_beta_free _ _ _, ?_⟩
  apply zeroLessSuccessor_free
  simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono] using
    inductionRename_free successor zero principle (Rename.weaken (σ := number)) free

def comparisonZero (second : Term Const Γ number) (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (comparisonCases successor (weakenCtx Γ zero) second) :=
  .impE (.eqPropEL (comparisonRight_beta successor (weakenCtx Γ zero) second))
    (inductionAt successor zero (comparisonRight successor (weakenCtx Γ zero)) second principle
      (.impE (.eqPropER (comparisonRight_beta successor (weakenCtx Γ zero) (weakenCtx Γ zero)))
        (.orIR (.orIL (.eqRefl _)))) (comparisonZeroStep successor zero principle))

theorem comparisonZero_free (second : Term Const Γ number) (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) : (comparisonZero successor zero second principle).FunctionExtensionalityFree :=
  ⟨comparisonRight_beta_free _ _ _,inductionAt_free _ _ _ _ principle _ _ free
    ⟨comparisonRight_beta_free _ _ _,True.intro⟩ (comparisonZeroStep_free successor zero principle free)⟩

def comparisonSuccessorStep (first : Term Const Γ number)
    (previous : ProofSyntax Const Δ (comparisonAll successor first)) :
    ProofSyntax Const Δ (successorClosed successor (comparisonRight successor (.app (weakenCtx Γ successor) first))) := by
  refine .allI (.impI ?_)
  let premise := Term.app (weaken (comparisonRight successor (.app (weakenCtx Γ successor) first))) (.var .vz)
  have old : ProofSyntax Const (premise :: weakenHyps Δ) (comparisonAll successor (weaken first)) := by
    apply ProofSyntax.castIndices rfl ?_ ((previous.rename Rename.weaken).prepend premise)
    exact comparisonAll_rename successor Rename.weaken first
  have smaller := comparisonAt successor (weaken first) (.var .vz) old
  have advanced := comparisonAdvance successor (weaken first) (.var .vz) smaller
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (comparisonRight_beta successor (.app (weakenCtx (number :: Γ) successor) (weaken first))
      (.app (weakenCtx _ successor) (.var .vz)))) advanced)
  simp only [weaken, comparisonRight_rename, HOL.rename, rename_weakenCtx]

theorem comparisonSuccessorStep_free (first : Term Const Γ number)
    (previous : ProofSyntax Const Δ (comparisonAll successor first)) (free : previous.FunctionExtensionalityFree) :
    (comparisonSuccessorStep successor first previous).FunctionExtensionalityFree := by
  unfold comparisonSuccessorStep
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨comparisonRight_beta_free _ _ _, ?_⟩
  apply comparisonAdvance_free
  apply comparisonAt_free
  simpa only [ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.prepend,
    ProofSyntax.functionExtensionalityFree_mono, ProofSyntax.functionExtensionalityFree_rename] using free

def comparisonSuccessor (first second : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (previous : ProofSyntax Const Δ (comparisonAll successor first)) :
    ProofSyntax Const Δ (comparisonCases successor (.app (weakenCtx Γ successor) first) second) :=
  .impE (.eqPropEL (comparisonRight_beta successor (.app (weakenCtx Γ successor) first) second))
    (inductionAt successor zero (comparisonRight successor (.app (weakenCtx Γ successor) first)) second principle
      (.impE (.eqPropER (comparisonRight_beta successor (.app (weakenCtx Γ successor) first) (weakenCtx Γ zero)))
        (.orIR (.orIR (zeroLessSuccessor successor zero first principle))))
      (comparisonSuccessorStep successor first previous))

theorem comparisonSuccessor_free (first second : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (previous : ProofSyntax Const Δ (comparisonAll successor first))
    (principleFree : principle.FunctionExtensionalityFree) (previousFree : previous.FunctionExtensionalityFree) :
    (comparisonSuccessor successor zero first second principle previous).FunctionExtensionalityFree :=
  ⟨comparisonRight_beta_free _ _ _,inductionAt_free _ _ _ _ principle _ _ principleFree
    ⟨comparisonRight_beta_free _ _ _,zeroLessSuccessor_free _ _ _ principle principleFree⟩
    (comparisonSuccessorStep_free successor first previous previousFree)⟩

def comparisonAllZero (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (comparisonAll successor (weakenCtx Γ zero)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.castIndices rfl ?_
    (comparisonZero successor zero (.var .vz) (inductionRename successor zero principle Rename.weaken))
  simp only [weaken, rename_weakenCtx]

theorem comparisonAllZero_free (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) : (comparisonAllZero successor zero principle).FunctionExtensionalityFree := by
  unfold comparisonAllZero
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact comparisonZero_free _ _ _ _ (inductionRename_free successor zero principle Rename.weaken free)

def comparisonAllSuccessor (first : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (previous : ProofSyntax Const Δ (comparisonAll successor first)) :
    ProofSyntax Const Δ (comparisonAll successor (.app (weakenCtx Γ successor) first)) := by
  apply ProofSyntax.allI
  have old : ProofSyntax Const (weakenHyps (σ := number) Δ) (comparisonAll successor (weaken (σ := number) first)) :=
    ProofSyntax.castIndices rfl (comparisonAll_rename successor Rename.weaken first) (previous.rename Rename.weaken)
  apply ProofSyntax.castIndices rfl ?_
    (comparisonSuccessor successor zero (weaken first) (.var .vz)
      (inductionRename successor zero principle Rename.weaken) old)
  simp only [weaken, HOL.rename, rename_weakenCtx]

theorem comparisonAllSuccessor_free (first : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (previous : ProofSyntax Const Δ (comparisonAll successor first))
    (principleFree : principle.FunctionExtensionalityFree) (previousFree : previous.FunctionExtensionalityFree) :
    (comparisonAllSuccessor successor zero first principle previous).FunctionExtensionalityFree := by
  unfold comparisonAllSuccessor
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply comparisonSuccessor_free
  · exact inductionRename_free successor zero principle Rename.weaken principleFree
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_rename] using previousFree

def comparisonMotiveStep (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (successorClosed successor (comparisonMotive successor)) := by
  refine .allI (.impI ?_)
  let premise := Term.app (weaken (comparisonMotive (Γ := Γ) successor)) (.var .vz)
  have current := (inductionRename successor zero principle (Rename.weaken (σ := number))).prepend premise
  have supplied : ProofSyntax Const (premise :: weakenHyps Δ) (.app (comparisonMotive successor) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := premise :: weakenHyps Δ) 0)
    change premise = _
    simp only [premise,weaken,comparisonMotive_rename]
  have old := ProofSyntax.impE (.eqPropEL (comparisonMotive_beta successor (.var .vz))) supplied
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (comparisonMotive_beta successor (.app (weakenCtx _ successor) (.var .vz))))
      (comparisonAllSuccessor successor zero (.var .vz) current old))
  simp only [weaken,comparisonMotive_rename]

theorem comparisonMotiveStep_free (principle : ProofSyntax Const Δ
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) : (comparisonMotiveStep successor zero principle).FunctionExtensionalityFree := by
  unfold comparisonMotiveStep
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨comparisonMotive_beta_free _ _, ?_⟩
  apply comparisonAllSuccessor_free
  · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono] using
      inductionRename_free successor zero principle (Rename.weaken (σ := number)) free
  · refine ⟨comparisonMotive_beta_free _ _, ?_⟩
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

def comparisonCoverage (first second : Term Const Γ number)
    (principle : ProofSyntax Const Δ
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (comparisonCases successor first second) :=
  comparisonAt successor first second
    (.impE (.eqPropEL (comparisonMotive_beta successor first))
      (inductionAt successor zero (comparisonMotive successor) first principle
        (.impE (.eqPropER (comparisonMotive_beta successor (weakenCtx Γ zero))) (comparisonAllZero successor zero principle))
        (comparisonMotiveStep successor zero principle)))

theorem comparisonCoverage_free (first second : Term Const Γ number)
    (principle : ProofSyntax Const Δ
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) : (comparisonCoverage successor zero first second principle).FunctionExtensionalityFree :=
  comparisonAt_free _ _ _ _ ⟨comparisonMotive_beta_free _ _,inductionAt_free _ _ _ _ principle _ _ free
    ⟨comparisonMotive_beta_free _ _,comparisonAllZero_free successor zero principle free⟩
    (comparisonMotiveStep_free successor zero principle free)⟩

def comparisonOtherwise (first second : Term Const Γ number)
    (principle : ProofSyntax Const Δ
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (different : ProofSyntax Const Δ (.not (.eq first second)))
    (notEarlier : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (less successor)) second) first))) :
    ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) first) second) :=
  .orE (comparisonCoverage successor zero first second principle) (.hyp 0)
    (.orE (.hyp 0) (.botE (.notE ((different.prepend _).prepend _) (.hyp 0)))
      (.botE (.notE ((notEarlier.prepend _).prepend _) (.hyp 0))))

theorem comparisonOtherwise_free (first second : Term Const Γ number)
    (principle : ProofSyntax Const Δ
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (different : ProofSyntax Const Δ (.not (.eq first second)))
    (notEarlier : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (less successor)) second) first)))
    (principleFree : principle.FunctionExtensionalityFree) (differentFree : different.FunctionExtensionalityFree)
    (notEarlierFree : notEarlier.FunctionExtensionalityFree) :
    (comparisonOtherwise successor zero first second principle different notEarlier).FunctionExtensionalityFree := by
  simp only [comparisonOtherwise, ProofSyntax.FunctionExtensionalityFree, ProofSyntax.prepend,
    ProofSyntax.functionExtensionalityFree_mono, comparisonCoverage_free _ _ _ _ principle principleFree,
    differentFree, notEarlierFree, and_self]

#print axioms comparisonCoverage
#print axioms comparisonCoverage_free
#print axioms comparisonOtherwise_free
end Mettapedia.Logic.HOL.SuccessorOrder
