import Mettapedia.Logic.HOL.SuccessorOrderProofs

/-!
# Retained transformations of synchronized successor closure

Starting sum at zero identifies its count and result. Moving its starting
point through successor produces an explicit predecessor witness for the
result. These transformations use the authored closure rules, without
assuming Peano induction or an external addition operation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder

open CurriedGuardProgramProofs
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
    (successor : ClosedTerm Const (number ⇒ number)) (zero : ClosedTerm Const number)

def equalInputs : Term Const Γ (number ⇒ number ⇒ .prop) :=
  .lam (.lam (.eq (.var (.vs .vz)) (.var .vz)))

def equalInputs_beta {assumptions : List (Formula Const Γ)} (first second : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (.app equalInputs first) second) (.eq first second)) := by
  apply ProofSyntax.castIndices rfl ?_ (beta2 (.eq (.var (.vs .vz)) (.var .vz)) first second)
  simp only [instantiate, HOL.subst, Subst.single, Subst.lift]
  have cancel : HOL.subst (Subst.single second) (HOL.rename Rename.weaken first) = first :=
    PredicateFixedPoint.subst_single_weaken second first
  rw [cancel]
  rfl

theorem equalInputs_beta_free {assumptions : List (Formula Const Γ)} (first second : Term Const Γ number) :
    (equalInputs_beta (assumptions := assumptions) first second).FunctionExtensionalityFree := by
  unfold equalInputs_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact beta2_free _ _ _

def sumZeroReflect {assumptions : List (Formula Const Γ)} (count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) (weakenCtx Γ zero)) count) result)) :
    ProofSyntax Const assumptions (.eq count result) := by
  have start : ProofSyntax Const assumptions
      (.app (.app equalInputs (weakenCtx Γ zero)) (weakenCtx Γ zero)) :=
    .impE (.eqPropER (equalInputs_beta _ _)) (.eqRefl (weakenCtx Γ zero))
  have closed : ProofSyntax Const assumptions (sumClosed successor equalInputs) := by
    apply ProofSyntax.allI
    apply ProofSyntax.allI
    apply ProofSyntax.impI
    let first : Term Const (number :: number :: Γ) number := .var (.vs .vz)
    let second : Term Const (number :: number :: Γ) number := .var .vz
    have previous : ProofSyntax Const
        (.app (.app equalInputs first) second :: weakenHyps (weakenHyps assumptions))
        (.eq first second) :=
      .impE (.eqPropEL (equalInputs_beta first second)) (.hyp 0)
    exact .impE (.eqPropER (equalInputs_beta (.app (weakenCtx _ successor) first)
      (.app (weakenCtx _ successor) second))) (.eqAppArg (weakenCtx _ successor) previous)
  have atResult := sumEliminate successor zero (weakenCtx Γ zero) count result equalInputs present start closed
  exact .impE (.eqPropEL (equalInputs_beta count result)) atResult

theorem sumZeroReflect_free {assumptions : List (Formula Const Γ)} (count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) (weakenCtx Γ zero)) count) result))
    (free : present.FunctionExtensionalityFree) :
    (sumZeroReflect successor zero count result present).FunctionExtensionalityFree := by
  unfold sumZeroReflect
  refine ⟨equalInputs_beta_free _ _, ?_⟩
  apply sumEliminate_free
  · exact free
  · exact ⟨equalInputs_beta_free _ _, trivial⟩
  · exact ⟨equalInputs_beta_free _ _, equalInputs_beta_free _ _, trivial⟩

#print axioms sumZeroReflect
#print axioms sumZeroReflect_free

/-- An explicit predecessor of the result, retaining its original sum proof. -/
def predecessorSum (first count result : Term Const Γ number) : Formula Const Γ :=
  .ex (.and (.eq (weaken result) (.app (weakenCtx _ successor) (.var .vz)))
    (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken count)) (.var .vz)))

theorem predecessorSum_subst (images : Subst Const Γ Ξ) (first count result : Term Const Γ number) :
    HOL.subst images (predecessorSum successor zero first count result) =
      predecessorSum successor zero (HOL.subst images first) (HOL.subst images count)
        (HOL.subst images result) := by
  simp only [predecessorSum, HOL.subst, subst_weaken, subst_weakenCtx, Subst.lift]

theorem predecessorSum_rename (images : Rename Base Γ Ξ) (first count result : Term Const Γ number) :
    HOL.rename images (predecessorSum successor zero first count result) =
      predecessorSum successor zero (HOL.rename images first) (HOL.rename images count)
        (HOL.rename images result) := by
  simp only [predecessorSum, HOL.rename, ExtDerivation.rename_weaken, rename_weakenCtx, Rename.lift]

def predecessorSumProgram (first : Term Const Γ number) : Term Const Γ (number ⇒ number ⇒ .prop) :=
  .lam (.lam (predecessorSum successor zero (weaken (weaken first)) (.var (.vs .vz)) (.var .vz)))

theorem predecessorSumProgram_rename (images : Rename Base Γ Ξ) (first : Term Const Γ number) :
    HOL.rename images (predecessorSumProgram successor zero first) =
      predecessorSumProgram successor zero (HOL.rename images first) := by
  simp only [predecessorSumProgram, HOL.rename, predecessorSum_rename, ExtDerivation.rename_weaken, Rename.lift]

def predecessorSumProgram_beta {assumptions : List (Formula Const Γ)}
    (first count result : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (.app (predecessorSumProgram successor zero first) count) result)
      (predecessorSum successor zero first count result)) := by
  apply ProofSyntax.castIndices rfl ?_ (beta2
    (predecessorSum successor zero (weaken (weaken first)) (.var (.vs .vz)) (.var .vz)) count result)
  apply congrArg₂ Term.eq
  · rfl
  · simp only [instantiate, predecessorSum_subst, subst_weaken, Subst.single, Subst.lift, HOL.subst]
    simp only [PredicateFixedPoint.subst_single_weaken]
    exact congrArg (fun point => predecessorSum successor zero first point result)
      (PredicateFixedPoint.subst_single_weaken result count)

theorem predecessorSumProgram_beta_free {assumptions : List (Formula Const Γ)}
    (first count result : Term Const Γ number) :
    (predecessorSumProgram_beta successor zero (assumptions := assumptions) first count result).FunctionExtensionalityFree := by
  unfold predecessorSumProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact beta2_free _ _ _

def predecessorSumIntro {assumptions : List (Formula Const Γ)}
    (first count result predecessor : Term Const Γ number)
    (equal : ProofSyntax Const assumptions (.eq result (.app (weakenCtx Γ successor) predecessor)))
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) predecessor)) :
    ProofSyntax Const assumptions (predecessorSum successor zero first count result) := by
  apply ProofSyntax.exI predecessor
  apply ProofSyntax.castIndices rfl ?_ (.andI equal present)
  simp only [instantiate, HOL.subst, Subst.single, subst_weakenCtx, PredicateFixedPoint.subst_single_weaken]

theorem predecessorSumIntro_free {assumptions : List (Formula Const Γ)}
    (first count result predecessor : Term Const Γ number)
    (equal : ProofSyntax Const assumptions (.eq result (.app (weakenCtx Γ successor) predecessor)))
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) predecessor))
    (equalFree : equal.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (predecessorSumIntro successor zero first count result predecessor equal present).FunctionExtensionalityFree := by
  unfold predecessorSumIntro
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨equalFree, presentFree⟩

def predecessorSumStep {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions (predecessorSum successor zero first count result)) :
    ProofSyntax Const assumptions (predecessorSum successor zero first
      (.app (weakenCtx Γ successor) count) (.app (weakenCtx Γ successor) result)) := by
  apply ProofSyntax.exE present
  let body : Formula Const (number :: Γ) :=
    .and (.eq (weaken result) (.app (weakenCtx _ successor) (.var .vz)))
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken count)) (.var .vz))
  let hypotheses := body :: weakenHyps assumptions
  have given : ProofSyntax Const hypotheses body := .hyp 0
  have nextSum := sumStep successor zero (weaken first) (weaken count) (.var .vz) (.andER given)
  have nextEqual := ProofSyntax.eqAppArg (weakenCtx _ successor) (.andEL given)
  apply ProofSyntax.castIndices rfl ?_ (predecessorSumIntro successor zero (weaken first)
    (.app (weakenCtx _ successor) (weaken count)) (.app (weakenCtx _ successor) (weaken result))
    (.app (weakenCtx _ successor) (.var .vz)) nextEqual nextSum)
  simp only [weaken, predecessorSum_rename, HOL.rename, rename_weakenCtx]

theorem predecessorSumStep_free {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions (predecessorSum successor zero first count result))
    (free : present.FunctionExtensionalityFree) :
    (predecessorSumStep successor zero first count result present).FunctionExtensionalityFree := by
  unfold predecessorSumStep
  refine ⟨free, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply predecessorSumIntro_free
  · trivial
  · apply sumStep_free
    trivial

/-- Moving the first input through successor exposes a predecessor of the result. -/
def sumLeftSuccessor {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor))
        (.app (weakenCtx Γ successor) first)) count) result)) :
    ProofSyntax Const assumptions (predecessorSum successor zero first count result) := by
  let predicate := predecessorSumProgram successor zero first
  have start : ProofSyntax Const assumptions
      (.app (.app predicate (weakenCtx Γ zero)) (.app (weakenCtx Γ successor) first)) :=
    .impE (.eqPropER (predecessorSumProgram_beta successor zero first (weakenCtx Γ zero)
      (.app (weakenCtx Γ successor) first)))
      (predecessorSumIntro successor zero first (weakenCtx Γ zero)
        (.app (weakenCtx Γ successor) first) first (.eqRefl _) (sumZero successor zero first))
  have closed : ProofSyntax Const assumptions (sumClosed successor predicate) := by
    apply ProofSyntax.allI
    apply ProofSyntax.allI
    apply ProofSyntax.impI
    let first' : Term Const (number :: number :: Γ) number := weaken (weaken first)
    let count' : Term Const (number :: number :: Γ) number := .var (.vs .vz)
    let result' : Term Const (number :: number :: Γ) number := .var .vz
    let antecedent := Term.app (.app (weaken (weaken predicate)) count') result'
    let hypotheses := antecedent :: weakenHyps (weakenHyps assumptions)
    have given : ProofSyntax Const hypotheses
        (.app (.app (predecessorSumProgram successor zero first') count') result') := by
      apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
      change antecedent = _
      simp only [antecedent, predicate, weaken, predecessorSumProgram_rename, first']
    have previous := ProofSyntax.impE (.eqPropEL (predecessorSumProgram_beta successor zero first' count' result')) given
    have advanced := predecessorSumStep successor zero first' count' result' previous
    have next := ProofSyntax.impE (.eqPropER (predecessorSumProgram_beta successor zero first'
      (.app (weakenCtx _ successor) count') (.app (weakenCtx _ successor) result'))) advanced
    apply ProofSyntax.castIndices rfl ?_ next
    simp only [predicate, weaken, predecessorSumProgram_rename, first']
    rfl
  have selected := sumEliminate successor zero (.app (weakenCtx Γ successor) first) count result
    predicate present start closed
  exact .impE (.eqPropEL (predecessorSumProgram_beta successor zero first count result)) selected

theorem sumLeftSuccessor_free {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor))
        (.app (weakenCtx Γ successor) first)) count) result))
    (free : present.FunctionExtensionalityFree) :
    (sumLeftSuccessor successor zero first count result present).FunctionExtensionalityFree := by
  unfold sumLeftSuccessor
  refine ⟨predecessorSumProgram_beta_free _ _ _ _ _, ?_⟩
  apply sumEliminate_free
  · exact free
  · constructor
    · exact predecessorSumProgram_beta_free _ _ _ _ _
    · apply predecessorSumIntro_free
      · trivial
      · exact sumZero_free _ _ _
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    constructor
    · exact predecessorSumProgram_beta_free _ _ _ _ _
    · apply predecessorSumStep_free
      constructor
      · exact predecessorSumProgram_beta_free _ _ _ _ _
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial

#print axioms predecessorSumIntro_free
#print axioms predecessorSumStep_free
#print axioms sumLeftSuccessor
#print axioms sumLeftSuccessor_free

/-- The upper endpoint has a predecessor strictly above the lower endpoint. -/
def predecessorLess (lower upper : Term Const Γ number) : Formula Const Γ :=
  .ex (.and (.eq (weaken upper) (.app (weakenCtx _ successor) (.var .vz)))
    (.app (.app (weakenCtx _ (less successor)) (weaken lower)) (.var .vz)))

theorem predecessorLess_subst (images : Subst Const Γ Ξ) (lower upper : Term Const Γ number) :
    HOL.subst images (predecessorLess successor lower upper) =
      predecessorLess successor (HOL.subst images lower) (HOL.subst images upper) := by
  simp only [predecessorLess, HOL.subst, subst_weaken, subst_weakenCtx, Subst.lift]

theorem predecessorLess_rename (images : Rename Base Γ Ξ) (lower upper : Term Const Γ number) :
    HOL.rename images (predecessorLess successor lower upper) =
      predecessorLess successor (HOL.rename images lower) (HOL.rename images upper) := by
  simp only [predecessorLess, HOL.rename, ExtDerivation.rename_weaken, rename_weakenCtx, Rename.lift]

def predecessorLessProgram (lower : Term Const Γ number) : Term Const Γ (number ⇒ .prop) :=
  .lam (predecessorLess successor (weaken lower) (.var .vz))

theorem predecessorLessProgram_rename (images : Rename Base Γ Ξ) (lower : Term Const Γ number) :
    HOL.rename images (predecessorLessProgram successor lower) =
      predecessorLessProgram successor (HOL.rename images lower) := by
  simp only [predecessorLessProgram, HOL.rename, predecessorLess_rename, ExtDerivation.rename_weaken, Rename.lift]

def predecessorLessProgram_beta {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (predecessorLessProgram successor lower) upper)
      (predecessorLess successor lower upper)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta upper (predecessorLess successor (weaken lower) (.var .vz)))
  simp only [instantiate, predecessorLess_subst, PredicateFixedPoint.subst_single_weaken,
    HOL.subst, Subst.single]
  rfl

theorem predecessorLessProgram_beta_free {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number) :
    (predecessorLessProgram_beta successor (assumptions := assumptions) lower upper).FunctionExtensionalityFree := by
  unfold predecessorLessProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def predecessorLessIntro {assumptions : List (Formula Const Γ)} (lower upper predecessor : Term Const Γ number)
    (equal : ProofSyntax Const assumptions (.eq upper (.app (weakenCtx Γ successor) predecessor)))
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower) predecessor)) :
    ProofSyntax Const assumptions (predecessorLess successor lower upper) := by
  apply ProofSyntax.exI predecessor
  apply ProofSyntax.castIndices rfl ?_ (.andI equal present)
  simp only [instantiate, HOL.subst, Subst.single, subst_weakenCtx, PredicateFixedPoint.subst_single_weaken]

theorem predecessorLessIntro_free {assumptions : List (Formula Const Γ)} (lower upper predecessor : Term Const Γ number)
    (equal : ProofSyntax Const assumptions (.eq upper (.app (weakenCtx Γ successor) predecessor)))
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower) predecessor))
    (equalFree : equal.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (predecessorLessIntro successor lower upper predecessor equal present).FunctionExtensionalityFree := by
  unfold predecessorLessIntro
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨equalFree, presentFree⟩

def predecessorLessStep {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number)
    (present : ProofSyntax Const assumptions (predecessorLess successor lower upper)) :
    ProofSyntax Const assumptions (predecessorLess successor lower (.app (weakenCtx Γ successor) upper)) := by
  apply ProofSyntax.exE present
  let body : Formula Const (number :: Γ) :=
    .and (.eq (weaken upper) (.app (weakenCtx _ successor) (.var .vz)))
      (.app (.app (weakenCtx _ (less successor)) (weaken lower)) (.var .vz))
  have given : ProofSyntax Const (body :: weakenHyps assumptions) body := .hyp 0
  have next := lessStep successor (weaken lower) (.var .vz) (.andER given)
  apply ProofSyntax.castIndices rfl ?_ (predecessorLessIntro successor (weaken lower)
    (.app (weakenCtx _ successor) (weaken upper)) (.app (weakenCtx _ successor) (.var .vz))
    (.eqAppArg (weakenCtx _ successor) (.andEL given)) next)
  simp only [weaken, predecessorLess_rename, HOL.rename, rename_weakenCtx]

theorem predecessorLessStep_free {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number)
    (present : ProofSyntax Const assumptions (predecessorLess successor lower upper))
    (free : present.FunctionExtensionalityFree) :
    (predecessorLessStep successor lower upper present).FunctionExtensionalityFree := by
  unfold predecessorLessStep
  refine ⟨free, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply predecessorLessIntro_free
  · trivial
  · apply lessStep_free
    trivial

def lessLeftSuccessor {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Γ (less successor)) (.app (weakenCtx Γ successor) lower)) upper)) :
    ProofSyntax Const assumptions (predecessorLess successor lower upper) := by
  let predicate := predecessorLessProgram successor lower
  have start : ProofSyntax Const assumptions
      (.app predicate (.app (weakenCtx Γ successor) (.app (weakenCtx Γ successor) lower))) :=
    .impE (.eqPropER (predecessorLessProgram_beta successor lower _))
      (predecessorLessIntro successor lower _ (.app (weakenCtx Γ successor) lower)
        (.eqRefl _) (lessNext successor lower))
  have closed : ProofSyntax Const assumptions (successorClosed successor predicate) := by
    apply ProofSyntax.allI
    apply ProofSyntax.impI
    let upper' : Term Const (number :: Γ) number := .var .vz
    let antecedent := Term.app (weaken predicate) upper'
    let hypotheses := antecedent :: weakenHyps assumptions
    have given : ProofSyntax Const hypotheses (.app (predecessorLessProgram successor (weaken lower)) upper') := by
      apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
      change antecedent = _
      simp only [antecedent, predicate, weaken, predecessorLessProgram_rename]
    have previous := ProofSyntax.impE (.eqPropEL (predecessorLessProgram_beta successor (weaken lower) upper')) given
    have advanced := predecessorLessStep successor (weaken lower) upper' previous
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.impE (.eqPropER (predecessorLessProgram_beta successor (weaken lower)
        (.app (weakenCtx _ successor) upper'))) advanced)
    simp only [predicate, weaken, predecessorLessProgram_rename]
    rfl
  have selected := lessEliminate successor (.app (weakenCtx Γ successor) lower) upper predicate present start closed
  exact .impE (.eqPropEL (predecessorLessProgram_beta successor lower upper)) selected

theorem lessLeftSuccessor_free {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Γ (less successor)) (.app (weakenCtx Γ successor) lower)) upper))
    (free : present.FunctionExtensionalityFree) :
    (lessLeftSuccessor successor lower upper present).FunctionExtensionalityFree := by
  unfold lessLeftSuccessor
  refine ⟨predecessorLessProgram_beta_free _ _ _, ?_⟩
  apply lessEliminate_free
  · exact free
  · constructor
    · exact predecessorLessProgram_beta_free _ _ _
    · apply predecessorLessIntro_free
      · trivial
      · exact lessNext_free _ _
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    constructor
    · exact predecessorLessProgram_beta_free _ _ _
    · apply predecessorLessStep_free
      constructor
      · exact predecessorLessProgram_beta_free _ _ _
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial

/-- Cancellation uses successor injectivity, without separation or induction. -/
def lessSuccessorCancel {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number)
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor))
      (.app (weakenCtx Γ successor) lower)) (.app (weakenCtx Γ successor) upper))) :
    ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower) upper) := by
  have witness := lessLeftSuccessor successor lower (.app (weakenCtx Γ successor) upper) present
  apply ProofSyntax.exE witness
  let body : Formula Const (number :: Γ) :=
    .and (.eq (weaken (.app (weakenCtx Γ successor) upper)) (.app (weakenCtx _ successor) (.var .vz)))
      (.app (.app (weakenCtx _ (less successor)) (weaken lower)) (.var .vz))
  let hypotheses := body :: weakenHyps assumptions
  have given : ProofSyntax Const hypotheses body := .hyp 0
  have law : ProofSyntax Const hypotheses (NaturalNumeralProofs.injectivity (weakenCtx (number :: Γ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken injective).prepend body)
    simp only [NaturalNumeralProofs.injectivity, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
  have equal : ProofSyntax Const hypotheses (.eq (weaken upper) (.var .vz)) :=
    .impE (.eqPropEL (NaturalNumeralProofs.successorEquality (weakenCtx _ successor) (weaken upper) (.var .vz) law))
      (ProofSyntax.castIndices rfl (by simp only [weaken, HOL.rename, rename_weakenCtx]) (.andEL given))
  have transferred := ProofSyntax.impE
    (.eqPropER (.eqAppArg (.app (weakenCtx _ (less successor)) (weaken lower)) equal)) (.andER given)
  apply ProofSyntax.castIndices rfl ?_ transferred
  simp only [weaken, HOL.rename, rename_weakenCtx]

theorem lessSuccessorCancel_free {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number)
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor))
      (.app (weakenCtx Γ successor) lower)) (.app (weakenCtx Γ successor) upper)))
    (injectiveFree : injective.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (lessSuccessorCancel successor lower upper injective present).FunctionExtensionalityFree := by
  unfold lessSuccessorCancel
  refine ⟨lessLeftSuccessor_free _ _ _ _ presentFree, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  constructor
  · constructor
    · apply NaturalNumeralProofs.successorEquality_free
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr injectiveFree
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      trivial
  · trivial

#print axioms lessLeftSuccessor
#print axioms lessLeftSuccessor_free
#print axioms lessSuccessorCancel
#print axioms lessSuccessorCancel_free

end Mettapedia.Logic.HOL.SuccessorOrder
