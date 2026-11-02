import Mettapedia.Logic.HOL.SuccessorOrderTransforms

/-!
# Retained induction for successor-closure arithmetic

The result stays universally quantified inside the induction motive. This
allows the successor step to use the predecessor result supplied by closure
elimination. Separation, injectivity and induction remain explicit inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
    (successor : ClosedTerm Const (number ⇒ number)) (zero : ClosedTerm Const number)

def inductionAt {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ .prop)) (point : Term Const Γ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (start : ProofSyntax Const assumptions (.app predicate (weakenCtx Γ zero)))
    (step : ProofSyntax Const assumptions (successorClosed successor predicate)) :
    ProofSyntax Const assumptions (.app predicate point) := by
  have every := ProofSyntax.impE (NaturalRecursionProofs.inductionInstance
    (weakenCtx Γ zero) (weakenCtx Γ successor) predicate principle) (.andI start step)
  apply ProofSyntax.castIndices rfl ?_ (.allE point every)
  simp only [instantiate, HOL.subst, Subst.single, PredicateFixedPoint.subst_single_weaken]

theorem inductionAt_free {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ .prop)) (point : Term Const Γ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (start : ProofSyntax Const assumptions (.app predicate (weakenCtx Γ zero)))
    (step : ProofSyntax Const assumptions (successorClosed successor predicate))
    (principleFree : principle.FunctionExtensionalityFree)
    (startFree : start.FunctionExtensionalityFree) (stepFree : step.FunctionExtensionalityFree) :
    (inductionAt successor zero predicate point principle start step).FunctionExtensionalityFree := by
  unfold inductionAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  constructor
  · unfold NaturalRecursionProofs.inductionInstance
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact principleFree
  · exact ⟨startFree, stepFree⟩

def sumBoundBody (first offset : Term Const Γ number) : Formula Const Γ :=
  .all (.imp (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken offset)) (.var .vz))
    (.not (.app (.app (weakenCtx _ (less successor)) (.var .vz)) (weaken first))))

theorem sumBoundBody_subst (images : Subst Const Γ Ξ) (first offset : Term Const Γ number) :
    HOL.subst images (sumBoundBody successor zero first offset) =
      sumBoundBody successor zero (HOL.subst images first) (HOL.subst images offset) := by
  simp only [sumBoundBody, HOL.subst, subst_weakenCtx, subst_weaken, Subst.lift]

theorem sumBoundBody_rename (images : Rename Base Γ Ξ) (first offset : Term Const Γ number) :
    HOL.rename images (sumBoundBody successor zero first offset) =
      sumBoundBody successor zero (HOL.rename images first) (HOL.rename images offset) := by
  simp only [sumBoundBody, HOL.rename, rename_weakenCtx, ExtDerivation.rename_weaken, Rename.lift]

def sumBoundProgram (offset : Term Const Γ number) : Term Const Γ (number ⇒ .prop) :=
  .lam (sumBoundBody successor zero (.var .vz) (weaken offset))

theorem sumBoundProgram_rename (images : Rename Base Γ Ξ) (offset : Term Const Γ number) :
    HOL.rename images (sumBoundProgram successor zero offset) =
      sumBoundProgram successor zero (HOL.rename images offset) := by
  simp only [sumBoundProgram, HOL.rename, sumBoundBody_rename, ExtDerivation.rename_weaken, Rename.lift]

def sumBoundProgram_beta {assumptions : List (Formula Const Γ)} (first offset : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (sumBoundProgram successor zero offset) first)
      (sumBoundBody successor zero first offset)) := by
  apply ProofSyntax.castIndices rfl ?_
    (.beta first (sumBoundBody successor zero (.var .vz) (weaken offset)))
  simp only [instantiate, sumBoundBody_subst, HOL.subst, Subst.single, PredicateFixedPoint.subst_single_weaken]
  rfl

theorem sumBoundProgram_beta_free {assumptions : List (Formula Const Γ)} (first offset : Term Const Γ number) :
    (sumBoundProgram_beta successor zero (assumptions := assumptions) first offset).FunctionExtensionalityFree := by
  unfold sumBoundProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def sumBoundAt {assumptions : List (Formula Const Γ)} (first offset result : Term Const Γ number)
    (bound : ProofSyntax Const assumptions (sumBoundBody successor zero first offset)) :
    ProofSyntax Const assumptions (.imp
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) offset) result)
      (.not (.app (.app (weakenCtx Γ (less successor)) result) first))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE result bound)
  simp only [instantiate, HOL.subst, Subst.single, subst_weakenCtx, PredicateFixedPoint.subst_single_weaken]

theorem sumBoundAt_free {assumptions : List (Formula Const Γ)} (first offset result : Term Const Γ number)
    (bound : ProofSyntax Const assumptions (sumBoundBody successor zero first offset))
    (free : bound.FunctionExtensionalityFree) :
    (sumBoundAt successor zero first offset result bound).FunctionExtensionalityFree := by
  unfold sumBoundAt
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

def sumBoundBase {assumptions : List (Formula Const Γ)} (offset : Term Const Γ number)
    (separate : ProofSyntax Const assumptions
      (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const assumptions (sumBoundBody successor zero (weakenCtx Γ zero) offset) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.notI
  let result : Term Const (number :: Γ) number := .var .vz
  let sumClaim := Term.app (.app (.app (weakenCtx _ (sum zero successor)) (weakenCtx _ zero)) (weaken offset)) result
  let lessClaim := Term.app (.app (weakenCtx _ (less successor)) result) (weakenCtx _ zero)
  let hypotheses := lessClaim :: sumClaim :: weakenHyps assumptions
  have law : ProofSyntax Const hypotheses
      (NaturalNumeralProofs.separation (weakenCtx (number :: Γ) zero) (weakenCtx (number :: Γ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_
      (((ProofSyntax.rename Rename.weaken separate).prepend sumClaim).prepend lessClaim)
    simp only [NaturalNumeralProofs.separation, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
  exact lessZeroRefute successor zero result law (.hyp 0)

theorem sumBoundBase_free {assumptions : List (Formula Const Γ)} (offset : Term Const Γ number)
    (separate : ProofSyntax Const assumptions
      (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : separate.FunctionExtensionalityFree) :
    (sumBoundBase successor zero offset separate).FunctionExtensionalityFree := by
  unfold sumBoundBase
  apply lessZeroRefute_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free
  · trivial

def sumBoundSuccessorRefute {assumptions : List (Formula Const Γ)} (first offset result : Term Const Γ number)
    (bound : ProofSyntax Const assumptions (sumBoundBody successor zero first offset))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) (.app (weakenCtx Γ successor) first)) offset) result))
    (smaller : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Γ (less successor)) result) (.app (weakenCtx Γ successor) first))) :
    ProofSyntax Const assumptions .bot := by
  have witness := sumLeftSuccessor successor zero first offset result present
  apply ProofSyntax.exE witness
  let body : Formula Const (number :: Γ) :=
    .and (.eq (weaken result) (.app (weakenCtx _ successor) (.var .vz)))
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken offset)) (.var .vz))
  let hypotheses := body :: weakenHyps assumptions
  have given : ProofSyntax Const hypotheses body := .hyp 0
  have bound' : ProofSyntax Const hypotheses (sumBoundBody successor zero (weaken first) (weaken offset)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken bound).prepend body)
    exact sumBoundBody_rename successor zero Rename.weaken first offset
  have injective' : ProofSyntax Const hypotheses (NaturalNumeralProofs.injectivity (weakenCtx (number :: Γ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken injective).prepend body)
    simp only [NaturalNumeralProofs.injectivity, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
  have smaller' : ProofSyntax Const hypotheses
      (.app (.app (weakenCtx _ (less successor)) (weaken result)) (.app (weakenCtx _ successor) (weaken first))) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken smaller).prepend body)
    simp only [HOL.rename, weaken, rename_weakenCtx]
  have atSuccessor : ProofSyntax Const hypotheses (.app (.app (weakenCtx _ (less successor))
      (.app (weakenCtx _ successor) (.var .vz))) (.app (weakenCtx _ successor) (weaken first))) :=
    .impE (.eqPropEL (.eqApp (.app (weakenCtx _ successor) (weaken first))
      (.eqAppArg (weakenCtx _ (less successor)) (.andEL given)))) smaller'
  have previousLess := lessSuccessorCancel successor (.var .vz) (weaken first) injective' atSuccessor
  exact .notE (.impE (sumBoundAt successor zero (weaken first) (weaken offset) (.var .vz) bound') (.andER given)) previousLess

theorem sumBoundSuccessorRefute_free {assumptions : List (Formula Const Γ)} (first offset result : Term Const Γ number)
    (bound : ProofSyntax Const assumptions (sumBoundBody successor zero first offset))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) (.app (weakenCtx Γ successor) first)) offset) result))
    (smaller : ProofSyntax Const assumptions
      (.app (.app (weakenCtx Γ (less successor)) result) (.app (weakenCtx Γ successor) first)))
    (boundFree : bound.FunctionExtensionalityFree) (injectiveFree : injective.FunctionExtensionalityFree)
    (presentFree : present.FunctionExtensionalityFree) (smallerFree : smaller.FunctionExtensionalityFree) :
    (sumBoundSuccessorRefute successor zero first offset result bound injective present smaller).FunctionExtensionalityFree := by
  unfold sumBoundSuccessorRefute
  refine ⟨sumLeftSuccessor_free _ _ _ _ _ _ presentFree, ?_⟩
  constructor
  · constructor
    · apply sumBoundAt_free
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr boundFree
    · trivial
  · apply lessSuccessorCancel_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr injectiveFree
    · constructor
      · trivial
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr smallerFree

def sumBoundStep {assumptions : List (Formula Const Γ)} (first offset : Term Const Γ number)
    (bound : ProofSyntax Const assumptions (sumBoundBody successor zero first offset))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor))) :
    ProofSyntax Const assumptions (sumBoundBody successor zero (.app (weakenCtx Γ successor) first) offset) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.notI
  let result : Term Const (number :: Γ) number := .var .vz
  let first' : Term Const (number :: Γ) number := weaken first
  let offset' : Term Const (number :: Γ) number := weaken offset
  let sumClaim := Term.app (.app (.app (weakenCtx _ (sum zero successor))
    (.app (weakenCtx _ successor) first')) offset') result
  let lessClaim := Term.app (.app (weakenCtx _ (less successor)) result) (.app (weakenCtx _ successor) first')
  let hypotheses := lessClaim :: sumClaim :: weakenHyps assumptions
  have bound' : ProofSyntax Const hypotheses (sumBoundBody successor zero first' offset') := by
    apply ProofSyntax.castIndices rfl ?_
      (((ProofSyntax.rename Rename.weaken bound).prepend sumClaim).prepend lessClaim)
    exact sumBoundBody_rename successor zero Rename.weaken first offset
  have injective' : ProofSyntax Const hypotheses (NaturalNumeralProofs.injectivity (weakenCtx (number :: Γ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_
      (((ProofSyntax.rename Rename.weaken injective).prepend sumClaim).prepend lessClaim)
    simp only [NaturalNumeralProofs.injectivity, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
  apply ProofSyntax.castIndices ?_ rfl
    (sumBoundSuccessorRefute successor zero first' offset' result bound' injective' (.hyp 1) (.hyp 0))
  simp only [hypotheses, sumClaim, lessClaim, first', offset', result, weaken, HOL.rename, rename_weakenCtx]

theorem sumBoundStep_free {assumptions : List (Formula Const Γ)} (first offset : Term Const Γ number)
    (bound : ProofSyntax Const assumptions (sumBoundBody successor zero first offset))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (boundFree : bound.FunctionExtensionalityFree) (injectiveFree : injective.FunctionExtensionalityFree) :
    (sumBoundStep successor zero first offset bound injective).FunctionExtensionalityFree := by
  unfold sumBoundStep
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply sumBoundSuccessorRefute_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr boundFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr injectiveFree
  · trivial
  · trivial

def sumBound {assumptions : List (Formula Const Γ)} (first offset : Term Const Γ number)
    (separate : ProofSyntax Const assumptions
      (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const assumptions (sumBoundBody successor zero first offset) := by
  let predicate := sumBoundProgram successor zero offset
  have start : ProofSyntax Const assumptions (.app predicate (weakenCtx Γ zero)) :=
    .impE (.eqPropER (sumBoundProgram_beta successor zero (weakenCtx Γ zero) offset))
      (sumBoundBase successor zero offset separate)
  have closed : ProofSyntax Const assumptions (successorClosed successor predicate) := by
    apply ProofSyntax.allI
    apply ProofSyntax.impI
    let first' : Term Const (number :: Γ) number := .var .vz
    let antecedent := Term.app (weaken predicate) first'
    let hypotheses := antecedent :: weakenHyps assumptions
    have given : ProofSyntax Const hypotheses (.app (sumBoundProgram successor zero (weaken offset)) first') := by
      apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
      change antecedent = _
      simp only [antecedent, predicate, weaken, sumBoundProgram_rename]
    have previous := ProofSyntax.impE (.eqPropEL (sumBoundProgram_beta successor zero first' (weaken offset))) given
    have law : ProofSyntax Const hypotheses (NaturalNumeralProofs.injectivity (weakenCtx (number :: Γ) successor)) := by
      apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken injective).prepend antecedent)
      simp only [NaturalNumeralProofs.injectivity, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
    have next := sumBoundStep successor zero first' (weaken offset) previous law
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.impE (.eqPropER (sumBoundProgram_beta successor zero
        (.app (weakenCtx _ successor) first') (weaken offset))) next)
    simp only [predicate, weaken, sumBoundProgram_rename]
    rfl
  exact .impE (.eqPropEL (sumBoundProgram_beta successor zero first offset))
    (inductionAt successor zero predicate first principle start closed)

theorem sumBound_free {assumptions : List (Formula Const Γ)} (first offset : Term Const Γ number)
    (separate : ProofSyntax Const assumptions
      (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (separateFree : separate.FunctionExtensionalityFree) (injectiveFree : injective.FunctionExtensionalityFree)
    (principleFree : principle.FunctionExtensionalityFree) :
    (sumBound successor zero first offset separate injective principle).FunctionExtensionalityFree := by
  unfold sumBound
  refine ⟨sumBoundProgram_beta_free _ _ _ _, ?_⟩
  apply inductionAt_free
  · exact principleFree
  · exact ⟨sumBoundProgram_beta_free _ _ _ _, sumBoundBase_free _ _ _ _ separateFree⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    constructor
    · exact sumBoundProgram_beta_free _ _ _ _
    · apply sumBoundStep_free
      · constructor
        · exact sumBoundProgram_beta_free _ _ _ _
        · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
          trivial
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr injectiveFree

#print axioms inductionAt_free
#print axioms sumBoundBase
#print axioms sumBoundSuccessorRefute
#print axioms sumBoundSuccessorRefute_free
#print axioms sumBoundStep_free
#print axioms sumBound
#print axioms sumBound_free

def sumUniqueBody (first leftOffset rightOffset : Term Const Γ number) : Formula Const Γ :=
  .all (.imp (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken leftOffset)) (.var .vz))
    (.imp (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken rightOffset)) (.var .vz))
      (.eq (weaken leftOffset) (weaken rightOffset))))

theorem sumUniqueBody_subst (images : Subst Const Γ Ξ) (first leftOffset rightOffset : Term Const Γ number) :
    HOL.subst images (sumUniqueBody successor zero first leftOffset rightOffset) =
      sumUniqueBody successor zero (HOL.subst images first) (HOL.subst images leftOffset) (HOL.subst images rightOffset) := by
  simp only [sumUniqueBody, HOL.subst, subst_weakenCtx, subst_weaken, Subst.lift]

theorem sumUniqueBody_rename (images : Rename Base Γ Ξ) (first leftOffset rightOffset : Term Const Γ number) :
    HOL.rename images (sumUniqueBody successor zero first leftOffset rightOffset) =
      sumUniqueBody successor zero (HOL.rename images first) (HOL.rename images leftOffset) (HOL.rename images rightOffset) := by
  simp only [sumUniqueBody, HOL.rename, rename_weakenCtx, ExtDerivation.rename_weaken, Rename.lift]

def sumUniqueProgram (leftOffset rightOffset : Term Const Γ number) : Term Const Γ (number ⇒ .prop) :=
  .lam (sumUniqueBody successor zero (.var .vz) (weaken leftOffset) (weaken rightOffset))

theorem sumUniqueProgram_rename (images : Rename Base Γ Ξ) (leftOffset rightOffset : Term Const Γ number) :
    HOL.rename images (sumUniqueProgram successor zero leftOffset rightOffset) =
      sumUniqueProgram successor zero (HOL.rename images leftOffset) (HOL.rename images rightOffset) := by
  simp only [sumUniqueProgram, HOL.rename, sumUniqueBody_rename, ExtDerivation.rename_weaken, Rename.lift]

def sumUniqueProgram_beta {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (sumUniqueProgram successor zero leftOffset rightOffset) first)
      (sumUniqueBody successor zero first leftOffset rightOffset)) := by
  apply ProofSyntax.castIndices rfl ?_
    (.beta first (sumUniqueBody successor zero (.var .vz) (weaken leftOffset) (weaken rightOffset)))
  simp only [instantiate, sumUniqueBody_subst, HOL.subst, Subst.single, PredicateFixedPoint.subst_single_weaken]
  rfl

theorem sumUniqueProgram_beta_free {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset : Term Const Γ number) :
    (sumUniqueProgram_beta successor zero (assumptions := assumptions) first leftOffset rightOffset).FunctionExtensionalityFree := by
  unfold sumUniqueProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def sumUniqueAt {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset result : Term Const Γ number)
    (unique : ProofSyntax Const assumptions (sumUniqueBody successor zero first leftOffset rightOffset)) :
    ProofSyntax Const assumptions (.imp
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) leftOffset) result)
      (.imp (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) rightOffset) result)
        (.eq leftOffset rightOffset))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE result unique)
  simp only [instantiate, HOL.subst, Subst.single, subst_weakenCtx, PredicateFixedPoint.subst_single_weaken]

theorem sumUniqueAt_free {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset result : Term Const Γ number)
    (unique : ProofSyntax Const assumptions (sumUniqueBody successor zero first leftOffset rightOffset))
    (free : unique.FunctionExtensionalityFree) :
    (sumUniqueAt successor zero first leftOffset rightOffset result unique).FunctionExtensionalityFree := by
  unfold sumUniqueAt
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

def sumUniqueBase {assumptions : List (Formula Const Γ)} (leftOffset rightOffset : Term Const Γ number) :
    ProofSyntax Const assumptions (sumUniqueBody successor zero (weakenCtx Γ zero) leftOffset rightOffset) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.impI
  let result : Term Const (number :: Γ) number := .var .vz
  let leftClaim := Term.app (.app (.app (weakenCtx _ (sum zero successor)) (weakenCtx _ zero)) (weaken leftOffset)) result
  let rightClaim := Term.app (.app (.app (weakenCtx _ (sum zero successor)) (weakenCtx _ zero)) (weaken rightOffset)) result
  have left : ProofSyntax Const (rightClaim :: leftClaim :: weakenHyps assumptions) leftClaim := .hyp 1
  have right : ProofSyntax Const (rightClaim :: leftClaim :: weakenHyps assumptions) rightClaim := .hyp 0
  exact .eqTrans (sumZeroReflect successor zero (weaken leftOffset) result left)
    (.eqSymm (sumZeroReflect successor zero (weaken rightOffset) result right))

theorem sumUniqueBase_free {assumptions : List (Formula Const Γ)} (leftOffset rightOffset : Term Const Γ number) :
    (sumUniqueBase successor zero (assumptions := assumptions) leftOffset rightOffset).FunctionExtensionalityFree := by
  unfold sumUniqueBase
  constructor
  · apply sumZeroReflect_free
    trivial
  · apply sumZeroReflect_free
    trivial

#print axioms sumUniqueBase_free

def sumUniqueSuccessorPoint {assumptions : List (Formula Const Γ)}
    (first leftOffset rightOffset result : Term Const Γ number)
    (unique : ProofSyntax Const assumptions (sumUniqueBody successor zero first leftOffset rightOffset))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (left : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor))
      (.app (weakenCtx Γ successor) first)) leftOffset) result))
    (right : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor))
      (.app (weakenCtx Γ successor) first)) rightOffset) result)) :
    ProofSyntax Const assumptions (.eq leftOffset rightOffset) := by
  have leftWitness := sumLeftSuccessor successor zero first leftOffset result left
  apply ProofSyntax.exE leftWitness
  let leftBody : Formula Const (number :: Γ) :=
    .and (.eq (weaken result) (.app (weakenCtx _ successor) (.var .vz)))
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken leftOffset)) (.var .vz))
  let leftHypotheses := leftBody :: weakenHyps assumptions
  have leftGiven : ProofSyntax Const leftHypotheses leftBody := .hyp 0
  have right' : ProofSyntax Const leftHypotheses (.app (.app (.app (weakenCtx _ (sum zero successor))
      (.app (weakenCtx _ successor) (weaken first))) (weaken rightOffset)) (weaken result)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken right).prepend leftBody)
    simp only [HOL.rename, weaken, rename_weakenCtx]
  have unique' : ProofSyntax Const leftHypotheses
      (sumUniqueBody successor zero (weaken first) (weaken leftOffset) (weaken rightOffset)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken unique).prepend leftBody)
    exact sumUniqueBody_rename successor zero Rename.weaken first leftOffset rightOffset
  have injective' : ProofSyntax Const leftHypotheses
      (NaturalNumeralProofs.injectivity (weakenCtx (number :: Γ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken injective).prepend leftBody)
    simp only [NaturalNumeralProofs.injectivity, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
  have rightWitness := sumLeftSuccessor successor zero (weaken first) (weaken rightOffset) (weaken result) right'
  apply ProofSyntax.exE rightWitness
  let rightBody : Formula Const (number :: number :: Γ) :=
    .and (.eq (weaken (weaken result)) (.app (weakenCtx _ successor) (.var .vz)))
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (weaken first)))
        (weaken (weaken rightOffset))) (.var .vz))
  let hypotheses := rightBody :: weakenHyps leftHypotheses
  have rightGiven : ProofSyntax Const hypotheses rightBody := .hyp 0
  have leftGiven' : ProofSyntax Const hypotheses
      (.and (.eq (weaken (weaken result)) (.app (weakenCtx _ successor) (.var (.vs .vz))))
        (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (weaken first)))
          (weaken (weaken leftOffset))) (.var (.vs .vz)))) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken leftGiven).prepend rightBody)
    simp only [leftBody, HOL.rename, rename_weakenCtx, Rename.weaken, weaken]
  have unique'' : ProofSyntax Const hypotheses
      (sumUniqueBody successor zero (weaken (weaken first)) (weaken (weaken leftOffset))
        (weaken (weaken rightOffset))) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken unique').prepend rightBody)
    exact sumUniqueBody_rename successor zero Rename.weaken (weaken first) (weaken leftOffset) (weaken rightOffset)
  have injective'' : ProofSyntax Const hypotheses
      (NaturalNumeralProofs.injectivity (weakenCtx (number :: number :: Γ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken injective').prepend rightBody)
    simp only [NaturalNumeralProofs.injectivity, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
  have samePredecessor : ProofSyntax Const hypotheses (.eq (.var (.vs .vz)) (.var .vz)) :=
    .impE (.eqPropEL (NaturalNumeralProofs.successorEquality (weakenCtx _ successor)
      (.var (.vs .vz)) (.var .vz) injective''))
      (.eqTrans (.eqSymm (.andEL leftGiven')) (.andEL rightGiven))
  have rightAtLeft : ProofSyntax Const hypotheses
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken (weaken first)))
        (weaken (weaken rightOffset))) (.var (.vs .vz))) :=
    .impE (.eqPropER (.eqAppArg (.app (.app (weakenCtx _ (sum zero successor)) (weaken (weaken first)))
      (weaken (weaken rightOffset))) samePredecessor)) (.andER rightGiven)
  exact .impE (.impE (sumUniqueAt successor zero (weaken (weaken first)) (weaken (weaken leftOffset))
    (weaken (weaken rightOffset)) (.var (.vs .vz)) unique'') (.andER leftGiven')) rightAtLeft

theorem sumUniqueSuccessorPoint_free {assumptions : List (Formula Const Γ)}
    (first leftOffset rightOffset result : Term Const Γ number)
    (unique : ProofSyntax Const assumptions (sumUniqueBody successor zero first leftOffset rightOffset))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (left : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor))
      (.app (weakenCtx Γ successor) first)) leftOffset) result))
    (right : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor))
      (.app (weakenCtx Γ successor) first)) rightOffset) result))
    (uniqueFree : unique.FunctionExtensionalityFree) (injectiveFree : injective.FunctionExtensionalityFree)
    (leftFree : left.FunctionExtensionalityFree) (rightFree : right.FunctionExtensionalityFree) :
    (sumUniqueSuccessorPoint successor zero first leftOffset rightOffset result unique injective left right).FunctionExtensionalityFree := by
  unfold sumUniqueSuccessorPoint
  refine ⟨sumLeftSuccessor_free _ _ _ _ _ _ leftFree, ?_⟩
  constructor
  · apply sumLeftSuccessor_free
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr rightFree
  · constructor
    · constructor
      · apply sumUniqueAt_free
        apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        apply (ProofSyntax.functionExtensionalityFree_rename _ _).mpr
        apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr uniqueFree
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr True.intro
    · constructor
      · constructor
        · apply NaturalNumeralProofs.successorEquality_free
          apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
          apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
          apply (ProofSyntax.functionExtensionalityFree_rename _ _).mpr
          apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
          apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
          exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr injectiveFree
        · constructor
          · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
            apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
            exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr True.intro
          · trivial
      · trivial

#print axioms sumUniqueSuccessorPoint
#print axioms sumUniqueSuccessorPoint_free

def sumUniqueStep {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset : Term Const Γ number)
    (unique : ProofSyntax Const assumptions (sumUniqueBody successor zero first leftOffset rightOffset))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor))) :
    ProofSyntax Const assumptions (sumUniqueBody successor zero (.app (weakenCtx Γ successor) first)
      leftOffset rightOffset) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.impI
  let result : Term Const (number :: Γ) number := .var .vz
  let first' : Term Const (number :: Γ) number := weaken first
  let leftOffset' : Term Const (number :: Γ) number := weaken leftOffset
  let rightOffset' : Term Const (number :: Γ) number := weaken rightOffset
  let leftClaim := Term.app (.app (.app (weakenCtx _ (sum zero successor))
    (.app (weakenCtx _ successor) first')) leftOffset') result
  let rightClaim := Term.app (.app (.app (weakenCtx _ (sum zero successor))
    (.app (weakenCtx _ successor) first')) rightOffset') result
  let hypotheses := rightClaim :: leftClaim :: weakenHyps assumptions
  have unique' : ProofSyntax Const hypotheses (sumUniqueBody successor zero first' leftOffset' rightOffset') := by
    apply ProofSyntax.castIndices rfl ?_
      (((ProofSyntax.rename Rename.weaken unique).prepend leftClaim).prepend rightClaim)
    exact sumUniqueBody_rename successor zero Rename.weaken first leftOffset rightOffset
  have injective' : ProofSyntax Const hypotheses
      (NaturalNumeralProofs.injectivity (weakenCtx (number :: Γ) successor)) := by
    apply ProofSyntax.castIndices rfl ?_
      (((ProofSyntax.rename Rename.weaken injective).prepend leftClaim).prepend rightClaim)
    simp only [NaturalNumeralProofs.injectivity, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
  apply ProofSyntax.castIndices ?_ rfl
    (sumUniqueSuccessorPoint successor zero first' leftOffset' rightOffset' result unique' injective' (.hyp 1) (.hyp 0))
  simp only [hypotheses, leftClaim, rightClaim, first', leftOffset', rightOffset', result,
    weaken, HOL.rename, rename_weakenCtx]

theorem sumUniqueStep_free {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset : Term Const Γ number)
    (unique : ProofSyntax Const assumptions (sumUniqueBody successor zero first leftOffset rightOffset))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (uniqueFree : unique.FunctionExtensionalityFree) (injectiveFree : injective.FunctionExtensionalityFree) :
    (sumUniqueStep successor zero first leftOffset rightOffset unique injective).FunctionExtensionalityFree := by
  unfold sumUniqueStep
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply sumUniqueSuccessorPoint_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr uniqueFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr injectiveFree
  · trivial
  · trivial

def sumUnique {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset : Term Const Γ number)
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const assumptions (sumUniqueBody successor zero first leftOffset rightOffset) := by
  let predicate := sumUniqueProgram successor zero leftOffset rightOffset
  have start : ProofSyntax Const assumptions (.app predicate (weakenCtx Γ zero)) :=
    .impE (.eqPropER (sumUniqueProgram_beta successor zero (weakenCtx Γ zero) leftOffset rightOffset))
      (sumUniqueBase successor zero leftOffset rightOffset)
  have closed : ProofSyntax Const assumptions (successorClosed successor predicate) := by
    apply ProofSyntax.allI
    apply ProofSyntax.impI
    let first' : Term Const (number :: Γ) number := .var .vz
    let antecedent := Term.app (weaken predicate) first'
    let hypotheses := antecedent :: weakenHyps assumptions
    have given : ProofSyntax Const hypotheses
        (.app (sumUniqueProgram successor zero (weaken leftOffset) (weaken rightOffset)) first') := by
      apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
      change antecedent = _
      simp only [antecedent, predicate, weaken, sumUniqueProgram_rename]
    have previous := ProofSyntax.impE
      (.eqPropEL (sumUniqueProgram_beta successor zero first' (weaken leftOffset) (weaken rightOffset))) given
    have law : ProofSyntax Const hypotheses (NaturalNumeralProofs.injectivity (weakenCtx (number :: Γ) successor)) := by
      apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken injective).prepend antecedent)
      simp only [NaturalNumeralProofs.injectivity, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
    have next := sumUniqueStep successor zero first' (weaken leftOffset) (weaken rightOffset) previous law
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.impE (.eqPropER (sumUniqueProgram_beta successor zero
        (.app (weakenCtx _ successor) first') (weaken leftOffset) (weaken rightOffset))) next)
    simp only [predicate, weaken, sumUniqueProgram_rename]
    rfl
  exact .impE (.eqPropEL (sumUniqueProgram_beta successor zero first leftOffset rightOffset))
    (inductionAt successor zero predicate first principle start closed)

theorem sumUnique_free {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset : Term Const Γ number)
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (injectiveFree : injective.FunctionExtensionalityFree) (principleFree : principle.FunctionExtensionalityFree) :
    (sumUnique successor zero first leftOffset rightOffset injective principle).FunctionExtensionalityFree := by
  unfold sumUnique
  refine ⟨sumUniqueProgram_beta_free _ _ _ _ _, ?_⟩
  apply inductionAt_free
  · exact principleFree
  · exact ⟨sumUniqueProgram_beta_free _ _ _ _ _, sumUniqueBase_free _ _ _ _⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    constructor
    · exact sumUniqueProgram_beta_free _ _ _ _ _
    · apply sumUniqueStep_free
      · constructor
        · exact sumUniqueProgram_beta_free _ _ _ _ _
        · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
          trivial
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr injectiveFree

def sumExcludesLeft {assumptions : List (Formula Const Γ)} (first offset result : Term Const Γ number)
    (separate : ProofSyntax Const assumptions
      (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) offset) result)) :
    ProofSyntax Const assumptions (.not (.app (.app (weakenCtx Γ (less successor)) result) first)) :=
  .impE (sumBoundAt successor zero first offset result (sumBound successor zero first offset separate injective principle)) present

theorem sumExcludesLeft_free {assumptions : List (Formula Const Γ)} (first offset result : Term Const Γ number)
    (separate : ProofSyntax Const assumptions
      (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) offset) result))
    (separateFree : separate.FunctionExtensionalityFree) (injectiveFree : injective.FunctionExtensionalityFree)
    (principleFree : principle.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (sumExcludesLeft successor zero first offset result separate injective principle present).FunctionExtensionalityFree := by
  constructor
  · apply sumBoundAt_free
    exact sumBound_free _ _ _ _ _ _ _ separateFree injectiveFree principleFree
  · exact presentFree

def sumOffsetUnique {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset result : Term Const Γ number)
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (left : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) leftOffset) result))
    (right : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) rightOffset) result)) :
    ProofSyntax Const assumptions (.eq leftOffset rightOffset) :=
  .impE (.impE (sumUniqueAt successor zero first leftOffset rightOffset result
    (sumUnique successor zero first leftOffset rightOffset injective principle)) left) right

theorem sumOffsetUnique_free {assumptions : List (Formula Const Γ)} (first leftOffset rightOffset result : Term Const Γ number)
    (injective : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor)))
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (left : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) leftOffset) result))
    (right : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) rightOffset) result))
    (injectiveFree : injective.FunctionExtensionalityFree) (principleFree : principle.FunctionExtensionalityFree)
    (leftFree : left.FunctionExtensionalityFree) (rightFree : right.FunctionExtensionalityFree) :
    (sumOffsetUnique successor zero first leftOffset rightOffset result injective principle left right).FunctionExtensionalityFree := by
  refine ⟨⟨?_, leftFree⟩, rightFree⟩
  apply sumUniqueAt_free
  exact sumUnique_free _ _ _ _ _ _ _ injectiveFree principleFree

#print axioms sumUnique
#print axioms sumUnique_free
#print axioms sumExcludesLeft
#print axioms sumExcludesLeft_free
#print axioms sumOffsetUnique
#print axioms sumOffsetUnique_free

/-- Retained arithmetic inputs shared by recursive position proofs. -/
structure PeanoEvidence (assumptions : List (Formula Const Γ)) where
  separation : ProofSyntax Const assumptions
    (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor))
  injectivity : ProofSyntax Const assumptions (NaturalNumeralProofs.injectivity (weakenCtx Γ successor))
  induction : ProofSyntax Const assumptions
    (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))

namespace PeanoEvidence
variable {successor zero} {assumptions : List (Formula Const Γ)}

def Free (evidence : PeanoEvidence successor zero assumptions) : Prop :=
  evidence.separation.FunctionExtensionalityFree ∧ evidence.injectivity.FunctionExtensionalityFree ∧
    evidence.induction.FunctionExtensionalityFree

def prepend (evidence : PeanoEvidence successor zero assumptions) (formula : Formula Const Γ) :
    PeanoEvidence successor zero (formula :: assumptions) where
  separation := evidence.separation.prepend formula
  injectivity := evidence.injectivity.prepend formula
  induction := evidence.induction.prepend formula

theorem prepend_free (evidence : PeanoEvidence successor zero assumptions) (formula : Formula Const Γ)
    (free : evidence.Free) : (evidence.prepend formula).Free := by
  exact ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr free.1,
    (ProofSyntax.functionExtensionalityFree_mono _ _).mpr free.2.1,
    (ProofSyntax.functionExtensionalityFree_mono _ _).mpr free.2.2⟩

def rename (evidence : PeanoEvidence successor zero assumptions) (images : Rename Base Γ Ξ) :
    PeanoEvidence successor zero (assumptions.map (HOL.rename images)) where
  separation := ProofSyntax.castIndices rfl (by
    simp only [NaturalNumeralProofs.separation, HOL.rename, Rename.lift, ExtDerivation.rename_weaken, rename_weakenCtx])
      (ProofSyntax.rename images evidence.separation)
  injectivity := ProofSyntax.castIndices rfl (by
    simp only [NaturalNumeralProofs.injectivity, HOL.rename, Rename.lift, ExtDerivation.rename_weaken, rename_weakenCtx])
      (ProofSyntax.rename images evidence.injectivity)
  induction := ProofSyntax.castIndices rfl (by
    simp only [NaturalRecursionProofs.inductionPrinciple, HOL.rename, Rename.lift,
      ExtDerivation.rename_weaken, rename_weakenCtx]) (ProofSyntax.rename images evidence.induction)

theorem rename_free (evidence : PeanoEvidence successor zero assumptions) (images : Rename Base Γ Ξ)
    (free : evidence.Free) : (evidence.rename images).Free := by
  simpa only [Free, rename, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free

end PeanoEvidence

#print axioms PeanoEvidence.rename_free

end Mettapedia.Logic.HOL.SuccessorOrder
