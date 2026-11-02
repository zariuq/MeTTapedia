import Mettapedia.Logic.HOL.SuccessorOrderArithmetic

/-!
# Constructing prefix-sum witnesses

The zero-start diagonal follows from the retained induction principle.
The general existence construction keeps the output existential, so dynamic
prefixes need no additional arithmetic constant or chosen output operation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
    (successor : ClosedTerm Const (number ⇒ number)) (zero : ClosedTerm Const number)

def diagonalSumProgram : Term Const Γ (number ⇒ .prop) :=
  .lam (.app (.app (.app (weakenCtx _ (sum zero successor)) (weakenCtx _ zero)) (.var .vz)) (.var .vz))

theorem diagonalSumProgram_rename (images : Rename Base Γ Ξ) :
    HOL.rename images (diagonalSumProgram (Γ := Γ) successor zero) = diagonalSumProgram successor zero := by
  simp only [diagonalSumProgram, HOL.rename, rename_weakenCtx, Rename.lift]

def diagonalSumProgram_beta {assumptions : List (Formula Const Γ)} (point : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (diagonalSumProgram successor zero) point)
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) (weakenCtx Γ zero)) point) point)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta point
    (.app (.app (.app (weakenCtx _ (sum zero successor)) (weakenCtx _ zero)) (.var .vz)) (.var .vz)))
  simp only [instantiate, HOL.subst, Subst.single, subst_weakenCtx]
  rfl

theorem diagonalSumProgram_beta_free {assumptions : List (Formula Const Γ)} (point : Term Const Γ number) :
    (diagonalSumProgram_beta successor zero (assumptions := assumptions) point).FunctionExtensionalityFree := by
  unfold diagonalSumProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def sumZeroLeft {assumptions : List (Formula Const Γ)} (point : Term Const Γ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) (weakenCtx Γ zero)) point) point) := by
  let predicate : Term Const Γ (number ⇒ .prop) := diagonalSumProgram successor zero
  have start : ProofSyntax Const assumptions (.app predicate (weakenCtx Γ zero)) :=
    .impE (.eqPropER (diagonalSumProgram_beta successor zero (weakenCtx Γ zero)))
      (sumZero successor zero (weakenCtx Γ zero))
  have closed : ProofSyntax Const assumptions (successorClosed successor predicate) := by
    apply ProofSyntax.allI
    apply ProofSyntax.impI
    let point' : Term Const (number :: Γ) number := .var .vz
    let antecedent := Term.app (weaken predicate) point'
    let hypotheses := antecedent :: weakenHyps assumptions
    have given : ProofSyntax Const hypotheses (.app (diagonalSumProgram successor zero) point') := by
      apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
      change antecedent = _
      simp only [antecedent, predicate, weaken, diagonalSumProgram_rename]
    have previous := ProofSyntax.impE (.eqPropEL (diagonalSumProgram_beta successor zero point')) given
    have next := sumStep successor zero (weakenCtx _ zero) point' point' previous
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.impE (.eqPropER (diagonalSumProgram_beta successor zero
        (.app (weakenCtx _ successor) point'))) next)
    simp only [predicate, weaken, diagonalSumProgram_rename]
    rfl
  exact .impE (.eqPropEL (diagonalSumProgram_beta successor zero point))
    (inductionAt successor zero predicate point principle start closed)

theorem sumZeroLeft_free {assumptions : List (Formula Const Γ)} (point : Term Const Γ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) :
    (sumZeroLeft successor zero point principle).FunctionExtensionalityFree := by
  unfold sumZeroLeft
  refine ⟨diagonalSumProgram_beta_free _ _ _, ?_⟩
  apply inductionAt_free
  · exact free
  · exact ⟨diagonalSumProgram_beta_free _ _ _, sumZero_free _ _ _⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    constructor
    · exact diagonalSumProgram_beta_free _ _ _
    · apply sumStep_free
      constructor
      · exact diagonalSumProgram_beta_free _ _ _
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial

def sumExists (first count : Term Const Γ number) : Formula Const Γ :=
  .ex (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken count)) (.var .vz))

theorem sumExists_subst (images : Subst Const Γ Ξ) (first count : Term Const Γ number) :
    HOL.subst images (sumExists successor zero first count) =
      sumExists successor zero (HOL.subst images first) (HOL.subst images count) := by
  simp only [sumExists, HOL.subst, subst_weakenCtx, subst_weaken, Subst.lift]

theorem sumExists_rename (images : Rename Base Γ Ξ) (first count : Term Const Γ number) :
    HOL.rename images (sumExists successor zero first count) =
      sumExists successor zero (HOL.rename images first) (HOL.rename images count) := by
  simp only [sumExists, HOL.rename, rename_weakenCtx, ExtDerivation.rename_weaken, Rename.lift]

def sumExistsProgram (first : Term Const Γ number) : Term Const Γ (number ⇒ .prop) :=
  .lam (sumExists successor zero (weaken first) (.var .vz))

theorem sumExistsProgram_rename (images : Rename Base Γ Ξ) (first : Term Const Γ number) :
    HOL.rename images (sumExistsProgram successor zero first) =
      sumExistsProgram successor zero (HOL.rename images first) := by
  simp only [sumExistsProgram, HOL.rename, sumExists_rename, ExtDerivation.rename_weaken, Rename.lift]

def sumExistsProgram_beta {assumptions : List (Formula Const Γ)} (first count : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (sumExistsProgram successor zero first) count)
      (sumExists successor zero first count)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta count (sumExists successor zero (weaken first) (.var .vz)))
  simp only [instantiate, sumExists_subst, HOL.subst, Subst.single, PredicateFixedPoint.subst_single_weaken]
  rfl

theorem sumExistsProgram_beta_free {assumptions : List (Formula Const Γ)} (first count : Term Const Γ number) :
    (sumExistsProgram_beta successor zero (assumptions := assumptions) first count).FunctionExtensionalityFree := by
  unfold sumExistsProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def sumExistsIntro {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) result)) :
    ProofSyntax Const assumptions (sumExists successor zero first count) := by
  apply ProofSyntax.exI result
  apply ProofSyntax.castIndices rfl ?_ present
  simp only [instantiate, HOL.subst, Subst.single, subst_weakenCtx, PredicateFixedPoint.subst_single_weaken]

theorem sumExistsIntro_free {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) result))
    (free : present.FunctionExtensionalityFree) :
    (sumExistsIntro successor zero first count result present).FunctionExtensionalityFree := by
  unfold sumExistsIntro
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

def sumExistsStep {assumptions : List (Formula Const Γ)} (first count : Term Const Γ number)
    (present : ProofSyntax Const assumptions (sumExists successor zero first count)) :
    ProofSyntax Const assumptions (sumExists successor zero first (.app (weakenCtx Γ successor) count)) := by
  apply ProofSyntax.exE present
  let body := Term.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken count)) (.var .vz)
  have given : ProofSyntax Const (body :: weakenHyps assumptions) body := .hyp 0
  have next := sumStep successor zero (weaken first) (weaken count) (.var .vz) given
  apply ProofSyntax.castIndices rfl ?_ (sumExistsIntro successor zero (weaken first)
    (.app (weakenCtx _ successor) (weaken count)) (.app (weakenCtx _ successor) (.var .vz)) next)
  simp only [weaken, sumExists_rename, HOL.rename, rename_weakenCtx]

theorem sumExistsStep_free {assumptions : List (Formula Const Γ)} (first count : Term Const Γ number)
    (present : ProofSyntax Const assumptions (sumExists successor zero first count))
    (free : present.FunctionExtensionalityFree) :
    (sumExistsStep successor zero first count present).FunctionExtensionalityFree := by
  unfold sumExistsStep
  refine ⟨free, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply sumExistsIntro_free
  apply sumStep_free
  trivial

def sumTotal {assumptions : List (Formula Const Γ)} (first count : Term Const Γ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const assumptions (sumExists successor zero first count) := by
  let predicate := sumExistsProgram successor zero first
  have start : ProofSyntax Const assumptions (.app predicate (weakenCtx Γ zero)) :=
    .impE (.eqPropER (sumExistsProgram_beta successor zero first (weakenCtx Γ zero)))
      (sumExistsIntro successor zero first (weakenCtx Γ zero) first (sumZero successor zero first))
  have closed : ProofSyntax Const assumptions (successorClosed successor predicate) := by
    apply ProofSyntax.allI
    apply ProofSyntax.impI
    let count' : Term Const (number :: Γ) number := .var .vz
    let antecedent := Term.app (weaken predicate) count'
    let hypotheses := antecedent :: weakenHyps assumptions
    have given : ProofSyntax Const hypotheses (.app (sumExistsProgram successor zero (weaken first)) count') := by
      apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
      change antecedent = _
      simp only [antecedent, predicate, weaken, sumExistsProgram_rename]
    have previous := ProofSyntax.impE (.eqPropEL (sumExistsProgram_beta successor zero (weaken first) count')) given
    have next := sumExistsStep successor zero (weaken first) count' previous
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.impE (.eqPropER (sumExistsProgram_beta successor zero (weaken first)
        (.app (weakenCtx _ successor) count'))) next)
    simp only [predicate, weaken, sumExistsProgram_rename]
    rfl
  exact .impE (.eqPropEL (sumExistsProgram_beta successor zero first count))
    (inductionAt successor zero predicate count principle start closed)

theorem sumTotal_free {assumptions : List (Formula Const Γ)} (first count : Term Const Γ number)
    (principle : ProofSyntax Const assumptions
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) :
    (sumTotal successor zero first count principle).FunctionExtensionalityFree := by
  unfold sumTotal
  refine ⟨sumExistsProgram_beta_free _ _ _ _, ?_⟩
  apply inductionAt_free
  · exact free
  · constructor
    · exact sumExistsProgram_beta_free _ _ _ _
    · apply sumExistsIntro_free
      exact sumZero_free _ _ _
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    constructor
    · exact sumExistsProgram_beta_free _ _ _ _
    · apply sumExistsStep_free
      constructor
      · exact sumExistsProgram_beta_free _ _ _ _
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial

#print axioms sumZeroLeft
#print axioms sumZeroLeft_free
#print axioms sumTotal
#print axioms sumTotal_free

def advanceResult (predicate : Term Const Γ (number ⇒ number ⇒ .prop)) :
    Term Const Γ (number ⇒ number ⇒ .prop) :=
  .lam (.lam (.app (.app (weaken (weaken predicate)) (.var (.vs .vz)))
    (.app (weakenCtx _ successor) (.var .vz))))

theorem advanceResult_rename (images : Rename Base Γ Ξ) (predicate : Term Const Γ (number ⇒ number ⇒ .prop)) :
    HOL.rename images (advanceResult successor predicate) = advanceResult successor (HOL.rename images predicate) := by
  simp only [advanceResult, HOL.rename, ExtDerivation.rename_weaken, rename_weakenCtx, Rename.lift]

def advanceResult_beta {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ number ⇒ .prop)) (count result : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (.app (advanceResult successor predicate) count) result)
      (.app (.app predicate count) (.app (weakenCtx Γ successor) result))) := by
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2
    (.app (.app (weaken (weaken predicate)) (.var (.vs .vz)))
      (.app (weakenCtx _ successor) (.var .vz))) count result)
  apply congrArg₂ Term.eq
  · rfl
  · simp only [instantiate, HOL.subst, subst_weaken, Subst.lift, Subst.single, subst_weakenCtx,
      PredicateFixedPoint.subst_single_weaken]
    have cancel : HOL.subst (Subst.single result) (HOL.rename Rename.weaken count) = count :=
      PredicateFixedPoint.subst_single_weaken result count
    rw [cancel]

theorem advanceResult_beta_free {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ number ⇒ .prop)) (count result : Term Const Γ number) :
    (advanceResult_beta successor (assumptions := assumptions) predicate count result).FunctionExtensionalityFree := by
  unfold advanceResult_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

theorem sumClosed_rename (images : Rename Base Γ Ξ) (predicate : Term Const Γ (number ⇒ number ⇒ .prop)) :
    HOL.rename images (sumClosed successor predicate) = sumClosed successor (HOL.rename images predicate) := by
  simpa only [subst_ofRename] using
    (sumClosed_subst successor (Subst.ofRename images) predicate)

def advanceResultClosed {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ number ⇒ .prop))
    (closed : ProofSyntax Const assumptions (sumClosed successor predicate)) :
    ProofSyntax Const assumptions (sumClosed successor (advanceResult successor predicate)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let count : Term Const (number :: number :: Γ) number := .var (.vs .vz)
  let result : Term Const (number :: number :: Γ) number := .var .vz
  let predicate' : Term Const (number :: number :: Γ) (number ⇒ number ⇒ .prop) := weaken (weaken predicate)
  let antecedent := Term.app (.app (weaken (weaken (advanceResult successor predicate))) count) result
  let hypotheses := antecedent :: weakenHyps (weakenHyps assumptions)
  have given : ProofSyntax Const hypotheses (.app (.app (advanceResult successor predicate') count) result) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
    change antecedent = _
    simp only [antecedent, predicate', weaken, advanceResult_rename]
  have previous := ProofSyntax.impE (.eqPropEL (advanceResult_beta successor predicate' count result)) given
  have closed' : ProofSyntax Const hypotheses (sumClosed successor predicate') := by
    apply ProofSyntax.castIndices rfl ?_
      ((ProofSyntax.rename Rename.weaken (ProofSyntax.rename Rename.weaken closed)).prepend antecedent)
    simp only [sumClosed_rename, predicate', weaken]
  have next := ProofSyntax.impE
    (sumClosedAt successor predicate' count (.app (weakenCtx _ successor) result) closed') previous
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.impE
    (.eqPropER (advanceResult_beta successor predicate' (.app (weakenCtx _ successor) count)
      (.app (weakenCtx _ successor) result))) next)
  simp only [predicate', weaken, advanceResult_rename]
  rfl

theorem advanceResultClosed_free {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ number ⇒ .prop))
    (closed : ProofSyntax Const assumptions (sumClosed successor predicate)) (free : closed.FunctionExtensionalityFree) :
    (advanceResultClosed successor predicate closed).FunctionExtensionalityFree := by
  unfold advanceResultClosed
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  constructor
  · exact advanceResult_beta_free _ _ _ _
  · constructor
    · apply sumClosedAt_free
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_rename _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free
    · constructor
      · exact advanceResult_beta_free _ _ _ _
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        trivial

def sumSuccLeft {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) result)) :
    ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor))
      (.app (weakenCtx Γ successor) first)) count) (.app (weakenCtx Γ successor) result)) := by
  apply ProofSyntax.impE (.eqPropER (sum_beta successor zero (.app (weakenCtx Γ successor) first)
    count (.app (weakenCtx Γ successor) result)))
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let predicate : Term Const ((number ⇒ number ⇒ .prop) :: Γ) (number ⇒ number ⇒ .prop) := .var .vz
  let antecedent := Term.and (.app (.app predicate (weakenCtx _ zero))
    (.app (weakenCtx _ successor) (weaken first))) (sumClosed successor predicate)
  let hypotheses := antecedent :: weakenHyps assumptions
  have given : ProofSyntax Const hypotheses antecedent := .hyp 0
  have earlier : ProofSyntax Const hypotheses (.app (.app (.app (weakenCtx _ (sum zero successor))
      (weaken first)) (weaken count)) (weaken result)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken present).prepend antecedent)
    simp only [HOL.rename, weaken, rename_weakenCtx]
  have start : ProofSyntax Const hypotheses (.app (.app (advanceResult successor predicate) (weakenCtx _ zero))
      (weaken first)) :=
    .impE (.eqPropER (advanceResult_beta successor predicate (weakenCtx _ zero) (weaken first))) (.andEL given)
  have selected := sumEliminate successor zero (weaken first) (weaken count) (weaken result)
    (advanceResult successor predicate) earlier start (advanceResultClosed successor predicate (.andER given))
  exact .impE (.eqPropEL (advanceResult_beta successor predicate (weaken count) (weaken result))) selected

theorem sumSuccLeft_free {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions
      (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) result))
    (free : present.FunctionExtensionalityFree) :
    (sumSuccLeft successor zero first count result present).FunctionExtensionalityFree := by
  unfold sumSuccLeft
  refine ⟨sum_beta_free _ _ _ _ _, advanceResult_beta_free _ _ _ _, ?_⟩
  apply sumEliminate_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free
  · exact ⟨advanceResult_beta_free _ _ _ _, trivial⟩
  · apply advanceResultClosed_free
    trivial

#print axioms sumSuccLeft
#print axioms sumSuccLeft_free

end Mettapedia.Logic.HOL.SuccessorOrder
