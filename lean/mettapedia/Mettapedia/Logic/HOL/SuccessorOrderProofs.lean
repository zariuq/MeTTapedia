import Mettapedia.Logic.HOL.SuccessorOrder
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.NaturalNumeralProofs
import Mettapedia.Logic.HOL.NaturalRecursionProofs

/-!
# Retained proofs for the authored successor-closure relations

These programs unfold the existing order and sum terms by explicit beta
steps. Closure elimination consumes retained base and step proofs. Arithmetic
consequences keep their separation, injectivity and induction premises
explicit; semantic natural-number interpretations are not certificates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder

open CurriedGuardProgramProofs
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
    (successor : ClosedTerm Const (number ⇒ number))

def successorClosed (predicate : Term Const Γ (number ⇒ .prop)) : Formula Const Γ :=
  .all (.imp (.app (weaken predicate) (.var .vz))
    (.app (weaken predicate) (.app (weakenCtx _ successor) (.var .vz))))

def lessBody (lower upper : Term Const Γ number) : Formula Const Γ :=
  .all (.imp (.and (.app (.var .vz) (.app (weakenCtx _ successor) (weaken lower)))
    (successorClosed successor (.var .vz))) (.app (.var .vz) (weaken upper)))

private theorem rename_from_empty {type : Ty Base} (term : ClosedTerm Const type)
    (context : Ctx Base) (mapping : Rename Base [] context) :
    HOL.rename mapping term = weakenCtx context term := by
  simpa only [weakenCtx_nil] using rename_weakenCtx mapping term

theorem less_closed_form : weakenCtx Γ (less successor) =
    .lam (.lam (lessBody successor (.var (.vs .vz)) (.var .vz))) := by
  rw [← rename_from_empty (less successor) Γ (fun impossible => nomatch impossible)]
  simp only [less, lessBody, successorClosed, HOL.rename, Rename.lift, Rename.weaken, weaken,
    rename_weakenCtx]

theorem successorClosed_subst (images : Subst Const Γ Ξ) (predicate : Term Const Γ (number ⇒ .prop)) :
    HOL.subst images (successorClosed successor predicate) = successorClosed successor (HOL.subst images predicate) := by
  simp only [successorClosed, HOL.subst, subst_weaken, subst_weakenCtx, Subst.lift]

theorem lessBody_subst (images : Subst Const Γ Ξ) (lower upper : Term Const Γ number) :
    HOL.subst images (lessBody successor lower upper) =
      lessBody successor (HOL.subst images lower) (HOL.subst images upper) := by
  simp only [lessBody, HOL.subst, successorClosed_subst, subst_weaken, subst_weakenCtx, Subst.lift]

def less_beta {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (.app (weakenCtx Γ (less successor)) lower) upper)
      (lessBody successor lower upper)) := by
  apply ProofSyntax.castIndices rfl ?_
    (beta2 (lessBody successor (.var (.vs .vz)) (.var .vz)) lower upper)
  apply congrArg₂ Term.eq
  · rw [less_closed_form]
  · simp only [instantiate, lessBody_subst, HOL.subst, Subst.lift, Subst.single]
    exact congrArg (fun value => lessBody successor value upper) (instantiate_weaken upper lower)

theorem less_beta_free {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number) :
    (less_beta successor (assumptions := assumptions) lower upper).FunctionExtensionalityFree := by
  unfold less_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact beta2_free _ _ _

def lessEliminate {assumptions : List (Formula Const Γ)}
    (lower upper : Term Const Γ number) (predicate : Term Const Γ (number ⇒ .prop))
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower) upper))
    (start : ProofSyntax Const assumptions (.app predicate (.app (weakenCtx Γ successor) lower)))
    (step : ProofSyntax Const assumptions (successorClosed successor predicate)) :
    ProofSyntax Const assumptions (.app predicate upper) := by
  have unfolded := ProofSyntax.impE (.eqPropEL (less_beta successor lower upper)) present
  have specialized := ProofSyntax.allE predicate unfolded
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ specialized) (.andI start step)
  simp only [instantiate, HOL.subst, Subst.single, successorClosed_subst,
    subst_weakenCtx, PredicateFixedPoint.subst_single_weaken]

theorem lessEliminate_free {assumptions : List (Formula Const Γ)}
    (lower upper : Term Const Γ number) (predicate : Term Const Γ (number ⇒ .prop))
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower) upper))
    (start : ProofSyntax Const assumptions (.app predicate (.app (weakenCtx Γ successor) lower)))
    (step : ProofSyntax Const assumptions (successorClosed successor predicate))
    (presentFree : present.FunctionExtensionalityFree) (startFree : start.FunctionExtensionalityFree)
    (stepFree : step.FunctionExtensionalityFree) :
    (lessEliminate successor lower upper predicate present start step).FunctionExtensionalityFree := by
  unfold lessEliminate
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact ⟨less_beta_free _ _ _, presentFree⟩
  · exact ⟨startFree, stepFree⟩

#print axioms less_closed_form
#print axioms lessEliminate_free

def successorClosedAt {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ .prop)) (point : Term Const Γ number)
    (closed : ProofSyntax Const assumptions (successorClosed successor predicate)) :
    ProofSyntax Const assumptions (.imp (.app predicate point)
      (.app predicate (.app (weakenCtx Γ successor) point))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE point closed)
  simp only [instantiate, HOL.subst, Subst.single, subst_weakenCtx,
    PredicateFixedPoint.subst_single_weaken]

def lessNext {assumptions : List (Formula Const Γ)} (lower : Term Const Γ number) :
    ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower)
      (.app (weakenCtx Γ successor) lower)) := by
  apply ProofSyntax.impE (.eqPropER (less_beta successor lower (.app (weakenCtx Γ successor) lower)))
  exact .allI (.impI (.andEL (.hyp 0)))

def lessStep {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number)
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower) upper)) :
    ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower)
      (.app (weakenCtx Γ successor) upper)) := by
  apply ProofSyntax.impE (.eqPropER (less_beta successor lower (.app (weakenCtx Γ successor) upper)))
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let predicate : Term Const ((number ⇒ .prop) :: Γ) (number ⇒ .prop) := .var .vz
  let antecedent := Term.and (.app predicate (.app (weakenCtx _ successor) (weaken lower)))
    (successorClosed successor predicate)
  let hypotheses := antecedent :: weakenHyps assumptions
  let given : ProofSyntax Const hypotheses antecedent := .hyp 0
  have earlier : ProofSyntax Const hypotheses
      (.app (.app (weakenCtx _ (less successor)) (weaken lower)) (weaken upper)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken present).prepend antecedent)
    simp only [HOL.rename, rename_weakenCtx, weaken]
  have atUpper := lessEliminate successor (weaken lower) (weaken upper) predicate
    earlier (.andEL given) (.andER given)
  exact .impE (successorClosedAt successor predicate (weaken upper) (.andER given)) atUpper

variable (zero : ClosedTerm Const number)

def sumClosed (predicate : Term Const Γ (number ⇒ number ⇒ .prop)) : Formula Const Γ :=
  .all (.all (.imp
    (.app (.app (weaken (weaken predicate)) (.var (.vs .vz))) (.var .vz))
    (.app (.app (weaken (weaken predicate)) (.app (weakenCtx _ successor) (.var (.vs .vz))))
      (.app (weakenCtx _ successor) (.var .vz)))))

def sumBody (first count result : Term Const Γ number) : Formula Const Γ :=
  .all (.imp (.and (.app (.app (.var .vz) (weakenCtx _ zero)) (weaken first))
    (sumClosed successor (.var .vz)))
    (.app (.app (.var .vz) (weaken count)) (weaken result)))

theorem sum_closed_form : weakenCtx Γ (sum zero successor) =
    .lam (.lam (.lam (sumBody successor zero (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))) := by
  rw [← rename_from_empty (sum zero successor) Γ (fun impossible => nomatch impossible)]
  simp only [sum, sumBody, sumClosed, HOL.rename, Rename.lift, Rename.weaken, weaken,
    rename_weakenCtx]

theorem sumClosed_subst (images : Subst Const Γ Ξ) (predicate : Term Const Γ (number ⇒ number ⇒ .prop)) :
    HOL.subst images (sumClosed successor predicate) = sumClosed successor (HOL.subst images predicate) := by
  simp only [sumClosed, HOL.subst, subst_weaken, subst_weakenCtx, Subst.lift]
  rfl

theorem sumBody_subst (images : Subst Const Γ Ξ) (first count result : Term Const Γ number) :
    HOL.subst images (sumBody successor zero first count result) =
      sumBody successor zero (HOL.subst images first) (HOL.subst images count) (HOL.subst images result) := by
  simp only [sumBody, HOL.subst, sumClosed_subst, subst_weaken, subst_weakenCtx, Subst.lift]

def sum_beta {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) result)
      (sumBody successor zero first count result)) := by
  apply ProofSyntax.castIndices rfl ?_ (beta3
    (sumBody successor zero (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)) first count result)
  apply congrArg₂ Term.eq
  · rw [sum_closed_form]
  · simp only [instantiate, sumBody_subst, HOL.subst, Subst.lift, Subst.single]
    simp [HOL.subst_rename, HOL.subst_comp, Subst.lift, Subst.single, HOL.rename, Rename.weaken]
    have firstSame : HOL.subst (Subst.comp (Subst.single result) (fun entry => .var (.vs entry))) first = first :=
      ProofSyntax.term_subst_of_identity (fun _ => rfl) first
    have countSame : HOL.subst (fun entry => .var entry) count = count :=
      ProofSyntax.term_subst_of_identity (fun _ => rfl) count
    rw [firstSame, countSame]

theorem sum_beta_free {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number) :
    (sum_beta successor zero (assumptions := assumptions) first count result).FunctionExtensionalityFree := by
  unfold sum_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact beta3_free _ _ _ _

def sumEliminate {assumptions : List (Formula Const Γ)}
    (first count result : Term Const Γ number) (predicate : Term Const Γ (number ⇒ number ⇒ .prop))
    (present : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) result))
    (start : ProofSyntax Const assumptions (.app (.app predicate (weakenCtx Γ zero)) first))
    (step : ProofSyntax Const assumptions (sumClosed successor predicate)) :
    ProofSyntax Const assumptions (.app (.app predicate count) result) := by
  have unfolded := ProofSyntax.impE (.eqPropEL (sum_beta successor zero first count result)) present
  have specialized := ProofSyntax.allE predicate unfolded
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ specialized) (.andI start step)
  simp only [instantiate, HOL.subst, Subst.single, sumClosed_subst,
    subst_weakenCtx, PredicateFixedPoint.subst_single_weaken]

theorem sumEliminate_free {assumptions : List (Formula Const Γ)}
    (first count result : Term Const Γ number) (predicate : Term Const Γ (number ⇒ number ⇒ .prop))
    (present : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) result))
    (start : ProofSyntax Const assumptions (.app (.app predicate (weakenCtx Γ zero)) first))
    (step : ProofSyntax Const assumptions (sumClosed successor predicate))
    (presentFree : present.FunctionExtensionalityFree) (startFree : start.FunctionExtensionalityFree)
    (stepFree : step.FunctionExtensionalityFree) :
    (sumEliminate successor zero first count result predicate present start step).FunctionExtensionalityFree := by
  unfold sumEliminate
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact ⟨sum_beta_free _ _ _ _ _, presentFree⟩
  · exact ⟨startFree, stepFree⟩

def sumZero {assumptions : List (Formula Const Γ)} (first : Term Const Γ number) :
    ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first)
      (weakenCtx Γ zero)) first) := by
  apply ProofSyntax.impE (.eqPropER (sum_beta successor zero first (weakenCtx Γ zero) first))
  exact .allI (.impI (.andEL (.hyp 0)))

#print axioms lessNext
#print axioms lessStep
#print axioms sum_closed_form
#print axioms sumEliminate_free
#print axioms sumZero

def sumClosedAt {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ number ⇒ .prop)) (count value : Term Const Γ number)
    (closed : ProofSyntax Const assumptions (sumClosed successor predicate)) :
    ProofSyntax Const assumptions (.imp (.app (.app predicate count) value)
      (.app (.app predicate (.app (weakenCtx Γ successor) count)) (.app (weakenCtx Γ successor) value))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE value (.allE count closed))
  simp only [instantiate, HOL.subst, Subst.single, Subst.lift, subst_weakenCtx, subst_weaken]
  simp only [PredicateFixedPoint.subst_single_weaken]
  have cancel : HOL.subst (Subst.single value) (HOL.rename Rename.weaken count) = count :=
    PredicateFixedPoint.subst_single_weaken value count
  rw [cancel]

def sumStep {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) result)) :
    ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first)
      (.app (weakenCtx Γ successor) count)) (.app (weakenCtx Γ successor) result)) := by
  apply ProofSyntax.impE (.eqPropER (sum_beta successor zero first
    (.app (weakenCtx Γ successor) count) (.app (weakenCtx Γ successor) result)))
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let predicate : Term Const ((number ⇒ number ⇒ .prop) :: Γ) (number ⇒ number ⇒ .prop) := .var .vz
  let antecedent := Term.and (.app (.app predicate (weakenCtx _ zero)) (weaken first))
    (sumClosed successor predicate)
  let hypotheses := antecedent :: weakenHyps assumptions
  let given : ProofSyntax Const hypotheses antecedent := .hyp 0
  have earlier : ProofSyntax Const hypotheses
      (.app (.app (.app (weakenCtx _ (sum zero successor)) (weaken first)) (weaken count)) (weaken result)) := by
    apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken present).prepend antecedent)
    simp only [HOL.rename, rename_weakenCtx, weaken]
  have atResult := sumEliminate successor zero (weaken first) (weaken count) (weaken result) predicate
    earlier (.andEL given) (.andER given)
  exact .impE (sumClosedAt successor predicate (weaken count) (weaken result) (.andER given)) atResult

def avoidsZero : Term Const Γ (number ⇒ .prop) :=
  .lam (.not (.eq (.var .vz) (weakenCtx _ zero)))

theorem avoidsZero_rename (images : Rename Base Γ Ξ) :
    HOL.rename images (avoidsZero (Γ := Γ) zero) = avoidsZero zero := by
  simp only [avoidsZero, HOL.rename, rename_weakenCtx, Rename.lift]

def avoidsZero_beta {assumptions : List (Formula Const Γ)} (point : Term Const Γ number) :
    ProofSyntax Const assumptions (.eq (.app (avoidsZero zero) point) (.not (.eq point (weakenCtx Γ zero)))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta point (.not (.eq (.var .vz) (weakenCtx _ zero))))
  simp only [instantiate, HOL.subst, Subst.single, subst_weakenCtx]
  rfl

def lessZeroRefute {assumptions : List (Formula Const Γ)} (lower : Term Const Γ number)
    (separate : ProofSyntax Const assumptions
      (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower) (weakenCtx Γ zero))) :
    ProofSyntax Const assumptions .bot := by
  let predicate : Term Const Γ (number ⇒ .prop) := avoidsZero zero
  have start : ProofSyntax Const assumptions (.app predicate (.app (weakenCtx Γ successor) lower)) :=
    .impE (.eqPropER (avoidsZero_beta zero _))
      (NaturalNumeralProofs.successorNeZero (weakenCtx Γ zero) (weakenCtx Γ successor) lower separate)
  have closed : ProofSyntax Const assumptions (successorClosed successor predicate) := by
    apply ProofSyntax.allI
    apply ProofSyntax.impI
    let antecedent := Term.app (weaken predicate) (.var .vz)
    let hypotheses := antecedent :: weakenHyps assumptions
    have law : ProofSyntax Const hypotheses
        (NaturalNumeralProofs.separation (weakenCtx (number :: Γ) zero) (weakenCtx (number :: Γ) successor)) := by
      apply ProofSyntax.castIndices rfl ?_ ((ProofSyntax.rename Rename.weaken separate).prepend antecedent)
      simp only [NaturalNumeralProofs.separation, HOL.rename, Rename.lift, weaken, rename_weakenCtx]
    have apart := NaturalNumeralProofs.successorNeZero (weakenCtx (number :: Γ) zero)
      (weakenCtx (number :: Γ) successor) (.var .vz) law
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.impE (.eqPropER (avoidsZero_beta zero (.app (weakenCtx _ successor) (.var .vz)))) apart)
    exact congrArg (fun function => Term.app function (.app (weakenCtx _ successor) (.var .vz)))
      (avoidsZero_rename zero Rename.weaken).symm
  have atZero := lessEliminate successor lower (weakenCtx Γ zero) predicate present start closed
  exact .notE (.impE (.eqPropEL (avoidsZero_beta zero (weakenCtx Γ zero))) atZero) (.eqRefl (weakenCtx Γ zero))

#print axioms sumStep
#print axioms lessZeroRefute

theorem successorClosedAt_free {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ .prop)) (point : Term Const Γ number)
    (closed : ProofSyntax Const assumptions (successorClosed successor predicate))
    (free : closed.FunctionExtensionalityFree) :
    (successorClosedAt successor predicate point closed).FunctionExtensionalityFree := by
  unfold successorClosedAt
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

theorem lessNext_free {assumptions : List (Formula Const Γ)} (lower : Term Const Γ number) :
    (lessNext successor (assumptions := assumptions) lower).FunctionExtensionalityFree := by
  unfold lessNext
  exact ⟨less_beta_free _ _ _, trivial⟩

theorem lessStep_free {assumptions : List (Formula Const Γ)} (lower upper : Term Const Γ number)
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower) upper))
    (free : present.FunctionExtensionalityFree) :
    (lessStep successor lower upper present).FunctionExtensionalityFree := by
  unfold lessStep
  refine ⟨less_beta_free _ _ _, ?_⟩
  constructor
  · apply successorClosedAt_free
    trivial
  · apply lessEliminate_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free
    · trivial
    · trivial

theorem sumZero_free {assumptions : List (Formula Const Γ)} (first : Term Const Γ number) :
    (sumZero successor zero (assumptions := assumptions) first).FunctionExtensionalityFree := by
  unfold sumZero
  exact ⟨sum_beta_free _ _ _ _ _, trivial⟩

theorem sumClosedAt_free {assumptions : List (Formula Const Γ)}
    (predicate : Term Const Γ (number ⇒ number ⇒ .prop)) (count value : Term Const Γ number)
    (closed : ProofSyntax Const assumptions (sumClosed successor predicate))
    (free : closed.FunctionExtensionalityFree) :
    (sumClosedAt successor predicate count value closed).FunctionExtensionalityFree := by
  unfold sumClosedAt
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

theorem sumStep_free {assumptions : List (Formula Const Γ)} (first count result : Term Const Γ number)
    (present : ProofSyntax Const assumptions (.app (.app (.app (weakenCtx Γ (sum zero successor)) first) count) result))
    (free : present.FunctionExtensionalityFree) :
    (sumStep successor zero first count result present).FunctionExtensionalityFree := by
  unfold sumStep
  refine ⟨sum_beta_free _ _ _ _ _, ?_⟩
  constructor
  · apply sumClosedAt_free
    trivial
  · apply sumEliminate_free
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free
    · trivial
    · trivial

theorem avoidsZero_beta_free {assumptions : List (Formula Const Γ)} (point : Term Const Γ number) :
    (avoidsZero_beta zero (assumptions := assumptions) point).FunctionExtensionalityFree := by
  unfold avoidsZero_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

theorem lessZeroRefute_free {assumptions : List (Formula Const Γ)} (lower : Term Const Γ number)
    (separate : ProofSyntax Const assumptions
      (NaturalNumeralProofs.separation (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (present : ProofSyntax Const assumptions (.app (.app (weakenCtx Γ (less successor)) lower) (weakenCtx Γ zero)))
    (separateFree : separate.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (lessZeroRefute successor zero lower separate present).FunctionExtensionalityFree := by
  unfold lessZeroRefute
  refine ⟨⟨avoidsZero_beta_free _ _, ?_⟩, trivial⟩
  apply lessEliminate_free
  · exact presentFree
  · exact ⟨avoidsZero_beta_free _ _, NaturalNumeralProofs.successorNeZero_free _ _ _ _ separateFree⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    constructor
    · exact avoidsZero_beta_free _ _
    · apply NaturalNumeralProofs.successorNeZero_free
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr separateFree

#print axioms sumStep_free
#print axioms lessZeroRefute_free

end Mettapedia.Logic.HOL.SuccessorOrder
