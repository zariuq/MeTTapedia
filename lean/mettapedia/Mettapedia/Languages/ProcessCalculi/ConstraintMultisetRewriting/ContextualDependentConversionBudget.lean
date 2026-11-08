import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentReductionBudget
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableConversion

/-!
# Fuel stability of executable dependent conversion

Successful comparisons and inferred neutral types are retained when fuel
increases, provided successful reduction results are retained. The actual
normalizer satisfies that condition. Stability is separate from eventual
success of the comparison on every declaratively equal pair.
-/

set_option autoImplicit false

universe u v

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConversionBudget

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion

/-- Additional work may finish an unfinished computation but may not
replace a previously returned result. -/
def Keeps {α : Type u} (first second : Option α) : Prop :=
  ∀ result, first = some result → second = some result

theorem keeps_refl {α : Type u} (value : Option α) : Keeps value value := fun _ accepted => accepted

theorem keeps_bind {α : Type u} {β : Type v} {first second : Option α}
    {left right : α → Option β} (input : Keeps first second)
    (body : ∀ value, Keeps (left value) (right value)) : Keeps (first.bind left) (second.bind right) := by
  intro result accepted
  obtain ⟨value, computed, returned⟩ := Option.bind_eq_some_iff.mp accepted
  exact Option.bind_eq_some_iff.mpr ⟨value, input value computed, body value result returned⟩

variable {Head : Type} (rules : Rules Head) [DecidableEq Head]
variable [DecidableRel rules.headEq] [∀ head, Decidable (rules.isUniverse head)]
variable (reducer : Reducer rules)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem all_success_succ :
    (∀ fuel n (Γ : Ctx Head n) left right type,
      Keeps (compare rules reducer fuel Γ left right type) (compare rules reducer (fuel + 1) Γ left right type)) ∧
    (∀ fuel n (Γ : Ctx Head n) left right type,
      Keeps (compareNeutral rules reducer fuel Γ left right type)
        (compareNeutral rules reducer (fuel + 1) Γ left right type)) ∧
    (∀ fuel n (Γ : Ctx Head n) left right,
      Keeps (neutral rules reducer fuel Γ left right) (neutral rules reducer (fuel + 1) Γ left right)) ∧
    (∀ fuel n (Γ : Ctx Head n) left right,
      Keeps (types rules reducer fuel Γ left right) (types rules reducer (fuel + 1) Γ left right)) := by
  apply ExecutableConversion.compare.mutual_induct rules
    (motive1 := fun fuel n Γ left right type =>
      Keeps (compare rules reducer fuel Γ left right type) (compare rules reducer (fuel + 1) Γ left right type))
    (motive2 := fun fuel n Γ left right type =>
      Keeps (compareNeutral rules reducer fuel Γ left right type)
        (compareNeutral rules reducer (fuel + 1) Γ left right type))
    (motive3 := fun fuel n Γ left right =>
      Keeps (neutral rules reducer fuel Γ left right) (neutral rules reducer (fuel + 1) Γ left right))
    (motive4 := fun fuel n Γ left right =>
      Keeps (types rules reducer fuel Γ left right) (types rules reducer (fuel + 1) Γ left right))
  case case1 => intro n Γ left right type result accepted; simp only [ExecutableConversion.compare] at accepted; cases accepted
  case case2 =>
    intro n fuel Γ left right type piIH fstIH sndIH typesIH neutralIH idIH result accepted
    rw [ExecutableConversion.compare] at accepted ⊢
    apply keeps_bind (stable (fuel + 1) type) ?_ result accepted
    intro normal
    rcases normal with ⟨code, path⟩
    cases code <;> dsimp only
    all_goals try exact neutralIH
    case pi domain body => exact keeps_bind (piIH domain body) (fun _ => keeps_refl _)
    case sigma domain body =>
      exact keeps_bind (fstIH domain) (fun _ => keeps_bind (sndIH body) (fun _ => keeps_refl _))
    case head value =>
      split
      · exact keeps_bind typesIH (fun _ => keeps_refl _)
      · exact neutralIH
    case id carrier a b =>
      apply keeps_bind (stable (fuel + 1) left)
      intro first
      apply keeps_bind (stable (fuel + 1) right)
      intro second
      split <;> try dsimp only
      · exact keeps_bind (idIH _ _ _) (fun _ => keeps_refl _)
      · exact neutralIH
  case case3 => intro n Γ left right type result accepted; simp only [compareNeutral] at accepted; cases accepted
  case case4 =>
    intro n fuel Γ left right type neutralIH result accepted
    rw [ExecutableConversion.compareNeutral] at accepted ⊢
    exact keeps_bind (stable (fuel + 1) left) (fun first =>
      keeps_bind (stable (fuel + 1) right) (fun second =>
        keeps_bind (neutralIH first second) (fun _ => keeps_refl _))) result accepted
  case case5 => intro n Γ left right result accepted; simp only [neutral] at accepted; cases accepted
  case case6 => intro n fuel Γ second result accepted; simpa only [neutral, dif_pos rfl] using accepted
  case case7 => intro n fuel Γ first second different result accepted; simp [neutral, different] at accepted
  case case8 => intro n fuel second type Γ known result accepted; simpa only [neutral, dif_pos rfl, known] using accepted
  case case9 =>
    intro n fuel second Γ unknown result accepted
    rw [neutral] at accepted
    split at accepted
    · split at accepted <;> simp_all
    · simp_all
  case case10 => intro n fuel first second different Γ result accepted; simp [neutral, different] at accepted
  case case11 =>
    intro n fuel Γ function argument other otherArgument neutralIH argumentIH result accepted
    rw [ExecutableConversion.neutral] at accepted ⊢
    apply keeps_bind neutralIH ?_ result accepted
    intro functionResult
    apply keeps_bind (stable (fuel + 1) functionResult.1)
    intro normal
    split <;> try dsimp only
    · exact keeps_bind (argumentIH _) (fun _ => keeps_refl _)
    · exact keeps_refl _
  case case12 =>
    intro n fuel Γ pair other neutralIH result accepted
    rw [ExecutableConversion.neutral] at accepted ⊢
    apply keeps_bind neutralIH ?_ result accepted
    intro pairResult
    apply keeps_bind (stable (fuel + 1) pairResult.1)
    intro normal
    exact keeps_refl _
  case case13 =>
    intro n fuel Γ pair other neutralIH result accepted
    rw [ExecutableConversion.neutral] at accepted ⊢
    apply keeps_bind neutralIH ?_ result accepted
    intro pairResult
    apply keeps_bind (stable (fuel + 1) pairResult.1)
    intro normal
    exact keeps_refl _
  case case14 =>
    intro n fuel Γ left right notVars notConsts notApps notFst notSnd result accepted
    rw [neutral] at accepted <;> try assumption
    cases accepted
  case case15 => intro n Γ left right result accepted; simp only [types] at accepted; cases accepted
  case case16 =>
    intro n fuel Γ left right domainsIH bodiesIH termsIH neutralIH result accepted
    rw [ExecutableConversion.types] at accepted ⊢
    apply keeps_bind (stable (fuel + 1) left) ?_ result accepted
    intro first
    apply keeps_bind (stable (fuel + 1) right)
    intro second
    split <;> try dsimp only
    · exact keeps_refl _
    · exact keeps_bind (domainsIH _ _) (fun _ => keeps_bind (bodiesIH _ _ _) (fun _ => keeps_refl _))
    · exact keeps_bind (domainsIH _ _) (fun _ => keeps_bind (bodiesIH _ _ _) (fun _ => keeps_refl _))
    · exact keeps_bind (domainsIH _ _) (fun _ => keeps_bind (termsIH _ _ _) (fun _ =>
        keeps_bind (termsIH _ _ _) (fun _ => keeps_refl _)))
    · exact keeps_bind (neutralIH first second) (fun _ => keeps_refl _)

include stable in
theorem compare_success_mono {n fuel larger : Nat} {Γ : Ctx Head n} {left right type : Tm Head n}
    {result : Certificate rules (.compare Γ left right type)}
    (accepted : compare rules reducer fuel Γ left right type = some result) (enough : fuel ≤ larger) :
    compare rules reducer larger Γ left right type = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact (all_success_succ rules reducer stable).1 larger n Γ left right type result ih

include stable in
theorem compareNeutral_success_mono {n fuel larger : Nat} {Γ : Ctx Head n} {left right type : Tm Head n}
    {result : Certificate rules (.compare Γ left right type)}
    (accepted : compareNeutral rules reducer fuel Γ left right type = some result) (enough : fuel ≤ larger) :
    compareNeutral rules reducer larger Γ left right type = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact (all_success_succ rules reducer stable).2.1 larger n Γ left right type result ih

include stable in
theorem neutral_success_mono {n fuel larger : Nat} {Γ : Ctx Head n} {left right : Tm Head n}
    {result : NeutralResult rules Γ left right}
    (accepted : neutral rules reducer fuel Γ left right = some result) (enough : fuel ≤ larger) :
    neutral rules reducer larger Γ left right = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact (all_success_succ rules reducer stable).2.2.1 larger n Γ left right result ih

include stable in
theorem types_success_mono {n fuel larger : Nat} {Γ : Ctx Head n} {left right : Tm Head n}
    {result : Certificate rules (.types Γ left right)}
    (accepted : types rules reducer fuel Γ left right = some result) (enough : fuel ≤ larger) :
    types rules reducer larger Γ left right = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact (all_success_succ rules reducer stable).2.2.2 larger n Γ left right result ih

omit [DecidableEq Head] [DecidableRel rules.headEq] [∀ head, Decidable (rules.isUniverse head)] in
theorem normalizer_stable (root : RootEvaluator rules) {n : Nat} (fuel : Nat) (term : Tm Head n) :
    Keeps (ExecutableReduction.normalize rules root fuel term)
      (ExecutableReduction.normalize rules root (fuel + 1) term) :=
  fun _ accepted => ContextualDependentReductionBudget.success_succ rules root accepted

theorem normalizer_compare_mono (root : RootEvaluator rules) {n fuel larger : Nat}
    {Γ : Ctx Head n} {left right type : Tm Head n} {result : Certificate rules (.compare Γ left right type)}
    (accepted : compare rules (ExecutableReduction.normalize rules root) fuel Γ left right type = some result)
    (enough : fuel ≤ larger) :
    compare rules (ExecutableReduction.normalize rules root) larger Γ left right type = some result :=
  compare_success_mono rules _ (normalizer_stable rules root) accepted enough

theorem normalizer_neutral_mono (root : RootEvaluator rules) {n fuel larger : Nat}
    {Γ : Ctx Head n} {left right : Tm Head n} {result : NeutralResult rules Γ left right}
    (accepted : neutral rules (ExecutableReduction.normalize rules root) fuel Γ left right = some result)
    (enough : fuel ≤ larger) :
    neutral rules (ExecutableReduction.normalize rules root) larger Γ left right = some result :=
  neutral_success_mono rules _ (normalizer_stable rules root) accepted enough

end ContextualDependentConversionBudget
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
