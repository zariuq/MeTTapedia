import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConversionBudget
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking

/-!
# Fuel stability of executable dependent checking

Increasing fuel retains inferred types and accepted checking judgments.
The subtyping check may switch from structural comparison to a newly
successful conversion proof; both certify the same subtyping judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCheckingBudget

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableChecking ContextualDependentConversionBudget

variable {Head : Type} (rules : Rules Head) [DecidableEq Head]
variable [DecidableRel rules.headEq] [∀ head, Decidable (rules.isUniverse head)] [DecidableRel rules.cumulative]
variable (choices : HeadChoices rules) (reducer : Reducer rules)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
omit [DecidableEq Head] [DecidableRel rules.headEq] [DecidableRel rules.cumulative] in
theorem asUniverse_succ {n : Nat} (fuel : Nat) (type : Tm Head n) :
    Keeps (asUniverse rules reducer fuel type) (asUniverse rules reducer (fuel + 1) type) := by
  unfold asUniverse
  exact keeps_bind (stable fuel type) (fun _ => keeps_refl _)

include stable in
theorem below_succ : ∀ fuel n (Γ : Ctx Head n) (first second : Tm Head n),
    Keeps (below rules reducer fuel Γ first second) (below rules reducer (fuel + 1) Γ first second) := by
  intro fuel
  induction fuel with
  | zero => intro n Γ first second result accepted; simp only [below] at accepted; cases accepted
  | succ fuel ih =>
    intro n Γ first second
    cases earlier : ExecutableConversion.types rules reducer (fuel + 1) Γ first second with
    | some certificate =>
      have later := types_success_mono rules reducer stable earlier (Nat.le_succ _)
      intro result accepted
      simp only [below, later]
    | none =>
      cases later : ExecutableConversion.types rules reducer (fuel + 1 + 1) Γ first second with
      | some certificate =>
        intro result accepted
        rw [below, later]
      | none =>
        intro result accepted
        rw [below, earlier] at accepted
        rw [below, later]
        apply keeps_bind (stable (fuel + 1) first) ?_ result accepted
        intro firstNormal
        apply keeps_bind (stable (fuel + 1) second)
        intro secondNormal
        split <;> try dsimp only
        · exact keeps_refl _
        · exact keeps_bind ((all_success_succ rules reducer stable).2.2.2 fuel _ _ _ _)
            (fun _ => keeps_bind (ih _ _ _ _) (fun _ => keeps_refl _))
        · exact keeps_bind (ih _ _ _ _) (fun _ => keeps_bind (ih _ _ _ _) (fun _ => keeps_refl _))
        · exact keeps_refl _

include stable in
theorem synth_check_succ :
    (∀ fuel {n : Nat} (Γ : Ctx Head n) (term : Tm Head n),
      Keeps (synth rules choices reducer fuel Γ term) (synth rules choices reducer (fuel + 1) Γ term)) ∧
    (∀ fuel {n : Nat} (Γ : Ctx Head n) (term type : Tm Head n),
      Keeps (check rules choices reducer fuel Γ term type) (check rules choices reducer (fuel + 1) Γ term type)) := by
  apply ExecutableChecking.synth.mutual_induct rules
    (motive_1 := fun fuel {n} Γ term =>
      Keeps (synth rules choices reducer fuel Γ term) (synth rules choices reducer (fuel + 1) Γ term))
    (motive_2 := fun fuel {n} Γ term type =>
      Keeps (check rules choices reducer fuel Γ term type) (check rules choices reducer (fuel + 1) Γ term type))
  case case1 => intro n Γ term result accepted; simp only [synth] at accepted; cases accepted
  case case2 => intro fuel n Γ index result accepted; simpa only [synth] using accepted
  case case3 => intro fuel n Γ name type known result accepted; simpa only [synth, known] using accepted
  case case4 =>
    intro fuel n Γ name unknown result accepted
    rw [synth] at accepted
    split at accepted <;> simp_all
  case case5 => intro fuel n Γ value result accepted; simpa only [synth] using accepted
  case case6 =>
    intro fuel n Γ domain body domainIH bodyIH result accepted
    rw [synth] at accepted ⊢
    exact keeps_bind domainIH (fun domainType =>
      keeps_bind (asUniverse_succ rules reducer stable (fuel + 1) domainType.1) (fun _ =>
        keeps_bind bodyIH (fun bodyType =>
          keeps_bind (asUniverse_succ rules reducer stable (fuel + 1) bodyType.1) (fun _ => keeps_refl _)))) result accepted
  case case7 =>
    intro fuel n Γ domain body domainIH bodyIH result accepted
    rw [synth] at accepted ⊢
    exact keeps_bind domainIH (fun domainType =>
      keeps_bind (asUniverse_succ rules reducer stable (fuel + 1) domainType.1) (fun _ =>
        keeps_bind bodyIH (fun bodyType =>
          keeps_bind (asUniverse_succ rules reducer stable (fuel + 1) bodyType.1) (fun _ => keeps_refl _)))) result accepted
  case case8 =>
    intro fuel n Γ carrier left right carrierIH leftIH rightIH result accepted
    rw [synth] at accepted ⊢
    exact keeps_bind carrierIH (fun carrierType =>
      keeps_bind (asUniverse_succ rules reducer stable (fuel + 1) carrierType.1) (fun _ =>
        keeps_bind leftIH (fun _ => keeps_bind rightIH (fun _ => keeps_refl _)))) result accepted
  case case9 =>
    intro fuel n Γ subject ih result accepted
    rw [synth] at accepted ⊢
    exact keeps_bind ih (fun _ => keeps_refl _) result accepted
  case case10 =>
    intro fuel n Γ body argument argumentIH bodyIH result accepted
    rw [synth] at accepted ⊢
    exact keeps_bind argumentIH (fun argumentType =>
      keeps_bind (bodyIH argumentType) (fun _ => keeps_refl _)) result accepted
  case case11 =>
    intro fuel n Γ function argument notLambda functionIH argumentIH result accepted
    rw [synth] at accepted ⊢ <;> try assumption
    apply keeps_bind functionIH ?_ result accepted
    intro functionType
    apply keeps_bind (stable (fuel + 1) functionType.1)
    intro normal
    split <;> try dsimp only
    · exact keeps_bind (argumentIH _) (fun _ => keeps_refl _)
    · exact keeps_refl _
  case case12 =>
    intro fuel n Γ pair ih result accepted
    rw [synth] at accepted ⊢
    exact keeps_bind ih (fun pairType =>
      keeps_bind (stable (fuel + 1) pairType.1) (fun _ => keeps_refl _)) result accepted
  case case13 =>
    intro fuel n Γ pair ih result accepted
    rw [synth] at accepted ⊢
    exact keeps_bind ih (fun pairType =>
      keeps_bind (stable (fuel + 1) pairType.1) (fun _ => keeps_refl _)) result accepted
  case case14 => intro fuel n Γ body result accepted; simp only [synth] at accepted; cases accepted
  case case15 => intro fuel n Γ first second result accepted; simp only [synth] at accepted; cases accepted
  case case16 => intro n Γ term type result accepted; simp only [check] at accepted; cases accepted
  case case17 =>
    intro fuel n Γ type body ih result accepted
    rw [check] at accepted ⊢
    apply keeps_bind (stable (fuel + 1) type) ?_ result accepted
    intro normal
    split <;> try dsimp only
    · exact keeps_bind (ih _ _) (fun _ => keeps_refl _)
    · exact keeps_refl _
  case case18 =>
    intro fuel n Γ type first second firstIH secondIH result accepted
    rw [check] at accepted ⊢
    apply keeps_bind (stable (fuel + 1) type) ?_ result accepted
    intro normal
    split <;> try dsimp only
    · exact keeps_bind (firstIH _) (fun _ => keeps_bind (secondIH _) (fun _ => keeps_refl _))
    · exact keeps_refl _
  case case19 =>
    intro fuel n Γ type subject ih result accepted
    rw [check] at accepted ⊢
    apply keeps_bind (stable (fuel + 1) type) ?_ result accepted
    intro normal
    split <;> try dsimp only
    · exact keeps_bind (ih _) (fun _ =>
        keeps_bind ((all_success_succ rules reducer stable).1 fuel _ _ _ _ _) (fun _ =>
          keeps_bind ((all_success_succ rules reducer stable).1 fuel _ _ _ _ _) (fun _ => keeps_refl _)))
    · exact keeps_refl _
  case case20 =>
    intro fuel n Γ type term notLambda notPair notRefl ih result accepted
    rw [check] at accepted ⊢ <;> try assumption
    exact keeps_bind ih (fun inferred =>
      keeps_bind (below_succ rules reducer stable fuel n Γ inferred.1 type) (fun _ => keeps_refl _)) result accepted

include stable in
theorem formContext_succ {n : Nat} (fuel : Nat) (Γ : Ctx Head n) :
    Keeps (formContext rules choices reducer fuel Γ) (formContext rules choices reducer (fuel + 1) Γ) := by
  induction Γ with
  | nil => exact keeps_refl _
  | snoc Γ domain ih =>
    intro result accepted
    rw [formContext] at accepted ⊢
    exact keeps_bind ih (fun _ =>
      keeps_bind ((synth_check_succ rules choices reducer stable).1 fuel Γ domain) (fun inferred =>
        keeps_bind (asUniverse_succ rules reducer stable fuel inferred.1) (fun _ => keeps_refl _))) result accepted

include stable in
theorem judgment_succ {n : Nat} (fuel : Nat) (Γ : Ctx Head n) (term type : Tm Head n) :
    Keeps (judgment rules choices reducer fuel Γ term type)
      (judgment rules choices reducer (fuel + 1) Γ term type) := by
  unfold judgment
  exact keeps_bind (formContext_succ rules choices reducer stable fuel Γ) (fun _ =>
    keeps_bind ((synth_check_succ rules choices reducer stable).1 fuel Γ type) (fun expected =>
      keeps_bind (asUniverse_succ rules reducer stable fuel expected.1) (fun _ =>
        keeps_bind ((synth_check_succ rules choices reducer stable).2 fuel Γ term type) (fun _ => keeps_refl _))))

include stable in
theorem equality_succ {n : Nat} (fuel : Nat) (Γ : Ctx Head n) (first second type : Tm Head n) :
    Keeps (equality rules choices reducer fuel Γ first second type)
      (equality rules choices reducer (fuel + 1) Γ first second type) := by
  unfold equality
  exact keeps_bind (judgment_succ rules choices reducer stable fuel Γ first type) (fun _ =>
    keeps_bind (judgment_succ rules choices reducer stable fuel Γ second type) (fun _ =>
      keeps_bind ((all_success_succ rules reducer stable).1 fuel n Γ first second type) (fun _ => keeps_refl _)))

include stable in
theorem synth_success_mono {n fuel larger : Nat} {Γ : Ctx Head n} {term : Tm Head n}
    {result : SynthResult rules Γ term}
    (accepted : synth rules choices reducer fuel Γ term = some result) (enough : fuel ≤ larger) :
    synth rules choices reducer larger Γ term = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact (synth_check_succ rules choices reducer stable).1 larger Γ term result ih

include stable in
theorem check_success_mono {n fuel larger : Nat} {Γ : Ctx Head n} {term type : Tm Head n}
    {result : CheckResult rules Γ term type}
    (accepted : check rules choices reducer fuel Γ term type = some result) (enough : fuel ≤ larger) :
    check rules choices reducer larger Γ term type = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact (synth_check_succ rules choices reducer stable).2 larger Γ term type result ih

include stable in
theorem below_success_mono {n fuel larger : Nat} {Γ : Ctx Head n} {first second : Tm Head n}
    {result : PLift (BelowAlgorithm rules Γ first second)}
    (accepted : below rules reducer fuel Γ first second = some result) (enough : fuel ≤ larger) :
    below rules reducer larger Γ first second = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact below_succ rules reducer stable larger n Γ first second result ih

include stable in
omit [DecidableEq Head] [DecidableRel rules.headEq] [DecidableRel rules.cumulative] in
theorem asUniverse_success_mono {n fuel larger : Nat} {type : Tm Head n}
    {result : {head : Head // rules.isUniverse head ∧ Reduces rules type (.head head)}}
    (accepted : asUniverse rules reducer fuel type = some result) (enough : fuel ≤ larger) :
    asUniverse rules reducer larger type = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact asUniverse_succ rules reducer stable larger type result ih

include stable in
theorem judgment_success_mono {n fuel larger : Nat} {Γ : Ctx Head n} {term type : Tm Head n}
    {result : JudgmentCertificate rules Γ term type}
    (accepted : judgment rules choices reducer fuel Γ term type = some result) (enough : fuel ≤ larger) :
    judgment rules choices reducer larger Γ term type = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact judgment_succ rules choices reducer stable larger Γ term type result ih

include stable in
theorem equality_success_mono {n fuel larger : Nat} {Γ : Ctx Head n} {first second type : Tm Head n}
    {result : EqualityCertificate rules Γ first second type}
    (accepted : equality rules choices reducer fuel Γ first second type = some result) (enough : fuel ≤ larger) :
    equality rules choices reducer larger Γ first second type = some result := by
  induction enough with
  | refl => exact accepted
  | @step larger _ ih => exact equality_succ rules choices reducer stable larger Γ first second type result ih

end ContextualDependentCheckingBudget
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
