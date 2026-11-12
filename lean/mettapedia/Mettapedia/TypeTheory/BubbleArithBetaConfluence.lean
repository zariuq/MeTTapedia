import Mettapedia.TypeTheory.BubbleBetaConfluence

/-!
# The arithmetic bubble with β is admitted for typing

`BubbleTypingAdmission` admits the recursion equations of addition, and `BubbleBetaConfluence`
admits β. Admission of each does not give admission of both together: the two facts about
products come from the confluence of the joint rule set. This module proves that confluence and
concludes.

* `ParA` is parallel reduction for β with the two recursion equations, `devA` its complete
  development, `parA_dev` the triangle.
* `joint_confluent`: β together with the recursion equations of addition is confluent.
* `rule_keeps_types_in`: the recursion equations keep types in every bubble whose conversion is
  coherent, has convertible domains for convertible products, and is stable under substitution.
* `joint_admitted`: the bubble that declares β and the recursion equations is admitted for
  typing. With that conversion at every node the comparison core has unique types up to
  conversion, weakening, substitution and subject reduction.

## Controls

* `Controls.identity_plus_zero_converts`: `Vec ((λ m. m + 0) n)` converts with `Vec n`, by one β
  step and one recursion step.
* `Controls.joint_types_unique`: any two types of a term in the joint bubble are convertible.
* `Controls.joint_not_convergent`: the joint bubble is not terminating on raw terms, so it does
  not meet the convergence criterion that decides conversion by normal forms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleArithBetaConfluence

open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.TypeTheory.BubbleSubjectReduction
open Mettapedia.TypeTheory.BubbleBetaTyping
open Mettapedia.TypeTheory.BubbleTypingAdmission
open Mettapedia.TypeTheory.BubbleBetaConfluence
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeUnderBinders.Controls
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.TypeTheory.PromotionAdmission (Terminating Convergent)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Mettapedia.Logic.Relation (Confluent)
open Expr

/-! ## The recursion equations keep types wherever products are injective -/

/-- A typed successor has a number below it and is a number. -/
theorem succ_inv_in {rules : AExpr → AExpr → Prop} (coherent : Coherent (Convertible rules))
    (domains : PiDomainInjective rules) (substStable : SubstitutionStable rules)
    {Γ : List AExpr} {y T : AExpr} (typed : HasTypeInside rules Γ (succE y) T) :
    HasTypeInside rules Γ y natType ∧ Convertible rules natType T := by
  obtain ⟨A, B, typedC, typedY, atT⟩ := typed_app_inv coherent typed
  have atC : Convertible rules (Expr.pi natType natType) (Expr.pi A B) :=
    typed_const_inv coherent typedC
  have domain : Convertible rules natType A := domains _ _ _ _ atC
  have codomain : Convertible rules natType B := coherent.piCodomain _ _ _ _ atC
  exact ⟨Typed.move typedY (Relation.EqvGen.symm _ _ domain),
    Relation.EqvGen.trans _ _ _ (convertible_substAt substStable codomain 0 y) atT⟩

/-- A typed sum has two numbers below it and is a number. -/
theorem add_inv_in {rules : AExpr → AExpr → Prop} (coherent : Coherent (Convertible rules))
    (domains : PiDomainInjective rules) (substStable : SubstitutionStable rules)
    {Γ : List AExpr} {x y T : AExpr} (typed : HasTypeInside rules Γ (addE x y) T) :
    HasTypeInside rules Γ x natType ∧ HasTypeInside rules Γ y natType ∧
      Convertible rules natType T := by
  obtain ⟨A, B, typedF, typedY, atT⟩ := typed_app_inv coherent typed
  obtain ⟨A₁, B₁, typedC, typedX, atF⟩ := typed_app_inv coherent typedF
  have atC : Convertible rules (Expr.pi natType (Expr.pi natType natType)) (Expr.pi A₁ B₁) :=
    typed_const_inv coherent typedC
  have domain₁ : Convertible rules natType A₁ := domains _ _ _ _ atC
  have codomain₁ : Convertible rules (Expr.pi natType natType) B₁ :=
    coherent.piCodomain _ _ _ _ atC
  have applied : Convertible rules (Expr.pi natType natType) (Expr.pi A B) :=
    Relation.EqvGen.trans _ _ _ (convertible_substAt substStable codomain₁ 0 x) atF
  have domain₂ : Convertible rules natType A := domains _ _ _ _ applied
  have codomain₂ : Convertible rules natType B := coherent.piCodomain _ _ _ _ applied
  exact ⟨Typed.move typedX (Relation.EqvGen.symm _ _ domain₁),
    Typed.move typedY (Relation.EqvGen.symm _ _ domain₂),
    Relation.EqvGen.trans _ _ _ (convertible_substAt substStable codomain₂ 0 y) atT⟩

theorem succ_typed_in {rules : AExpr → AExpr → Prop} {Γ : List AExpr} {y : AExpr}
    (typedY : HasTypeInside rules Γ y natType) : HasTypeInside rules Γ (succE y) natType :=
  Typed.app (A := natType) (B := natType) (Typed.const _ ArithConst.succ) typedY

theorem add_typed_in {rules : AExpr → AExpr → Prop} {Γ : List AExpr} {x y : AExpr}
    (typedX : HasTypeInside rules Γ x natType) (typedY : HasTypeInside rules Γ y natType) :
    HasTypeInside rules Γ (addE x y) natType :=
  Typed.app (A := natType) (B := natType)
    (Typed.app (A := natType) (B := Expr.pi natType natType) (Typed.const _ ArithConst.add)
      typedX)
    typedY

/-- **The recursion equations keep types in every bubble with injective products.** -/
theorem rule_keeps_types_in {rules : AExpr → AExpr → Prop}
    (coherent : Coherent (Convertible rules)) (domains : PiDomainInjective rules)
    (substStable : SubstitutionStable rules) :
    ∀ (Γ : List AExpr) (left right A : AExpr), Rule left right →
      HasTypeInside rules Γ left A → HasTypeInside rules Γ right A := by
  intro Γ left right T rule typed
  cases rule with
  | addZero =>
      obtain ⟨typedLeft, _, atT⟩ := add_inv_in coherent domains substStable typed
      exact Typed.move typedLeft atT
  | addSucc =>
      obtain ⟨typedLeft, typedSucc, atT⟩ := add_inv_in coherent domains substStable typed
      obtain ⟨typedRight, _⟩ := succ_inv_in coherent domains substStable typedSucc
      exact Typed.move (succ_typed_in (add_typed_in typedLeft typedRight)) atT

/-- The left side of a recursion equation is an application. -/
theorem rule_app {left right : AExpr} (rule : Rule left right) :
    ∃ f a : AExpr, left = Expr.app f a := by
  cases rule with
  | addZero => exact ⟨_, _, rfl⟩
  | addSucc => exact ⟨_, _, rfl⟩

/-- Neither β nor a recursion equation rewrites a product at the root. -/
theorem joint_noPiRule (A B right : AExpr) : ¬ withBeta Rule (Expr.pi A B) right := by
  intro rule
  rcases rule with contracted | declared
  · cases contracted
  · obtain ⟨f, a, shape⟩ := rule_app declared
    cases shape

/-- Admission of the joint bubble follows from the confluence of the joint rule set. -/
theorem joint_admitted_of_confluent (confluent : Confluent (Rewrite (withBeta Rule))) :
    TypingAdmission (withBeta Rule) := by
  have codomains := piCodomainInjective_of_confluent confluent joint_noPiRule
  have domains := piDomainInjective_of_confluent confluent joint_noPiRule
  have substStable := withBeta_substStable rule_stable
  have coherent := coherent_convertible substStable codomains
  exact TypingAdmission.of_confluent substStable (withBeta_shiftStable rule_shiftStable)
    confluent joint_noPiRule
    (withBeta_preservesTypes rule_stable rule_shiftStable coherent domains
      (rule_keeps_types_in coherent domains substStable))

/-! ## Parallel reduction for β with the recursion equations -/

/-- Parallel reduction: any set of β redexes and of redexes of the recursion equations present
in a term, contracted at once. -/
inductive ParA : AExpr → AExpr → Prop where
  | bvar (i : Nat) : ParA (Expr.bvar i) (Expr.bvar i)
  | univ : ParA Expr.univ Expr.univ
  | prop : ParA Expr.prop Expr.prop
  | base (b : Unit) : ParA (Expr.base b) (Expr.base b)
  | pi {A A' B B' : AExpr} : ParA A A' → ParA B B' → ParA (Expr.pi A B) (Expr.pi A' B')
  | lam {A A' b b' : AExpr} : ParA A A' → ParA b b' → ParA (Expr.lam A b) (Expr.lam A' b')
  | app {f f' a a' : AExpr} : ParA f f' → ParA a a' → ParA (Expr.app f a) (Expr.app f' a')
  | const (τ : Ty Unit) (c : ArithConst τ) : ParA (Expr.const τ c) (Expr.const τ c)
  | tyFam (b : Unit) : ParA (Expr.tyFam b) (Expr.tyFam b)
  | top : ParA Expr.top Expr.top
  | bot : ParA Expr.bot Expr.bot
  | and {p p' q q' : AExpr} : ParA p p' → ParA q q' → ParA (Expr.and p q) (Expr.and p' q')
  | or {p p' q q' : AExpr} : ParA p p' → ParA q q' → ParA (Expr.or p q) (Expr.or p' q')
  | imp {p p' q q' : AExpr} : ParA p p' → ParA q q' → ParA (Expr.imp p q) (Expr.imp p' q')
  | not {p p' : AExpr} : ParA p p' → ParA (Expr.not p) (Expr.not p')
  | eq {a a' b b' : AExpr} : ParA a a' → ParA b b' → ParA (Expr.eq a b) (Expr.eq a' b')
  | all {A A' b b' : AExpr} : ParA A A' → ParA b b' → ParA (Expr.all A b) (Expr.all A' b')
  | ex {A A' b b' : AExpr} : ParA A A' → ParA b b' → ParA (Expr.ex A b) (Expr.ex A' b')
  | beta {A b b' a a' : AExpr} :
      ParA b b' → ParA a a' → ParA (Expr.app (Expr.lam A b) a) (substAt 0 a' b')
  | addZero {x x' : AExpr} :
      ParA x x' →
        ParA (Expr.app (Expr.app (Expr.const _ ArithConst.add) x) (Expr.const _ ArithConst.zero)) x'
  | addSucc {x x' y y' : AExpr} :
      ParA x x' → ParA y y' →
        ParA
          (Expr.app (Expr.app (Expr.const _ ArithConst.add) x)
            (Expr.app (Expr.const _ ArithConst.succ) y))
          (Expr.app (Expr.const _ ArithConst.succ)
            (Expr.app (Expr.app (Expr.const _ ArithConst.add) x') y'))

theorem parA_refl : ∀ e : AExpr, ParA e e
  | .bvar i => .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (parA_refl A) (parA_refl B)
  | .lam A b => .lam (parA_refl A) (parA_refl b)
  | .app f a => .app (parA_refl f) (parA_refl a)
  | .const τ c => .const τ c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (parA_refl p) (parA_refl q)
  | .or p q => .or (parA_refl p) (parA_refl q)
  | .imp p q => .imp (parA_refl p) (parA_refl q)
  | .not p => .not (parA_refl p)
  | .eq a b => .eq (parA_refl a) (parA_refl b)
  | .all A b => .all (parA_refl A) (parA_refl b)
  | .ex A b => .ex (parA_refl A) (parA_refl b)

/-- A step of the joint rule set at any position is a parallel step. -/
theorem parA_of_rewrite {e e' : AExpr} (step : Rewrite (withBeta Rule) e e') : ParA e e' := by
  induction step with
  | root rule =>
      rcases rule with contracted | declared
      · cases contracted with
        | contract A b a => exact ParA.beta (parA_refl b) (parA_refl a)
      · cases declared with
        | addZero => exact ParA.addZero (parA_refl _)
        | addSucc => exact ParA.addSucc (parA_refl _) (parA_refl _)
  | piDomain _ ih => exact .pi ih (parA_refl _)
  | piBody _ ih => exact .pi (parA_refl _) ih
  | lamDomain _ ih => exact .lam ih (parA_refl _)
  | lamBody _ ih => exact .lam (parA_refl _) ih
  | appFunction _ ih => exact .app ih (parA_refl _)
  | appArgument _ ih => exact .app (parA_refl _) ih
  | andLeft _ ih => exact .and ih (parA_refl _)
  | andRight _ ih => exact .and (parA_refl _) ih
  | orLeft _ ih => exact .or ih (parA_refl _)
  | orRight _ ih => exact .or (parA_refl _) ih
  | impLeft _ ih => exact .imp ih (parA_refl _)
  | impRight _ ih => exact .imp (parA_refl _) ih
  | notBody _ ih => exact .not ih
  | eqLeft _ ih => exact .eq ih (parA_refl _)
  | eqRight _ ih => exact .eq (parA_refl _) ih
  | allDomain _ ih => exact .all ih (parA_refl _)
  | allBody _ ih => exact .all (parA_refl _) ih
  | exDomain _ ih => exact .ex ih (parA_refl _)
  | exBody _ ih => exact .ex (parA_refl _) ih

/-- A parallel step is a sequence of steps of the joint rule set. -/
theorem reduces_of_parA {e e' : AExpr} (h : ParA e e') :
    Relation.ReflTransGen (Rewrite (withBeta Rule)) e e' := by
  induction h with
  | bvar i => exact .refl
  | univ => exact .refl
  | prop => exact .refl
  | base b => exact .refl
  | pi _ _ ihA ihB =>
      exact reduces_congr₂ Expr.pi (fun _ _ _ step => .piDomain step)
        (fun _ _ _ step => .piBody step) ihA ihB
  | lam _ _ ihA ihb =>
      exact reduces_congr₂ Expr.lam (fun _ _ _ step => .lamDomain step)
        (fun _ _ _ step => .lamBody step) ihA ihb
  | app _ _ ihf iha =>
      exact reduces_congr₂ Expr.app (fun _ _ _ step => .appFunction step)
        (fun _ _ _ step => .appArgument step) ihf iha
  | const τ c => exact .refl
  | tyFam b => exact .refl
  | top => exact .refl
  | bot => exact .refl
  | and _ _ ihp ihq =>
      exact reduces_congr₂ Expr.and (fun _ _ _ step => .andLeft step)
        (fun _ _ _ step => .andRight step) ihp ihq
  | or _ _ ihp ihq =>
      exact reduces_congr₂ Expr.or (fun _ _ _ step => .orLeft step)
        (fun _ _ _ step => .orRight step) ihp ihq
  | imp _ _ ihp ihq =>
      exact reduces_congr₂ Expr.imp (fun _ _ _ step => .impLeft step)
        (fun _ _ _ step => .impRight step) ihp ihq
  | not _ ihp => exact reduces_congr Expr.not (fun _ _ step => .notBody step) ihp
  | eq _ _ iha ihb =>
      exact reduces_congr₂ Expr.eq (fun _ _ _ step => .eqLeft step)
        (fun _ _ _ step => .eqRight step) iha ihb
  | all _ _ ihA ihb =>
      exact reduces_congr₂ Expr.all (fun _ _ _ step => .allDomain step)
        (fun _ _ _ step => .allBody step) ihA ihb
  | ex _ _ ihA ihb =>
      exact reduces_congr₂ Expr.ex (fun _ _ _ step => .exDomain step)
        (fun _ _ _ step => .exBody step) ihA ihb
  | @beta A b b' x x' _ _ ihb ihx =>
      exact (reduces_congr₂ Expr.app (fun _ _ _ step => .appFunction step)
        (fun _ _ _ step => .appArgument step)
        (reduces_congr (fun z => Expr.lam A z) (fun _ _ step => .lamBody step) ihb) ihx).tail
        (Rewrite.root (Or.inl (Beta.contract A b' x')))
  | @addZero x x' _ ihx =>
      exact (reduces_congr (fun z => addE z zeroE)
        (fun _ _ step => Rewrite.appFunction (Rewrite.appArgument step)) ihx).tail
        (Rewrite.root (Or.inr (Rule.addZero x')))
  | @addSucc x x' y y' _ _ ihx ihy =>
      exact ((reduces_congr (fun z => addE z (succE y))
        (fun _ _ step => Rewrite.appFunction (Rewrite.appArgument step)) ihx).trans
        (reduces_congr (fun z => addE x' (succE z))
          (fun _ _ step => Rewrite.appArgument (Rewrite.appArgument step)) ihy)).tail
        (Rewrite.root (Or.inr (Rule.addSucc x' y')))

/-- Parallel steps are stable under shifting. -/
theorem parA_shift {e e' : AExpr} (h : ParA e e') :
    ∀ cutoff : Nat, ParA (shiftAt cutoff e) (shiftAt cutoff e') := by
  induction h with
  | bvar i => exact fun _ => parA_refl _
  | univ => exact fun _ => .univ
  | prop => exact fun _ => .prop
  | base b => exact fun _ => .base b
  | pi _ _ ihA ihB => exact fun cutoff => .pi (ihA cutoff) (ihB (cutoff + 1))
  | lam _ _ ihA ihb => exact fun cutoff => .lam (ihA cutoff) (ihb (cutoff + 1))
  | app _ _ ihf iha => exact fun cutoff => .app (ihf cutoff) (iha cutoff)
  | const τ c => exact fun _ => .const τ c
  | tyFam b => exact fun _ => .tyFam b
  | top => exact fun _ => .top
  | bot => exact fun _ => .bot
  | and _ _ ihp ihq => exact fun cutoff => .and (ihp cutoff) (ihq cutoff)
  | or _ _ ihp ihq => exact fun cutoff => .or (ihp cutoff) (ihq cutoff)
  | imp _ _ ihp ihq => exact fun cutoff => .imp (ihp cutoff) (ihq cutoff)
  | not _ ihp => exact fun cutoff => .not (ihp cutoff)
  | eq _ _ iha ihb => exact fun cutoff => .eq (iha cutoff) (ihb cutoff)
  | all _ _ ihA ihb => exact fun cutoff => .all (ihA cutoff) (ihb (cutoff + 1))
  | ex _ _ ihA ihb => exact fun cutoff => .ex (ihA cutoff) (ihb (cutoff + 1))
  | @beta A b b' x x' _ _ ihb ihx =>
      intro cutoff
      have key : shiftAt cutoff (substAt 0 x' b') =
          substAt 0 (shiftAt cutoff x') (shiftAt (cutoff + 1) b') :=
        shiftAt_substAt x' b' cutoff 0
      show ParA
        (Expr.app (Expr.lam (shiftAt cutoff A) (shiftAt (cutoff + 1) b)) (shiftAt cutoff x))
        (shiftAt cutoff (substAt 0 x' b'))
      rw [key]
      exact ParA.beta (ihb (cutoff + 1)) (ihx cutoff)
  | addZero _ ihx => exact fun cutoff => ParA.addZero (ihx cutoff)
  | addSucc _ _ ihx ihy => exact fun cutoff => ParA.addSucc (ihx cutoff) (ihy cutoff)

theorem parA_shiftN {e e' : AExpr} (h : ParA e e') :
    ∀ count : Nat, ParA (shiftN count e) (shiftN count e')
  | 0 => h
  | count + 1 => parA_shift (parA_shiftN h count) 0

/-- Parallel steps in the argument and in the body give a parallel step of the instance. -/
theorem parA_subst {a a' : AExpr} (ha : ParA a a') {b b' : AExpr} (hb : ParA b b') :
    ∀ k : Nat, ParA (substAt k a b) (substAt k a' b') := by
  induction hb with
  | bvar i =>
      intro k
      rcases Nat.lt_trichotomy i k with below | same | above
      · rw [substAt_bvar_lt a below, substAt_bvar_lt a' below]
        exact .bvar i
      · subst same
        rw [substAt_bvar_eq, substAt_bvar_eq]
        exact parA_shiftN ha i
      · rw [substAt_bvar_gt a above, substAt_bvar_gt a' above]
        exact .bvar _
  | univ => exact fun _ => .univ
  | prop => exact fun _ => .prop
  | base b => exact fun _ => .base b
  | pi _ _ ihA ihB => exact fun k => .pi (ihA k) (ihB (k + 1))
  | lam _ _ ihA ihb => exact fun k => .lam (ihA k) (ihb (k + 1))
  | app _ _ ihf ihx => exact fun k => .app (ihf k) (ihx k)
  | const τ c => exact fun _ => .const τ c
  | tyFam b => exact fun _ => .tyFam b
  | top => exact fun _ => .top
  | bot => exact fun _ => .bot
  | and _ _ ihp ihq => exact fun k => .and (ihp k) (ihq k)
  | or _ _ ihp ihq => exact fun k => .or (ihp k) (ihq k)
  | imp _ _ ihp ihq => exact fun k => .imp (ihp k) (ihq k)
  | not _ ihp => exact fun k => .not (ihp k)
  | eq _ _ ihx ihy => exact fun k => .eq (ihx k) (ihy k)
  | all _ _ ihA ihb => exact fun k => .all (ihA k) (ihb (k + 1))
  | ex _ _ ihA ihb => exact fun k => .ex (ihA k) (ihb (k + 1))
  | @beta A body body' x x' _ _ ihb ihx =>
      intro k
      have key : substAt k a' (substAt 0 x' body') =
          substAt 0 (substAt k a' x') (substAt (k + 1) a' body') :=
        substAt_substAt a' x' body' k 0
      show ParA
        (Expr.app (Expr.lam (substAt k a A) (substAt (k + 1) a body)) (substAt k a x))
        (substAt k a' (substAt 0 x' body'))
      rw [key]
      exact ParA.beta (ihb (k + 1)) (ihx k)
  | addZero _ ihx => exact fun k => ParA.addZero (ihx k)
  | addSucc _ _ ihx ihy => exact fun k => ParA.addSucc (ihx k) (ihy k)

/-! ## Complete developments -/

/-- The complete development for β with the recursion equations. -/
def devA : AExpr → AExpr
  | .app (.app (.const _ .add) x) (.const _ .zero) => devA x
  | .app (.app (.const _ .add) x) (.app (.const _ .succ) y) =>
      .app (.const _ .succ) (.app (.app (.const _ .add) (devA x)) (devA y))
  | .app (.lam _ b) a => substAt 0 (devA a) (devA b)
  | .app f a => .app (devA f) (devA a)
  | .bvar i => .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (devA A) (devA B)
  | .lam A b => .lam (devA A) (devA b)
  | .const τ c => .const τ c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (devA p) (devA q)
  | .or p q => .or (devA p) (devA q)
  | .imp p q => .imp (devA p) (devA q)
  | .not p => .not (devA p)
  | .eq a b => .eq (devA a) (devA b)
  | .all A b => .all (devA A) (devA b)
  | .ex A b => .ex (devA A) (devA b)

/-- **The triangle**: every parallel reduct of a term makes a parallel step to the complete
development of the term. -/
theorem parA_dev {e e' : AExpr} (h : ParA e e') : ParA e' (devA e) := by
  induction h with
  | bvar i => exact .bvar i
  | univ => exact .univ
  | prop => exact .prop
  | base b => exact .base b
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | app hf ha ihf iha =>
      cases hf with
      | lam _ _ =>
          have ihf' : ParA (Expr.lam _ _) (Expr.lam (devA _) (devA _)) := ihf
          cases ihf' with
          | lam _ hb => exact ParA.beta hb iha
      | app hg _ =>
          cases hg with
          | const τ c =>
              cases c with
              | add =>
                  cases ha with
                  | const τ' c' =>
                      cases c' with
                      | zero =>
                          have ihf' : ParA (Expr.app (Expr.const _ ArithConst.add) _)
                              (Expr.app (Expr.const _ ArithConst.add) (devA _)) := ihf
                          cases ihf' with
                          | app _ hx' => exact ParA.addZero hx'
                      | _ => exact ParA.app ihf iha
                  | app hs _ =>
                      cases hs with
                      | const τ' c' =>
                          cases c' with
                          | succ =>
                              have ihf' : ParA (Expr.app (Expr.const _ ArithConst.add) _)
                                  (Expr.app (Expr.const _ ArithConst.add) (devA _)) := ihf
                              have iha' : ParA (Expr.app (Expr.const _ ArithConst.succ) _)
                                  (Expr.app (Expr.const _ ArithConst.succ) (devA _)) := iha
                              cases ihf' with
                              | app _ hx' =>
                                  cases iha' with
                                  | app _ hy' => exact ParA.addSucc hx' hy'
                          | _ => exact ParA.app ihf iha
                      | _ => exact ParA.app ihf iha
                  | _ => exact ParA.app ihf iha
              | _ => exact ParA.app ihf iha
          | _ => exact ParA.app ihf iha
      | _ => exact ParA.app ihf iha
  | const τ c => exact .const τ c
  | tyFam b => exact .tyFam b
  | top => exact .top
  | bot => exact .bot
  | and _ _ ihp ihq => exact .and ihp ihq
  | or _ _ ihp ihq => exact .or ihp ihq
  | imp _ _ ihp ihq => exact .imp ihp ihq
  | not _ ihp => exact .not ihp
  | eq _ _ iha ihb => exact .eq iha ihb
  | all _ _ ihA ihb => exact .all ihA ihb
  | ex _ _ ihA ihb => exact .ex ihA ihb
  | beta _ _ ihb iha => exact parA_subst iha ihb 0
  | addZero _ ihx => exact ihx
  | addSucc _ _ ihx ihy =>
      exact ParA.app (ParA.const _ _) (ParA.app (ParA.app (ParA.const _ _) ihx) ihy)

theorem parAStar_of_reduces {e e' : AExpr}
    (reduced : Relation.ReflTransGen (Rewrite (withBeta Rule)) e e') :
    Relation.ReflTransGen ParA e e' := by
  induction reduced with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (parA_of_rewrite step)

theorem reduces_of_parAStar {e e' : AExpr} (reduced : Relation.ReflTransGen ParA e e') :
    Relation.ReflTransGen (Rewrite (withBeta Rule)) e e' := by
  induction reduced with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (reduces_of_parA step)

/-- **β together with the recursion equations of addition is confluent.** -/
theorem joint_confluent : Confluent (Rewrite (withBeta Rule)) := by
  intro source left right toLeft toRight
  obtain ⟨common, fromLeft, fromRight⟩ :=
    Relation.church_rosser
      (fun a _ _ first second =>
        ⟨devA a, Relation.ReflGen.single (parA_dev first),
          Relation.ReflTransGen.single (parA_dev second)⟩)
      (parAStar_of_reduces toLeft) (parAStar_of_reduces toRight)
  exact ⟨common, reduces_of_parAStar fromLeft, reduces_of_parAStar fromRight⟩

/-- **The bubble that declares β and the recursion equations of addition is admitted for
typing.** -/
theorem joint_admitted : TypingAdmission (withBeta Rule) :=
  joint_admitted_of_confluent joint_confluent

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleBetaConfluence.Controls

/-- **β and the recursion equations work together**: `Vec ((λ m. m + 0) n)` converts with
`Vec n`. -/
theorem identity_plus_zero_converts :
    Convertible (withBeta Rule)
      (vec (Expr.app (Expr.lam natType (addE (bvar 0) zeroE)) (bvar 1))) (vec (bvar 1)) :=
  Relation.EqvGen.trans _ (vec (addE (bvar 1) zeroE)) _
    (Relation.EqvGen.rel _ _
      (Rewrite.appArgument
        (Rewrite.root (Or.inl (Beta.contract natType (addE (bvar 0) zeroE) (bvar 1))))))
    (Relation.EqvGen.rel _ _
      (Rewrite.appArgument (Rewrite.root (Or.inr (Rule.addZero (bvar 1))))))

/-- **In the joint bubble a term has one type up to conversion.** -/
theorem joint_types_unique {Γ : List AExpr} {e A B : AExpr}
    (first : HasTypeInside (withBeta Rule) Γ e A)
    (second : HasTypeInside (withBeta Rule) Γ e B) : Convertible (withBeta Rule) A B :=
  joint_admitted.unique first second

/-- **The joint bubble is admitted for typing and does not meet the convergence criterion**: the
self-application makes a step to itself. -/
theorem joint_not_convergent :
    TypingAdmission (withBeta Rule) ∧ ¬ Convergent (Rewrite (withBeta Rule)) :=
  ⟨joint_admitted, fun convergent =>
    not_acc_of_loop
      (show Rewrite (withBeta Rule) loop loop from
        Rewrite.root (Or.inl (Beta.contract natType (Expr.app (bvar 0) (bvar 0)) selfApply)))
      (convergent.terminating loop)⟩

end Controls

/-! ## Axiom audit -/

#print axioms rule_keeps_types_in
#print axioms joint_admitted_of_confluent
#print axioms parA_subst
#print axioms parA_dev
#print axioms joint_confluent
#print axioms joint_admitted
#print axioms Controls.identity_plus_zero_converts
#print axioms Controls.joint_types_unique
#print axioms Controls.joint_not_convergent

end Mettapedia.TypeTheory.BubbleArithBetaConfluence
