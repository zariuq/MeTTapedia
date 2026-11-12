import Mettapedia.TypeTheory.BubbleTypingAdmission
import Mettapedia.TypeTheory.PromotionAdmission.Criterion

/-!
# β is confluent on the comparison core, so the bubble of β is admitted for typing

`BubbleBetaTyping` and `BubbleTypingAdmission` reduce the good behaviour of typing with β as a
conversion to one fact: β is confluent. This module proves it, by parallel reduction and complete
developments.

* `Par` is parallel β reduction, `dev` the complete development, `par_dev` the triangle: every
  parallel reduct of a term makes a parallel step to the development of the term.
* `beta_confluent`: β steps at any position are confluent.
* `beta_admitted`: the bubble whose only declared step is β is admitted for typing. With β as the
  conversion at every node, the comparison core has unique types up to conversion, weakening,
  substitution and subject reduction (`BubbleTypingAdmission.TypingAdmission`).

The proof uses the commutation laws of shifting and substitution
(`KnowledgeSubstitution.shiftAt_substAt`, `KnowledgeSubstitution.substAt_substAt`).

## Controls

* `Controls.beta_in_the_bubble_keeps_the_type`: with β declared, the step from `g ((λ m. m) 0)` to
  `g 0` keeps the type `Vec ((λ m. m) 0)`. In the arithmetic bubble, where β is a computation and
  not a conversion, the same step loses it
  (`BubbleBetaTyping.Controls.computation_outside_conversion_breaks_types`).
* `Controls.beta_admitted_not_convergent`: β is admitted for typing and is not terminating on raw
  terms (`Controls.loop_steps_to_itself`), so it does not meet the convergence criterion that
  decides conversion by normal forms. Admission for typing and the decision of conversion are two
  obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleBetaConfluence

open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.TypeTheory.BubbleSubjectReduction
open Mettapedia.TypeTheory.BubbleBetaTyping
open Mettapedia.TypeTheory.BubbleTypingAdmission
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.TypeTheory.PromotionAdmission (Terminating Convergent)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Mettapedia.Logic.Relation (Confluent)
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Parallel reduction -/

/-- Parallel β reduction: any set of the redexes present in a term, contracted at once. -/
inductive Par : Expr Base Const → Expr Base Const → Prop where
  | bvar (i : Nat) : Par (Expr.bvar i) (Expr.bvar i)
  | univ : Par Expr.univ Expr.univ
  | prop : Par Expr.prop Expr.prop
  | base (b : Base) : Par (Expr.base b) (Expr.base b)
  | pi {A A' B B' : Expr Base Const} : Par A A' → Par B B' → Par (Expr.pi A B) (Expr.pi A' B')
  | lam {A A' b b' : Expr Base Const} : Par A A' → Par b b' → Par (Expr.lam A b) (Expr.lam A' b')
  | app {f f' a a' : Expr Base Const} : Par f f' → Par a a' → Par (Expr.app f a) (Expr.app f' a')
  | const (τ : Ty Base) (c : Const τ) : Par (Expr.const τ c) (Expr.const τ c)
  | tyFam (b : Base) : Par (Expr.tyFam b) (Expr.tyFam b)
  | top : Par Expr.top Expr.top
  | bot : Par Expr.bot Expr.bot
  | and {p p' q q' : Expr Base Const} : Par p p' → Par q q' → Par (Expr.and p q) (Expr.and p' q')
  | or {p p' q q' : Expr Base Const} : Par p p' → Par q q' → Par (Expr.or p q) (Expr.or p' q')
  | imp {p p' q q' : Expr Base Const} : Par p p' → Par q q' → Par (Expr.imp p q) (Expr.imp p' q')
  | not {p p' : Expr Base Const} : Par p p' → Par (Expr.not p) (Expr.not p')
  | eq {a a' b b' : Expr Base Const} : Par a a' → Par b b' → Par (Expr.eq a b) (Expr.eq a' b')
  | all {A A' b b' : Expr Base Const} : Par A A' → Par b b' → Par (Expr.all A b) (Expr.all A' b')
  | ex {A A' b b' : Expr Base Const} : Par A A' → Par b b' → Par (Expr.ex A b) (Expr.ex A' b')
  | beta {A b b' a a' : Expr Base Const} :
      Par b b' → Par a a' → Par (Expr.app (Expr.lam A b) a) (substAt 0 a' b')

theorem par_refl : ∀ e : Expr Base Const, Par e e
  | .bvar i => .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (par_refl A) (par_refl B)
  | .lam A b => .lam (par_refl A) (par_refl b)
  | .app f a => .app (par_refl f) (par_refl a)
  | .const τ c => .const τ c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (par_refl p) (par_refl q)
  | .or p q => .or (par_refl p) (par_refl q)
  | .imp p q => .imp (par_refl p) (par_refl q)
  | .not p => .not (par_refl p)
  | .eq a b => .eq (par_refl a) (par_refl b)
  | .all A b => .all (par_refl A) (par_refl b)
  | .ex A b => .ex (par_refl A) (par_refl b)

/-- A β step at any position is a parallel step. -/
theorem par_of_rewrite {e e' : Expr Base Const} (step : Rewrite Beta e e') : Par e e' := by
  induction step with
  | root rule =>
      cases rule with
      | contract A b a => exact Par.beta (par_refl b) (par_refl a)
  | piDomain _ ih => exact .pi ih (par_refl _)
  | piBody _ ih => exact .pi (par_refl _) ih
  | lamDomain _ ih => exact .lam ih (par_refl _)
  | lamBody _ ih => exact .lam (par_refl _) ih
  | appFunction _ ih => exact .app ih (par_refl _)
  | appArgument _ ih => exact .app (par_refl _) ih
  | andLeft _ ih => exact .and ih (par_refl _)
  | andRight _ ih => exact .and (par_refl _) ih
  | orLeft _ ih => exact .or ih (par_refl _)
  | orRight _ ih => exact .or (par_refl _) ih
  | impLeft _ ih => exact .imp ih (par_refl _)
  | impRight _ ih => exact .imp (par_refl _) ih
  | notBody _ ih => exact .not ih
  | eqLeft _ ih => exact .eq ih (par_refl _)
  | eqRight _ ih => exact .eq (par_refl _) ih
  | allDomain _ ih => exact .all ih (par_refl _)
  | allBody _ ih => exact .all (par_refl _) ih
  | exDomain _ ih => exact .ex ih (par_refl _)
  | exBody _ ih => exact .ex (par_refl _) ih

theorem reduces_congr {rules : Expr Base Const → Expr Base Const → Prop}
    (wrap : Expr Base Const → Expr Base Const)
    (lift : ∀ x y, Rewrite rules x y → Rewrite rules (wrap x) (wrap y)) {x y : Expr Base Const}
    (reduced : Relation.ReflTransGen (Rewrite rules) x y) :
    Relation.ReflTransGen (Rewrite rules) (wrap x) (wrap y) := by
  induction reduced with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (lift _ _ step)

theorem reduces_congr₂ {rules : Expr Base Const → Expr Base Const → Prop}
    (former : Expr Base Const → Expr Base Const → Expr Base Const)
    (left : ∀ x x' y, Rewrite rules x x' → Rewrite rules (former x y) (former x' y))
    (right : ∀ x y y', Rewrite rules y y' → Rewrite rules (former x y) (former x y'))
    {x x' y y' : Expr Base Const} (first : Relation.ReflTransGen (Rewrite rules) x x')
    (second : Relation.ReflTransGen (Rewrite rules) y y') :
    Relation.ReflTransGen (Rewrite rules) (former x y) (former x' y') :=
  (reduces_congr (fun z => former z y) (fun _ _ step => left _ _ _ step) first).trans
    (reduces_congr (fun z => former x' z) (fun _ _ step => right _ _ _ step) second)

/-- A parallel step is a sequence of β steps. -/
theorem reduces_of_par {e e' : Expr Base Const} (h : Par e e') :
    Relation.ReflTransGen (Rewrite Beta) e e' := by
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
        (Rewrite.root (Beta.contract A b' x'))

/-- Parallel steps are stable under shifting. -/
theorem par_shift {e e' : Expr Base Const} (h : Par e e') :
    ∀ cutoff : Nat, Par (shiftAt cutoff e) (shiftAt cutoff e') := by
  induction h with
  | bvar i => exact fun _ => par_refl _
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
      show Par
        (Expr.app (Expr.lam (shiftAt cutoff A) (shiftAt (cutoff + 1) b)) (shiftAt cutoff x))
        (shiftAt cutoff (substAt 0 x' b'))
      rw [key]
      exact Par.beta (ihb (cutoff + 1)) (ihx cutoff)

theorem par_shiftN {e e' : Expr Base Const} (h : Par e e') :
    ∀ count : Nat, Par (shiftN count e) (shiftN count e')
  | 0 => h
  | count + 1 => par_shift (par_shiftN h count) 0

/-- Parallel steps in the argument and in the body give a parallel step of the instance. -/
theorem par_subst {a a' : Expr Base Const} (ha : Par a a') {b b' : Expr Base Const}
    (hb : Par b b') : ∀ k : Nat, Par (substAt k a b) (substAt k a' b') := by
  induction hb with
  | bvar i =>
      intro k
      rcases Nat.lt_trichotomy i k with below | same | above
      · rw [substAt_bvar_lt a below, substAt_bvar_lt a' below]
        exact .bvar i
      · subst same
        rw [substAt_bvar_eq, substAt_bvar_eq]
        exact par_shiftN ha i
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
      show Par
        (Expr.app (Expr.lam (substAt k a A) (substAt (k + 1) a body)) (substAt k a x))
        (substAt k a' (substAt 0 x' body'))
      rw [key]
      exact Par.beta (ihb (k + 1)) (ihx k)

/-! ## Complete developments -/

/-- The complete development: every β redex present in the term, contracted. -/
def dev : Expr Base Const → Expr Base Const
  | .app (.lam _ b) a => substAt 0 (dev a) (dev b)
  | .app f a => .app (dev f) (dev a)
  | .bvar i => .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (dev A) (dev B)
  | .lam A b => .lam (dev A) (dev b)
  | .const τ c => .const τ c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (dev p) (dev q)
  | .or p q => .or (dev p) (dev q)
  | .imp p q => .imp (dev p) (dev q)
  | .not p => .not (dev p)
  | .eq a b => .eq (dev a) (dev b)
  | .all A b => .all (dev A) (dev b)
  | .ex A b => .ex (dev A) (dev b)

/-- **The triangle**: every parallel reduct of a term makes a parallel step to the complete
development of the term. -/
theorem par_dev {e e' : Expr Base Const} (h : Par e e') : Par e' (dev e) := by
  induction h with
  | bvar i => exact .bvar i
  | univ => exact .univ
  | prop => exact .prop
  | base b => exact .base b
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | app hf _ ihf iha =>
      cases hf with
      | lam _ _ =>
          have ihf' : Par (Expr.lam _ _) (Expr.lam (dev _) (dev _)) := ihf
          cases ihf' with
          | lam _ hb => exact Par.beta hb iha
      | _ => exact Par.app ihf iha
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
  | beta _ _ ihb iha => exact par_subst iha ihb 0

theorem parStar_of_reduces {e e' : Expr Base Const}
    (reduced : Relation.ReflTransGen (Rewrite Beta) e e') : Relation.ReflTransGen Par e e' := by
  induction reduced with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (par_of_rewrite step)

theorem reduces_of_parStar {e e' : Expr Base Const} (reduced : Relation.ReflTransGen Par e e') :
    Relation.ReflTransGen (Rewrite Beta) e e' := by
  induction reduced with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans (reduces_of_par step)

/-- **β is confluent on the comparison core.** -/
theorem beta_confluent :
    Confluent (Rewrite (Beta : Expr Base Const → Expr Base Const → Prop)) := by
  intro source left right toLeft toRight
  obtain ⟨common, fromLeft, fromRight⟩ :=
    Relation.church_rosser
      (fun a _ _ first second =>
        ⟨dev a, Relation.ReflGen.single (par_dev first),
          Relation.ReflTransGen.single (par_dev second)⟩)
      (parStar_of_reduces toLeft) (parStar_of_reduces toRight)
  exact ⟨common, reduces_of_parStar fromLeft, reduces_of_parStar fromRight⟩

/-! ## The bubble of β is admitted for typing -/

/-- β does not rewrite a product at the root. -/
theorem beta_noPiRule (A B right : Expr Base Const) : ¬ Beta (Expr.pi A B) right := by
  intro rule
  cases rule

/-- **β keeps types** in the bubble whose conversion is β. -/
theorem beta_preservesTypes :
    PreservesTypes (Beta : Expr Base Const → Expr Base Const → Prop) := by
  intro Γ left right T rule typed
  cases rule with
  | contract A b a =>
      exact beta_keeps_type beta_substStable beta_shiftStable
        (coherent_convertible beta_substStable
          (piCodomainInjective_of_confluent beta_confluent beta_noPiRule))
        (piDomainInjective_of_confluent beta_confluent beta_noPiRule) typed

/-- **The comparison core with β as its conversion is admitted for typing.** -/
theorem beta_admitted : TypingAdmission (Beta : Expr Base Const → Expr Base Const → Prop) :=
  TypingAdmission.of_confluent beta_substStable beta_shiftStable beta_confluent beta_noPiRule
    beta_preservesTypes

/-- A step that leads back to its source is not accessible. -/
theorem not_acc_of_loop {α : Type u} {r : α → α → Prop} {x : α} (again : r x x) :
    ¬ Acc (fun target source => r source target) x := by
  intro accessible
  induction accessible with
  | intro y _ ih => exact ih y again again

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleBetaTyping.Controls

/-- `g ((λ m. m) 0)` is typed at `Vec ((λ m. m) 0)` by the global judgment. -/
theorem applied_global :
    HasType familyContext (Expr.app (bvar 0) identityAtZero) (vec identityAtZero) :=
  HasType.app (A := natType) (B := vec (bvar 0)) (HasType.var (Γ := familyContext) (i := 0) rfl)
    (HasType.app (A := natType) (B := natType)
      (HasType.lam (HasType.base ()) (HasType.var (Γ := natType :: familyContext) (i := 0) rfl))
      (HasType.const _ ArithConst.zero))

/-- **With β declared, the step that lost the type keeps it**: `g 0` is typed at
`Vec ((λ m. m) 0)` in the bubble of β. -/
theorem beta_in_the_bubble_keeps_the_type :
    HasTypeInside Beta familyContext (Expr.app (bvar 0) zeroE) (vec identityAtZero) :=
  beta_admitted.reduces (Typed.of_hasType applied_global)
    (Relation.ReflTransGen.single
      (Rewrite.appArgument (Rewrite.root (Beta.contract natType (bvar 0) zeroE))))

/-- The self-application `λ (x : nat). x x`. -/
def selfApply : AExpr := Expr.lam natType (Expr.app (bvar 0) (bvar 0))

/-- The term `(λ x. x x) (λ x. x x)`. -/
def loop : AExpr := Expr.app selfApply selfApply

/-- The term makes a β step to itself. -/
theorem loop_steps_to_itself : Rewrite Beta loop loop :=
  Rewrite.root (Beta.contract natType (Expr.app (bvar 0) (bvar 0)) selfApply)

/-- β is not terminating on raw terms. -/
theorem beta_not_terminating : ¬ Terminating (Rewrite (Beta : AExpr → AExpr → Prop)) :=
  fun terminating => not_acc_of_loop loop_steps_to_itself (terminating loop)

/-- **β is admitted for typing and does not meet the convergence criterion.** -/
theorem beta_admitted_not_convergent :
    TypingAdmission (Beta : AExpr → AExpr → Prop) ∧
      ¬ Convergent (Rewrite (Beta : AExpr → AExpr → Prop)) :=
  ⟨beta_admitted, fun convergent => beta_not_terminating convergent.terminating⟩

end Controls

/-! ## Axiom audit -/

#print axioms par_subst
#print axioms par_dev
#print axioms beta_confluent
#print axioms beta_preservesTypes
#print axioms beta_admitted
#print axioms Controls.beta_in_the_bubble_keeps_the_type
#print axioms Controls.loop_steps_to_itself
#print axioms Controls.beta_not_terminating
#print axioms Controls.beta_admitted_not_convergent

end Mettapedia.TypeTheory.BubbleBetaConfluence
