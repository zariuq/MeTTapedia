import Mettapedia.TypeTheory.KnowledgeSubstitution
import Mettapedia.TypeTheory.BubbleTypingAlgorithmic

/-!
# A term that computes keeps its type

The declared steps of a bubble are used in two ways. Read on types, they are the conversion that
the typing judgment may use. Read on terms, they are the computation of the program. This module
proves that the two readings fit.

* `subject_reduction`: when every rule keeps the type of its left side (`PreservesTypes`) and the
  rules are stable under shifting, a term typed in the bubble, with the conversion rule at every
  node, keeps its type under a step at any position.
* `subject_reduction_star`: the same for any number of steps.

The proof is by induction on the typing. A step in the domain of a binder changes the context of
the body, and `typed_replace` moves the body to the new context. A step in the argument of an
application changes the type of the application, and `convertible_substAt_arg` converts it back.
Both use the conversion rule inside the term: the root-only judgment cannot state this theorem.

`PreservesTypes` is one obligation per rule. Stability of the rules under shifting does not imply
it: the second control is a rule with one and not the other.

## Controls

* `Controls.rule_preservesTypes`, `Controls.arith_subject_reduction`: the recursion equations of
  addition keep types, so the arithmetic bubble has subject reduction.
* `Controls.zeroToNat_breaks_subject_reduction`: the rule that rewrites the number zero to the
  type of numbers is stable under shifting (`Controls.zeroToNat_shiftStable`), and it sends the
  typed term `0 : nat` to `nat`, which is not typed at `nat`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleSubjectReduction

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Conversion is a congruence -/

theorem convertible_congr {rules : Expr Base Const → Expr Base Const → Prop}
    (wrap : Expr Base Const → Expr Base Const)
    (lift : ∀ x y, Rewrite rules x y → Rewrite rules (wrap x) (wrap y)) {x y : Expr Base Const}
    (converted : Convertible rules x y) : Convertible rules (wrap x) (wrap y) := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (lift _ _ step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

theorem convertible_congr₂ {rules : Expr Base Const → Expr Base Const → Prop}
    (former : Expr Base Const → Expr Base Const → Expr Base Const)
    (left : ∀ x x' y, Rewrite rules x x' → Rewrite rules (former x y) (former x' y))
    (right : ∀ x y y', Rewrite rules y y' → Rewrite rules (former x y) (former x y'))
    {x x' y y' : Expr Base Const} (first : Convertible rules x x')
    (second : Convertible rules y y') : Convertible rules (former x y) (former x' y') :=
  Relation.EqvGen.trans _ _ _
    (convertible_congr (fun z => former z y) (fun _ _ step => left _ _ _ step) first)
    (convertible_congr (fun z => former x' z) (fun _ _ step => right _ _ _ step) second)

/-- **Convertible arguments give convertible instances.** -/
theorem convertible_substAt_arg {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {a a' : Expr Base Const} (converted : Convertible rules a a') :
    ∀ (B : Expr Base Const) (k : Nat), Convertible rules (substAt k a B) (substAt k a' B)
  | .bvar i, k => by
      rcases Nat.lt_trichotomy i k with below | same | above
      · rw [substAt_bvar_lt a below, substAt_bvar_lt a' below]
        exact Relation.EqvGen.refl _
      · subst same
        rw [substAt_bvar_eq, substAt_bvar_eq]
        exact convertible_shiftN stable converted i
      · rw [substAt_bvar_gt a above, substAt_bvar_gt a' above]
        exact Relation.EqvGen.refl _
  | .univ, _ => Relation.EqvGen.refl _
  | .prop, _ => Relation.EqvGen.refl _
  | .base _, _ => Relation.EqvGen.refl _
  | .pi A B, k =>
      convertible_congr₂ Expr.pi (fun _ _ _ step => .piDomain step)
        (fun _ _ _ step => .piBody step) (convertible_substAt_arg stable converted A k)
        (convertible_substAt_arg stable converted B (k + 1))
  | .lam A b, k =>
      convertible_congr₂ Expr.lam (fun _ _ _ step => .lamDomain step)
        (fun _ _ _ step => .lamBody step) (convertible_substAt_arg stable converted A k)
        (convertible_substAt_arg stable converted b (k + 1))
  | .app f x, k =>
      convertible_congr₂ Expr.app (fun _ _ _ step => .appFunction step)
        (fun _ _ _ step => .appArgument step) (convertible_substAt_arg stable converted f k)
        (convertible_substAt_arg stable converted x k)
  | .const _ _, _ => Relation.EqvGen.refl _
  | .tyFam _, _ => Relation.EqvGen.refl _
  | .top, _ => Relation.EqvGen.refl _
  | .bot, _ => Relation.EqvGen.refl _
  | .and p q, k =>
      convertible_congr₂ Expr.and (fun _ _ _ step => .andLeft step)
        (fun _ _ _ step => .andRight step) (convertible_substAt_arg stable converted p k)
        (convertible_substAt_arg stable converted q k)
  | .or p q, k =>
      convertible_congr₂ Expr.or (fun _ _ _ step => .orLeft step)
        (fun _ _ _ step => .orRight step) (convertible_substAt_arg stable converted p k)
        (convertible_substAt_arg stable converted q k)
  | .imp p q, k =>
      convertible_congr₂ Expr.imp (fun _ _ _ step => .impLeft step)
        (fun _ _ _ step => .impRight step) (convertible_substAt_arg stable converted p k)
        (convertible_substAt_arg stable converted q k)
  | .not p, k =>
      convertible_congr Expr.not (fun _ _ step => .notBody step)
        (convertible_substAt_arg stable converted p k)
  | .eq x y, k =>
      convertible_congr₂ Expr.eq (fun _ _ _ step => .eqLeft step)
        (fun _ _ _ step => .eqRight step) (convertible_substAt_arg stable converted x k)
        (convertible_substAt_arg stable converted y k)
  | .all A b, k =>
      convertible_congr₂ Expr.all (fun _ _ _ step => .allDomain step)
        (fun _ _ _ step => .allBody step) (convertible_substAt_arg stable converted A k)
        (convertible_substAt_arg stable converted b (k + 1))
  | .ex A b, k =>
      convertible_congr₂ Expr.ex (fun _ _ _ step => .exDomain step)
        (fun _ _ _ step => .exBody step) (convertible_substAt_arg stable converted A k)
        (convertible_substAt_arg stable converted b (k + 1))

/-! ## Moving a typing to a context with a moved entry -/

/-- A variable of a context with one entry replaced: the replaced entry, or the same variable. -/
theorem lookup_replace (A A' : Expr Base Const) (Γ : List (Expr Base Const)) :
    ∀ (Δ : List (Expr Base Const)) (i : Nat) (T : Expr Base Const),
      (Δ ++ A :: Γ)[i]? = some T →
        (T = A ∧ (Δ ++ A' :: Γ)[i]? = some A') ∨ (Δ ++ A' :: Γ)[i]? = some T
  | [], 0, T, lookup => by
      obtain rfl : A = T := Option.some.inj lookup
      exact Or.inl ⟨rfl, rfl⟩
  | [], _ + 1, _, lookup => Or.inr lookup
  | _ :: _, 0, _, lookup => Or.inr lookup
  | _ :: Δ, i + 1, T, lookup => lookup_replace A A' Γ Δ i T lookup

/-- **A typing moves to a context with a moved entry**: when the new entry moves back to the old
one under every number of binders, what was typed stays typed at the same type. -/
theorem typed_replace {moves : Expr Base Const → Expr Base Const → Prop}
    {A A' : Expr Base Const} (back : ∀ count : Nat, moves (shiftN count A') (shiftN count A))
    {Γ₀ : List (Expr Base Const)} {e T : Expr Base Const} (typed : Typed moves Γ₀ e T) :
    ∀ (Δ Γ : List (Expr Base Const)), Γ₀ = Δ ++ A :: Γ → Typed moves (Δ ++ A' :: Γ) e T := by
  induction typed with
  | @var Γ₀ i T lookup =>
      intro Δ Γ split
      subst split
      rcases lookup_replace A A' Γ Δ i T lookup with ⟨same, lookup'⟩ | lookup'
      · rw [same]
        exact .move (.var lookup') (back (i + 1))
      · exact .var lookup'
  | base b => exact fun _ _ _ => .base b
  | prop => exact fun _ _ _ => .prop
  | @pi Γ₀ A₀ B _ _ ihA ihB =>
      exact fun Δ Γ split => .pi (ihA Δ Γ split) (ihB (A₀ :: Δ) Γ (by rw [split]; rfl))
  | @lam Γ₀ A₀ b B _ _ ihA ihb =>
      exact fun Δ Γ split => .lam (ihA Δ Γ split) (ihb (A₀ :: Δ) Γ (by rw [split]; rfl))
  | app _ _ ihf iha => exact fun Δ Γ split => .app (ihf Δ Γ split) (iha Δ Γ split)
  | const τ c => exact fun _ _ _ => .const τ c
  | tyFam b => exact fun _ _ _ => .tyFam b
  | top => exact fun _ _ _ => .top
  | bot => exact fun _ _ _ => .bot
  | and _ _ ihp ihq => exact fun Δ Γ split => .and (ihp Δ Γ split) (ihq Δ Γ split)
  | or _ _ ihp ihq => exact fun Δ Γ split => .or (ihp Δ Γ split) (ihq Δ Γ split)
  | imp _ _ ihp ihq => exact fun Δ Γ split => .imp (ihp Δ Γ split) (ihq Δ Γ split)
  | not _ ihp => exact fun Δ Γ split => .not (ihp Δ Γ split)
  | eq _ _ iha ihb => exact fun Δ Γ split => .eq (iha Δ Γ split) (ihb Δ Γ split)
  | @all Γ₀ A₀ b _ _ ihA ihb =>
      exact fun Δ Γ split => .all (ihA Δ Γ split) (ihb (A₀ :: Δ) Γ (by rw [split]; rfl))
  | @ex Γ₀ A₀ b _ _ ihA ihb =>
      exact fun Δ Γ split => .ex (ihA Δ Γ split) (ihb (A₀ :: Δ) Γ (by rw [split]; rfl))
  | move _ moved ih => exact fun Δ Γ split => .move (ih Δ Γ split) moved

/-- A typing in a bubble moves to the context whose newest entry has made one step. -/
theorem typed_step_context {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {A A' : Expr Base Const} (step : Rewrite rules A A')
    {Γ : List (Expr Base Const)} {e T : Expr Base Const}
    (typed : HasTypeInside rules (A :: Γ) e T) : HasTypeInside rules (A' :: Γ) e T :=
  typed_replace (A := A) (A' := A')
    (fun count =>
      convertible_shiftN stable (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ step)) count)
    typed [] Γ rfl

/-! ## Subject reduction -/

/-- Every rule keeps the type of its left side, in every context. -/
def PreservesTypes (rules : Expr Base Const → Expr Base Const → Prop) : Prop :=
  ∀ (Γ : List (Expr Base Const)) (left right A : Expr Base Const), rules left right →
    HasTypeInside rules Γ left A → HasTypeInside rules Γ right A

/-- **Subject reduction.** In a bubble whose rules keep types at the root and are stable under
shifting, a typed term keeps its type under a step at any position. -/
theorem subject_reduction {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) (preserves : PreservesTypes rules)
    {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typed : Typed (Convertible rules) Γ e A) :
    ∀ e' : Expr Base Const, Rewrite rules e e' → Typed (Convertible rules) Γ e' A := by
  induction typed with
  | var lookup =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.var lookup)
  | base b =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.base b)
  | prop =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule .prop
  | pi dA dB ihA ihB =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.pi dA dB)
      | piDomain inner => exact .pi (ihA _ inner) (typed_step_context stable inner dB)
      | piBody inner => exact .pi dA (ihB _ inner)
  | lam dA db ihA ihb =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.lam dA db)
      | lamDomain inner =>
          exact .move (.lam (ihA _ inner) (typed_step_context stable inner db))
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Rewrite.piDomain inner)))
      | lamBody inner => exact .lam dA (ihb _ inner)
  | app df da ihf iha =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.app df da)
      | appFunction inner => exact .app (ihf _ inner) da
      | appArgument inner =>
          exact .move (.app df (iha _ inner))
            (convertible_substAt_arg stable
              (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ inner)) _ 0)
  | const τ c =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.const τ c)
  | tyFam b =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.tyFam b)
  | top =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule .top
  | bot =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule .bot
  | and dp dq ihp ihq =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.and dp dq)
      | andLeft inner => exact .and (ihp _ inner) dq
      | andRight inner => exact .and dp (ihq _ inner)
  | or dp dq ihp ihq =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.or dp dq)
      | orLeft inner => exact .or (ihp _ inner) dq
      | orRight inner => exact .or dp (ihq _ inner)
  | imp dp dq ihp ihq =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.imp dp dq)
      | impLeft inner => exact .imp (ihp _ inner) dq
      | impRight inner => exact .imp dp (ihq _ inner)
  | not dp ihp =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.not dp)
      | notBody inner => exact .not (ihp _ inner)
  | eq da db iha ihb =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.eq da db)
      | eqLeft inner => exact .eq (iha _ inner) db
      | eqRight inner => exact .eq da (ihb _ inner)
  | all dA db ihA ihb =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.all dA db)
      | allDomain inner => exact .all (ihA _ inner) (typed_step_context stable inner db)
      | allBody inner => exact .all dA (ihb _ inner)
  | ex dA db ihA ihb =>
      intro e' step
      cases step with
      | root rule => exact preserves _ _ _ _ rule (.ex dA db)
      | exDomain inner => exact .ex (ihA _ inner) (typed_step_context stable inner db)
      | exBody inner => exact .ex dA (ihb _ inner)
  | move _ converted ih => exact fun e' step => .move (ih e' step) converted

/-- **Subject reduction along any number of steps.** -/
theorem subject_reduction_star {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) (preserves : PreservesTypes rules)
    {Γ : List (Expr Base Const)} {e e' A : Expr Base Const}
    (typed : HasTypeInside rules Γ e A)
    (reduced : Relation.ReflTransGen (Rewrite rules) e e') : HasTypeInside rules Γ e' A := by
  induction reduced with
  | refl => exact typed
  | tail _ step ih => exact subject_reduction stable preserves ih _ step

/-! ## Reading a typing backwards -/

/-- A typed application has a function typed at a product and an argument typed at its domain. -/
theorem typed_app_inv {moves : Expr Base Const → Expr Base Const → Prop}
    (coherent : Coherent moves) {Γ : List (Expr Base Const)} {f a T : Expr Base Const}
    (typed : Typed moves Γ (Expr.app f a) T) :
    ∃ A B, Typed moves Γ f (Expr.pi A B) ∧ Typed moves Γ a A ∧ moves (substAt 0 a B) T := by
  obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed
  cases synth with
  | app synthf atF syntha atA =>
      exact ⟨_, _, .move synthf.typed atF, .move syntha.typed atA, moved⟩

/-- The type of a constant moves to every type the constant is typed at. -/
theorem typed_const_inv {moves : Expr Base Const → Expr Base Const → Prop}
    (coherent : Coherent moves) {Γ : List (Expr Base Const)} {τ : Ty Base} {c : Const τ}
    {T : Expr Base Const} (typed : Typed moves Γ (Expr.const τ c) T) : moves (tyToExpr τ) T := by
  obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed
  cases synth
  exact moved

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic.Controls
open Mettapedia.TypeTheory.KnowledgeUnderBinders.Controls

/-- The conversion of the recursion equations of addition is coherent. -/
theorem coherentRule : Coherent (Convertible Rule) := arith_coherent false

/-- Convertible products have convertible domains, by normal forms. -/
theorem arith_piDomain {A B A' B' : AExpr}
    (converted : Convertible Rule (Expr.pi A B) (Expr.pi A' B')) : Convertible Rule A A' := by
  have same : Expr.pi (Arith.norm false A) (Arith.norm false B) =
      Expr.pi (Arith.norm false A') (Arith.norm false B') := (conv_iff_norm false).mp converted
  exact (conv_iff_norm false).mpr (Expr.pi.inj same).1

theorem arith_piCodomain {A B A' B' : AExpr}
    (converted : Convertible Rule (Expr.pi A B) (Expr.pi A' B')) : Convertible Rule B B' :=
  arith_piCodomainInjective false A B A' B' converted

/-- A typed successor has a number below it and is a number. -/
theorem succ_inv {Γ : List AExpr} {y T : AExpr} (typed : HasTypeInside Rule Γ (succE y) T) :
    HasTypeInside Rule Γ y natType ∧ Convertible Rule natType T := by
  obtain ⟨A, B, typedC, typedY, atT⟩ := typed_app_inv coherentRule typed
  have atC : Convertible Rule (Expr.pi natType natType) (Expr.pi A B) :=
    typed_const_inv coherentRule typedC
  have domain : Convertible Rule natType A := arith_piDomain atC
  have codomain : Convertible Rule natType B := arith_piCodomain atC
  exact ⟨Typed.move typedY (Relation.EqvGen.symm _ _ domain),
    Relation.EqvGen.trans _ _ _ (convertible_substAt rule_stable codomain 0 y) atT⟩

/-- A typed sum has two numbers below it and is a number. -/
theorem add_inv {Γ : List AExpr} {x y T : AExpr} (typed : HasTypeInside Rule Γ (addE x y) T) :
    HasTypeInside Rule Γ x natType ∧ HasTypeInside Rule Γ y natType ∧
      Convertible Rule natType T := by
  obtain ⟨A, B, typedF, typedY, atT⟩ := typed_app_inv coherentRule typed
  obtain ⟨A₁, B₁, typedC, typedX, atF⟩ := typed_app_inv coherentRule typedF
  have atC : Convertible Rule (Expr.pi natType (Expr.pi natType natType)) (Expr.pi A₁ B₁) :=
    typed_const_inv coherentRule typedC
  have domain₁ : Convertible Rule natType A₁ := arith_piDomain atC
  have codomain₁ : Convertible Rule (Expr.pi natType natType) B₁ := arith_piCodomain atC
  have applied : Convertible Rule (Expr.pi natType natType) (Expr.pi A B) :=
    Relation.EqvGen.trans _ _ _ (convertible_substAt rule_stable codomain₁ 0 x) atF
  have domain₂ : Convertible Rule natType A := arith_piDomain applied
  have codomain₂ : Convertible Rule natType B := arith_piCodomain applied
  exact ⟨Typed.move typedX (Relation.EqvGen.symm _ _ domain₁),
    Typed.move typedY (Relation.EqvGen.symm _ _ domain₂),
    Relation.EqvGen.trans _ _ _ (convertible_substAt rule_stable codomain₂ 0 y) atT⟩

theorem succ_typed {Γ : List AExpr} {y : AExpr} (typedY : HasTypeInside Rule Γ y natType) :
    HasTypeInside Rule Γ (succE y) natType :=
  Typed.app (A := natType) (B := natType) (Typed.const _ ArithConst.succ) typedY

theorem add_typed {Γ : List AExpr} {x y : AExpr} (typedX : HasTypeInside Rule Γ x natType)
    (typedY : HasTypeInside Rule Γ y natType) : HasTypeInside Rule Γ (addE x y) natType :=
  Typed.app (A := natType) (B := natType)
    (Typed.app (A := natType) (B := Expr.pi natType natType) (Typed.const _ ArithConst.add)
      typedX)
    typedY

/-- **The recursion equations of addition keep types.** -/
theorem rule_preservesTypes : PreservesTypes Rule := by
  intro Γ left right T rule typed
  cases rule with
  | addZero =>
      obtain ⟨typedLeft, _, atT⟩ := add_inv typed
      exact Typed.move typedLeft atT
  | addSucc =>
      obtain ⟨typedLeft, typedSucc, atT⟩ := add_inv typed
      obtain ⟨typedRight, _⟩ := succ_inv typedSucc
      exact Typed.move (succ_typed (add_typed typedLeft typedRight)) atT

/-- **The arithmetic bubble has subject reduction**: a typed term keeps its type along any
computation by the recursion equations, at any position. -/
theorem arith_subject_reduction {Γ : List AExpr} {e e' A : AExpr}
    (typed : HasTypeInside Rule Γ e A) (reduced : Relation.ReflTransGen (Rewrite Rule) e e') :
    HasTypeInside Rule Γ e' A :=
  subject_reduction_star rule_shiftStable rule_preservesTypes typed reduced

/-- A rule that rewrites the number zero to the type of numbers. -/
inductive ZeroToNat : AExpr → AExpr → Prop where
  | collapse : ZeroToNat zeroE natType

/-- The rule is stable under shifting: both sides are closed. -/
theorem zeroToNat_shiftStable : ShiftStable ZeroToNat := by
  intro left right rule cutoff
  cases rule
  exact ZeroToNat.collapse

/-- Every constant read as the type of numbers. -/
def constToBase : AExpr → AExpr
  | .bvar i => .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (constToBase A) (constToBase B)
  | .lam A b => .lam (constToBase A) (constToBase b)
  | .app f a => .app (constToBase f) (constToBase a)
  | .const _ _ => .base ()
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (constToBase p) (constToBase q)
  | .or p q => .or (constToBase p) (constToBase q)
  | .imp p q => .imp (constToBase p) (constToBase q)
  | .not p => .not (constToBase p)
  | .eq a b => .eq (constToBase a) (constToBase b)
  | .all A b => .all (constToBase A) (constToBase b)
  | .ex A b => .ex (constToBase A) (constToBase b)

theorem constToBase_step {e e' : AExpr} (step : Rewrite ZeroToNat e e') :
    constToBase e = constToBase e' := by
  induction step with
  | root rule =>
      cases rule
      rfl
  | piDomain _ ih => simp only [constToBase, ih]
  | piBody _ ih => simp only [constToBase, ih]
  | lamDomain _ ih => simp only [constToBase, ih]
  | lamBody _ ih => simp only [constToBase, ih]
  | appFunction _ ih => simp only [constToBase, ih]
  | appArgument _ ih => simp only [constToBase, ih]
  | andLeft _ ih => simp only [constToBase, ih]
  | andRight _ ih => simp only [constToBase, ih]
  | orLeft _ ih => simp only [constToBase, ih]
  | orRight _ ih => simp only [constToBase, ih]
  | impLeft _ ih => simp only [constToBase, ih]
  | impRight _ ih => simp only [constToBase, ih]
  | notBody _ ih => simp only [constToBase, ih]
  | eqLeft _ ih => simp only [constToBase, ih]
  | eqRight _ ih => simp only [constToBase, ih]
  | allDomain _ ih => simp only [constToBase, ih]
  | allBody _ ih => simp only [constToBase, ih]
  | exDomain _ ih => simp only [constToBase, ih]
  | exBody _ ih => simp only [constToBase, ih]

theorem constToBase_conv {e e' : AExpr} (converted : Convertible ZeroToNat e e') :
    constToBase e = constToBase e' := by
  induction converted with
  | rel _ _ step => exact constToBase_step step
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Every type of the type of numbers reads as the universe. -/
theorem base_typed_at {Γ : List AExpr} {e T : AExpr}
    (typed : Typed (Convertible ZeroToNat) Γ e T) :
    e = Expr.base () → constToBase T = Expr.univ := by
  induction typed with
  | var _ => intro same; cases same
  | base _ => intro _; rfl
  | prop => intro same; cases same
  | pi _ _ _ _ => intro same; cases same
  | lam _ _ _ _ => intro same; cases same
  | app _ _ _ _ => intro same; cases same
  | const _ _ => intro same; cases same
  | tyFam _ => intro same; cases same
  | top => intro same; cases same
  | bot => intro same; cases same
  | and _ _ _ _ => intro same; cases same
  | or _ _ _ _ => intro same; cases same
  | imp _ _ _ _ => intro same; cases same
  | not _ _ => intro same; cases same
  | eq _ _ _ _ => intro same; cases same
  | all _ _ _ _ => intro same; cases same
  | ex _ _ _ _ => intro same; cases same
  | move _ converted ih =>
      intro same
      rw [← constToBase_conv converted]
      exact ih same

/-- **A rule that does not keep types breaks subject reduction.** In the bubble of the rule
`0 ↦ nat`, the term `0` is typed at `nat` and makes a step to `nat`, which is not typed at
`nat`. -/
theorem zeroToNat_breaks_subject_reduction :
    HasTypeInside ZeroToNat [] zeroE natType ∧ Rewrite ZeroToNat zeroE natType ∧
      ¬ HasTypeInside ZeroToNat [] natType natType := by
  refine ⟨Typed.const _ ArithConst.zero, Rewrite.root ZeroToNat.collapse, ?_⟩
  intro typed
  have atUniv := base_typed_at typed rfl
  simp [constToBase, natType] at atUniv

/-- The rule `0 ↦ nat` does not keep types. -/
theorem zeroToNat_not_preserving : ¬ PreservesTypes ZeroToNat := by
  intro preserves
  obtain ⟨typed, _, refused⟩ := zeroToNat_breaks_subject_reduction
  exact refused (preserves [] zeroE natType natType ZeroToNat.collapse typed)

end Controls

/-! ## Axiom audit -/

#print axioms convertible_substAt_arg
#print axioms typed_replace
#print axioms typed_step_context
#print axioms subject_reduction
#print axioms subject_reduction_star
#print axioms typed_app_inv
#print axioms typed_const_inv
#print axioms Controls.rule_preservesTypes
#print axioms Controls.arith_subject_reduction
#print axioms Controls.zeroToNat_shiftStable
#print axioms Controls.zeroToNat_breaks_subject_reduction
#print axioms Controls.zeroToNat_not_preserving

end Mettapedia.TypeTheory.BubbleSubjectReduction
