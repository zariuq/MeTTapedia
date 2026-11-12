import Mettapedia.TypeTheory.KnowledgeUnderBinders
import Mettapedia.Logic.Relation.Normalization

/-!
# Where a typing asks for a conversion, and uniqueness of types up to conversion

`BubbleTypingInside.Typed moves` has a movement rule at every node: a derivation may change the
type of any subterm at any time. This module gives the judgment in which a movement is asked for
only where a rule needs one, and proves that nothing is lost.

* `Synth moves` is the syntax-directed judgment. Each rule asks for one movement per premise whose
  type the rule constrains: the function of an application has to move to a product, the argument
  to the domain, a domain to the universe, a proposition to `prop`, the two sides of an equation
  to each other. No other movement is used.
* `typed_iff_synth`: for a coherent movement relation, a term is typed at `T` exactly when the
  syntax-directed judgment gives it a type that moves to `T`.
* `typed_unique`: for a coherent movement relation, any two types of a term move to each other.
* `hasTypeInside_iff_synth_run`: in a bubble, a term is typed exactly when the syntax-directed
  judgment types it with every ask answered by a run of the bubble's conversion step.

`Coherent` names the laws used: an equivalence, a congruence for the codomain of a product, stable
under substitution, and with convertible products having convertible codomains. For the conversion
of a bubble the first three hold when the rules are stable under substitution
(`coherent_convertible`). The last one is the content:

* `piCodomainInjective_of_confluent`: it holds in a confluent bubble with no rule that rewrites a
  product at the root.
* `Controls.arith_piCodomainInjective`: it holds in the arithmetic bubbles, by normal forms.
* `Controls.product_knowledge_two_types`: it fails at a frame that assumes an equation between two
  products. There one term has two types that the frame does not convert. Types are unique at a
  frame with knowledge only when the frame's knowledge respects the codomains of products.

For a frame whose knowledge the bubble proves, uniqueness is inherited
(`typedKnowing_unique_of_sound`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleTypingAlgorithmic

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingRuns
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Mettapedia.Logic.Relation (Confluent)
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## The syntax-directed judgment -/

/-- Typing of the comparison core with a movement asked for only where a rule constrains the type
of a premise. -/
inductive Synth (moves : Expr Base Const → Expr Base Const → Prop) :
    List (Expr Base Const) → Expr Base Const → Expr Base Const → Prop where
  | var {Γ : List (Expr Base Const)} {i : Nat} {A : Expr Base Const}
      (lookup : Γ[i]? = some A) : Synth moves Γ (bvar i) (shiftN (i + 1) A)
  | base {Γ : List (Expr Base Const)} (b : Base) : Synth moves Γ (Expr.base b) univ
  | prop {Γ : List (Expr Base Const)} : Synth moves Γ Expr.prop univ
  | pi {Γ : List (Expr Base Const)} {A B S S' : Expr Base Const} :
      Synth moves Γ A S → moves S univ → Synth moves (A :: Γ) B S' → moves S' univ →
        Synth moves Γ (Expr.pi A B) univ
  | lam {Γ : List (Expr Base Const)} {A b B S : Expr Base Const} :
      Synth moves Γ A S → moves S univ → Synth moves (A :: Γ) b B →
        Synth moves Γ (Expr.lam A b) (Expr.pi A B)
  | app {Γ : List (Expr Base Const)} {f a F A A' B : Expr Base Const} :
      Synth moves Γ f F → moves F (Expr.pi A B) → Synth moves Γ a A' → moves A' A →
        Synth moves Γ (Expr.app f a) (substAt 0 a B)
  | const {Γ : List (Expr Base Const)} (τ : Ty Base) (c : Const τ) :
      Synth moves Γ (Expr.const τ c) (tyToExpr τ)
  | tyFam {Γ : List (Expr Base Const)} (b : Base) :
      Synth moves Γ (Expr.tyFam b) (Expr.pi (Expr.base b) univ)
  | top {Γ : List (Expr Base Const)} : Synth moves Γ Expr.top Expr.prop
  | bot {Γ : List (Expr Base Const)} : Synth moves Γ Expr.bot Expr.prop
  | and {Γ : List (Expr Base Const)} {p q P Q : Expr Base Const} :
      Synth moves Γ p P → moves P Expr.prop → Synth moves Γ q Q → moves Q Expr.prop →
        Synth moves Γ (Expr.and p q) Expr.prop
  | or {Γ : List (Expr Base Const)} {p q P Q : Expr Base Const} :
      Synth moves Γ p P → moves P Expr.prop → Synth moves Γ q Q → moves Q Expr.prop →
        Synth moves Γ (Expr.or p q) Expr.prop
  | imp {Γ : List (Expr Base Const)} {p q P Q : Expr Base Const} :
      Synth moves Γ p P → moves P Expr.prop → Synth moves Γ q Q → moves Q Expr.prop →
        Synth moves Γ (Expr.imp p q) Expr.prop
  | not {Γ : List (Expr Base Const)} {p P : Expr Base Const} :
      Synth moves Γ p P → moves P Expr.prop → Synth moves Γ (Expr.not p) Expr.prop
  | eq {Γ : List (Expr Base Const)} {a b A B : Expr Base Const} :
      Synth moves Γ a A → Synth moves Γ b B → moves A B → Synth moves Γ (Expr.eq a b) Expr.prop
  | all {Γ : List (Expr Base Const)} {A b S P : Expr Base Const} :
      Synth moves Γ A S → moves S univ → Synth moves (A :: Γ) b P → moves P Expr.prop →
        Synth moves Γ (Expr.all A b) Expr.prop
  | ex {Γ : List (Expr Base Const)} {A b S P : Expr Base Const} :
      Synth moves Γ A S → moves S univ → Synth moves (A :: Γ) b P → moves P Expr.prop →
        Synth moves Γ (Expr.ex A b) Expr.prop

/-- More movements, more syntax-directed typings. -/
theorem Synth.mono {small large : Expr Base Const → Expr Base Const → Prop}
    (included : ∀ A B, small A B → large A B) {Γ : List (Expr Base Const)}
    {e A : Expr Base Const} (synth : Synth small Γ e A) : Synth large Γ e A := by
  induction synth with
  | var lookup => exact .var lookup
  | base b => exact .base b
  | prop => exact .prop
  | pi _ atA _ atB ihA ihB => exact .pi ihA (included _ _ atA) ihB (included _ _ atB)
  | lam _ atA _ ihA ihb => exact .lam ihA (included _ _ atA) ihb
  | app _ atF _ atA ihf iha => exact .app ihf (included _ _ atF) iha (included _ _ atA)
  | const τ c => exact .const τ c
  | tyFam b => exact .tyFam b
  | top => exact .top
  | bot => exact .bot
  | and _ atP _ atQ ihp ihq => exact .and ihp (included _ _ atP) ihq (included _ _ atQ)
  | or _ atP _ atQ ihp ihq => exact .or ihp (included _ _ atP) ihq (included _ _ atQ)
  | imp _ atP _ atQ ihp ihq => exact .imp ihp (included _ _ atP) ihq (included _ _ atQ)
  | not _ atP ihp => exact .not ihp (included _ _ atP)
  | eq _ _ same iha ihb => exact .eq iha ihb (included _ _ same)
  | all _ atA _ atP ihA ihb => exact .all ihA (included _ _ atA) ihb (included _ _ atP)
  | ex _ atA _ atP ihA ihb => exact .ex ihA (included _ _ atA) ihb (included _ _ atP)

/-- A syntax-directed typing is a typing: each ask is one use of the movement rule. -/
theorem Synth.typed {moves : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} (synth : Synth moves Γ e A) :
    Typed moves Γ e A := by
  induction synth with
  | var lookup => exact .var lookup
  | base b => exact .base b
  | prop => exact .prop
  | pi _ atA _ atB ihA ihB => exact .pi (.move ihA atA) (.move ihB atB)
  | lam _ atA _ ihA ihb => exact .lam (.move ihA atA) ihb
  | app _ atF _ atA ihf iha => exact .app (.move ihf atF) (.move iha atA)
  | const τ c => exact .const τ c
  | tyFam b => exact .tyFam b
  | top => exact .top
  | bot => exact .bot
  | and _ atP _ atQ ihp ihq => exact .and (.move ihp atP) (.move ihq atQ)
  | or _ atP _ atQ ihp ihq => exact .or (.move ihp atP) (.move ihq atQ)
  | imp _ atP _ atQ ihp ihq => exact .imp (.move ihp atP) (.move ihq atQ)
  | not _ atP ihp => exact .not (.move ihp atP)
  | eq _ _ same iha ihb => exact .eq (.move iha same) ihb
  | all _ atA _ atP ihA ihb => exact .all (.move ihA atA) (.move ihb atP)
  | ex _ atA _ atP ihA ihb => exact .ex (.move ihA atA) (.move ihb atP)

/-! ## Coherent movement -/

/-- The laws of a movement relation under which the movement rule is needed only where a rule
asks, and types are unique up to movement. -/
structure Coherent (moves : Expr Base Const → Expr Base Const → Prop) : Prop where
  /-- Every type moves to itself. -/
  refl : ∀ A, moves A A
  /-- Movement goes both ways. -/
  symm : ∀ A B, moves A B → moves B A
  /-- Movements compose. -/
  trans : ∀ A B C, moves A B → moves B C → moves A C
  /-- Movement of a codomain is movement of the product. -/
  piBody : ∀ A B B', moves B B' → moves (Expr.pi A B) (Expr.pi A B')
  /-- Products that move to each other have codomains that move to each other. -/
  piCodomain : ∀ A B A' B', moves (Expr.pi A B) (Expr.pi A' B') → moves B B'
  /-- Movement is stable under the substitution of an argument. -/
  subst : ∀ a B B', moves B B' → moves (substAt 0 a B) (substAt 0 a B')

/-- **Every typing has a syntax-directed typing below it.** -/
theorem synth_of_typed {moves : Expr Base Const → Expr Base Const → Prop}
    (coherent : Coherent moves) {Γ : List (Expr Base Const)} {e T : Expr Base Const}
    (typed : Typed moves Γ e T) : ∃ A, Synth moves Γ e A ∧ moves A T := by
  induction typed with
  | var lookup => exact ⟨_, Synth.var lookup, coherent.refl _⟩
  | base b => exact ⟨_, Synth.base b, coherent.refl _⟩
  | prop => exact ⟨_, Synth.prop, coherent.refl _⟩
  | pi _ _ ihA ihB =>
      obtain ⟨_, synthA, atA⟩ := ihA
      obtain ⟨_, synthB, atB⟩ := ihB
      exact ⟨_, Synth.pi synthA atA synthB atB, coherent.refl _⟩
  | lam _ _ ihA ihb =>
      obtain ⟨_, synthA, atA⟩ := ihA
      obtain ⟨_, synthb, atB⟩ := ihb
      exact ⟨_, Synth.lam synthA atA synthb, coherent.piBody _ _ _ atB⟩
  | app _ _ ihf iha =>
      obtain ⟨_, synthf, atF⟩ := ihf
      obtain ⟨_, syntha, atA⟩ := iha
      exact ⟨_, Synth.app synthf atF syntha atA, coherent.refl _⟩
  | const τ c => exact ⟨_, Synth.const τ c, coherent.refl _⟩
  | tyFam b => exact ⟨_, Synth.tyFam b, coherent.refl _⟩
  | top => exact ⟨_, Synth.top, coherent.refl _⟩
  | bot => exact ⟨_, Synth.bot, coherent.refl _⟩
  | and _ _ ihp ihq =>
      obtain ⟨_, synthp, atP⟩ := ihp
      obtain ⟨_, synthq, atQ⟩ := ihq
      exact ⟨_, Synth.and synthp atP synthq atQ, coherent.refl _⟩
  | or _ _ ihp ihq =>
      obtain ⟨_, synthp, atP⟩ := ihp
      obtain ⟨_, synthq, atQ⟩ := ihq
      exact ⟨_, Synth.or synthp atP synthq atQ, coherent.refl _⟩
  | imp _ _ ihp ihq =>
      obtain ⟨_, synthp, atP⟩ := ihp
      obtain ⟨_, synthq, atQ⟩ := ihq
      exact ⟨_, Synth.imp synthp atP synthq atQ, coherent.refl _⟩
  | not _ ihp =>
      obtain ⟨_, synthp, atP⟩ := ihp
      exact ⟨_, Synth.not synthp atP, coherent.refl _⟩
  | eq _ _ iha ihb =>
      obtain ⟨_, syntha, atA⟩ := iha
      obtain ⟨_, synthb, atB⟩ := ihb
      exact ⟨_, Synth.eq syntha synthb (coherent.trans _ _ _ atA (coherent.symm _ _ atB)),
        coherent.refl _⟩
  | all _ _ ihA ihb =>
      obtain ⟨_, synthA, atA⟩ := ihA
      obtain ⟨_, synthb, atP⟩ := ihb
      exact ⟨_, Synth.all synthA atA synthb atP, coherent.refl _⟩
  | ex _ _ ihA ihb =>
      obtain ⟨_, synthA, atA⟩ := ihA
      obtain ⟨_, synthb, atP⟩ := ihb
      exact ⟨_, Synth.ex synthA atA synthb atP, coherent.refl _⟩
  | move _ moved ih =>
      obtain ⟨A₀, synth, atA⟩ := ih
      exact ⟨A₀, synth, coherent.trans _ _ _ atA moved⟩

/-- **The movement rule is needed only where a rule asks.** For a coherent movement relation, a
term is typed at `T` exactly when the syntax-directed judgment gives it a type that moves to
`T`. -/
theorem typed_iff_synth {moves : Expr Base Const → Expr Base Const → Prop}
    (coherent : Coherent moves) {Γ : List (Expr Base Const)} {e T : Expr Base Const} :
    Typed moves Γ e T ↔ ∃ A, Synth moves Γ e A ∧ moves A T :=
  ⟨synth_of_typed coherent, fun ⟨_, synth, moved⟩ => .move synth.typed moved⟩

/-- The syntax-directed types of a term move to each other. -/
theorem synth_unique {moves : Expr Base Const → Expr Base Const → Prop}
    (coherent : Coherent moves) {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (first : Synth moves Γ e A) : ∀ {B : Expr Base Const}, Synth moves Γ e B → moves A B := by
  induction first with
  | var lookup =>
      intro B second
      cases second with
      | var lookup' =>
          obtain rfl := Option.some.inj (lookup.symm.trans lookup')
          exact coherent.refl _
  | base b => intro B second; cases second; exact coherent.refl _
  | prop => intro B second; cases second; exact coherent.refl _
  | pi _ _ _ _ _ _ => intro B second; cases second; exact coherent.refl _
  | lam _ _ _ _ ihb =>
      intro B second
      cases second with
      | lam _ _ synthb => exact coherent.piBody _ _ _ (ihb synthb)
  | app _ atF _ _ ihf _ =>
      intro B second
      cases second with
      | app synthf atF' _ _ =>
          exact coherent.subst _ _ _
            (coherent.piCodomain _ _ _ _
              (coherent.trans _ _ _ (coherent.symm _ _ atF)
                (coherent.trans _ _ _ (ihf synthf) atF')))
  | const τ c => intro B second; cases second; exact coherent.refl _
  | tyFam b => intro B second; cases second; exact coherent.refl _
  | top => intro B second; cases second; exact coherent.refl _
  | bot => intro B second; cases second; exact coherent.refl _
  | and _ _ _ _ _ _ => intro B second; cases second; exact coherent.refl _
  | or _ _ _ _ _ _ => intro B second; cases second; exact coherent.refl _
  | imp _ _ _ _ _ _ => intro B second; cases second; exact coherent.refl _
  | not _ _ _ => intro B second; cases second; exact coherent.refl _
  | eq _ _ _ _ _ => intro B second; cases second; exact coherent.refl _
  | all _ _ _ _ _ _ => intro B second; cases second; exact coherent.refl _
  | ex _ _ _ _ _ _ => intro B second; cases second; exact coherent.refl _

/-- **Types are unique up to movement.** For a coherent movement relation, any two types of a
term, in derivations that use the movement rule anywhere, move to each other. -/
theorem typed_unique {moves : Expr Base Const → Expr Base Const → Prop}
    (coherent : Coherent moves) {Γ : List (Expr Base Const)} {e A B : Expr Base Const}
    (first : Typed moves Γ e A) (second : Typed moves Γ e B) : moves A B := by
  obtain ⟨A₀, synthA, atA⟩ := synth_of_typed coherent first
  obtain ⟨B₀, synthB, atB⟩ := synth_of_typed coherent second
  exact coherent.trans _ _ _ (coherent.symm _ _ atA)
    (coherent.trans _ _ _ (synth_unique coherent synthA synthB) atB)

/-! ## The conversion of a bubble -/

/-- Conversion of a codomain is conversion of the product. -/
theorem convertible_piBody {rules : Expr Base Const → Expr Base Const → Prop}
    (A : Expr Base Const) {B B' : Expr Base Const} (converted : Convertible rules B B') :
    Convertible rules (Expr.pi A B) (Expr.pi A B') := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (Rewrite.piBody step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- Convertible products have convertible codomains. -/
def PiCodomainInjective (rules : Expr Base Const → Expr Base Const → Prop) : Prop :=
  ∀ A B A' B' : Expr Base Const, Convertible rules (Expr.pi A B) (Expr.pi A' B') →
    Convertible rules B B'

/-- The conversion of a bubble whose rules are stable under substitution is coherent as soon as
convertible products have convertible codomains. -/
theorem coherent_convertible {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : SubstitutionStable rules) (injective : PiCodomainInjective rules) :
    Coherent (Convertible rules) where
  refl := Relation.EqvGen.refl
  symm := Relation.EqvGen.symm
  trans := Relation.EqvGen.trans
  piBody := fun A _ _ converted => convertible_piBody A converted
  piCodomain := injective
  subst := fun a _ _ converted => convertible_substAt stable converted 0 a

theorem convertible_of_reduces {rules : Expr Base Const → Expr Base Const → Prop}
    {e e' : Expr Base Const} (reduced : Relation.ReflTransGen (Rewrite rules) e e') :
    Convertible rules e e' := by
  induction reduced with
  | refl => exact Relation.EqvGen.refl _
  | tail _ step ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ step)

/-- When no rule rewrites a product at the root, a reduct of a product is a product of
reducts. -/
theorem reduct_of_pi {rules : Expr Base Const → Expr Base Const → Prop}
    (noPiRule : ∀ A B right, ¬ rules (Expr.pi A B) right) {A B reduct : Expr Base Const}
    (reduced : Relation.ReflTransGen (Rewrite rules) (Expr.pi A B) reduct) :
    ∃ A' B', reduct = Expr.pi A' B' ∧ Relation.ReflTransGen (Rewrite rules) A A' ∧
      Relation.ReflTransGen (Rewrite rules) B B' := by
  induction reduced with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨A', B', rfl, toA, toB⟩ := ih
      cases step with
      | root rule => exact absurd rule (noPiRule _ _ _)
      | piDomain inner => exact ⟨_, B', rfl, toA.tail inner, toB⟩
      | piBody inner => exact ⟨A', _, rfl, toA, toB.tail inner⟩

/-- **In a confluent bubble with no rule that rewrites a product at the root, convertible products
have convertible codomains.** -/
theorem piCodomainInjective_of_confluent {rules : Expr Base Const → Expr Base Const → Prop}
    (confluent : Confluent (Rewrite rules))
    (noPiRule : ∀ A B right, ¬ rules (Expr.pi A B) right) : PiCodomainInjective rules := by
  intro A B A' B' converted
  obtain ⟨common, fromLeft, fromRight⟩ := confluent.eqvGen_iff_join.mp converted
  obtain ⟨_, B₁, rfl, _, toB⟩ := reduct_of_pi noPiRule fromLeft
  obtain ⟨_, B₂, same, _, toB'⟩ := reduct_of_pi noPiRule fromRight
  obtain ⟨_, rfl⟩ := Expr.pi.inj same
  exact Relation.EqvGen.trans _ _ _ (convertible_of_reduces toB)
    (Relation.EqvGen.symm _ _ (convertible_of_reduces toB'))

/-- **Types are unique up to conversion in a confluent bubble** whose rules are stable under
substitution and do not rewrite a product at the root, with the conversion rule at every node. -/
theorem hasTypeInside_unique {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : SubstitutionStable rules) (confluent : Confluent (Rewrite rules))
    (noPiRule : ∀ A B right, ¬ rules (Expr.pi A B) right) {Γ : List (Expr Base Const)}
    {e A B : Expr Base Const} (first : HasTypeInside rules Γ e A)
    (second : HasTypeInside rules Γ e B) : Convertible rules A B :=
  typed_unique (coherent_convertible stable (piCodomainInjective_of_confluent confluent noPiRule))
    first second

/-- **Every ask is answered by a run.** In a bubble with coherent conversion, a term is typed with
the conversion rule at every node exactly when the syntax-directed judgment types it with each
ask answered by a run of the bubble's conversion step. -/
theorem hasTypeInside_iff_synth_run {rules : Expr Base Const → Expr Base Const → Prop}
    (coherent : Coherent (Convertible rules)) {Γ : List (Expr Base Const)}
    {e T : Expr Base Const} :
    HasTypeInside rules Γ e T ↔ ∃ A, Synth (Reaches rules) Γ e A ∧ Reaches rules A T := by
  constructor
  · intro typed
    obtain ⟨A, synth, moved⟩ := synth_of_typed coherent typed
    exact ⟨A, synth.mono fun _ _ converted => (convertible_iff_run [] 0).mp converted,
      (convertible_iff_run [] 0).mp moved⟩
  · rintro ⟨A, synth, reached⟩
    exact .move (synth.mono fun _ _ ran => (convertible_iff_run [] 0).mpr ran).typed
      ((convertible_iff_run [] 0).mpr reached)

/-- **At a frame whose knowledge the bubble proves, types are unique up to the bubble's
conversion.** -/
theorem typedKnowing_unique_of_sound {rules : Expr Base Const → Expr Base Const → Prop}
    (shiftStable : ShiftStable rules) (coherent : Coherent (Convertible rules))
    {store : EquationStore (Expr Base Const)}
    (sound : ∀ equation ∈ store, Convertible rules equation.1 equation.2)
    {Γ : List (Expr Base Const)} {e A B : Expr Base Const}
    (first : TypedKnowing rules store Γ e A) (second : TypedKnowing rules store Γ e B) :
    Convertible rules A B :=
  typed_unique coherent (typedKnowing_discharge shiftStable first sound)
    (typedKnowing_discharge shiftStable second sound)

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- **In the arithmetic bubbles, convertible products have convertible codomains**: normal forms
are computed componentwise on a product. -/
theorem arith_piCodomainInjective (plus : Bool) : PiCodomainInjective (bubbleRules plus) := by
  intro A B A' B' converted
  have same : Expr.pi (Arith.norm plus A) (Arith.norm plus B) =
      Expr.pi (Arith.norm plus A') (Arith.norm plus B') := (conv_iff_norm plus).mp converted
  exact (conv_iff_norm plus).mpr (Expr.pi.inj same).2

/-- The conversion of an arithmetic bubble is coherent. -/
theorem arith_coherent (plus : Bool) : Coherent (Convertible (bubbleRules plus)) :=
  coherent_convertible (bubbleRules_stable plus) (arith_piCodomainInjective plus)

/-- **In the arithmetic bubbles a term has one type up to conversion**, with the conversion rule
at every node, and so one normal type. -/
theorem arith_normal_type_unique (plus : Bool) {Γ : List AExpr} {e A B : AExpr}
    (first : HasTypeInside (bubbleRules plus) Γ e A)
    (second : HasTypeInside (bubbleRules plus) Γ e B) : Arith.norm plus A = Arith.norm plus B :=
  (conv_iff_norm plus).mp (typed_unique (arith_coherent plus) first second)

/-- With no declared step, uniqueness up to conversion is uniqueness. -/
theorem none_types_unique {Γ : List AExpr} {e A B : AExpr}
    (first : HasTypeInside (fun _ _ => False) Γ e A)
    (second : HasTypeInside (fun _ _ => False) Γ e B) : A = B :=
  convertible_none_iff.mp
    (typed_unique
      (coherent_convertible (fun _ _ rule => rule.elim) (fun _ _ _ _ converted =>
        convertible_none_iff.mpr (Expr.pi.inj (convertible_none_iff.mp converted)).2))
      first second)

/-- The knowledge that two products with different codomains are equal:
`Π (m : nat). Vec 0 ≐ Π (m : nat). Vec 1`. -/
def productKnowledge : EquationStore AExpr :=
  [(Expr.pi natType (vec zeroE), Expr.pi natType (vec (succE zeroE)))]

/-- The context `f : Π (m : nat). Vec 0`. -/
def functionContext : List AExpr := [Expr.pi natType (vec zeroE)]

/-- At the frame, `f 0` is typed at `Vec 0`. -/
theorem applied_at_zero :
    TypedKnowing (fun _ _ => False) productKnowledge functionContext
      (Expr.app (bvar 0) zeroE) (vec zeroE) :=
  TypedKnowing.app (A := natType) (B := vec zeroE)
    (TypedKnowing.var (Γ := functionContext) (i := 0) rfl) (TypedKnowing.const _ ArithConst.zero)

/-- At the frame, `f 0` is also typed at `Vec 1`: the knowledge moves the type of `f`. -/
theorem applied_at_one :
    TypedKnowing (fun _ _ => False) productKnowledge functionContext
      (Expr.app (bvar 0) zeroE) (vec (succE zeroE)) :=
  TypedKnowing.app (A := natType) (B := vec (succE zeroE))
    (TypedKnowing.move (TypedKnowing.var (Γ := functionContext) (i := 0) rfl)
      (Relation.EqvGen.rel _ _
        (RewriteUnder.root
          (Or.inr ⟨(Expr.pi natType (vec zeroE), Expr.pi natType (vec (succE zeroE))),
            List.mem_singleton_self _, rfl, rfl⟩))))
    (TypedKnowing.const _ ArithConst.zero)

/-- Forget the codomain of every product. -/
def forgetCodomain : AExpr → AExpr
  | .bvar i => .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A _ => .pi (forgetCodomain A) .prop
  | .lam A b => .lam (forgetCodomain A) (forgetCodomain b)
  | .app f a => .app (forgetCodomain f) (forgetCodomain a)
  | .const τ c => .const τ c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (forgetCodomain p) (forgetCodomain q)
  | .or p q => .or (forgetCodomain p) (forgetCodomain q)
  | .imp p q => .imp (forgetCodomain p) (forgetCodomain q)
  | .not p => .not (forgetCodomain p)
  | .eq a b => .eq (forgetCodomain a) (forgetCodomain b)
  | .all A b => .all (forgetCodomain A) (forgetCodomain b)
  | .ex A b => .ex (forgetCodomain A) (forgetCodomain b)

theorem shiftN_productZero :
    ∀ depth : Nat, shiftN depth (Expr.pi natType (vec zeroE)) = Expr.pi natType (vec zeroE)
  | 0 => rfl
  | depth + 1 => by
      show shiftAt 0 (shiftN depth (Expr.pi natType (vec zeroE))) = Expr.pi natType (vec zeroE)
      rw [shiftN_productZero depth]
      rfl

theorem shiftN_productOne :
    ∀ depth : Nat,
      shiftN depth (Expr.pi natType (vec (succE zeroE))) = Expr.pi natType (vec (succE zeroE))
  | 0 => rfl
  | depth + 1 => by
      show shiftAt 0 (shiftN depth (Expr.pi natType (vec (succE zeroE)))) =
        Expr.pi natType (vec (succE zeroE))
      rw [shiftN_productOne depth]
      rfl

/-- A step by the knowledge between the two products keeps the reading without codomains. -/
theorem forgetCodomain_step {depth : Nat} {e e' : AExpr}
    (step : RewriteUnder
      (fun depth left right => False ∨ assumedAt productKnowledge depth left right) depth e e') :
    forgetCodomain e = forgetCodomain e' := by
  induction step with
  | @root depth left right rule =>
      rcases rule with impossible | ⟨equation, member, atLeft, atRight⟩
      · exact impossible.elim
      · obtain rfl := List.mem_singleton.mp member
        rw [atLeft, atRight, shiftN_productZero, shiftN_productOne]
        rfl
  | piDomain _ ih => simp only [forgetCodomain, ih]
  | piBody _ _ => simp only [forgetCodomain]
  | lamDomain _ ih => simp only [forgetCodomain, ih]
  | lamBody _ ih => simp only [forgetCodomain, ih]
  | appFunction _ ih => simp only [forgetCodomain, ih]
  | appArgument _ ih => simp only [forgetCodomain, ih]
  | andLeft _ ih => simp only [forgetCodomain, ih]
  | andRight _ ih => simp only [forgetCodomain, ih]
  | orLeft _ ih => simp only [forgetCodomain, ih]
  | orRight _ ih => simp only [forgetCodomain, ih]
  | impLeft _ ih => simp only [forgetCodomain, ih]
  | impRight _ ih => simp only [forgetCodomain, ih]
  | notBody _ ih => simp only [forgetCodomain, ih]
  | eqLeft _ ih => simp only [forgetCodomain, ih]
  | eqRight _ ih => simp only [forgetCodomain, ih]
  | allDomain _ ih => simp only [forgetCodomain, ih]
  | allBody _ ih => simp only [forgetCodomain, ih]
  | exDomain _ ih => simp only [forgetCodomain, ih]
  | exBody _ ih => simp only [forgetCodomain, ih]

theorem forgetCodomain_conv {e e' : AExpr}
    (converted : ConvertibleKnowing (fun _ _ => False) productKnowledge e e') :
    forgetCodomain e = forgetCodomain e' := by
  induction converted with
  | rel _ _ step => exact forgetCodomain_step step
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **Knowledge between products breaks uniqueness of types.** At the frame that assumes
`Π (m : nat). Vec 0 ≐ Π (m : nat). Vec 1`, the term `f 0` is typed at `Vec 0` and at `Vec 1`, and
the frame does not convert `Vec 0` with `Vec 1`. -/
theorem product_knowledge_two_types :
    TypedKnowing (fun _ _ => False) productKnowledge functionContext
        (Expr.app (bvar 0) zeroE) (vec zeroE) ∧
      TypedKnowing (fun _ _ => False) productKnowledge functionContext
        (Expr.app (bvar 0) zeroE) (vec (succE zeroE)) ∧
      ¬ ConvertibleKnowing (fun _ _ => False) productKnowledge (vec zeroE) (vec (succE zeroE)) := by
  refine ⟨applied_at_zero, applied_at_one, ?_⟩
  intro converted
  have same := forgetCodomain_conv converted
  simp [forgetCodomain, vec, succE, zeroE] at same

end Controls

/-! ## Axiom audit -/

#print axioms Synth.typed
#print axioms synth_of_typed
#print axioms typed_iff_synth
#print axioms synth_unique
#print axioms typed_unique
#print axioms coherent_convertible
#print axioms piCodomainInjective_of_confluent
#print axioms hasTypeInside_unique
#print axioms hasTypeInside_iff_synth_run
#print axioms typedKnowing_unique_of_sound
#print axioms Controls.arith_piCodomainInjective
#print axioms Controls.arith_normal_type_unique
#print axioms Controls.none_types_unique
#print axioms Controls.product_knowledge_two_types

end Mettapedia.TypeTheory.BubbleTypingAlgorithmic
