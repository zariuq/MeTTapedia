import Mettapedia.TypeTheory.BubbleTypingAlgorithmic

/-!
# A typing is a skeleton and a list of asks

The syntax-directed judgment `BubbleTypingAlgorithmic.Synth moves` uses the movement relation at
fixed places. This module separates the two parts.

* `Asking Γ e A asked` is the skeleton of a typing of `e`: it mentions no movement relation, and
  it records in `asked` the pairs of types that the typing asks to be moved to each other.
* `synth_iff_asking`: a term is typed by the syntax-directed judgment of a movement relation
  exactly when it has a skeleton all of whose asks the relation answers.
* `Asking.length_eq`: the number of asks is a function of the term (`asks`): two for a product, an
  application, a connective with two sides or a quantifier, one for an abstraction, a negation or
  an equation, none for a variable or a constant.
* `hasTypeInside_iff_asking`: in a bubble with coherent conversion, a term is typed exactly when
  it has a skeleton whose `asks e` asks are each answered by a run of the bubble's conversion
  step, with one more run at the root.

So the evidence for a typing is a list of runs whose number is fixed by the term. What a bubble,
a frame or a store of conversions contributes to typing is answers to these asks.

## Controls

* `Controls.application_asking`: the skeleton of `f v`, with `f : Vec (n + 0) → nat` and
  `v : Vec n`, asks two things; the second is `Vec n` against `Vec (n + 0)`.
* `Controls.application_answered`, `Controls.application_not_answered`: the recursion equations
  answer both asks, and with no declared step the second is not answered.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleTypingAsks

open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The number of asks of the syntax-directed typing of a term. -/
def asks : Expr Base Const → Nat
  | .bvar _ => 0
  | .univ => 0
  | .prop => 0
  | .base _ => 0
  | .pi A B => asks A + asks B + 1 + 1
  | .lam A b => asks A + asks b + 1
  | .app f a => asks f + asks a + 1 + 1
  | .const _ _ => 0
  | .tyFam _ => 0
  | .top => 0
  | .bot => 0
  | .and p q => asks p + asks q + 1 + 1
  | .or p q => asks p + asks q + 1 + 1
  | .imp p q => asks p + asks q + 1 + 1
  | .not p => asks p + 1
  | .eq a b => asks a + asks b + 1
  | .all A b => asks A + asks b + 1 + 1
  | .ex A b => asks A + asks b + 1 + 1

/-- The skeleton of a syntax-directed typing: no movement relation, and the list of the pairs of
types that the typing asks to be moved to each other. -/
inductive Asking : List (Expr Base Const) → Expr Base Const → Expr Base Const →
    List (Expr Base Const × Expr Base Const) → Prop where
  | var {Γ : List (Expr Base Const)} {i : Nat} {A : Expr Base Const}
      (lookup : Γ[i]? = some A) : Asking Γ (bvar i) (shiftN (i + 1) A) []
  | base {Γ : List (Expr Base Const)} (b : Base) : Asking Γ (Expr.base b) univ []
  | prop {Γ : List (Expr Base Const)} : Asking Γ Expr.prop univ []
  | pi {Γ : List (Expr Base Const)} {A B S S' : Expr Base Const}
      {asksA asksB : List (Expr Base Const × Expr Base Const)} :
      Asking Γ A S asksA → Asking (A :: Γ) B S' asksB →
        Asking Γ (Expr.pi A B) univ ((S, univ) :: (S', univ) :: (asksA ++ asksB))
  | lam {Γ : List (Expr Base Const)} {A b B S : Expr Base Const}
      {asksA asksB : List (Expr Base Const × Expr Base Const)} :
      Asking Γ A S asksA → Asking (A :: Γ) b B asksB →
        Asking Γ (Expr.lam A b) (Expr.pi A B) ((S, univ) :: (asksA ++ asksB))
  | app {Γ : List (Expr Base Const)} {f a F A A' B : Expr Base Const}
      {asksF asksA : List (Expr Base Const × Expr Base Const)} :
      Asking Γ f F asksF → Asking Γ a A' asksA →
        Asking Γ (Expr.app f a) (substAt 0 a B) ((F, Expr.pi A B) :: (A', A) :: (asksF ++ asksA))
  | const {Γ : List (Expr Base Const)} (τ : Ty Base) (c : Const τ) :
      Asking Γ (Expr.const τ c) (tyToExpr τ) []
  | tyFam {Γ : List (Expr Base Const)} (b : Base) :
      Asking Γ (Expr.tyFam b) (Expr.pi (Expr.base b) univ) []
  | top {Γ : List (Expr Base Const)} : Asking Γ Expr.top Expr.prop []
  | bot {Γ : List (Expr Base Const)} : Asking Γ Expr.bot Expr.prop []
  | and {Γ : List (Expr Base Const)} {p q P Q : Expr Base Const}
      {asksP asksQ : List (Expr Base Const × Expr Base Const)} :
      Asking Γ p P asksP → Asking Γ q Q asksQ →
        Asking Γ (Expr.and p q) Expr.prop ((P, Expr.prop) :: (Q, Expr.prop) :: (asksP ++ asksQ))
  | or {Γ : List (Expr Base Const)} {p q P Q : Expr Base Const}
      {asksP asksQ : List (Expr Base Const × Expr Base Const)} :
      Asking Γ p P asksP → Asking Γ q Q asksQ →
        Asking Γ (Expr.or p q) Expr.prop ((P, Expr.prop) :: (Q, Expr.prop) :: (asksP ++ asksQ))
  | imp {Γ : List (Expr Base Const)} {p q P Q : Expr Base Const}
      {asksP asksQ : List (Expr Base Const × Expr Base Const)} :
      Asking Γ p P asksP → Asking Γ q Q asksQ →
        Asking Γ (Expr.imp p q) Expr.prop ((P, Expr.prop) :: (Q, Expr.prop) :: (asksP ++ asksQ))
  | not {Γ : List (Expr Base Const)} {p P : Expr Base Const}
      {asksP : List (Expr Base Const × Expr Base Const)} :
      Asking Γ p P asksP → Asking Γ (Expr.not p) Expr.prop ((P, Expr.prop) :: asksP)
  | eq {Γ : List (Expr Base Const)} {a b A B : Expr Base Const}
      {asksA asksB : List (Expr Base Const × Expr Base Const)} :
      Asking Γ a A asksA → Asking Γ b B asksB →
        Asking Γ (Expr.eq a b) Expr.prop ((A, B) :: (asksA ++ asksB))
  | all {Γ : List (Expr Base Const)} {A b S P : Expr Base Const}
      {asksA asksB : List (Expr Base Const × Expr Base Const)} :
      Asking Γ A S asksA → Asking (A :: Γ) b P asksB →
        Asking Γ (Expr.all A b) Expr.prop ((S, univ) :: (P, Expr.prop) :: (asksA ++ asksB))
  | ex {Γ : List (Expr Base Const)} {A b S P : Expr Base Const}
      {asksA asksB : List (Expr Base Const × Expr Base Const)} :
      Asking Γ A S asksA → Asking (A :: Γ) b P asksB →
        Asking Γ (Expr.ex A b) Expr.prop ((S, univ) :: (P, Expr.prop) :: (asksA ++ asksB))

/-- **The number of asks is a function of the term.** -/
theorem Asking.length_eq {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    {asked : List (Expr Base Const × Expr Base Const)} (asking : Asking Γ e A asked) :
    asked.length = asks e := by
  induction asking with
  | var _ => rfl
  | base _ => rfl
  | prop => rfl
  | pi _ _ ihA ihB => simp only [List.length_cons, List.length_append, asks, ihA, ihB]
  | lam _ _ ihA ihB => simp only [List.length_cons, List.length_append, asks, ihA, ihB]
  | app _ _ ihF ihA => simp only [List.length_cons, List.length_append, asks, ihF, ihA]
  | const _ _ => rfl
  | tyFam _ => rfl
  | top => rfl
  | bot => rfl
  | and _ _ ihP ihQ => simp only [List.length_cons, List.length_append, asks, ihP, ihQ]
  | or _ _ ihP ihQ => simp only [List.length_cons, List.length_append, asks, ihP, ihQ]
  | imp _ _ ihP ihQ => simp only [List.length_cons, List.length_append, asks, ihP, ihQ]
  | not _ ihP => simp only [List.length_cons, asks, ihP]
  | eq _ _ ihA ihB => simp only [List.length_cons, List.length_append, asks, ihA, ihB]
  | all _ _ ihA ihB => simp only [List.length_cons, List.length_append, asks, ihA, ihB]
  | ex _ _ ihA ihB => simp only [List.length_cons, List.length_append, asks, ihA, ihB]

/-- A skeleton whose asks a movement relation answers is a syntax-directed typing for it. -/
theorem Asking.synth {moves : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    {asked : List (Expr Base Const × Expr Base Const)} (asking : Asking Γ e A asked) :
    (∀ ask ∈ asked, moves ask.1 ask.2) → Synth moves Γ e A := by
  induction asking with
  | var lookup => exact fun _ => .var lookup
  | base b => exact fun _ => .base b
  | prop => exact fun _ => .prop
  | pi _ _ ihA ihB =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      obtain ⟨second, rest⟩ := List.forall_mem_cons.mp rest
      obtain ⟨left, right⟩ := List.forall_mem_append.mp rest
      exact .pi (ihA left) first (ihB right) second
  | lam _ _ ihA ihB =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      obtain ⟨left, right⟩ := List.forall_mem_append.mp rest
      exact .lam (ihA left) first (ihB right)
  | app _ _ ihF ihA =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      obtain ⟨second, rest⟩ := List.forall_mem_cons.mp rest
      obtain ⟨left, right⟩ := List.forall_mem_append.mp rest
      exact .app (ihF left) first (ihA right) second
  | const τ c => exact fun _ => .const τ c
  | tyFam b => exact fun _ => .tyFam b
  | top => exact fun _ => .top
  | bot => exact fun _ => .bot
  | and _ _ ihP ihQ =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      obtain ⟨second, rest⟩ := List.forall_mem_cons.mp rest
      obtain ⟨left, right⟩ := List.forall_mem_append.mp rest
      exact .and (ihP left) first (ihQ right) second
  | or _ _ ihP ihQ =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      obtain ⟨second, rest⟩ := List.forall_mem_cons.mp rest
      obtain ⟨left, right⟩ := List.forall_mem_append.mp rest
      exact .or (ihP left) first (ihQ right) second
  | imp _ _ ihP ihQ =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      obtain ⟨second, rest⟩ := List.forall_mem_cons.mp rest
      obtain ⟨left, right⟩ := List.forall_mem_append.mp rest
      exact .imp (ihP left) first (ihQ right) second
  | not _ ihP =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      exact .not (ihP rest) first
  | eq _ _ ihA ihB =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      obtain ⟨left, right⟩ := List.forall_mem_append.mp rest
      exact .eq (ihA left) (ihB right) first
  | all _ _ ihA ihB =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      obtain ⟨second, rest⟩ := List.forall_mem_cons.mp rest
      obtain ⟨left, right⟩ := List.forall_mem_append.mp rest
      exact .all (ihA left) first (ihB right) second
  | ex _ _ ihA ihB =>
      intro answered
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp answered
      obtain ⟨second, rest⟩ := List.forall_mem_cons.mp rest
      obtain ⟨left, right⟩ := List.forall_mem_append.mp rest
      exact .ex (ihA left) first (ihB right) second

/-- A syntax-directed typing has a skeleton, and the movement relation answers its asks. -/
theorem asking_of_synth {moves : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} (synth : Synth moves Γ e A) :
    ∃ asked, Asking Γ e A asked ∧ ∀ ask ∈ asked, moves ask.1 ask.2 := by
  induction synth with
  | var lookup => exact ⟨[], .var lookup, fun _ member => absurd member List.not_mem_nil⟩
  | base b => exact ⟨[], .base b, fun _ member => absurd member List.not_mem_nil⟩
  | prop => exact ⟨[], .prop, fun _ member => absurd member List.not_mem_nil⟩
  | pi _ atA _ atB ihA ihB =>
      obtain ⟨_, askingA, answeredA⟩ := ihA
      obtain ⟨_, askingB, answeredB⟩ := ihB
      exact ⟨_, .pi askingA askingB,
        List.forall_mem_cons.mpr ⟨atA, List.forall_mem_cons.mpr
          ⟨atB, List.forall_mem_append.mpr ⟨answeredA, answeredB⟩⟩⟩⟩
  | lam _ atA _ ihA ihB =>
      obtain ⟨_, askingA, answeredA⟩ := ihA
      obtain ⟨_, askingB, answeredB⟩ := ihB
      exact ⟨_, .lam askingA askingB,
        List.forall_mem_cons.mpr ⟨atA, List.forall_mem_append.mpr ⟨answeredA, answeredB⟩⟩⟩
  | app _ atF _ atA ihF ihA =>
      obtain ⟨_, askingF, answeredF⟩ := ihF
      obtain ⟨_, askingA, answeredA⟩ := ihA
      exact ⟨_, .app askingF askingA,
        List.forall_mem_cons.mpr ⟨atF, List.forall_mem_cons.mpr
          ⟨atA, List.forall_mem_append.mpr ⟨answeredF, answeredA⟩⟩⟩⟩
  | const τ c => exact ⟨[], .const τ c, fun _ member => absurd member List.not_mem_nil⟩
  | tyFam b => exact ⟨[], .tyFam b, fun _ member => absurd member List.not_mem_nil⟩
  | top => exact ⟨[], .top, fun _ member => absurd member List.not_mem_nil⟩
  | bot => exact ⟨[], .bot, fun _ member => absurd member List.not_mem_nil⟩
  | and _ atP _ atQ ihP ihQ =>
      obtain ⟨_, askingP, answeredP⟩ := ihP
      obtain ⟨_, askingQ, answeredQ⟩ := ihQ
      exact ⟨_, .and askingP askingQ,
        List.forall_mem_cons.mpr ⟨atP, List.forall_mem_cons.mpr
          ⟨atQ, List.forall_mem_append.mpr ⟨answeredP, answeredQ⟩⟩⟩⟩
  | or _ atP _ atQ ihP ihQ =>
      obtain ⟨_, askingP, answeredP⟩ := ihP
      obtain ⟨_, askingQ, answeredQ⟩ := ihQ
      exact ⟨_, .or askingP askingQ,
        List.forall_mem_cons.mpr ⟨atP, List.forall_mem_cons.mpr
          ⟨atQ, List.forall_mem_append.mpr ⟨answeredP, answeredQ⟩⟩⟩⟩
  | imp _ atP _ atQ ihP ihQ =>
      obtain ⟨_, askingP, answeredP⟩ := ihP
      obtain ⟨_, askingQ, answeredQ⟩ := ihQ
      exact ⟨_, .imp askingP askingQ,
        List.forall_mem_cons.mpr ⟨atP, List.forall_mem_cons.mpr
          ⟨atQ, List.forall_mem_append.mpr ⟨answeredP, answeredQ⟩⟩⟩⟩
  | not _ atP ihP =>
      obtain ⟨_, askingP, answeredP⟩ := ihP
      exact ⟨_, .not askingP, List.forall_mem_cons.mpr ⟨atP, answeredP⟩⟩
  | eq _ _ same ihA ihB =>
      obtain ⟨_, askingA, answeredA⟩ := ihA
      obtain ⟨_, askingB, answeredB⟩ := ihB
      exact ⟨_, .eq askingA askingB,
        List.forall_mem_cons.mpr ⟨same, List.forall_mem_append.mpr ⟨answeredA, answeredB⟩⟩⟩
  | all _ atA _ atP ihA ihB =>
      obtain ⟨_, askingA, answeredA⟩ := ihA
      obtain ⟨_, askingB, answeredB⟩ := ihB
      exact ⟨_, .all askingA askingB,
        List.forall_mem_cons.mpr ⟨atA, List.forall_mem_cons.mpr
          ⟨atP, List.forall_mem_append.mpr ⟨answeredA, answeredB⟩⟩⟩⟩
  | ex _ atA _ atP ihA ihB =>
      obtain ⟨_, askingA, answeredA⟩ := ihA
      obtain ⟨_, askingB, answeredB⟩ := ihB
      exact ⟨_, .ex askingA askingB,
        List.forall_mem_cons.mpr ⟨atA, List.forall_mem_cons.mpr
          ⟨atP, List.forall_mem_append.mpr ⟨answeredA, answeredB⟩⟩⟩⟩

/-- **A syntax-directed typing is a skeleton whose asks are answered.** -/
theorem synth_iff_asking {moves : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} :
    Synth moves Γ e A ↔ ∃ asked, Asking Γ e A asked ∧ ∀ ask ∈ asked, moves ask.1 ask.2 :=
  ⟨asking_of_synth, fun ⟨_, asking, answered⟩ => asking.synth answered⟩

/-- **A typing in a bubble is a skeleton, one run for each of its asks, and one run at the
root.** The number of runs is fixed by the term. -/
theorem hasTypeInside_iff_asking {rules : Expr Base Const → Expr Base Const → Prop}
    (coherent : Coherent (Convertible rules)) {Γ : List (Expr Base Const)}
    {e T : Expr Base Const} :
    HasTypeInside rules Γ e T ↔
      ∃ A asked, Asking Γ e A asked ∧ asked.length = asks e ∧
        (∀ ask ∈ asked, Reaches rules ask.1 ask.2) ∧ Reaches rules A T := by
  constructor
  · intro typed
    obtain ⟨A, synth, reached⟩ := (hasTypeInside_iff_synth_run coherent).mp typed
    obtain ⟨asked, asking, answered⟩ := asking_of_synth synth
    exact ⟨A, asked, asking, asking.length_eq, answered, reached⟩
  · rintro ⟨A, asked, asking, _, answered, reached⟩
    exact (hasTypeInside_iff_synth_run coherent).mpr ⟨A, asking.synth answered, reached⟩

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleTypingInside.Controls

/-- The asks of `f v` with `f : Vec (n + 0) → nat` and `v : Vec n`: the type of `f` against a
product, and the type of `v` against the domain. -/
def applicationAsks : List (AExpr × AExpr) :=
  [(Expr.pi (vec (addE (bvar 2) zeroE)) natType, Expr.pi (vec (addE (bvar 2) zeroE)) natType),
    (vec (bvar 2), vec (addE (bvar 2) zeroE))]

/-- **The skeleton of the application**, with its two asks. -/
theorem application_asking :
    Asking appContext (Expr.app (bvar 0) (bvar 1)) natType applicationAsks :=
  Asking.app (A := vec (addE (bvar 2) zeroE)) (B := natType)
    (Asking.var (Γ := appContext) (i := 0) rfl) (Asking.var (Γ := appContext) (i := 1) rfl)

/-- The term asks twice. -/
theorem application_asks : asks (Expr.app (bvar 0) (bvar 1) : AExpr) = 2 :=
  rfl

/-- **The recursion equations answer both asks.** -/
theorem application_answered :
    ∀ ask ∈ applicationAsks, Convertible (bubbleRules false) ask.1 ask.2 := by
  intro ask member
  rcases List.mem_cons.mp member with rfl | rest
  · exact Relation.EqvGen.refl _
  · obtain rfl := List.mem_singleton.mp rest
    exact Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ (Rewrite.appArgument (Rewrite.root (Rule.addZero (bvar 2)))))

/-- **With no declared step the second ask is not answered.** -/
theorem application_not_answered :
    ¬ ∀ ask ∈ applicationAsks, Convertible (fun _ _ => False) ask.1 ask.2 := by
  intro answered
  have second :=
    convertible_none_iff.mp
      (answered (vec (bvar 2), vec (addE (bvar 2) zeroE))
        (List.mem_cons.mpr (Or.inr (List.mem_singleton_self _))))
  simp [vec, addE] at second

end Controls

/-! ## Axiom audit -/

#print axioms Asking.length_eq
#print axioms Asking.synth
#print axioms asking_of_synth
#print axioms synth_iff_asking
#print axioms hasTypeInside_iff_asking
#print axioms Controls.application_asking
#print axioms Controls.application_answered
#print axioms Controls.application_not_answered

end Mettapedia.TypeTheory.BubbleTypingAsks
