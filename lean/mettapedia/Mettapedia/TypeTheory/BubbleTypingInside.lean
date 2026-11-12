import Mettapedia.TypeTheory.BubbleTypingRuns

/-!
# The conversion rule at every node, and the run rule that replaces it

`BubbleConversion.HasTypeIn` applies a bubble's conversion once, after syntax-directed typing. A
program that passes `v : Vec n` to a function of domain `Vec (n + 0)` needs the conversion at the
argument, inside the derivation. This module states typing with a movement rule at every node
(`Typed`), parameterized by which movements of types are allowed, and compares three instances.

* `HasTypeInside rules`: the movement is the bubble's conversion. This is the usual conversion rule.
* `HasTypeRun rules`: the movement is a run of the bubble's conversion step (`Reaches`).
* **The run rule replaces the conversion rule** (`hasTypeInside_iff_hasTypeRun`): the two judgments
  have the same derivable typings.
* With no declared step both are the global judgment (`hasTypeInside_none_iff`); the judgment is
  monotone in the allowed movements (`Typed.mono`); root-only typing embeds
  (`hasTypeInside_of_hasTypeIn`).
* **Three places an equation can live.** A conversion of the bubble needs nothing. An equation
  assumed at a frame is used there with no change to terms (`hasTypeInside_withKnowledge`), and it is
  discharged, again with no change to terms, exactly when the bubble converts it
  (`hasTypeInside_discharge`). An equation the bubble does not convert stays the frame's knowledge
  until a bubble that declares it is used (`Controls.zeroAdd_under_knowledge`,
  `Controls.zeroAdd_not_discharged`, `Controls.zeroAdd_discharged_in_plus`).

## Controls (`Controls`)

In the context `n : nat, v : Vec n, f : Vec (n + 0) → nat`:
* the application `f v` is typed with the recursion equations, by one conversion at the argument
  (`application_typed`), hence by one run there (`application_typed_by_run`);
* it has no type in the global judgment (`application_not_global`), so root-only typing does not
  type it in any bubble (`application_not_root_only`), and typing with the movement rule and no
  declared step does not either (`application_not_without_steps`).

Scope: the comparison core of `SimpleSliceOfDependent`. Uniqueness of types up to conversion for
`HasTypeInside` is not claimed; it needs injectivity of the dependent function former under the
bubble's conversion. Assumed equations are raw rewrite rules; they are the frame's knowledge at
positions outside binders (`KnowledgeUnderBinders`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleTypingInside

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.ConversionRuns
open Mettapedia.TypeTheory.BubbleTypingRuns
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Typing of the comparison core with a movement rule at every node: a term typed at `A` is
typed at `B` whenever `A` moves to `B`. -/
inductive Typed (moves : Expr Base Const → Expr Base Const → Prop) :
    List (Expr Base Const) → Expr Base Const → Expr Base Const → Prop where
  | var {Γ : List (Expr Base Const)} {i : Nat} {A : Expr Base Const}
      (lookup : Γ[i]? = some A) : Typed moves Γ (bvar i) (shiftN (i + 1) A)
  | base {Γ : List (Expr Base Const)} (b : Base) : Typed moves Γ (Expr.base b) univ
  | prop {Γ : List (Expr Base Const)} : Typed moves Γ Expr.prop univ
  | pi {Γ : List (Expr Base Const)} {A B : Expr Base Const} :
      Typed moves Γ A univ → Typed moves (A :: Γ) B univ → Typed moves Γ (Expr.pi A B) univ
  | lam {Γ : List (Expr Base Const)} {A b B : Expr Base Const} :
      Typed moves Γ A univ → Typed moves (A :: Γ) b B → Typed moves Γ (Expr.lam A b) (Expr.pi A B)
  | app {Γ : List (Expr Base Const)} {f a A B : Expr Base Const} :
      Typed moves Γ f (Expr.pi A B) → Typed moves Γ a A →
        Typed moves Γ (Expr.app f a) (substAt 0 a B)
  | const {Γ : List (Expr Base Const)} (τ : Ty Base) (c : Const τ) :
      Typed moves Γ (Expr.const τ c) (tyToExpr τ)
  | tyFam {Γ : List (Expr Base Const)} (b : Base) :
      Typed moves Γ (Expr.tyFam b) (Expr.pi (Expr.base b) univ)
  | top {Γ : List (Expr Base Const)} : Typed moves Γ Expr.top Expr.prop
  | bot {Γ : List (Expr Base Const)} : Typed moves Γ Expr.bot Expr.prop
  | and {Γ : List (Expr Base Const)} {p q : Expr Base Const} :
      Typed moves Γ p Expr.prop → Typed moves Γ q Expr.prop → Typed moves Γ (Expr.and p q) Expr.prop
  | or {Γ : List (Expr Base Const)} {p q : Expr Base Const} :
      Typed moves Γ p Expr.prop → Typed moves Γ q Expr.prop → Typed moves Γ (Expr.or p q) Expr.prop
  | imp {Γ : List (Expr Base Const)} {p q : Expr Base Const} :
      Typed moves Γ p Expr.prop → Typed moves Γ q Expr.prop → Typed moves Γ (Expr.imp p q) Expr.prop
  | not {Γ : List (Expr Base Const)} {p : Expr Base Const} :
      Typed moves Γ p Expr.prop → Typed moves Γ (Expr.not p) Expr.prop
  | eq {Γ : List (Expr Base Const)} {a b A : Expr Base Const} :
      Typed moves Γ a A → Typed moves Γ b A → Typed moves Γ (Expr.eq a b) Expr.prop
  | all {Γ : List (Expr Base Const)} {A b : Expr Base Const} :
      Typed moves Γ A univ → Typed moves (A :: Γ) b Expr.prop → Typed moves Γ (Expr.all A b) Expr.prop
  | ex {Γ : List (Expr Base Const)} {A b : Expr Base Const} :
      Typed moves Γ A univ → Typed moves (A :: Γ) b Expr.prop → Typed moves Γ (Expr.ex A b) Expr.prop
  | move {Γ : List (Expr Base Const)} {e A B : Expr Base Const} :
      Typed moves Γ e A → moves A B → Typed moves Γ e B

/-- **More movements, more typings.** -/
theorem Typed.mono {small large : Expr Base Const → Expr Base Const → Prop}
    (included : ∀ A B, small A B → large A B) {Γ : List (Expr Base Const)}
    {e A : Expr Base Const} (typed : Typed small Γ e A) : Typed large Γ e A := by
  induction typed with
  | var lookup => exact .var lookup
  | base b => exact .base b
  | prop => exact .prop
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | app _ _ ihf iha => exact .app ihf iha
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
  | move _ moved ih => exact .move ih (included _ _ moved)

/-- Every typing of the global judgment is a typing with any movement rule. -/
theorem Typed.of_hasType {moves : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} (typing : HasType Γ e A) :
    Typed moves Γ e A := by
  induction typing with
  | var lookup => exact .var lookup
  | base b => exact .base b
  | prop => exact .prop
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | app _ _ ihf iha => exact .app ihf iha
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

/-- When the only movement is to the same type, typing is the global judgment. -/
theorem typed_eq_iff {Γ : List (Expr Base Const)} {e A : Expr Base Const} :
    Typed (fun A B : Expr Base Const => A = B) Γ e A ↔ HasType Γ e A := by
  constructor
  · intro typed
    induction typed with
    | var lookup => exact .var lookup
    | base b => exact .base b
    | prop => exact .prop
    | pi _ _ ihA ihB => exact .pi ihA ihB
    | lam _ _ ihA ihb => exact .lam ihA ihb
    | app _ _ ihf iha => exact .app ihf iha
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
    | move _ same ih => exact same ▸ ih
  · exact Typed.of_hasType

/-- **Typing in a bubble with the conversion rule at every node.** -/
abbrev HasTypeInside (rules : Expr Base Const → Expr Base Const → Prop) :=
  Typed (Convertible rules)

/-- A type reaches another when a run of the bubble's conversion step, from the goal with nothing
told, leads from the first to the second. -/
def Reaches (rules : Expr Base Const → Expr Base Const → Prop) (A B : Expr Base Const) : Prop :=
  ∃ run : (conversionStep (bubbles Base Const) rules ()).Run ⟨A, [], 0⟩, run.last.cursor = B

/-- **Typing in a bubble with the run rule at every node.** -/
abbrev HasTypeRun (rules : Expr Base Const → Expr Base Const → Prop) :=
  Typed (Reaches rules)

/-- **The run rule replaces the conversion rule.** Typing with the bubble's conversion at every
node and typing with a run of its conversion step at every node derive the same typings. -/
theorem hasTypeInside_iff_hasTypeRun {rules : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} :
    HasTypeInside rules Γ e A ↔ HasTypeRun rules Γ e A :=
  ⟨Typed.mono fun _ _ converted => (convertible_iff_run [] 0).mp converted,
    Typed.mono fun _ _ reached => (convertible_iff_run [] 0).mpr reached⟩

/-- **With no declared step, typing with the conversion rule is the global judgment.** -/
theorem hasTypeInside_none_iff {Γ : List (Expr Base Const)} {e A : Expr Base Const} :
    HasTypeInside (fun _ _ => False) Γ e A ↔ HasType Γ e A :=
  ⟨fun typed => typed_eq_iff.mp (typed.mono fun _ _ converted => convertible_none_iff.mp converted),
    Typed.of_hasType⟩

/-- Root-only typing in a bubble is typing with the conversion rule. -/
theorem hasTypeInside_of_hasTypeIn {rules : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e B : Expr Base Const} (typed : HasTypeIn rules Γ e B) :
    HasTypeInside rules Γ e B := by
  obtain ⟨A, typing, converted⟩ := hasTypeIn_iff.mp typed
  exact .move (Typed.of_hasType typing) converted

/-- Conversion with the bubble's rules and a store of equations that the bubble already converts
is conversion of the bubble. -/
theorem convertible_of_withKnowledge {rules : Expr Base Const → Expr Base Const → Prop}
    {store : EquationStore (Expr Base Const)}
    (sound : ∀ e ∈ store, Convertible rules e.1 e.2) {e e' : Expr Base Const}
    (converted : Convertible (withKnowledge rules store) e e') : Convertible rules e e' :=
  BubbleWeakness.rel_of_convertible (θ := BubbleWeakness.conversionModel rules)
    (fun φ member => by
      rcases (show rules φ.1 φ.2 ∨ KnowledgeFramesCore.assumed store φ.1 φ.2 from member) with
        rule | told
      · exact Relation.EqvGen.rel _ _ (Rewrite.root rule)
      · exact sound φ told)
    converted

/-- **Knowledge that the bubble proves is discharged with no change to the term.** A typing
derived at a frame whose assumed equations are all conversions of the bubble is a typing in the
bubble: the same term, at the same type. -/
theorem hasTypeInside_discharge {rules : Expr Base Const → Expr Base Const → Prop}
    {store : EquationStore (Expr Base Const)}
    (sound : ∀ e ∈ store, Convertible rules e.1 e.2) {Γ : List (Expr Base Const)}
    {e A : Expr Base Const} (typed : HasTypeInside (withKnowledge rules store) Γ e A) :
    HasTypeInside rules Γ e A :=
  typed.mono fun _ _ converted => convertible_of_withKnowledge sound converted

/-- What the bubble types stays typed at every frame of the bubble. -/
theorem hasTypeInside_withKnowledge {rules : Expr Base Const → Expr Base Const → Prop}
    (store : EquationStore (Expr Base Const)) {Γ : List (Expr Base Const)}
    {e A : Expr Base Const} (typed : HasTypeInside rules Γ e A) :
    HasTypeInside (withKnowledge rules store) Γ e A :=
  typed.mono fun _ _ converted => convertible_mono (fun _ _ rule => Or.inl rule) converted

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- The knowledge `0 + n ≐ n`, for the variable `n` of the vector context. -/
def knowsZeroAdd : EquationStore AExpr := [(addE zeroE (bvar 1), bvar 1)]

/-- **An equation the bubble does not convert, held as knowledge.** With the recursion equations
and the knowledge `0 + n ≐ n`, `v : Vec n` is typed at `Vec (0 + n)`. -/
theorem zeroAdd_under_knowledge :
    HasTypeInside (withKnowledge (bubbleRules false) knowsZeroAdd) vecContext (bvar 0)
      (vec (addE zeroE (bvar 1))) :=
  Typed.move (Typed.of_hasType vecVariable_typed)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Rewrite.appArgument (Rewrite.root (Or.inr (List.mem_singleton_self _))))))

/-- **It is not discharged into the recursion equations**: the bubble does not convert it, so the
frame's knowledge is doing the work. -/
theorem zeroAdd_not_discharged :
    ¬ ∀ e ∈ knowsZeroAdd, Convertible (bubbleRules false) e.1 e.2 := by
  intro sound
  have converted := sound (addE zeroE (bvar 1), bvar 1) (List.mem_singleton_self _)
  have same := (conv_iff_norm false).mp converted
  simp [Arith.norm, appNorm, addNorm, addE, zeroE] at same

/-- **It is discharged into the bubble that declares the left unit**: there the same term has the
same type with no knowledge. -/
theorem zeroAdd_discharged_in_plus :
    HasTypeInside (bubbleRules true) vecContext (bvar 0) (vec (addE zeroE (bvar 1))) :=
  hasTypeInside_discharge (store := knowsZeroAdd)
    (by
      intro e member
      obtain rfl := List.mem_singleton.mp member
      exact Relation.EqvGen.rel _ _ (Rewrite.root (RulePlus.zeroAdd (bvar 1))))
    (Typed.move (Typed.of_hasType vecVariable_typed)
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        (Rewrite.appArgument (Rewrite.root (Or.inr (List.mem_singleton_self _)))))))

/-- The context `n : nat, v : Vec n, f : Vec (n + 0) → nat`, newest first. -/
def appContext : List AExpr := [Expr.pi (vec (addE (bvar 1) zeroE)) natType, vec (bvar 0), natType]

theorem function_typed :
    HasType appContext (bvar 0) (Expr.pi (vec (addE (bvar 2) zeroE)) natType) :=
  HasType.var (Γ := appContext) (i := 0) rfl

theorem argument_typed : HasType appContext (bvar 1) (vec (bvar 2)) :=
  HasType.var (Γ := appContext) (i := 1) rfl

/-- **The application `f v` is typed with the recursion equations**, by one conversion at the
argument. -/
theorem application_typed :
    HasTypeInside (bubbleRules false) appContext (Expr.app (bvar 0) (bvar 1)) natType :=
  Typed.app (A := vec (addE (bvar 2) zeroE)) (B := natType) (Typed.of_hasType function_typed)
    (Typed.move (Typed.of_hasType argument_typed)
      (show Convertible (bubbleRules false) (vec (bvar 2)) (vec (addE (bvar 2) zeroE)) from
        Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
          (Rewrite.appArgument (Rewrite.root (Rule.addZero (bvar 2)))))))

/-- Hence by one run of the conversion step there. -/
theorem application_typed_by_run :
    HasTypeRun (bubbleRules false) appContext (Expr.app (bvar 0) (bvar 1)) natType :=
  hasTypeInside_iff_hasTypeRun.mp application_typed

/-- **The application has no type in the global judgment.** -/
theorem application_not_global (A : AExpr) :
    ¬ HasType appContext (Expr.app (bvar 0) (bvar 1)) A := by
  intro typing
  cases typing with
  | app functionTyping argumentTyping =>
      have domain := (Expr.pi.inj (function_typed.unique functionTyping)).1
      have same := domain.trans (argument_typed.unique argumentTyping).symm
      simp [vec, addE] at same

/-- So root-only typing does not type it, in any bubble and at any type. -/
theorem application_not_root_only (rules : AExpr → AExpr → Prop) (B : AExpr) :
    ¬ HasTypeIn rules appContext (Expr.app (bvar 0) (bvar 1)) B := by
  intro typed
  obtain ⟨A, typing, _⟩ := hasTypeIn_iff.mp typed
  exact application_not_global A typing

/-- And typing with the conversion rule and no declared step does not type it. -/
theorem application_not_without_steps (B : AExpr) :
    ¬ HasTypeInside (fun _ _ => False) appContext (Expr.app (bvar 0) (bvar 1)) B :=
  fun typed => application_not_global B (hasTypeInside_none_iff.mp typed)

end Controls

/-! ## Axiom audit -/

#print axioms Typed.mono
#print axioms typed_eq_iff
#print axioms hasTypeInside_iff_hasTypeRun
#print axioms hasTypeInside_none_iff
#print axioms hasTypeInside_of_hasTypeIn
#print axioms hasTypeInside_discharge
#print axioms hasTypeInside_withKnowledge
#print axioms Controls.zeroAdd_under_knowledge
#print axioms Controls.zeroAdd_not_discharged
#print axioms Controls.zeroAdd_discharged_in_plus
#print axioms Controls.application_typed
#print axioms Controls.application_typed_by_run
#print axioms Controls.application_not_global
#print axioms Controls.application_not_root_only
#print axioms Controls.application_not_without_steps

end Mettapedia.TypeTheory.BubbleTypingInside
