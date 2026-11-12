import Mettapedia.TypeTheory.KnowledgeSolvedForm

/-!
# Peeling a definition off a frame, whatever else the frame knows

`KnowledgeSolvedForm` treats a frame whose whole knowledge is one definition `x ≐ u`. This module
removes the restriction: a definition can be eliminated from any frame.

* `peel_definition_iff`: at a frame that knows `x ≐ u` and anything else, two terms convert
  exactly when their instances at `x := u` convert at the frame with the rest of the knowledge
  instantiated.
* `typedKnowing_peel`: a typing at the frame is a typing of the instance at the instantiated
  frame.
* `unique_of_peeled`: uniqueness of types up to the frame's conversion is inherited from the
  instantiated frame.

A store that is a list of definitions, each for a variable the earlier ones have not removed, is
eliminated one definition at a time, down to the conversion of the bubble
(`convertibleKnowing_nil_iff`).

Two general facts carry the proofs. Scoped conversion is stable under entering a binder
(`rewriteUnder_enter`), and a frame that converts every equation of another frame converts
everything the other frame converts and types everything it types
(`convertibleKnowing_of_entailed`, `typedKnowing_of_entailed`).

## Controls

* `Controls.two_definitions_conversion`: at the frame `n m : nat` that knows `m ≐ 0` and `n ≐ 0`,
  two terms convert exactly when their instances at both variables are identical.
* `Controls.vec_m_converts_with_vec_n`, `Controls.vec_other_does_not_convert`: `Vec m` converts
  with `Vec n` there, and `Vec p` for a third variable `p` does not convert with `Vec 0`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgePeeling

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.TypeTheory.KnowledgeSolvedForm
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The rules of a frame at each depth: the bubble's rules and the frame's equations. -/
abbrev frameRules (rules : Expr Base Const → Expr Base Const → Prop)
    (K : EquationStore (Expr Base Const)) : Nat → Expr Base Const → Expr Base Const → Prop :=
  fun depth left right => rules left right ∨ assumedAt K depth left right

/-! ## Scoped conversion under one more binder -/

/-- A scoped step, seen under one more binder inserted at or below its depth. -/
theorem rewriteUnder_enter {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {K : EquationStore (Expr Base Const)} {depth : Nat}
    {e e' : Expr Base Const} (step : RewriteUnder (frameRules rules K) depth e e') :
    ∀ cutoff : Nat, cutoff ≤ depth →
      RewriteUnder (frameRules rules K) (depth + 1) (shiftAt cutoff e) (shiftAt cutoff e') := by
  induction step with
  | root rule =>
      intro cutoff ordered
      rcases rule with direct | ⟨equation, member, atLeft, atRight⟩
      · exact .root (Or.inl (stable _ _ direct cutoff))
      · exact .root (Or.inr ⟨equation, member, by rw [atLeft, shiftAt_shiftN _ _ _ ordered],
          by rw [atRight, shiftAt_shiftN _ _ _ ordered]⟩)
  | piDomain _ ih => exact fun cutoff ordered => .piDomain (ih cutoff ordered)
  | piBody _ ih => exact fun cutoff ordered => .piBody (ih (cutoff + 1) (by omega))
  | lamDomain _ ih => exact fun cutoff ordered => .lamDomain (ih cutoff ordered)
  | lamBody _ ih => exact fun cutoff ordered => .lamBody (ih (cutoff + 1) (by omega))
  | appFunction _ ih => exact fun cutoff ordered => .appFunction (ih cutoff ordered)
  | appArgument _ ih => exact fun cutoff ordered => .appArgument (ih cutoff ordered)
  | andLeft _ ih => exact fun cutoff ordered => .andLeft (ih cutoff ordered)
  | andRight _ ih => exact fun cutoff ordered => .andRight (ih cutoff ordered)
  | orLeft _ ih => exact fun cutoff ordered => .orLeft (ih cutoff ordered)
  | orRight _ ih => exact fun cutoff ordered => .orRight (ih cutoff ordered)
  | impLeft _ ih => exact fun cutoff ordered => .impLeft (ih cutoff ordered)
  | impRight _ ih => exact fun cutoff ordered => .impRight (ih cutoff ordered)
  | notBody _ ih => exact fun cutoff ordered => .notBody (ih cutoff ordered)
  | eqLeft _ ih => exact fun cutoff ordered => .eqLeft (ih cutoff ordered)
  | eqRight _ ih => exact fun cutoff ordered => .eqRight (ih cutoff ordered)
  | allDomain _ ih => exact fun cutoff ordered => .allDomain (ih cutoff ordered)
  | allBody _ ih => exact fun cutoff ordered => .allBody (ih (cutoff + 1) (by omega))
  | exDomain _ ih => exact fun cutoff ordered => .exDomain (ih cutoff ordered)
  | exBody _ ih => exact fun cutoff ordered => .exBody (ih (cutoff + 1) (by omega))

theorem eqvGen_enter {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {K : EquationStore (Expr Base Const)} {depth : Nat}
    {e e' : Expr Base Const}
    (converted : Relation.EqvGen (RewriteUnder (frameRules rules K) depth) e e') (cutoff : Nat)
    (ordered : cutoff ≤ depth) :
    Relation.EqvGen (RewriteUnder (frameRules rules K) (depth + 1)) (shiftAt cutoff e)
      (shiftAt cutoff e') := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (rewriteUnder_enter stable step cutoff ordered)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- **A conversion at a frame holds under every number of binders**, on the shifted terms. -/
theorem convertibleKnowing_shiftN {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {K : EquationStore (Expr Base Const)}
    {left right : Expr Base Const} (converted : ConvertibleKnowing rules K left right) :
    ∀ depth : Nat,
      Relation.EqvGen (RewriteUnder (frameRules rules K) depth) (shiftN depth left)
        (shiftN depth right)
  | 0 => converted
  | depth + 1 =>
      eqvGen_enter stable (convertibleKnowing_shiftN stable converted depth) 0 (Nat.zero_le _)

/-! ## A frame that converts another frame's knowledge -/

/-- A step by rules that the target converts at every depth is a conversion of the target. -/
theorem eqvGen_of_rewriteUnder {R R' : Nat → Expr Base Const → Expr Base Const → Prop}
    (root : ∀ depth left right, R depth left right →
      Relation.EqvGen (RewriteUnder R' depth) left right)
    {depth : Nat} {e e' : Expr Base Const} (step : RewriteUnder R depth e e') :
    Relation.EqvGen (RewriteUnder R' depth) e e' := by
  induction step with
  | root rule => exact root _ _ _ rule
  | @piDomain depth A A' B _ ih =>
      exact under_congr (fun z => Expr.pi z B) (fun _ _ inner => .piDomain inner) ih
  | @piBody depth A B B' _ ih =>
      exact under_congr (fun z => Expr.pi A z) (fun _ _ inner => .piBody inner) ih
  | @lamDomain depth A A' b _ ih =>
      exact under_congr (fun z => Expr.lam z b) (fun _ _ inner => .lamDomain inner) ih
  | @lamBody depth A b b' _ ih =>
      exact under_congr (fun z => Expr.lam A z) (fun _ _ inner => .lamBody inner) ih
  | @appFunction depth f f' a _ ih =>
      exact under_congr (fun z => Expr.app z a) (fun _ _ inner => .appFunction inner) ih
  | @appArgument depth f a a' _ ih =>
      exact under_congr (fun z => Expr.app f z) (fun _ _ inner => .appArgument inner) ih
  | @andLeft depth p p' q _ ih =>
      exact under_congr (fun z => Expr.and z q) (fun _ _ inner => .andLeft inner) ih
  | @andRight depth p q q' _ ih =>
      exact under_congr (fun z => Expr.and p z) (fun _ _ inner => .andRight inner) ih
  | @orLeft depth p p' q _ ih =>
      exact under_congr (fun z => Expr.or z q) (fun _ _ inner => .orLeft inner) ih
  | @orRight depth p q q' _ ih =>
      exact under_congr (fun z => Expr.or p z) (fun _ _ inner => .orRight inner) ih
  | @impLeft depth p p' q _ ih =>
      exact under_congr (fun z => Expr.imp z q) (fun _ _ inner => .impLeft inner) ih
  | @impRight depth p q q' _ ih =>
      exact under_congr (fun z => Expr.imp p z) (fun _ _ inner => .impRight inner) ih
  | notBody _ ih => exact under_congr Expr.not (fun _ _ inner => .notBody inner) ih
  | @eqLeft depth a a' b _ ih =>
      exact under_congr (fun z => Expr.eq z b) (fun _ _ inner => .eqLeft inner) ih
  | @eqRight depth a b b' _ ih =>
      exact under_congr (fun z => Expr.eq a z) (fun _ _ inner => .eqRight inner) ih
  | @allDomain depth A A' b _ ih =>
      exact under_congr (fun z => Expr.all z b) (fun _ _ inner => .allDomain inner) ih
  | @allBody depth A b b' _ ih =>
      exact under_congr (fun z => Expr.all A z) (fun _ _ inner => .allBody inner) ih
  | @exDomain depth A A' b _ ih =>
      exact under_congr (fun z => Expr.ex z b) (fun _ _ inner => .exDomain inner) ih
  | @exBody depth A b b' _ ih =>
      exact under_congr (fun z => Expr.ex A z) (fun _ _ inner => .exBody inner) ih

/-- **A frame that converts every equation of another frame converts everything the other frame
converts.** -/
theorem convertibleKnowing_of_entailed {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {S K : EquationStore (Expr Base Const)}
    (entailed : ∀ equation ∈ S, ConvertibleKnowing rules K equation.1 equation.2)
    {A B : Expr Base Const} (converted : ConvertibleKnowing rules S A B) :
    ConvertibleKnowing rules K A B := by
  induction converted with
  | rel _ _ step =>
      refine eqvGen_of_rewriteUnder (R' := frameRules rules K) (fun depth left right rule => ?_) step
      rcases rule with direct | ⟨equation, member, atLeft, atRight⟩
      · exact Relation.EqvGen.rel _ _ (RewriteUnder.root (Or.inl direct))
      · rw [atLeft, atRight]
        exact convertibleKnowing_shiftN stable (entailed equation member) depth
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- With no knowledge, conversion at a frame is the conversion of the bubble. -/
theorem convertibleKnowing_nil_iff {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {A B : Expr Base Const} :
    ConvertibleKnowing rules [] A B ↔ Convertible rules A B :=
  ⟨convertible_of_knowing stable (fun _ member => absurd member List.not_mem_nil),
    convertibleKnowing_of_convertible []⟩

/-- An equation of the frame is a conversion at the frame. -/
theorem convertibleKnowing_of_mem {rules : Expr Base Const → Expr Base Const → Prop}
    {K : EquationStore (Expr Base Const)} {equation : Expr Base Const × Expr Base Const}
    (member : equation ∈ K) : ConvertibleKnowing rules K equation.1 equation.2 :=
  Relation.EqvGen.rel _ _ (RewriteUnder.root (Or.inr ⟨equation, member, rfl, rfl⟩))

/-! ## Peeling a definition -/

/-- The store with a definition, instantiated at the definition, is converted by the rest of the
store instantiated. -/
theorem peeled_entailed {rules : Expr Base Const → Expr Base Const → Prop} (k : Nat)
    (u : Expr Base Const) (K' : EquationStore (Expr Base Const)) :
    ∀ equation ∈ substStore k u ((bvar k, shiftN (k + 1) u) :: K'),
      ConvertibleKnowing rules (substStore k u K') equation.1 equation.2 := by
  intro equation member
  rcases List.mem_cons.mp member with rfl | inRest
  · show ConvertibleKnowing rules (substStore k u K') (substAt k u (bvar k))
      (substAt k u (shiftN (k + 1) u))
    rw [substAt_bvar_eq, substAt_shiftN_cancel u u k k (Nat.le_refl _)]
    exact Relation.EqvGen.refl _
  · exact convertibleKnowing_of_mem inRest

/-- **A definition is eliminated by instantiation, whatever else the frame knows.** -/
theorem peel_definition_iff {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules) (k : Nat)
    (u : Expr Base Const) (K' : EquationStore (Expr Base Const)) {A B : Expr Base Const} :
    ConvertibleKnowing rules ((bvar k, shiftN (k + 1) u) :: K') A B ↔
      ConvertibleKnowing rules (substStore k u K') (substAt k u A) (substAt k u B) := by
  constructor
  · intro converted
    exact convertibleKnowing_of_entailed shiftStable (peeled_entailed k u K')
      (convertibleKnowing_subst substStable k u converted)
  · intro instances
    have known : ((bvar k : Expr Base Const), shiftN (k + 1) u) ∈
        ((bvar k, shiftN (k + 1) u) :: K') := List.mem_cons.mpr (Or.inl rfl)
    have back : ConvertibleKnowing rules ((bvar k, shiftN (k + 1) u) :: K')
        (shiftAt k (substAt k u A)) (shiftAt k (substAt k u B)) := by
      refine convertibleKnowing_of_entailed shiftStable ?_
        (convertibleKnowing_shift shiftStable k instances)
      intro equation member
      obtain ⟨middle, inMiddle, rfl⟩ := List.mem_map.mp member
      obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp inMiddle
      show ConvertibleKnowing rules ((bvar k, shiftN (k + 1) u) :: K')
        (shiftAt k (substAt k u original.1)) (shiftAt k (substAt k u original.2))
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (converts_with_instance k u known original.1 0))
        (Relation.EqvGen.trans _ _ _
          (convertibleKnowing_of_mem (List.mem_cons.mpr (Or.inr inStore)))
          (converts_with_instance k u known original.2 0))
    exact Relation.EqvGen.trans _ _ _ (converts_with_instance k u known A 0)
      (Relation.EqvGen.trans _ _ _ back
        (Relation.EqvGen.symm _ _ (converts_with_instance k u known B 0)))

/-! ## Typing along a peeling -/

theorem entailed_shiftStore {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {S K : EquationStore (Expr Base Const)}
    (entailed : ∀ equation ∈ S, ConvertibleKnowing rules K equation.1 equation.2) :
    ∀ equation ∈ shiftStore S, ConvertibleKnowing rules (shiftStore K) equation.1 equation.2 := by
  intro equation member
  obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp member
  exact convertibleKnowing_shift stable 0 (entailed original inStore)

/-- **A frame that converts every equation of another frame types everything the other frame
types.** -/
theorem typedKnowing_of_entailed {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {S : EquationStore (Expr Base Const)}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} (typed : TypedKnowing rules S Γ e A) :
    ∀ K : EquationStore (Expr Base Const),
      (∀ equation ∈ S, ConvertibleKnowing rules K equation.1 equation.2) →
        TypedKnowing rules K Γ e A := by
  induction typed with
  | var lookup => exact fun _ _ => .var lookup
  | base b => exact fun _ _ => .base b
  | prop => exact fun _ _ => .prop
  | pi _ _ ihA ihB =>
      exact fun K entailed => .pi (ihA K entailed) (ihB _ (entailed_shiftStore stable entailed))
  | lam _ _ ihA ihb =>
      exact fun K entailed => .lam (ihA K entailed) (ihb _ (entailed_shiftStore stable entailed))
  | app _ _ ihf iha => exact fun K entailed => .app (ihf K entailed) (iha K entailed)
  | const τ c => exact fun _ _ => .const τ c
  | tyFam b => exact fun _ _ => .tyFam b
  | top => exact fun _ _ => .top
  | bot => exact fun _ _ => .bot
  | and _ _ ihp ihq => exact fun K entailed => .and (ihp K entailed) (ihq K entailed)
  | or _ _ ihp ihq => exact fun K entailed => .or (ihp K entailed) (ihq K entailed)
  | imp _ _ ihp ihq => exact fun K entailed => .imp (ihp K entailed) (ihq K entailed)
  | not _ ihp => exact fun K entailed => .not (ihp K entailed)
  | eq _ _ iha ihb => exact fun K entailed => .eq (iha K entailed) (ihb K entailed)
  | all _ _ ihA ihb =>
      exact fun K entailed => .all (ihA K entailed) (ihb _ (entailed_shiftStore stable entailed))
  | ex _ _ ihA ihb =>
      exact fun K entailed => .ex (ihA K entailed) (ihb _ (entailed_shiftStore stable entailed))
  | move _ converted ih =>
      exact fun K entailed =>
        .move (ih K entailed) (convertibleKnowing_of_entailed stable entailed converted)

/-- **A typing at a frame with a definition is a typing of the instance at the frame with the rest
of the knowledge instantiated.** -/
theorem typedKnowing_peel {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    {Θ : List (Expr Base Const)} {u C : Expr Base Const}
    (typedU : HasTypeInside rules Θ u C) (Δ : List (Expr Base Const))
    {Γ : List (Expr Base Const)} (split : Γ = Δ ++ C :: Θ)
    (K' : EquationStore (Expr Base Const)) {e A : Expr Base Const}
    (typed : TypedKnowing rules ((bvar Δ.length, shiftN (Δ.length + 1) u) :: K') Γ e A) :
    TypedKnowing rules (substStore Δ.length u K') (substCtx u Δ ++ Θ) (substAt Δ.length u e)
      (substAt Δ.length u A) :=
  typedKnowing_of_entailed shiftStable
    (typedKnowing_subst substStable shiftStable (typedKnowing_of_inside typedU []) typed Δ
      (substStore Δ.length u ((bvar Δ.length, shiftN (Δ.length + 1) u) :: K')) split
      (fun _ member => member)
      (fun _ member => by
        rw [liftStore_nil] at member
        exact absurd member List.not_mem_nil))
    (substStore Δ.length u K') (peeled_entailed Δ.length u K')

/-- **Uniqueness of types is inherited from the instantiated frame.** -/
theorem unique_of_peeled {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    {Θ : List (Expr Base Const)} {u C : Expr Base Const}
    (typedU : HasTypeInside rules Θ u C) (Δ : List (Expr Base Const))
    {Γ : List (Expr Base Const)} (split : Γ = Δ ++ C :: Θ)
    (K' : EquationStore (Expr Base Const)) {e A B : Expr Base Const}
    (uniqueBelow : ∀ A' B' : Expr Base Const,
      TypedKnowing rules (substStore Δ.length u K') (substCtx u Δ ++ Θ) (substAt Δ.length u e) A' →
      TypedKnowing rules (substStore Δ.length u K') (substCtx u Δ ++ Θ) (substAt Δ.length u e) B' →
        ConvertibleKnowing rules (substStore Δ.length u K') A' B')
    (first : TypedKnowing rules ((bvar Δ.length, shiftN (Δ.length + 1) u) :: K') Γ e A)
    (second : TypedKnowing rules ((bvar Δ.length, shiftN (Δ.length + 1) u) :: K') Γ e B) :
    ConvertibleKnowing rules ((bvar Δ.length, shiftN (Δ.length + 1) u) :: K') A B :=
  (peel_definition_iff substStable shiftStable Δ.length u K').mpr
    (uniqueBelow _ _ (typedKnowing_peel substStable shiftStable typedU Δ split K' first)
      (typedKnowing_peel substStable shiftStable typedU Δ split K' second))

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- The frame `n m : nat` that knows `m ≐ 0` and `n ≐ 0`; `m` is the newest variable. -/
def twoDefinitions : EquationStore AExpr := [(bvar 0, zeroE), (bvar 1, zeroE)]

/-- **Two definitions are eliminated one after the other.** At the frame, with no declared step,
two terms convert exactly when their instances at both variables are identical. -/
theorem two_definitions_conversion {A B : AExpr} :
    ConvertibleKnowing (fun _ _ => False) twoDefinitions A B ↔
      substAt 0 zeroE (substAt 0 zeroE A) = substAt 0 zeroE (substAt 0 zeroE B) :=
  (peel_definition_iff (rules := fun _ _ : AExpr => False) (fun _ _ rule => rule.elim)
    (fun _ _ rule => rule.elim) 0 zeroE [(bvar 1, zeroE)]).trans
    ((peel_definition_iff (rules := fun _ _ : AExpr => False) (fun _ _ rule => rule.elim)
      (fun _ _ rule => rule.elim) 0 zeroE []).trans
      ((convertibleKnowing_nil_iff (fun _ _ rule => rule.elim)).trans convertible_none_iff))

/-- `Vec m` converts with `Vec n` at the frame. -/
theorem vec_m_converts_with_vec_n :
    ConvertibleKnowing (fun _ _ => False) twoDefinitions (vec (bvar 0)) (vec (bvar 1)) :=
  two_definitions_conversion.mpr rfl

/-- For a third variable `p`, `Vec p` does not convert with `Vec 0` at the frame. -/
theorem vec_other_does_not_convert :
    ¬ ConvertibleKnowing (fun _ _ => False) twoDefinitions (vec (bvar 2)) (vec zeroE) := by
  intro converted
  have same := two_definitions_conversion.mp converted
  simp [substAt, vec, zeroE] at same

end Controls

/-! ## Axiom audit -/

#print axioms rewriteUnder_enter
#print axioms convertibleKnowing_shiftN
#print axioms convertibleKnowing_of_entailed
#print axioms convertibleKnowing_nil_iff
#print axioms peel_definition_iff
#print axioms typedKnowing_of_entailed
#print axioms typedKnowing_peel
#print axioms unique_of_peeled
#print axioms Controls.two_definitions_conversion
#print axioms Controls.vec_m_converts_with_vec_n
#print axioms Controls.vec_other_does_not_convert

end Mettapedia.TypeTheory.KnowledgePeeling
