import Mettapedia.TypeTheory.KnowledgePeeling

/-!
# Frames whose knowledge is a sequence of definitions

`KnowledgePeeling.peel_definition_iff` eliminates one definition from a frame. This module follows
the elimination to the end.

* `Peelable` is a store that is emptied one definition at a time: its first equation defines a
  variable, and the rest, instantiated at that definition, is peelable again. A later definition
  may mention variables defined earlier.
* `peelable_conversion`: for a peelable store there is an instantiation of terms under which the
  frame's conversion is the conversion of the bubble.
* `SolvedFrame` is a peelable store together with a context in which each defining term is typed
  below its variable.
* `solvedFrame_unique`: at a solved frame of a bubble with coherent conversion, the types of a
  term convert at the frame.

So for the frames that a successful unification produces, knowledge costs nothing: conversion is
the bubble's conversion of instances, and types stay unique.

## Controls

* `Controls.twoDefinitions_peelable`, `Controls.vector_frame_solved`: the frames used in the
  earlier controls are of this kind.
* `Controls.successors_not_peelable`: the store `succ n ≐ succ 0` is not peelable. Its first
  equation does not define a variable.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgeDefinitions

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.TypeTheory.KnowledgeSolvedForm
open Mettapedia.TypeTheory.KnowledgePeeling
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A store that is emptied one definition at a time. -/
inductive Peelable : EquationStore (Expr Base Const) → Prop where
  | nil : Peelable []
  | cons (k : Nat) (u : Expr Base Const) {K' : EquationStore (Expr Base Const)} :
      Peelable (substStore k u K') → Peelable ((bvar k, shiftN (k + 1) u) :: K')

/-- **A peelable store is an instantiation.** There is an instantiation of terms under which the
conversion of the frame is the conversion of the bubble. -/
theorem peelable_conversion {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    {K : EquationStore (Expr Base Const)} (peelable : Peelable K) :
    ∃ instantiate : Expr Base Const → Expr Base Const, ∀ A B : Expr Base Const,
      ConvertibleKnowing rules K A B ↔ Convertible rules (instantiate A) (instantiate B) := by
  induction peelable with
  | nil => exact ⟨id, fun _ _ => convertibleKnowing_nil_iff shiftStable⟩
  | cons k u _ ih =>
      obtain ⟨instantiate, decided⟩ := ih
      exact ⟨fun e => instantiate (substAt k u e), fun A B =>
        (peel_definition_iff substStable shiftStable k u _).trans (decided _ _)⟩

/-- The first equation of a peelable store defines a variable. -/
theorem Peelable.head_defines {K : EquationStore (Expr Base Const)} (peelable : Peelable K)
    {left right : Expr Base Const} {rest : EquationStore (Expr Base Const)}
    (shape : K = (left, right) :: rest) : ∃ k : Nat, left = bvar k := by
  cases peelable with
  | nil => cases shape
  | cons k u _ =>
      obtain ⟨head, _⟩ := List.cons.inj shape
      exact ⟨k, (congrArg Prod.fst head).symm⟩

/-- A frame whose knowledge is a sequence of definitions, each defining term typed in the bubble
below its variable. -/
inductive SolvedFrame (rules : Expr Base Const → Expr Base Const → Prop) :
    EquationStore (Expr Base Const) → List (Expr Base Const) → Prop where
  | nil (Γ : List (Expr Base Const)) : SolvedFrame rules [] Γ
  | cons {Θ : List (Expr Base Const)} {u C : Expr Base Const}
      (typedU : HasTypeInside rules Θ u C) (Δ : List (Expr Base Const))
      {K' : EquationStore (Expr Base Const)} :
      SolvedFrame rules (substStore Δ.length u K') (substCtx u Δ ++ Θ) →
        SolvedFrame rules ((bvar Δ.length, shiftN (Δ.length + 1) u) :: K') (Δ ++ C :: Θ)

/-- The store of a solved frame is peelable. -/
theorem SolvedFrame.peelable {rules : Expr Base Const → Expr Base Const → Prop}
    {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
    (solved : SolvedFrame rules K Γ) : Peelable K := by
  induction solved with
  | nil _ => exact .nil
  | cons _ Δ _ ih => exact .cons Δ.length _ ih

/-- **At a solved frame, the types of a term convert at the frame**, when the conversion of the
bubble is coherent. -/
theorem solvedFrame_unique {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    (coherent : Coherent (Convertible rules)) {K : EquationStore (Expr Base Const)}
    {Γ : List (Expr Base Const)} (solved : SolvedFrame rules K Γ) :
    ∀ {e A B : Expr Base Const}, TypedKnowing rules K Γ e A → TypedKnowing rules K Γ e B →
      ConvertibleKnowing rules K A B := by
  induction solved with
  | nil _ =>
      intro e A B first second
      exact convertibleKnowing_of_convertible []
        (typed_unique coherent
          (typedKnowing_discharge shiftStable first
            (fun _ member => absurd member List.not_mem_nil))
          (typedKnowing_discharge shiftStable second
            (fun _ member => absurd member List.not_mem_nil)))
  | cons typedU Δ _ ih =>
      intro e A B first second
      exact unique_of_peeled substStable shiftStable typedU Δ rfl _
        (fun _ _ below₁ below₂ => ih below₁ below₂) first second

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.KnowledgeUnderBinders.Controls
open Mettapedia.TypeTheory.KnowledgePeeling.Controls

/-- The frame that knows `m ≐ 0` and `n ≐ 0` is peelable. -/
theorem twoDefinitions_peelable : Peelable twoDefinitions :=
  Peelable.cons 0 zeroE (K' := [(bvar 1, zeroE)]) (Peelable.cons 0 zeroE (K' := []) Peelable.nil)

/-- The frame `n : nat, v : Vec n` that knows `n ≐ 0` is a solved frame, with no declared
step. -/
theorem vector_frame_solved : SolvedFrame (fun _ _ => False) vectorKnowledge vecContext :=
  SolvedFrame.cons (Θ := []) (u := zeroE) (C := natType) (K' := [])
    (BubbleTypingInside.hasTypeInside_none_iff.mpr (HasType.const _ ArithConst.zero))
    [vec (bvar 0)] (SolvedFrame.nil _)

/-- **A store whose first equation does not define a variable is not peelable**:
`succ n ≐ succ 0`. -/
theorem successors_not_peelable :
    ¬ Peelable ([(succE (bvar 0), succE zeroE)] : EquationStore AExpr) := by
  intro peelable
  obtain ⟨k, defines⟩ := peelable.head_defines rfl
  simp [succE] at defines

end Controls

/-! ## Axiom audit -/

#print axioms peelable_conversion
#print axioms Peelable.head_defines
#print axioms SolvedFrame.peelable
#print axioms solvedFrame_unique
#print axioms Controls.twoDefinitions_peelable
#print axioms Controls.vector_frame_solved
#print axioms Controls.successors_not_peelable

end Mettapedia.TypeTheory.KnowledgeDefinitions
