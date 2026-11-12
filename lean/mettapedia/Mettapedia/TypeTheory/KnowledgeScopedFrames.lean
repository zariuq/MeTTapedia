import Mettapedia.TypeTheory.KnowledgePeeling
import Mettapedia.TypeTheory.KnowledgeUnsolved

/-!
# An ask at a frame with knowledge is an entailment of the calculus's frames

`KnowledgeFramesCore.entails_iff_convertible` joins assumed equations to the frames of the
calculus in the reading where an equation is used unchanged under binders. That reading captures
bound variables (`KnowledgeUnderBinders.Controls.raw_captures`). This module gives the join for
the scoped reading, where an equation used under binders is shifted past them, and for a bubble
with declared steps.

* `ScopedCongruence` is a relation on terms at each depth: an equivalence at each depth, closed
  under the term formers with the depth going up under a binder, and stable under entering a
  binder.
* `scopedFrames rules` is an instance of the calculus's `Frames`: its objects are the scoped
  congruences that validate the rules of a bubble, its morphisms are coarsenings.
* `rel_of_frameConversion` (soundness): a model of the bubble that validates a store relates
  everything the frame of that store converts, at every depth.
* `frameModel`: the conversion of a frame, at every depth, is itself such a model.
* `entails_iff_convertibleKnowing`: a store entails an equation over the models of a bubble
  exactly when the frame of the store converts its two sides.

So the conversion that `KnowledgeUnderBinders.TypedKnowing` uses at every node is the ask of the
calculus, for the frames `scopedFrames`.

## Controls

* `Controls.knowsZero_entails`: over the models, `n ≐ 0` entails `Vec n ≐ Vec 0`.
* `Controls.successors_have_a_separating_model`: a model validates `succ n ≐ succ 0` and does not
  relate `Vec n` with `Vec 0`. The models are congruences; they need not have injective
  constructors.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgeScopedFrames

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.TypeTheory.KnowledgeSolvedForm
open Mettapedia.TypeTheory.KnowledgePeeling
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

/-- A relation on terms at each depth: an equivalence at each depth, closed under the term
formers with the depth going up under a binder, and stable under entering a binder. -/
structure ScopedCongruence (Base : Type u) (Const : Ty Base → Type v) where
  /-- The terms the model identifies under `depth` binders. -/
  rel : Nat → Expr Base Const → Expr Base Const → Prop
  equivalence : ∀ depth : Nat, Equivalence (rel depth)
  compatible : ∀ {depth : Nat} {e e' : Expr Base Const}, RewriteUnder rel depth e e' → rel depth e e'
  enter : ∀ {depth : Nat} {e e' : Expr Base Const},
    rel depth e e' → rel (depth + 1) (shiftAt 0 e) (shiftAt 0 e')

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- What a model identifies at the top, it identifies under every number of binders, on the
shifted terms. -/
theorem ScopedCongruence.enterN (θ : ScopedCongruence Base Const) {left right : Expr Base Const}
    (related : θ.rel 0 left right) :
    ∀ depth : Nat, θ.rel depth (shiftN depth left) (shiftN depth right)
  | 0 => related
  | depth + 1 => θ.enter (θ.enterN related depth)

/-- A scoped congruence validates the rules of a bubble when it identifies the two sides of every
rule at every depth. -/
def Validates (rules : Expr Base Const → Expr Base Const → Prop)
    (θ : ScopedCongruence Base Const) : Prop :=
  ∀ (depth : Nat) (left right : Expr Base Const), rules left right → θ.rel depth left right

/-- **Soundness**: a model of a bubble that validates a store identifies everything the frame of
that store converts, at every depth. -/
theorem rel_of_frameConversion {rules : Expr Base Const → Expr Base Const → Prop}
    {θ : ScopedCongruence Base Const} (validRules : Validates rules θ)
    {K : EquationStore (Expr Base Const)}
    (validStore : ∀ equation ∈ K, θ.rel 0 equation.1 equation.2) {depth : Nat}
    {e e' : Expr Base Const}
    (converted : Relation.EqvGen (RewriteUnder (frameRules rules K) depth) e e') :
    θ.rel depth e e' := by
  induction converted with
  | rel _ _ step =>
      refine θ.compatible (RewriteUnder.mono (fun depth left right rule => ?_) step)
      rcases rule with direct | ⟨equation, member, atLeft, atRight⟩
      · exact validRules depth left right direct
      · rw [atLeft, atRight]
        exact θ.enterN (validStore equation member) depth
  | refl e => exact (θ.equivalence _).refl e
  | symm _ _ _ ih => exact (θ.equivalence _).symm ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact (θ.equivalence _).trans ihFirst ihSecond

/-- **The conversion of a frame, at every depth, is a scoped congruence.** -/
def frameModel (rules : Expr Base Const → Expr Base Const → Prop) (stable : ShiftStable rules)
    (K : EquationStore (Expr Base Const)) : ScopedCongruence Base Const where
  rel := fun depth => Relation.EqvGen (RewriteUnder (frameRules rules K) depth)
  equivalence := fun _ => Relation.EqvGen.is_equivalence _
  compatible := fun step => eqvGen_of_rewriteUnder (fun _ _ _ related => related) step
  enter := fun related => eqvGen_enter stable related 0 (Nat.zero_le _)

theorem frameModel_validates {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) (K : EquationStore (Expr Base Const)) :
    Validates rules (frameModel rules stable K) :=
  fun _ _ _ rule => Relation.EqvGen.rel _ _ (RewriteUnder.root (Or.inl rule))

/-- The models of a bubble: the scoped congruences that validate its rules. -/
abbrev BubbleModel (rules : Expr Base Const → Expr Base Const → Prop) :=
  {θ : ScopedCongruence Base Const // Validates rules θ}

/-- The frames of a bubble's models, with coarsenings as morphisms. A term is acted on by a
coarsening as itself; the equivalence of a frame is what its model identifies at the top. -/
def scopedFrames (rules : Expr Base Const → Expr Base Const → Prop) :
    Frames (fun _ : BubbleModel rules => Expr Base Const)
      (fun fine coarse : BubbleModel rules =>
        PLift (∀ (depth : Nat) (e e' : Expr Base Const),
          fine.1.rel depth e e' → coarse.1.rel depth e e')) where
  E := fun {θ} e e' => θ.1.rel 0 e e'
  equivalence := fun θ => θ.1.equivalence 0
  act := fun _ e => e
  id := fun _ => ⟨fun _ _ _ related => related⟩
  comp := fun later earlier =>
    ⟨fun depth e e' related => later.down depth e e' (earlier.down depth e e' related)⟩
  act_id := fun _ => rfl
  act_comp := fun _ _ _ => rfl
  preserves := fun {_ _} coarsening {_ _} related => coarsening.down 0 _ _ related

/-- A coarsening solves a store exactly when its target validates the store's equations. -/
theorem scoped_models_iff {rules : Expr Base Const → Expr Base Const → Prop}
    {fine coarse : BubbleModel rules}
    (coarsening : PLift (∀ (depth : Nat) (e e' : Expr Base Const),
      fine.1.rel depth e e' → coarse.1.rel depth e e'))
    (store : EquationStore (Expr Base Const)) :
    (scopedFrames rules).Models coarsening store ↔
      ∀ equation ∈ store, coarse.1.rel 0 equation.1 equation.2 :=
  Iff.rfl

/-- The bubble's own conversion, as a model of the bubble. -/
def bubbleModel {rules : Expr Base Const → Expr Base Const → Prop} (stable : ShiftStable rules)
    (K : EquationStore (Expr Base Const)) : BubbleModel rules :=
  ⟨frameModel rules stable K, frameModel_validates stable K⟩

/-- Every model of a bubble coarsens the bubble's conversion. -/
def fromConversion {rules : Expr Base Const → Expr Base Const → Prop} (stable : ShiftStable rules)
    (θ : BubbleModel rules) :
    PLift (∀ (depth : Nat) (e e' : Expr Base Const),
      (bubbleModel stable []).1.rel depth e e' → θ.1.rel depth e e') :=
  ⟨fun _ _ _ converted =>
    rel_of_frameConversion θ.2 (fun _ member => absurd member List.not_mem_nil) converted⟩

/-- **An ask at a frame with knowledge is an entailment of the calculus's frames**: a store entails
an equation over the models of a bubble exactly when the frame of the store converts its two
sides. -/
theorem entails_iff_convertibleKnowing {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) (store : EquationStore (Expr Base Const))
    (e e' : Expr Base Const) :
    (scopedFrames rules).Entails (a := bubbleModel stable []) store
        (fun θ _ => θ.1.rel 0 e e') ↔
      ConvertibleKnowing rules store e e' := by
  constructor
  · intro entailed
    exact entailed (bubbleModel stable store) (fromConversion stable (bubbleModel stable store))
      (fun _ member => convertibleKnowing_of_mem member)
  · intro converted θ _ solved
    exact rel_of_frameConversion θ.2 solved converted

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.KnowledgeUnderBinders.Controls
open Mettapedia.TypeTheory.KnowledgeUnsolved.Controls

/-- No declared step is stable under shifting. -/
theorem none_shiftStable : ShiftStable (fun _ _ : AExpr => False) :=
  fun _ _ rule => rule.elim

/-- **Over the models, `n ≐ 0` entails `Vec n ≐ Vec 0`.** -/
theorem knowsZero_entails :
    (scopedFrames (fun _ _ : AExpr => False)).Entails (a := bubbleModel none_shiftStable [])
      knowsZero (fun θ _ => θ.1.rel 0 (vec (bvar 0)) (vec zeroE)) :=
  (entails_iff_convertibleKnowing none_shiftStable knowsZero _ _).mpr solved_form_converts

/-- **A model validates `succ n ≐ succ 0` and separates `Vec n` from `Vec 0`.** -/
theorem successors_have_a_separating_model :
    ∃ θ : BubbleModel (fun _ _ : AExpr => False),
      (∀ equation ∈ knowsSuccessors, θ.1.rel 0 equation.1 equation.2) ∧
        ¬ θ.1.rel 0 (vec (bvar 0)) (vec zeroE) :=
  ⟨bubbleModel none_shiftStable knowsSuccessors,
    fun _ member => convertibleKnowing_of_mem member, successors_do_not_decompose⟩

/-- The knowledge `succ n ≐ succ 0` does not entail `Vec n ≐ Vec 0` over the models. -/
theorem successors_do_not_entail :
    ¬ (scopedFrames (fun _ _ : AExpr => False)).Entails (a := bubbleModel none_shiftStable [])
      knowsSuccessors (fun θ _ => θ.1.rel 0 (vec (bvar 0)) (vec zeroE)) :=
  fun entailed =>
    successors_do_not_decompose
      ((entails_iff_convertibleKnowing none_shiftStable knowsSuccessors _ _).mp entailed)

end Controls

/-! ## Axiom audit -/

#print axioms rel_of_frameConversion
#print axioms frameModel
#print axioms scopedFrames
#print axioms entails_iff_convertibleKnowing
#print axioms Controls.knowsZero_entails
#print axioms Controls.successors_have_a_separating_model
#print axioms Controls.successors_do_not_entail

end Mettapedia.TypeTheory.KnowledgeScopedFrames
