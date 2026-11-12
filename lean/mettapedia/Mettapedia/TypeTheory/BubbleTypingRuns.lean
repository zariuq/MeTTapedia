import Mettapedia.TypeTheory.ConversionRuns
import Mettapedia.TypeTheory.KnowledgeFramesCore

/-!
# Typing in a bubble is global typing and a run

On the dependent comparison core, typing in a bubble is syntax-directed typing followed by one
conversion of the bubble (`BubbleConversion.hasTypeIn_iff`). With `ConversionRuns`, that conversion
is a run of the bubble's conversion step.

* `convertible_iff_conv`: the bubble conversion of the core is the existence of free conversion
  evidence of `coreBubbles`.
* `convertible_iff_run`: two expressions are convertible in a bubble exactly when a run of its
  conversion step leads from one to the other.
* **`hasTypeIn_iff_run`**: a term has a type in a bubble exactly when it has a type in the global
  judgment and a run of the bubble's conversion step leads from that type to the asked one.
* `hasTypeIn_unique`: two types of one term in a bubble are joined by a run.
* `run_none`: the bubble that declares no step has only runs that stay where they are, so its
  typing is the global judgment (`BubbleConversion.hasTypeIn_none_iff`).
* `hasTypeIn_withKnowledge_iff_run`: at a frame with assumed equations, the declared steps are
  those of the bubble and the frame's equations (`withKnowledge`), and typing is global typing
  and a run of that step.

Controls: `v : Vec n` is typed at `Vec (n + 0)` by a run of the recursion equations
(`Controls.addZero_typed_by_run`) and at `Vec (0 + n)` by none (`Controls.zeroAdd_no_typing_run`);
in the frame that knows `n ≐ 0` it is typed at `Vec 0` by a run of the frame's equation alone
(`Controls.knowledge_typed_by_run`).

Scope: the comparison core of `SimpleSliceOfDependent`, whose bubble typing applies conversion
once, at the end. The frame's equations in `withKnowledge` are raw rewrite rules; they are the
frame's knowledge at positions outside binders (`KnowledgeUnderBinders`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleTypingRuns

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.FreeConversion
open Mettapedia.TypeTheory.JudgmentalEquality
open Mettapedia.TypeTheory.ConversionRuns
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

variable (Base Const) in
/-- The bubbles of the comparison core. -/
abbrev bubbles : Bubbles.{0, max u v, max u v, 0} Unit := coreBubbles (Base := Base) (Const := Const)

/-- Free conversion evidence of the core's bubbles is a conversion. -/
theorem convertible_of_conv {rules : Expr Base Const → Expr Base Const → Prop} :
    ∀ {e e' : Expr Base Const}, (bubbles Base Const).Conv rules (index := ()) e e' →
      Convertible rules e e'
  | _, _, .step step => Relation.EqvGen.rel _ _ (PLift.down step)
  | _, _, .refl _ => Relation.EqvGen.refl _
  | _, _, .symm path => Relation.EqvGen.symm _ _ (convertible_of_conv path)
  | _, _, .trans first second =>
      Relation.EqvGen.trans _ _ _ (convertible_of_conv first) (convertible_of_conv second)

/-- The bubble conversion of the core is the existence of free conversion evidence. -/
theorem convertible_iff_conv {rules : Expr Base Const → Expr Base Const → Prop}
    {e e' : Expr Base Const} :
    Convertible rules e e' ↔ Nonempty ((bubbles Base Const).Conv rules (index := ()) e e') := by
  constructor
  · intro converted
    induction converted with
    | rel _ _ step => exact ⟨ConversionEvidence.step (PLift.up step)⟩
    | refl e => exact ⟨convRefl (bubbles Base Const) rules (index := ()) e⟩
    | symm _ _ _ ih => exact ih.elim fun path => ⟨ConversionEvidence.symm path⟩
    | trans _ _ _ _ _ ihFirst ihSecond =>
        exact ihFirst.elim fun first => ihSecond.elim fun second =>
          ⟨ConversionEvidence.trans first second⟩
  · exact fun evidence => evidence.elim convertible_of_conv

/-- **Conversion in a bubble of the core is reachability by runs of its conversion step.** -/
theorem convertible_iff_run {rules : Expr Base Const → Expr Base Const → Prop}
    {e e' : Expr Base Const} (ledger : EquationStore (Expr Base Const)) (clock : Nat) :
    Convertible rules e e' ↔
      ∃ run : (conversionStep (bubbles Base Const) rules ()).Run ⟨e, ledger, clock⟩,
        run.last.cursor = e' :=
  convertible_iff_conv.trans (conv_iff_run (B := bubbles Base Const) (bubble := rules) ledger clock)

/-- **Typing in a bubble is global typing and a run.** A term has a type in a bubble exactly
when it has a type in the global judgment and a run of the bubble's conversion step leads from
that type to the asked one. -/
theorem hasTypeIn_iff_run {rules : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e B : Expr Base Const} :
    HasTypeIn rules Γ e B ↔
      ∃ A, HasType Γ e A ∧
        ∃ run : (conversionStep (bubbles Base Const) rules ()).Run ⟨A, [], 0⟩,
          run.last.cursor = B := by
  rw [hasTypeIn_iff]
  constructor
  · rintro ⟨A, typing, converted⟩
    exact ⟨A, typing, (convertible_iff_run [] 0).mp converted⟩
  · rintro ⟨A, typing, reached⟩
    exact ⟨A, typing, (convertible_iff_run [] 0).mpr reached⟩

/-- **A term has one type up to the bubble's conversion**, hence up to a run: two types of one term
in a bubble are joined by a run of its conversion step. -/
theorem hasTypeIn_unique {rules : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e A B : Expr Base Const}
    (first : HasTypeIn rules Γ e A) (second : HasTypeIn rules Γ e B) :
    ∃ run : (conversionStep (bubbles Base Const) rules ()).Run ⟨A, [], 0⟩, run.last.cursor = B := by
  obtain ⟨firstBase, firstTyping, firstConverted⟩ := hasTypeIn_iff.mp first
  obtain ⟨secondBase, secondTyping, secondConverted⟩ := hasTypeIn_iff.mp second
  have same := firstTyping.unique secondTyping
  subst same
  exact (convertible_iff_run [] 0).mp
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ firstConverted) secondConverted)

/-- A zigzag of the bubble that declares no step stays where it is. -/
theorem zigzag_none : ∀ {e e' : Expr Base Const},
    Zigzag (bubbles Base Const) (fun _ _ => False) (index := ()) e e' → e = e'
  | _, _, .nil _ => rfl
  | _, _, .forward step _ => (rewrite_none (PLift.down step)).elim
  | _, _, .backward step _ => (rewrite_none (PLift.down step)).elim

/-- **With no declared step, every run ends where it starts.** -/
theorem run_none {goal : Goal (bubbles Base Const) ()}
    (run : (conversionStep (bubbles Base Const) (fun _ _ => False) ()).Run goal) :
    run.last.cursor = goal.cursor :=
  (zigzag_none (zigzagOfRun run)).symm

/-- The declared steps at a frame with assumed equations: those of the bubble, and the frame's
equations. -/
def withKnowledge (rules : Expr Base Const → Expr Base Const → Prop)
    (store : EquationStore (Expr Base Const)) : Expr Base Const → Expr Base Const → Prop :=
  fun left right => rules left right ∨ assumed store left right

/-- **Typing in a bubble, at a frame with assumed equations, is global typing and a run** whose
firings carry a declared step of the bubble or an equation of the frame. -/
theorem hasTypeIn_withKnowledge_iff_run {rules : Expr Base Const → Expr Base Const → Prop}
    {store : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)}
    {e B : Expr Base Const} :
    HasTypeIn (withKnowledge rules store) Γ e B ↔
      ∃ A, HasType Γ e A ∧
        ∃ run : (conversionStep (bubbles Base Const) (withKnowledge rules store) ()).Run ⟨A, [], 0⟩,
          run.last.cursor = B :=
  hasTypeIn_iff_run

/-- Typing with the bubble alone is typing at every frame of the bubble: what the bubble types
stays typed when equations are assumed. -/
theorem hasTypeIn_withKnowledge_of_bubble {rules : Expr Base Const → Expr Base Const → Prop}
    (store : EquationStore (Expr Base Const)) {Γ : List (Expr Base Const)} {e B : Expr Base Const}
    (typed : HasTypeIn rules Γ e B) : HasTypeIn (withKnowledge rules store) Γ e B :=
  hasTypeIn_mono (fun _ _ rule => Or.inl rule) typed

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.KnowledgeFramesCore.Controls

/-- **`v : Vec n` is typed at `Vec (n + 0)` by a run of the recursion equations.** -/
theorem addZero_typed_by_run :
    ∃ A, HasType vecContext (bvar 0) A ∧
      ∃ run : (conversionStep (bubbles Unit ArithConst) (bubbleRules false) ()).Run ⟨A, [], 0⟩,
        run.last.cursor = vec (addE (bvar 1) zeroE) :=
  hasTypeIn_iff_run.mp (vec_addZero_inside false)

/-- **It is typed at `Vec (0 + n)` by no run of them.** -/
theorem zeroAdd_no_typing_run :
    ¬ ∃ A, HasType vecContext (bvar 0) A ∧
      ∃ run : (conversionStep (bubbles Unit ArithConst) (bubbleRules false) ()).Run ⟨A, [], 0⟩,
        run.last.cursor = vec (addE zeroE (bvar 1)) :=
  fun reached => vec_zeroAdd_not_arith (hasTypeIn_iff_run.mpr reached)

/-- **In the frame that knows `n ≐ 0`, `v` is typed at `Vec 0` by a run of the frame's equation.** -/
theorem knowledge_typed_by_run :
    ∃ A, HasType vecContext (bvar 0) A ∧
      ∃ run : (conversionStep (bubbles Unit ArithConst) (assumed knowsZero) ()).Run ⟨A, [], 0⟩,
        run.last.cursor = vec zeroE :=
  hasTypeIn_iff_run.mp vec_at_zero

end Controls

/-! ## Axiom audit -/

#print axioms convertible_iff_conv
#print axioms convertible_iff_run
#print axioms hasTypeIn_iff_run
#print axioms hasTypeIn_unique
#print axioms run_none
#print axioms hasTypeIn_withKnowledge_iff_run
#print axioms hasTypeIn_withKnowledge_of_bubble
#print axioms Controls.addZero_typed_by_run
#print axioms Controls.zeroAdd_no_typing_run
#print axioms Controls.knowledge_typed_by_run

end Mettapedia.TypeTheory.BubbleTypingRuns
