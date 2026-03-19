import Mettapedia.Logic.LP.Stratification
import Mathlib.Data.Fintype.Pi

/-!
# Grounding for First-Order Normal ProbLog Programs

This file lifts the existing ground normal-program semantics to a small
first-order surface layer. The intended reading is standard ProbLog practice:
first-order normal rules are grounded explicitly, and the grounded program is
then evaluated with the stratified semantics from `Stratification.lean`.

Positive example:
- A first-order rule `smokes(X) :- stress(X), not quit(X)` is represented as a
  `FirstOrderNormalClause` and grounded over all substitutions for `X`.

Negative example:
- This file does **not** introduce a new non-ground fixed-point semantics in
  parallel with the grounded one. The semantics is the grounded semantics.

0 sorry.
-/

namespace Mettapedia.Logic.LP

open Mettapedia.Logic.BDDCore
open Mettapedia.Logic.ProbLogCompilation

/-- A first-order goal literal for normal-rule bodies. -/
inductive FirstOrderGoalLit (σ : LPSignature) where
  | pos : Atom σ → FirstOrderGoalLit σ
  | neg : Atom σ → FirstOrderGoalLit σ
  | neq : Atom σ → Atom σ → FirstOrderGoalLit σ

/-- A first-order normal clause: first-order head plus first-order goal literals. -/
structure FirstOrderNormalClause (σ : LPSignature) where
  head : Atom σ
  body : List (FirstOrderGoalLit σ)

/-- Ground a first-order goal literal using a grounding substitution. -/
def Grounding.groundFirstOrderGoalLit {σ : LPSignature}
    (g : Grounding σ) : FirstOrderGoalLit σ → GoalLit σ
  | .pos a => .pos (g.groundAtom a)
  | .neg a => .neg (g.groundAtom a)
  | .neq a b => .neq (g.groundAtom a) (g.groundAtom b)

/-- Ground a list of first-order goal literals using a grounding substitution. -/
def Grounding.groundFirstOrderGoals {σ : LPSignature}
    (g : Grounding σ) (goals : List (FirstOrderGoalLit σ)) : List (GoalLit σ) :=
  goals.map g.groundFirstOrderGoalLit

@[simp] theorem Grounding.forall_mem_groundFirstOrderGoals_iff
    {σ : LPSignature} (g : Grounding σ) (goals : List (FirstOrderGoalLit σ))
    (P : GoalLit σ → Prop) :
    (∀ goal ∈ g.groundFirstOrderGoals goals, P goal) ↔
      ∀ goal ∈ goals, P (g.groundFirstOrderGoalLit goal) := by
  induction goals with
  | nil =>
      simp [Grounding.groundFirstOrderGoals]
  | cons goal goals ih =>
      simp [Grounding.groundFirstOrderGoals]

/-- Ground a first-order normal clause using a grounding substitution. -/
def Grounding.groundFirstOrderNormalClause {σ : LPSignature}
    (g : Grounding σ) (c : FirstOrderNormalClause σ) : NormalClause σ where
  head := g.groundAtom c.head
  body := c.body.map g.groundFirstOrderGoalLit

/-- A first-order normal ProbLog program: definite ProbLog core plus
    first-order normal rules whose semantics is obtained by explicit grounding. -/
structure FirstOrderNormalProbLogProgram (σ : LPSignature) (n : ℕ)
    extends ProbLogProgram σ n where
  normalRules : List (FirstOrderNormalClause σ)

/-- Explicitly ground all first-order normal rules.

Duplicates are harmless: the stratified semantics only asks whether a witnessing
ground clause is present, so repeated grounded clauses do not change the model. -/
noncomputable def FirstOrderNormalProbLogProgram.groundNormalRules
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderNormalProbLogProgram σ n) : List (NormalClause σ) :=
  prog.normalRules.flatMap fun c =>
    (Fintype.elems (α := Grounding σ)).toList.map fun g =>
      g.groundFirstOrderNormalClause c

/-- Convert a first-order normal ProbLog program to the existing ground
    normal-program layer by grounding all normal rules. -/
noncomputable def FirstOrderNormalProbLogProgram.toGroundNormalProgram
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderNormalProbLogProgram σ n) : NormalProbLogProgram σ n where
  probFacts := prog.probFacts
  probs := prog.probs
  rules := prog.rules
  facts_injective := prog.facts_injective
  normalRules := prog.groundNormalRules

/-- A first-order normal program is grounded-stratified by `s` when the explicit
    grounding of its normal rules respects `s`. -/
def FirstOrderNormalProbLogProgram.GroundedStratified
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderNormalProbLogProgram σ n) (s : Stratification σ) : Prop :=
  ∀ c ∈ prog.toGroundNormalProgram.normalRules, respectsStratification c s

/-- Query semantics for first-order normal ProbLog programs: ground the normal
    rules, then use the existing stratified semantics. -/
noncomputable def queryHoldsGroundedNormalA
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderNormalProbLogProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) (a : Fin n → Bool) : Prop :=
  queryHoldsNormalA prog.toGroundNormalProgram s q a

/-- Goal-literal interpretation for the grounded semantics of a first-order
    normal ProbLog program. -/
noncomputable def GoalLit.holdsGroundedNormal
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderNormalProbLogProgram σ n)
    (s : Stratification σ) (a : Fin n → Bool) : GoalLit σ → Prop :=
  GoalLit.holdsNormal prog.toGroundNormalProgram s a

/-- First-order goal-literal interpretation for the grounded semantics of a
    first-order normal ProbLog program. -/
noncomputable def FirstOrderGoalLit.holdsGroundedNormal
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderNormalProbLogProgram σ n)
    (goalGrounding : Grounding σ)
    (s : Stratification σ) (a : Fin n → Bool) : FirstOrderGoalLit σ → Prop
  | g => GoalLit.holdsGroundedNormal prog s a (goalGrounding.groundFirstOrderGoalLit g)

@[simp] theorem queryHoldsGroundedNormalA_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderNormalProbLogProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) (a : Fin n → Bool) :
    queryHoldsGroundedNormalA prog s q a =
      queryHoldsNormalA prog.toGroundNormalProgram s q a := rfl

@[simp] theorem GoalLit.holdsGroundedNormal_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderNormalProbLogProgram σ n)
    (s : Stratification σ) (a : Fin n → Bool) (g : GoalLit σ) :
    GoalLit.holdsGroundedNormal prog s a g =
      GoalLit.holdsNormal prog.toGroundNormalProgram s a g := rfl

@[simp] theorem FirstOrderGoalLit.holdsGroundedNormal_eq
    {σ : LPSignature} {n : ℕ}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)]
    (prog : FirstOrderNormalProbLogProgram σ n)
    (goalGrounding : Grounding σ)
    (s : Stratification σ) (a : Fin n → Bool) (g : FirstOrderGoalLit σ) :
    FirstOrderGoalLit.holdsGroundedNormal prog goalGrounding s a g =
      GoalLit.holdsGroundedNormal prog s a (goalGrounding.groundFirstOrderGoalLit g) := rfl

end Mettapedia.Logic.LP
