import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDispatch

/-!
# A solver step built from the qualified rules

One round on a residual store, in this order:

1. **refute** when some equation is a certified rigid clash (`ContextualDependentRigid`);
2. **convert** when the bounded typed eta conversion scan discharges at least one equation; the
   context is unchanged and the store is shorter;
3. **solve** the newest declaration when the existing dispatcher finds a flexible definition
   anywhere in the store; skipped equations, including heterogeneous ones, are transported and
   scanned again, so a definition of a type variable wakes the equations that wait for it;
4. otherwise **stuck**: only residual or postponed equations remain for this step.

The rank is the number of declarations of the context, then the length of the store. Each
progressing round lowers it: conversion keeps the context and shortens the store, and the
dispatcher removes the newest declaration (`ContextualDependentDispatch.search_target`). A
refutation is reported only for a clash, so a store whose equations are merely outside the
step's reach, such as a non-pattern equation with a solution, is never refuted
(`round_refuted_clashes`).

The newest declaration of a context is read from its last entry, whose universe is synthesized
by the existing checker (`newestOf`). The newest-variable dispatcher is the step's solving rule;
the general pattern step of the dependent unifier instantiates the same `Solver` interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentWorklist

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- A context presented as an older context extended by its newest declaration. -/
structure Newest (Γ : Context S.R) where
  base : Context S.R
  type : TypeOver base
  same : Γ = extend base type

/-- Run a computation at the newest declaration, keeping the decrease of the context. -/
def throughNewest {Γ : Context S.R} (view : Newest Γ) (problem : EquationStore (TotalTerm Γ))
    (solve : (stored : EquationStore (TotalTerm (extend view.base view.type))) →
      Option {update : Update S.levels stored // update.target.arity < view.base.arity + 1}) :
    Option {update : Update S.levels problem // update.target.arity < Γ.arity} := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact solve problem

/-- The rank of a store: the number of declarations, then the number of equations. -/
def size {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Nat × Nat :=
  (Γ.arity, problem.length)

theorem formedPrefix {n : Nat} {raw : Ctx Head n} {code : Tm Head n}
    (formed : CtxFormed S.R (.snoc raw code)) : CtxFormed S.R raw := by
  cases formed
  assumption

theorem context_eq {n : Nat} {first second : Ctx Head n} (same : first = second)
    (firstFormed : CtxFormed S.R first) (secondFormed : CtxFormed S.R second) :
    (⟨n, first, firstFormed⟩ : Context S.R) = ⟨n, second, secondFormed⟩ := by
  subst same
  rfl

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (facts : FormFacts S.R S.roles)
  (complete : AlgorithmicComplete S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **The newest declaration** of a context, with its universe synthesized by the checker. -/
def newestOf (fuel : Nat) : (Γ : Context S.R) → Option (Newest Γ)
  | ⟨_, .nil, _⟩ => none
  | ⟨_, .snoc raw code, formed⟩ => do
      let checked ← ContextualDependentPruning.formType facts roots heads algebra declared choices
        reducer fuel ⟨_, raw, formedPrefix formed⟩ code
      return ⟨⟨_, raw, formedPrefix formed⟩, checked.val, by
        obtain ⟨type, same⟩ := checked
        exact context_eq (congrArg (Ctx.snoc raw) same.symm) formed _⟩

/-- **The dispatcher at the newest declaration**: a successful search removes it. -/
def dispatchNewest (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type))) :
    Option {update : Update S.levels problem // update.target.arity < Γ.arity + 1} :=
  match found : ContextualDependentDispatch.search facts roots heads algebra declared choices
      reducer fuel type problem with
  | none => none
  | some updated => some ⟨updated.then (conversion facts roots heads algebra reducer fuel
      updated.remaining), by
        change updated.target.arity < Γ.arity + 1
        rw [ContextualDependentDispatch.search_target facts roots heads algebra declared choices
          reducer type problem updated found]
        exact Nat.lt_succ_self _⟩

/-- **One round of the step.** -/
def round (fuel : Nat) {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    Round S.levels size problem :=
  if clash : ContextualDependentRigid.storeClashes problem = true then
    .refuted (ContextualDependentRigid.not_solvable_of_storeClashes rigid facts complete clash)
  else if shorter :
      (Conversion.scan facts roots heads algebra reducer fuel problem).length < problem.length then
    .progress (conversion facts roots heads algebra reducer fuel problem) (Prod.Lex.right _ shorter)
  else
    match newestOf facts roots heads algebra declared choices reducer fuel Γ with
    | none => .stuck
    | some view =>
        match throughNewest view problem
            (dispatchNewest facts roots heads algebra declared choices reducer fuel view.type) with
        | none => .stuck
        | some ⟨update, smaller⟩ => .progress update (Prod.Lex.left _ _ smaller)

/-- **The step as a solver** for the worklist driver. -/
def solver (fuel : Nat) : Solver S.levels where
  rank := size
  round := round rigid facts complete roots heads algebra declared choices reducer fuel

/-- **A refutation is a certified clash**: the step refutes nothing else. -/
theorem round_refuted_clashes (fuel : Nat) {Γ : Context S.R}
    {problem : EquationStore (TotalTerm Γ)} {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : round rigid facts complete roots heads algebra declared choices reducer fuel problem =
      .refuted absent) :
    ContextualDependentRigid.storeClashes problem = true := by
  unfold round at refuted
  split at refuted
  · assumption
  · split at refuted
    · cases refuted
    · split at refuted
      · cases refuted
      · split at refuted
        · cases refuted
        · cases refuted

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
theorem throughNewest_nil {Γ : Context S.R} (view : Newest Γ)
    (solve : (stored : EquationStore (TotalTerm (extend view.base view.type))) →
      Option {update : Update S.levels stored // update.target.arity < view.base.arity + 1})
    (nothing : solve [] = none) : throughNewest view [] solve = none := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact nothing

/-- **The step does nothing at the empty store.** -/
theorem round_nil (fuel : Nat) {Γ : Context S.R} :
    round rigid facts complete roots heads algebra declared choices reducer fuel
      ([] : EquationStore (TotalTerm Γ)) = .stuck := by
  unfold round
  rw [dif_neg (by simp [ContextualDependentRigid.storeClashes])]
  rw [dif_neg (by simp [Conversion.scan])]
  cases newestOf facts roots heads algebra declared choices reducer fuel Γ with
  | none => rfl
  | some view =>
      simp only
      rw [throughNewest_nil view _ rfl]

/-- **The stores the step decides form a fragment** for the worklist driver. -/
def decidedFragment (fuel : Nat) :
    Fragment (solver rigid facts complete roots heads algebra declared choices reducer fuel) :=
  Reaches.fragment _ (round_nil rigid facts complete roots heads algebra declared choices reducer fuel)

end ContextualDependentWorklist
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
