import Mettapedia.Logic.BDD.ProbMeTTaBridge
import Mettapedia.Logic.LP.NormalGrounding

/-!
# First-Order Normal ProbLog Bridge

This file lifts the current ground crown theorem to a first-order normal-program
surface layer by explicit grounding.

Positive example:
- A function-free normal rule with variables can now be supplied as a
  `FirstOrderNormalClause`; the theorem applies to its grounded semantics.

Negative example:
- This file does **not** yet introduce first-order annotated disjunction syntax.
  Ground or already-expanded ADs still flow through the existing AD translation
  pipeline.

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore

open Mettapedia.Logic.LP

/-- **First-order normal ProbLog equivalence via grounding.**

    For a function-free first-order normal ProbLog program, explicitly grounding
    the normal rules reduces the problem to the existing ground crown theorem.
    This closes the remaining theorem gap for non-ground normal rules without
    introducing a second semantics: the semantics is the grounded semantics. -/
theorem problog_functionFree_normal_equivalence {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderNormalProbLogProgram σ n)
    (s : Stratification σ)
    (_hstrat : prog.GroundedStratified s)
    (goalsQ goalsE : List (GoalLit σ))
    (env : Fin n → ENNReal) (henv : ∀ i, env i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE, GoalLit.holdsGroundedNormal prog s a g) ∧
      assignmentWeight env a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE env ≠ 0 ∧
      bdd_wmc fQE env / bdd_wmc fE env =
        weightedSat fQE.eval env / weightedSat fE.eval env ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE, GoalLit.holdsGroundedNormal prog s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE, GoalLit.holdsGroundedNormal prog s a g) := by
  simpa using
    (problog_full_ground_equivalence prog.toGroundNormalProgram s goalsQ goalsE env henv hEpos)

/-- **First-order normal ProbLog surface equivalence via grounding.**

    This is the same bridge as `problog_functionFree_normal_equivalence`, but
    exposed at a first-order query/evidence surface. A grounding substitution
    chooses the concrete ground instance of the first-order goals. -/
theorem problog_functionFree_normal_surface_equivalence {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (prog : FirstOrderNormalProbLogProgram σ n)
    (s : Stratification σ)
    (_hstrat : prog.GroundedStratified s)
    (goalGrounding : Grounding σ)
    (goalsQ goalsE : List (FirstOrderGoalLit σ))
    (env : Fin n → ENNReal) (henv : ∀ i, env i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE, FirstOrderGoalLit.holdsGroundedNormal prog goalGrounding s a g) ∧
      assignmentWeight env a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE env ≠ 0 ∧
      bdd_wmc fQE env / bdd_wmc fE env =
        weightedSat fQE.eval env / weightedSat fE.eval env ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE, FirstOrderGoalLit.holdsGroundedNormal prog goalGrounding s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE, FirstOrderGoalLit.holdsGroundedNormal prog goalGrounding s a g) := by
  obtain ⟨a, haE, haw⟩ := hEpos
  have hEposGround :
      ∃ a : Fin n → Bool,
        (∀ g ∈ goalGrounding.groundFirstOrderGoals goalsE,
          GoalLit.holdsGroundedNormal prog s a g) ∧
        assignmentWeight env a ≠ 0 := by
    refine ⟨a, ?_, haw⟩
    rw [Grounding.forall_mem_groundFirstOrderGoals_iff]
    simpa [FirstOrderGoalLit.holdsGroundedNormal] using haE
  obtain ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, hiffQE, hiffE⟩ :=
    problog_functionFree_normal_equivalence
      prog s _hstrat
      (goalGrounding.groundFirstOrderGoals goalsQ)
      (goalGrounding.groundFirstOrderGoals goalsE)
      env henv hEposGround
  refine ⟨fQE, fE, hordQE, hordE, hwmcE, hratio, ?_, ?_⟩
  · intro a'
    constructor
    · intro hf
      have hGround :
          ∀ g ∈ goalGrounding.groundFirstOrderGoals (goalsQ ++ goalsE),
            GoalLit.holdsGroundedNormal prog s a' g := by
        simpa [Grounding.groundFirstOrderGoals, List.map_append] using (hiffQE a').mp hf
      have hFirstOrder :
          ∀ g ∈ goalsQ ++ goalsE,
            GoalLit.holdsGroundedNormal prog s a'
              (goalGrounding.groundFirstOrderGoalLit g) :=
        (Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding (goalsQ ++ goalsE)
          (fun g => GoalLit.holdsGroundedNormal prog s a' g)).1 hGround
      simpa [FirstOrderGoalLit.holdsGroundedNormal] using hFirstOrder
    · intro hf
      have hFirstOrder :
          ∀ g ∈ goalsQ ++ goalsE,
            GoalLit.holdsGroundedNormal prog s a'
              (goalGrounding.groundFirstOrderGoalLit g) := by
        simpa [FirstOrderGoalLit.holdsGroundedNormal] using hf
      have hGround :
          ∀ g ∈ goalGrounding.groundFirstOrderGoals (goalsQ ++ goalsE),
            GoalLit.holdsGroundedNormal prog s a' g :=
        (Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding (goalsQ ++ goalsE)
          (fun g => GoalLit.holdsGroundedNormal prog s a' g)).2 hFirstOrder
      exact (hiffQE a').2 (by
        simpa [Grounding.groundFirstOrderGoals, List.map_append] using hGround)
  · intro a'
    constructor
    · intro hf
      have hGround :
          ∀ g ∈ goalGrounding.groundFirstOrderGoals goalsE,
            GoalLit.holdsGroundedNormal prog s a' g := (hiffE a').mp hf
      have hFirstOrder :
          ∀ g ∈ goalsE,
            GoalLit.holdsGroundedNormal prog s a'
              (goalGrounding.groundFirstOrderGoalLit g) :=
        (Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding goalsE
          (fun g => GoalLit.holdsGroundedNormal prog s a' g)).1 hGround
      simpa [FirstOrderGoalLit.holdsGroundedNormal] using hFirstOrder
    · intro hf
      have hFirstOrder :
          ∀ g ∈ goalsE,
            GoalLit.holdsGroundedNormal prog s a'
              (goalGrounding.groundFirstOrderGoalLit g) := by
        simpa [FirstOrderGoalLit.holdsGroundedNormal] using hf
      exact (hiffE a').2
        ((Grounding.forall_mem_groundFirstOrderGoals_iff
          goalGrounding goalsE
          (fun g => GoalLit.holdsGroundedNormal prog s a' g)).2 hFirstOrder)

end Mettapedia.Logic.BDDCore
