import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.DAGLevelization

/-!
# Reverse-error uniqueness on arbitrary computation DAGs

Millidge, Tschantz, and Buckley (2020), *Predictive Coding Approximates
Backprop along Arbitrary Computation Graphs*, identify the equilibrium
prediction-error equation with reverse-mode differentiation and appeal to
induction through the graph.

This file makes that induction explicit for every finite ranked scalar
`SharedLatentDAG`.  A reverse-error field is fixed on a chosen terminal set and
obeys full edge-occurrence aggregation everywhere else.  The rank carried by
the graph gives a well-founded reverse order, so these two conditions determine
the entire field uniquely.  Consequently, an equilibrium predictive-coding
error force equals any reverse-mode field satisfying the same terminal
condition.

The result is deliberately conditional on existence of the equilibrium and on
the terminal error identity.  It does not claim that an arbitrary discretized
settling loop converges, nor that a free-equilibrium parameter gradient uses
the forward-pass activation required by ordinary backpropagation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

section ReverseRecursion

variable {Node Edge : Type*} [Fintype Node] [Fintype Edge]

/-- Largest node rank in a finite ranked computation graph. -/
noncomputable def dagMaxRank (G : SharedLatentDAG Node Edge) : ℕ :=
  Finset.univ.sup G.rank

theorem dag_rank_le_maxRank
    (G : SharedLatentDAG Node Edge) (v : Node) :
    G.rank v ≤ dagMaxRank G := by
  exact Finset.le_sup (Finset.mem_univ v)

/-- The rank difference to the graph maximum strictly decreases along every
forward edge. -/
theorem dag_reverseMeasure_target_lt_source
    (G : SharedLatentDAG Node Edge) (edge : Edge) :
    dagMaxRank G - G.rank (G.target edge) <
      dagMaxRank G - G.rank (G.source edge) := by
  have hforward := G.forward edge
  have htarget := dag_rank_le_maxRank G (G.target edge)
  omega

variable [DecidableEq Node]

/-- A reverse-error field has prescribed terminal values and otherwise equals
the sum of all outgoing edge-occurrence contributions. -/
def SatisfiesDAGReverseRecursion
    (G : SharedLatentDAG Node Edge) (terminal : Finset Node)
    (boundary error : Node → ℝ) : Prop :=
  (∀ v ∈ terminal, error v = boundary v) ∧
    (∀ v ∉ terminal, error v = dagFullParentAggregate G error v)

/-- The interior equations without a terminal condition.  This weaker
predicate is useful for stating the boundary counterexample below. -/
def SatisfiesDAGInteriorReverseRecursion
    (G : SharedLatentDAG Node Edge) (terminal : Finset Node)
    (error : Node → ℝ) : Prop :=
  ∀ v ∉ terminal, error v = dagFullParentAggregate G error v

/-- Reverse aggregation on a finite ranked DAG is uniquely determined by its
terminal values.  Parallel edges are kept as separate summands. -/
theorem satisfiesDAGReverseRecursion_unique
    (G : SharedLatentDAG Node Edge) (terminal : Finset Node)
    (boundary error₁ error₂ : Node → ℝ)
    (h₁ : SatisfiesDAGReverseRecursion G terminal boundary error₁)
    (h₂ : SatisfiesDAGReverseRecursion G terminal boundary error₂) :
    error₁ = error₂ := by
  funext v
  have hbyMeasure :
      ∀ measure, ∀ u,
        dagMaxRank G - G.rank u = measure → error₁ u = error₂ u := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure ih =>
        intro u hmeasure
        by_cases hut : u ∈ terminal
        · rw [h₁.1 u hut, h₂.1 u hut]
        · rw [h₁.2 u hut, h₂.2 u hut]
          unfold dagFullParentAggregate dagParentContribution
          apply Finset.sum_congr rfl
          intro edge _hedge
          by_cases hs : G.source edge = u
          · simp only [hs, if_true]
            congr 1
            apply ih (dagMaxRank G - G.rank (G.target edge))
            · rw [← hmeasure]
              simpa [hs] using dag_reverseMeasure_target_lt_source G edge
            · rfl
          · simp [hs]
  exact hbyMeasure (dagMaxRank G - G.rank v) v rfl

/-- At a clamped energy minimum, the precision-weighted prediction errors
satisfy the same full reverse recursion once their clamped values are supplied
as the terminal boundary. -/
theorem equilibriumForce_satisfiesDAGReverseRecursion
    (G : SharedLatentDAG Node Edge)
    (clampState z terminalBoundary : Node → ℝ)
    (hterminal :
      ∀ v ∈ G.clamped, dagResidualForce G z v = terminalBoundary v)
    (heq : dagEquilibrium G clampState z) :
    SatisfiesDAGReverseRecursion
      G G.clamped terminalBoundary (dagResidualForce G z) := by
  constructor
  · exact hterminal
  · intro v hv
    exact sharedDAGEquilibriumError_satisfies_parentAggregationRecursion
      G clampState z v hv heq

/-- Arbitrary-DAG correspondence crown: an equilibrium PC error force and a
reverse-mode error field coincide when they obey the same edge-occurrence
recursion and terminal condition. -/
theorem equilibriumForce_eq_reverseError
    (G : SharedLatentDAG Node Edge)
    (clampState z terminalBoundary reverseError : Node → ℝ)
    (hterminal :
      ∀ v ∈ G.clamped, dagResidualForce G z v = terminalBoundary v)
    (heq : dagEquilibrium G clampState z)
    (hreverse :
      SatisfiesDAGReverseRecursion
        G G.clamped terminalBoundary reverseError) :
    dagResidualForce G z = reverseError := by
  exact satisfiesDAGReverseRecursion_unique
    G G.clamped terminalBoundary _ _
    (equilibriumForce_satisfiesDAGReverseRecursion
      G clampState z terminalBoundary hterminal heq)
    hreverse

end ReverseRecursion

/-! ## Executable boundary fixtures -/

/-- The output node of the two-node reference graph is terminal. -/
noncomputable def twoNodeReverseTerminal : Finset (Fin 2) := {1}

/-- With unit gain, both nodes carry the same reverse error. -/
noncomputable def twoNodeReverseError (terminalError : ℝ) : Fin 2 → ℝ :=
  fun _node => terminalError

theorem twoNodeReverseError_satisfies (terminalError : ℝ) :
    SatisfiesDAGReverseRecursion
      dagTwoNodeGraph twoNodeReverseTerminal
      (fun _node => terminalError) (twoNodeReverseError terminalError) := by
  constructor
  · intro _v _hv
    rfl
  · intro v hv
    fin_cases v
    · norm_num [twoNodeReverseError, twoNodeReverseTerminal,
        dagFullParentAggregate, dagParentContribution, dagTwoNodeGraph]
    · simp [twoNodeReverseTerminal] at hv

theorem twoNodeReverseError_is_unique (terminalError : ℝ)
    (error : Fin 2 → ℝ)
    (herror :
      SatisfiesDAGReverseRecursion
        dagTwoNodeGraph twoNodeReverseTerminal
        (fun _node => terminalError) error) :
    error = twoNodeReverseError terminalError := by
  exact satisfiesDAGReverseRecursion_unique
    dagTwoNodeGraph twoNodeReverseTerminal (fun _node => terminalError)
    error (twoNodeReverseError terminalError) herror
    (twoNodeReverseError_satisfies terminalError)

/-- Interior reverse equations alone are not unique: without the terminal
error identity, two distinct fields solve the same interior equation. -/
theorem terminalBoundary_is_necessary :
    SatisfiesDAGInteriorReverseRecursion
        dagTwoNodeGraph twoNodeReverseTerminal (twoNodeReverseError 1) ∧
      SatisfiesDAGInteriorReverseRecursion
        dagTwoNodeGraph twoNodeReverseTerminal (twoNodeReverseError 2) ∧
      twoNodeReverseError 1 ≠ twoNodeReverseError 2 := by
  constructor
  · exact (twoNodeReverseError_satisfies 1).2
  constructor
  · exact (twoNodeReverseError_satisfies 2).2
  · intro h
    have hterminal := congrFun h (1 : Fin 2)
    norm_num [twoNodeReverseError] at hterminal

#print axioms dag_reverseMeasure_target_lt_source
#print axioms satisfiesDAGReverseRecursion_unique
#print axioms equilibriumForce_satisfiesDAGReverseRecursion
#print axioms equilibriumForce_eq_reverseError
#print axioms twoNodeReverseError_is_unique
#print axioms terminalBoundary_is_necessary

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
