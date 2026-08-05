import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.DAGScheduleExactness
import Mathlib.Tactic

/-!
# Constructive levelization of finite computation DAGs

A scheduled reverse-differentiation pass is simplest when every edge advances
exactly one rank.  A long edge can be replaced by one transformed segment
followed by identity segments.  This file constructs that subdivision for
every finite ranked `SharedLatentDAG`.

Intermediate nodes and segments are dependent types indexed by the original
edge, so parallel edges remain distinct.  The construction proves:

* every original edge has a positive rank gap;
* the first and last subdivided segments have the original endpoints;
* consecutive segments are incident;
* every subdivided edge advances exactly one rank;
* the product of segment gains equals the original gain;
* original ranks and clamps are preserved; and
* the exact added-node and segment counts are sums of rank gaps.

Only the first segment carries the original gain.  A long-edge fixture shows
that copying the gain to every identity segment changes the represented map.
The result is a structural and path-semantic levelization theorem; it does not
claim equality of finite inference trajectories after inserting extra latent
states.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

open scoped BigOperators

noncomputable section

variable {Node Edge : Type*} [Fintype Node] [Fintype Edge]

/-! ## Rank gaps and dependent subdivision types -/

/-- Number of unit-rank segments replacing an original edge. -/
def edgeRankGap (G : SharedLatentDAG Node Edge) (edge : Edge) : ℕ :=
  G.rank (G.target edge) - G.rank (G.source edge)

theorem edgeRankGap_pos
    (G : SharedLatentDAG Node Edge) (edge : Edge) :
    0 < edgeRankGap G edge := by
  have forward := G.forward edge
  unfold edgeRankGap
  omega

theorem sourceRank_add_edgeRankGap
    (G : SharedLatentDAG Node Edge) (edge : Edge) :
    G.rank (G.source edge) + edgeRankGap G edge =
      G.rank (G.target edge) := by
  have forward := G.forward edge
  unfold edgeRankGap
  omega

/-- Original nodes plus one private intermediate node for each internal rank
of every original edge. -/
abbrev LevelizedNode (G : SharedLatentDAG Node Edge) :=
  Node ⊕ (Σ edge : Edge, Fin (edgeRankGap G edge - 1))

/-- One segment for each unit of every original edge's rank gap. -/
abbrev LevelizedEdge (G : SharedLatentDAG Node Edge) :=
  Σ edge : Edge, Fin (edgeRankGap G edge)

/-- Source of a subdivided edge segment. -/
def levelizedSource
    (G : SharedLatentDAG Node Edge) :
    LevelizedEdge G → LevelizedNode G
  | ⟨edge, segment⟩ =>
      if zero : segment.val = 0 then
        Sum.inl (G.source edge)
      else
        Sum.inr ⟨edge, ⟨segment.val - 1, by
          have bound := segment.isLt
          omega⟩⟩

/-- Target of a subdivided edge segment. -/
def levelizedTarget
    (G : SharedLatentDAG Node Edge) :
    LevelizedEdge G → LevelizedNode G
  | ⟨edge, segment⟩ =>
      if last : segment.val + 1 = edgeRankGap G edge then
        Sum.inl (G.target edge)
      else
        Sum.inr ⟨edge, ⟨segment.val, by
          have bound := segment.isLt
          omega⟩⟩

/-- Original nodes keep their rank.  The `k`th intermediate node on an edge
has rank `sourceRank + k + 1`. -/
def levelizedRank
    (G : SharedLatentDAG Node Edge) : LevelizedNode G → ℕ
  | Sum.inl node => G.rank node
  | Sum.inr ⟨edge, intermediate⟩ =>
      G.rank (G.source edge) + intermediate.val + 1

/-- The first segment of an original edge. -/
def firstLevelizedEdge
    (G : SharedLatentDAG Node Edge) (edge : Edge) :
    LevelizedEdge G :=
  ⟨edge, ⟨0, edgeRankGap_pos G edge⟩⟩

/-- The last segment of an original edge. -/
def lastLevelizedEdge
    (G : SharedLatentDAG Node Edge) (edge : Edge) :
    LevelizedEdge G :=
  ⟨edge, ⟨edgeRankGap G edge - 1, by
    have positive := edgeRankGap_pos G edge
    omega⟩⟩

theorem firstLevelizedEdge_source
    (G : SharedLatentDAG Node Edge) (edge : Edge) :
    levelizedSource G (firstLevelizedEdge G edge) =
      Sum.inl (G.source edge) := by
  simp [levelizedSource, firstLevelizedEdge]

theorem lastLevelizedEdge_target
    (G : SharedLatentDAG Node Edge) (edge : Edge) :
    levelizedTarget G (lastLevelizedEdge G edge) =
      Sum.inl (G.target edge) := by
  have positive := edgeRankGap_pos G edge
  have last :
      edgeRankGap G edge - 1 + 1 = edgeRankGap G edge := by
    omega
  simp [levelizedTarget, lastLevelizedEdge, last]

/-- Adjacent segments of one subdivided edge share their intermediate node. -/
theorem levelizedEdge_consecutive
    (G : SharedLatentDAG Node Edge) (edge : Edge)
    (segment : ℕ)
    (hasNext : segment + 1 < edgeRankGap G edge) :
    levelizedTarget G ⟨edge, ⟨segment, by omega⟩⟩ =
      levelizedSource G ⟨edge, ⟨segment + 1, hasNext⟩⟩ := by
  have notLast : ¬ segment + 1 = edgeRankGap G edge := by omega
  simp [levelizedTarget, levelizedSource, notLast]

/-! ## Unit-rank and gain semantics -/

theorem levelizedRank_target_eq_source_add_one
    (G : SharedLatentDAG Node Edge) (edge : LevelizedEdge G) :
    levelizedRank G (levelizedTarget G edge) =
      levelizedRank G (levelizedSource G edge) + 1 := by
  rcases edge with ⟨original, segment⟩
  by_cases zero : segment.val = 0
  · by_cases last : segment.val + 1 = edgeRankGap G original
    · have last' : 1 = edgeRankGap G original := by omega
      simp [
        levelizedTarget, levelizedSource, levelizedRank,
        zero, last'
      ]
      have gapEquation := sourceRank_add_edgeRankGap G original
      omega
    · have last' : ¬ 1 = edgeRankGap G original := by omega
      simp [
        levelizedTarget, levelizedSource, levelizedRank,
        zero, last'
      ]
  · by_cases last : segment.val + 1 = edgeRankGap G original
    · simp [
        levelizedTarget, levelizedSource, levelizedRank,
        zero, last
      ]
      have gapEquation := sourceRank_add_edgeRankGap G original
      omega
    · simp [
        levelizedTarget, levelizedSource, levelizedRank,
        zero, last
      ]
      omega

/-- Only the first segment performs the original linear transform; subsequent
segments are identities. -/
def levelizedGain
    (G : SharedLatentDAG Node Edge) : LevelizedEdge G → ℝ
  | ⟨edge, segment⟩ =>
      if segment.val = 0 then G.gain edge else 1

theorem firstLevelizedEdge_gain
    (G : SharedLatentDAG Node Edge) (edge : Edge) :
    levelizedGain G (firstLevelizedEdge G edge) = G.gain edge := by
  simp [levelizedGain, firstLevelizedEdge]

theorem levelizedGain_eq_one_of_ne_zero
    (G : SharedLatentDAG Node Edge) (edge : Edge)
    (segment : Fin (edgeRankGap G edge))
    (nonzero : segment.val ≠ 0) :
    levelizedGain G ⟨edge, segment⟩ = 1 := by
  simp [levelizedGain, nonzero]

/-- Composition along all subdivided segments recovers the original scalar
edge transform. -/
theorem prod_levelizedGain_eq_original
    (G : SharedLatentDAG Node Edge) (edge : Edge) :
    (∏ segment : Fin (edgeRankGap G edge),
      levelizedGain G ⟨edge, segment⟩) =
        G.gain edge := by
  classical
  let zeroSegment : Fin (edgeRankGap G edge) :=
    ⟨0, edgeRankGap_pos G edge⟩
  rw [
    Finset.prod_eq_single_of_mem
      zeroSegment (Finset.mem_univ zeroSegment)
  ]
  · simp [levelizedGain, zeroSegment]
  · intro segment _member different
    have nonzero : segment.val ≠ 0 := by
      intro valueZero
      apply different
      apply Fin.ext
      simp [zeroSegment, valueZero]
    simp [levelizedGain, nonzero]

/-! ## The levelized graph -/

def levelizedPrecision
    (G : SharedLatentDAG Node Edge) : LevelizedNode G → ℝ
  | Sum.inl node => G.precision node
  | Sum.inr _intermediate => 1

def levelizedOffset
    (G : SharedLatentDAG Node Edge) : LevelizedNode G → ℝ
  | Sum.inl node => G.offset node
  | Sum.inr _intermediate => 0

/-- Constructive unit-levelization of a finite ranked DAG. -/
def levelize
    [DecidableEq Node] [DecidableEq Edge]
    (G : SharedLatentDAG Node Edge) :
    SharedLatentDAG (LevelizedNode G) (LevelizedEdge G) where
  source := levelizedSource G
  target := levelizedTarget G
  rank := levelizedRank G
  forward := by
    intro edge
    have step := levelizedRank_target_eq_source_add_one G edge
    omega
  gain := levelizedGain G
  precision := levelizedPrecision G
  precision_pos := by
    intro node
    cases node with
    | inl original =>
        exact G.precision_pos original
    | inr intermediate =>
        norm_num [levelizedPrecision]
  offset := levelizedOffset G
  clamped := G.clamped.image Sum.inl

/-- Every constructed edge advances exactly one rank. -/
theorem levelize_isUnitLevelized
    [DecidableEq Node] [DecidableEq Edge]
    (G : SharedLatentDAG Node Edge) :
    IsUnitLevelized (levelize G) := by
  intro edge
  exact levelizedRank_target_eq_source_add_one G edge

theorem levelize_original_rank
    [DecidableEq Node] [DecidableEq Edge]
    (G : SharedLatentDAG Node Edge) (node : Node) :
    (levelize G).rank (Sum.inl node) = G.rank node :=
  rfl

theorem levelize_original_clamped_iff
    [DecidableEq Node] [DecidableEq Edge]
    (G : SharedLatentDAG Node Edge) (node : Node) :
    Sum.inl node ∈ (levelize G).clamped ↔ node ∈ G.clamped := by
  simp [levelize]

/-- Exact number of subdivided segments. -/
theorem levelizedEdge_card
    (G : SharedLatentDAG Node Edge) :
    Fintype.card (LevelizedEdge G) =
      ∑ edge : Edge, edgeRankGap G edge := by
  simp [LevelizedEdge]

/-- Exact node overhead: every edge contributes `gap - 1` private identity
nodes. -/
theorem levelizedNode_card
    (G : SharedLatentDAG Node Edge) :
    Fintype.card (LevelizedNode G) =
      Fintype.card Node +
        ∑ edge : Edge, (edgeRankGap G edge - 1) := by
  simp [LevelizedNode]

/-- A graph that was already unit-levelized gains no intermediate nodes and
keeps one segment per original edge. -/
theorem levelize_card_eq_of_unitLevelized
    (G : SharedLatentDAG Node Edge)
    (unit : IsUnitLevelized G) :
    Fintype.card (LevelizedNode G) = Fintype.card Node ∧
      Fintype.card (LevelizedEdge G) = Fintype.card Edge := by
  have gapOne : ∀ edge, edgeRankGap G edge = 1 := by
    intro edge
    have forward := G.forward edge
    have rankStep := unit edge
    unfold edgeRankGap
    omega
  constructor
  · rw [levelizedNode_card]
    simp [gapOne]
  · rw [levelizedEdge_card]
    simp [gapOne]

/-! ## Long-edge positive and negative fixtures -/

def longEdgeGraph : SharedLatentDAG (Fin 2) (Fin 1) where
  source _edge := 0
  target _edge := 1
  rank node := if node = 0 then 0 else 3
  forward := by
    intro edge
    fin_cases edge
    norm_num
  gain _edge := 2
  precision _node := 1
  precision_pos _node := by norm_num
  offset _node := 0
  clamped := ∅

theorem longEdgeGraph_gap :
    edgeRankGap longEdgeGraph 0 = 3 := by
  norm_num [edgeRankGap, longEdgeGraph]

theorem longEdgeGraph_levelization_size :
    Fintype.card (LevelizedNode longEdgeGraph) = 4 ∧
      Fintype.card (LevelizedEdge longEdgeGraph) = 3 := by
  constructor
  · rw [levelizedNode_card]
    norm_num [longEdgeGraph_gap]
  · rw [levelizedEdge_card]
    norm_num [longEdgeGraph_gap]

theorem longEdgeGraph_levelization_is_unit :
    IsUnitLevelized (levelize longEdgeGraph) :=
  levelize_isUnitLevelized longEdgeGraph

theorem longEdgeGraph_levelized_gain_recovers :
    (∏ segment : Fin (edgeRankGap longEdgeGraph 0),
      levelizedGain longEdgeGraph ⟨0, segment⟩) = 2 := by
  rw [prod_levelizedGain_eq_original]
  rfl

/-- Incorrectly repeating the original gain on every inserted segment cubes
the gain of this three-segment path instead of preserving it. -/
theorem longEdgeGraph_repeated_gain_is_wrong :
    (∏ _segment : Fin (edgeRankGap longEdgeGraph 0), (2 : ℝ)) = 8 ∧
      (∏ _segment : Fin (edgeRankGap longEdgeGraph 0), (2 : ℝ)) ≠
        longEdgeGraph.gain 0 := by
  rw [longEdgeGraph_gap]
  norm_num [longEdgeGraph]

#print axioms levelizedEdge_consecutive
#print axioms levelizedRank_target_eq_source_add_one
#print axioms prod_levelizedGain_eq_original
#print axioms levelize_isUnitLevelized
#print axioms levelize_original_clamped_iff
#print axioms levelize_card_eq_of_unitLevelized
#print axioms longEdgeGraph_levelization_size
#print axioms longEdgeGraph_repeated_gain_is_wrong

end

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
