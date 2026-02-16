/-
# Classic Bayesian Network Examples

This file provides standard examples to verify the Bayesian network formalization.
We demonstrate the three fundamental structures:

1. **Chain**: A → B → C
2. **Fork**: A ← B → C (common cause)
3. **Collider**: A → C ← B (v-structure)

## References

- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988)
- Koller & Friedman, "Probabilistic Graphical Models" (2009), Chapter 3
-/

import Mettapedia.ProbabilityTheory.BayesianNetworks.DirectedGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparationSoundness

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

open DirectedGraph BayesianNetwork DSeparation

/-! ## Three-Node Networks -/

/-- Three-node vertex type. -/
inductive Three : Type
  | A | B | C
  deriving DecidableEq, Repr

instance : Fintype Three where
  elems := {Three.A, Three.B, Three.C}
  complete := by intro x; cases x <;> simp

/-! ### Chain: A → B → C -/

/-- The chain graph: A → B → C -/
def chainGraph : DirectedGraph Three where
  edges u v := (u = Three.A ∧ v = Three.B) ∨ (u = Three.B ∧ v = Three.C)

/-- Helper: no path from C in chain graph (C is a sink). -/
private theorem chainGraph_no_path_from_C (v : Three) (h : chainGraph.Path Three.C v) :
    v = Three.C := by
  generalize hc : Three.C = c at h
  induction h with
  | refl => rfl
  | step hedge _ ih =>
    simp only [chainGraph] at hedge
    rcases hedge with ⟨hu, _⟩ | ⟨hu, _⟩
    · subst hc; exact absurd hu (by decide)
    · subst hc; exact absurd hu (by decide)

/-- Helper: no path from B to A in chain graph. -/
private theorem chainGraph_no_path_B_to_A (h : chainGraph.Path Three.B Three.A) : False := by
  -- Three.B ≠ Three.A, so refl is impossible; must be step
  cases h with
  | step hedge htail =>
    simp only [chainGraph] at hedge
    rcases hedge with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · -- Edge from A to something, but we start from B
      exact absurd hu (by decide)
    · -- Edge B → C, then path from C to A
      subst hv
      have := chainGraph_no_path_from_C Three.A htail
      exact absurd this (by decide)

/-- The chain graph is acyclic. -/
theorem chainGraph_acyclic : chainGraph.IsAcyclic := by
  intro v ⟨w, hedge, hreach⟩
  simp only [chainGraph] at hedge
  rcases hedge with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · -- Edge A → B, need: no path B → A
    subst hv hw
    exact chainGraph_no_path_B_to_A hreach
  · -- Edge B → C, need: no path C → B
    subst hv hw
    have := chainGraph_no_path_from_C Three.B hreach
    exact absurd this (by decide)

/-- The chain Bayesian network. -/
noncomputable def chainBN : BayesianNetwork Three where
  graph := chainGraph
  acyclic := chainGraph_acyclic
  stateSpace := fun _ => Bool
  measurableSpace := fun _ => ⊤

instance chainBN_stateSpace_standardBorel (v : Three) :
    StandardBorelSpace (chainBN.stateSpace v) := by
  dsimp [chainBN]
  infer_instance

instance chainBN_jointSpace_standardBorel :
    StandardBorelSpace chainBN.JointSpace := by
  dsimp [BayesianNetwork.JointSpace]
  infer_instance

/-! ### Fork: A ← B → C -/

/-- The fork graph: A ← B → C -/
def forkGraph : DirectedGraph Three where
  edges u v := (u = Three.B ∧ v = Three.A) ∨ (u = Three.B ∧ v = Three.C)

/-- Helper: no path from A or C in fork graph (they are sinks). -/
private theorem forkGraph_no_path_from_sink (u v : Three) (hu : u = Three.A ∨ u = Three.C)
    (h : forkGraph.Path u v) : v = u := by
  generalize hs : u = s at h
  induction h with
  | refl => rfl
  | step hedge _ _ =>
    simp only [forkGraph] at hedge
    rcases hedge with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
    · subst hs; rcases hu with rfl | rfl <;> exact absurd hb (by decide)

/-- The fork graph is acyclic. -/
theorem forkGraph_acyclic : forkGraph.IsAcyclic := by
  intro v ⟨w, hedge, hreach⟩
  simp only [forkGraph] at hedge
  rcases hedge with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · -- Edge B → A, need: no path A → B
    subst hv hw
    have := forkGraph_no_path_from_sink Three.A Three.B (Or.inl rfl) hreach
    exact absurd this (by decide)
  · -- Edge B → C, need: no path C → B
    subst hv hw
    have := forkGraph_no_path_from_sink Three.C Three.B (Or.inr rfl) hreach
    exact absurd this (by decide)

/-- The fork Bayesian network. -/
noncomputable def forkBN : BayesianNetwork Three where
  graph := forkGraph
  acyclic := forkGraph_acyclic
  stateSpace := fun _ => Bool
  measurableSpace := fun _ => ⊤

instance forkBN_stateSpace_standardBorel (v : Three) :
    StandardBorelSpace (forkBN.stateSpace v) := by
  dsimp [forkBN]
  infer_instance

instance forkBN_jointSpace_standardBorel :
    StandardBorelSpace forkBN.JointSpace := by
  dsimp [BayesianNetwork.JointSpace]
  infer_instance

/-! ### Collider: A → C ← B -/

/-- The collider graph: A → C ← B -/
def colliderGraph : DirectedGraph Three where
  edges u v := (u = Three.A ∧ v = Three.C) ∨ (u = Three.B ∧ v = Three.C)

/-- Helper: no path from C in collider graph (C is a sink). -/
private theorem colliderGraph_no_path_from_C (v : Three) (h : colliderGraph.Path Three.C v) :
    v = Three.C := by
  generalize hc : Three.C = c at h
  induction h with
  | refl => rfl
  | step hedge _ _ =>
    simp only [colliderGraph] at hedge
    rcases hedge with ⟨hu, _⟩ | ⟨hu, _⟩ <;>
    · subst hc; exact absurd hu (by decide)

/-- The collider graph is acyclic. -/
theorem colliderGraph_acyclic : colliderGraph.IsAcyclic := by
  intro v ⟨w, hedge, hreach⟩
  simp only [colliderGraph] at hedge
  rcases hedge with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · -- Edge A → C, need: no path C → A
    subst hv hw
    have := colliderGraph_no_path_from_C Three.A hreach
    exact absurd this (by decide)
  · -- Edge B → C, need: no path C → B
    subst hv hw
    have := colliderGraph_no_path_from_C Three.B hreach
    exact absurd this (by decide)

/-- The collider Bayesian network. -/
noncomputable def colliderBN : BayesianNetwork Three where
  graph := colliderGraph
  acyclic := colliderGraph_acyclic
  stateSpace := fun _ => Bool
  measurableSpace := fun _ => ⊤

/-! ## Parent Theorems (WIP) -/

/-- In a chain A → B → C, B's parent is A. -/
theorem chain_parents_B : chainBN.parents Three.B = {Three.A} := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents chainBN chainGraph
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h; rcases h with ⟨rfl, _⟩ | ⟨_, h⟩ <;> [rfl; exact absurd h (by decide)]
  · intro rfl; left; exact ⟨rfl, trivial⟩

/-- In a chain A → B → C, C's parent is B. -/
theorem chain_parents_C : chainBN.parents Three.C = {Three.B} := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents chainBN chainGraph
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h; rcases h with ⟨_, h⟩ | ⟨rfl, _⟩ <;> [exact absurd h (by decide); rfl]
  · intro rfl; right; exact ⟨rfl, trivial⟩

/-- In a chain, A has no parents. -/
theorem chain_parents_A : chainBN.parents Three.A = ∅ := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents chainBN chainGraph
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)

/-- In a fork A ← B → C, B has no parents. -/
theorem fork_parents_B : forkBN.parents Three.B = ∅ := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents forkBN forkGraph
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact absurd h (by decide)

/-- In a collider A → C ← B, C has parents {A, B}. -/
theorem collider_parents_C : colliderBN.parents Three.C = {Three.A, Three.B} := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents colliderBN colliderGraph
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · left; rfl
    · right; rfl
  · intro h
    rcases h with rfl | rfl
    · left; exact ⟨rfl, trivial⟩
    · right; exact ⟨rfl, trivial⟩

/-! ## D-Separation Examples (WIP) -/

/-- In a chain A → B → C, A and C are d-separated given {B}.

    The only path A-B-C is blocked because B is a non-collider and B ∈ Z.
-/
theorem chain_dsep_A_C_given_B :
    DSeparated chainGraph {Three.A} {Three.C} {Three.B} := by
  intro x hx y hy hxy hpath
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx hy
  unfold HasActivePath at hpath
  rcases hpath with heq | ⟨hedge, _⟩ | ⟨b, hbx, hby, hxb, hby', hab, hbc, hac, hactive⟩
  · -- Case: A = C (impossible)
    exact Three.noConfusion heq
  · -- Case: Direct edge A ~ C (doesn't exist in chain)
    unfold UndirectedEdge chainGraph at hedge
    rcases hedge with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      first | exact Three.noConfusion h1 | exact Three.noConfusion h2
  · -- Case: Path through intermediate vertex b
    -- The only intermediate vertex connecting A and C is B
    have hbB : b = Three.B := by
      -- hab : UndirectedEdge chainGraph A b
      -- = (chainGraph.edges A b) ∨ (chainGraph.edges b A)
      -- = ((A=A ∧ b=B) ∨ (A=B ∧ b=C)) ∨ ((b=A ∧ A=B) ∨ (b=B ∧ A=C))
      unfold UndirectedEdge chainGraph at hab
      rcases hab with (⟨_, h⟩ | ⟨h, _⟩) | (⟨_, h⟩ | ⟨h, _⟩)
      · exact h  -- b = B
      · exact Three.noConfusion h  -- A = B is false
      · exact Three.noConfusion h  -- A = B is false
      · exact h  -- b = B
    subst hbB
    -- Show the triple ⟨A, B, C⟩ is blocked because B is non-collider and B ∈ Z
    unfold IsActive at hactive
    apply hactive
    unfold IsBlocked
    left
    constructor
    · -- B is a non-collider: ¬(A → B ∧ C → B)
      unfold IsNonCollider IsCollider
      intro ⟨_, hcb⟩
      -- C → B doesn't exist in chainGraph
      simp only [chainGraph] at hcb
      rcases hcb with ⟨h, _⟩ | ⟨h, _⟩ <;> exact Three.noConfusion h
    · -- B ∈ Z = {B}
      simp only [Set.mem_singleton_iff]

private theorem chain_hasActivePath_of_hasActiveTrail_A_C_given_B
    (htrail :
      HasActiveTrail chainGraph ({Three.B} : Set Three) Three.A Three.C) :
    HasActivePath chainGraph ({Three.B} : Set Three) Three.A Three.C := by
  rcases htrail with ⟨p, hpne, hEnds, hAct⟩
  cases hAct with
  | single v =>
      -- Endpoints [v] = (A,C) is impossible.
      exfalso
      simp [PathEndpoints] at hEnds
      have hAC : Three.A = Three.C := hEnds.1.symm.trans hEnds.2
      exact Three.noConfusion hAC
  | two hedge =>
      -- Endpoints [u,v] = (A,C), so edge A~C would be required (false in chain).
      exfalso
      simp [PathEndpoints] at hEnds
      rcases hEnds with ⟨hu, hv⟩
      subst hu
      subst hv
      have hAC : UndirectedEdge chainGraph Three.A Three.C := hedge
      unfold UndirectedEdge chainGraph at hAC
      rcases hAC with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
        first | exact Three.noConfusion h1 | exact Three.noConfusion h2
  | @cons a b c rest hab hbc hac hActive _hTail =>
      -- Use the first active triple. Endpoints force `a = A` and final endpoint `C`.
      have ha : a = Three.A := by
        -- PathEndpoints for length >= 3 stores head as first endpoint.
        cases rest with
        | nil =>
            have hpair : (a, c) = (Three.A, Three.C) := by
              simpa [PathEndpoints] using Option.some.inj hEnds
            exact congrArg Prod.fst hpair
        | cons h t =>
            have hpair : (a, (h :: t).getLast (by simp)) = (Three.A, Three.C) := by
              simpa [PathEndpoints] using Option.some.inj hEnds
            exact congrArg Prod.fst hpair
      subst ha
      have hb : b = Three.B := by
        -- In chain graph, the only undirected neighbor of A is B.
        unfold UndirectedEdge chainGraph at hab
        rcases hab with (⟨_, hb⟩ | ⟨hb, _⟩) | (⟨_, hb⟩ | ⟨hb, _⟩)
        · exact hb
        · exact Three.noConfusion hb
        · exact Three.noConfusion hb
        · exact hb
      subst hb
      have hc : c = Three.C := by
        -- B has undirected neighbors A and C; `c ≠ A` from hac, so c = C.
        have hc_ne_A : c ≠ Three.A := by
          intro h
          exact hac h.symm
        cases c with
        | A => exact (hc_ne_A rfl).elim
        | B =>
            exfalso
            -- B~B impossible in chain graph.
            unfold UndirectedEdge chainGraph at hbc
            rcases hbc with h | h <;> simp at h
        | C => rfl
      subst hc
      -- Build the legacy short active-path witness via the active triple A-B-C.
      right; right
      refine ⟨Three.B, by decide, by decide, ?_, ?_, ?_⟩
      · -- A ~ B
        unfold UndirectedEdge chainGraph
        left; left; exact ⟨rfl, rfl⟩
      · -- B ~ C
        unfold UndirectedEdge chainGraph
        left; right; exact ⟨rfl, rfl⟩
      · refine ⟨?_, ?_, by decide, hActive⟩
        · unfold UndirectedEdge chainGraph
          left; left; exact ⟨rfl, rfl⟩
        · unfold UndirectedEdge chainGraph
          left; right; exact ⟨rfl, rfl⟩

theorem chain_dsepFull_A_C_given_B :
    DSeparatedFull chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) := by
  intro x hx y hy hxy htrail
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx; subst hy
  have hlegacy : ¬ HasActivePath chainGraph ({Three.B} : Set Three) Three.A Three.C :=
    chain_dsep_A_C_given_B Three.A (by simp) Three.C (by simp) (by decide)
  exact hlegacy (chain_hasActivePath_of_hasActiveTrail_A_C_given_B htrail)

theorem chain_separatedInMoral_A_C_given_B :
    SeparatedInMoral chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) := by
  intro x hx y hy hxy hpath
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx
  subst hy
  rcases hpath with ⟨p, hpne, hEnds, hTrail, hAvoid⟩
  cases p with
  | nil =>
      exact (hpne rfl).elim
  | cons a rest =>
      have ha : a = Three.A := by
        cases rest with
        | nil =>
            have hpair : (a, a) = (Three.A, Three.C) := by
              simpa [PathEndpoints] using Option.some.inj hEnds
            exact congrArg Prod.fst hpair
        | cons b rest2 =>
            have hpair : (a, (b :: rest2).getLast (by simp)) = (Three.A, Three.C) := by
              simpa [PathEndpoints] using Option.some.inj hEnds
            exact congrArg Prod.fst hpair
      subst ha
      cases rest with
      | nil =>
          have hpair : (Three.A, Three.A) = (Three.A, Three.C) := by
            simpa [PathEndpoints] using Option.some.inj hEnds
          exact Three.noConfusion (congrArg Prod.snd hpair)
      | cons b rest2 =>
          cases hTrail with
          | cons hAB _ =>
              have hbB : b = Three.B := by
                cases b with
                | A =>
                    exfalso
                    have : False := by
                      simp [UndirectedEdge, moralGraph, moralUndirectedEdge, chainGraph] at hAB
                    exact this
                | B => rfl
                | C =>
                    exfalso
                    have : False := by
                      simp [UndirectedEdge, moralGraph, moralUndirectedEdge, chainGraph] at hAB
                    exact this
              subst hbB
              cases rest2 with
              | nil =>
                  have hpair : (Three.A, Three.B) = (Three.A, Three.C) := by
                    simpa [PathEndpoints] using Option.some.inj hEnds
                  exact Three.noConfusion (congrArg Prod.snd hpair)
              | cons c rest3 =>
                  -- In paths of length >= 3, `PathAvoidsInternals` requires the second node
                  -- to be outside Z; here the second node is B and Z = {B}.
                  have hBnot : Three.B ∉ ({Three.B} : Set Three) := by
                    simpa [PathAvoidsInternals] using (And.left hAvoid)
                  exact hBnot (by simp)

theorem chain_relevantVertices_A_C_B_univ :
    relevantVertices chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) =
      (Set.univ : Set Three) := by
  ext v
  cases v <;> simp [relevantVertices, ancestorClosure, chainGraph]

theorem chain_moralAncestral_eq_moral :
    moralAncestralGraph chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) =
      moralGraph chainGraph := by
  have hrel :
      relevantVertices chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) =
        (Set.univ : Set Three) := chain_relevantVertices_A_C_B_univ
  have hind : inducedSubgraph chainGraph (Set.univ : Set Three) = chainGraph := by
    ext u v
    constructor
    · intro h
      exact h.2.2
    · intro h
      exact ⟨trivial, trivial, h⟩
  simp [moralAncestralGraph, moralGraph, hrel, hind]

theorem chain_separatedInMoralAncestral_A_C_given_B :
    SeparatedInMoralAncestral chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) := by
  intro x hx y hy hxy
  simpa [chain_moralAncestral_eq_moral] using
    (chain_separatedInMoral_A_C_given_B x hx y hy hxy)

theorem chain_separatedInMoralAncestral_iff_separatedInMoral_A_C_given_B :
    SeparatedInMoralAncestral chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) ↔
      SeparatedInMoral chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) := by
  simp [SeparatedInMoralAncestral, SeparatedInMoral, chain_moralAncestral_eq_moral]

theorem chain_dsepFull_iff_separatedInMoral_A_C_given_B :
    DSeparatedFull chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) ↔
      SeparatedInMoral chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) := by
  constructor
  · intro _h
    exact chain_separatedInMoral_A_C_given_B
  · intro _h
    exact chain_dsepFull_A_C_given_B

theorem chain_dsepFull_iff_separatedInMoralAncestral_A_C_given_B :
    DSeparatedFull chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) ↔
      SeparatedInMoralAncestral chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) := by
  constructor
  · intro hFull
    exact chain_separatedInMoralAncestral_A_C_given_B
  · intro hSepAnc
    have hSep :
        SeparatedInMoral chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) :=
      (chain_separatedInMoralAncestral_iff_separatedInMoral_A_C_given_B).1 hSepAnc
    exact (chain_dsepFull_iff_separatedInMoral_A_C_given_B).2 hSep

theorem chain_sep_moral_ancestral_A_C_B :
    SeparatedInMoralAncestral chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) := by
  exact chain_separatedInMoralAncestral_A_C_given_B

theorem chain_dsepFull_iff_sep_moral_ancestral_A_C_B :
    DSeparatedFull chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) ↔
      SeparatedInMoralAncestral chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) := by
  exact chain_dsepFull_iff_separatedInMoralAncestral_A_C_given_B

/-! ## Restricted d-sep ⇒ CondIndep bridge for the chain -/

theorem chain_descendants_C_empty :
    chainBN.descendants Three.C = (∅ : Set Three) := by
  ext u
  constructor
  · intro hu
    unfold BayesianNetwork.descendants DirectedGraph.descendants at hu
    rcases hu with ⟨hreach, hne⟩
    have huC : u = Three.C := chainGraph_no_path_from_C u hreach
    exact (hne huC).elim
  · intro hu
    exact False.elim (Set.notMem_empty _ hu)

theorem chain_graph_descendants_C_empty :
    chainBN.graph.descendants Three.C = (∅ : Set Three) := by
  simpa [BayesianNetwork.descendants] using chain_descendants_C_empty

theorem chain_graph_parents_C :
    chainBN.graph.parents Three.C = ({Three.B} : Set Three) := by
  simpa [BayesianNetwork.parents] using chain_parents_C

theorem chain_nonDescExceptParentsSelf_C :
    chainBN.nonDescendantsExceptParentsAndSelf Three.C = ({Three.A} : Set Three) := by
  ext u
  cases u <;>
    simp [BayesianNetwork.nonDescendantsExceptParentsAndSelf,
      chain_graph_descendants_C_empty, chain_graph_parents_C]

theorem chain_condIndep_CA_given_B_of_localMarkov
    [StandardBorelSpace chainBN.JointSpace]
    (μ : MeasureTheory.Measure chainBN.JointSpace) [MeasureTheory.IsFiniteMeasure μ]
    [HasLocalMarkovProperty chainBN μ] :
    CondIndepVertices chainBN μ ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  have hmarkovC :=
    HasLocalMarkovProperty.markov_condition (bn := chainBN) (μ := μ) Three.C
  simpa [BayesianNetwork.LocalMarkovCondition,
    chain_nonDescExceptParentsSelf_C, chain_graph_parents_C] using hmarkovC

theorem chain_dsep_to_condIndep_CA_given_B
    [StandardBorelSpace chainBN.JointSpace]
    (μ : MeasureTheory.Measure chainBN.JointSpace) [MeasureTheory.IsFiniteMeasure μ]
    [HasLocalMarkovProperty chainBN μ] :
    DSeparatedFull chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) →
      CondIndepVertices chainBN μ ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  intro _hdsep
  exact chain_condIndep_CA_given_B_of_localMarkov (μ := μ)

theorem chain_dsep_to_condIndep_AC_given_B
    [StandardBorelSpace chainBN.JointSpace]
    (μ : MeasureTheory.Measure chainBN.JointSpace) [MeasureTheory.IsFiniteMeasure μ]
    [HasLocalMarkovProperty chainBN μ] :
    DSeparatedFull chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) →
      CondIndepVertices chainBN μ ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) := by
  intro hdsep
  exact condIndepVertices_symm (bn := chainBN) (μ := μ)
    (chain_dsep_to_condIndep_CA_given_B (μ := μ) hdsep)

/-- Restricted full-definition bridge for the chain:
`DSeparatedFull` implies `CondIndepVertices` for `C ⟂ A | B`. -/
theorem chain_dsepFull_to_condIndep_CA_given_B
    [StandardBorelSpace chainBN.JointSpace]
    (μ : MeasureTheory.Measure chainBN.JointSpace) [MeasureTheory.IsFiniteMeasure μ]
    [HasLocalMarkovProperty chainBN μ] :
    Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.DSeparatedFull
      chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) →
      CondIndepVertices chainBN μ ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  intro hdsepFull
  exact chain_dsep_to_condIndep_CA_given_B (μ := μ) hdsepFull

/-! ## Fork D-Separation -/

/-- In a fork A ← B → C, A and C are d-separated given {B}.

    The only path A-B-C is blocked because B is a non-collider and B ∈ Z.
    (Same blocking reason as the chain, but with reversed edge at A.) -/
theorem fork_dsep_A_C_given_B :
    DSeparated forkGraph {Three.A} {Three.C} {Three.B} := by
  intro x hx y hy hxy hpath
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx hy
  unfold HasActivePath at hpath
  rcases hpath with heq | ⟨hedge, _⟩ | ⟨b, hbx, hby, hxb, hby', hab, hbc, hac, hactive⟩
  · -- Case: A = C (impossible)
    exact Three.noConfusion heq
  · -- Case: Direct edge A ~ C (doesn't exist in fork graph)
    unfold UndirectedEdge forkGraph at hedge
    rcases hedge with (⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩) <;>
      exact Three.noConfusion h
  · -- Case: Path through intermediate vertex b
    have hbB : b = Three.B := by
      unfold UndirectedEdge forkGraph at hab
      rcases hab with (⟨h, _⟩ | ⟨h, _⟩) | (⟨hb, _⟩ | ⟨hb, h⟩)
      · exact Three.noConfusion h  -- A = B is false
      · exact Three.noConfusion h  -- A = B is false
      · exact hb                   -- b = B ✓
      · exact Three.noConfusion h  -- A = C is false
    subst hbB
    unfold IsActive at hactive
    apply hactive
    unfold IsBlocked
    left
    constructor
    · -- B is a non-collider: ¬(A → B ∧ C → B)
      -- In forkGraph, edges are B→A and B→C. Neither A→B nor C→B exists.
      unfold IsNonCollider IsCollider
      intro ⟨hab', hcb'⟩
      -- hab' : forkGraph.edges A B, but forkGraph has B→A and B→C only
      simp only [forkGraph] at hab'
      rcases hab' with ⟨h, _⟩ | ⟨h, _⟩ <;> exact Three.noConfusion h
    · -- B ∈ Z = {B}
      simp only [Set.mem_singleton_iff]

private theorem fork_hasActivePath_of_hasActiveTrail_A_C_given_B
    (htrail :
      HasActiveTrail forkGraph ({Three.B} : Set Three) Three.A Three.C) :
    HasActivePath forkGraph ({Three.B} : Set Three) Three.A Three.C := by
  rcases htrail with ⟨p, hpne, hEnds, hAct⟩
  cases hAct with
  | single v =>
      exfalso
      simp [PathEndpoints] at hEnds
      have hAC : Three.A = Three.C := hEnds.1.symm.trans hEnds.2
      exact Three.noConfusion hAC
  | two hedge =>
      exfalso
      simp [PathEndpoints] at hEnds
      rcases hEnds with ⟨hu, hv⟩
      subst hu; subst hv
      have hAC : UndirectedEdge forkGraph Three.A Three.C := hedge
      unfold UndirectedEdge forkGraph at hAC
      rcases hAC with (⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩) <;>
        exact Three.noConfusion h
  | @cons a b c rest hab hbc hac hActive _hTail =>
      have ha : a = Three.A := by
        cases rest with
        | nil =>
            have hpair : (a, c) = (Three.A, Three.C) := by
              simpa [PathEndpoints] using Option.some.inj hEnds
            exact congrArg Prod.fst hpair
        | cons h t =>
            have hpair : (a, (h :: t).getLast (by simp)) = (Three.A, Three.C) := by
              simpa [PathEndpoints] using Option.some.inj hEnds
            exact congrArg Prod.fst hpair
      subst ha
      have hb : b = Three.B := by
        unfold UndirectedEdge forkGraph at hab
        rcases hab with (⟨h, _⟩ | ⟨h, _⟩) | (⟨hb, _⟩ | ⟨hb, h⟩)
        · exact Three.noConfusion h  -- A = B is false
        · exact Three.noConfusion h  -- A = B is false
        · exact hb                   -- b = B ✓
        · exact Three.noConfusion h  -- A = C is false
      subst hb
      have hc : c = Three.C := by
        have hc_ne_A : c ≠ Three.A := by
          intro h; exact hac h.symm
        cases c with
        | A => exact (hc_ne_A rfl).elim
        | B =>
            exfalso
            unfold UndirectedEdge forkGraph at hbc
            rcases hbc with (⟨_, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩)
            · exact Three.noConfusion h  -- B = A is false
            · exact Three.noConfusion h  -- B = C is false
            · exact Three.noConfusion h  -- B = A is false
            · exact Three.noConfusion h  -- B = C is false
        | C => rfl
      subst hc
      right; right
      refine ⟨Three.B, by decide, by decide, ?_, ?_, ?_⟩
      · -- A ~ B (undirected: forkGraph has B→A)
        unfold UndirectedEdge forkGraph
        right; left; exact ⟨rfl, rfl⟩
      · -- B ~ C (undirected: forkGraph has B→C)
        unfold UndirectedEdge forkGraph
        left; right; exact ⟨rfl, rfl⟩
      · refine ⟨?_, ?_, by decide, hActive⟩
        · unfold UndirectedEdge forkGraph
          right; left; exact ⟨rfl, rfl⟩
        · unfold UndirectedEdge forkGraph
          left; right; exact ⟨rfl, rfl⟩

/-- Full trail-based d-separation for the fork. -/
theorem fork_dsepFull_A_C_given_B :
    DSeparatedFull forkGraph ({Three.A} : Set Three) ({Three.C} : Set Three)
      ({Three.B} : Set Three) := by
  intro x hx y hy hxy htrail
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx; subst hy
  have hlegacy : ¬ HasActivePath forkGraph ({Three.B} : Set Three) Three.A Three.C :=
    fork_dsep_A_C_given_B Three.A (by simp) Three.C (by simp) (by decide)
  exact hlegacy (fork_hasActivePath_of_hasActiveTrail_A_C_given_B htrail)

/-! ## Fork graph-structural helpers + CondIndep bridge -/

/-- In forkBN, C has parents {B}. -/
theorem fork_parents_C : forkBN.parents Three.C = ({Three.B} : Set Three) := by
  ext u
  unfold BayesianNetwork.parents DirectedGraph.parents forkBN forkGraph
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h; rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rfl
    · rfl
  · intro h; subst h; right; exact ⟨rfl, trivial⟩

/-- In forkBN, C has no descendants (it's a sink). -/
theorem fork_descendants_C_empty :
    forkBN.descendants Three.C = (∅ : Set Three) := by
  ext u
  constructor
  · intro hu
    unfold BayesianNetwork.descendants DirectedGraph.descendants at hu
    rcases hu with ⟨hreach, hne⟩
    have huC : u = Three.C :=
      forkGraph_no_path_from_sink Three.C u (Or.inr rfl) hreach
    exact (hne huC).elim
  · intro hu; exact False.elim (Set.notMem_empty _ hu)

theorem fork_graph_descendants_C_empty :
    forkBN.graph.descendants Three.C = (∅ : Set Three) := by
  simpa [BayesianNetwork.descendants] using fork_descendants_C_empty

theorem fork_graph_parents_C :
    forkBN.graph.parents Three.C = ({Three.B} : Set Three) := by
  simpa [BayesianNetwork.parents] using fork_parents_C

theorem fork_nonDescExceptParentsSelf_C :
    forkBN.nonDescendantsExceptParentsAndSelf Three.C = ({Three.A} : Set Three) := by
  ext u
  cases u <;>
    simp [BayesianNetwork.nonDescendantsExceptParentsAndSelf,
      fork_graph_descendants_C_empty, fork_graph_parents_C]

/-- Local Markov condition at C in forkBN gives C ⊥ {A} | {B}. -/
theorem fork_condIndep_CA_given_B_of_localMarkov
    [StandardBorelSpace forkBN.JointSpace]
    (μ : MeasureTheory.Measure forkBN.JointSpace) [MeasureTheory.IsFiniteMeasure μ]
    [HasLocalMarkovProperty forkBN μ] :
    CondIndepVertices forkBN μ ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  have hmarkovC :=
    HasLocalMarkovProperty.markov_condition (bn := forkBN) (μ := μ) Three.C
  simpa [BayesianNetwork.LocalMarkovCondition,
    fork_nonDescExceptParentsSelf_C, fork_graph_parents_C] using hmarkovC

/-- DSeparatedFull + local Markov ⇒ CondIndepVertices for fork. -/
theorem fork_dsep_to_condIndep_CA_given_B
    [StandardBorelSpace forkBN.JointSpace]
    (μ : MeasureTheory.Measure forkBN.JointSpace) [MeasureTheory.IsFiniteMeasure μ]
    [HasLocalMarkovProperty forkBN μ] :
    DSeparatedFull forkGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) →
      CondIndepVertices forkBN μ ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  intro _hdsep
  exact fork_condIndep_CA_given_B_of_localMarkov (μ := μ)

/-- Full d-sep bridge for fork. -/
theorem fork_dsepFull_to_condIndep_CA_given_B
    [StandardBorelSpace forkBN.JointSpace]
    (μ : MeasureTheory.Measure forkBN.JointSpace) [MeasureTheory.IsFiniteMeasure μ]
    [HasLocalMarkovProperty forkBN μ] :
    Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.DSeparatedFull
      forkGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) →
      CondIndepVertices forkBN μ ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  intro hdsepFull
  exact fork_dsep_to_condIndep_CA_given_B (μ := μ) hdsepFull

/-! ## Collider D-Separation -/

/-- In a collider A → C ← B, A and B are d-separated given ∅.

    The only path A-C-B is blocked because C is a collider and Z = ∅.
    Colliders are blocked unless they or their descendants are observed.
-/
theorem collider_dsep_A_B_given_empty :
    DSeparated colliderGraph {Three.A} {Three.B} ∅ := by
  intro x hx y hy hxy hpath
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx hy
  unfold HasActivePath at hpath
  rcases hpath with heq | ⟨hedge, _⟩ | ⟨c, hcx, hcy, hxc, hcy', hac, hcb, hab, hactive⟩
  · -- Case: A = B (impossible)
    exact Three.noConfusion heq
  · -- Case: Direct edge A ~ B (doesn't exist in collider graph)
    -- colliderGraph edges are A → C and B → C only
    unfold UndirectedEdge colliderGraph at hedge
    rcases hedge with (⟨_, h⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨_, h⟩)
    · exact Three.noConfusion h  -- C = B is false
    · exact Three.noConfusion h  -- B = A is false
    · exact Three.noConfusion h  -- B = A is false
    · exact Three.noConfusion h  -- C = A is false
  · -- Case: Path through intermediate vertex c
    -- The only intermediate vertex connecting A and B is C
    have hcC : c = Three.C := by
      -- hac : UndirectedEdge colliderGraph A c
      -- = ((A=A ∧ c=C) ∨ (A=B ∧ c=C)) ∨ ((c=A ∧ A=C) ∨ (c=B ∧ A=C))
      unfold UndirectedEdge colliderGraph at hac
      rcases hac with (⟨_, h⟩ | ⟨h, _⟩) | (⟨_, h⟩ | ⟨_, h⟩)
      · exact h  -- c = C
      · exact Three.noConfusion h  -- A = B is false
      · exact Three.noConfusion h  -- A = C is false
      · exact Three.noConfusion h  -- A = C is false
    subst hcC
    -- Show the triple ⟨A, C, B⟩ is blocked because C is a collider and Z = ∅
    unfold IsActive at hactive
    apply hactive
    unfold IsBlocked
    right
    constructor
    · -- C is a collider: A → C ∧ B → C
      unfold IsCollider colliderGraph
      constructor
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
    constructor
    · -- C ∉ Z = ∅
      simp only [Set.notMem_empty, not_false_eq_true]
    · -- No descendant of C is in Z = ∅ (vacuously true since ∅ is empty)
      intro d _ hd
      exact Set.notMem_empty d hd

/-! ## Alarm Network (WIP) -/

/-- Five-node type for the Alarm network. -/
inductive Five : Type
  | Burglary | Earthquake | Alarm | JohnCalls | MaryCalls
  deriving DecidableEq, Repr

instance : Fintype Five where
  elems := {Five.Burglary, Five.Earthquake, Five.Alarm, Five.JohnCalls, Five.MaryCalls}
  complete := by intro x; cases x <;> simp

/-- The Alarm network graph. -/
def alarmGraph : DirectedGraph Five where
  edges u v :=
    (u = Five.Burglary ∧ v = Five.Alarm) ∨
    (u = Five.Earthquake ∧ v = Five.Alarm) ∨
    (u = Five.Alarm ∧ v = Five.JohnCalls) ∨
    (u = Five.Alarm ∧ v = Five.MaryCalls)

/-- Helper: no path from JohnCalls or MaryCalls (they are sinks). -/
private theorem alarmGraph_no_path_from_sink (u v : Five)
    (hu : u = Five.JohnCalls ∨ u = Five.MaryCalls)
    (h : alarmGraph.Path u v) : v = u := by
  generalize hs : u = s at h
  induction h with
  | refl => rfl
  | step hedge _ _ =>
    simp only [alarmGraph] at hedge
    rcases hedge with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩ <;>
    · subst hs; rcases hu with rfl | rfl <;> exact Five.noConfusion hb

/-- Helper: no path from Alarm to Burglary or Earthquake. -/
private theorem alarmGraph_no_path_from_Alarm (v : Five)
    (hv : v = Five.Burglary ∨ v = Five.Earthquake)
    (h : alarmGraph.Path Five.Alarm v) : False := by
  cases h with
  | refl =>
    -- If refl, then v = Five.Alarm, but hv says v = Burglary or Earthquake
    -- These are impossible equalities (Alarm ≠ Burglary, Alarm ≠ Earthquake)
    rcases hv with h | h <;> exact Five.noConfusion h
  | step hedge htail =>
    simp only [alarmGraph] at hedge
    rcases hedge with ⟨habs, _⟩ | ⟨habs, _⟩ | ⟨_, hv'⟩ | ⟨_, hv'⟩
    · exact Five.noConfusion habs
    · exact Five.noConfusion habs
    · -- Alarm → JohnCalls, then path from JohnCalls
      subst hv'
      have := alarmGraph_no_path_from_sink Five.JohnCalls v (Or.inl rfl) htail
      rcases hv with rfl | rfl <;> exact Five.noConfusion this
    · -- Alarm → MaryCalls, then path from MaryCalls
      subst hv'
      have := alarmGraph_no_path_from_sink Five.MaryCalls v (Or.inr rfl) htail
      rcases hv with rfl | rfl <;> exact Five.noConfusion this

/-- The alarm graph is acyclic. -/
theorem alarmGraph_acyclic : alarmGraph.IsAcyclic := by
  intro v ⟨w, hedge, hreach⟩
  simp only [alarmGraph] at hedge
  rcases hedge with ⟨hv, hw⟩ | ⟨hv, hw⟩ | ⟨hv, hw⟩ | ⟨hv, hw⟩
  · -- Edge Burglary → Alarm, need: no path Alarm → Burglary
    subst hv hw
    exact alarmGraph_no_path_from_Alarm Five.Burglary (Or.inl rfl) hreach
  · -- Edge Earthquake → Alarm, need: no path Alarm → Earthquake
    subst hv hw
    exact alarmGraph_no_path_from_Alarm Five.Earthquake (Or.inr rfl) hreach
  · -- Edge Alarm → JohnCalls, need: no path JohnCalls → Alarm
    subst hv hw
    have := alarmGraph_no_path_from_sink Five.JohnCalls Five.Alarm (Or.inl rfl) hreach
    exact Five.noConfusion this
  · -- Edge Alarm → MaryCalls, need: no path MaryCalls → Alarm
    subst hv hw
    have := alarmGraph_no_path_from_sink Five.MaryCalls Five.Alarm (Or.inr rfl) hreach
    exact Five.noConfusion this

/-- The Alarm Bayesian network. -/
noncomputable def alarmBN : BayesianNetwork Five where
  graph := alarmGraph
  acyclic := alarmGraph_acyclic
  stateSpace := fun _ => Bool
  measurableSpace := fun _ => ⊤

/-! ## Summary

This file demonstrates the fundamental BN structures - ALL PROOFS COMPLETE (0 sorries).

**Three-node networks** (all acyclicity proven ✓):
- **Chain**: A → B → C
- **Fork**: A ← B → C (common cause)
- **Collider**: A → C ← B (v-structure)

**Five-node Alarm network** (acyclicity proven ✓):
- Burglary → Alarm ← Earthquake
- Alarm → JohnCalls, Alarm → MaryCalls

**Parent set theorems** (all proven ✓):
- `chain_parents_A`, `chain_parents_B`, `chain_parents_C`
- `fork_parents_B`
- `collider_parents_C`

**D-separation examples** (all proven ✓):
- `chain_dsep_A_C_given_B` - Path A-B-C blocked when B observed (non-collider in Z)
- `collider_dsep_A_B_given_empty` - Path A-C-B blocked when C not observed (collider not in Z)
-/

end Mettapedia.ProbabilityTheory.BayesianNetworks.Examples
