import Mettapedia.GSLT.Causality.DoCalculus.BowArc
import Mettapedia.GSLT.Causality.DoCalculus.DoRules

/-!
# Numeric controls for the three do-calculus rules

Each rule has one graph on which the queried conditional masses agree, and one
graph on which an active trail remains and the masses disagree.

The agreeing cases of rules 2 and 3 are the proved sufficient conditions:
every parent of `Z` already lies in the conditioned set, and `Z` has no child
outside `X ∪ Z`. The disagreeing case of rule 2 is the bow, model 2, where
`P(Y = true | X = true)` is `1` and `P(Y = true | do(X = true))` is `1/2`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open DSeparation
open PMF
open scoped BigOperators ENNReal

/-- Three vertices: treatment `x`, outcome `y`, covariate `z`. -/
inductive Node
  | x
  | y
  | z
  deriving DecidableEq

instance : Fintype Node where
  elems := {Node.x, Node.y, Node.z}
  complete := by intro v; cases v <;> simp

/-- Read a configuration off three bits, in order `x`, `y`, `z`. -/
def nodeOf (bx byy bz : Bool) : Node → Bool
  | .x => bx
  | .y => byy
  | .z => bz

lemma prod_node (g : Node → ℝ≥0∞) : ∏ v, g v = g .x * (g .y * g .z) := by
  have huniv : (Finset.univ : Finset Node) = insert .x (insert .y {.z}) := by
    ext v
    cases v <;> simp
  rw [huniv, Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]

lemma sum_node (g : (Node → Bool) → ℝ≥0∞) :
    ∑ f, g f = ∑ bx, ∑ byy, ∑ bz, g (nodeOf bx byy bz) := by
  let e : (Node → Bool) ≃ Bool × Bool × Bool :=
    { toFun := fun f => (f .x, f .y, f .z)
      invFun := fun p => nodeOf p.1 p.2.1 p.2.2
      left_inv := by
        intro f
        ext v
        cases v <;> rfl
      right_inv := by
        rintro ⟨bx, byy, bz⟩
        rfl }
  rw [← Equiv.sum_comp e.symm g]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bx _ => ?_
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun byy _ => ?_
  refine Finset.sum_congr rfl fun bz _ => ?_
  rfl

/-- Mass of the configurations accepted by `keep`, under a truncated weight. -/
noncomputable def nodeMass
    (graph : DirectedGraph Node) (hAcyclic : graph.IsAcyclic) [DecidableRel graph.edges]
    (cpt : (network (β := Bool) graph hAcyclic).DiscreteCPT)
    (assignment : Node → Option Bool) (keep : (Node → Bool) → Bool) : ℝ≥0∞ :=
  ∑ f, if keep f = true then truncatedWeight graph hAcyclic cpt assignment f else 0

lemma half_ne_zero : (2 : ℝ≥0∞)⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top

lemma half_ne_top : (2 : ℝ≥0∞)⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.2 two_ne_zero

lemma div_half : (2 : ℝ≥0∞)⁻¹ / (2 : ℝ≥0∞)⁻¹ = 1 :=
  ENNReal.div_self half_ne_zero half_ne_top

lemma div_by_one (a : ℝ≥0∞) : a / 1 = a := by
  rw [ENNReal.div_eq_inv_mul, inv_one, one_mul]

lemma two_quarters :
    (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
  rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

lemma four_quarters :
    (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ +
      ((2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) = 1 := by
  rw [two_quarters, ENNReal.inv_two_add_inv_two]

/-! ## An active trail cannot end at an isolated vertex -/

lemma trail_avoids_isolated
    {G : DirectedGraph Node} {isolated : Node} {cond : Set Node} {p : List Node}
    (hiso : ∀ {u v : Node}, UndirectedEdge G u v → u ≠ isolated ∧ v ≠ isolated)
    (hact : ActiveTrail G cond p) :
    ∀ s e, PathEndpoints p = some (s, e) → s ≠ e → e ≠ isolated :=
  ActiveTrail.rec
    (motive := fun p _ => ∀ s e, PathEndpoints p = some (s, e) → s ≠ e → e ≠ isolated)
    (fun vtx s e hpe hne => by
      simp only [PathEndpoints] at hpe
      injection hpe with hpair
      have hs : s = vtx := ((Prod.ext_iff.mp hpair).1).symm
      have he : e = vtx := ((Prod.ext_iff.mp hpair).2).symm
      exact absurd (hs.trans he.symm) hne)
    (fun {u vNode} hedge s e hpe _ => by
      simp only [PathEndpoints, List.getLast_singleton] at hpe
      injection hpe with hpair
      have hev : e = vNode := ((Prod.ext_iff.mp hpair).2).symm
      exact hev ▸ (hiso hedge).2)
    (fun {a b c : Node} {rest : List Node} hab _ _ _ _ ih s e hpe hne => by
      have hsplit := pathEndpoints_of_cons (V := Node) hpe
      by_cases hbe : b = e
      · exact hbe ▸ (hiso hab).2
      · exact ih b e hsplit.2 hbe)
    hact

lemma separated_from_isolated
    {G : DirectedGraph Node} {isolated : Node} {cond : Set Node}
    (hiso : ∀ {u v : Node}, UndirectedEdge G u v → u ≠ isolated ∧ v ≠ isolated)
    (Y : Set Node) :
    DSeparatedFull G Y ({isolated} : Set Node) cond := by
  intro outcome _ covariate hcovariate hne htrail
  rcases htrail with ⟨p, _, hpe, hact⟩
  have hcov : covariate = isolated := by simpa [Set.mem_singleton_iff] using hcovariate
  exact trail_avoids_isolated hiso hact outcome covariate hpe hne hcov

lemma endpoints_pair (a b : Node) : PathEndpoints [a, b] = some (a, b) := by
  simp [PathEndpoints]

/-! ## Chain `X → Y`, with `Z` isolated -/

/-- `X → Y`, and `Z` has no edge. -/
def chainGraph : DirectedGraph Node where
  edges a b := a = .x ∧ b = .y

instance : DecidableRel chainGraph.edges := fun _ _ => by
  unfold chainGraph
  infer_instance

def chainRank : Node → ℕ
  | .x => 0
  | .z => 0
  | .y => 1

lemma chain_edge_increases {a b : Node} (h : chainGraph.edges a b) :
    chainRank a < chainRank b := by
  cases a <;> cases b <;> simp [chainGraph, chainRank] at h ⊢

lemma chain_reachable_rank {a b : Node} (h : chainGraph.Reachable a b) :
    chainRank a ≤ chainRank b := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih => exact le_trans (Nat.le_of_lt (chain_edge_increases hedge)) ih

lemma chainAcyclic : chainGraph.IsAcyclic := by
  intro v ⟨src, hedge, hreach⟩
  exact lt_irrefl _ <|
    lt_of_lt_of_le (chain_edge_increases hedge) (chain_reachable_rank hreach)

lemma chain_x_parent_y :
    Node.x ∈ (network (β := Bool) chainGraph chainAcyclic).parents Node.y := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, chainGraph]

/-- `X` and `Z` are fair coins, and `Y` copies `X`. -/
noncomputable def chainCPT : (network (β := Bool) chainGraph chainAcyclic).DiscreteCPT where
  cpt := fun v pa =>
    match v with
    | .x => fairBit
    | .y => PMF.pure (pa .x chain_x_parent_y)
    | .z => fairBit

lemma chain_node_x (f : Node → Bool) :
    DiscreteCPT.nodeProb chainCPT f .x = fairBit (f .x) := by
  simp [DiscreteCPT.nodeProb, chainCPT]

lemma chain_node_y (f : Node → Bool) :
    DiscreteCPT.nodeProb chainCPT f .y = PMF.pure (f .x) (f .y) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, chainCPT]

lemma chain_node_z (f : Node → Bool) :
    DiscreteCPT.nodeProb chainCPT f .z = fairBit (f .z) := by
  simp [DiscreteCPT.nodeProb, chainCPT]

/-- Set `X` to `true`. -/
def nodeDoX : Node → Option Bool
  | .x => some true
  | .y => none
  | .z => none

lemma nodeDoX_eq :
    nodeDoX = doFinset ({.x} : Finset Node) (fun _ => true) := by
  funext v
  cases v <;> simp [nodeDoX, doFinset]

/-- Set `X` and `Z` to `true`. -/
def doXZTrue : Node → Option Bool
  | .x => some true
  | .y => none
  | .z => some true

lemma doXZTrue_eq :
    doXZTrue = doFinset ({.x, .z} : Finset Node) (fun _ => true) := by
  funext v
  cases v <;> simp [doXZTrue, doFinset]

lemma chain_doX_weight (f : Node → Bool) :
    truncatedWeight chainGraph chainAcyclic chainCPT nodeDoX f =
      (if f .x = true then 1 else 0) * (PMF.pure (f .x) (f .y) * fairBit (f .z)) := by
  unfold truncatedWeight
  rw [prod_node]
  have hx : truncatedFactor chainGraph chainAcyclic chainCPT nodeDoX f .x =
      if f .x = true then 1 else 0 := by
    simp [truncatedFactor, nodeDoX]
  have hy : truncatedFactor chainGraph chainAcyclic chainCPT nodeDoX f .y =
      PMF.pure (f .x) (f .y) := by
    simp [truncatedFactor, nodeDoX, cptAt_eq_nodeProb, chain_node_y]
  have hz : truncatedFactor chainGraph chainAcyclic chainCPT nodeDoX f .z =
      fairBit (f .z) := by
    simp [truncatedFactor, nodeDoX, cptAt_eq_nodeProb, chain_node_z]
  simp [hx, hy, hz]

lemma chain_doXZ_weight (f : Node → Bool) :
    truncatedWeight chainGraph chainAcyclic chainCPT doXZTrue f =
      (if f .x = true then 1 else 0) *
        (PMF.pure (f .x) (f .y) * if f .z = true then 1 else 0) := by
  unfold truncatedWeight
  rw [prod_node]
  have hx : truncatedFactor chainGraph chainAcyclic chainCPT doXZTrue f .x =
      if f .x = true then 1 else 0 := by
    simp [truncatedFactor, doXZTrue]
  have hy : truncatedFactor chainGraph chainAcyclic chainCPT doXZTrue f .y =
      PMF.pure (f .x) (f .y) := by
    simp [truncatedFactor, doXZTrue, cptAt_eq_nodeProb, chain_node_y]
  have hz : truncatedFactor chainGraph chainAcyclic chainCPT doXZTrue f .z =
      if f .z = true then 1 else 0 := by
    simp [truncatedFactor, doXZTrue]
  simp [hx, hy, hz]

lemma chain_in_xy {u v : Node}
    (h : (deleteIncoming chainGraph ({.x} : Finset Node)).edges u v) :
    u = .x ∧ v = .y := by
  rcases h with ⟨hedge, _⟩
  simpa [chainGraph] using hedge

lemma chain_in_isolates_z {u v : Node} :
    UndirectedEdge (deleteIncoming chainGraph ({.x} : Finset Node)) u v →
      u ≠ .z ∧ v ≠ .z := by
  intro h
  rcases h with hdir | hrev
  · obtain ⟨rfl, rfl⟩ := chain_in_xy hdir
    exact ⟨by decide, by decide⟩
  · obtain ⟨rfl, rfl⟩ := chain_in_xy hrev
    exact ⟨by decide, by decide⟩

lemma chain_rule3_xy {u v : Node}
    (h : (deleteIncoming (deleteIncoming chainGraph ({.x} : Finset Node))
      ({.z} : Finset Node)).edges u v) :
    u = .x ∧ v = .y := by
  rcases h with ⟨hedge, _⟩
  exact chain_in_xy hedge

lemma chain_rule3_isolates_z {u v : Node} :
    UndirectedEdge (deleteIncoming (deleteIncoming chainGraph ({.x} : Finset Node))
      ({.z} : Finset Node)) u v → u ≠ .z ∧ v ≠ .z := by
  intro h
  rcases h with hdir | hrev
  · obtain ⟨rfl, rfl⟩ := chain_rule3_xy hdir
    exact ⟨by decide, by decide⟩
  · obtain ⟨rfl, rfl⟩ := chain_rule3_xy hrev
    exact ⟨by decide, by decide⟩

/-- **Rule 1, positive separation.** `Y` and `Z` are d-separated by `X` once the
arrows into `X` are deleted: the only remaining edge is `X → Y`. -/
theorem chain_rule1_separated :
    DSeparatedFull (deleteIncoming chainGraph ({.x} : Finset Node))
      ({.y} : Set Node) ({.z} : Set Node) ({.x} : Set Node) :=
  separated_from_isolated chain_in_isolates_z _

lemma chain_mass_yz :
    nodeMass chainGraph chainAcyclic chainCPT nodeDoX (fun f => f .y && f .z) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [chain_doX_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]

lemma chain_mass_z :
    nodeMass chainGraph chainAcyclic chainCPT nodeDoX (fun f => f .z) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [chain_doX_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]

lemma chain_mass_y :
    nodeMass chainGraph chainAcyclic chainCPT nodeDoX (fun f => f .y) = 1 := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [chain_doX_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply, ENNReal.inv_two_add_inv_two]

lemma chain_mass_all :
    nodeMass chainGraph chainAcyclic chainCPT nodeDoX (fun _ => true) = 1 := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [chain_doX_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply, ENNReal.inv_two_add_inv_two]

/-- **Rule 1, positive masses.** Under `do(X = true)`, `Y` copies `X`, so
`P(Y = true | Z = true) = P(Y = true) = 1`. -/
theorem chain_rule1_conditional_eq :
    nodeMass chainGraph chainAcyclic chainCPT (doFinset ({.x} : Finset Node) (fun _ => true))
        (fun f => f .y && f .z) /
      nodeMass chainGraph chainAcyclic chainCPT (doFinset ({.x} : Finset Node) (fun _ => true))
        (fun f => f .z) =
    nodeMass chainGraph chainAcyclic chainCPT (doFinset ({.x} : Finset Node) (fun _ => true))
        (fun f => f .y) /
      nodeMass chainGraph chainAcyclic chainCPT (doFinset ({.x} : Finset Node) (fun _ => true))
        (fun _ => true) := by
  rw [← nodeDoX_eq, chain_mass_yz, chain_mass_z, chain_mass_y, chain_mass_all, div_half, div_by_one]

lemma chain_mass_xz_y :
    nodeMass chainGraph chainAcyclic chainCPT doXZTrue (fun f => f .y) = 1 := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [chain_doXZ_weight, nodeOf, sum_bool]
  simp [PMF.pure_apply]

lemma chain_mass_xz_all :
    nodeMass chainGraph chainAcyclic chainCPT doXZTrue (fun _ => true) = 1 := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [chain_doXZ_weight, nodeOf, sum_bool]
  simp [PMF.pure_apply]

/-- **Rule 3, positive separation.** Deleting the arrows into `X` and into `Z`
leaves `Z` isolated. -/
theorem chain_rule3_separated :
    DSeparatedFull
      (deleteIncoming (deleteIncoming chainGraph ({.x} : Finset Node)) ({.z} : Finset Node))
      ({.y} : Set Node) ({.z} : Set Node) ({.x} : Set Node) :=
  separated_from_isolated chain_rule3_isolates_z _

/-- **Rule 3, positive masses, and the no-outside-child hypothesis.**

`Z` has no edge at all, so every edge out of `Z` lands in `X ∪ Z`. Both
`P(Y = true | do(X = true), do(Z = true))` and `P(Y = true | do(X = true))`
equal `1`. -/
theorem chain_rule3_conditional_eq :
    (∀ u ∈ ({.z} : Finset Node), ∀ v, chainGraph.edges u v → v ∈ ({.x} ∪ {.z} : Finset Node)) ∧
      nodeMass chainGraph chainAcyclic chainCPT
          (doFinset ({.x, .z} : Finset Node) (fun _ => true)) (fun f => f .y) /
        nodeMass chainGraph chainAcyclic chainCPT
          (doFinset ({.x, .z} : Finset Node) (fun _ => true)) (fun _ => true) =
      nodeMass chainGraph chainAcyclic chainCPT
          (doFinset ({.x} : Finset Node) (fun _ => true)) (fun f => f .y) /
        nodeMass chainGraph chainAcyclic chainCPT
          (doFinset ({.x} : Finset Node) (fun _ => true)) (fun _ => true) := by
  refine ⟨?_, ?_⟩
  · intro u hu v hedge
    have huZ : u = .z := by simpa using hu
    subst huZ
    simp [chainGraph] at hedge
  · rw [← doXZTrue_eq, ← nodeDoX_eq, chain_mass_xz_y, chain_mass_xz_all,
      chain_mass_y, chain_mass_all, div_by_one]

/-! ## Copy `Z → Y`, with `X` isolated -/

/-- `Z → Y`, and `X` has no edge. -/
def copyGraph : DirectedGraph Node where
  edges a b := a = .z ∧ b = .y

instance : DecidableRel copyGraph.edges := fun _ _ => by
  unfold copyGraph
  infer_instance

def copyRank : Node → ℕ
  | .z => 0
  | .x => 0
  | .y => 1

lemma copy_edge_increases {a b : Node} (h : copyGraph.edges a b) :
    copyRank a < copyRank b := by
  cases a <;> cases b <;> simp [copyGraph, copyRank] at h ⊢

lemma copy_reachable_rank {a b : Node} (h : copyGraph.Reachable a b) :
    copyRank a ≤ copyRank b := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih => exact le_trans (Nat.le_of_lt (copy_edge_increases hedge)) ih

lemma copyAcyclic : copyGraph.IsAcyclic := by
  intro v ⟨src, hedge, hreach⟩
  exact lt_irrefl _ <|
    lt_of_lt_of_le (copy_edge_increases hedge) (copy_reachable_rank hreach)

lemma copy_z_parent_y :
    Node.z ∈ (network (β := Bool) copyGraph copyAcyclic).parents Node.y := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, copyGraph]

/-- `Z` is a fair coin, `Y` copies `Z`, and `X` is an independent fair coin. -/
noncomputable def copyCPT : (network (β := Bool) copyGraph copyAcyclic).DiscreteCPT where
  cpt := fun v pa =>
    match v with
    | .x => fairBit
    | .y => PMF.pure (pa .z copy_z_parent_y)
    | .z => fairBit

lemma copy_node_x (f : Node → Bool) :
    DiscreteCPT.nodeProb copyCPT f .x = fairBit (f .x) := by
  simp [DiscreteCPT.nodeProb, copyCPT]

lemma copy_node_y (f : Node → Bool) :
    DiscreteCPT.nodeProb copyCPT f .y = PMF.pure (f .z) (f .y) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, copyCPT]

lemma copy_node_z (f : Node → Bool) :
    DiscreteCPT.nodeProb copyCPT f .z = fairBit (f .z) := by
  simp [DiscreteCPT.nodeProb, copyCPT]

/-- Set `Z` to `true`. -/
def doZTrue : Node → Option Bool
  | .x => none
  | .y => none
  | .z => some true

lemma doZTrue_eq :
    doZTrue = doFinset ({.z} : Finset Node) (fun _ => true) := by
  funext v
  cases v <;> simp [doZTrue, doFinset]

/-- Observe every variable. -/
def doNone : Node → Option Bool := fun _ => none

lemma doNone_eq : doNone = doFinset (∅ : Finset Node) (fun _ => true) := by
  funext v
  cases v <;> simp [doNone, doFinset]

lemma copy_doX_weight (f : Node → Bool) :
    truncatedWeight copyGraph copyAcyclic copyCPT nodeDoX f =
      (if f .x = true then 1 else 0) * (PMF.pure (f .z) (f .y) * fairBit (f .z)) := by
  unfold truncatedWeight
  rw [prod_node]
  have hx : truncatedFactor copyGraph copyAcyclic copyCPT nodeDoX f .x =
      if f .x = true then 1 else 0 := by
    simp [truncatedFactor, nodeDoX]
  have hy : truncatedFactor copyGraph copyAcyclic copyCPT nodeDoX f .y =
      PMF.pure (f .z) (f .y) := by
    simp [truncatedFactor, nodeDoX, cptAt_eq_nodeProb, copy_node_y]
  have hz : truncatedFactor copyGraph copyAcyclic copyCPT nodeDoX f .z =
      fairBit (f .z) := by
    simp [truncatedFactor, nodeDoX, cptAt_eq_nodeProb, copy_node_z]
  simp [hx, hy, hz]

lemma copy_doZ_weight (f : Node → Bool) :
    truncatedWeight copyGraph copyAcyclic copyCPT doZTrue f =
      fairBit (f .x) * (PMF.pure (f .z) (f .y) * if f .z = true then 1 else 0) := by
  unfold truncatedWeight
  rw [prod_node]
  have hx : truncatedFactor copyGraph copyAcyclic copyCPT doZTrue f .x =
      fairBit (f .x) := by
    simp [truncatedFactor, doZTrue, cptAt_eq_nodeProb, copy_node_x]
  have hy : truncatedFactor copyGraph copyAcyclic copyCPT doZTrue f .y =
      PMF.pure (f .z) (f .y) := by
    simp [truncatedFactor, doZTrue, cptAt_eq_nodeProb, copy_node_y]
  have hz : truncatedFactor copyGraph copyAcyclic copyCPT doZTrue f .z =
      if f .z = true then 1 else 0 := by
    simp [truncatedFactor, doZTrue]
  simp [hx, hy, hz]

lemma copy_obs_weight (f : Node → Bool) :
    truncatedWeight copyGraph copyAcyclic copyCPT doNone f =
      fairBit (f .x) * (PMF.pure (f .z) (f .y) * fairBit (f .z)) := by
  unfold truncatedWeight
  rw [prod_node]
  have hx : truncatedFactor copyGraph copyAcyclic copyCPT doNone f .x =
      fairBit (f .x) := by
    simp [truncatedFactor, doNone, cptAt_eq_nodeProb, copy_node_x]
  have hy : truncatedFactor copyGraph copyAcyclic copyCPT doNone f .y =
      PMF.pure (f .z) (f .y) := by
    simp [truncatedFactor, doNone, cptAt_eq_nodeProb, copy_node_y]
  have hz : truncatedFactor copyGraph copyAcyclic copyCPT doNone f .z =
      fairBit (f .z) := by
    simp [truncatedFactor, doNone, cptAt_eq_nodeProb, copy_node_z]
  simp [hx, hy, hz]

lemma copy_in_edge :
    UndirectedEdge (deleteIncoming copyGraph ({.x} : Finset Node)) .y .z :=
  Or.inr ⟨⟨rfl, rfl⟩, Finset.notMem_singleton.mpr (by decide)⟩

/-- **Rule 1, failing separation.** `Z → Y` is still an edge after the arrows
into `X` are deleted, so `[Z, Y]` is an active trail given `X`. -/
theorem copy_rule1_not_separated :
    ¬ DSeparatedFull (deleteIncoming copyGraph ({.x} : Finset Node))
        ({.y} : Set Node) ({.z} : Set Node) ({.x} : Set Node) := by
  intro hsep
  have htrail : HasActiveTrail (deleteIncoming copyGraph ({.x} : Finset Node))
      ({.x} : Set Node) .y .z :=
    ⟨[.y, .z], List.cons_ne_nil _ _, endpoints_pair .y .z, ActiveTrail.two copy_in_edge⟩
  exact hsep .y (Set.mem_singleton _) .z (Set.mem_singleton _) (by decide) htrail

lemma copy_doX_mass_yz :
    nodeMass copyGraph copyAcyclic copyCPT nodeDoX (fun f => f .y && f .z) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [copy_doX_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]

lemma copy_doX_mass_z :
    nodeMass copyGraph copyAcyclic copyCPT nodeDoX (fun f => f .z) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [copy_doX_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]

lemma copy_doX_mass_y :
    nodeMass copyGraph copyAcyclic copyCPT nodeDoX (fun f => f .y) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [copy_doX_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]

lemma copy_doX_mass_all :
    nodeMass copyGraph copyAcyclic copyCPT nodeDoX (fun _ => true) = 1 := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [copy_doX_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply, ENNReal.inv_two_add_inv_two]

/-- **Rule 1, failing masses.** `Y` copies `Z`, and `do(X = true)` does not
touch that edge. `P(Y = true | Z = true) = 1`, while `P(Y = true) = 1/2`. -/
theorem copy_rule1_conditional_ne :
    nodeMass copyGraph copyAcyclic copyCPT (doFinset ({.x} : Finset Node) (fun _ => true))
        (fun f => f .y && f .z) /
      nodeMass copyGraph copyAcyclic copyCPT (doFinset ({.x} : Finset Node) (fun _ => true))
        (fun f => f .z) ≠
    nodeMass copyGraph copyAcyclic copyCPT (doFinset ({.x} : Finset Node) (fun _ => true))
        (fun f => f .y) /
      nodeMass copyGraph copyAcyclic copyCPT (doFinset ({.x} : Finset Node) (fun _ => true))
        (fun _ => true) := by
  rw [← nodeDoX_eq, copy_doX_mass_yz, copy_doX_mass_z, copy_doX_mass_y, copy_doX_mass_all,
    div_half, div_by_one]
  exact one_ne_inv_two

lemma copy_out_no_edge {u v : Node} :
    ¬ (deleteOutgoing copyGraph ({.z} : Finset Node)).edges u v := by
  intro h
  rcases h with ⟨hedge, hsrc⟩
  simp only [copyGraph] at hedge
  rcases hedge with ⟨rfl, rfl⟩
  exact hsrc (Finset.mem_singleton_self _)

lemma copy_out_isolates_z {u v : Node} :
    UndirectedEdge (deleteOutgoing copyGraph ({.z} : Finset Node)) u v →
      u ≠ .z ∧ v ≠ .z := by
  intro h
  rcases h with hdir | hrev
  · exact absurd hdir copy_out_no_edge
  · exact absurd hrev copy_out_no_edge

/-- **Rule 2, positive separation.** Deleting the arrows out of `Z` removes
`Z → Y`. With `X` empty, `Y` and `Z` are d-separated by the empty set. -/
theorem copy_rule2_separated :
    DSeparatedFull (deleteOutgoing copyGraph ({.z} : Finset Node))
      ({.y} : Set Node) ({.z} : Set Node) (∅ : Set Node) :=
  separated_from_isolated copy_out_isolates_z _

lemma copy_doZ_mass_y :
    nodeMass copyGraph copyAcyclic copyCPT doZTrue (fun f => f .y) = 1 := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [copy_doZ_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply, ENNReal.inv_two_add_inv_two]

lemma copy_doZ_mass_all :
    nodeMass copyGraph copyAcyclic copyCPT doZTrue (fun _ => true) = 1 := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [copy_doZ_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply, ENNReal.inv_two_add_inv_two]

lemma copy_obs_mass_yz :
    nodeMass copyGraph copyAcyclic copyCPT doNone (fun f => f .y && f .z) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [copy_obs_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]
  exact two_quarters

lemma copy_obs_mass_z :
    nodeMass copyGraph copyAcyclic copyCPT doNone (fun f => f .z) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [copy_obs_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]
  exact two_quarters

/-- **Rule 2, positive masses, and the parent hypothesis.**

`Z` has no parents, so every parent of `Z` lies in `Z`. Both
`P(Y = true | do(Z = true))` and `P(Y = true | Z = true)` equal `1`. -/
theorem copy_rule2_conditional_eq :
    (∀ v ∈ ({.z} : Finset Node), ∀ u, copyGraph.edges u v → u ∈ ({.z} : Finset Node)) ∧
      nodeMass copyGraph copyAcyclic copyCPT (doFinset ({.z} : Finset Node) (fun _ => true))
          (fun f => f .y) /
        nodeMass copyGraph copyAcyclic copyCPT (doFinset ({.z} : Finset Node) (fun _ => true))
          (fun _ => true) =
      nodeMass copyGraph copyAcyclic copyCPT (doFinset (∅ : Finset Node) (fun _ => true))
          (fun f => f .y && f .z) /
        nodeMass copyGraph copyAcyclic copyCPT (doFinset (∅ : Finset Node) (fun _ => true))
          (fun f => f .z) := by
  refine ⟨?_, ?_⟩
  · intro v hv u hedge
    have hvZ : v = .z := by simpa using hv
    subst hvZ
    simp [copyGraph] at hedge
  · rw [← doZTrue_eq, ← doNone_eq, copy_doZ_mass_y, copy_doZ_mass_all,
      copy_obs_mass_yz, copy_obs_mass_z, div_by_one, div_half]

lemma copy_rule3_edge :
    UndirectedEdge
      (deleteIncoming (deleteIncoming copyGraph ({.x} : Finset Node)) ({.z} : Finset Node))
      .y .z :=
  Or.inr ⟨⟨⟨rfl, rfl⟩, Finset.notMem_singleton.mpr (by decide)⟩,
    Finset.notMem_singleton.mpr (by decide)⟩

/-- **Rule 3, failing separation.** `W` is empty, so `Z(W) = Z`. Deleting the
arrows into `X` and into `Z` leaves `Z → Y`, an active trail. -/
theorem copy_rule3_not_separated :
    ¬ DSeparatedFull
        (deleteIncoming (deleteIncoming copyGraph ({.x} : Finset Node)) ({.z} : Finset Node))
        ({.y} : Set Node) ({.z} : Set Node) ({.x} : Set Node) := by
  intro hsep
  have htrail : HasActiveTrail
      (deleteIncoming (deleteIncoming copyGraph ({.x} : Finset Node)) ({.z} : Finset Node))
      ({.x} : Set Node) .y .z :=
    ⟨[.y, .z], List.cons_ne_nil _ _, endpoints_pair .y .z, ActiveTrail.two copy_rule3_edge⟩
  exact hsep .y (Set.mem_singleton _) .z (Set.mem_singleton _) (by decide) htrail

lemma copy_obs_mass_y :
    nodeMass copyGraph copyAcyclic copyCPT doNone (fun f => f .y) =
      (2 : ℝ≥0∞)⁻¹ := by
  unfold nodeMass
  rw [sum_node]
  simp_rw [copy_obs_weight, nodeOf, sum_bool]
  simp [fairBit_apply, PMF.pure_apply]
  exact two_quarters

/-- **Rule 3, failing masses.** `P(Y = true | do(Z = true)) = 1` and the
observational `P(Y = true) = 1/2`. -/
theorem copy_rule3_conditional_ne :
    nodeMass copyGraph copyAcyclic copyCPT (doFinset ({.z} : Finset Node) (fun _ => true))
        (fun f => f .y) /
      nodeMass copyGraph copyAcyclic copyCPT (doFinset ({.z} : Finset Node) (fun _ => true))
        (fun _ => true) ≠
    nodeMass copyGraph copyAcyclic copyCPT (doFinset (∅ : Finset Node) (fun _ => true))
        (fun f => f .y) /
      nodeMass copyGraph copyAcyclic copyCPT (doFinset (∅ : Finset Node) (fun _ => true))
        (fun _ => true) := by
  rw [← doZTrue_eq, ← doNone_eq, copy_doZ_mass_y, copy_doZ_mass_all, copy_obs_mass_y]
  have hobs : nodeMass copyGraph copyAcyclic copyCPT doNone (fun _ => true) = 1 := by
    unfold nodeMass
    rw [sum_node]
    simp_rw [copy_obs_weight, nodeOf, sum_bool]
    simp [fairBit_apply, PMF.pure_apply]
    exact four_quarters
  rw [hobs]
  conv_lhs => rw [div_by_one]
  conv_rhs => rw [div_by_one]
  exact one_ne_inv_two

/-! ## The bow, exchanging `do(X)` with observing `X` -/

/-- Mass of the configurations accepted by `keep` in bow model 2. -/
noncomputable def bowSlice (keep : (Bow → Bool) → Bool) : ℝ≥0∞ :=
  ∑ f, if keep f = true then bowCPT2.jointWeight f else 0

lemma bow_slice_xy :
    bowSlice (fun f => f .x && f .y) = (2 : ℝ≥0∞)⁻¹ := by
  unfold bowSlice
  rw [sum_bow]
  simp_rw [joint2_factor, bowOf, sum_bool, bow_factor_support₂, fairBit_apply]
  simp

lemma bow_slice_x :
    bowSlice (fun f => f .x) = (2 : ℝ≥0∞)⁻¹ := by
  unfold bowSlice
  rw [sum_bow]
  simp_rw [joint2_factor, bowOf, sum_bool, bow_factor_support₂, fairBit_apply]
  simp

/-- **Rule 2 on the bow, observational side.** In model 2,
`P(Y = true | X = true) = 1`. -/
theorem bow_obs_conditional_eq_one :
    bowSlice (fun f => f .x && f .y) / bowSlice (fun f => f .x) = 1 := by
  rw [bow_slice_xy, bow_slice_x, div_half]

lemma bow_out_uy :
    UndirectedEdge (deleteOutgoing bowGraph ({.x} : Finset Bow)) .y .u :=
  Or.inr ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), Finset.notMem_singleton.mpr (by decide)⟩

lemma bow_out_ux :
    UndirectedEdge (deleteOutgoing bowGraph ({.x} : Finset Bow)) .u .x :=
  Or.inl ⟨Or.inl ⟨rfl, rfl⟩, Finset.notMem_singleton.mpr (by decide)⟩

/-- The fork `Y ← U → X` stays open after the arrows out of `X` are deleted. -/
lemma bow_fork_active :
    IsActive (deleteOutgoing bowGraph ({.x} : Finset Bow)) (∅ : Set Bow)
      ⟨.y, .u, .x, bow_out_uy, bow_out_ux, by decide⟩ := by
  intro hblocked
  rcases hblocked with ⟨_, hu⟩ | ⟨hcol, _, _⟩
  · simp at hu
  · rcases hcol with ⟨hyu, _⟩
    rcases hyu.1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact absurd ha (by decide)
    · exact absurd ha (by decide)
    · exact absurd hb (by decide)

lemma bow_fork_trail :
    ActiveTrail (deleteOutgoing bowGraph ({.x} : Finset Bow)) (∅ : Set Bow)
      [Bow.y, Bow.u, Bow.x] :=
  ActiveTrail.cons bow_out_uy bow_out_ux (by decide) bow_fork_active
    (ActiveTrail.two bow_out_ux)

lemma bow_fork_endpoints :
    PathEndpoints [Bow.y, Bow.u, Bow.x] = some (Bow.y, Bow.x) := by
  simp [PathEndpoints]

/-- **Rule 2, failing separation on the bow.** With the arrows out of `X`
deleted and nothing conditioned, `Y ← U → X` is an active trail. -/
theorem bow_rule2_not_separated :
    ¬ DSeparatedFull (deleteOutgoing bowGraph ({.x} : Finset Bow))
        ({.y} : Set Bow) ({.x} : Set Bow) (∅ : Set Bow) := by
  intro hsep
  exact hsep .y (by simp) .x (by simp) (by decide)
    ⟨[Bow.y, Bow.u, Bow.x], List.cons_ne_nil _ _, bow_fork_endpoints, bow_fork_trail⟩

/-- **Rule 2, failing masses on the bow.** Model 2 has
`P(Y = true | X = true) = 1` and `P(Y = true | do(X = true)) = 1/2`. -/
theorem bow_rule2_conditional_ne :
    bowSlice (fun f => f .x && f .y) / bowSlice (fun f => f .x) ≠
      bowDoMass bowCPT2 true := by
  rw [bow_obs_conditional_eq_one, bow_do_model2]
  exact one_ne_inv_two

end Mettapedia.GSLT.Causality.DoCalculus
