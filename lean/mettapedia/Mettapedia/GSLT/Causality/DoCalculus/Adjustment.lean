import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.List.Nodup
import Mettapedia.GSLT.Causality.DoCalculus.TruncatedFactorization
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation

/-!
# Back-door adjustment for one treatment

On a finite acyclic causal model with one shared value type, the parents of a
treatment are a back-door set whenever the outcome is not itself a parent of
the treatment. For that set the g-formula collapses to parent adjustment:

`P(y | do(x)) = Σ_{pa} P(y | x, pa) P(pa)`,

provided the treatment's conditional table is positive on every parent row.
The identity is the sum over parent rows of the observational conditional.
It is not claimed for an arbitrary back-door set.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open scoped BigOperators ENNReal

variable {V β : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype β] [DecidableEq β] [MeasurableSpace β]

variable (graph : DirectedGraph V)
variable (hAcyclic : graph.IsAcyclic)
variable [DecidableRel graph.edges]

/-! ## Mutilating the graph -/

/-- Delete every edge that leaves `forbidden`. -/
def deleteOutgoing (forbidden : Finset V) : DirectedGraph V where
  edges u v := graph.edges u v ∧ u ∉ forbidden

/-- Delete every edge that enters `forbidden`. -/
def deleteIncoming (forbidden : Finset V) : DirectedGraph V where
  edges u v := graph.edges u v ∧ v ∉ forbidden

omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β]
  [DecidableRel graph.edges] in
/-- A path that uses only a subset of the edges is a path of the original graph. -/
lemma reachable_of_edge_subset {H : DirectedGraph V}
    (hsub : ∀ u v, H.edges u v → graph.edges u v) {a b : V}
    (path : H.Reachable a b) : graph.Reachable a b := by
  induction path with
  | refl => exact reachable_refl graph _
  | step hedge _ ih => exact Path.step (hsub _ _ hedge) ih

include hAcyclic in
omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β]
  [DecidableRel graph.edges] in
lemma deleteOutgoing_acyclic (forbidden : Finset V) :
    (deleteOutgoing graph forbidden).IsAcyclic := by
  intro v ⟨u, hedge, hreach⟩
  have hsub : ∀ a b, (deleteOutgoing graph forbidden).edges a b → graph.edges a b :=
    fun _ _ hab => And.left hab
  exact hAcyclic v ⟨u, And.left hedge, reachable_of_edge_subset graph hsub hreach⟩

include hAcyclic in
omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β]
  [DecidableRel graph.edges] in
lemma deleteIncoming_acyclic (forbidden : Finset V) :
    (deleteIncoming graph forbidden).IsAcyclic := by
  intro v ⟨u, hedge, hreach⟩
  have hsub : ∀ a b, (deleteIncoming graph forbidden).edges a b → graph.edges a b :=
    fun _ _ hab => And.left hab
  exact hAcyclic v ⟨u, And.left hedge, reachable_of_edge_subset graph hsub hreach⟩

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
/-- **Back-door criterion** for one treatment and one outcome.

`Z` contains neither the treatment nor a descendant of it, and in the graph
with the arrows out of the treatment removed, the treatment is fully
d-separated from the outcome by `Z`. In that graph the only surviving paths
are the back-door paths.
-/
structure BackDoorCriterion (treatment outcome : V) (Z : Set V) : Prop where
  avoidsTreatment : ∀ z ∈ Z, z ≠ treatment
  avoidsDescendants : ∀ z ∈ Z, z ∉ graph.descendants treatment
  separated :
    DSeparation.DSeparatedFull (deleteOutgoing graph {treatment}) {treatment} {outcome} Z

include hAcyclic in
omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β]
  [DecidableRel graph.edges] in
lemma parent_not_descendant (treatment parent : V)
    (hedge : graph.edges parent treatment) :
    parent ∉ graph.descendants treatment := by
  intro hdesc
  exact hAcyclic parent ⟨treatment, hedge, hdesc.1⟩

include hAcyclic in
omit [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β]
  [DecidableRel graph.edges] in
lemma parent_ne_treatment (treatment parent : V)
    (hedge : graph.edges parent treatment) : parent ≠ treatment := by
  intro h
  exact graph.isAcyclic_irrefl hAcyclic treatment (h ▸ hedge)

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] [DecidableRel graph.edges] in
/-- An edge out of a vertex whose outgoing edges were deleted has to be incoming. -/
lemma incoming_of_undirected_deleted {forbidden : Finset V} {u v : V}
    (hu : u ∈ forbidden)
    (hedge : DSeparation.UndirectedEdge (deleteOutgoing graph forbidden) u v) :
    graph.edges v u ∧ v ∉ forbidden := by
  rcases hedge with hout | hin
  · exact absurd hout.2 (by simpa using hu)
  · exact ⟨hin.1, hin.2⟩

include hAcyclic in
omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
/-- **Parents meet the back-door criterion** when the outcome is not a parent
of the treatment. A direct arrow from the outcome into the treatment is a
back-door path with no intermediate vertex, so no conditioning set blocks it.
-/
theorem parents_satisfy_backDoor (treatment outcome : V)
    (hnotParent : ¬ graph.edges outcome treatment) :
    BackDoorCriterion graph treatment outcome
      (parentsFinset graph treatment : Set V) where
  avoidsTreatment := by
    intro z hz
    exact parent_ne_treatment graph hAcyclic treatment z
      ((mem_parentsFinset_iff graph z treatment).1 hz)
  avoidsDescendants := by
    intro z hz
    exact parent_not_descendant graph hAcyclic treatment z
      ((mem_parentsFinset_iff graph z treatment).1 hz)
  separated := by
    intro x hx y hy hxy htrail
    simp only [Set.mem_singleton_iff] at hx hy
    subst hx hy
    rcases htrail with ⟨_p, _, hends, hact⟩
    exact DSeparation.ActiveTrail.casesOn
      (motive := fun p _ =>
        DSeparation.PathEndpoints p = some (x, y) → False)
      hact
      (fun v hpe => by
        simp only [DSeparation.PathEndpoints] at hpe
        injection hpe with hpair
        exact hxy ((Prod.mk.inj hpair).1.symm.trans (Prod.mk.inj hpair).2))
      (fun {u v : V} hEdge hpe => by
        simp only [DSeparation.PathEndpoints, List.getLast_singleton] at hpe
        injection hpe with hpair
        have hu : u = x := (Prod.ext_iff.mp hpair).1
        have hv : v = y := (Prod.ext_iff.mp hpair).2
        have hedge :
            DSeparation.UndirectedEdge (deleteOutgoing graph {x}) x y := by
          simpa [hu, hv] using hEdge
        rcases incoming_of_undirected_deleted graph
            (Finset.mem_singleton_self x) hedge with ⟨hin, _⟩
        exact hnotParent hin)
      (fun {a b c : V} {_rest : List V} hab hbc hac hAct _hTail hpe => by
        have ha : a = x := by
          simp only [DSeparation.PathEndpoints] at hpe
          injection hpe with hpair
          exact (Prod.ext_iff.mp hpair).1
        subst ha
        rcases incoming_of_undirected_deleted graph
            (Finset.mem_singleton_self a) hab with ⟨hedge, _⟩
        have hnotCol :
            ¬ DSeparation.IsCollider (deleteOutgoing graph {a})
              ⟨a, b, c, hab, hbc, hac⟩ := by
          intro hcol
          exact hcol.1.2 (Finset.mem_singleton_self a)
        have hmem : b ∈ (parentsFinset graph a : Set V) :=
          Finset.mem_coe.mpr ((mem_parentsFinset_iff graph b a).2 hedge)
        exact hAct (Or.inl ⟨hnotCol, hmem⟩))
      hends

/-! ## Elimination of a topological suffix -/

/-- One g-formula factor, with the node's own value written into the store. -/
noncomputable def stepFactor (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (omitNode : V → Bool) (store : V → β) (v : V) (b : β) : ℝ≥0∞ :=
  if omitNode v then 1 else
    cptAt graph hAcyclic cpt v (parentFunOf graph (Function.update store v b) v) b

/-- The factor of a finished configuration. Omitted nodes contribute `1`. -/
noncomputable def piece (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (omitNode : V → Bool) (f : V → β) (v : V) : ℝ≥0∞ :=
  if omitNode v then 1 else cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)

/-- Product of the factors at or after position `k` in `order`. -/
noncomputable def suffixProd (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (omitNode : V → Bool) (order : List V) (k : ℕ) (f : V → β) : ℝ≥0∞ :=
  ∏ v, if k ≤ order.idxOf v then piece graph hAcyclic cpt omitNode f v else 1

/-- Sum the conditional table of every node from index `k` on.

A node clamped to `some b` contributes only that value. An omitted node
contributes the constant `1` instead of its conditional table. The recursion
follows `order`; it is the g-formula sum, not a probability parameter.
-/
noncomputable def elim (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V) (clamp : V → Option β) (omitNode : V → Bool)
    (k : ℕ) (store : V → β) : ℝ≥0∞ :=
  if hk : k < order.length then
    match clamp (order[k]) with
    | some b =>
        stepFactor graph hAcyclic cpt omitNode store (order[k]) b *
          elim cpt order clamp omitNode (k + 1) (Function.update store (order[k]) b)
    | none =>
        ∑ b : β,
          stepFactor graph hAcyclic cpt omitNode store (order[k]) b *
            elim cpt order clamp omitNode (k + 1) (Function.update store (order[k]) b)
  else
    1
termination_by order.length - k

include hAcyclic in
omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
lemma parentFunOf_update_self (store : V → β) (v : V) (b : β) :
    parentFunOf graph (Function.update store v b) v = parentFunOf graph store v := by
  funext p
  have hne : ↑p ≠ v := by
    intro h
    have hedge : graph.edges v v := by
      simpa [h] using (mem_parentsFinset_iff graph (↑p) v).1 p.property
    exact graph.isAcyclic_irrefl hAcyclic v hedge
  simp only [parentFunOf]
  rw [Function.update_of_ne hne]

omit [DecidableEq β] in
lemma elim_of_ge (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V) (clamp : V → Option β) (omitNode : V → Bool)
    {k : ℕ} (hk : order.length ≤ k) (store : V → β) :
    elim graph hAcyclic cpt order clamp omitNode k store = 1 := by
  conv_lhs => unfold elim
  simp [show ¬ k < order.length from by omega]

omit [DecidableEq β] in
lemma elim_some (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V) (clamp : V → Option β) (omitNode : V → Bool)
    {k : ℕ} (hk : k < order.length) {b : β}
    (hclamp : clamp (order[k]) = some b) (store : V → β) :
    elim graph hAcyclic cpt order clamp omitNode k store =
      stepFactor graph hAcyclic cpt omitNode store (order[k]) b *
        elim graph hAcyclic cpt order clamp omitNode (k + 1)
          (Function.update store (order[k]) b) := by
  conv_lhs => unfold elim
  rw [dif_pos hk]
  simp only [hclamp]

omit [DecidableEq β] in
lemma elim_none (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V) (clamp : V → Option β) (omitNode : V → Bool)
    {k : ℕ} (hk : k < order.length)
    (hclamp : clamp (order[k]) = none) (store : V → β) :
    elim graph hAcyclic cpt order clamp omitNode k store =
      ∑ b : β,
        stepFactor graph hAcyclic cpt omitNode store (order[k]) b *
          elim graph hAcyclic cpt order clamp omitNode (k + 1)
            (Function.update store (order[k]) b) := by
  conv_lhs => unfold elim
  rw [dif_pos hk]
  simp only [hclamp]

omit [Fintype β] [DecidableEq β] in
lemma stepFactor_of_kept (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (omitNode : V → Bool) (store : V → β) (v : V) (b : β)
    (hkeep : omitNode v = false) :
    stepFactor graph hAcyclic cpt omitNode store v b =
      cptAt graph hAcyclic cpt v (parentFunOf graph store v) b := by
  simp [stepFactor, hkeep, parentFunOf_update_self graph hAcyclic store v b]

omit [DecidableEq β] in
/-- A suffix in which every node is summed and none is omitted totals `1`. -/
lemma elim_open (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V) (clamp : V → Option β) (omitNode : V → Bool) (k : ℕ)
    (hopen : ∀ i, k ≤ i → (hi : i < order.length) →
      clamp (order[i]'hi) = none ∧ omitNode (order[i]'hi) = false)
    (store : V → β) :
    elim graph hAcyclic cpt order clamp omitNode k store = 1 := by
  suffices ∀ n k store, order.length - k = n →
      (∀ i, k ≤ i → (hi : i < order.length) →
        clamp (order[i]'hi) = none ∧ omitNode (order[i]'hi) = false) →
      elim graph hAcyclic cpt order clamp omitNode k store = 1 from
    this (order.length - k) k store rfl hopen
  intro n
  induction n with
  | zero =>
      intro k store hn _
      exact elim_of_ge graph hAcyclic cpt order clamp omitNode (by omega) store
  | succ n ih =>
      intro k store hn hopen
      have hk : k < order.length := by omega
      have hhere := hopen k (le_refl k) hk
      rw [elim_none graph hAcyclic cpt order clamp omitNode hk hhere.1 store]
      have htail : ∀ b,
          elim graph hAcyclic cpt order clamp omitNode (k + 1)
            (Function.update store (order[k]) b) = 1 := by
        intro b
        refine ih (k + 1) _ (by omega) ?_
        intro i hi hlen
        exact hopen i (by omega) hlen
      simp_rw [htail, mul_one, stepFactor_of_kept graph hAcyclic cpt omitNode store _ _ hhere.2]
      exact BayesianNetwork.DiscreteCPT.pmf_sum_eq_one _

/-- The store agrees with every clamp on the strict prefix of `order`. -/
def PrefixMatches (clamp : V → Option β) (order : List V) (k : ℕ) (store : V → β) : Prop :=
  ∀ i, i < k → ∀ hi : i < order.length,
    ∀ b, clamp (order[i]'hi) = some b → store (order[i]'hi) = b

/-- `f` agrees with `store` on the strict prefix. -/
def prefixAgreeBool (order : List V) (k : ℕ) (store f : V → β) : Bool :=
  (List.range k).all fun i =>
    if h : i < order.length then decide (f (order[i]'h) = store (order[i]'h)) else true

/-- `f` agrees with every clamped coordinate. -/
def clampAgreeBool (clamp : V → Option β) (f : V → β) : Bool :=
  decide (∀ v b, clamp v = some b → f v = b)

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] [DecidableRel graph.edges] in
lemma list_all_true_iff {α : Type} (l : List α) (p : α → Bool) :
    l.all p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.all_cons, Bool.and_eq_true, List.mem_cons, ih]
      constructor
      · intro h b hb
        rcases hb with rfl | hb
        · exact h.1
        · exact h.2 b hb
      · intro h
        exact ⟨h a (Or.inl rfl), fun b hb => h b (Or.inr hb)⟩

omit [Fintype V] [DecidableEq V] [Fintype β] [MeasurableSpace β] in
lemma prefixAgreeBool_iff (order : List V) (k : ℕ) (store f : V → β) :
    prefixAgreeBool order k store f = true ↔
      ∀ i, i < k → ∀ hi : i < order.length, f (order[i]'hi) = store (order[i]'hi) := by
  unfold prefixAgreeBool
  rw [list_all_true_iff]
  constructor
  · intro h i hi hlen
    have hbit := h i (List.mem_range.mpr hi)
    rw [dif_pos hlen] at hbit
    exact of_decide_eq_true hbit
  · intro h i hi
    rw [List.mem_range] at hi
    by_cases hlen : i < order.length
    · rw [dif_pos hlen]
      exact decide_eq_true (h i hi hlen)
    · rw [dif_neg hlen]

omit [DecidableEq V] [MeasurableSpace β] in
lemma clampAgreeBool_iff (clamp : V → Option β) (f : V → β) :
    clampAgreeBool clamp f = true ↔ ∀ v b, clamp v = some b → f v = b := by
  unfold clampAgreeBool
  simp [decide_eq_true_eq]

omit [Fintype V] [Fintype β] [MeasurableSpace β] in
lemma idx_get (order : List V) (hnodup : order.Nodup) {k : ℕ} (hk : k < order.length) :
    order.idxOf (order[k]'hk) = k := by
  simpa using List.get_idxOf (l := order) hnodup ⟨k, hk⟩

omit [Fintype V] [DecidableEq V] [Fintype β] [MeasurableSpace β] in
lemma prefix_ne_current (order : List V) (hnodup : order.Nodup)
    {k : ℕ} (hk : k < order.length) {i : ℕ} (hi : i < k) (hlen : i < order.length) :
    order[i]'hlen ≠ order[k]'hk := by
  intro heq
  have hinj := (List.nodup_iff_injective_get).1 hnodup
  have := hinj (show order.get ⟨i, hlen⟩ = order.get ⟨k, hk⟩ by simpa using heq)
  exact (ne_of_lt hi) (Fin.ext_iff.mp this)

omit [Fintype V] [Fintype β] [MeasurableSpace β] in
lemma prefixAgreeBool_succ_update (order : List V) (hnodup : order.Nodup)
    {k : ℕ} (hk : k < order.length) (store f : V → β) (b : β) :
    prefixAgreeBool order (k + 1) (Function.update store (order[k]) b) f = true ↔
      prefixAgreeBool order k store f = true ∧ f (order[k]) = b := by
  rw [prefixAgreeBool_iff, prefixAgreeBool_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi hlen
      have hne := prefix_ne_current order hnodup hk hi hlen
      have := h i (Nat.lt_succ_of_lt hi) hlen
      simpa [Function.update_of_ne hne] using this
    · have := h k (Nat.lt_succ_self k) hk
      simpa [Function.update_self] using this
  · intro h i hi hlen
    by_cases hik : i < k
    · have hne := prefix_ne_current order hnodup hk hik hlen
      simpa [Function.update_of_ne hne] using h.1 i hik hlen
    · have heq : i = k := by omega
      subst heq
      simpa [Function.update_self] using h.2

omit [Fintype β] [DecidableEq β] in
lemma suffixProd_of_ge (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (omitNode : V → Bool) (order : List V)
    (hmem : ∀ v, v ∈ order) {k : ℕ} (hk : order.length ≤ k) (f : V → β) :
    suffixProd graph hAcyclic cpt omitNode order k f = 1 := by
  unfold suffixProd
  refine Finset.prod_eq_one fun v _ => ?_
  have hlt : order.idxOf v < order.length := List.idxOf_lt_length_iff.mpr (hmem v)
  have : ¬ k ≤ order.idxOf v := by omega
  simp [this]

omit [Fintype β] [DecidableEq β] in
lemma suffixProd_succ (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (omitNode : V → Bool) (order : List V) (hnodup : order.Nodup)
    (hmem : ∀ v, v ∈ order) {k : ℕ} (hk : k < order.length) (f : V → β) :
    suffixProd graph hAcyclic cpt omitNode order k f =
      piece graph hAcyclic cpt omitNode f (order[k]) *
        suffixProd graph hAcyclic cpt omitNode order (k + 1) f := by
  unfold suffixProd
  set v0 : V := order[k]
  have hidx : order.idxOf v0 = k := idx_get order hnodup hk
  have hprod :=
    Finset.mul_prod_erase (s := Finset.univ)
      (f := fun v => if k ≤ order.idxOf v then piece graph hAcyclic cpt omitNode f v else 1)
      (a := v0) (Finset.mem_univ v0)
  have hgate : (if k ≤ order.idxOf v0 then piece graph hAcyclic cpt omitNode f v0 else 1) =
      piece graph hAcyclic cpt omitNode f v0 := by simp [hidx]
  rw [← hprod, hgate]
  refine congrArg (piece graph hAcyclic cpt omitNode f v0 * ·) ?_
  have hv0one :
      (if k + 1 ≤ order.idxOf v0 then piece graph hAcyclic cpt omitNode f v0 else 1) = 1 := by
    simp [hidx]
  rw [← Finset.prod_erase (s := Finset.univ) (a := v0) hv0one]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hv0 : v ≠ v0 := by simpa using hv
  have hlt : order.idxOf v < order.length := List.idxOf_lt_length_iff.mpr (hmem v)
  have hidxne : order.idxOf v ≠ k := by
    intro heq
    have hvget : order[order.idxOf v] = v := List.getElem_idxOf hlt
    exact hv0 (by simpa [v0, heq, hk] using hvget.symm)
  have hiff : k ≤ order.idxOf v ↔ k + 1 ≤ order.idxOf v := by
    constructor
    · intro hle
      have : k < order.idxOf v := lt_of_le_of_ne hle hidxne.symm
      omega
    · intro hle
      omega
  by_cases hle : k ≤ order.idxOf v
  · have hle' : k + 1 ≤ order.idxOf v := hiff.mp hle
    simp [hle, hle']
  · have hle' : ¬ k + 1 ≤ order.idxOf v := fun h => hle (hiff.mpr h)
    simp [hle, hle']

omit [Fintype β] in
lemma parentFunOf_of_prefix (order : List V)
    (horder : (network (β := β) graph hAcyclic).IsTopologicalOrder order)
    {v : V} {k : ℕ} (hk : order.idxOf v = k) (store f : V → β)
    (hpref : prefixAgreeBool order k store f = true) :
    parentFunOf graph f v = parentFunOf graph store v := by
  funext p
  have hlt : order.idxOf p.val < k := by simpa [hk] using idxOf_parent_lt graph hAcyclic order horder p
  have hlen : order.idxOf p.val < order.length :=
    List.idxOf_lt_length_iff.mpr (horder.2.1 p.val)
  have hagree := (prefixAgreeBool_iff order k store f).1 hpref
    (order.idxOf p.val) hlt hlen
  have hget : order[order.idxOf p.val] = p.val := List.getElem_idxOf hlen
  simpa [parentFunOf, hget] using hagree

omit [Fintype β] in
lemma piece_eq_stepFactor_of_prefix (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (omitNode : V → Bool) (order : List V)
    (horder : (network (β := β) graph hAcyclic).IsTopologicalOrder order)
    {v : V} {k : ℕ} (hk : order.idxOf v = k) (store f : V → β)
    (hpref : prefixAgreeBool order k store f = true) :
    piece graph hAcyclic cpt omitNode f v =
      stepFactor graph hAcyclic cpt omitNode store v (f v) := by
  unfold piece stepFactor
  by_cases homit : omitNode v
  · simp [homit]
  · simp only [homit]
    rw [parentFunOf_update_self graph hAcyclic store v (f v),
      parentFunOf_of_prefix graph hAcyclic order horder hk store f hpref]

/-- The g-formula sum is the topological elimination. -/
theorem elim_eq_sum (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V)
    (horder : (network (β := β) graph hAcyclic).IsTopologicalOrder order)
    (clamp : V → Option β) (omitNode : V → Bool) (k : ℕ) (store : V → β)
    (hpre : PrefixMatches clamp order k store) :
    elim graph hAcyclic cpt order clamp omitNode k store =
      ∑ f : V → β,
        if prefixAgreeBool order k store f && clampAgreeBool clamp f then
          suffixProd graph hAcyclic cpt omitNode order k f else 0 := by
  have hnodup : order.Nodup := horder.1
  have hmem : ∀ v, v ∈ order := horder.2.1
  suffices ∀ n k store, order.length - k = n → PrefixMatches clamp order k store →
      elim graph hAcyclic cpt order clamp omitNode k store =
        ∑ f, if prefixAgreeBool order k store f && clampAgreeBool clamp f then
          suffixProd graph hAcyclic cpt omitNode order k f else 0 from
    this (order.length - k) k store rfl hpre
  intro n
  induction n with
  | zero =>
      intro k store hn hpre
      have hk : order.length ≤ k := by omega
      rw [elim_of_ge graph hAcyclic cpt order clamp omitNode hk store]
      have hprod : ∀ f, suffixProd graph hAcyclic cpt omitNode order k f = 1 :=
        fun f => suffixProd_of_ge graph hAcyclic cpt omitNode order hmem hk f
      have hstorePref : prefixAgreeBool order k store store = true := by
        rw [prefixAgreeBool_iff]
        intro i _ hi
        rfl
      have hstoreClamp : clampAgreeBool clamp store = true := by
        rw [clampAgreeBool_iff]
        intro v b hb
        have hlen : order.idxOf v < order.length := List.idxOf_lt_length_iff.mpr (hmem v)
        have hik : order.idxOf v < k := by omega
        have hb' : clamp (order[order.idxOf v]'hlen) = some b := by
          simpa [List.getElem_idxOf hlen] using hb
        have hmatch := hpre (order.idxOf v) hik hlen b hb'
        simpa [List.getElem_idxOf hlen] using hmatch
      have honly : ∀ f,
          (prefixAgreeBool order k store f && clampAgreeBool clamp f) = true ↔ f = store := by
        intro f
        constructor
        · intro h
          rw [Bool.and_eq_true] at h
          funext v
          have hlen : order.idxOf v < order.length := List.idxOf_lt_length_iff.mpr (hmem v)
          have hik : order.idxOf v < k := by omega
          have hagree := (prefixAgreeBool_iff order k store f).1 h.1
            (order.idxOf v) hik hlen
          simpa [List.getElem_idxOf hlen] using hagree
        · rintro rfl
          simp [hstorePref, hstoreClamp]
      have hsum : (∑ f : V → β, if f = store then (1 : ℝ≥0∞) else 0) = 1 := by
        simp
      rw [← hsum]
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases hf : prefixAgreeBool order k store f && clampAgreeBool clamp f
      · have hf' : f = store := (honly f).1 hf
        subst hf'
        simp [hstorePref, hstoreClamp, hprod]
      · have hfne : f ≠ store := by
          intro h
          exact hf ((honly f).2 h)
        simp [hf, hfne]
  | succ n ih =>
      intro k store hn hpre
      have hk : k < order.length := by omega
      set v : V := order[k]
      have hidx : order.idxOf v = k := idx_get order hnodup hk
      cases hclamp : clamp v with
      | some b =>
          rw [elim_some graph hAcyclic cpt order clamp omitNode hk hclamp store]
          have hpre' :
              PrefixMatches clamp order (k + 1) (Function.update store v b) := by
            intro i hi hlen c hc
            by_cases hik : i < k
            · have hne : order[i]'hlen ≠ v := by
                simpa [v] using prefix_ne_current order hnodup hk hik hlen
              rw [Function.update_of_ne hne]
              exact hpre i hik hlen c hc
            · have heq : i = k := by omega
              cases heq
              rw [Function.update_self]
              have hc' : clamp v = some c := by simpa [v] using hc
              rw [hclamp] at hc'
              cases hc'
              rfl
          have htail := ih (k + 1) (Function.update store v b) (by omega) hpre'
          rw [htail, Finset.mul_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          have hgate : (prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                clampAgreeBool clamp f) = true ↔
              (prefixAgreeBool order k store f && clampAgreeBool clamp f) = true := by
            constructor
            · intro h
              rw [Bool.and_eq_true] at h
              have hsplit :=
                (prefixAgreeBool_succ_update order hnodup hk store f b).1 h.1
              have : clampAgreeBool clamp f = true := h.2
              simp [hsplit.1, this]
            · intro h
              rw [Bool.and_eq_true] at h
              have hvb : f v = b := (clampAgreeBool_iff clamp f).1 h.2 v b hclamp
              have hsucc :=
                (prefixAgreeBool_succ_update order hnodup hk store f b).2 ⟨h.1, hvb⟩
              have hsucc' :
                  prefixAgreeBool order (k + 1) (Function.update store v b) f = true := by
                simpa [v] using hsucc
              rw [Bool.and_eq_true]
              exact ⟨hsucc', h.2⟩
          by_cases hind : prefixAgreeBool order k store f && clampAgreeBool clamp f
          · have hboth : prefixAgreeBool order k store f = true ∧
                clampAgreeBool clamp f = true := by
              rw [← Bool.and_eq_true]
              exact hind
            have hvb : f v = b := (clampAgreeBool_iff clamp f).1 hboth.2 v b hclamp
            have hpreK : prefixAgreeBool order (k + 1)
                (Function.update store (order[k]) b) f = true :=
              (prefixAgreeBool_succ_update order hnodup hk store f b).2 ⟨hboth.1, hvb⟩
            have hpreV : prefixAgreeBool order (k + 1)
                (Function.update store v b) f = true := by
              simpa [v] using hpreK
            have hgateT : (prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                clampAgreeBool clamp f) = true := by
              rw [Bool.and_eq_true]
              exact ⟨hpreV, hboth.2⟩
            simp only [hgateT, hind, ite_true]
            have hsplit :=
              suffixProd_succ graph hAcyclic cpt omitNode order hnodup hmem hk f
            rw [hsplit]
            have hpiece :=
              piece_eq_stepFactor_of_prefix graph hAcyclic cpt omitNode order horder
                hidx store f hboth.1
            have hpiece' : piece graph hAcyclic cpt omitNode f (order[k]) =
                stepFactor graph hAcyclic cpt omitNode store (order[k]) b := by
              simpa [v, hvb] using hpiece
            rw [hpiece']
          · have hind' : ¬ (prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                clampAgreeBool clamp f) = true := by
              intro h
              exact hind (hgate.mp h)
            simp [hind, hind']
      | none =>
          rw [elim_none graph hAcyclic cpt order clamp omitNode hk hclamp store]
          have hpreb : ∀ b,
              PrefixMatches clamp order (k + 1) (Function.update store v b) := by
            intro b i hi hlen c hc
            by_cases hik : i < k
            · have hne : order[i]'hlen ≠ v := by
                simpa [v] using prefix_ne_current order hnodup hk hik hlen
              rw [Function.update_of_ne hne]
              exact hpre i hik hlen c hc
            · have heq : i = k := by omega
              cases heq
              exfalso
              have hc' : clamp v = some c := by simpa [v] using hc
              rw [hclamp] at hc'
              cases hc'
          have hvorder : v = order[k] := by simp [v]
          simp_rw [← hvorder]
          have hih : ∀ b,
              elim graph hAcyclic cpt order clamp omitNode (k + 1)
                  (Function.update store v b) =
                ∑ f,
                  if prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                      clampAgreeBool clamp f then
                    suffixProd graph hAcyclic cpt omitNode order (k + 1) f else 0 :=
            fun b => ih (k + 1) (Function.update store v b) (by omega) (hpreb b)
          have hmul : ∀ b,
              stepFactor graph hAcyclic cpt omitNode store v b *
                  elim graph hAcyclic cpt order clamp omitNode (k + 1)
                    (Function.update store v b) =
                ∑ f,
                  if prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                      clampAgreeBool clamp f then
                    stepFactor graph hAcyclic cpt omitNode store v b *
                      suffixProd graph hAcyclic cpt omitNode order (k + 1) f else 0 := by
            intro b
            rw [hih b, Finset.mul_sum]
            refine Finset.sum_congr rfl fun f _ => ?_
            by_cases hp :
                prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                  clampAgreeBool clamp f
            · simp [hp]
            · simp [hp, mul_zero]
          rw [Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
            (fun b (_ : b ∈ Finset.univ) => hmul b)]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ => ?_
          have hpart : ∀ b,
              ((prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                  clampAgreeBool clamp f) = true) ↔
                (prefixAgreeBool order k store f && clampAgreeBool clamp f) = true ∧
                  f v = b := by
            intro b
            constructor
            · intro h
              rw [Bool.and_eq_true] at h
              have hsplit :=
                (prefixAgreeBool_succ_update order hnodup hk store f b).1 h.1
              exact ⟨by simp [hsplit.1, h.2], hsplit.2⟩
            · intro h
              rw [Bool.and_eq_true] at h
              have hleft : prefixAgreeBool order k store f = true := h.1.1
              have hsucc :=
                (prefixAgreeBool_succ_update order hnodup hk store f b).2 ⟨hleft, h.2⟩
              have hsucc' :
                  prefixAgreeBool order (k + 1) (Function.update store v b) f = true := by
                simpa [v] using hsucc
              rw [Bool.and_eq_true]
              exact ⟨hsucc', h.1.2⟩
          by_cases hbase : prefixAgreeBool order k store f && clampAgreeBool clamp f
          · have hsumb :
                (∑ b, if prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                    clampAgreeBool clamp f then
                    stepFactor graph hAcyclic cpt omitNode store v b *
                      suffixProd graph hAcyclic cpt omitNode order (k + 1) f else 0) =
                  stepFactor graph hAcyclic cpt omitNode store v (f v) *
                    suffixProd graph hAcyclic cpt omitNode order (k + 1) f := by
              have hone : ∀ b,
                  (if prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                      clampAgreeBool clamp f then
                      stepFactor graph hAcyclic cpt omitNode store v b *
                        suffixProd graph hAcyclic cpt omitNode order (k + 1) f else 0) =
                    if b = f v then
                      stepFactor graph hAcyclic cpt omitNode store v (f v) *
                        suffixProd graph hAcyclic cpt omitNode order (k + 1) f else 0 := by
                intro b
                by_cases hb : b = f v
                · have htrue := (hpart b).2 ⟨hbase, hb.symm⟩
                  subst hb
                  rw [htrue]
                  simp
                · have hfalse :
                      ¬ (prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                          clampAgreeBool clamp f) = true := by
                    intro h
                    exact hb ((hpart b).1 h).2.symm
                  simp [hb, hfalse]
              simp_rw [hone]
              simp
            rw [Bool.and_eq_true] at hbase
            rw [hsumb]
            have hpiece :=
              piece_eq_stepFactor_of_prefix graph hAcyclic cpt omitNode order horder
                hidx store f hbase.1
            have hsplit :=
              suffixProd_succ graph hAcyclic cpt omitNode order hnodup hmem hk f
            have hpiece' :
                piece graph hAcyclic cpt omitNode f (order[k]) =
                  stepFactor graph hAcyclic cpt omitNode store v (f v) := by
              simpa [v] using hpiece
            simp only [hbase.1, hbase.2, Bool.and_self, ite_true]
            rw [hsplit, hpiece']
          · have hzero : ∀ b,
                ¬ (prefixAgreeBool order (k + 1) (Function.update store v b) f &&
                    clampAgreeBool clamp f) = true := by
              intro b h
              exact hbase ((hpart b).1 h).1
            simp only [hbase]
            apply Finset.sum_eq_zero
            intro b _
            simp [hzero b]

omit [DecidableEq β] in
lemma elim_agree_treatment (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V) (hnodup : order.Nodup) (clamp clamp' : V → Option β)
    (omitNode : V → Bool) (t : V) (x x' : β)
    (hidx : order.idxOf t < order.length) (hget : order[order.idxOf t] = t)
    (hct : clamp t = some x) (hct' : clamp' t = some x')
    (homit : omitNode t = true)
    (hafterO : ∀ i, order.idxOf t < i → (hi : i < order.length) →
      omitNode (order[i]'hi) = false)
    (hafterC : ∀ i, order.idxOf t < i → (hi : i < order.length) →
      clamp (order[i]'hi) = none)
    (hafterC' : ∀ i, order.idxOf t < i → (hi : i < order.length) →
      clamp' (order[i]'hi) = none)
    (hoff : ∀ v, v ≠ t → clamp v = clamp' v) :
    ∀ k, k ≤ order.idxOf t → ∀ store,
      elim graph hAcyclic cpt order clamp omitNode k store =
        elim graph hAcyclic cpt order clamp' omitNode k store := by
  intro k hk
  suffices ∀ n k, order.idxOf t - k = n → k ≤ order.idxOf t → ∀ store,
      elim graph hAcyclic cpt order clamp omitNode k store =
        elim graph hAcyclic cpt order clamp' omitNode k store from
    this (order.idxOf t - k) k rfl hk
  intro n
  induction n with
  | zero =>
      intro k hn hk store
      have heq : k = order.idxOf t := by omega
      subst heq
      have hopen : ∀ i, order.idxOf t + 1 ≤ i → (hi : i < order.length) →
          clamp (order[i]'hi) = none ∧ omitNode (order[i]'hi) = false := by
        intro i hi hlen
        exact ⟨hafterC i (by omega) hlen, hafterO i (by omega) hlen⟩
      have hopen' : ∀ i, order.idxOf t + 1 ≤ i → (hi : i < order.length) →
          clamp' (order[i]'hi) = none ∧ omitNode (order[i]'hi) = false := by
        intro i hi hlen
        exact ⟨hafterC' i (by omega) hlen, hafterO i (by omega) hlen⟩
      have htail :=
        elim_open graph hAcyclic cpt order clamp omitNode (order.idxOf t + 1) hopen
      have htail' :=
        elim_open graph hAcyclic cpt order clamp' omitNode (order.idxOf t + 1) hopen'
      rw [elim_some graph hAcyclic cpt order clamp omitNode hidx
          (by simpa [hget] using hct),
        elim_some graph hAcyclic cpt order clamp' omitNode hidx
          (by simpa [hget] using hct')]
      simp [homit, stepFactor, hget, htail, htail']
  | succ n ih =>
      intro k hn hk store
      have hklt : k < order.idxOf t := by omega
      have hlen : k < order.length := by omega
      have hvne : order[k] ≠ t := by
        intro heq
        have := idx_get order hnodup hlen
        rw [heq] at this
        omega
      have hsame : clamp (order[k]) = clamp' (order[k]) := hoff _ hvne
      cases hclamp : clamp (order[k]) with
      | some b =>
          rw [hsame] at hclamp
          rw [elim_some graph hAcyclic cpt order clamp omitNode hlen (hsame.symm ▸ hclamp),
            elim_some graph hAcyclic cpt order clamp' omitNode hlen hclamp]
          simp_rw [ih (k + 1) (by omega) (by omega)]
      | none =>
          rw [hsame] at hclamp
          rw [elim_none graph hAcyclic cpt order clamp omitNode hlen (hsame.symm ▸ hclamp),
            elim_none graph hAcyclic cpt order clamp' omitNode hlen hclamp]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp_rw [ih (k + 1) (by omega) (by omega)]

/-! ## Parent adjustment -/

/-- Product of every conditional table except the treatment's. -/
noncomputable def exceptWeight (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (f : V → β) : ℝ≥0∞ :=
  ∏ v, if v = treatment then 1 else
    cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)

/-- `f` gives the parents of `treatment` the row `pa`. -/
def parentsMatch (treatment : V) (pa : ParentFun (β := β) graph treatment) (f : V → β) : Bool :=
  decide (∀ u, (hu : u ∈ parentsFinset graph treatment) → f u = pa ⟨u, hu⟩)

omit [Fintype β] [MeasurableSpace β] in
lemma parentsMatch_iff (treatment : V) (pa : ParentFun (β := β) graph treatment) (f : V → β) :
    parentsMatch graph treatment pa f = true ↔ parentFunOf graph f treatment = pa := by
  unfold parentsMatch parentFunOf
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    funext p
    exact h p.val p.property
  · intro h u hu
    simpa [h] using congrFun h ⟨u, hu⟩

omit [Fintype β] [MeasurableSpace β] in
lemma parentsMatch_parentFun (treatment : V) (f : V → β) :
    parentsMatch graph treatment (parentFunOf graph f treatment) f = true :=
  (parentsMatch_iff graph treatment (parentFunOf graph f treatment) f).2 rfl

/-- Clamp the treatment and its parents; leave every other node free. -/
def clampParents (treatment : V) (x : β) (pa : ParentFun (β := β) graph treatment)
    (v : V) : Option β :=
  if v = treatment then some x else
    if hv : v ∈ parentsFinset graph treatment then some (pa ⟨v, hv⟩) else none

include hAcyclic in
omit [MeasurableSpace β] in
lemma clampAgree_clampParents_iff (treatment : V) (x : β)
    (pa : ParentFun (β := β) graph treatment) (f : V → β) :
    clampAgreeBool (clampParents graph treatment x pa) f = true ↔
      parentsMatch graph treatment pa f = true ∧ f treatment = x := by
  rw [clampAgreeBool_iff, parentsMatch_iff]
  constructor
  · intro h
    have hx : f treatment = x := h treatment x (by simp [clampParents])
    refine ⟨?_, hx⟩
    funext p
    have hne : ↑p ≠ treatment :=
      parent_ne_treatment graph hAcyclic treatment (↑p)
        ((mem_parentsFinset_iff graph (↑p) treatment).1 p.property)
    have hp : f (↑p) = pa p :=
      h (↑p) (pa p) (by simp [clampParents, hne, p.property])
    simpa [parentFunOf] using hp
  · intro h v b hb
    by_cases hv : v = treatment
    · subst hv
      simp only [clampParents, ite_true] at hb
      cases hb
      exact h.2
    · simp only [clampParents, hv, ite_false] at hb
      by_cases hparent : v ∈ parentsFinset graph treatment
      · simp only [hparent, dite_true] at hb
        cases hb
        have := congrFun h.1 ⟨v, hparent⟩
        simpa [parentFunOf] using this
      · simp [hparent] at hb

omit [Fintype β] [DecidableEq β] in
lemma exceptWeight_eq_suffixProd (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V) (_hmem : ∀ v, v ∈ order) (treatment : V) (f : V → β) :
    exceptWeight graph hAcyclic cpt treatment f =
      suffixProd graph hAcyclic cpt (fun v => decide (v = treatment)) order 0 f := by
  unfold exceptWeight suffixProd piece
  refine Finset.prod_congr rfl fun v _ => ?_
  have : 0 ≤ order.idxOf v := Nat.zero_le _
  simp [this, decide_eq_true_eq]

omit [Fintype β] [DecidableEq β] in
lemma except_ne_top (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (f : V → β) :
    exceptWeight graph hAcyclic cpt treatment f ≠ ∞ := by
  unfold exceptWeight
  refine ENNReal.prod_ne_top fun v _ => ?_
  by_cases hv : v = treatment
  · simp [hv]
  · simp only [hv, ite_false]
    exact (cpt.cpt v _).apply_ne_top _

omit [Fintype β] [DecidableEq β] in
lemma jointWeight_eq_except (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (f : V → β) :
    cpt.jointWeight f =
      cptAt graph hAcyclic cpt treatment (parentFunOf graph f treatment) (f treatment) *
        exceptWeight graph hAcyclic cpt treatment f := by
  have hjoint : cpt.jointWeight f =
      ∏ v, cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v) := by
    unfold DiscreteCPT.jointWeight
    refine Finset.prod_congr rfl fun v _ => ?_
    exact (cptAt_eq_nodeProb graph hAcyclic cpt f v).symm
  rw [hjoint]
  have hsplit :=
    Finset.mul_prod_erase (s := Finset.univ)
      (f := fun v => cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v))
      (a := treatment) (Finset.mem_univ treatment)
  rw [← hsplit]
  refine congrArg
    (cptAt graph hAcyclic cpt treatment (parentFunOf graph f treatment) (f treatment) * ·) ?_
  unfold exceptWeight
  have hrest :=
    Finset.mul_prod_erase (s := Finset.univ)
      (f := fun v => if v = treatment then (1 : ℝ≥0∞) else
        cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v))
      (a := treatment) (Finset.mem_univ treatment)
  have htreatment :
      (if treatment = treatment then (1 : ℝ≥0∞) else
        cptAt graph hAcyclic cpt treatment (parentFunOf graph f treatment) (f treatment)) = 1 := by
    simp
  rw [← hrest, htreatment, one_mul]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvn : v ≠ treatment := by simpa using hv
  simp [hvn]

/-- Sum of the g-formula over configurations with treatment `x` and parent row `pa`. -/
noncomputable def allSlice (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (x : β) (pa : ParentFun (β := β) graph treatment) : ℝ≥0∞ :=
  ∑ f, if parentsMatch graph treatment pa f && decide (f treatment = x) then
    exceptWeight graph hAcyclic cpt treatment f else 0

/-- The same sum, further restricted to outcome `y`. -/
noncomputable def outcomeSlice (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment outcome : V) (x y : β) (pa : ParentFun (β := β) graph treatment) : ℝ≥0∞ :=
  ∑ f, if parentsMatch graph treatment pa f && decide (f treatment = x) &&
      decide (f outcome = y) then
    exceptWeight graph hAcyclic cpt treatment f else 0

lemma allSlice_ne_top (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (x : β) (pa : ParentFun (β := β) graph treatment) :
    allSlice graph hAcyclic cpt treatment x pa ≠ ∞ := by
  unfold allSlice
  refine (ENNReal.sum_ne_top).2 fun f _ => ?_
  by_cases h : parentsMatch graph treatment pa f && decide (f treatment = x)
  · simpa [h] using except_ne_top graph hAcyclic cpt treatment f
  · simp [h]

lemma outcomeSlice_ne_top (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment outcome : V) (x y : β) (pa : ParentFun (β := β) graph treatment) :
    outcomeSlice graph hAcyclic cpt treatment outcome x y pa ≠ ∞ := by
  unfold outcomeSlice
  refine (ENNReal.sum_ne_top).2 fun f _ => ?_
  by_cases h : parentsMatch graph treatment pa f && decide (f treatment = x) &&
      decide (f outcome = y)
  · simpa [h] using except_ne_top graph hAcyclic cpt treatment f
  · simp [h]

lemma outcomeSlice_le_allSlice (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment outcome : V) (x y : β) (pa : ParentFun (β := β) graph treatment) :
    outcomeSlice graph hAcyclic cpt treatment outcome x y pa ≤
      allSlice graph hAcyclic cpt treatment x pa := by
  unfold outcomeSlice allSlice
  refine Finset.sum_le_sum fun f _ => ?_
  by_cases hy : decide (f outcome = y)
  · by_cases h : parentsMatch graph treatment pa f && decide (f treatment = x)
    · simp [h, hy]
    · simp [h]
  · simp [hy]

/-- **Parent slice of the g-formula, for one supplied topological order.**

Omitting the treatment factor and summing every non-parent does not depend on
the value written at the treatment. Parents occur before the treatment, and
every later conditional table sums to `1`.
-/
theorem allSlice_indep_treatment_of_order
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V)
    (horder : (network (β := β) graph hAcyclic).IsTopologicalOrder order)
    (treatment : V) (x x' : β) (pa : ParentFun (β := β) graph treatment) :
    allSlice graph hAcyclic cpt treatment x pa =
      allSlice graph hAcyclic cpt treatment x' pa := by
  let omitNode : V → Bool := fun v => decide (v = treatment)
  have hmem : ∀ v, v ∈ order := horder.2.1
  have hlen : order.idxOf treatment < order.length :=
    List.idxOf_lt_length_iff.mpr (hmem treatment)
  have hget : order[order.idxOf treatment] = treatment := List.getElem_idxOf hlen
  have hafterC : ∀ x0 i, order.idxOf treatment < i → (hi : i < order.length) →
      clampParents graph treatment x0 pa (order[i]'hi) = none := by
    intro x0 i hi hlen'
    have hne : (order[i]'hlen') ≠ treatment := by
      intro heq
      have hidx : order.idxOf (order[i]'hlen') = i := idx_get order horder.1 hlen'
      exact (Nat.ne_of_lt hi) (by simpa [heq] using hidx)
    have hnotParent : (order[i]'hlen') ∉ parentsFinset graph treatment := by
      intro hp
      have hlt := idxOf_parent_lt graph hAcyclic order horder ⟨order[i]'hlen', hp⟩
      have hidx : order.idxOf (order[i]'hlen') = i := idx_get order horder.1 hlen'
      have hbefore : i < order.idxOf treatment := by simpa [hidx] using hlt
      exact Nat.lt_irrefl i (Nat.lt_trans hbefore hi)
    simp [clampParents, hne, hnotParent]
  have hafterO : ∀ i, order.idxOf treatment < i → (hi : i < order.length) →
      omitNode (order[i]'hi) = false := by
    intro i hi hlen'
    have hne : (order[i]'hlen') ≠ treatment := by
      intro heq
      have hidx : order.idxOf (order[i]'hlen') = i := idx_get order horder.1 hlen'
      exact (Nat.ne_of_lt hi) (by simpa [heq] using hidx)
    simp [omitNode, hne]
  have hempty : ∀ (clamp : V → Option β) (store : V → β),
      PrefixMatches clamp order 0 store := by
    intro _ _ i hi
    omega
  have hgate : ∀ (store : V → β) x0 f,
      (prefixAgreeBool order 0 store f &&
          clampAgreeBool (clampParents graph treatment x0 pa) f) =
        (parentsMatch graph treatment pa f && decide (f treatment = x0)) := by
    intro store x0 f
    have hpref : prefixAgreeBool order 0 store f = true := by
      rw [prefixAgreeBool_iff]
      intro i hi hlen'
      omega
    by_cases hclamp : clampAgreeBool (clampParents graph treatment x0 pa) f = true
    · have hpm := (clampAgree_clampParents_iff graph hAcyclic treatment x0 pa f).1 hclamp
      simp [hpref, hclamp, hpm.1, hpm.2]
    · have hclampF : clampAgreeBool (clampParents graph treatment x0 pa) f = false :=
        Bool.eq_false_iff.mpr hclamp
      have hnot :
          ¬ (parentsMatch graph treatment pa f = true ∧ f treatment = x0) := by
        intro h
        exact hclamp ((clampAgree_clampParents_iff graph hAcyclic treatment x0 pa f).2 h)
      have hright :
          (parentsMatch graph treatment pa f && decide (f treatment = x0)) = false := by
        apply Bool.eq_false_iff.mpr
        intro hr
        rw [Bool.and_eq_true] at hr
        exact hnot ⟨hr.1, of_decide_eq_true hr.2⟩
      simp [hpref, hclampF, hright]
  have hweight : ∀ f,
      exceptWeight graph hAcyclic cpt treatment f =
        suffixProd graph hAcyclic cpt omitNode order 0 f :=
    fun f => exceptWeight_eq_suffixProd graph hAcyclic cpt order hmem treatment f
  have hEx :=
    elim_eq_sum graph hAcyclic cpt order horder
      (clampParents graph treatment x pa) omitNode 0 (fun _ => x)
      (hempty (clampParents graph treatment x pa) (fun _ => x))
  have hEx' :=
    elim_eq_sum graph hAcyclic cpt order horder
      (clampParents graph treatment x' pa) omitNode 0 (fun _ => x)
      (hempty (clampParents graph treatment x' pa) (fun _ => x))
  have hagree :=
    elim_agree_treatment graph hAcyclic cpt order horder.1
      (clampParents graph treatment x pa) (clampParents graph treatment x' pa)
      omitNode treatment x x' hlen hget
      (by simp [clampParents]) (by simp [clampParents])
      (by simp [omitNode])
      hafterO (hafterC x) (hafterC x')
      (by
        intro v hv
        simp [clampParents, hv])
      0 (Nat.zero_le _) (fun _ => x)
  unfold allSlice
  simp_rw [← hgate (fun _ => x) x, ← hgate (fun _ => x) x', hweight]
  rw [← hEx, ← hEx']
  exact hagree

omit [MeasurableSpace β] in
/-- Mass of `do(treatment = x)` on the configurations with outcome `y`. -/
noncomputable def interventionalMass (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment outcome : V) (x y : β) : ℝ≥0∞ :=
  ∑ f, if decide (f outcome = y) then
    truncatedWeight graph hAcyclic cpt (fun v => if v = treatment then some x else none) f else 0

omit [Fintype β] in
lemma truncatedWeight_do_eq_except (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (x : β) (f : V → β) :
    truncatedWeight graph hAcyclic cpt (fun v => if v = treatment then some x else none) f =
      if f treatment = x then exceptWeight graph hAcyclic cpt treatment f else 0 := by
  unfold truncatedWeight exceptWeight truncatedFactor
  have hbeta : ∀ v,
      (match (fun v => if v = treatment then some x else none) v with
        | none => cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)
        | some a => if f v = a then 1 else 0) =
      (match (if v = treatment then some x else none) with
        | none => cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)
        | some a => if f v = a then 1 else 0) :=
    fun v => rfl
  have hprod :=
    Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun v (_ : v ∈ Finset.univ) => hbeta v)
  refine Eq.trans hprod ?_
  have hsplit :=
    Finset.mul_prod_erase (s := Finset.univ)
      (f := fun v =>
        match (if v = treatment then some x else none) with
        | none => cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)
        | some a => if f v = a then 1 else 0)
      (a := treatment) (Finset.mem_univ treatment)
  rw [← hsplit]
  have hfactor :
      (match (if treatment = treatment then some x else none) with
        | none => cptAt graph hAcyclic cpt treatment (parentFunOf graph f treatment) (f treatment)
        | some a => if f treatment = a then 1 else 0) =
        if f treatment = x then 1 else 0 := by
    simp
  rw [hfactor]
  by_cases hfx : f treatment = x
  · rw [if_pos hfx, one_mul]
    have hrest :=
      Finset.mul_prod_erase (s := Finset.univ)
        (f := fun v => if v = treatment then (1 : ℝ≥0∞) else
          cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v))
        (a := treatment) (Finset.mem_univ treatment)
    have hone :
        (if treatment = treatment then (1 : ℝ≥0∞) else
          cptAt graph hAcyclic cpt treatment (parentFunOf graph f treatment)
            (f treatment)) = 1 := by simp
    rw [← hrest, hone, one_mul]
    have hrhs :
        (if f treatment = x then
            ∏ v ∈ Finset.univ.erase treatment,
              if v = treatment then (1 : ℝ≥0∞) else
                cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v)
          else 0) =
          ∏ v ∈ Finset.univ.erase treatment,
            if v = treatment then (1 : ℝ≥0∞) else
              cptAt graph hAcyclic cpt v (parentFunOf graph f v) (f v) := by
      simp [hfx]
    rw [hrhs]
    apply Finset.prod_congr rfl
    intro v hv
    have hvn : v ≠ treatment := (Finset.mem_erase.mp hv).1
    simp [hvn]
  · simp [hfx]

lemma interventionalMass_eq_slices (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment outcome : V) (x y : β) :
    interventionalMass graph hAcyclic cpt treatment outcome x y =
      ∑ pa : ParentFun (β := β) graph treatment,
        outcomeSlice graph hAcyclic cpt treatment outcome x y pa := by
  unfold interventionalMass outcomeSlice
  simp_rw [truncatedWeight_do_eq_except graph hAcyclic cpt treatment x]
  have hswap :
      (∑ pa, ∑ f, if parentsMatch graph treatment pa f && decide (f treatment = x) &&
          decide (f outcome = y) then exceptWeight graph hAcyclic cpt treatment f else 0) =
        ∑ f, ∑ pa, if parentsMatch graph treatment pa f && decide (f treatment = x) &&
          decide (f outcome = y) then exceptWeight graph hAcyclic cpt treatment f else 0 :=
    Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hpa :
      (∑ pa, if parentsMatch graph treatment pa f && decide (f treatment = x) &&
          decide (f outcome = y) then exceptWeight graph hAcyclic cpt treatment f else 0) =
        if decide (f treatment = x) && decide (f outcome = y) then
          exceptWeight graph hAcyclic cpt treatment f else 0 := by
    have hone :=
      Finset.sum_ite_eq' (s := Finset.univ) (a := parentFunOf graph f treatment)
        (b := fun pa =>
          if parentsMatch graph treatment pa f && decide (f treatment = x) &&
              decide (f outcome = y) then exceptWeight graph hAcyclic cpt treatment f else 0)
    -- only the matching parent row survives, and it matches `f`
    have hself := parentsMatch_parentFun graph treatment f
    simp only [Finset.mem_univ, ite_true] at hone
    -- hone is the wrong shape if the ite is outside. Rewrite directly.
    classical
    have hunique : ∀ pa,
        (if pa = parentFunOf graph f treatment then
            (if decide (f treatment = x) && decide (f outcome = y) then
              exceptWeight graph hAcyclic cpt treatment f else 0) else 0) =
          if parentsMatch graph treatment pa f && decide (f treatment = x) &&
              decide (f outcome = y) then exceptWeight graph hAcyclic cpt treatment f else 0 := by
      intro pa
      by_cases hrow : pa = parentFunOf graph f treatment
      · subst hrow
        simp [hself]
      · have hnomatch : parentsMatch graph treatment pa f = false := by
          apply Bool.eq_false_iff.mpr
          intro h
          exact hrow ((parentsMatch_iff graph treatment pa f).1 h).symm
        simp [hrow, hnomatch]
    simp_rw [← hunique]
    simp
  rw [hpa]
  by_cases hx : f treatment = x
  · by_cases hy : f outcome = y
    · simp [hx, hy]
    · simp [hx, hy]
  · simp [hx]

lemma parentJoint_eq (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (x : β) (pa : ParentFun (β := β) graph treatment) :
    (∑ f, if parentsMatch graph treatment pa f && decide (f treatment = x) then
        cpt.jointWeight f else 0) =
      cptAt graph hAcyclic cpt treatment pa x * allSlice graph hAcyclic cpt treatment x pa := by
  unfold allSlice
  simp_rw [jointWeight_eq_except graph hAcyclic cpt treatment]
  refine Eq.trans (Finset.sum_congr rfl fun f _ => ?_) (Finset.mul_sum _ _ _).symm
  by_cases h : parentsMatch graph treatment pa f && decide (f treatment = x)
  · rw [Bool.and_eq_true] at h
    have hrow := (parentsMatch_iff graph treatment pa f).1 h.1
    have hx := decide_eq_true_eq.mp h.2
    simp [h.1, hrow, hx]
  · simp [h]

lemma outcomeJoint_eq (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment outcome : V) (x y : β) (pa : ParentFun (β := β) graph treatment) :
    (∑ f, if parentsMatch graph treatment pa f && decide (f treatment = x) &&
        decide (f outcome = y) then cpt.jointWeight f else 0) =
      cptAt graph hAcyclic cpt treatment pa x *
        outcomeSlice graph hAcyclic cpt treatment outcome x y pa := by
  unfold outcomeSlice
  simp_rw [jointWeight_eq_except graph hAcyclic cpt treatment]
  refine Eq.trans (Finset.sum_congr rfl fun f _ => ?_) (Finset.mul_sum _ _ _).symm
  by_cases h : parentsMatch graph treatment pa f && decide (f treatment = x) &&
      decide (f outcome = y)
  · rw [Bool.and_eq_true, Bool.and_eq_true] at h
    have hrow := (parentsMatch_iff graph treatment pa f).1 h.1.1
    have hx := decide_eq_true_eq.mp h.1.2
    simp [h, hrow, hx]
  · simp [h]

/-- Observational mass of one parent row. -/
noncomputable def parentMass (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (pa : ParentFun (β := β) graph treatment) : ℝ≥0∞ :=
  ∑ f, if parentsMatch graph treatment pa f then cpt.jointWeight f else 0

lemma parentMass_eq_allSlice_of_order
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (order : List V)
    (horder : (network (β := β) graph hAcyclic).IsTopologicalOrder order)
    (treatment : V) (x : β) (pa : ParentFun (β := β) graph treatment) :
    parentMass graph hAcyclic cpt treatment pa =
      allSlice graph hAcyclic cpt treatment x pa := by
  have hpart : parentMass graph hAcyclic cpt treatment pa =
      ∑ a : β, ∑ f, if parentsMatch graph treatment pa f && decide (f treatment = a) then
        cpt.jointWeight f else 0 := by
    unfold parentMass
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hsplit : (if parentsMatch graph treatment pa f then cpt.jointWeight f else 0) =
        ∑ a : β, if parentsMatch graph treatment pa f && decide (f treatment = a) then
          cpt.jointWeight f else 0 := by
      have hone :=
        Finset.sum_ite_eq (s := Finset.univ) (a := f treatment)
          (b := fun _ => if parentsMatch graph treatment pa f then cpt.jointWeight f else 0)
      simp only [Finset.mem_univ, ite_true] at hone
      rw [← hone]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : a = f treatment
      · simp [ha]
      · have hne : f treatment ≠ a := Ne.symm ha
        simp [hne]
    exact hsplit
  rw [hpart]
  have hsummed :
      (∑ a : β, ∑ f, if parentsMatch graph treatment pa f && decide (f treatment = a) then
          cpt.jointWeight f else 0) =
        ∑ a : β, cptAt graph hAcyclic cpt treatment pa a *
          allSlice graph hAcyclic cpt treatment x pa := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [parentJoint_eq graph hAcyclic cpt treatment a pa,
      allSlice_indep_treatment_of_order graph hAcyclic cpt order horder treatment a x pa]
  rw [hsummed]
  rw [← Finset.sum_mul (s := Finset.univ)
    (f := fun a => cptAt graph hAcyclic cpt treatment pa a)
    (a := allSlice graph hAcyclic cpt treatment x pa)]
  have hsum : (∑ a : β, cptAt graph hAcyclic cpt treatment pa a) = 1 :=
    BayesianNetwork.DiscreteCPT.pmf_sum_eq_one _
  simp [hsum, one_mul]

/-- **Parent adjustment.**

If `pa ↦ cpt(treatment | pa)(x)` never vanishes, then
`P(outcome = y | do(treatment = x)) = Σ_{pa} P(y | x, pa) P(pa)`.
The conditional is the observational mass ratio, and it is `0` when the
parent row itself has mass `0`. Without the positivity hypothesis the identity
is false: an intervention can select a parent row the observational table
never used.
-/
theorem parentAdjustment (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment outcome : V) (x y : β)
    (hpos : ∀ pa : ParentFun (β := β) graph treatment,
      cptAt graph hAcyclic cpt treatment pa x ≠ 0) :
    interventionalMass graph hAcyclic cpt treatment outcome x y =
      ∑ pa : ParentFun (β := β) graph treatment,
        ((∑ f, if parentsMatch graph treatment pa f && decide (f treatment = x) &&
              decide (f outcome = y) then cpt.jointWeight f else 0) /
          (∑ f, if parentsMatch graph treatment pa f && decide (f treatment = x) then
              cpt.jointWeight f else 0)) *
          parentMass graph hAcyclic cpt treatment pa := by
  obtain ⟨order, horder⟩ := (network (β := β) graph hAcyclic).exists_topological_order
  rw [interventionalMass_eq_slices graph hAcyclic cpt treatment outcome x y]
  refine Finset.sum_congr rfl fun pa _ => ?_
  rw [outcomeJoint_eq graph hAcyclic cpt treatment outcome x y pa,
    parentJoint_eq graph hAcyclic cpt treatment x pa,
    parentMass_eq_allSlice_of_order graph hAcyclic cpt order horder treatment x pa]
  set c : ℝ≥0∞ := cptAt graph hAcyclic cpt treatment pa x
  set A : ℝ≥0∞ := allSlice graph hAcyclic cpt treatment x pa
  set S : ℝ≥0∞ := outcomeSlice graph hAcyclic cpt treatment outcome x y pa
  have hc0 : c ≠ 0 := hpos pa
  have hcTop : c ≠ ∞ := (cpt.cpt treatment _).apply_ne_top x
  have hA : A ≠ ∞ := allSlice_ne_top graph hAcyclic cpt treatment x pa
  have hSle : S ≤ A := outcomeSlice_le_allSlice graph hAcyclic cpt treatment outcome x y pa
  by_cases hA0 : A = 0
  · have hS0 : S = 0 := le_antisymm (hSle.trans (le_of_eq hA0)) (bot_le (a := S))
    simp [hS0, hA0, mul_zero, ENNReal.zero_div]
  · rw [ENNReal.mul_div_mul_left S A hc0 hcTop, ENNReal.div_mul_cancel hA0 hA]

end Mettapedia.GSLT.Causality.DoCalculus
