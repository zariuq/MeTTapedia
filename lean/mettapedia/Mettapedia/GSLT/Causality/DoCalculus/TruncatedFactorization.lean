import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mettapedia.GSLT.Causality.StructuralModels
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics

/-!
# Truncated factorization and surgery

On a finite acyclic causal model whose variables share one finite value type,
`do` has two descriptions.

* **Truncated factorization.** The joint weight of a configuration is the
  product of the conditional probability tables of the variables that were
  not set, and it is zero when a set variable disagrees with the configuration.
  This is the g-formula.
* **Surgery.** Independent exogenous noise, one lookup table per variable,
  realizes those tables. The structural mechanisms read the row selected by
  the parents. An intervention replaces the mechanisms of the set variables
  by constants (`StructuralModels.surgery`). The interventional law is the
  pushforward of the noise along the unique solution of the surgical model.

The two agree. The weight carrier is Mathlib's `PMF`: each conditional table
is already a `PMF`, and joints are its `ℝ≥0∞` values. A common finite alphabet
is the value type `StructuralModels.surgery` acts on.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.GSLT.Causality.StructuralModels
open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open scoped BigOperators ENNReal

variable {V β : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]

variable (graph : DirectedGraph V)
variable (acyclic : graph.IsAcyclic)
variable [DecidableRel graph.edges]

/-- The causal model with one shared finite alphabet. -/
abbrev network : BayesianNetwork V where
  graph := graph
  acyclic := acyclic
  stateSpace := fun _ => β
  measurableSpace := fun _ => inferInstance

/-- Parents of `v`, as a finset. -/
def parentsFinset (v : V) : Finset V :=
  Finset.univ.filter fun u => graph.edges u v

/-- A parent of `v`, packaged with the edge. -/
abbrev ParentIdx (v : V) := {u : V // u ∈ parentsFinset graph v}

/-- A row of the conditional table at `v`: one value per parent. -/
abbrev ParentFun (v : V) := ParentIdx graph v → β

/-- Exogenous noise: for each variable, a lookup table over parent rows. -/
abbrev Noise := ∀ v : V, ParentFun (β := β) graph v → β

omit [DecidableEq V] in
lemma mem_parentsFinset_iff (u v : V) :
    u ∈ parentsFinset graph v ↔ graph.edges u v := by
  simp [parentsFinset]

/-- The parent row read off a store. -/
def parentFunOf (x : V → β) (v : V) : ParentFun (β := β) graph v :=
  fun p => x p.val

/-- Convert a parent row into the assignment type used by `DiscreteCPT`. -/
def toParentAssignment (v : V) (f : ParentFun (β := β) graph v) :
    (network (β := β) graph acyclic).ParentAssignment v :=
  fun u hu =>
    f ⟨u, (mem_parentsFinset_iff graph u v).2
      (by simpa [network, BayesianNetwork.parents, DirectedGraph.parents] using hu)⟩

/-- Conditional weight of value `b` at `v` on parent row `pa`. -/
def cptAt (cpt : (network (β := β) graph acyclic).DiscreteCPT) (v : V)
    (pa : ParentFun (β := β) graph v) (b : β) : ℝ≥0∞ :=
  cpt.cpt v (toParentAssignment graph acyclic v pa) b

omit [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β] in
lemma cptAt_eq_nodeProb (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (x : V → β) (v : V) :
    cptAt graph acyclic cpt v (parentFunOf graph x v) (x v) =
      DiscreteCPT.nodeProb cpt x v := by
  unfold cptAt DiscreteCPT.nodeProb DiscreteCPT.parentAssignOfConfig
    toParentAssignment parentFunOf
  rfl

/-! ## Truncated factorization -/

/-- One factor of the g-formula at `v`.

An unset variable contributes its conditional table. A variable set to `a`
contributes `1` when the configuration agrees and `0` otherwise. -/
def truncatedFactor (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (x : V → β) (v : V) : ℝ≥0∞ :=
  match assignment v with
  | none => cptAt graph acyclic cpt v (parentFunOf graph x v) (x v)
  | some a => if x v = a then 1 else 0

/-- **Truncated factorization** of `do(assignment)` at configuration `x`. -/
noncomputable def truncatedWeight (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (x : V → β) : ℝ≥0∞ :=
  ∏ v, truncatedFactor graph acyclic cpt assignment x v

omit [DecidableEq V] [Fintype β] [Inhabited β] in
/-- With nothing set, the g-formula is the Bayesian-network joint. -/
theorem truncatedWeight_none_eq_jointWeight
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (x : V → β) :
    truncatedWeight graph acyclic cpt (fun _ => none) x = cpt.jointWeight x := by
  unfold truncatedWeight truncatedFactor DiscreteCPT.jointWeight
  refine Finset.prod_congr rfl fun v _ => ?_
  simpa using cptAt_eq_nodeProb graph acyclic cpt x v

/-- `do` on a finset of variables, setting each to the corresponding coordinate of `x`. -/
def doFinset (target : Finset V) (x : V → β) : V → Option β :=
  fun v => if v ∈ target then some (x v) else none

/-! ## Mechanisms, rank, and evaluation -/

/-- Mechanisms of one noise sample: each variable reads the row of its parents. -/
def mechanisms (u : Noise (β := β) graph) : Mechanisms V β :=
  fun v store => u v (parentFunOf graph store v)

omit [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β] in
lemma mechanisms_depends_parents (u : Noise (β := β) graph) (v : V) :
    DependsOnly (mechanisms graph u v) ((network (β := β) graph acyclic).parents v) := by
  intro store store' agree
  unfold mechanisms parentFunOf
  apply congrArg (u v)
  funext p
  exact agree p.val
    (by simpa [network, BayesianNetwork.parents, DirectedGraph.parents, parentsFinset]
      using p.property)

/-- Position of a variable in a list. -/
abbrev topologicalRank (order : List V) (v : V) : ℕ := order.idxOf v

omit [Fintype β] [DecidableEq β] [Inhabited β] in
lemma idxOf_parent_lt (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    {v : V} (p : ParentIdx graph v) :
    order.idxOf p.val < order.idxOf v := by
  have hedge : graph.edges p.val v :=
    (mem_parentsFinset_iff graph p.val v).1 p.property
  have hu : order.idxOf p.val < order.length :=
    List.idxOf_lt_length_iff.mpr (horder.2.1 p.val)
  have hv : order.idxOf v < order.length :=
    List.idxOf_lt_length_iff.mpr (horder.2.1 v)
  exact horder.2.2 p.val v hedge ⟨order.idxOf p.val, hu⟩ ⟨order.idxOf v, hv⟩
    (List.getElem_idxOf hu) (List.getElem_idxOf hv)

/-- A topological order ranks the noise mechanisms strictly below their parents' children. -/
def recursiveOfTopologicalOrder (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (u : Noise (β := β) graph) : Recursive (mechanisms graph u) where
  rank := topologicalRank order
  bound := order.length
  rank_lt v := List.idxOf_lt_length_iff.mpr (horder.2.1 v)
  depends v store store' agree := by
    apply mechanisms_depends_parents graph acyclic u v
    intro q hq
    have hp : q ∈ parentsFinset graph v :=
      (mem_parentsFinset_iff graph q v).2
        (by simpa [network, BayesianNetwork.parents, DirectedGraph.parents] using hq)
    exact agree q (idxOf_parent_lt graph acyclic order horder ⟨q, hp⟩)

/-- The value written for `v` by the surgical mechanism. -/
def written (assignment : V → Option β) (u : Noise (β := β) graph) (store : V → β) (v : V) : β :=
  match assignment v with
  | some a => a
  | none => u v (parentFunOf graph store v)

omit [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β] in
lemma written_eq_surgery (assignment : V → Option β) (u : Noise (β := β) graph)
    (store : V → β) (v : V) :
    written graph assignment u store v =
      surgery assignment (mechanisms graph u) v store := by
  simp only [written, surgery, mechanisms]
  cases assignment v <;> rfl

/-- The value written at one variable by its own lookup table. -/
def writtenLookup (assignment : V → Option β) {v : V}
    (f : ParentFun (β := β) graph v → β) (store : V → β) : β :=
  match assignment v with
  | some a => a
  | none => f (parentFunOf graph store v)

omit [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β] in
lemma written_eq_writtenLookup (assignment : V → Option β) (u : Noise (β := β) graph)
    (store : V → β) (v : V) :
    written graph assignment u store v =
      writtenLookup graph assignment (u v) store := by
  cases assignment v <;> rfl

omit [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β] in
lemma written_congr (assignment : V → Option β) (u : Noise (β := β) graph)
    {store store' : V → β} (v : V)
    (agree : ∀ p : ParentIdx graph v, store p.val = store' p.val) :
    written graph assignment u store v = written graph assignment u store' v := by
  cases hassign : assignment v with
  | some _ => simp [written, hassign]
  | none =>
      simp only [written, hassign]
      apply congrArg (u v)
      funext p
      exact agree p

/-- Evaluate the surgical mechanisms in list order, starting from `seed`. -/
def foldEval (assignment : V → Option β) (u : Noise (β := β) graph) :
    List V → (V → β) → (V → β)
  | [], store => store
  | v :: rest, store =>
      foldEval assignment u rest
        (Function.update store v (written graph assignment u store v))

omit [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β] in
@[simp] lemma foldEval_nil (assignment : V → Option β) (u : Noise (β := β) graph)
    (store : V → β) :
    foldEval graph assignment u [] store = store := rfl

omit [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β] in
@[simp] lemma foldEval_cons (assignment : V → Option β) (u : Noise (β := β) graph)
    (v : V) (rest : List V) (store : V → β) :
    foldEval graph assignment u (v :: rest) store =
      foldEval graph assignment u rest
        (Function.update store v (written graph assignment u store v)) := rfl

omit [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β] in
lemma foldEval_append (assignment : V → Option β) (u : Noise (β := β) graph)
    (pref rest : List V) (seed : V → β) :
    foldEval graph assignment u (pref ++ rest) seed =
      foldEval graph assignment u rest (foldEval graph assignment u pref seed) := by
  induction pref generalizing seed with
  | nil => simp
  | cons v pref ih =>
      simp only [List.cons_append, foldEval_cons]
      exact ih _

omit [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β] in
lemma foldEval_notMem (assignment : V → Option β) (u : Noise (β := β) graph)
    (l : List V) (seed : V → β) (w : V) (hw : w ∉ l) :
    foldEval graph assignment u l seed w = seed w := by
  induction l generalizing seed with
  | nil => rfl
  | cons v rest ih =>
      rw [foldEval_cons]
      have hvw : w ≠ v := fun h => hw (List.mem_cons.2 (Or.inl h))
      have hwrest : w ∉ rest := fun h => hw (List.mem_cons.2 (Or.inr h))
      rw [ih _ hwrest]
      exact Function.update_of_ne hvw _ _

omit [Fintype V] [DecidableEq V] in
lemma getElem_not_mem_drop_succ {l : List V} (hl : l.Nodup) {j : ℕ}
    (hj : j < l.length) : l[j] ∉ l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a t ih =>
      cases j with
      | zero => simpa using (List.nodup_cons.mp hl).1
      | succ j =>
          exact ih (List.nodup_cons.mp hl).2 (by simpa using hj)

omit [Fintype β] [DecidableEq β] [Inhabited β] in
lemma parent_not_mem_suffix (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order) (v : V)
    (p : ParentIdx graph v) :
    p.val ∉ order[order.idxOf v]'(List.idxOf_lt_length_iff.mpr (horder.2.1 v)) ::
      order.drop (order.idxOf v + 1) := by
  intro hmem
  have hi : order.idxOf v < order.length :=
    List.idxOf_lt_length_iff.mpr (horder.2.1 v)
  have hj : order.idxOf p.val < order.length :=
    List.idxOf_lt_length_iff.mpr (horder.2.1 p.val)
  have hlt : order.idxOf p.val < order.idxOf v :=
    idxOf_parent_lt graph acyclic order horder p
  have hnot : order[order.idxOf p.val] ∉ order.drop (order.idxOf p.val + 1) :=
    getElem_not_mem_drop_succ horder.1 hj
  rw [List.mem_cons] at hmem
  cases hmem with
  | inl hhead =>
      have hv : order[order.idxOf v] = v := List.getElem_idxOf hi
      have hp : p.val = v := hhead.trans hv
      have hidx : order.idxOf p.val = order.idxOf v := congrArg order.idxOf hp
      omega
  | inr htail =>
      have hsub :
          order.drop (order.idxOf v + 1) =
            (order.drop (order.idxOf p.val + 1)).drop
              (order.idxOf v - order.idxOf p.val) := by
        rw [List.drop_drop]
        congr 1
        omega
      have hmemDrop : p.val ∈ order.drop (order.idxOf p.val + 1) := by
        rw [hsub] at htail
        exact List.mem_of_mem_drop htail
      exact hnot ((List.getElem_idxOf hj).symm ▸ hmemDrop)

omit [Fintype β] [DecidableEq β] [Inhabited β] in
/-- Folding a topological order solves the surgical mechanisms. -/
theorem foldEval_pointwise (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (assignment : V → Option β) (u : Noise (β := β) graph) (seed : V → β) (v : V) :
    foldEval graph assignment u order seed v =
      written graph assignment u (foldEval graph assignment u order seed) v := by
  set σ := foldEval graph assignment u order seed
  have hv : v ∈ order := horder.2.1 v
  have hi : order.idxOf v < order.length := List.idxOf_lt_length_iff.mpr hv
  set i := order.idxOf v
  have hget : order[i] = v := List.getElem_idxOf hi
  set pref := order.take i
  set rest := order.drop (i + 1)
  have hcat : pref ++ order[i] :: rest = order := by
    have hdrop : order.drop i = order[i] :: rest := by
      simp [rest]
    simpa [pref, hdrop] using List.take_append_drop i order
  have happ :
      foldEval graph assignment u order seed =
        foldEval graph assignment u (order[i] :: rest)
          (foldEval graph assignment u pref seed) :=
    (congrArg (fun l => foldEval graph assignment u l seed) hcat.symm).trans
      (foldEval_append graph assignment u pref (order[i] :: rest) seed)
  have hvrest : v ∉ rest := by
    simpa [rest, hget] using getElem_not_mem_drop_succ (l := order) horder.1 hi
  have hwrite :
      foldEval graph assignment u (order[i] :: rest)
          (foldEval graph assignment u pref seed) v =
        written graph assignment u (foldEval graph assignment u pref seed) v := by
    rw [hget, foldEval_cons, foldEval_notMem graph assignment u rest _ v hvrest]
    exact Function.update_self _ _ _
  have hparents : ∀ p : ParentIdx graph v,
      foldEval graph assignment u pref seed p.val = σ p.val := by
    intro p
    have hpnot : p.val ∉ order[i] :: rest := by
      simpa [i, rest] using parent_not_mem_suffix graph acyclic order horder v p
    have hval :=
      foldEval_notMem graph assignment u (order[i] :: rest)
        (foldEval graph assignment u pref seed) p.val hpnot
    rw [← happ] at hval
    exact hval.symm
  have hwritten :=
    written_congr graph assignment u (v := v) hparents
  have hstep :
      foldEval graph assignment u order seed v = written graph assignment u σ v := by
    rw [happ]
    exact hwrite.trans hwritten
  simpa [σ] using hstep

omit [Fintype β] [DecidableEq β] [Inhabited β] in
/-- **The folded store is a solution of the surgical model.** -/
theorem foldEval_isSolution (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (assignment : V → Option β) (u : Noise (β := β) graph) (seed : V → β) :
    IsSolution (surgery assignment (mechanisms graph u))
      (foldEval graph assignment u order seed) := by
  intro v
  rw [foldEval_pointwise graph acyclic order horder assignment u seed v]
  exact written_eq_surgery graph assignment u _ v

omit [Fintype β] [DecidableEq β] [Inhabited β] in
/-- **Surgery on a topologically ranked noise sample has one solution.** -/
theorem surgicalModel_exists_unique_solution (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (assignment : V → Option β) (u : Noise (β := β) graph) (seed : V → β) :
    ∃! store, IsSolution (surgery assignment (mechanisms graph u)) store :=
  surgery_exists_unique_solution
    (recursiveOfTopologicalOrder graph acyclic order horder u) assignment seed

omit [Fintype β] [DecidableEq β] [Inhabited β] in
/-- Any two seeds fold to the same store: it is the unique solution. -/
theorem foldEval_seed_indep (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (assignment : V → Option β) (u : Noise (β := β) graph) (seed seed' : V → β) :
    foldEval graph assignment u order seed =
      foldEval graph assignment u order seed' :=
  solution_unique
    (recursive_surgery
      (recursiveOfTopologicalOrder graph acyclic order horder u) assignment)
    (foldEval_isSolution graph acyclic order horder assignment u seed)
    (foldEval_isSolution graph acyclic order horder assignment u seed')

omit [Fintype β] [DecidableEq β] [Inhabited β] in
/-- The folded store is the solution characterized by the surgical fixed point. -/
theorem foldEval_eq_iff (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (assignment : V → Option β) (u : Noise (β := β) graph) (seed : V → β) (x : V → β) :
    foldEval graph assignment u order seed = x ↔
      ∀ v, x v = written graph assignment u x v := by
  constructor
  · intro h v
    rw [← h]
    exact foldEval_pointwise graph acyclic order horder assignment u seed v
  · intro hall
    have hsol : IsSolution (surgery assignment (mechanisms graph u)) x := by
      intro v
      rw [hall v]
      exact written_eq_surgery graph assignment u x v
    exact solution_unique
      (recursive_surgery
        (recursiveOfTopologicalOrder graph acyclic order horder u) assignment)
      (foldEval_isSolution graph acyclic order horder assignment u seed) hsol

/-! ## Noise law and the pushforward -/

private lemma pmf_fintype_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a : ℝ≥0∞) = 1 :=
  BayesianNetwork.DiscreteCPT.pmf_sum_eq_one p

/-- Weight of one lookup table: the product of the conditional table over rows. -/
noncomputable def localWeight (cpt : (network (β := β) graph acyclic).DiscreteCPT) (v : V)
    (f : ParentFun (β := β) graph v → β) : ℝ≥0∞ :=
  ∏ pa : ParentFun (β := β) graph v, cptAt graph acyclic cpt v pa (f pa)

/-- Weight of a noise sample: the product of the lookup-table weights. -/
noncomputable def noiseWeight (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (u : Noise (β := β) graph) : ℝ≥0∞ :=
  ∏ v, localWeight graph acyclic cpt v (u v)

private lemma sum_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (g : ∀ i, κ i → ℝ≥0∞) :
    ∑ f : (∀ i, κ i), ∏ i, g i (f i) = ∏ i, ∑ b, g i b := by
  simpa using
    (Finset.prod_univ_sum (t := fun i => (Finset.univ : Finset (κ i))) g).symm

omit [Inhabited β] in
private lemma localWeight_sum_eq_one (cpt : (network (β := β) graph acyclic).DiscreteCPT) (v : V) :
    ∑ f : ParentFun (β := β) graph v → β, localWeight graph acyclic cpt v f = 1 := by
  unfold localWeight
  rw [sum_prod_pi (g := fun pa b => cptAt graph acyclic cpt v pa b)]
  refine Finset.prod_eq_one fun pa _ => ?_
  exact pmf_fintype_sum (cpt.cpt v (toParentAssignment graph acyclic v pa))

omit [Inhabited β] in
private lemma noiseWeight_sum_eq_one (cpt : (network (β := β) graph acyclic).DiscreteCPT) :
    ∑ u : Noise (β := β) graph, noiseWeight graph acyclic cpt u = 1 := by
  unfold noiseWeight
  rw [sum_prod_pi (g := fun v f => localWeight graph acyclic cpt v f)]
  refine Finset.prod_eq_one fun v _ => ?_
  exact localWeight_sum_eq_one graph acyclic cpt v

/-- The law of the independent exogenous noise. -/
noncomputable def noisePMF (cpt : (network (β := β) graph acyclic).DiscreteCPT) : PMF (Noise (β := β) graph) :=
  PMF.ofFintype (noiseWeight graph acyclic cpt) (noiseWeight_sum_eq_one graph acyclic cpt)

/-- Law of the surgical solution. The fold seed is overwritten at every variable. -/
noncomputable def surgeryPMF (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (order : List V) : PMF (V → β) :=
  (noisePMF graph acyclic cpt).map
    (fun u => foldEval graph assignment u order (fun _ => default))

private lemma sum_prod_fix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (g : ι → γ → ℝ≥0∞) (j : ι) (b : γ) :
    ∑ f : ι → γ, (∏ i, g i (f i)) * (if f j = b then (1 : ℝ≥0∞) else 0) =
      g j b * ∏ i ∈ Finset.univ.erase j, ∑ c, g i c := by
  classical
  have hmul : ∀ f : ι → γ,
      (∏ i, g i (f i)) * (if f j = b then 1 else 0) =
        if f j = b then ∏ i, g i (f i) else 0 := by
    intro f
    by_cases h : f j = b <;> simp [h]
  simp_rw [hmul, ← Finset.sum_filter]
  let t : ι → Finset γ := Function.update (fun _ => (Finset.univ : Finset γ)) j {b}
  have ht_sum : ∀ i, ∑ c ∈ t i, g i c =
      if i = j then g j b else ∑ c, g i c := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [t, Function.update_self, Finset.sum_singleton]
    · rw [show t i = Finset.univ from by simp [t, Function.update_of_ne hij]]
      simp [hij]
  have hfilter :
      (Finset.univ.filter fun f : ι → γ => f j = b) = Fintype.piFinset t := by
    have h :=
      Fintype.piFinset_update_singleton_eq_filter_piFinset_eq
        (s := fun _ : ι => (Finset.univ : Finset γ)) j (a := b) (Finset.mem_univ b)
    simpa [t] using h.symm
  have hprod := Finset.prod_univ_sum (t := t) g
  rw [hfilter]
  rw [← hprod]
  simp_rw [ht_sum]
  have hsplit :
      (∏ i, if i = j then g j b else ∑ c, g i c) =
        g j b * ∏ i ∈ Finset.univ.erase j, ∑ c, g i c := by
    rw [← Finset.mul_prod_erase Finset.univ
        (fun i => if i = j then g j b else ∑ c, g i c) (Finset.mem_univ j)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun i hi => ?_
      simp [(Finset.mem_erase.mp hi).1]
  exact hsplit

omit [Inhabited β] in
private lemma constrained_local_sum (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (x : V → β) (v : V) :
    ∑ f : ParentFun (β := β) graph v → β,
        localWeight graph acyclic cpt v f *
          (if x v = writtenLookup graph assignment f x then (1 : ℝ≥0∞) else 0) =
      truncatedFactor graph acyclic cpt assignment x v := by
  cases hassign : assignment v with
  | some a =>
      have hwritten : ∀ f : ParentFun (β := β) graph v → β,
          writtenLookup graph assignment f x = a := by
        intro f
        simp [writtenLookup, hassign]
      simp_rw [hwritten]
      have hconst : ∀ f : ParentFun (β := β) graph v → β,
          localWeight graph acyclic cpt v f * (if x v = a then 1 else 0) =
            (if x v = a then 1 else 0) * localWeight graph acyclic cpt v f := by
        intro _
        rw [mul_comm]
      simp_rw [hconst, ← Finset.mul_sum, localWeight_sum_eq_one graph acyclic cpt v, mul_one]
      simp [truncatedFactor, hassign]
  | none =>
      unfold localWeight
      have hwritten : ∀ f : ParentFun (β := β) graph v → β,
          (x v = writtenLookup graph assignment f x) ↔
            f (parentFunOf graph x v) = x v := by
        intro f
        simp only [writtenLookup, hassign]
        exact Iff.intro Eq.symm Eq.symm
      simp_rw [hwritten]
      rw [sum_prod_fix (g := fun pa b => cptAt graph acyclic cpt v pa b)
          (parentFunOf graph x v) (x v)]
      have htail :
          (∏ pa ∈ Finset.univ.erase (parentFunOf graph x v),
              ∑ c, cptAt graph acyclic cpt v pa c) = 1 := by
        refine Finset.prod_eq_one fun pa _ => ?_
        exact pmf_fintype_sum (cpt.cpt v (toParentAssignment graph acyclic v pa))
      rw [htail, mul_one]
      simp [truncatedFactor, hassign]

private lemma cylinder_sum_eq_truncated
    (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order) (x : V → β) :
    ∑ u : Noise (β := β) graph,
        noiseWeight graph acyclic cpt u *
          (if foldEval graph assignment u order (fun _ => default) = x then
            (1 : ℝ≥0∞) else 0) =
      truncatedWeight graph acyclic cpt assignment x := by
  classical
  have hindicator : ∀ u : Noise (β := β) graph,
      (if foldEval graph assignment u order (fun _ => default) = x then (1 : ℝ≥0∞) else 0) =
        ∏ v, if x v = written graph assignment u x v then 1 else 0 := by
    intro u
    if h : foldEval graph assignment u order (fun _ => default) = x then
      have hall : ∀ v, x v = written graph assignment u x v :=
        (foldEval_eq_iff graph acyclic order horder assignment u _ x).1 h
      simp [h, hall, Finset.prod_const_one]
    else
      have hn : ¬ ∀ v, x v = written graph assignment u x v :=
        fun hall => h ((foldEval_eq_iff graph acyclic order horder assignment u _ x).2 hall)
      have hex : ∃ v, x v ≠ written graph assignment u x v := by
        push Not at hn
        exact hn
      obtain ⟨v, hv⟩ := hex
      have hprod :
          (∏ w, if x w = written graph assignment u x w then (1 : ℝ≥0∞) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])
      simp [h, hprod]
  simp_rw [hindicator]
  have hlookup : ∀ (u : Noise (β := β) graph) (v : V),
      written graph assignment u x v = writtenLookup graph assignment (u v) x :=
    fun u v => written_eq_writtenLookup graph assignment u x v
  simp_rw [hlookup, noiseWeight, ← Finset.prod_mul_distrib]
  rw [sum_prod_pi (g := fun v f =>
      localWeight graph acyclic cpt v f *
        (if x v = writtenLookup graph assignment f x then (1 : ℝ≥0∞) else 0))]
  unfold truncatedWeight
  refine Finset.prod_congr rfl fun v _ => ?_
  exact constrained_local_sum graph acyclic cpt assignment x v

/-- **Surgery and the truncated factorization agree.**

The mass `surgeryPMF` places on `x` is the g-formula weight of `x`. -/
theorem surgeryPMF_apply_eq_truncatedWeight
    (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order) (x : V → β) :
    surgeryPMF graph acyclic cpt assignment order x =
      truncatedWeight graph acyclic cpt assignment x := by
  classical
  unfold surgeryPMF noisePMF
  rw [PMF.map_apply]
  have hcoe : ∀ a,
      PMF.ofFintype (noiseWeight graph acyclic cpt)
          (noiseWeight_sum_eq_one graph acyclic cpt) a =
        noiseWeight graph acyclic cpt a :=
    fun a => PMF.ofFintype_apply (noiseWeight_sum_eq_one graph acyclic cpt) a
  simp_rw [hcoe]
  rw [tsum_eq_sum (s := Finset.univ) (fun u hu => (hu (Finset.mem_univ u)).elim)]
  have hswap : ∀ u,
      (if x = foldEval graph assignment u order (fun _ => default) then
          noiseWeight graph acyclic cpt u else 0) =
        noiseWeight graph acyclic cpt u *
          (if foldEval graph assignment u order (fun _ => default) = x then 1 else 0) := by
    intro u
    if h : foldEval graph assignment u order (fun _ => default) = x then
      simp [h]
    else
      have h' : x ≠ foldEval graph assignment u order (fun _ => default) := fun heq => h heq.symm
      simp [h, h']
  simp_rw [hswap]
  exact cylinder_sum_eq_truncated graph acyclic cpt assignment order horder x

/-- The interventional law does not depend on which topological order ranks the mechanisms. -/
theorem surgeryPMF_order_indep
    (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (order order' : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (horder' : (network (β := β) graph acyclic).IsTopologicalOrder order') (x : V → β) :
    surgeryPMF graph acyclic cpt assignment order x =
      surgeryPMF graph acyclic cpt assignment order' x := by
  rw [surgeryPMF_apply_eq_truncatedWeight graph acyclic cpt assignment order horder,
    surgeryPMF_apply_eq_truncatedWeight graph acyclic cpt assignment order' horder']

/-- **The g-formula is a probability.** Summing the truncated weights gives `1`. -/
theorem truncatedWeight_sum_eq_one
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (assignment : V → Option β) :
    ∑ x : V → β, truncatedWeight graph acyclic cpt assignment x = 1 := by
  obtain ⟨order, horder⟩ := (network (β := β) graph acyclic).exists_topological_order
  have hs := pmf_fintype_sum (surgeryPMF graph acyclic cpt assignment order)
  simp_rw [surgeryPMF_apply_eq_truncatedWeight graph acyclic cpt assignment order horder] at hs
  exact hs

/-- With nothing set, surgery reproduces the Bayesian-network joint. -/
theorem surgeryPMF_none_eq_jointWeight
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order) (x : V → β) :
    surgeryPMF graph acyclic cpt (fun _ => none) order x = cpt.jointWeight x := by
  rw [surgeryPMF_apply_eq_truncatedWeight graph acyclic cpt (fun _ => none) order horder]
  exact truncatedWeight_none_eq_jointWeight graph acyclic cpt x

end Mettapedia.GSLT.Causality.DoCalculus
