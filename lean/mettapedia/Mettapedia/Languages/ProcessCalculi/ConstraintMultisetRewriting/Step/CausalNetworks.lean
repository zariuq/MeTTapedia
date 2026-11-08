import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalCells
import Mettapedia.GSLT.Causality.DoCalculus.TruncatedFactorization

/-!
# A causal Bayesian network as a cell system

The variable gadget of a causal Bayesian network on a finite acyclic graph with one finite
alphabet `β` (the setting of `DoCalculus.TruncatedFactorization`).

* **An event** `⟨v, (row, r, b)⟩`: the variable `v` read the row `row` of its parents' values and
  the regime `r` of its mechanism, and made the value `b` (`Event`).
* **A cell** `⟨v, (row, r)⟩` races over the value (`Cell`). It is enabled at a configuration when
  `v` has not fired, every parent `p` has fired with the value `row p` (a join on the parents'
  rows), and `r` is the regime installed at `v` (`cells`).
* **The weights** are a table `table : Event → ℝ`, for instance the conditional probability table.

A cell of a variable with several parents is enabled by several earlier events: the dependent case
of the race identity. The history of an assignment `x` (`historyOf`) fires every variable once,
with the row of `x` (`isHistory`), and a topological order linearizes it (`reach`). So its
likelihood under the jump chain, summed over its linearizations, is the product over the
variables of the table's weight over the row's total (`likelihood`).

## The network and its interventions

With one regime (`Unit`) and the conditional probability table as weights (`cptWeight`):
* **the history likelihood is the Bayesian-network joint** `DiscreteCPT.jointWeight`
  (`likelihood_eq_jointWeight`), defined independently of the step;
* **a do as a restriction of weights** (`doWeight`, the cell form of R103's
  `Intervention.restrictWeight`: an event of a set variable keeps its weight when it makes the set
  value, and weighs `0` otherwise) gives Grok's truncated factorization `truncatedWeight`
  (`likelihood_doWeight`), when the set values have positive probability on the history's rows.
  A restriction never overrides, so where a set value has probability `0` the race at that
  variable starves (`StepBridge.restriction_starves`); the regime atom of `StepBridge` overrides
  instead.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalNetworks

open CausalCells
open Mettapedia.GSLT.Causality.DoCalculus
open Mettapedia.ProbabilityTheory.BayesianNetworks
open scoped ENNReal

variable {V β : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype β] [DecidableEq β] [MeasurableSpace β]
variable (graph : DirectedGraph V)
variable (acyclic : graph.IsAcyclic)
variable [DecidableRel graph.edges]
variable {R : Type} [Fintype R] [DecidableEq R]

/-- **An event**: a variable, the row of its parents' values it read, the regime it read, and the
value it made. -/
abbrev Event := Σ v : V, ParentFun (β := β) graph v × R × β

/-- **A cell**: a variable, a row and a regime. Its events race over the value. -/
abbrev Cell := Σ v : V, ParentFun (β := β) graph v × R

local notation "Ev" => Event (β := β) (R := R) graph
local notation "Cl" => Cell (β := β) (R := R) graph

/-- **The network's cell system**, with the regime installed at each variable and a table of
weights. -/
def cells (regime : V → R) (table : Ev → ℝ) : CellSystem Ev Cl where
  cell e := ⟨e.1, (e.2.1, e.2.2.1)⟩
  members c := Finset.univ.image fun b : β => (⟨c.1, (c.2.1, c.2.2, b)⟩ : Ev)
  cell_of_mem := by
    intro e c member
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp member
    rfl
  weight := table
  enabled y := Finset.univ.filter fun c : Cl =>
    (∀ e ∈ y, e.1 ≠ c.1) ∧ (∀ p : ParentIdx graph c.1, ∃ e ∈ y, e.1 = p.1 ∧ e.2.2.2 = c.2.1 p) ∧
      c.2.2 = regime c.1

/-- The event of variable `v` in the history of `x`. -/
def assignmentEvent (regime : V → R) (x : V → β) (v : V) : Ev :=
  ⟨v, (parentFunOf graph x v, regime v, x v)⟩

/-- **The history of an assignment**: every variable fires once, with the row of `x`. -/
def historyOf (regime : V → R) (x : V → β) : Finset Ev :=
  Finset.univ.image (assignmentEvent graph regime x)

variable {graph}

omit [MeasurableSpace β] in
theorem mem_enabled {regime : V → R} {table : Ev → ℝ} {y : Finset Ev} {c : Cl} :
    c ∈ (cells graph regime table).enabled y ↔
      (∀ e ∈ y, e.1 ≠ c.1) ∧ (∀ p : ParentIdx graph c.1, ∃ e ∈ y, e.1 = p.1 ∧ e.2.2.2 = c.2.1 p) ∧
        c.2.2 = regime c.1 := by
  show c ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

omit [Fintype β] [MeasurableSpace β] [Fintype R] in
theorem mem_historyOf {regime : V → R} {x : V → β} {e : Ev} :
    e ∈ historyOf graph regime x ↔ e = assignmentEvent graph regime x e.1 := by
  constructor
  · intro member
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp member
    rfl
  · intro same
    rw [same]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

omit [DecidableEq V] [Fintype β] [DecidableEq β] [MeasurableSpace β] [Fintype R]
  [DecidableEq R] in
theorem assignmentEvent_injective (regime : V → R) (x : V → β) :
    Function.Injective (assignmentEvent graph regime x) :=
  fun _ _ same => congrArg Sigma.fst same

omit [MeasurableSpace β] in
theorem cellTotal_eq (regime : V → R) (table : Ev → ℝ) (c : Cl) :
    (cells graph regime table).cellTotal c = ∑ b, table ⟨c.1, (c.2.1, c.2.2, b)⟩ := by
  unfold CellSystem.cellTotal
  show ∑ e ∈ Finset.univ.image (fun b : β => (⟨c.1, (c.2.1, c.2.2, b)⟩ : Ev)), table e = _
  rw [Finset.sum_image (fun b _ b' _ same => by simpa using same)]

omit [MeasurableSpace β] in
/-- Along the history of `x`, an enabled cell has the row of `x` and the installed regime. -/
theorem enabled_eq (regime : V → R) (table : Ev → ℝ) (x : V → β) {y : Finset Ev}
    (sub : y ⊆ historyOf graph regime x) {c : Cl} (enabled : c ∈ (cells graph regime table).enabled y) :
    c = ⟨c.1, (parentFunOf graph x c.1, regime c.1)⟩ := by
  obtain ⟨_, rows, installed⟩ := mem_enabled.mp enabled
  rcases c with ⟨v, row, r⟩
  simp only at rows installed
  subst installed
  have sameRow : row = parentFunOf graph x v := by
    funext p
    obtain ⟨e, inY, var, value⟩ := rows p
    have shape := mem_historyOf.mp (sub inY)
    have made : e.2.2.2 = x e.1 := congrArg (fun e : Ev => e.2.2.2) shape
    rw [← value, made, var]
    rfl
  subst sameRow
  rfl

omit [MeasurableSpace β] in
/-- **The history of an assignment is conflict-free, maximal, persistent and positive.** -/
theorem isHistory (regime : V → R) (table : Ev → ℝ) (x : V → β)
    (positive : ∀ v, 0 < (cells graph regime table).cellTotal ⟨v, (parentFunOf graph x v, regime v)⟩) :
    (cells graph regime table).History (historyOf graph regime x) where
  conflictFree := by
    intro e inX e' inX' same
    have first : e.1 = e'.1 := by
      have cells := congrArg Sigma.fst same
      exact cells
    rw [mem_historyOf.mp inX, mem_historyOf.mp inX', first]
  maximal := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro c enabled
    obtain ⟨unfired, _, _⟩ := mem_enabled.mp enabled
    exact unfired (assignmentEvent graph regime x c.1)
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)) rfl
  persistent := by
    intro y sub c e enabled _ inX _ different
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp inX
    have shape := enabled_eq regime table x sub enabled
    rw [mem_enabled] at enabled ⊢
    obtain ⟨unfired, rows, installed⟩ := enabled
    refine ⟨?_, fun p => ?_, installed⟩
    · intro e' member
      rcases Finset.mem_insert.mp member with rfl | inY
      · intro same
        apply different
        rw [shape]
        change (⟨w, (parentFunOf graph x w, regime w)⟩ : Cl) =
          ⟨c.1, (parentFunOf graph x c.1, regime c.1)⟩
        rw [show w = c.1 from same]
      · exact unfired e' inY
    · obtain ⟨e', inY, h1, h2⟩ := rows p
      exact ⟨e', Finset.mem_insert_of_mem inY, h1, h2⟩
  positive := by
    intro y sub c enabled
    rw [enabled_eq regime table x sub enabled]
    exact positive c.1

/-- **A topological order linearizes the history of every assignment.** -/
theorem reach (regime : V → R) (table : Ev → ℝ) (x : V → β) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order) :
    (cells graph regime table).Reach (historyOf graph regime x) ∅ := by
  let ev := assignmentEvent graph regime x
  have claim : ∀ (suf pre : List V), pre ++ suf = order →
      (cells graph regime table).IsLin (historyOf graph regime x) (pre.toFinset.image ev)
        (suf.map ev) := by
    intro suf
    induction suf with
    | nil =>
        intro pre whole
        rw [List.append_nil] at whole
        subst whole
        have all : pre.toFinset = Finset.univ :=
          Finset.eq_univ_iff_forall.mpr fun v => List.mem_toFinset.mpr (horder.2.1 v)
        rw [all, List.map_nil]
        exact CellSystem.IsLin.nil
    | cons v suf ih =>
        intro pre whole
        have nodup : (pre ++ v :: suf).Nodup := whole ▸ horder.1
        have notPre : v ∉ pre := fun inPre =>
          List.disjoint_of_nodup_append nodup inPre (List.mem_cons_self)
        have fresh : ev v ∉ pre.toFinset.image ev := by
          intro member
          obtain ⟨w, inPre, same⟩ := Finset.mem_image.mp member
          have : w = v := congrArg Sigma.fst same
          exact notPre (this ▸ List.mem_toFinset.mp inPre)
        have cand : ev v ∈ (cells graph regime table).candidates (pre.toFinset.image ev) := by
          rw [CellSystem.mem_candidates]
          refine ⟨mem_enabled.mpr ⟨?_, fun p => ?_, rfl⟩, ?_⟩
          · intro e member
            obtain ⟨w, inPre, rfl⟩ := Finset.mem_image.mp member
            intro same
            have same' : w = v := same
            exact notPre (same' ▸ List.mem_toFinset.mp inPre)
          · refine ⟨ev p.1, Finset.mem_image_of_mem _ (List.mem_toFinset.mpr ?_), rfl, rfl⟩
            by_contra outside
            have below := idxOf_parent_lt (β := β) graph acyclic order horder p
            change order.idxOf p.1 < order.idxOf v at below
            rw [← whole, List.idxOf_append_of_notMem notPre, List.idxOf_cons_self,
              List.idxOf_append_of_notMem outside] at below
            omega
          · exact Finset.mem_image.mpr ⟨x v, Finset.mem_univ _, rfl⟩
        refine CellSystem.IsLin.cons cand fresh ?_
        have grown : insert (ev v) (pre.toFinset.image ev) = (pre ++ [v]).toFinset.image ev := by
          rw [← Finset.image_insert]
          congr 1
          ext w
          simp
        rw [grown]
        exact ih (pre ++ [v]) (by rw [List.append_assoc]; exact whole)
  have start := claim order [] rfl
  simp only [List.toFinset_nil, Finset.image_empty] at start
  exact ⟨_, start⟩

/-- **The history likelihood of an assignment**: the product over the variables of the table's
weight over the row's total. -/
theorem likelihood (regime : V → R) (table : Ev → ℝ) (x : V → β) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (positive : ∀ v, 0 < ∑ b, table ⟨v, (parentFunOf graph x v, regime v, b)⟩) :
    ∑ l ∈ (cells graph regime table).lins (historyOf graph regime x) ∅,
        (cells graph regime table).pathProb ∅ l =
      ∏ v, table (assignmentEvent graph regime x v) /
        ∑ b, table ⟨v, (parentFunOf graph x v, regime v, b)⟩ := by
  have positive' : ∀ v, 0 < (cells graph regime table).cellTotal
      ⟨v, (parentFunOf graph x v, regime v)⟩ := fun v => by
    rw [cellTotal_eq]
    exact positive v
  rw [(isHistory regime table x positive').race_identity
    (reach acyclic regime table x order horder), historyOf,
    Finset.prod_image (fun v _ w _ same => assignmentEvent_injective regime x same)]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [cellTotal_eq]
  rfl

/-! ## The network and its interventions -/

variable (graph)

/-- **The conditional probability table as weights**: an event weighs the probability its row
gives its value. -/
def cptWeight (cpt : (network (β := β) graph acyclic).DiscreteCPT) (e : Event (β := β) (R := Unit) graph) :
    ℝ :=
  (cptAt graph acyclic cpt e.1 e.2.1 e.2.2.2).toReal

/-- **A do as a restriction of weights**: an event of a set variable keeps its weight when it makes
the set value and weighs `0` otherwise; the other events keep their weights. -/
def doWeight (cpt : (network (β := β) graph acyclic).DiscreteCPT) (assignment : V → Option β)
    (e : Event (β := β) (R := Unit) graph) : ℝ :=
  match assignment e.1 with
  | none => cptWeight graph acyclic cpt e
  | some a => if e.2.2.2 = a then cptWeight graph acyclic cpt e else 0

/-- The single regime of the unintervened network. -/
abbrev plain : V → Unit := fun _ => ()

variable {graph}

omit [DecidableEq V] [DecidableEq β] in
theorem sum_cptAt (cpt : (network (β := β) graph acyclic).DiscreteCPT) (v : V)
    (row : ParentFun (β := β) graph v) :
    ∑ b, (cptAt graph acyclic cpt v row b).toReal = 1 := by
  have finite : ∀ b ∈ (Finset.univ : Finset β), cptAt graph acyclic cpt v row b ≠ ∞ :=
    fun b _ => PMF.apply_ne_top _ _
  rw [← ENNReal.toReal_sum finite]
  unfold cptAt
  rw [BayesianNetwork.DiscreteCPT.pmf_sum_eq_one, ENNReal.toReal_one]

/-- **Under a do, the history likelihood is the truncated factorization**, when every set value
has positive probability on the history's rows. -/
theorem likelihood_doWeight (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (x : V → β) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (setPositive : ∀ v a, assignment v = some a →
      0 < (cptAt graph acyclic cpt v (parentFunOf graph x v) a).toReal) :
    ∑ l ∈ (cells graph (plain) (doWeight graph acyclic cpt assignment)).lins
          (historyOf graph (plain) x) ∅,
        (cells graph (plain) (doWeight graph acyclic cpt assignment)).pathProb ∅ l =
      (truncatedWeight graph acyclic cpt assignment x).toReal := by
  have rowTotal : ∀ v, ∑ b, doWeight graph acyclic cpt assignment
      ⟨v, (parentFunOf graph x v, plain v, b)⟩ =
        match assignment v with
        | none => 1
        | some a => (cptAt graph acyclic cpt v (parentFunOf graph x v) a).toReal := by
    intro v
    cases set : assignment v with
    | none =>
        simp only [doWeight, set]
        exact sum_cptAt acyclic cpt v _
    | some a =>
        simp only [doWeight, set, cptWeight]
        simp
  rw [likelihood acyclic _ _ x order horder]
  · unfold truncatedWeight
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [rowTotal v]
    unfold truncatedFactor
    cases set : assignment v with
    | none =>
        simp only [doWeight, assignmentEvent, set, cptWeight, div_one]
    | some a =>
        simp only [doWeight, assignmentEvent, set, cptWeight]
        by_cases same : x v = a
        · subst same
          simp [div_self (setPositive v _ set).ne']
        · simp [same]
  · intro v
    rw [rowTotal v]
    cases set : assignment v with
    | none => exact one_pos
    | some a => exact setPositive v a set

/-- **The history likelihood is the Bayesian-network joint.** -/
theorem likelihood_eq_jointWeight (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (x : V → β) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order) :
    ∑ l ∈ (cells graph (plain) (doWeight graph acyclic cpt fun _ => none)).lins
          (historyOf graph (plain) x) ∅,
        (cells graph (plain) (doWeight graph acyclic cpt fun _ => none)).pathProb ∅ l =
      (cpt.jointWeight x).toReal := by
  rw [likelihood_doWeight acyclic cpt _ x order horder (fun _ _ unset => by simp at unset),
    truncatedWeight_none_eq_jointWeight]

#print axioms cellTotal_eq
#print axioms enabled_eq
#print axioms isHistory
#print axioms reach
#print axioms likelihood
#print axioms sum_cptAt
#print axioms likelihood_doWeight
#print axioms likelihood_eq_jointWeight

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalNetworks

end
