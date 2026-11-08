import Mettapedia.GSLT.Causality.StepBridge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceHistories

/-!
# Counterfactual replay on the step

A run of the network program records, entry by entry (`Race.Entry.ofFiring`), the pending atom
each firing took and the value it made. Along a linearization of the history of `x`, the entry of
the firing of `v` made `(val v (x v))`, and every variable has one (`record_made`,
`record_covers`): **the record reads off the assignment, and with it the exogenous noise on the
rows the run visited** (Grok's `Noise`: one lookup table per variable).

## Replay

**Replaying a noise sample** `u` under an intervention fires, at each cell, the value the surgical
mechanism writes on its row (`replayTable`, the row form of Grok's `written`). On the step:
* **the replay's history likelihood is the indicator of Grok's folded store**
  `foldEval assignment u order seed` (`replay_likelihood`), the unique solution of the surgical
  model, for every topological order;
* **abduction is exact on the record** (`extends_record_iff`): a noise sample replays the recorded
  history without intervention exactly when it agrees with the record on the rows the run visited;
* **averaged over Grok's noise law, replay under a do is the do** (`replay_average`): the step's
  truncated factorization, by `surgeryPMF_apply_eq_truncatedWeight`;
* **Pearl's three steps** (`counterfactual_total`): weight each noise sample by the likelihood that
  it replays the recorded history (abduction), replay it under the do (action), read the store
  (prediction). Summed over the predicted stores, the weights give back the step's likelihood of
  the record, its Bayesian-network joint.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalReplay

open CausalCells CausalNetworks CausalNetworksStep
open Mettapedia.GSLT.Causality.StepBridge (stepLikelihood stepLikelihood_eq)
open Mettapedia.GSLT.Causality.DoCalculus
open Mettapedia.ProbabilityTheory.BayesianNetworks
open scoped ENNReal

universe uS

variable {V β : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
variable (graph : DirectedGraph V)
variable (acyclic : graph.IsAcyclic)
variable [DecidableRel graph.edges]
variable {S : Type uS}

/-! ## The record of a run -/

section Record

variable {E : Type*} {C : Type*} [DecidableEq E] {K : CellSystem E C}

theorem IsLin.mem {X x : Finset E} {l : List E} (lin : K.IsLin X x l) {e : E} (member : e ∈ l) :
    e ∈ X := by
  induction lin with
  | nil => simp at member
  | cons _ _ rest ih =>
      rcases List.mem_cons.mp member with rfl | inside
      · exact rest.subset (Finset.mem_insert_self _ _)
      · exact ih inside

theorem IsLin.covers {X x : Finset E} {l : List E} (lin : K.IsLin X x l) {e : E} (member : e ∈ X) :
    e ∈ x ∨ e ∈ l := by
  induction lin with
  | nil => exact Or.inl member
  | @cons x e' l _ _ _ ih =>
      rcases ih with inside | inside
      · rcases Finset.mem_insert.mp inside with rfl | old
        · exact Or.inr List.mem_cons_self
        · exact Or.inl old
      · exact Or.inr (List.mem_cons_of_mem _ inside)

end Record

local notation "Ev" => Event (β := β) (R := Unit) graph

omit [Inhabited β] [MeasurableSpace β] in
/-- **The record of a linearization reads off the assignment**: the entry of each firing made the
value of its variable in `x`. -/
theorem record_made (table : Ev → ℝ) (x : V → β) {l : List Ev}
    (member : l ∈ (cells graph plain table).lins (historyOf graph plain x) ∅) {e : Ev}
    (inL : e ∈ l) :
    (Race.Entry.ofFiring (firing (S := S) graph e)).made = [Atom.val e.1 (x e.1)] := by
  have inX := IsLin.mem (((cells graph plain table).mem_lins _ _ l).mp member) inL
  rw [mem_historyOf.mp inX]
  rfl

omit [Inhabited β] [MeasurableSpace β] in
/-- **Every variable has an entry in the record.** -/
theorem record_covers (table : Ev → ℝ) (x : V → β) {l : List Ev}
    (member : l ∈ (cells graph plain table).lins (historyOf graph plain x) ∅) (v : V) :
    ∃ e ∈ l, e.1 = v := by
  have lin := ((cells graph plain table).mem_lins _ _ l).mp member
  rcases IsLin.covers lin (Finset.mem_image_of_mem (assignmentEvent graph plain x)
    (Finset.mem_univ v)) with empty | inL
  · simp at empty
  · exact ⟨_, inL, rfl⟩

/-! ## Replay -/

/-- The value the surgical mechanism of `v` writes on a row. -/
def writtenRow (assignment : V → Option β) (u : Noise (β := β) graph) (v : V)
    (row : ParentFun (β := β) graph v) : β :=
  match assignment v with
  | some a => a
  | none => u v row

/-- **The replay table of a noise sample under an intervention**: the firing that makes what the
surgical mechanism writes on its row weighs `1`, the others `0`. -/
def replayTable (assignment : V → Option β) (u : Noise (β := β) graph) (e : Ev) : ℝ :=
  if e.2.2.2 = writtenRow graph assignment u e.1 e.2.1 then 1 else 0

omit [DecidableEq V] [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β] in
theorem writtenRow_parentFunOf (assignment : V → Option β) (u : Noise (β := β) graph) (x : V → β)
    (v : V) : writtenRow graph assignment u v (parentFunOf graph x v) = written graph assignment u x v := by
  unfold writtenRow written
  cases assignment v <;> rfl

omit [DecidableEq V] [Inhabited β] [MeasurableSpace β] in
theorem replayTable_total (assignment : V → Option β) (u : Noise (β := β) graph) (v : V)
    (row : ParentFun (β := β) graph v) (r : Unit) :
    ∑ b, replayTable graph assignment u ⟨v, (row, r, b)⟩ = 1 := by
  simp [replayTable]

omit [Inhabited β] in
/-- **The replay's history likelihood on the step is the indicator of Grok's folded store.** -/
theorem replay_likelihood (A : SubstitutionAction (Atom V β Unit) S) (assignment : V → Option β)
    (u : Noise (β := β) graph) (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order) (seed x : V → β) :
    stepLikelihood graph A plain (replayTable graph assignment u) x =
      if foldEval graph assignment u order seed = x then 1 else 0 := by
  rw [stepLikelihood_eq graph acyclic A plain _ x
    (fun v => by rw [replayTable_total]; exact one_pos)]
  simp only [replayTable_total, div_one]
  simp only [replayTable, assignmentEvent, writtenRow_parentFunOf]
  rw [Fintype.prod_boole]
  simp only [foldEval_eq_iff graph acyclic order horder assignment u seed x]

omit [Fintype β] [DecidableEq β] [Inhabited β] in
/-- **Abduction is exact on the record**: a noise sample replays the recorded history, without
intervention, exactly when it agrees with the record on the rows the run visited. -/
theorem extends_record_iff (order : List V)
    (horder : (network (β := β) graph acyclic).IsTopologicalOrder order)
    (u : Noise (β := β) graph) (seed x : V → β) :
    foldEval graph (fun _ => none) u order seed = x ↔ ∀ v, u v (parentFunOf graph x v) = x v := by
  rw [foldEval_eq_iff graph acyclic order horder]
  exact ⟨fun h v => (h v).symm, fun h v => (h v).symm⟩

/-- **Averaged over Grok's noise law, replay under a do is the do.** -/
theorem replay_average (A : SubstitutionAction (Atom V β Unit) S)
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (assignment : V → Option β) (x : V → β) :
    ∑ u : Noise (β := β) graph, (noiseWeight graph acyclic cpt u).toReal *
        stepLikelihood graph A plain (replayTable graph assignment u) x =
      (truncatedWeight graph acyclic cpt assignment x).toReal := by
  classical
  obtain ⟨order, horder⟩ := (network (β := β) graph acyclic).exists_topological_order
  simp_rw [replay_likelihood graph acyclic A assignment _ order horder (fun _ => default) x]
  rw [← surgeryPMF_apply_eq_truncatedWeight graph acyclic cpt assignment order horder x]
  unfold surgeryPMF noisePMF
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [PMF.ofFintype_apply]
    by_cases same : foldEval graph assignment u order (fun _ => default) = x
    · rw [if_pos same, if_pos same.symm, mul_one]
    · rw [if_neg same, if_neg (Ne.symm same), mul_zero, ENNReal.toReal_zero]
  · intro u _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top

/-- **Pearl's counterfactual mass on the step**: abduction weighs a noise sample by the likelihood
that it replays the recorded history `observed`; action replays it under the do; prediction reads
the store `predicted`. -/
def counterfactualMass (A : SubstitutionAction (Atom V β Unit) S)
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (observed : V → β)
    (assignment : V → Option β) (predicted : V → β) : ℝ :=
  ∑ u : Noise (β := β) graph, (noiseWeight graph acyclic cpt u).toReal *
    stepLikelihood graph A plain (replayTable graph (fun _ => none) u) observed *
      stepLikelihood graph A plain (replayTable graph assignment u) predicted

/-- **The counterfactual masses sum to the likelihood of the record**: the step's
Bayesian-network joint of the observed history. -/
theorem counterfactual_total (A : SubstitutionAction (Atom V β Unit) S)
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (observed : V → β)
    (assignment : V → Option β) :
    ∑ predicted, counterfactualMass graph acyclic A cpt observed assignment predicted =
      (cpt.jointWeight observed).toReal := by
  obtain ⟨order, horder⟩ := (network (β := β) graph acyclic).exists_topological_order
  unfold counterfactualMass
  rw [Finset.sum_comm]
  have predictedTotal : ∀ u : Noise (β := β) graph,
      ∑ predicted, stepLikelihood graph A plain (replayTable graph assignment u) predicted = 1 := by
    intro u
    simp_rw [replay_likelihood graph acyclic A assignment u order horder (fun _ => default)]
    simp
  simp_rw [← Finset.mul_sum, predictedTotal, mul_one]
  rw [replay_average graph acyclic A cpt (fun _ => none) observed,
    truncatedWeight_none_eq_jointWeight]

#print axioms record_made
#print axioms record_covers
#print axioms replay_likelihood
#print axioms extends_record_iff
#print axioms replay_average
#print axioms counterfactual_total

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalReplay

end
