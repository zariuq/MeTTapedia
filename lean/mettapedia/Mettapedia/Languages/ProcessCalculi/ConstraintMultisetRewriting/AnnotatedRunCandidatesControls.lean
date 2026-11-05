import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidatesFrontier

/-!
# Controls for source-derived candidates

* **Generation from the sources** (`candidates_eq`): the taker's rule with the scan `0, 1` gives
  two candidates, one per scanned occurrence; both are admitted at the start.
* **The defect of the rho-weighted simulator** (`defect_reports_absorbing`): a step that keeps
  only completed `true` classifications, drops those that ran out of budget, and reads a zero total
  propensity as absorption, reports absorption with a known enabled firing of propensity `2`
  and an exhausted budget. Any step of that shape does so whenever every classification ran out
  (`defective_absorbs_when_exhausted`).
* **The generator cannot report it** (`generator_reports_incomplete`): on the same inputs it
  reports incomplete, never "no admitted firing".
* **With budget** (`budget_restores_the_step`): the step continues, and the generation is complete
  and exact relative to the catalogue.
* **Incompleteness is not emptiness** (`complete_none_vs_incomplete`): an empty scan of the empty
  configuration is complete and reports "no admitted firing", which is true; the start with no
  budget also admits nothing, and reports incomplete.
* **The unfolding driven by the sources** (`driven_frontier`): with no budget the depth-one
  frontier found nothing and is incomplete; with budget it is complete and holds the taker's
  history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidates.Controls

open AnnotatedRuns
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run zeros taker start taker_valid)
open AnnotatedRunUnfolding (known pending Terminal)

/-- One catalogue entry: the taker's rule, without predicate queries. -/
def catalogue : List (Entry (Term signature) (Subst signature) Nat) := [entryOf taker]

/-- The scan of the start configuration. -/
def contents : List Nat := [0, 1]

/-- The fresh identity of the output. -/
def supply (_ : Entry (Term signature) (Subst signature) Nat) : List Nat := [2]

/-- The taker's rule, taking occurrence `1` instead. -/
def takerOne : Run := ⟨taker.rule, [], ⟨[1], [], [2]⟩⟩

theorem candidates_eq : candidates catalogue contents supply = [taker, takerOne] := rfl

/-- Every variable to `f(0)`. -/
def fZero : Subst signature := fun _ => ConstraintMultisetRewriting.Controls.f (.const 0)

theorem takerOne_valid : takerOne.Valid A label start := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨fZero, ?_⟩, by simp [takerOne, taker]⟩,
    by simp [takerOne]⟩
  intro equation member
  have same : equation = (ConstraintMultisetRewriting.Controls.f (.const 0), label 1) := by
    simpa [Selection.problem, Selection.equations, start, takerOne, taker] using member
  subst same
  rfl

/-- Answers after one unit of budget, nothing before. -/
def classify : Classifier (Term signature) (Subst signature) Nat :=
  fun budget _ => if budget = 0 then none else some true

theorem calibrated : Calibrated A label start (candidates catalogue contents supply) classify := by
  intro budget f member answer answered
  rw [candidates_eq] at member
  unfold classify at answered
  split at answered
  · cases answered
  · obtain rfl := Option.some.inj answered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact iff_of_true taker_valid rfl
    · exact iff_of_true takerOne_valid rfl

/-! ## The defect of the rho-weighted simulator -/

/-- How a simulator step ends. -/
inductive Stop where
  | absorbing
  | continues
deriving DecidableEq

/-- **The shape of the defect**: only completed `true` classifications are kept, a classification
that ran out of budget is dropped, and a zero total propensity is read as absorption. -/
def defectiveStep (cands : List Run) (check : Run → Option Bool) (propensity : Run → ℕ) : Stop :=
  if ((known cands check).map propensity).sum = 0 then .absorbing else .continues

/-- A step of that shape absorbs whenever every classification ran out, whatever is enabled. -/
theorem defective_absorbs_when_exhausted (cands : List Run) (check : Run → Option Bool)
    (propensity : Run → ℕ) (exhausted : ∀ f ∈ cands, check f = none) :
    defectiveStep cands check propensity = .absorbing := by
  have empty : known cands check = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro f member
    simp only [known, List.mem_filter, decide_eq_true_eq] at member
    rw [exhausted f member.1] at member
    cases member.2
  simp [defectiveStep, empty]

/-- **The defect reproduced.** A known enabled firing of positive propensity, an exhausted budget,
and the defective step reports absorption. -/
theorem defect_reports_absorbing :
    taker.Valid A label start ∧ taker ∈ candidates catalogue contents supply ∧
      classify 0 taker = none ∧
      defectiveStep (candidates catalogue contents supply) (classify 0) (fun _ => 2) = .absorbing :=
  ⟨taker_valid, by rw [candidates_eq]; exact List.mem_cons_self, rfl,
    defective_absorbs_when_exhausted _ _ _ fun _ _ => rfl⟩

/-- **The generator cannot report it.** On the same inputs the generation is incomplete, and its
verdict is incomplete, not "no admitted firing". -/
theorem generator_reports_incomplete :
    (generate catalogue contents supply classify 0).status = .incomplete ∧
      (generate catalogue contents supply classify 0).verdict = .incomplete ∧
      (generate catalogue contents supply classify 0).verdict ≠ .none :=
  ⟨rfl, rfl, not_none_of_valid A label calibrated (by rw [candidates_eq]; exact List.mem_cons_self)
    taker_valid⟩

/-- **With budget**, the step continues, and the generation is complete and exact relative to the
catalogue. -/
theorem budget_restores_the_step :
    defectiveStep (candidates catalogue contents supply) (classify 1) (fun _ => 2) = .continues ∧
      (generate catalogue contents supply classify 1).status = .complete ∧
      (generate catalogue contents supply classify 1).verdict = .admitted ∧
      ∀ f, f ∈ (generate catalogue contents supply classify 1).admitted ↔
        entryOf f ∈ catalogue ∧ f.selection.made = supply (entryOf f) ∧ f.Valid A label start := by
  have complete : (generate catalogue contents supply classify 1).status = .complete := rfl
  refine ⟨rfl, complete, rfl, fun f => ?_⟩
  exact complete_exact_catalogue A label (by decide) calibrated complete f

/-! ## Incompleteness is not emptiness -/

theorem empty_scan_candidates : candidates catalogue [] supply = [] := rfl

/-- **Incompleteness is not emptiness.** An empty scan of the empty configuration is complete and
reports "no admitted firing", and no catalogue firing with the supplied identities is admitted
there; at the start with no budget nothing is admitted either, and the report is incomplete. -/
theorem complete_none_vs_incomplete :
    (generate catalogue [] supply classify 0).status = .complete ∧
      (generate catalogue [] supply classify 0).verdict = .none ∧
      (∀ f : Run, entryOf f ∈ catalogue → f.selection.made = supply (entryOf f) →
        ¬ f.Valid A label AnnotatedRuns.Controls.empty) ∧
      (generate catalogue contents supply classify 0).admitted = [] ∧
      (generate catalogue contents supply classify 0).verdict = .incomplete := by
  refine ⟨rfl, rfl, fun f entry made valid => ?_, rfl, rfl⟩
  have member := mem_candidates_of_valid A label (C := AnnotatedRuns.Controls.empty) (contents := [])
    (by intro o present; simp [AnnotatedRuns.Controls.empty] at present) entry made valid
  rw [empty_scan_candidates] at member
  cases member

/-! ## The unfolding driven by the sources -/

/-- The same catalogue, scan and supply at every cut. -/
def sources : Sources (Term signature) (Subst signature) Nat :=
  ⟨catalogue, fun _ => contents, fun _ => supply⟩

open Classical in
/-- A semantic classifier gated by a budget: nothing at budget `0`, the verdict otherwise. -/
noncomputable def gated :
    Configuration (Term signature) Nat → Classifier (Term signature) (Subst signature) Nat :=
  fun cut budget f => if budget = 0 then none else some (decide (f.Valid A label cut))

theorem gated_calibrated : CalibratedEverywhere A label sources gated := by
  intro cut budget f _ answer answered
  unfold gated at answered
  split at answered
  · cases answered
  · obtain rfl := Option.some.inj answered
    simp

theorem pending_gated (cut : Configuration (Term signature) Nat) (budget : ℕ) (positive : budget ≠ 0) :
    AnnotatedRunUnfolding.pending (sources.candidatesAt cut) (gated cut budget) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro f member
  simp only [AnnotatedRunUnfolding.pending, List.mem_filter, decide_eq_true_eq, gated,
    if_neg positive] at member
  cases member.2

/-- **The unfolding driven by the sources.** With no budget the depth-one frontier found nothing
and is incomplete; with budget it is complete and holds the taker's history. -/
theorem driven_frontier :
    (sourceFrontier A label sources gated 0 1 start).2 = .incomplete ∧
      (sourceFrontier A label sources gated 0 1 start).1 = [] ∧
      (sourceFrontier A label sources gated 1 1 start).2 = .complete ∧
      [taker] ∈ (sourceFrontier A label sources gated 1 1 start).1 := by
  have complete : (sourceFrontier A label sources gated 1 1 start).2 = .complete := by
    refine (sourceFrontier_succ_status A label).mpr ⟨?_, fun f _ => rfl⟩
    exact status_complete_iff.mpr (pending_gated start 1 one_ne_zero)
  refine ⟨rfl, rfl, complete, ?_⟩
  refine (sourceFrontier_exact A label gated_calibrated 1 start complete [taker]).mpr
    ⟨rfl, ⟨taker_valid, taker_valid.firing.consistent⟩, .cons ?_ (.nil _)⟩
  change taker ∈ candidates catalogue contents supply
  rw [candidates_eq]
  exact List.mem_cons_self

#print axioms candidates_eq
#print axioms takerOne_valid
#print axioms calibrated
#print axioms defective_absorbs_when_exhausted
#print axioms defect_reports_absorbing
#print axioms generator_reports_incomplete
#print axioms budget_restores_the_step
#print axioms complete_none_vs_incomplete
#print axioms gated_calibrated
#print axioms driven_frontier

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidates.Controls
