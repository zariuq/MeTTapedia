import Mettapedia.GSLT.Distinction.Probabilistic.FiniteChains

/-!
# Sub-distributions: the stopped completion and the metric of a probabilistic GSLT

A probabilistic GSLT may refuse a step with positive probability: its steps are
sub-distributions.  On a finite state space it is completed to a labelled
Markov chain (`completion`) by a stopped state `none`: the defect of every step
goes there, the stopped state stays put, and an extra observable `halted`
reads `1` there and `0` elsewhere; the atoms of the system are read as
indicators.

* **Larsen–Skou bisimilarity is bisimilarity of the completion**
  (`lsBisimilar_iff_completion_bisimilar`): the defect of a step is the mass of
  the complement of everything, so related states refuse alike.
* **The behavioural pseudometric of a finite probabilistic GSLT**
  (`behaviouralMetric`) is the Kantorovich fixed point of the completion, read
  at the states.  It is the logical distance of functional expressions on the
  completion (`behaviouralMetric_eq_logicalDistance`), and it vanishes exactly
  on Larsen–Skou bisimilarity (`behaviouralMetric_eq_zero_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.GSLT
open Mettapedia.Cybernetics.ApproximateAdequacy

universe uAtom uLabel

variable {S : Type*} [Fintype S] [DecidableEq S]
  (M : ProbabilisticSystem.{_, uAtom, uLabel} (stateGSLT S))

/-! ## The stopped completion -/

/-- The steps of the completion. -/
noncomputable def completionTrans (label : M.Label) : Option S → Option S → ℝ
  | none => dirac none
  | some s => fun
      | none => 1 - (M.kernel label s).total
      | some x => (M.kernel label s).weight x

open Classical in
/-- The observables of the completion: `none` is `halted`, `some a` is the
indicator of the atom `a`. -/
noncomputable def completionObserve : Option M.Atom → Option S → ℝ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some atom, some s => if M.observes atom s then 1 else 0

theorem isDistribution_completionTrans (label : M.Label) (state : Option S) :
    IsDistribution (completionTrans M label state) := by
  rcases state with _ | s
  · exact isDistribution_dirac none
  · have total : (M.kernel label s).total = ∑ x, (M.kernel label s).weight x :=
      (M.kernel label s).total_eq_sum
    refine ⟨fun x => ?_, ?_⟩
    · rcases x with _ | x
      · change 0 ≤ 1 - (M.kernel label s).total
        linarith [(M.kernel label s).total_le_one']
      · exact (M.kernel label s).nonneg x
    · rw [Fintype.sum_option]
      change 1 - (M.kernel label s).total + ∑ x, (M.kernel label s).weight x = 1
      rw [total]
      ring

/-- **The stopped completion** of a finite probabilistic GSLT. -/
noncomputable def completion : LabelledMarkovChain ℝ M.Label (Option M.Atom) (Option S) where
  trans := completionTrans M
  isDistribution := isDistribution_completionTrans M
  observe := completionObserve M

variable {M}

open Classical in
/-- The mass of a predicate under a completed step from a state. -/
theorem sum_completion_some (label : M.Label) (s : S) (C : S → Prop) :
    (∑ w : Option S, if (∃ z, w = some z ∧ C z) then (completion M).trans label (some s) w else 0) =
      M.prob label s C := by
  rw [Fintype.sum_option]
  unfold ProbabilisticSystem.prob
  rw [SubDistribution.mass_eq_sum]
  simp only [reduceCtorEq, false_and, exists_false, if_false, zero_add, Option.some.injEq,
    exists_eq_left']
  rfl

/-! ## Larsen–Skou bisimilarity is bisimilarity of the completion -/

/-- The relation of the completion induced by a relation on states. -/
def liftRelation (R : S → S → Prop) : Option S → Option S → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

omit [Fintype S] [DecidableEq S] in
theorem equivalence_liftRelation {R : S → S → Prop} (equivalence : Equivalence R) :
    Equivalence (liftRelation R) := by
  refine ⟨fun x => ?_, fun {x y} related => ?_, fun {x y z} first second => ?_⟩
  · rcases x with _ | x
    · trivial
    · exact equivalence.refl x
  · rcases x with _ | x <;> rcases y with _ | y
    · trivial
    · exact related
    · exact related
    · exact equivalence.symm related
  · rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;>
      first | trivial | exact first.elim | exact second.elim |
        exact equivalence.trans first second

/-- **A Larsen–Skou bisimulation lifts to a probabilistic bisimulation of the
completion.** -/
theorem ProbabilisticSystem.IsLSBisimulation.isProbabilisticBisimulation_completion
    {R : S → S → Prop}
    (bisimulation : M.IsLSBisimulation R) :
    IsProbabilisticBisimulation (completion M) (completion M) (liftRelation R) := by
  classical
  have lifted := equivalence_liftRelation bisimulation.equivalence
  intro p q related
  rcases p with _ | x <;> rcases q with _ | y
  · exact ⟨fun _ => rfl, fun label =>
      exists_coupling_of_classMass_eq lifted ((completion M).isDistribution label none)
        ((completion M).isDistribution label none) fun _ => rfl⟩
  · exact related.elim
  · exact related.elim
  · have related' : R x y := related
    refine ⟨fun atom => ?_, fun label => ?_⟩
    · rcases atom with _ | atom
      · rfl
      · change (if M.observes atom x then (1 : ℝ) else 0) = if M.observes atom y then 1 else 0
        rw [if_congr (bisimulation.observes related' atom) rfl rfl]
    · refine exists_coupling_of_classMass_eq lifted ((completion M).isDistribution label (some x))
        ((completion M).isDistribution label (some y)) fun w => ?_
      have total : (M.kernel label x).total = (M.kernel label y).total := by
        rw [← (M.kernel label x).mass_true, ← (M.kernel label y).mass_true]
        exact bisimulation.masses related' label _ fun _ _ _ => Iff.rfl
      rcases w with _ | z
      · unfold relationMass
        rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_option, Fintype.sum_option]
        have stopped : ∀ μ : Option S → ℝ, ((if liftRelation R none none then μ none else 0) +
            ∑ i : S, if liftRelation R none (some i) then μ (some i) else 0) = μ none := by
          intro μ
          rw [if_pos (show liftRelation R none none from trivial),
            Finset.sum_eq_zero fun i _ => if_neg (show ¬ liftRelation R none (some i) from not_false),
            add_zero]
        rw [stopped, stopped]
        change 1 - (M.kernel label x).total = 1 - (M.kernel label y).total
        rw [total]
      · have closed : ProbabilisticSystem.ClosedUnder (S := stateGSLT S) R (R z) := by
          intro u v uv
          exact ⟨fun first => bisimulation.equivalence.trans first uv,
            fun second => bisimulation.equivalence.trans second (bisimulation.equivalence.symm uv)⟩
        have masses := bisimulation.masses related' label (R z) closed
        have read : ∀ s : S, relationMass (liftRelation R) ((completion M).trans label (some s))
            (some z) = M.prob label s (R z) := by
          intro s
          rw [← sum_completion_some]
          unfold relationMass
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun w _ => ?_
          rcases w with _ | w
          · simp [liftRelation]
          · by_cases holds : R z w <;> simp [liftRelation, holds]
        rw [read, read]
        exact masses

/-- Distance zero at discount one, between states of the completion. -/
noncomputable def completionZero [Fintype M.Label] [Fintype M.Atom] (x y : S) : Prop :=
  bisimulationMetric (completion M) (completion M) 1 (some x) (some y) = 0

/-- **Distance zero in the completion is a Larsen–Skou bisimulation.** -/
theorem isLSBisimulation_completionZero [Fintype M.Label] [Fintype M.Atom] :
    M.IsLSBisimulation (completionZero (M := M)) := by
  classical
  have bisimulation := (couplingBound_bisimulationMetric (P := completion M) (Q := completion M)
    zero_le_one le_rfl).isProbabilisticBisimulation_zero zero_lt_one
  have equivalence : Equivalence fun p q : Option S =>
      bisimulationMetric (completion M) (completion M) 1 p q = 0 := equivalence_metric_zero
  have stopped : ∀ x, bisimulationMetric (completion M) (completion M) 1 (some x) none ≠ 0 := by
    intro x zero
    have observed := (bisimulation zero).1 none
    change (0 : ℝ) = 1 at observed
    norm_num at observed
  refine ⟨⟨fun x => equivalence.refl _, fun related => equivalence.symm related,
      fun first second => equivalence.trans first second⟩, fun {x y} same => ?_,
    fun {x y} related atom => ?_, fun {x y} related label C closed => ?_⟩
  · have equal : x = y := same
    subst equal
    exact equivalence.refl _
  · have observed := (bisimulation related).1 (some atom)
    change (if M.observes atom x then (1 : ℝ) else 0) = if M.observes atom y then 1 else 0
      at observed
    by_cases first : M.observes atom x <;> by_cases second : M.observes atom y <;>
      simp_all
  · obtain ⟨ω, supported⟩ := (bisimulation related).2 label
    have lifted : ∀ p q, bisimulationMetric (completion M) (completion M) 1 p q = 0 →
        ((∃ z, p = some z ∧ C z) ↔ (∃ z, q = some z ∧ C z)) := by
      intro p q zero
      rcases p with _ | u <;> rcases q with _ | v
      · exact Iff.rfl
      · exact absurd (by rw [bisimulationMetric_comm zero_le_one le_rfl]; exact zero) (stopped v)
      · exact absurd zero (stopped u)
      · have uv : C u ↔ C v := closed u v zero
        simp only [Option.some.injEq, exists_eq_left']
        exact uv
    have equal := mass_eq_of_coupling ω supported lifted
    calc M.prob label x C = _ := (sum_completion_some label x C).symm
      _ = _ := by convert equal using 3
      _ = M.prob label y C := sum_completion_some label y C

/-- **Larsen–Skou bisimilarity is probabilistic bisimilarity of the
completion.** -/
theorem lsBisimilar_iff_completion_bisimilar [Fintype M.Label] [Fintype M.Atom] {x y : S} :
    M.LSBisimilar x y ↔ ProbabilisticallyBisimilar (completion M) (completion M) (some x) (some y) := by
  constructor
  · rintro ⟨R, bisimulation, related⟩
    exact ⟨liftRelation R, bisimulation.isProbabilisticBisimulation_completion, related⟩
  · intro bisimilar
    exact ⟨_, isLSBisimulation_completionZero,
      (bisimulationMetric_eq_zero_iff zero_lt_one le_rfl).mpr bisimilar⟩

/-! ## The behavioural pseudometric of a finite probabilistic GSLT -/

/-- **The behavioural pseudometric** of a finite probabilistic GSLT at discount
`c`: the Kantorovich fixed point of its stopped completion, read at the
states. -/
noncomputable def behaviouralMetric [Fintype M.Label] [Fintype M.Atom] (c : ℝ) (x y : S) : ℝ :=
  bisimulationMetric (completion M) (completion M) c (some x) (some y)

/-- **It is the logical distance of functional expressions on the
completion.** -/
theorem behaviouralMetric_eq_logicalDistance [Fintype M.Label] [Fintype M.Atom] {c : ℝ}
    (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (x y : S) :
    behaviouralMetric (M := M) c x y = logicalDistance (completion M) c (some x) (some y) := by
  unfold behaviouralMetric
  rw [bisimulationMetric_eq_logicalDistance c_nonneg c_le]

/-- **It vanishes exactly on Larsen–Skou bisimilarity**, at every discount
`0 < c ≤ 1`. -/
theorem behaviouralMetric_eq_zero_iff [Fintype M.Label] [Fintype M.Atom] {c : ℝ} (c_pos : 0 < c)
    (c_le : c ≤ 1) {x y : S} : behaviouralMetric (M := M) c x y = 0 ↔ M.LSBisimilar x y :=
  (bisimulationMetric_eq_zero_iff c_pos c_le).trans lsBisimilar_iff_completion_bisimilar.symm

/-- **It is a pseudometric**: symmetric, with the triangle inequality. -/
theorem behaviouralMetric_comm [Fintype M.Label] [Fintype M.Atom] {c : ℝ} (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) (x y : S) :
    behaviouralMetric (M := M) c x y = behaviouralMetric (M := M) c y x := by
  unfold behaviouralMetric
  exact (bisimulationMetric_comm (P := completion M) (Q := completion M) c_nonneg c_le
    (some x) (some y)).symm

theorem behaviouralMetric_triangle [Fintype M.Label] [Fintype M.Atom] {c : ℝ} (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) (x y z : S) :
    behaviouralMetric (M := M) c x z ≤
      behaviouralMetric (M := M) c x y + behaviouralMetric (M := M) c y z :=
  bisimulationMetric_triangle (P := completion M) (Q := completion M) (completion M) c_nonneg c_le
    (some x) (some y) (some z)

end Mettapedia.GSLT.Distinction.Probabilistic
