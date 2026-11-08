import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceCommit
import Mathlib.Data.Real.Basic

/-!
# Weighted firings: the die pair

A **generative probabilistic step**: every member of a program's alphabet carries a weight, and at a
configuration an admitted firing fires with its weight divided by the total weight of the admitted
firings (`prob`). Labels name firings (`name`).

* **Trace distributions** (`traceProb`): the probability that the run begins with a given word of
  labels.
* **Probabilistic bisimulation** (`ProbBisimulation`, Larsen and Skou): an equivalence under which
  related configurations move with equal probability, under every label, into every union of
  classes.

## The die pair (`Die`)

The race pair of `RacePair`, weighted. `P` fires `A` and then races `B` with weight `p` against `C`
with weight `1 - p`: `a.(p·b + (1−p)·c)`. `Q` races two firings of `A` with weights `p` and
`1 - p`, committing to `b` or to `c`: `p·(a.b) + (1−p)·(a.c)`.

* **Equal trace distributions** (`traceProb_P_eq_Q`), for every `p`.
* **Not probabilistically bisimilar** (`not_probBisimilar`) when `0 < p < 1`: after `A`, `P` is in the
  class of the configuration that still races, with probability `1`, and `Q` with probability `0`.

## A randomized commit (`Twins.uniform_commit`)

The twins of `RaceCommit`, both weighted `1`: each outcome has probability `1/2`, and the start is
fixed by the exchange. The distribution of outcomes is invariant under the exchange, while each
outcome breaks the symmetry (`Twins.record_breaks_symmetry`): a randomized commit is equivariant in
distribution, which `no_deterministic_equivariant_commit` does not exclude.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing renameConfiguration)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

section Weighted

variable (A : SubstitutionAction T S) (label : O → T) (alphabet : List (Firing T S O))
  (name : Firing T S O → L) (weight : Firing T S O → ℝ)

/-- The admitted members of the alphabet, in alphabet order. -/
noncomputable def admitted (C : Configuration T O) : List (Firing T S O) :=
  ((alternatives A label alphabet).next C).map fun g => g.1.1

/-- The total weight of the admitted firings. -/
noncomputable def total (C : Configuration T O) : ℝ := ((admitted A label alphabet C).map weight).sum

open Classical in
/-- **The generative probabilistic step**: the probability of firing under `ℓ` into `E`. -/
noncomputable def prob (C : Configuration T O) (ℓ : L) (E : Set (Configuration T O)) : ℝ :=
  ((admitted A label alphabet C).map fun f =>
    if name f = ℓ ∧ f.result label C ∈ E then weight f else 0).sum / total A label alphabet weight C

open Classical in
/-- **The trace distribution**: the probability that the run begins with a word of labels. -/
noncomputable def traceProb : List L → Configuration T O → ℝ
  | [], _ => 1
  | ℓ :: u, C => ((admitted A label alphabet C).map fun f =>
      if name f = ℓ then weight f / total A label alphabet weight C * traceProb u (f.result label C)
      else 0).sum

/-- **Probabilistic bisimulation** (Larsen–Skou): an equivalence under which related
configurations move with equal probability into every union of classes. -/
def ProbBisimulation (R : Configuration T O → Configuration T O → Prop) : Prop :=
  Equivalence R ∧ ∀ C D, R C D → ∀ (ℓ : L) (E : Set (Configuration T O)),
    (∀ X Y, R X Y → (X ∈ E ↔ Y ∈ E)) → prob A label alphabet name weight C ℓ E =
      prob A label alphabet name weight D ℓ E

end Weighted

/-! ## The die pair -/

namespace Die

open Pair

variable (t : Tags T) (A : SubstitutionAction T S) (p : ℝ)

/-- The weights: `p` for the `A` that commits to `b` and for `B` in the race at `k`; `1 - p` for
their partners; `1` otherwise. -/
def weight (f : Firing T S Site) : ℝ :=
  match f.selection.taken, f.selection.made with
  | [.a, .q], [.kb] => p
  | [.a, .q], [.kc] => 1 - p
  | [.k], [.ob] => p
  | [.k], [.oc] => 1 - p
  | _, _ => 1

/-- Labels are rules. -/
def name (f : Firing T S Site) : RuleInstance T := f.rule

theorem name_aP : name (aP (S := S) t) = ruleA t := rfl
theorem name_aQb : name (aQb (S := S) t) = ruleA t := rfl
theorem name_aQc : name (aQc (S := S) t) = ruleA t := rfl
theorem name_bP : name (bP (S := S) t) = ruleB t := rfl
theorem name_cP : name (cP (S := S) t) = ruleC t := rfl
theorem name_bQ : name (bQ (S := S) t) = ruleB t := rfl
theorem name_cQ : name (cQ (S := S) t) = ruleC t := rfl

theorem weight_aP : weight p (aP (S := S) t) = 1 := rfl
theorem weight_aQb : weight p (aQb (S := S) t) = p := rfl
theorem weight_aQc : weight p (aQc (S := S) t) = 1 - p := rfl
theorem weight_bP : weight p (bP (S := S) t) = p := rfl
theorem weight_cP : weight p (cP (S := S) t) = 1 - p := rfl
theorem weight_bQ : weight p (bQ (S := S) t) = 1 := rfl
theorem weight_cQ : weight p (cQ (S := S) t) = 1 := rfl

noncomputable abbrev tp := traceProb A (label t) (alphabet t) name (weight p)

theorem admitted_P : admitted A (label t) (alphabet (S := S) t) P = [aP t] := next_P t A
theorem admitted_K : admitted A (label t) (alphabet (S := S) t) (K t) = [bP t, cP t] := next_K t A
theorem admitted_Q : admitted A (label t) (alphabet (S := S) t) Q = [aQb t, aQc t] := next_Q t A
theorem admitted_Kb : admitted A (label t) (alphabet (S := S) t) (Kb t) = [bQ t] := next_Kb t A
theorem admitted_Kc : admitted A (label t) (alphabet (S := S) t) (Kc t) = [cQ t] := next_Kc t A

theorem total_P : total A (label t) (alphabet t) (weight p) P = 1 := by
  simp [total, admitted_P, weight_aP]
theorem total_K : total A (label t) (alphabet t) (weight p) (K t) = 1 := by
  simp [total, admitted_K, weight_bP, weight_cP]
theorem total_Q : total A (label t) (alphabet t) (weight p) Q = 1 := by
  simp [total, admitted_Q, weight_aQb, weight_aQc]
theorem total_Kb : total A (label t) (alphabet t) (weight p) (Kb t) = 1 := by
  simp [total, admitted_Kb, weight_bQ]
theorem total_Kc : total A (label t) (alphabet t) (weight p) (Kc t) = 1 := by
  simp [total, admitted_Kc, weight_cQ]

/-- At `k`, the race is the mixture of the two committed configurations. -/
theorem tp_K_mix (u : List (RuleInstance T)) :
    tp t A p u (K t) = p * tp t A p u (Kb t) + (1 - p) * tp t A p u (Kc t) := by
  cases u with
  | nil => simp only [tp, traceProb]; ring
  | cons ℓ u =>
      simp only [tp, traceProb, admitted_K, admitted_Kb, admitted_Kc, total_K, total_Kb, total_Kc,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, result_bP, result_cP, result_bQ,
        result_cQ, name_bP, name_cP, name_bQ, name_cQ, weight_bP, weight_cP, weight_bQ, weight_cQ,
        div_one, add_zero]
      by_cases hb : ruleB t = ℓ <;> by_cases hc : ruleC t = ℓ <;> simp only [hb, hc, ↓reduceIte] <;> ring

/-- **The die pair has equal trace distributions.** -/
theorem traceProb_P_eq_Q (u : List (RuleInstance T)) : tp t A p u P = tp t A p u Q := by
  cases u with
  | nil => rfl
  | cons ℓ u =>
      simp only [tp, traceProb, admitted_P, admitted_Q, total_P, total_Q, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, result_aP, result_aQb, result_aQc, name_aP, name_aQb, name_aQc,
        weight_aP, weight_aQb, weight_aQc, div_one, add_zero]
      by_cases ha : ruleA t = ℓ
      · simp only [ha, if_true, one_mul]
        exact tp_K_mix t A p u
      · simp [ha]

noncomputable abbrev pr := prob A (label t) (alphabet t) name (weight p)

theorem pr_Kb_B : pr t A p (Kb t) (ruleB t) Set.univ = 1 := by
  simp [pr, prob, admitted_Kb, total_Kb, name_bQ, weight_bQ]

theorem pr_K_B (apart : t.b ≠ t.c) : pr t A p (K t) (ruleB t) Set.univ = p := by
  have ne : ruleC t ≠ ruleB t := (ruleB_ne_ruleC t apart).symm
  simp [pr, prob, admitted_K, total_K, name_bP, name_cP, weight_bP, ne]

theorem pr_Kc_C : pr t A p (Kc t) (ruleC t) Set.univ = 1 := by
  simp [pr, prob, admitted_Kc, total_Kc, name_cQ, weight_cQ]

theorem pr_K_C (apart : t.b ≠ t.c) : pr t A p (K t) (ruleC t) Set.univ = 1 - p := by
  have ne : ruleB t ≠ ruleC t := ruleB_ne_ruleC t apart
  simp [pr, prob, admitted_K, total_K, name_bP, name_cP, weight_cP, ne]

/-- **The die pair is not probabilistically bisimilar** when the die is not loaded to one side. -/
theorem not_probBisimilar (apart : t.b ≠ t.c) (positive : 0 < p) (belowOne : p < 1) :
    ¬ ∃ R, ProbBisimulation A (label t) (alphabet t) name (weight p) R ∧ R P Q := by
  rintro ⟨R, ⟨equivalence, transfer⟩, related⟩
  have closedUniv : ∀ X Y, R X Y → (X ∈ (Set.univ : Set (Configuration T Site)) ↔ Y ∈ Set.univ) :=
    fun _ _ _ => Iff.rfl
  have notKb : ¬ R (Kb t) (K t) := fun r => by
    have := transfer _ _ r (ruleB t) Set.univ closedUniv
    change pr t A p (Kb t) (ruleB t) Set.univ = pr t A p (K t) (ruleB t) Set.univ at this
    rw [pr_Kb_B, pr_K_B t A p apart] at this
    linarith
  have notKc : ¬ R (Kc t) (K t) := fun r => by
    have := transfer _ _ r (ruleC t) Set.univ closedUniv
    change pr t A p (Kc t) (ruleC t) Set.univ = pr t A p (K t) (ruleC t) Set.univ at this
    rw [pr_Kc_C, pr_K_C t A p apart] at this
    linarith
  have closedClass : ∀ X Y, R X Y → (X ∈ {Z | R Z (K t)} ↔ Y ∈ {Z | R Z (K t)}) := fun X Y r =>
    ⟨fun xK => equivalence.trans (equivalence.symm r) xK, fun yK => equivalence.trans r yK⟩
  have moved := transfer _ _ related (ruleA t) {Z | R Z (K t)} closedClass
  change pr t A p P (ruleA t) {Z | R Z (K t)} = pr t A p Q (ruleA t) {Z | R Z (K t)} at moved
  simp only [pr, prob, admitted_P, admitted_Q, total_P, total_Q, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, result_aP, result_aQb, result_aQc, name_aP, name_aQb, name_aQc,
    weight_aP, weight_aQb, weight_aQc, div_one, add_zero] at moved
  have hK : R ((aP (S := S) t).result (label t) P) (K t) := by
    rw [result_aP]
    exact equivalence.refl _
  have hKb : ¬ R ((aQb (S := S) t).result (label t) Q) (K t) := by
    rw [result_aQb]
    exact notKb
  have hKc : ¬ R ((aQc (S := S) t).result (label t) Q) (K t) := by
    rw [result_aQc]
    exact notKc
  simp [hK, hKb, hKc] at moved

end Die

/-! ## A randomized commit is equivariant in distribution -/

namespace Twins

variable (τ : T) (A : SubstitutionAction T S)

theorem admitted_C : admitted A (label τ) (competitors (S := S) τ) C = [take τ .x, take τ .y] :=
  next_C τ A

theorem start_fixed : renameConfiguration exchange (C : Configuration T Site) = C :=
  config_eq rfl (of_decide_eq_true rfl)

/-- **A uniform commit**: with both competitors weighted `1`, each outcome has probability `1/2`,
and the start is fixed by the exchange. -/
theorem uniform_commit :
    prob A (label τ) (competitors τ) (fun _ => ()) (fun _ => (1 : ℝ)) C () {Cx τ} = 1 / 2 ∧
      prob A (label τ) (competitors τ) (fun _ => ()) (fun _ => (1 : ℝ)) C () {Cy τ} = 1 / 2 ∧
      renameConfiguration exchange (C : Configuration T Site) = C := by
  have apart : Cx τ ≠ Cy τ := fun same =>
    absurd (congrArg Configuration.present same) (of_decide_eq_false rfl)
  have yNotX : (take (S := S) τ .y).result (label τ) C ≠ Cx τ := by
    rw [result_y]
    exact apart.symm
  have xNotY : (take (S := S) τ .x).result (label τ) C ≠ Cy τ := by
    rw [result_x]
    exact apart
  refine ⟨?_, ?_, start_fixed⟩
  · simp [prob, total, admitted_C, result_x, yNotX]
    norm_num
  · simp [prob, total, admitted_C, result_y, xNotY]
    norm_num

end Twins

#print axioms Die.traceProb_P_eq_Q
#print axioms Die.not_probBisimilar
#print axioms Twins.uniform_commit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
