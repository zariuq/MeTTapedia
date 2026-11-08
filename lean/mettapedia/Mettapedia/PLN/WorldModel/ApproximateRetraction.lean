import Mettapedia.Logic.WorldModel.Approximation
import Mettapedia.PLN.WorldModel.EvidenceSpaces

/-!
# Approximate retraction with certified bounds

Exact retraction is the specification: forgetting the sources `S` gives what would have been
computed without them (`LedgerRetraction`, `ProvenanceRetraction`).  A compressed representation
of evidence often cannot compute that.  An approximate forgetting is then measured against exact
recomputation,

  `d(observe_q(F_S(c W)), observe_q(U_S W)) ≤ ε(W, S, q)`,

where `U_S` is the exact reference, `c` compresses a state and `F_S` forgets on compressed states.

## The certified bound is an approximation map

Reading a claim after a retraction is a world model on the same states (`AfterRetraction`): the
query `(S, q)` reads `q` once `S` is withdrawn.  The certified bound is an `ApproximationMap` from
the exact reference to the compressed forgetting (`certified`): states are compressed, queries and
values are kept.  Every Lipschitz readout inherits the bound scaled by its constant
(`certified_measured`, through `ApproximationMap.measured_error`).  Confidence `n / (n + k)` is
`k⁻¹`-Lipschitz (`confidence_lipschitz`).

## One-sided bounds

The compressed representations of `ApproximateRetractionProvenance` and
`ApproximateRetractionCounts` err on one side: their reading never exceeds the exact one and misses
at most a width they hold (`Encloses`).  On `ℝ≥0` this is a pair of bounds in the Lawvere distance
`a - b` (truncated subtraction), `lo - x = 0` and `x - lo ≤ w` (`encloses_iff_tsub`).  The
symmetric distance used by `ApproximationMap` is its symmetrization, `nndist a b = max (a - b)
(b - a)` (`NNReal.nndist_eq`), so a width bounds the distance (`Encloses.dist_le`).

* Revision adds enclosures and their widths (`Encloses.add`): constant 1 in each argument.
* Deduction multiplies them (`Encloses.mul`): each premise's width is scaled by the other premise's
  estimate, `lo₁ w₂ + w₁ lo₂ + w₁ w₂` (`mulWidth`).
* Both steps are monotone, so the one-sided law survives them.  Strength is not monotone in the
  negative count: a reading that manufactures no count can manufacture strength
  (`strength_manufactured`).

## The consumer: a threshold guard

`thresholdGuard θ lo hi` commits `above` when the whole certified interval `[lo, hi]` is at least
`θ`, commits `below` when it lies entirely below `θ`, and is otherwise `undecided`.  It reads only
the interval, which the compressed system holds, and a committed decision is never wrong
(`thresholdGuard_sound`, `thresholdGuard_decision_sound`).  A zero-width interval always decides
(`thresholdGuard_point_decides`); an interval containing the threshold never does
(`thresholdGuard_undecided_iff`).  At the threshold, an interval starting at `θ` commits and one
ending at `θ` does not (`thresholdGuard_at_threshold`).

## Strength near a zero denominator

Strength `p / (p + n)` has no global Lipschitz constant for the count distance
(`strength_not_lipschitz`), so no Lipschitz-readout argument certifies it.  From one-sided count
bounds it lies between the corners `p̃ / (p̃ + ñ + w⁻)` and `(p̃ + w⁺) / (p̃ + w⁺ + ñ)`
(`strength_mem_corners`).  `strengthGuard` is undecided when the held counts are both zero, since
the exact readout (`EvidenceSpaces.Evidence.readout`) may then be undetermined
(`zero_denominator`); otherwise it guards the corners.  It never commits wrongly and never commits
on an undetermined readout (`strengthGuard_sound`).

## Two contracts

* **Belief retraction** (`BeliefRetraction`): every observable reading of the forgotten state agrees
  with the reading of the recomputed state.
* **Whole-state erasure** (`StateErasure`): the retained state is the recomputed state.  Its weak
  form (`ErasesUpToRecomputation`) asks that two states agreeing once the scope is removed cannot
  be told apart after forgetting.

Erasure gives belief retraction (`StateErasure.beliefRetraction`); the converse fails
(`ApproximateRetractionCounts.Contracts`).  An approximation that is exact on states the
retraction fixes and erases up to recomputation is exact (`exact_of_erases_of_vacuous`).  Hence
an approximation that is exact on clean states and inexact somewhere keeps information about the
withdrawn sources (`leaks_of_inexact`): its error depends on them.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ApproximateRetraction

open scoped NNReal
open Mettapedia.Logic.WorldModel (ApproximationMap)
open Mettapedia.PLN.WorldModel.EvidenceSpaces (Evidence)

/-! ## Reading after a retraction -/

section Reading

variable {X C Scope Q V : Type*}

/-- The states `X` read after a retraction: the query `(S, q)` reads `q` with `read` once
`retract` has withdrawn `S`. -/
def AfterRetraction (_retract : Scope → X → X) (_read : X → Q → V) : Type _ := X

/-- Reading after a retraction is a world model on the same states, with their revision and empty
state. -/
instance instWorldModelAfterRetraction [Add X] [Zero X] (retract : Scope → X → X)
    (read : X → Q → V) : WorldModel (AfterRetraction retract read) (Scope × Q) V where
  revise := fun (first second : X) => first + second
  empty := (0 : X)
  extract W request := read (retract request.1 W) request.2

/-- **The certified bound is an approximation map** from the exact reference to the compressed
forgetting.  `bound` states `d(observe_q(forget S (compress W)), observe_q(retract S W)) ≤
error W S q`; states are compressed, and queries and values are kept. -/
def certified [Add X] [Zero X] [Add C] [Zero C] [PseudoMetricSpace V]
    (retract : Scope → X → X) (read : X → Q → V) (forget : Scope → C → C)
    (estimate : C → Q → V) (compress : X → C) (error : X → Scope → Q → ℝ≥0)
    (bound : ∀ W S q, dist (estimate (forget S (compress W)) q) (read (retract S W) q) ≤
      error W S q) :
    ApproximationMap (AfterRetraction retract read) (Scope × Q) V
      (AfterRetraction forget estimate) (Scope × Q) V where
  state := compress
  query := id
  value := id
  error W request := error W request.1 request.2
  observe W request := bound W request.1 request.2

/-- **Every Lipschitz readout inherits the bound**, scaled by its constant. -/
theorem certified_measured [Add X] [Zero X] [Add C] [Zero C] [PseudoMetricSpace V]
    {Y : Type*} [PseudoMetricSpace Y]
    (retract : Scope → X → X) (read : X → Q → V) (forget : Scope → C → C)
    (estimate : C → Q → V) (compress : X → C) (error : X → Scope → Q → ℝ≥0)
    (bound : ∀ W S q, dist (estimate (forget S (compress W)) q) (read (retract S W) q) ≤
      error W S q)
    (readout : V → Y) (K : ℝ≥0) (stable : LipschitzWith K readout) (W : X) (S : Scope) (q : Q) :
    dist (readout (estimate (forget S (compress W)) q)) (readout (read (retract S W) q)) ≤
      (K : ℝ) * error W S q :=
  (certified retract read forget estimate compress error bound).measured_error readout K stable W
    (S, q)

end Reading

/-! ## Confidence is a Lipschitz readout -/

/-- Confidence from an evidence total, `n / (n + k)`. -/
noncomputable def confidence (k n : ℝ≥0) : ℝ≥0 := n / (n + k)

/-- **Confidence is `k⁻¹`-Lipschitz**, with no guard. -/
theorem confidence_lipschitz {k : ℝ≥0} (hk : 0 < k) : LipschitzWith k⁻¹ (confidence k) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [confidence]
  rw [NNReal.dist_eq, NNReal.dist_eq]
  push_cast
  have hk' : (0 : ℝ) < k := NNReal.coe_pos.mpr hk
  have ha : (0 : ℝ) ≤ a := a.coe_nonneg
  have hb : (0 : ℝ) ≤ b := b.coe_nonneg
  have hak : (0 : ℝ) < a + k := by linarith
  have hbk : (0 : ℝ) < b + k := by linarith
  have key : (a : ℝ) / (a + k) - b / (b + k) = k * (a - b) / ((a + k) * (b + k)) := by
    rw [div_sub_div _ _ hak.ne' hbk.ne']
    congr 1
    ring
  have hsq : (k : ℝ) * k ≤ (a + k) * (b + k) := by nlinarith
  rw [key, inv_mul_eq_div, abs_div, abs_mul, abs_of_pos hk', abs_of_pos (mul_pos hak hbk),
    div_le_div_iff₀ (mul_pos hak hbk) hk']
  nlinarith [abs_nonneg ((a : ℝ) - b)]

/-! ## One-sided bounds -/

/-- `lo` encloses `x` from below with width `w`: `lo ≤ x ≤ lo + w`.  The estimate `lo`
manufactures nothing and misses at most `w`. -/
structure Encloses (lo w x : ℝ≥0) : Prop where
  le : lo ≤ x
  le_add : x ≤ lo + w

/-- **An enclosure is a pair of bounds in the Lawvere distance `a - b`**: distance zero from the
estimate to the exact value, and at most the width back. -/
theorem encloses_iff_tsub {lo w x : ℝ≥0} : Encloses lo w x ↔ lo - x = 0 ∧ x - lo ≤ w := by
  rw [tsub_eq_zero_iff_le, tsub_le_iff_left]
  exact ⟨fun h => ⟨h.le, h.le_add⟩, fun h => ⟨h.1, h.2⟩⟩

/-- A width bounds the symmetric distance, the one `ApproximationMap` uses. -/
theorem Encloses.dist_le {lo w x : ℝ≥0} (h : Encloses lo w x) : dist lo x ≤ w := by
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h.le))]
  have upper := NNReal.coe_le_coe.mpr h.le_add
  rw [NNReal.coe_add] at upper
  linarith

/-- An exact value encloses itself with width zero. -/
theorem Encloses.self (x : ℝ≥0) : Encloses x 0 x := ⟨le_rfl, (add_zero x).ge⟩

/-- A larger width still encloses. -/
theorem Encloses.mono {lo w w' x : ℝ≥0} (h : Encloses lo w x) (hw : w ≤ w') :
    Encloses lo w' x :=
  ⟨h.le, h.le_add.trans (add_le_add le_rfl hw)⟩

/-- **Revision adds enclosures**: constant 1 in each argument, and the widths add. -/
theorem Encloses.add {lo₁ w₁ x₁ lo₂ w₂ x₂ : ℝ≥0} (h₁ : Encloses lo₁ w₁ x₁)
    (h₂ : Encloses lo₂ w₂ x₂) : Encloses (lo₁ + lo₂) (w₁ + w₂) (x₁ + x₂) :=
  ⟨add_le_add h₁.le h₂.le, (add_le_add h₁.le_add h₂.le_add).trans_eq (by ring)⟩

/-- The width of a deduction: each premise's width scaled by the other premise's estimate, plus
the product of the widths. -/
def mulWidth (lo₁ w₁ lo₂ w₂ : ℝ≥0) : ℝ≥0 := lo₁ * w₂ + w₁ * lo₂ + w₁ * w₂

/-- **Deduction multiplies enclosures.**  The sensitivity of the product to the second premise is
the first premise's estimate, and conversely. -/
theorem Encloses.mul {lo₁ w₁ x₁ lo₂ w₂ x₂ : ℝ≥0} (h₁ : Encloses lo₁ w₁ x₁)
    (h₂ : Encloses lo₂ w₂ x₂) : Encloses (lo₁ * lo₂) (mulWidth lo₁ w₁ lo₂ w₂) (x₁ * x₂) :=
  ⟨mul_le_mul' h₁.le h₂.le,
    (mul_le_mul' h₁.le_add h₂.le_add).trans_eq (by unfold mulWidth; ring)⟩

/-! ## The consumer: a threshold guard -/

/-- The verdict of a threshold guard. -/
inductive Verdict where
  /-- Commits: the exact value is at least the threshold. -/
  | above
  /-- Commits: the exact value is below the threshold. -/
  | below
  /-- Does not commit. -/
  | undecided
  deriving DecidableEq

/-- The decision a verdict commits: `some true` for at least the threshold, `some false` for below
it, and none when undecided. -/
def Verdict.decision : Verdict → Option Bool
  | .above => some true
  | .below => some false
  | .undecided => none

section Guard

variable {α : Type*} [LinearOrder α]

/-- **A threshold guard on a certified interval `[lo, hi]`**: it commits only when the whole
interval lies on one side of `θ`. -/
def thresholdGuard (θ lo hi : α) : Verdict :=
  if θ ≤ lo then .above else if hi < θ then .below else .undecided

/-- **The guard never commits wrongly.** -/
theorem thresholdGuard_sound {θ lo hi x : α} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    (thresholdGuard θ lo hi = .above → θ ≤ x) ∧ (thresholdGuard θ lo hi = .below → x < θ) := by
  unfold thresholdGuard
  by_cases h₁ : θ ≤ lo
  · rw [if_pos h₁]
    exact ⟨fun _ => h₁.trans hlo, (fun h => by cases h)⟩
  · rw [if_neg h₁]
    by_cases h₂ : hi < θ
    · rw [if_pos h₂]
      exact ⟨(fun h => by cases h), fun _ => hhi.trans_lt h₂⟩
    · rw [if_neg h₂]
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

/-- **A committed decision is the exact one.** -/
theorem thresholdGuard_decision_sound {θ lo hi x : α} (hlo : lo ≤ x) (hhi : x ≤ hi) {b : Bool}
    (h : (thresholdGuard θ lo hi).decision = some b) : b = decide (θ ≤ x) := by
  obtain ⟨above, below⟩ := thresholdGuard_sound (θ := θ) hlo hhi
  cases hv : thresholdGuard θ lo hi with
  | above =>
      rw [hv] at h
      cases h
      exact (decide_eq_true (above hv)).symm
  | below =>
      rw [hv] at h
      cases h
      exact (decide_eq_false (not_le.mpr (below hv))).symm
  | undecided =>
      rw [hv] at h
      cases h

/-- The guard is undecided exactly when the threshold lies inside the interval. -/
theorem thresholdGuard_undecided_iff {θ lo hi : α} :
    thresholdGuard θ lo hi = .undecided ↔ lo < θ ∧ θ ≤ hi := by
  unfold thresholdGuard
  by_cases h₁ : θ ≤ lo
  · rw [if_pos h₁]
    exact ⟨(fun h => by cases h), fun h => absurd h.1 (not_lt.mpr h₁)⟩
  · rw [if_neg h₁]
    by_cases h₂ : hi < θ
    · rw [if_pos h₂]
      exact ⟨(fun h => by cases h), fun h => absurd h.2 (not_le.mpr h₂)⟩
    · rw [if_neg h₂]
      exact ⟨fun _ => ⟨not_le.mp h₁, not_lt.mp h₂⟩, fun _ => rfl⟩

/-- **A zero-width interval always decides.** -/
theorem thresholdGuard_point_decides (θ x : α) : thresholdGuard θ x x ≠ .undecided := by
  rw [Ne, thresholdGuard_undecided_iff]
  exact fun h => lt_irrefl x (h.1.trans_le h.2)

/-- **At the threshold**: an interval starting at the threshold commits `above`; one ending at the
threshold and starting below it stays undecided. -/
theorem thresholdGuard_at_threshold {θ lo hi : α} (hlo : lo < θ) :
    thresholdGuard θ θ hi = .above ∧ thresholdGuard θ lo θ = .undecided :=
  ⟨if_pos le_rfl, thresholdGuard_undecided_iff.mpr ⟨hlo, le_rfl⟩⟩

end Guard

/-! ## Strength near a zero denominator -/

section Strength

/-- The lower corner of strength: the fewest positives and the most negatives the bounds allow. -/
noncomputable def strengthLo (e w : Evidence ℝ≥0) : ℝ≥0 := e.pos / (e.pos + e.neg + w.neg)

/-- The upper corner of strength: the most positives and the fewest negatives the bounds allow. -/
noncomputable def strengthHi (e w : Evidence ℝ≥0) : ℝ≥0 := (e.pos + w.pos) / (e.pos + w.pos + e.neg)

/-- **Strength lies between the corners.**  If the held counts `e` enclose the exact counts `x`
with widths `w` in both polarities and do not both vanish, then the exact total is nonzero and its
strength lies between the corners. -/
theorem strength_mem_corners {e w x : Evidence ℝ≥0} (hpos : Encloses e.pos w.pos x.pos)
    (hneg : Encloses e.neg w.neg x.neg) (held : e.pos + e.neg ≠ 0) :
    x.total ≠ 0 ∧ strengthLo e w ≤ x.strength ∧ x.strength ≤ strengthHi e w := by
  have heldPos : 0 < e.pos + e.neg := pos_iff_ne_zero.mpr held
  have hx : 0 < x.pos + x.neg := heldPos.trans_le (add_le_add hpos.le hneg.le)
  have hlo : 0 < e.pos + e.neg + w.neg := heldPos.trans_le le_self_add
  have hhi : 0 < e.pos + w.pos + e.neg :=
    heldPos.trans_le (add_le_add le_self_add le_rfl)
  refine ⟨hx.ne', ?_, ?_⟩
  · unfold strengthLo Evidence.strength Evidence.total
    rw [div_le_div_iff₀ hlo hx]
    calc e.pos * (x.pos + x.neg) = e.pos * x.pos + e.pos * x.neg := mul_add _ _ _
      _ ≤ e.pos * x.pos + x.pos * (e.neg + w.neg) :=
          add_le_add le_rfl (mul_le_mul' hpos.le hneg.le_add)
      _ = x.pos * (e.pos + e.neg + w.neg) := by ring
  · unfold strengthHi Evidence.strength Evidence.total
    rw [div_le_div_iff₀ hx hhi]
    calc x.pos * (e.pos + w.pos + e.neg) = x.pos * (e.pos + w.pos) + x.pos * e.neg := mul_add _ _ _
      _ ≤ x.pos * (e.pos + w.pos) + (e.pos + w.pos) * x.neg :=
          add_le_add le_rfl (mul_le_mul' hpos.le_add hneg.le)
      _ = (e.pos + w.pos) * (x.pos + x.neg) := by ring

/-- **The strength guard.**  With no held evidence the exact readout may be undetermined, so it is
undecided; otherwise it guards the corners. -/
noncomputable def strengthGuard (θ : ℝ≥0) (e w : Evidence ℝ≥0) : Verdict :=
  if e.pos + e.neg = 0 then .undecided else thresholdGuard θ (strengthLo e w) (strengthHi e w)

/-- **The strength guard never commits wrongly, and never commits on an undetermined readout.** -/
theorem strengthGuard_sound {θ : ℝ≥0} {e w x : Evidence ℝ≥0} (hpos : Encloses e.pos w.pos x.pos)
    (hneg : Encloses e.neg w.neg x.neg) :
    (strengthGuard θ e w = .above → ∃ s, x.readout = some s ∧ θ ≤ s) ∧
      (strengthGuard θ e w = .below → ∃ s, x.readout = some s ∧ s < θ) := by
  unfold strengthGuard
  by_cases h0 : e.pos + e.neg = 0
  · rw [if_pos h0]
    exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  · rw [if_neg h0]
    obtain ⟨hx, hlo, hhi⟩ := strength_mem_corners hpos hneg h0
    have hread : x.readout = some x.strength := by
      unfold Evidence.readout
      rw [if_neg hx]
    obtain ⟨above, below⟩ := thresholdGuard_sound (θ := θ) hlo hhi
    exact ⟨fun h => ⟨_, hread, above h⟩, fun h => ⟨_, hread, below h⟩⟩

/-- **A zero denominator.**  The held counts `(0, 0)` with widths `(1, 1)` enclose the exact counts
`(0, 0)`, whose readout is undetermined, and `(1, 0)`, whose strength is one.  Division gives the
held counts strength `0`, which a guard on the point estimate would commit on; the strength guard is
undecided at every threshold. -/
theorem zero_denominator :
    Encloses 0 1 0 ∧ Encloses 0 1 1 ∧ (⟨0, 0⟩ : Evidence ℝ≥0).readout = none ∧
      (⟨1, 0⟩ : Evidence ℝ≥0).readout = some 1 ∧ (⟨0, 0⟩ : Evidence ℝ≥0).strength = 0 ∧
      ∀ θ, strengthGuard θ ⟨0, 0⟩ ⟨1, 1⟩ = .undecided := by
  refine ⟨⟨le_rfl, zero_le⟩, ⟨zero_le, (zero_add 1).ge⟩, ?_, ?_, ?_, ?_⟩
  · have empty : (⟨0, 0⟩ : Evidence ℝ≥0).total = 0 := by simp [Evidence.total]
    unfold Evidence.readout
    rw [if_pos empty]
  · have held : (⟨1, 0⟩ : Evidence ℝ≥0).total ≠ 0 := by simp [Evidence.total]
    unfold Evidence.readout
    rw [if_neg held]
    congr 1
    simp [Evidence.strength, Evidence.total]
  · simp [Evidence.strength]
  · intro θ
    simp [strengthGuard]

/-- **Strength has no global Lipschitz constant** for the count distance, even on evidence with
nonzero total. -/
theorem strength_not_lipschitz (K : ℝ≥0) :
    ∃ e e' : Evidence ℝ≥0, e.total ≠ 0 ∧ e'.total ≠ 0 ∧
      (K : ℝ) * (dist e.pos e'.pos + dist e.neg e'.neg) < dist e.strength e'.strength := by
  set δ : ℝ≥0 := (2 * (K + 1))⁻¹ with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have s₁ : (⟨δ, 0⟩ : Evidence ℝ≥0).strength = 1 := by
    simp [Evidence.strength, Evidence.total, hδpos.ne']
  have s₂ : (⟨0, δ⟩ : Evidence ℝ≥0).strength = 0 := by
    simp [Evidence.strength]
  refine ⟨⟨δ, 0⟩, ⟨0, δ⟩, by simp [Evidence.total, hδpos.ne'],
    by simp [Evidence.total, hδpos.ne'], ?_⟩
  rw [s₁, s₂]
  have hδ₁ : (δ : ℝ) * (2 * ((K : ℝ) + 1)) = 1 := by
    rw [hδ]
    push_cast
    exact inv_mul_cancel₀ (by positivity)
  have hδr : (0 : ℝ) < δ := NNReal.coe_pos.mpr hδpos
  have h₂ : (K : ℝ) * ((δ : ℝ) + δ) = 1 - 2 * δ := by linear_combination hδ₁
  simp only [NNReal.dist_eq, NNReal.coe_zero, NNReal.coe_one, sub_zero, zero_sub, abs_neg,
    abs_of_pos hδr, abs_one]
  rw [h₂]
  linarith

/-- **A count estimate that manufactures nothing can manufacture strength.**  The held counts
`(1, 0)` lie below the exact counts `(1, 1)` in both polarities, and their strength is higher. -/
theorem strength_manufactured :
    Encloses 1 0 1 ∧ Encloses 0 1 1 ∧
      (⟨1, 1⟩ : Evidence ℝ≥0).strength < (⟨1, 0⟩ : Evidence ℝ≥0).strength := by
  refine ⟨Encloses.self 1, ⟨zero_le, (zero_add 1).ge⟩, ?_⟩
  have h₁ : (⟨1, 1⟩ : Evidence ℝ≥0).strength = 2⁻¹ := by
    simp [Evidence.strength, Evidence.total, one_add_one_eq_two]
  have h₂ : (⟨1, 0⟩ : Evidence ℝ≥0).strength = 1 := by
    simp [Evidence.strength, Evidence.total]
  rw [h₁, h₂, ← NNReal.coe_lt_coe]
  norm_num

end Strength

/-! ## Two contracts -/

section Contracts

variable {Y Z X C Scope Q V : Type*}

/-- **Belief retraction**: every observable reading of the forgotten state agrees with the reading
of the state recomputed without the scope. -/
def BeliefRetraction (forget retract : Scope → Y → Y) (read : Y → Q → V) : Prop :=
  ∀ S W q, read (forget S W) q = read (retract S W) q

/-- **Whole-state erasure**: the retained state is the recomputed state. -/
def StateErasure (forget retract : Scope → Y → Y) : Prop :=
  ∀ S W, forget S W = retract S W

/-- **Erasure up to recomputation**: two states that agree once the scope is removed cannot be told
apart after forgetting it. -/
def ErasesUpToRecomputation (forget : Scope → X → Z) (retract : Scope → X → X) : Prop :=
  ∀ S W W', retract S W = retract S W' → forget S W = forget S W'

/-- Whole-state erasure gives belief retraction for every reading. -/
theorem StateErasure.beliefRetraction {forget retract : Scope → Y → Y}
    (h : StateErasure forget retract) (read : Y → Q → V) : BeliefRetraction forget retract read :=
  fun S W q => by rw [h S W]

/-- Whole-state erasure gives erasure up to recomputation. -/
theorem StateErasure.erasesUpToRecomputation {forget retract : Scope → Y → Y}
    (h : StateErasure forget retract) : ErasesUpToRecomputation forget retract :=
  fun S W W' same => by rw [h S W, h S W', same]

/-- **An approximation that leaks nothing and is exact on clean states is exact.**  If forgetting on
compressed states cannot tell apart two states that agree once the scope is removed, and the
approximation is exact on the states the retraction fixes, then it is exact everywhere. -/
theorem exact_of_erases_of_vacuous (retract : Scope → X → X) (forget : Scope → C → C)
    (compress : X → C) (read : X → Q → V) (estimate : C → Q → V)
    (idempotent : ∀ S W, retract S (retract S W) = retract S W)
    (erases : ErasesUpToRecomputation (fun S W => forget S (compress W)) retract)
    (vacuous : ∀ S W, retract S W = W → ∀ q, estimate (forget S (compress W)) q = read W q)
    (S : Scope) (W : X) (q : Q) :
    estimate (forget S (compress W)) q = read (retract S W) q := by
  have same : forget S (compress W) = forget S (compress (retract S W)) :=
    erases S W (retract S W) (idempotent S W).symm
  rw [same]
  exact vacuous S (retract S W) (idempotent S W) q

/-- **An inexact approximation that is exact on clean states keeps information about the withdrawn
sources**: some two states that agree once the scope is removed are told apart after forgetting. -/
theorem leaks_of_inexact (retract : Scope → X → X) (forget : Scope → C → C)
    (compress : X → C) (read : X → Q → V) (estimate : C → Q → V)
    (idempotent : ∀ S W, retract S (retract S W) = retract S W)
    (vacuous : ∀ S W, retract S W = W → ∀ q, estimate (forget S (compress W)) q = read W q)
    {S : Scope} {W : X} {q : Q}
    (inexact : estimate (forget S (compress W)) q ≠ read (retract S W) q) :
    ¬ ErasesUpToRecomputation (fun S W => forget S (compress W)) retract :=
  fun erases => inexact
    (exact_of_erases_of_vacuous retract forget compress read estimate idempotent erases vacuous
      S W q)

end Contracts

end Mettapedia.PLN.WorldModel.ApproximateRetraction

open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms certified
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms certified_measured
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms confidence_lipschitz
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms encloses_iff_tsub
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms Encloses.dist_le
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms Encloses.add
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms Encloses.mul
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms thresholdGuard_sound
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms thresholdGuard_decision_sound
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms thresholdGuard_undecided_iff
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms thresholdGuard_point_decides
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms thresholdGuard_at_threshold
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms strength_mem_corners
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms strengthGuard_sound
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms zero_denominator
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms strength_not_lipschitz
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms strength_manufactured
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms exact_of_erases_of_vacuous
open Mettapedia.PLN.WorldModel.ApproximateRetraction in
#print axioms leaks_of_inexact
