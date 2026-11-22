import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Contention
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Permissions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalHistories
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsGrades

/-!
# Intervention on the step: restriction of weights at a space handle

An intervention changes the weights of candidates (Meredith, Def. 3.1). A **restriction** keeps
the weight of the candidates a constraint admits and sends the others to `0` (`restrictWeight`):
it restricts and never overrides (Observation 4.6).

## Laws

* **Composition by conjunction** (`restrictWeight_restrictWeight`), hence commutation
  (`restrictWeight_comm`); the trivial constraint is the identity (`restrictWeight_true`)
  (Prop. 4.8).
* **Lowering is exact on a static alphabet** (`prob_restrictWeight`): the jump chain with restricted
  weights is the jump chain of the alphabet filtered by the constraint once, before running
  (Prop. 4.4). The first-order step's alphabets are static; nothing can bring a firing into the
  program after elaboration.
* **Fatality** (`restricted_total_eq_zero_iff`): with positive weights, the restricted race total
  at a configuration is `0` exactly when no admitted candidate satisfies the constraint; the race
  starves there (Remark 5.8).
* **A hard intervention discards the weights** (`prob_hard`): when one admitted candidate satisfies
  the constraint, it fires with probability `1`, whatever the weights (Theorem 5.7's mechanism).
* **Autonomy** (`autonomy`): on a composition of two rate systems, restricting one side changes a
  causal history's likelihood only through that side's factor.

## A do at a space handle needs the `send` right there

`DoAt space label h φ` constrains every make at the space `h` to satisfy `φ`: the scope is named by
a handle, not by a bound name. A firing permitted under rights without `send` at `h` makes nothing
there, so every do at `h` admits it and leaves its weight unchanged (`doAt_of_no_send`,
`restrictWeight_doAt_of_no_send`): **a do at `h` reaches only the firings that hold `send` at `h`**.

## A context with an absence guard performs a hard do (`Controls.context_performs_do`)

In the race of `Contention.Controls`, the hard do "only `racer`" and the one-atom context that adds
`p` give `racer` probability `1` alike. Meredith's Prop. 3.3 makes hard intervention white-box over
the positive reals; on the step, an absence guard lets a context perform it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Intervention

open AnnotatedRuns (Firing)
open Race (admitted total prob)
open MeTTaCalculus.InteractionTypes (Rights Facet)

universe uT uS uO uN

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Restriction of weights -/

section Restriction

open Classical in
/-- **A restriction**: the weight of a candidate the constraint admits, `0` otherwise. -/
noncomputable def restrictWeight (keep : Firing T S O → Prop) (weight : Firing T S O → ℝ)
    (f : Firing T S O) : ℝ :=
  if keep f then weight f else 0

omit [DecidableEq O] in
/-- **Restrictions compose by conjunction.** -/
theorem restrictWeight_restrictWeight (first second : Firing T S O → Prop)
    (weight : Firing T S O → ℝ) :
    restrictWeight first (restrictWeight second weight) =
      restrictWeight (fun f => first f ∧ second f) weight := by
  funext f
  unfold restrictWeight
  by_cases h₁ : first f <;> by_cases h₂ : second f <;> simp [h₁, h₂]

omit [DecidableEq O] in
theorem restrictWeight_comm (first second : Firing T S O → Prop) (weight : Firing T S O → ℝ) :
    restrictWeight first (restrictWeight second weight) =
      restrictWeight second (restrictWeight first weight) := by
  rw [restrictWeight_restrictWeight, restrictWeight_restrictWeight]
  congr 1
  funext f
  exact propext and_comm

omit [DecidableEq O] in
/-- **The trivial constraint is the identity.** -/
theorem restrictWeight_true (weight : Firing T S O → ℝ) :
    restrictWeight (fun _ => True) weight = weight := by
  funext f
  simp [restrictWeight]

omit [DecidableEq O] in
open Classical in
/-- Summing restricted values over a list is summing over the admitted members. -/
theorem sum_ite_eq_sum_filter {X : Type*} (keep : X → Prop) (g : X → ℝ) :
    ∀ L : List X, (L.map fun x => if keep x then g x else 0).sum =
      ((L.filter fun x => decide (keep x)).map g).sum
  | [] => rfl
  | x :: rest => by
      by_cases hx : keep x
      · simp [hx, sum_ite_eq_sum_filter keep g rest]
      · simp [hx, sum_ite_eq_sum_filter keep g rest]

variable {A : SubstitutionAction T S} {label : O → T} {alphabet : List (Firing T S O)}

open Classical in
/-- The admitted members of a filtered alphabet are the filtered admitted members. -/
theorem admitted_filter (keep : Firing T S O → Prop) (C : Configuration T O) :
    admitted A label (alphabet.filter fun f => decide (keep f)) C =
      (admitted A label alphabet C).filter fun f => decide (keep f) := by
  rw [Contention.admitted_eq, Contention.admitted_eq, List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro f member
  by_cases hk : keep f <;> by_cases hv : f.Valid A label C <;> simp [hk, hv, member, List.mem_filter]

open Classical in
/-- **Lowering is exact on a static alphabet**: the jump chain with restricted weights is the jump
chain of the alphabet filtered by the constraint. -/
theorem prob_restrictWeight {L : Type*} (keep : Firing T S O → Prop) (name : Firing T S O → L)
    (weight : Firing T S O → ℝ) (C : Configuration T O) (ℓ : L) (E : Set (Configuration T O)) :
    prob A label alphabet name (restrictWeight keep weight) C ℓ E =
      prob A label (alphabet.filter fun f => decide (keep f)) name weight C ℓ E := by
  unfold prob total
  rw [admitted_filter]
  congr 1
  · rw [← sum_ite_eq_sum_filter keep]
    congr 1
    apply List.map_congr_left
    intro f _
    by_cases hk : keep f <;> simp [restrictWeight, hk]
  · rw [← sum_ite_eq_sum_filter keep]
    rfl

open Classical in
/-- **Fatality**: with positive weights, the restricted race total is `0` exactly when no admitted
candidate satisfies the constraint. -/
theorem restricted_total_eq_zero_iff (keep : Firing T S O → Prop) {weight : Firing T S O → ℝ}
    (positive : ∀ f, 0 < weight f) (C : Configuration T O) :
    total A label alphabet (restrictWeight keep weight) C = 0 ↔
      ∀ f ∈ admitted A label alphabet C, ¬ keep f := by
  unfold total
  have rewrite : ((admitted A label alphabet C).map (restrictWeight keep weight)).sum =
      (((admitted A label alphabet C).filter fun f => decide (keep f)).map weight).sum :=
    sum_ite_eq_sum_filter keep weight _
  rw [rewrite]
  constructor
  · intro zero f member kept
    have inFilter : f ∈ (admitted A label alphabet C).filter fun f => decide (keep f) :=
      List.mem_filter.mpr ⟨member, decide_eq_true kept⟩
    have pos : 0 < (((admitted A label alphabet C).filter fun f => decide (keep f)).map weight).sum := by
      apply List.sum_pos
      · intro x mem
        obtain ⟨g, _, rfl⟩ := List.mem_map.mp mem
        exact positive g
      · intro empty
        have : weight f ∈ ((admitted A label alphabet C).filter fun f => decide (keep f)).map weight :=
          List.mem_map.mpr ⟨f, inFilter, rfl⟩
        rw [empty] at this
        simp at this
    linarith
  · intro none
    have empty : ((admitted A label alphabet C).filter fun f => decide (keep f)) = [] :=
      List.filter_eq_nil_iff.mpr fun f member => by simpa using none f member
    rw [empty]
    rfl

open Classical in
/-- **A hard intervention discards the weights**: when exactly one admitted candidate satisfies the
constraint, it fires with probability `1`. -/
theorem prob_hard (keep : Firing T S O → Prop) {weight : Firing T S O → ℝ} {C : Configuration T O}
    {f : Firing T S O} (single : (admitted A label alphabet C).filter (fun g => decide (keep g)) = [f])
    (positive : 0 < weight f) :
    prob A label alphabet id (restrictWeight keep weight) C f Set.univ = 1 := by
  rw [prob_restrictWeight, ← admitted_filter] at *
  unfold prob total
  rw [single]
  simp [positive.ne']

end Restriction

/-! ## Autonomy on causal histories -/

section Autonomy

open CausalHistories

variable {X : Type*} {Y : Type*} (stepA : X → List (X × ℝ)) (stepB : Y → List (Y × ℝ))

/-- **Autonomy**: restricting one side of a composition changes a causal history's likelihood only
through that side's own factor. -/
theorem autonomy (keep : X → X × ℝ → Bool) (positiveA : Positive stepA) (positiveB : Positive stepB)
    {a : X} {b : Y} {α : List (X × ℝ)} {β : List (Y × ℝ)}
    (maximalA : Maximal (restrict stepA keep) a α) (maximalB : Maximal stepB b β) :
    ((shuffles α β).map fun σ =>
        pathProb (par (restrict stepA keep) stepB) (a, b) (realize a b σ)).sum =
      pathProb (restrict stepA keep) a α * pathProb stepB b β :=
  history_factorizes _ _ (restrict_positive positiveA keep) positiveB maximalA maximalB

end Autonomy

/-! ## The resolution algebra decides whether an arrival can force a race -/

section Dichotomy

open Mettapedia.GSLT.Core (raceShare raceTotal maxSelector)

/-- **Normalized shares against maximum selection** (Prop. 3.3's two halves). Over the positive
reals an arriving competitor never refuses a candidate of positive weight: its normalized share
stays positive. Under maximum selection, an idempotent resolution, the same arrival refuses it
(`AnnotatedRuns.argmax_changed_by_arrival`). -/
theorem forcing_dichotomy {Candidate : Type*} (weight : Candidate → ℕ) {low high : Candidate}
    (outweighed : weight low < weight high) (positive : 0 < weight low) :
    0 < raceShare (fun c => (weight c : ℝ)) {low, high} low ∧
      low ∈ maxSelector weight {low} ∧ low ∉ maxSelector weight {low, high} := by
  refine ⟨?_, AnnotatedRuns.argmax_changed_by_arrival weight outweighed⟩
  have hl : (0 : ℝ) < weight low := by exact_mod_cast positive
  have hh : (0 : ℝ) ≤ weight high := Nat.cast_nonneg _
  unfold raceShare raceTotal
  refine div_pos hl ?_
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  linarith

end Dichotomy

/-! ## A do at a space handle -/

section Handles

variable {H : Type uN} (space : O → H) (label : O → T)

/-- **A do at the space `h`**: every make of the firing at `h` satisfies `φ`. -/
def DoAt (h : H) (φ : T → Prop) (f : Firing T S O) : Prop :=
  ∀ o ∈ f.selection.made, space o = h → φ (label o)

omit [DecidableEq O] in
/-- Two dos at one handle are one do with the conjoined constraint. -/
theorem doAt_and (h : H) (φ ψ : T → Prop) (f : Firing T S O) :
    (DoAt space label h φ f ∧ DoAt space label h ψ f) ↔
      DoAt space label h (fun t => φ t ∧ ψ t) f :=
  ⟨fun both o made atH => ⟨both.1 o made atH, both.2 o made atH⟩,
    fun joint => ⟨fun o made atH => (joint o made atH).1, fun o made atH => (joint o made atH).2⟩⟩

omit [DecidableEq O] in
/-- The trivial do admits every firing. -/
theorem doAt_true (h : H) (f : Firing T S O) : DoAt space label h (fun _ => True) f :=
  fun _ _ _ => trivial

variable {A : SubstitutionAction T S} (Γ : Rights H)

/-- **A do at `h` admits every firing that lacks `send` at `h`**: such a firing, permitted by the
rights, makes nothing at `h`. -/
theorem doAt_of_no_send {C : Configuration T O} {f : Firing T S O}
    (permitted : Permissions.Permitted (AnnotatedRuns.firstOrder A label).toStep space Γ (s := C) f)
    {h : H} (denied : Γ h .send = false) (φ : T → Prop) : DoAt space label h φ f := by
  intro o made atH
  have allowed := permitted.made o
    (show o ∈ (f.selection.commit (T := H)).made by simpa [Selection.commit] using made)
  simp [atH, denied] at allowed

/-- **A do at `h` leaves the weight of every firing without `send` at `h` unchanged.** -/
theorem restrictWeight_doAt_of_no_send {C : Configuration T O} {f : Firing T S O}
    (permitted : Permissions.Permitted (AnnotatedRuns.firstOrder A label).toStep space Γ (s := C) f)
    {h : H} (denied : Γ h .send = false) (φ : T → Prop) (weight : Firing T S O → ℝ) :
    restrictWeight (DoAt space label h φ) weight f = weight f := by
  unfold restrictWeight
  rw [if_pos (doAt_of_no_send space label Γ permitted denied φ)]

end Handles

/-! ## Controls -/

namespace Controls

open Contention.Controls

variable {S : Type uS} (A : SubstitutionAction Tok S) (weight : Firing Tok S Site → ℝ)

open Classical in
theorem only_racer :
    (admitted A label (race (S := S)) D0).filter (fun g => decide (g = racer)) = [racer] := by
  rw [admitted_D0]
  simp [vetoed_ne_racer]

/-- **The hard do "only `racer`"** gives `racer` probability `1` at `D0`. -/
theorem hard_do (positiveR : 0 < weight racer) :
    prob A label race id (restrictWeight (fun g => g = racer) weight) D0 racer Set.univ = 1 :=
  prob_hard _ (only_racer A) positiveR

/-- **A context with an absence guard performs the hard do**: the white-box intervention and the
one-atom context give `racer` the same probability `1`, where the unintervened race gives it
`w_r/(w_r+w_v) < 1`. -/
theorem context_performs_do (positiveR : 0 < weight racer) (positiveV : 0 < weight vetoed) :
    prob A label race id (restrictWeight (fun g => g = racer) weight) D0 racer Set.univ =
        prob A label race id weight (Race.addAtom D0 .mp) racer Set.univ ∧
      prob A label race id weight D0 racer Set.univ < 1 := by
  obtain ⟨_, below, forced⟩ := forcing_control A weight positiveR positiveV
  exact ⟨(hard_do A weight positiveR).trans forced.symm, below⟩

open Classical in
/-- **Restriction, not override**: a do that excludes every admitted candidate starves the race;
nothing has positive weight there. -/
theorem fatal_do (positive : ∀ f, 0 < weight f) :
    total A label race (restrictWeight (fun g => g ≠ racer ∧ g ≠ vetoed) weight) D0 = 0 := by
  rw [restricted_total_eq_zero_iff _ positive, admitted_D0]
  intro f member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp

end Controls

#print axioms restrictWeight_restrictWeight
#print axioms restrictWeight_comm
#print axioms restrictWeight_true
#print axioms admitted_filter
#print axioms prob_restrictWeight
#print axioms restricted_total_eq_zero_iff
#print axioms prob_hard
#print axioms autonomy
#print axioms forcing_dichotomy
#print axioms doAt_and
#print axioms doAt_of_no_send
#print axioms restrictWeight_doAt_of_no_send
#print axioms Controls.hard_do
#print axioms Controls.context_performs_do
#print axioms Controls.fatal_do

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Intervention
