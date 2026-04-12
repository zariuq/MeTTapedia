import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure

/-!
# Markov de Finetti Recurrence (Active Minimal Surface)

Minimal recurrence interface used by the active Fortini/anchor modules.
-/

noncomputable section

namespace Mettapedia.Logic

open MeasureTheory

namespace MarkovDeFinettiRecurrence

variable {k : ℕ}

def cylinder (xs : List (Fin k)) : Set (ℕ → Fin k) :=
  ⋂ i : Fin xs.length, { ω | ω i.1 = xs[i.1] }

def returnEvent (n : ℕ) : Set (ℕ → Fin k) :=
  { ω | ω n = ω 0 }

def recurrentEvent : Set (ℕ → Fin k) :=
  ⋂ N : ℕ, ⋃ n ≥ N, returnEvent (k := k) n

/-- `recurrentEvent` means infinitely many returns to the dynamic anchor `ω 0`. -/
lemma mem_recurrentEvent_iff_infinite_returns_to_start (ω : ℕ → Fin k) :
    ω ∈ recurrentEvent (k := k) ↔ Set.Infinite {t : ℕ | ω t = ω 0} := by
  constructor
  · intro hrec
    rw [Set.infinite_iff_exists_gt]
    intro a
    have hrec' : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ω n = ω 0 := by
      simpa [recurrentEvent, returnEvent, Set.mem_setOf_eq] using hrec
    rcases hrec' (a + 1) with ⟨n, hnge, hne⟩
    refine ⟨n, hne, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self a) hnge
  · intro hinf
    have hgt : ∀ a : ℕ, ∃ b ∈ ({t : ℕ | ω t = ω 0}), a < b := by
      simpa using (Set.infinite_iff_exists_gt.mp hinf)
    have hrec' : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ω n = ω 0 := by
      intro N
      rcases hgt N with ⟨n, hmem, hlt⟩
      exact ⟨n, Nat.le_of_lt hlt, hmem⟩
    simpa [recurrentEvent, returnEvent, Set.mem_setOf_eq] using hrec'

lemma measurableSet_returnEvent (n : ℕ) :
    MeasurableSet (returnEvent (k := k) n) := by
  simpa [returnEvent, Set.preimage, Set.setOf_eq_eq_singleton] using
    (measurableSet_eq_fun (measurable_pi_apply n) (measurable_pi_apply 0))

lemma measurableSet_recurrentEvent :
    MeasurableSet (recurrentEvent (k := k)) := by
  refine MeasurableSet.iInter ?_
  intro N
  refine MeasurableSet.iUnion ?_
  intro n
  refine MeasurableSet.iUnion ?_
  intro _
  exact measurableSet_returnEvent (k := k) n

/-- Prefix-measure recurrence interface for Markov de Finetti. -/
def MarkovRecurrentPrefixMeasure
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
    (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
    P (recurrentEvent (k := k)) = 1

/-- Strong row-wise recurrence interface: each fixed anchor state is visited
infinitely often almost surely under one extension measure. -/
def MarkovRowRecurrentPrefixMeasure
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
    (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
    (∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})

theorem ae_infinite_returns_to_start_of_recurrentEvent
    (P : Measure (ℕ → Fin k)) (hP : IsProbabilityMeasure P)
    (hrec : P (recurrentEvent (k := k)) = 1) :
    ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0} := by
  letI : IsProbabilityMeasure P := hP
  have haeRec : ∀ᵐ ω ∂P, ω ∈ recurrentEvent (k := k) := by
    exact (mem_ae_iff_prob_eq_one (μ := P) (measurableSet_recurrentEvent (k := k))).2 hrec
  exact haeRec.mono (fun ω hω =>
    (mem_recurrentEvent_iff_infinite_returns_to_start (k := k) ω).1 hω)

theorem MarkovRecurrentPrefixMeasure.exists_extension_ae_infinite_returns_to_start
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k))
    (hrecμ : MarkovRecurrentPrefixMeasure (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0}) := by
  rcases hrecμ with ⟨P, hP, hrep, hrec⟩
  refine ⟨P, hP, hrep, ?_⟩
  exact ae_infinite_returns_to_start_of_recurrentEvent (k := k) P hP hrec

theorem MarkovRowRecurrentPrefixMeasure.ae_infinite_visits
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k))
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) := by
  exact hrow

theorem MarkovRowRecurrentPrefixMeasure.to_MarkovRecurrentPrefixMeasure
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k))
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    MarkovRecurrentPrefixMeasure (k := k) μ := by
  rcases hrow with ⟨P, hP, hrep, hrows⟩
  letI : IsProbabilityMeasure P := hP
  have hallRows : ∀ᵐ ω ∂P, ∀ i : Fin k, Set.Infinite {t : ℕ | ω t = i} :=
    ae_all_iff.2 hrows
  have hstartInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0} := by
    filter_upwards [hallRows] with ω hω
    exact hω (ω 0)
  have hrecAe : ∀ᵐ ω ∂P, ω ∈ recurrentEvent (k := k) := by
    filter_upwards [hstartInf] with ω hω
    exact (mem_recurrentEvent_iff_infinite_returns_to_start (k := k) ω).2 hω
  have hrec : P (recurrentEvent (k := k)) = 1 :=
    (mem_ae_iff_prob_eq_one (μ := P) (measurableSet_recurrentEvent (k := k))).1 hrecAe
  exact ⟨P, hP, hrep, hrec⟩

/-! ## Class-Based Recurrence (Generalization)

The original recurrence definitions anchor on the starting state ω 0.
This section generalizes to recurrence within a designated class C ⊆ Fin k,
enabling the representation theorem for multi-component Markov systems.
-/

section ClassRecurrence

variable (C : Set (Fin k))

/-- Return event to any state in class C -/
def returnToClassEvent (n : ℕ) : Set (ℕ → Fin k) :=
  { ω | ω n ∈ C }

/-- Recurrent event within class C: infinitely many visits to some state in C -/
def recurrentClassEvent : Set (ℕ → Fin k) :=
  ⋂ N : ℕ, ⋃ n ≥ N, returnToClassEvent (k := k) C n

/-- `recurrentClassEvent` means infinitely many visits to class C. -/
lemma mem_recurrentClassEvent_iff_infinite_visits_to_class (ω : ℕ → Fin k) :
    ω ∈ recurrentClassEvent (k := k) C ↔ Set.Infinite {t : ℕ | ω t ∈ C} := by
  constructor
  · intro hrec
    rw [Set.infinite_iff_exists_gt]
    intro a
    have hrec' : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ω n ∈ C := by
      simpa [recurrentClassEvent, returnToClassEvent, Set.mem_setOf_eq] using hrec
    rcases hrec' (a + 1) with ⟨n, hnge, hne⟩
    refine ⟨n, hne, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self a) hnge
  · intro hinf
    have hgt : ∀ a : ℕ, ∃ b ∈ ({t : ℕ | ω t ∈ C}), a < b := by
      simpa using (Set.infinite_iff_exists_gt.mp hinf)
    have hrec' : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ω n ∈ C := by
      intro N
      rcases hgt N with ⟨n, hmem, hlt⟩
      exact ⟨n, Nat.le_of_lt hlt, hmem⟩
    simpa [recurrentClassEvent, returnToClassEvent, Set.mem_setOf_eq] using hrec'

lemma measurableSet_returnToClassEvent (n : ℕ) (hC : MeasurableSet C) :
    MeasurableSet (returnToClassEvent (k := k) C n) := by
  simp only [returnToClassEvent]
  exact (measurable_pi_apply n) hC

lemma measurableSet_recurrentClassEvent (hC : MeasurableSet C) :
    MeasurableSet (recurrentClassEvent (k := k) C) := by
  refine MeasurableSet.iInter ?_
  intro N
  refine MeasurableSet.iUnion ?_
  intro n
  refine MeasurableSet.iUnion ?_
  intro _
  exact measurableSet_returnToClassEvent (k := k) C n hC

/-- A recurrent class is a set of states where every pair has infinitely many
    transitions between them almost surely. -/
def RecurrentClass (P : Measure (ℕ → Fin k)) : Prop :=
  C.Nonempty ∧
  ∀ i j : Fin k, i ∈ C → j ∈ C →
    ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i ∧ ω (t + 1) = j}

/-- Strong recurrence relative to a class C: if the trajectory ever enters C,
    then all states in C are visited infinitely often. -/
def StrongRecurrenceInClass (P : Measure (ℕ → Fin k)) : Prop :=
  ∀ i ∈ C, ∀ᵐ ω ∂P,
    (∃ t : ℕ, ω t ∈ C) → Set.Infinite {t : ℕ | ω t = i}

/-- Prefix-measure recurrence within a class C. -/
def MarkovRecurrentClassPrefixMeasure
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k))
    (_hC : MeasurableSet C) : Prop :=
  ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
    (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
    P (recurrentClassEvent (k := k) C) = 1

/-- Singleton class restricted to starting at a equals original recurrence. -/
theorem recurrentClassEvent_singleton_of_start (a : Fin k) (ω : ℕ → Fin k) (ha : ω 0 = a) :
    ω ∈ recurrentClassEvent (k := k) {a} ↔ ω ∈ recurrentEvent (k := k) := by
  simp only [recurrentClassEvent, returnToClassEvent, Set.mem_singleton_iff,
             recurrentEvent, returnEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro hrec N
    rcases hrec N with ⟨n, hn, heq⟩
    refine ⟨n, hn, ?_⟩
    rw [ha]
    exact heq
  · intro hrec N
    rcases hrec N with ⟨n, hn, heq⟩
    refine ⟨n, hn, ?_⟩
    rw [← ha]
    exact heq

/-- Original recurrence implies class recurrence for the full state space. -/
theorem recurrentEvent_eq_recurrentClassEvent_univ :
    recurrentEvent (k := k) ⊆ recurrentClassEvent (k := k) Set.univ := by
  intro ω hrec
  simp only [recurrentClassEvent, returnToClassEvent, Set.mem_univ, Set.mem_setOf_eq,
             Set.mem_iInter, Set.mem_iUnion, exists_prop]
  simp only [recurrentEvent, returnEvent, Set.mem_setOf_eq,
             Set.mem_iInter, Set.mem_iUnion, exists_prop] at hrec
  intro N
  rcases hrec N with ⟨n, hn, _⟩
  exact ⟨n, hn, trivial⟩

end ClassRecurrence

end MarkovDeFinettiRecurrence
end Mettapedia.Logic
