import Mettapedia.Logic.MarkovDeFinettiAnchorAdapter
import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Exchangeability.DeFinetti.Theorem
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Basic

/-!
# Markov de Finetti: Fortini-Style Bridge (Active Minimal Surface)

Minimal Fortini-facing abstractions and adapters, with no archive imports.
-/

noncomputable section

namespace Mettapedia.Logic

open MeasureTheory
open Filter
open scoped BigOperators

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovExchangeability
open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

def successorAt (ω : ℕ → Fin k) (t : ℕ) : Fin k := ω (t + 1)

def visitCountBefore (ω : ℕ → Fin k) (i : Fin k) (t : ℕ) : ℕ :=
  Finset.sum (Finset.range t) (fun s => if ω s = i then (1 : ℕ) else (0 : ℕ))

def isNthVisitTime (ω : ℕ → Fin k) (i : Fin k) (n t : ℕ) : Prop :=
  ω t = i ∧ visitCountBefore (k := k) ω i t = n

def nthVisitTimeExists (ω : ℕ → Fin k) (i : Fin k) (n : ℕ) : Prop :=
  ∃ t : ℕ, isNthVisitTime (k := k) ω i n t

noncomputable def nthVisitTime (ω : ℕ → Fin k) (i : Fin k) (n : ℕ) : Option ℕ :=
  by
    classical
    exact if h : nthVisitTimeExists (k := k) ω i n then some (Nat.find h) else none

/-! ### Class-Based Visit Infrastructure

Generalizes visit-time machinery from single states to state classes.
-/

section ClassVisits

variable (C : Set (Fin k))

/-- Count of visits to any state in class C before time t. -/
noncomputable def classVisitCountBefore (ω : ℕ → Fin k) (t : ℕ) : ℕ := by
  classical
  exact Finset.sum (Finset.range t) (fun s => if ω s ∈ C then (1 : ℕ) else (0 : ℕ))

/-- Time t is the n-th visit to class C. -/
def isNthClassVisitTime (ω : ℕ → Fin k) (n t : ℕ) : Prop :=
  ω t ∈ C ∧ classVisitCountBefore (k := k) C ω t = n

/-- There exists an n-th visit time to class C. -/
def nthClassVisitTimeExists (ω : ℕ → Fin k) (n : ℕ) : Prop :=
  ∃ t : ℕ, isNthClassVisitTime (k := k) C ω n t

/-- The actual time of the n-th visit to class C. -/
noncomputable def nthClassVisitTime (ω : ℕ → Fin k) (n : ℕ) : Option ℕ := by
  classical
  exact if h : nthClassVisitTimeExists (k := k) C ω n then some (Nat.find h) else none

/-- Singleton class visit count equals state visit count. -/
lemma classVisitCountBefore_singleton (i : Fin k) (ω : ℕ → Fin k) (t : ℕ) :
    classVisitCountBefore (k := k) ({i} : Set (Fin k)) ω t = visitCountBefore (k := k) ω i t := by
  classical
  simp only [classVisitCountBefore, visitCountBefore, Set.mem_singleton_iff]

/-- Singleton class n-th visit time equals state n-th visit time. -/
lemma isNthClassVisitTime_singleton (i : Fin k) (ω : ℕ → Fin k) (n t : ℕ) :
    isNthClassVisitTime (k := k) ({i} : Set (Fin k)) ω n t ↔ isNthVisitTime (k := k) ω i n t := by
  simp only [isNthClassVisitTime, isNthVisitTime, Set.mem_singleton_iff,
             classVisitCountBefore_singleton]

/-- Singleton class n-th visit existence equals state n-th visit existence. -/
lemma nthClassVisitTimeExists_singleton (i : Fin k) (ω : ℕ → Fin k) (n : ℕ) :
    nthClassVisitTimeExists (k := k) ({i} : Set (Fin k)) ω n ↔
    nthVisitTimeExists (k := k) ω i n := by
  simp only [nthClassVisitTimeExists, nthVisitTimeExists, isNthClassVisitTime_singleton]

/-- Singleton class n-th visit time equals state n-th visit time. -/
lemma nthClassVisitTime_singleton (i : Fin k) (ω : ℕ → Fin k) (n : ℕ) :
    nthClassVisitTime (k := k) ({i} : Set (Fin k)) ω n = nthVisitTime (k := k) ω i n := by
  classical
  unfold nthClassVisitTime nthVisitTime
  have hiff : nthClassVisitTimeExists (k := k) ({i} : Set (Fin k)) ω n ↔
              nthVisitTimeExists (k := k) ω i n :=
    nthClassVisitTimeExists_singleton (k := k) i ω n
  by_cases h : nthVisitTimeExists (k := k) ω i n
  · simp only [dif_pos h, dif_pos (hiff.2 h)]
    congr 1
    apply Nat.le_antisymm
    · apply Nat.find_le
      exact (isNthClassVisitTime_singleton (k := k) i ω n _).2 (Nat.find_spec h)
    · apply Nat.find_le
      exact (isNthClassVisitTime_singleton (k := k) i ω n _).1 (Nat.find_spec (hiff.2 h))
  · simp only [dif_neg h, dif_neg (fun hc => h (hiff.1 hc))]

end ClassVisits

noncomputable def rowSuccessorAtNthVisit (i : Fin k) (n : ℕ) (ω : ℕ → Fin k) : Fin k :=
  match nthVisitTime (k := k) ω i n with
  | some t => successorAt (k := k) ω t
  | none => i

noncomputable def rowSuccessorVisitProcess (i : Fin k) (ω : ℕ → Fin k) : ℕ → Fin k :=
  fun n => rowSuccessorAtNthVisit (k := k) i n ω

def rowVisitCylinderEvent (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) : Set (ℕ → Fin k) :=
  {ω | ∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i n ω = v n}

/-- Truncated row-visit cylinder event:
all required visit-index constraints are witnessed by times `< N`. -/
def rowVisitCylinderEventUpTo
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) : Set (ℕ → Fin k) :=
  {ω | ∀ n ∈ S, ∃ t : ℕ, t < N ∧
      nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = v n}

/-- Extend a finite prefix trajectory to an infinite path by keeping the first
`N+1` coordinates and then defaulting to the first symbol. -/
def prefixExtend (N : ℕ) (xs : Fin (N + 1) → Fin k) : ℕ → Fin k :=
  fun m =>
    if h : m ≤ N then xs ⟨m, Nat.lt_succ_of_le h⟩ else xs 0

/-- Single-coordinate row-successor value event. -/
def rowSuccessorValueEvent (i : Fin k) (n : ℕ) (a : Fin k) : Set (ℕ → Fin k) :=
  {ω | rowSuccessorAtNthVisit (k := k) i n ω = a}

/-- Time-indexed piece for row-successor value decomposition. -/
def rowSuccessorValueEventAtTime
    (i : Fin k) (n : ℕ) (a : Fin k) (t : ℕ) : Set (ℕ → Fin k) :=
  {ω | nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = a}

/-- Finite-cylinder row event decomposes as finite intersection of single-coordinate
row-successor events. -/
lemma rowVisitCylinderEventUpTo_eq_iInter_iUnion_time
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    rowVisitCylinderEventUpTo (k := k) i S v N =
      ⋂ n ∈ S, ⋃ t ∈ Finset.range N,
        rowSuccessorValueEventAtTime (k := k) i n (v n) t := by
  ext ω
  simp [rowVisitCylinderEventUpTo, rowSuccessorValueEventAtTime, and_left_comm]

/-- Single-coordinate row-successor event decomposition into `none`-case plus a
countable union over exact visit times. -/
lemma rowSuccessorValueEvent_eq_none_or_iUnion_time
    (i : Fin k) (n : ℕ) (a : Fin k) :
    rowSuccessorValueEvent (k := k) i n a =
      ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none ∧ i = a} ∪
        ⋃ t : ℕ, rowSuccessorValueEventAtTime (k := k) i n a t) := by
  ext ω
  constructor
  · intro hω
    by_cases hnone : nthVisitTime (k := k) ω i n = none
    · left
      refine ⟨hnone, ?_⟩
      have hrow : rowSuccessorAtNthVisit (k := k) i n ω = i := by
        simp [rowSuccessorAtNthVisit, hnone]
      have hval : rowSuccessorAtNthVisit (k := k) i n ω = a := hω
      exact hrow.symm.trans hval
    · right
      rcases hsome : nthVisitTime (k := k) ω i n with _ | t
      · contradiction
      · refine Set.mem_iUnion.mpr ⟨t, ?_⟩
        refine ⟨hsome, ?_⟩
        have hrow : rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
          simp [rowSuccessorAtNthVisit, hsome]
        have hval : rowSuccessorAtNthVisit (k := k) i n ω = a := hω
        exact hrow.symm.trans hval
  · intro hω
    rcases hω with hnone | hsome
    · rcases hnone with ⟨hnone, hia⟩
      have : rowSuccessorAtNthVisit (k := k) i n ω = i := by
        simp [rowSuccessorAtNthVisit, hnone]
      simpa [rowSuccessorValueEvent, hia] using this
    · rcases Set.mem_iUnion.mp hsome with ⟨t, ht⟩
      rcases ht with ⟨hvisit, hsucc⟩
      have hrow : rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
        simp [rowSuccessorAtNthVisit, hvisit]
      exact hrow.trans hsucc

lemma rowSuccessorValueEvent_eq_iUnion_upTo_of_ne
    (i : Fin k) (n : ℕ) (a : Fin k) (h : a ≠ i) :
    rowSuccessorValueEvent (k := k) i n a =
      ⋃ N : ℕ,
        rowVisitCylinderEventUpTo (k := k) i {n} (fun m => if m = n then a else i) N := by
  classical
  -- drop the none-case using `a ≠ i`
  have hnone :
      {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none ∧ i = a} = (∅ : Set (ℕ → Fin k)) := by
    ext ω; constructor
    · intro hω
      exact (h hω.2.symm).elim
    · intro hω
      cases hω
  have hunion :
      (⋃ t : ℕ, rowSuccessorValueEventAtTime (k := k) i n a t) =
        ⋃ N : ℕ,
          ⋃ t ∈ Finset.range N,
            rowSuccessorValueEventAtTime (k := k) i n a t := by
    ext ω; constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨t, ht⟩
      refine Set.mem_iUnion.mpr ⟨t + 1, ?_⟩
      refine Set.mem_iUnion.mpr ⟨t, ?_⟩
      refine Set.mem_iUnion.mpr ?_
      have ht' : t ∈ Finset.range (t + 1) := by
        simp [Finset.mem_range]
      exact ⟨ht', ht⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨N, hN⟩
      rcases Set.mem_iUnion.mp hN with ⟨t, ht⟩
      rcases Set.mem_iUnion.mp ht with ⟨htN, hωt⟩
      exact Set.mem_iUnion.mpr ⟨t, hωt⟩
  -- rewrite `rowVisitCylinderEventUpTo` for singleton `S`
  have hUpTo :
      (⋃ N : ℕ,
        rowVisitCylinderEventUpTo (k := k) i {n} (fun m => if m = n then a else i) N) =
        ⋃ N : ℕ,
          ⋃ t ∈ Finset.range N,
            rowSuccessorValueEventAtTime (k := k) i n a t := by
    ext ω; constructor <;> intro hω
    · rcases Set.mem_iUnion.mp hω with ⟨N, hN⟩
      have hN' :
          ω ∈ ⋃ t ∈ Finset.range N,
            rowSuccessorValueEventAtTime (k := k) i n a t := by
        -- simplify the singleton intersection
        simpa [rowVisitCylinderEventUpTo_eq_iInter_iUnion_time] using hN
      exact Set.mem_iUnion.mpr ⟨N, hN'⟩
    · rcases Set.mem_iUnion.mp hω with ⟨N, hN⟩
      -- fold back to the UpTo event
      have hEq' :
          rowVisitCylinderEventUpTo (k := k) i ({n} : Finset ℕ)
            (fun m => if m = n then a else i) N =
            ⋃ t ∈ Finset.range N,
              rowSuccessorValueEventAtTime (k := k) i n a t := by
        simp [rowVisitCylinderEventUpTo_eq_iInter_iUnion_time]
      exact Set.mem_iUnion.mpr ⟨N, by simpa [hEq'] using hN⟩
  -- combine
  calc
    rowSuccessorValueEvent (k := k) i n a
        = (⋃ t : ℕ, rowSuccessorValueEventAtTime (k := k) i n a t) := by
            simp [rowSuccessorValueEvent_eq_none_or_iUnion_time, hnone]
    _ = ⋃ N : ℕ,
          ⋃ t ∈ Finset.range N,
            rowSuccessorValueEventAtTime (k := k) i n a t := hunion
    _ = ⋃ N : ℕ,
          rowVisitCylinderEventUpTo (k := k) i {n} (fun m => if m = n then a else i) N := by
          simp [hUpTo]

/-- Pushforward law of the visit-indexed row process under an extension measure `P`. -/
noncomputable def rowProcessLaw (P : Measure (ℕ → Fin k)) (i : Fin k) : Measure (ℕ → Fin k) :=
  Measure.map (rowSuccessorVisitProcess (k := k) i) P

/-- State-conditioned successor event at time `t`. -/
lemma measurable_visitCountBefore (i : Fin k) (t : ℕ) :
    Measurable (fun ω : ℕ → Fin k => visitCountBefore (k := k) ω i t) := by
  classical
  change Measurable
    (fun ω : ℕ → Fin k =>
      Finset.sum (Finset.range t) (fun s => if ω s = i then (1 : ℕ) else (0 : ℕ)))
  refine Finset.measurable_sum (s := Finset.range t)
    (f := fun s => fun ω : ℕ → Fin k => if ω s = i then (1 : ℕ) else (0 : ℕ)) ?_
  intro s hs
  have hpred : MeasurableSet {ω : ℕ → Fin k | ω s = i} := by
    have hcoord : Measurable (fun ω : ℕ → Fin k => ω s) := measurable_pi_apply s
    simpa [Set.preimage] using hcoord (MeasurableSet.singleton i)
  exact
    ((measurable_const : Measurable (fun _ : ℕ → Fin k => (1 : ℕ))).piecewise
      hpred
      (measurable_const : Measurable (fun _ : ℕ → Fin k => (0 : ℕ))))

lemma measurableSet_isNthVisitTime (i : Fin k) (n t : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | isNthVisitTime (k := k) ω i n t} := by
  have hvisit : MeasurableSet {ω : ℕ → Fin k | ω t = i} := by
    have hcoord : Measurable (fun ω : ℕ → Fin k => ω t) := measurable_pi_apply t
    simpa [Set.preimage] using hcoord (MeasurableSet.singleton i)
  have hcount : MeasurableSet
      {ω : ℕ → Fin k | visitCountBefore (k := k) ω i t = n} := by
    have hmeas := measurable_visitCountBefore (k := k) i t
    simpa [Set.preimage] using hmeas (MeasurableSet.singleton n)
  simpa [isNthVisitTime, Set.setOf_and] using hvisit.inter hcount

lemma measurableSet_nthVisitTimeExists (i : Fin k) (n : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | nthVisitTimeExists (k := k) ω i n} := by
  unfold nthVisitTimeExists
  simpa [Set.setOf_exists] using
    (MeasurableSet.iUnion (fun t => measurableSet_isNthVisitTime (k := k) i n t))

lemma visitCountBefore_eq_natCount
    (ω : ℕ → Fin k) (i : Fin k) :
    ∀ t : ℕ, visitCountBefore (k := k) ω i t = Nat.count (fun s => ω s = i) t := by
  intro t
  unfold visitCountBefore
  simp [Nat.count_eq_card_filter_range]

lemma nthVisitTimeExists_of_infinite_visits
    (ω : ℕ → Fin k) (i : Fin k) (n : ℕ)
    (hinf : Set.Infinite {t : ℕ | ω t = i}) :
    nthVisitTimeExists (k := k) ω i n := by
  classical
  let p : ℕ → Prop := fun t => ω t = i
  have hinf' : (setOf p).Infinite := by
    simpa [p] using hinf
  refine ⟨Nat.nth p n, ?_⟩
  refine ⟨?_, ?_⟩
  · exact Nat.nth_mem_of_infinite hinf' n
  · calc
      visitCountBefore (k := k) ω i (Nat.nth p n)
          = Nat.count p (Nat.nth p n) := by
              simpa [p] using (visitCountBefore_eq_natCount (k := k) ω i (Nat.nth p n))
      _ = n := Nat.count_nth_of_infinite hinf' n

/-- Strong recurrence in a class implies all visit indices exist for class members.
This connects the measure-theoretic `StrongRecurrenceInClass` to the combinatorial
`nthVisitTimeExists`. -/
lemma nthVisitTimeExists_of_StrongRecurrenceInClass
    (C : Set (Fin k)) (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
    (hstrong :
      ∀ i ∈ C, ∀ᵐ ω ∂P, (∃ t : ℕ, ω t ∈ C) → Set.Infinite {t : ℕ | ω t = i})
    (i : Fin k) (hi : i ∈ C) (n : ℕ) :
    ∀ᵐ ω ∂P, (∃ t : ℕ, ω t ∈ C) → nthVisitTimeExists (k := k) ω i n := by
  have hae : ∀ᵐ ω ∂P, (∃ t : ℕ, ω t ∈ C) → Set.Infinite {t : ℕ | ω t = i} := hstrong i hi
  filter_upwards [hae] with ω hω henter
  exact nthVisitTimeExists_of_infinite_visits (k := k) ω i n (hω henter)

lemma visitCountBefore_strict_mono_of_visit
    (ω : ℕ → Fin k) (i : Fin k) {t u : ℕ}
    (ht : ω t = i) (htu : t < u) :
    visitCountBefore (k := k) ω i t < visitCountBefore (k := k) ω i u := by
  have hcount :
      Nat.count (fun s => ω s = i) t <
        Nat.count (fun s => ω s = i) u :=
    Nat.count_strict_mono (p := fun s => ω s = i) (m := t) (n := u) ht htu
  simpa [visitCountBefore_eq_natCount (k := k) ω i t,
    visitCountBefore_eq_natCount (k := k) ω i u] using hcount

lemma isNthVisitTime_unique
    (ω : ℕ → Fin k) (i : Fin k) (n t u : ℕ)
    (ht : isNthVisitTime (k := k) ω i n t)
    (hu : isNthVisitTime (k := k) ω i n u) :
    t = u := by
  rcases lt_trichotomy t u with hlt | heq | hgt
  · exfalso
    rcases ht with ⟨ht_visit, ht_count⟩
    rcases hu with ⟨_, hu_count⟩
    have hcount_lt :
        visitCountBefore (k := k) ω i t < visitCountBefore (k := k) ω i u :=
      visitCountBefore_strict_mono_of_visit (k := k) ω i ht_visit hlt
    rw [ht_count, hu_count] at hcount_lt
    exact (Nat.lt_irrefl n) hcount_lt
  · exact heq
  · exfalso
    rcases ht with ⟨_, ht_count⟩
    rcases hu with ⟨hu_visit, hu_count⟩
    have hcount_lt :
        visitCountBefore (k := k) ω i u < visitCountBefore (k := k) ω i t :=
      visitCountBefore_strict_mono_of_visit (k := k) ω i hu_visit hgt
    rw [ht_count, hu_count] at hcount_lt
    exact (Nat.lt_irrefl n) hcount_lt

lemma nthVisitTime_eq_some_iff
    (ω : ℕ → Fin k) (i : Fin k) (n t : ℕ) :
    nthVisitTime (k := k) ω i n = some t ↔
      isNthVisitTime (k := k) ω i n t := by
  constructor
  · intro hsome
    classical
    unfold nthVisitTime at hsome
    by_cases hex : nthVisitTimeExists (k := k) ω i n
    · simp [hex] at hsome
      simpa [hsome] using (Nat.find_spec hex)
    · simp [hex] at hsome
  · intro ht
    classical
    have hex : nthVisitTimeExists (k := k) ω i n := ⟨t, ht⟩
    unfold nthVisitTime
    simp [hex]
    exact isNthVisitTime_unique (k := k) ω i n (Nat.find hex) t (Nat.find_spec hex) ht

lemma nthVisitTime_eq_none_iff
    (ω : ℕ → Fin k) (i : Fin k) (n : ℕ) :
    nthVisitTime (k := k) ω i n = none ↔
      ¬ nthVisitTimeExists (k := k) ω i n := by
  classical
  unfold nthVisitTime
  by_cases hex : nthVisitTimeExists (k := k) ω i n
  · simp [hex]
  · simp [hex]

lemma isNthVisitTime_zero_zero_of_start
    (ω : ℕ → Fin k) (i : Fin k)
    (hstart : ω 0 = i) :
    isNthVisitTime (k := k) ω i 0 0 := by
  refine ⟨hstart, ?_⟩
  simp [visitCountBefore]

lemma nthVisitTime_zero_eq_some_zero_of_start
    (ω : ℕ → Fin k) (i : Fin k)
    (hstart : ω 0 = i) :
    nthVisitTime (k := k) ω i 0 = some 0 := by
  exact
    (nthVisitTime_eq_some_iff (k := k) ω i 0 0).2
      (isNthVisitTime_zero_zero_of_start (k := k) ω i hstart)

lemma rowSuccessorAtNthVisit_zero_eq_successor_of_start
    (ω : ℕ → Fin k) (i : Fin k)
    (hstart : ω 0 = i) :
    rowSuccessorAtNthVisit (k := k) i 0 ω = successorAt (k := k) ω 0 := by
  simp [rowSuccessorAtNthVisit,
    nthVisitTime_zero_eq_some_zero_of_start (k := k) ω i hstart]

lemma visitCountBefore_eq_of_prefixEq_upTo
    (ω ω' : ℕ → Fin k) (i : Fin k) {N t : ℕ}
    (ht : t ≤ N)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    visitCountBefore (k := k) ω i t = visitCountBefore (k := k) ω' i t := by
  unfold visitCountBefore
  refine Finset.sum_congr rfl ?_
  intro s hs
  have hslt : s < t := Finset.mem_range.mp hs
  have hsleN : s ≤ N := Nat.le_trans (Nat.le_of_lt hslt) ht
  simp [hprefix s hsleN]

lemma isNthVisitTime_iff_of_prefixEq_upTo
    (ω ω' : ℕ → Fin k) (i : Fin k) (n t : ℕ) {N : ℕ}
    (ht : t ≤ N)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    isNthVisitTime (k := k) ω i n t ↔ isNthVisitTime (k := k) ω' i n t := by
  constructor
  · intro h
    rcases h with ⟨hvisit, hcount⟩
    refine ⟨?_, ?_⟩
    · calc
        ω' t = ω t := by simpa using (hprefix t ht).symm
        _ = i := hvisit
    · calc
        visitCountBefore (k := k) ω' i t = visitCountBefore (k := k) ω i t := by
          simpa using
            (visitCountBefore_eq_of_prefixEq_upTo (k := k) ω' ω i ht
              (fun m hm => (hprefix m hm).symm))
        _ = n := hcount
  · intro h
    rcases h with ⟨hvisit, hcount⟩
    refine ⟨?_, ?_⟩
    · calc
        ω t = ω' t := by simpa using hprefix t ht
        _ = i := hvisit
    · calc
        visitCountBefore (k := k) ω i t = visitCountBefore (k := k) ω' i t := by
          simpa using visitCountBefore_eq_of_prefixEq_upTo (k := k) ω ω' i ht hprefix
        _ = n := hcount

lemma nthVisitTime_eq_some_iff_of_prefixEq_upTo
    (ω ω' : ℕ → Fin k) (i : Fin k) (n t : ℕ) {N : ℕ}
    (ht : t ≤ N)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    nthVisitTime (k := k) ω i n = some t ↔
      nthVisitTime (k := k) ω' i n = some t := by
  rw [nthVisitTime_eq_some_iff (k := k) ω i n t, nthVisitTime_eq_some_iff (k := k) ω' i n t]
  exact isNthVisitTime_iff_of_prefixEq_upTo (k := k) ω ω' i n t ht hprefix

lemma successorAt_eq_of_prefixEq_upTo_lt
    (ω ω' : ℕ → Fin k) {N t : ℕ}
    (ht : t < N)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    successorAt (k := k) ω t = successorAt (k := k) ω' t := by
  have ht1 : t + 1 ≤ N := Nat.succ_le_of_lt ht
  calc
    successorAt (k := k) ω t = ω (t + 1) := by rfl
    _ = ω' (t + 1) := hprefix (t + 1) ht1
    _ = successorAt (k := k) ω' t := by rfl

lemma rowVisitCylinderEventUpTo_mem_iff_of_prefixEq
    (ω ω' : ℕ → Fin k) (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    ω ∈ rowVisitCylinderEventUpTo (k := k) i S v N ↔
      ω' ∈ rowVisitCylinderEventUpTo (k := k) i S v N := by
  constructor
  · intro h n hnS
    rcases h n hnS with ⟨t, htN, htime, hsucc⟩
    refine ⟨t, htN, ?_, ?_⟩
    · exact (nthVisitTime_eq_some_iff_of_prefixEq_upTo (k := k) ω ω' i n t
        (Nat.le_of_lt htN) hprefix).1 htime
    · calc
        successorAt (k := k) ω' t = successorAt (k := k) ω t := by
          simpa using
            (successorAt_eq_of_prefixEq_upTo_lt (k := k) ω' ω htN
              (fun m hm => (hprefix m hm).symm))
        _ = v n := hsucc
  · intro h n hnS
    rcases h n hnS with ⟨t, htN, htime, hsucc⟩
    refine ⟨t, htN, ?_, ?_⟩
    · exact (nthVisitTime_eq_some_iff_of_prefixEq_upTo (k := k) ω ω' i n t
        (Nat.le_of_lt htN) hprefix).2 htime
    · calc
        successorAt (k := k) ω t = successorAt (k := k) ω' t := by
          exact successorAt_eq_of_prefixEq_upTo_lt (k := k) ω ω' htN hprefix
        _ = v n := hsucc

lemma measurableSet_nthVisitTime_eq_some (i : Fin k) (n t : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} := by
  have hEq :
      {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} =
        {ω : ℕ → Fin k | isNthVisitTime (k := k) ω i n t} := by
    ext ω
    exact nthVisitTime_eq_some_iff (k := k) ω i n t
  simpa [hEq] using measurableSet_isNthVisitTime (k := k) i n t

lemma measurableSet_nthVisitTime_eq_none (i : Fin k) (n : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} := by
  have hEq :
      {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} =
        {ω : ℕ → Fin k | ¬ nthVisitTimeExists (k := k) ω i n} := by
    ext ω
    exact nthVisitTime_eq_none_iff (k := k) ω i n
  simpa [hEq, Set.compl_setOf] using
    (measurableSet_nthVisitTimeExists (k := k) i n).compl

lemma measurableSet_successorAt_eq (a : Fin k) (t : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | successorAt (k := k) ω t = a} := by
  have hcoord : Measurable (fun ω : ℕ → Fin k => ω (t + 1)) := measurable_pi_apply (t + 1)
  simpa [successorAt, Set.preimage] using hcoord (MeasurableSet.singleton a)

lemma measurableSet_rowSuccessorValueEventAtTime
    (i : Fin k) (n : ℕ) (a : Fin k) (t : ℕ) :
    MeasurableSet (rowSuccessorValueEventAtTime (k := k) i n a t) := by
  have hvisit : MeasurableSet {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} :=
    measurableSet_nthVisitTime_eq_some (k := k) i n t
  have hsucc : MeasurableSet {ω : ℕ → Fin k | successorAt (k := k) ω t = a} :=
    measurableSet_successorAt_eq (k := k) a t
  simpa [rowSuccessorValueEventAtTime, Set.setOf_and] using hvisit.inter hsucc

lemma measurableSet_rowSuccessorAtNthVisit_eq
    (i : Fin k) (n : ℕ) (a : Fin k) :
    MeasurableSet {ω : ℕ → Fin k | rowSuccessorAtNthVisit (k := k) i n ω = a} := by
  have hdecomp :
      {ω : ℕ → Fin k | rowSuccessorAtNthVisit (k := k) i n ω = a} =
        ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} ∩
          {ω : ℕ → Fin k | i = a}) ∪
          ⋃ t : ℕ,
            ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} ∩
              {ω : ℕ → Fin k | successorAt (k := k) ω t = a}) := by
    ext ω
    constructor
    · intro hω
      unfold rowSuccessorAtNthVisit at hω
      cases hnt : nthVisitTime (k := k) ω i n with
      | none =>
          left
          refine ⟨hnt, ?_⟩
          simpa [hnt] using hω
      | some t =>
          right
          refine Set.mem_iUnion.mpr ⟨t, ?_⟩
          refine ⟨hnt, ?_⟩
          simpa [hnt] using hω
    · intro hω
      rcases hω with hnone | hsome
      · rcases hnone with ⟨hnt, hia⟩
        change rowSuccessorAtNthVisit (k := k) i n ω = a
        have hnt' : nthVisitTime (k := k) ω i n = none := by simpa using hnt
        unfold rowSuccessorAtNthVisit
        rw [hnt']
        simpa using hia
      · rcases Set.mem_iUnion.mp hsome with ⟨t, ht⟩
        rcases ht with ⟨hnt, hsucc⟩
        change rowSuccessorAtNthVisit (k := k) i n ω = a
        have hnt' : nthVisitTime (k := k) ω i n = some t := by simpa using hnt
        unfold rowSuccessorAtNthVisit
        rw [hnt']
        simpa using hsucc
  have hnone : MeasurableSet {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} :=
    measurableSet_nthVisitTime_eq_none (k := k) i n
  have hiEqA : MeasurableSet {ω : ℕ → Fin k | i = a} := by
    by_cases hia : i = a <;> simp [hia]
  have hleft :
      MeasurableSet
        ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} ∩
          {ω : ℕ → Fin k | i = a}) := hnone.inter hiEqA
  have hright :
      MeasurableSet
        (⋃ t : ℕ,
          ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} ∩
            {ω : ℕ → Fin k | successorAt (k := k) ω t = a})) :=
    MeasurableSet.iUnion (fun t =>
      (measurableSet_nthVisitTime_eq_some (k := k) i n t).inter
        (measurableSet_successorAt_eq (k := k) a t))
  simpa [hdecomp] using hleft.union hright

lemma measurableSet_rowSuccessorValueEvent
    (i : Fin k) (n : ℕ) (a : Fin k) :
    MeasurableSet (rowSuccessorValueEvent (k := k) i n a) := by
  simpa [rowSuccessorValueEvent] using
    (measurableSet_rowSuccessorAtNthVisit_eq (k := k) i n a)

lemma measurableSet_preimage_rowSuccessorAtNthVisit_singleton
    (i : Fin k) (n : ℕ) (a : Fin k) :
    MeasurableSet ((rowSuccessorAtNthVisit (k := k) i n) ⁻¹' ({a} : Set (Fin k))) := by
  simpa [Set.preimage] using
    measurableSet_rowSuccessorAtNthVisit_eq (k := k) i n a

lemma measurable_rowSuccessorAtNthVisit
    (i : Fin k) (n : ℕ) :
    Measurable (fun ω : ℕ → Fin k => rowSuccessorAtNthVisit (k := k) i n ω) := by
  refine measurable_to_countable' (f := fun ω : ℕ → Fin k => rowSuccessorAtNthVisit (k := k) i n ω) ?_
  intro a
  simpa using measurableSet_preimage_rowSuccessorAtNthVisit_singleton (k := k) i n a

lemma measurable_rowSuccessorVisitProcess
    (i : Fin k) :
    Measurable (rowSuccessorVisitProcess (k := k) i) := by
  rw [measurable_pi_iff]
  intro n
  simpa [rowSuccessorVisitProcess] using
    measurable_rowSuccessorAtNthVisit (k := k) i n

lemma measurableSet_cylinder (xs : List (Fin k)) :
    MeasurableSet (cylinder (k := k) xs) := by
  unfold MarkovDeFinettiRecurrence.cylinder
  refine MeasurableSet.iInter ?_
  intro i
  have hcoord : Measurable (fun ω : ℕ → Fin k => ω i.1) := measurable_pi_apply i.1
  simpa [Set.preimage] using hcoord (MeasurableSet.singleton xs[i.1])

lemma cylinder_pair_eq_start_and_rowSuccessorZero
    (a b : Fin k) :
    cylinder (k := k) [a, b] =
      ({ω : ℕ → Fin k | ω 0 = a} ∩
        rowSuccessorValueEvent (k := k) a 0 b) := by
  ext ω
  constructor
  · intro hω
    have hpair : ω 0 = a ∧ ω 1 = b := by
      simpa [MarkovDeFinettiRecurrence.cylinder] using hω
    have h0 : ω 0 = a := hpair.1
    have h1 : ω 1 = b := hpair.2
    refine ⟨h0, ?_⟩
    have hsucc :
        successorAt (k := k) ω 0 = b := by
      simpa [successorAt] using h1
    calc
      rowSuccessorAtNthVisit (k := k) a 0 ω = successorAt (k := k) ω 0 := by
        exact rowSuccessorAtNthVisit_zero_eq_successor_of_start (k := k) ω a h0
      _ = b := hsucc
  · intro hω
    rcases hω with ⟨h0, hrow⟩
    have hsucc :
        successorAt (k := k) ω 0 = b := by
      calc
        successorAt (k := k) ω 0 = rowSuccessorAtNthVisit (k := k) a 0 ω := by
          symm
          exact rowSuccessorAtNthVisit_zero_eq_successor_of_start (k := k) ω a h0
        _ = b := hrow
    have h1 : ω 1 = b := by simpa [successorAt] using hsucc
    have hpair : ω 0 = a ∧ ω 1 = b := ⟨h0, h1⟩
    simpa [MarkovDeFinettiRecurrence.cylinder] using hpair

lemma measure_cylinder_pair_eq_start_and_rowSuccessorZero
    (P : Measure (ℕ → Fin k)) (a b : Fin k) :
    P (cylinder (k := k) [a, b]) =
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ rowSuccessorValueEvent (k := k) a 0 b) := by
  simp [cylinder_pair_eq_start_and_rowSuccessorZero (k := k) a b]

/-- The visit index of position `n` inside a finite word: the number of previous
occurrences of the symbol at `n`. -/
def wordVisitIndex
    (xs : List (Fin k)) (d : Fin k) (n : ℕ) : ℕ :=
  Nat.count (fun m => xs.getD m d = xs.getD n d) n

/-- The ordered list of tuple coordinates in `ys` whose anchor symbol in the
word `a :: ys` is `i`. The order is inherited from `List.finRange ys.length`. -/
def wordAnchorFiberList
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) : List (Fin ys.length) :=
  (List.finRange ys.length).filter fun j => (a :: ys).getD j.1 a = i

lemma mem_wordAnchorFiberList_iff
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) (j : Fin ys.length) :
    j ∈ wordAnchorFiberList (k := k) a ys i ↔ (a :: ys).getD j.1 a = i := by
  simp [wordAnchorFiberList, List.mem_filter, List.mem_finRange]

lemma getElem_wordAnchorFiberList_eq_anchor
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) {n : ℕ}
    (hn : n < (wordAnchorFiberList (k := k) a ys i).length) :
    (a :: ys).getD ((wordAnchorFiberList (k := k) a ys i)[n]).1 a = i := by
  simpa [wordAnchorFiberList] using
    (List.getElem_filter
      (xs := List.finRange ys.length)
      (p := fun j : Fin ys.length => (a :: ys).getD j.1 a = i)
      hn)

lemma length_wordAnchorFiberList_eq_countP
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) :
    (wordAnchorFiberList (k := k) a ys i).length =
      (List.finRange ys.length).countP (fun j : Fin ys.length => (a :: ys).getD j.1 a = i) := by
  simp [wordAnchorFiberList, List.countP_eq_length_filter]

lemma idxOf_filter_eq_countP_take_idxOf
    {α : Type*} [DecidableEq α] (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → ∀ {x : α}, x ∈ l.filter p →
      (l.filter p).idxOf x = (l.take (l.idxOf x)).countP p
  | [], _, x, hx => by simp at hx
  | a :: l, hnd, x, hx => by
      rcases List.nodup_cons.mp hnd with ⟨ha, hnd'⟩
      by_cases hp : p a
      · have hx' : x = a ∨ x ∈ l.filter p := by
          simpa [hp] using hx
        rcases hx' with rfl | hx'
        · simp [hp]
        · have hxa : x ≠ a := by
            intro hax
            subst hax
            exact ha (List.mem_of_mem_filter hx')
          rw [List.filter_cons, if_pos hp]
          rw [List.idxOf_cons_ne (a := x) (b := a) (l := List.filter p l) hxa.symm,
            List.idxOf_cons_ne (a := x) (b := a) (l := l) hxa.symm]
          simp [hp, idxOf_filter_eq_countP_take_idxOf p hnd' hx']
      · have hx' : x ∈ l.filter p := by
          simpa [hp] using hx
        have hxa : x ≠ a := by
          intro hax
          subst hax
          simp [hp] at hx'
        rw [List.filter_cons, if_neg hp]
        rw [List.idxOf_cons_ne (a := x) (b := a) (l := l) hxa.symm]
        simp [hp, idxOf_filter_eq_countP_take_idxOf p hnd' hx']

lemma take_finRange_eq_map_castLT
    {n : ℕ} (j : Fin n) :
    (List.finRange n).take j.1 =
      (List.finRange j.1).map (fun i : Fin j.1 => Fin.castLT i (Nat.lt_trans i.2 j.2)) := by
  apply List.ext_getElem <;> simp [List.getElem_map, List.getElem_finRange]

lemma countP_take_finRange_eq_wordVisitIndex
    (a : Fin k) (ys : List (Fin k)) (i : Fin k) (j : Fin ys.length)
    (hj : (a :: ys).getD j.1 a = i) :
    ((List.finRange ys.length).take j.1).countP
        (fun m : Fin ys.length => (a :: ys).getD m.1 a = i) =
      wordVisitIndex (k := k) (a :: ys) a j.1 := by
  rw [take_finRange_eq_map_castLT j, wordVisitIndex, hj]
  calc
    ((List.finRange j.1).map (fun m : Fin j.1 => Fin.castLT m (Nat.lt_trans m.2 j.2))).countP
        (fun m : Fin ys.length => decide ((a :: ys).getD m.1 a = i)) =
      (List.finRange j.1).countP
        (((fun m : Fin ys.length => decide ((a :: ys).getD m.1 a = i)) ∘
          fun m : Fin j.1 => Fin.castLT m (Nat.lt_trans m.2 j.2))) := by
        exact
          (List.countP_map
            (p := fun m : Fin ys.length => decide ((a :: ys).getD m.1 a = i))
            (f := fun m : Fin j.1 => Fin.castLT m (Nat.lt_trans m.2 j.2))
            (l := List.finRange j.1))
    _ = (List.finRange j.1).countP (fun m : Fin j.1 => decide ((a :: ys).getD m.1 a = i)) := by
        rfl
    _ = ((List.finRange j.1).map (fun m : Fin j.1 => m.1)).countP
          (fun m => decide ((a :: ys).getD m a = i)) := by
        exact
          (List.countP_map
            (p := fun m => decide ((a :: ys).getD m a = i))
            (f := fun m : Fin j.1 => m.1)
            (l := List.finRange j.1)).symm
    _ = (List.range j.1).countP (fun m => (a :: ys).getD m a = i) := by
        exact congrArg
          (fun l => l.countP (fun m => (a :: ys).getD m a = i))
          (List.map_coe_finRange_eq_range (n := j.1))
    _ = Nat.count (fun m => (a :: ys).getD m a = i) j.1 := by
        rfl

lemma wordVisitIndex_getElem_wordAnchorFiberList
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (t : Fin (wordAnchorFiberList (k := k) a ys i).length) :
    wordVisitIndex (k := k) (a :: ys) a
        ((wordAnchorFiberList (k := k) a ys i)[t]).1 = t := by
  let p : Fin ys.length → Bool := fun j => (a :: ys).getD j.1 a = i
  let x : Fin ys.length := (wordAnchorFiberList (k := k) a ys i)[t]
  have hx : x ∈ (List.finRange ys.length).filter p := by
    simp [wordAnchorFiberList, p, x]
  have hidx_filter :
      ((List.finRange ys.length).filter p).idxOf x = t := by
    simpa [wordAnchorFiberList, p, x] using
      ((List.nodup_finRange ys.length).filter p).idxOf_getElem t.1 t.2
  have hcount :
      ((List.finRange ys.length).take ((List.finRange ys.length).idxOf x)).countP p = t := by
    rw [← hidx_filter]
    exact (idxOf_filter_eq_countP_take_idxOf p (List.nodup_finRange ys.length) hx).symm
  have hcount' :
      ((List.finRange ys.length).take x.1).countP p = t := by
    simpa [x, List.idxOf_finRange] using hcount
  have hx_anchor : (a :: ys).getD x.1 a = i := by
    simpa [x] using getElem_wordAnchorFiberList_eq_anchor (k := k) a ys i t.2
  simpa [p, x] using
    (countP_take_finRange_eq_wordVisitIndex (k := k) a ys i x hx_anchor).symm.trans hcount'

/-- If a path agrees with a finite word up to position `n`, then position `n` is
the `wordVisitIndex`-th visit of its current symbol. -/
lemma nthVisitTime_eq_some_of_wordPrefix
    (xs : List (Fin k)) (ω : ℕ → Fin k) {n : ℕ}
    (d : Fin k)
    (hprefix : ∀ m ≤ n, ω m = xs.getD m d) :
    nthVisitTime (k := k) ω (xs.getD n d) (wordVisitIndex (k := k) xs d n) = some n := by
  have hvisit : ω n = xs.getD n d := hprefix n le_rfl
  have hcount :
      visitCountBefore (k := k) ω (xs.getD n d) n =
        wordVisitIndex (k := k) xs d n := by
    rw [visitCountBefore_eq_natCount (k := k) ω (xs.getD n d) n, wordVisitIndex]
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    congr 1
    refine Finset.filter_congr ?_
    intro m hm
    simp [hprefix m (Nat.le_of_lt (Finset.mem_range.mp hm))]
  exact
    (nthVisitTime_eq_some_iff (k := k) ω (xs.getD n d) (wordVisitIndex (k := k) xs d n) n).2
      ⟨hvisit, hcount⟩

/-- Membership in a nonempty cylinder is equivalent to matching the start state
and every successor constraint encoded by the word's visit indices. -/
lemma mem_cylinder_cons_iff_rowSuccessor_constraints
    (ω : ℕ → Fin k) (a : Fin k) (ys : List (Fin k)) :
    ω ∈ cylinder (k := k) (a :: ys) ↔
      ω 0 = a ∧
      ∀ n, n + 1 < (a :: ys).length →
        rowSuccessorAtNthVisit (k := k) ((a :: ys).getD n a)
          (wordVisitIndex (k := k) (a :: ys) a n) ω
          = (a :: ys).getD (n + 1) a := by
  let xs := a :: ys
  constructor
  · intro hω
    have hcoords : ∀ i : Fin xs.length, ω i.1 = xs[i.1] := by
      simpa [xs, MarkovDeFinettiRecurrence.cylinder] using hω
    refine ⟨?_, ?_⟩
    · simpa [xs] using hcoords ⟨0, by simp [xs]⟩
    · intro n hn
      have hprefix : ∀ m ≤ n, ω m = xs.getD m a := by
        intro m hm
        have hm_lt : m < xs.length := Nat.lt_of_le_of_lt hm (Nat.lt_of_succ_lt hn)
        calc
          ω m = xs[m] := hcoords ⟨m, hm_lt⟩
          _ = xs.getD m a := (List.getD_eq_getElem (l := xs) (d := a) hm_lt).symm
      have hNth :
          nthVisitTime (k := k) ω (xs.getD n a)
            (wordVisitIndex (k := k) xs a n) = some n :=
        nthVisitTime_eq_some_of_wordPrefix (k := k) xs ω a hprefix
      have hnext : ω (n + 1) = xs.getD (n + 1) a := by
        have hnext' : ω (n + 1) = xs[n + 1] := hcoords ⟨n + 1, hn⟩
        exact hnext'.trans (List.getD_eq_getElem (l := xs) (d := a) hn).symm
      have hrow :
          rowSuccessorAtNthVisit (k := k) (xs.getD n a) (wordVisitIndex (k := k) xs a n) ω =
            xs.getD (n + 1) a := by
        rw [rowSuccessorAtNthVisit, hNth]
        simpa [successorAt] using hnext
      simpa [xs] using hrow
  · rintro ⟨hstart, hrows⟩
    have hprefix :
        ∀ n, n < xs.length → ∀ m ≤ n, ω m = xs.getD m a := by
      intro n hn
      induction n with
      | zero =>
          intro m hm
          have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
          simpa [xs, hm0] using hstart
      | succ n ih =>
          intro m hm
          rcases lt_or_eq_of_le hm with hm_lt | rfl
          · exact ih (Nat.lt_of_succ_lt hn) m (Nat.lt_succ_iff.mp hm_lt)
          · have hprefix_n : ∀ m ≤ n, ω m = xs.getD m a := ih (Nat.lt_of_succ_lt hn)
            have hNth :
                nthVisitTime (k := k) ω (xs.getD n a)
                  (wordVisitIndex (k := k) xs a n) = some n :=
              nthVisitTime_eq_some_of_wordPrefix (k := k) xs ω a hprefix_n
            have hrow :
                rowSuccessorAtNthVisit (k := k) (xs.getD n a)
                  (wordVisitIndex (k := k) xs a n) ω = xs.getD (n + 1) a := by
              simpa [xs] using hrows n hn
            rw [rowSuccessorAtNthVisit, hNth] at hrow
            simpa [successorAt] using hrow
    refine Set.mem_iInter.mpr ?_
    intro i
    calc
      ω i.1 = xs.getD i.1 a := hprefix i.1 i.2 i.1 le_rfl
      _ = xs[i.1] := List.getD_eq_getElem (l := xs) (d := a) i.2

/-- Set-level form of `mem_cylinder_cons_iff_rowSuccessor_constraints`. -/
lemma cylinder_cons_eq_start_and_rowSuccessor_constraints
    (a : Fin k) (ys : List (Fin k)) :
    cylinder (k := k) (a :: ys) =
      {ω : ℕ → Fin k |
        ω 0 = a ∧
        ∀ n, n + 1 < (a :: ys).length →
          rowSuccessorAtNthVisit (k := k) ((a :: ys).getD n a)
            (wordVisitIndex (k := k) (a :: ys) a n) ω
            = (a :: ys).getD (n + 1) a} := by
  ext ω
  exact mem_cylinder_cons_iff_rowSuccessor_constraints (k := k) ω a ys

/-- Tuple-valued measurable map collecting the row-successor constraints encoded
by a finite word `a :: ys`. -/
def wordSuccessorTupleMap
    (a : Fin k) (ys : List (Fin k)) :
    (ℕ → Fin k) → Fin ys.length → Fin k :=
  fun ω j =>
    rowSuccessorAtNthVisit (k := k) ((a :: ys).getD j.1 a)
      (wordVisitIndex (k := k) (a :: ys) a j.1) ω

/-- Target tuple of successor values encoded by a finite word `a :: ys`. -/
def wordSuccessorTuple
    (a : Fin k) (ys : List (Fin k)) :
    Fin ys.length → Fin k :=
  fun j => (a :: ys).getD (j.1 + 1) a

lemma measurable_wordSuccessorTupleMap
    (a : Fin k) (ys : List (Fin k)) :
    Measurable (wordSuccessorTupleMap (k := k) a ys) := by
  refine measurable_pi_lambda _ ?_
  intro j
  simpa [wordSuccessorTupleMap] using
    measurable_rowSuccessorAtNthVisit (k := k) ((a :: ys).getD j.1 a)
      (wordVisitIndex (k := k) (a :: ys) a j.1)

/-- Tuple form of `mem_cylinder_cons_iff_rowSuccessor_constraints`. -/
lemma mem_cylinder_cons_iff_start_and_wordSuccessorTuple
    (ω : ℕ → Fin k) (a : Fin k) (ys : List (Fin k)) :
    ω ∈ cylinder (k := k) (a :: ys) ↔
      ω 0 = a ∧
        wordSuccessorTupleMap (k := k) a ys ω = wordSuccessorTuple (k := k) a ys := by
  constructor
  · intro hω
    rcases (mem_cylinder_cons_iff_rowSuccessor_constraints (k := k) ω a ys).1 hω with
      ⟨hstart, hrows⟩
    refine ⟨hstart, funext ?_⟩
    intro j
    have hj : j.1 + 1 < (a :: ys).length := by
      exact Nat.succ_lt_succ j.2
    simpa [wordSuccessorTupleMap, wordSuccessorTuple] using hrows j.1 hj
  · rintro ⟨hstart, htuple⟩
    refine (mem_cylinder_cons_iff_rowSuccessor_constraints (k := k) ω a ys).2 ?_
    refine ⟨hstart, ?_⟩
    intro n hn
    have htuple_n := congrFun htuple ⟨n, by simpa using hn⟩
    simpa [wordSuccessorTupleMap, wordSuccessorTuple] using htuple_n

/-- Set-level tuple form of the cylinder decomposition for a nonempty word. -/
lemma cylinder_cons_eq_start_inter_preimage_wordSuccessorTuple
    (a : Fin k) (ys : List (Fin k)) :
    cylinder (k := k) (a :: ys) =
      {ω : ℕ → Fin k | ω 0 = a} ∩
        (wordSuccessorTupleMap (k := k) a ys) ⁻¹'
          ({wordSuccessorTuple (k := k) a ys} : Set (Fin ys.length → Fin k)) := by
  ext ω
  rw [mem_cylinder_cons_iff_start_and_wordSuccessorTuple (k := k) ω a ys]
  simp [Set.preimage, Set.mem_setOf_eq]

lemma measurableSet_rowVisitCylinderEventUpTo
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    MeasurableSet (rowVisitCylinderEventUpTo (k := k) i S v N) := by
  rw [rowVisitCylinderEventUpTo_eq_iInter_iUnion_time (k := k) i S v N]
  refine Finset.measurableSet_biInter S ?_
  intro n hnS
  refine Finset.measurableSet_biUnion (Finset.range N) ?_
  intro t ht
  exact measurableSet_rowSuccessorValueEventAtTime (k := k) i n (v n) t

lemma mem_cylinder_of_prefix
    (ω : ℕ → Fin k) (N : ℕ) :
    ω ∈ cylinder (k := k) (List.ofFn (fun j : Fin (N + 1) => ω j)) := by
  refine Set.mem_iInter.mpr ?_
  intro i
  change ω i.1 = (List.ofFn (fun j : Fin (N + 1) => ω j))[i.1]
  let j : Fin (N + 1) := ⟨i.1, by simpa [List.length_ofFn] using i.2⟩
  have hiLt : i.1 < (List.ofFn (fun t : Fin (N + 1) => ω t)).length := by
    simpa [List.length_ofFn] using i.2
  have hget : (List.ofFn (fun t : Fin (N + 1) => ω t))[i.1] = ω j := by
    simpa [j] using
      (List.getElem_ofFn (f := fun t : Fin (N + 1) => ω t) (i := i.1) (h := hiLt))
  simpa [j] using hget.symm

lemma mem_cylinder_ofFn_iff
    (ω : ℕ → Fin k) (N : ℕ) (xs : Fin (N + 1) → Fin k) :
    ω ∈ cylinder (k := k) (List.ofFn xs) ↔
      ∀ j : Fin (N + 1), ω j = xs j := by
  constructor
  · intro hω j
    have hω' :
        ∀ i : Fin (List.ofFn xs).length, ω i.1 = (List.ofFn xs)[i.1] := by
      simpa [MarkovDeFinettiRecurrence.cylinder] using hω
    have hj' : j.1 < (List.ofFn xs).length := by
      simpa [List.length_ofFn] using j.2
    have hmain : ω j.1 = (List.ofFn xs)[j.1] := hω' ⟨j.1, hj'⟩
    have hget : (List.ofFn xs)[j.1] = xs j := by
      simpa [List.length_ofFn] using (List.getElem_ofFn (f := xs) (i := j.1) (h := hj'))
    simpa using hmain.trans hget
  · intro hω
    refine Set.mem_iInter.mpr ?_
    intro i
    let j : Fin (N + 1) := ⟨i.1, by simpa [List.length_ofFn] using i.2⟩
    have hpoint : ω j = xs j := hω j
    have hj' : i.1 < (List.ofFn xs).length := by
      simpa [List.length_ofFn] using i.2
    have hget : (List.ofFn xs)[i.1] = xs j := by
      simpa [j, List.length_ofFn] using
        (List.getElem_ofFn (f := xs) (i := i.1) (h := hj'))
    have : ω i.1 = (List.ofFn xs)[i.1] := by
      calc
        ω i.1 = ω j := by rfl
        _ = xs j := hpoint
        _ = (List.ofFn xs)[i.1] := hget.symm
    simpa using this

lemma eq_prefixExtend_of_mem_cylinder
    (ω : ℕ → Fin k) (N : ℕ) (xs : Fin (N + 1) → Fin k)
    (hω : ω ∈ cylinder (k := k) (List.ofFn xs)) :
    ∀ m ≤ N, ω m = prefixExtend (k := k) N xs m := by
  intro m hm
  have hω' :
      ∀ j : Fin (List.ofFn xs).length, ω j.1 = (List.ofFn xs)[j.1] := by
    simpa [MarkovDeFinettiRecurrence.cylinder] using hω
  have hmval : ω m = xs ⟨m, Nat.lt_succ_of_le hm⟩ := by
    have hm' : m < (List.ofFn xs).length := by
      simpa [List.length_ofFn] using Nat.lt_succ_of_le hm
    have hwm : ω m = (List.ofFn xs)[m] := hω' ⟨m, hm'⟩
    let jm : Fin (N + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
    have hget : (List.ofFn xs)[m] = xs jm := by
      simpa [jm, List.length_ofFn] using (List.getElem_ofFn (f := xs) (i := m) (h := hm'))
    exact hwm.trans hget
  simpa [prefixExtend, hm] using hmval

/-- Prefix trajectories whose `prefixExtend` satisfies a truncated row-visit
cylinder event. -/
noncomputable def rowVisitCylinderEventUpToPrefixCarrier
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    Finset (Fin (N + 1) → Fin k) := by
  classical
  exact (Finset.univ : Finset (Fin (N + 1) → Fin k)).filter
    (fun xs => rowVisitCylinderEventUpTo (k := k) i S v N (prefixExtend (k := k) N xs))

lemma rowVisitCylinderEventUpTo_eq_iUnion_cylinder
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    rowVisitCylinderEventUpTo (k := k) i S v N =
      ⋃ xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N,
        cylinder (k := k) (List.ofFn xs) := by
  classical
  ext ω
  constructor
  · intro hω
    let xsω : Fin (N + 1) → Fin k := fun j => ω j
    have hcarrier : xsω ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ xsω, ?_⟩
      have hprefix : ∀ m ≤ N, ω m = prefixExtend (k := k) N xsω m := by
        intro m hm
        simp [prefixExtend, hm, xsω]
      exact (rowVisitCylinderEventUpTo_mem_iff_of_prefixEq (k := k)
        ω (prefixExtend (k := k) N xsω) i S v N hprefix).1 hω
    refine Set.mem_iUnion.mpr ⟨xsω, Set.mem_iUnion.mpr ?_⟩
    refine ⟨hcarrier, ?_⟩
    exact mem_cylinder_of_prefix (k := k) ω N
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨xs, hω⟩
    rcases Set.mem_iUnion.mp hω with ⟨hxs, hmem⟩
    have hxs' :
        rowVisitCylinderEventUpTo (k := k) i S v N (prefixExtend (k := k) N xs) := by
      simpa [rowVisitCylinderEventUpToPrefixCarrier] using (Finset.mem_filter.mp hxs).2
    have hprefix : ∀ m ≤ N, ω m = prefixExtend (k := k) N xs m :=
      eq_prefixExtend_of_mem_cylinder (k := k) ω N xs hmem
    exact (rowVisitCylinderEventUpTo_mem_iff_of_prefixEq (k := k)
      ω (prefixExtend (k := k) N xs) i S v N hprefix).2 hxs'

lemma pairwiseDisjoint_cylinder_ofFn_on_prefixCarrier
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    ((↑(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N) :
      Set (Fin (N + 1) → Fin k))).PairwiseDisjoint
      (fun xs => cylinder (k := k) (List.ofFn xs)) := by
  intro xs hxs ys hys hne
  refine Set.disjoint_left.2 ?_
  intro ω hωx hωy
  have hx : ∀ j : Fin (N + 1), ω j = xs j :=
    (mem_cylinder_ofFn_iff (k := k) ω N xs).1 hωx
  have hy : ∀ j : Fin (N + 1), ω j = ys j :=
    (mem_cylinder_ofFn_iff (k := k) ω N ys).1 hωy
  have hEq : xs = ys := by
    funext j
    calc
      xs j = ω j := (hx j).symm
      _ = ys j := hy j
  exact hne hEq

lemma measure_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
    (P : Measure (ℕ → Fin k)) (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    P (rowVisitCylinderEventUpTo (k := k) i S v N) =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
        (fun xs => P (cylinder (k := k) (List.ofFn xs))) := by
  rw [rowVisitCylinderEventUpTo_eq_iUnion_cylinder (k := k) i S v N]
  exact measure_biUnion_finset
    (μ := P)
    (s := rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
    (f := fun xs => cylinder (k := k) (List.ofFn xs))
    (pairwiseDisjoint_cylinder_ofFn_on_prefixCarrier (k := k) i S v N)
    (fun xs hxs => measurableSet_cylinder (k := k) (List.ofFn xs))

lemma measure_start_inter_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
    (P : Measure (ℕ → Fin k)) (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k)
    (N : ℕ) (j : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i S v N) =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
        (fun xs =>
          if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
  classical
  let S0 : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = j}
  have hS0meas : MeasurableSet S0 := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({j} : Set (Fin k)))
    exact (measurable_pi_apply 0) (MeasurableSet.singleton j)
  have hleft :
      P (S0 ∩ rowVisitCylinderEventUpTo (k := k) i S v N) =
        (P.restrict S0) (rowVisitCylinderEventUpTo (k := k) i S v N) := by
    have h :=
      Measure.restrict_apply (μ := P) (s := S0)
        (t := rowVisitCylinderEventUpTo (k := k) i S v N)
        (measurableSet_rowVisitCylinderEventUpTo (k := k) i S v N)
    simpa [Set.inter_comm] using h.symm
  have hsum :=
    measure_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
      (k := k) (P := P.restrict S0) i S v N
  have hterm :
      ∀ xs : Fin (N + 1) → Fin k,
        (P.restrict S0) (cylinder (k := k) (List.ofFn xs)) =
          if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0 := by
    intro xs
    by_cases hxs : xs 0 = j
    · have hsubset : cylinder (k := k) (List.ofFn xs) ⊆ S0 := by
        intro ω hω
        have h0 : ω 0 = xs 0 := by
          have hω' := (mem_cylinder_ofFn_iff (k := k) ω N xs).1 hω
          simpa using hω' ⟨0, Nat.succ_pos _⟩
        simpa [S0, hxs] using h0
      have hmeas := measurableSet_cylinder (k := k) (List.ofFn xs)
      have hrestrict :
          (P.restrict S0) (cylinder (k := k) (List.ofFn xs)) =
            P (cylinder (k := k) (List.ofFn xs)) := by
        have hinter : S0 ∩ cylinder (k := k) (List.ofFn xs) =
            cylinder (k := k) (List.ofFn xs) := by
          ext ω
          constructor
          · intro hω
            exact hω.2
          · intro hω
            exact ⟨hsubset hω, hω⟩
        have hrestrict' :
            (P.restrict S0) (cylinder (k := k) (List.ofFn xs)) =
              P (cylinder (k := k) (List.ofFn xs) ∩ S0) :=
          Measure.restrict_apply (μ := P) (s := S0)
            (t := cylinder (k := k) (List.ofFn xs)) hmeas
        calc
          (P.restrict S0) (cylinder (k := k) (List.ofFn xs))
              = P (cylinder (k := k) (List.ofFn xs) ∩ S0) := hrestrict'
          _ = P (cylinder (k := k) (List.ofFn xs)) := by
                rw [Set.inter_comm, hinter]
      have hif :
          (if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) =
            P (cylinder (k := k) (List.ofFn xs)) := by
        simp [hxs, -List.ofFn_succ]
      calc
        (P.restrict S0) (cylinder (k := k) (List.ofFn xs))
            = P (cylinder (k := k) (List.ofFn xs)) := hrestrict
        _ = (if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
              symm; exact hif
    · have hdisj : S0 ∩ cylinder (k := k) (List.ofFn xs) = (∅ : Set (ℕ → Fin k)) := by
        ext ω
        constructor
        · intro hω
          have h0 : ω 0 = xs 0 := by
            have hω' := (mem_cylinder_ofFn_iff (k := k) ω N xs).1 hω.2
            simpa using hω' ⟨0, Nat.succ_pos _⟩
          have h0' : ω 0 = j := hω.1
          exact (hxs (by simpa [h0] using h0'))
        · intro hω
          cases hω
      have hmeas := measurableSet_cylinder (k := k) (List.ofFn xs)
      have hrestrict :
          (P.restrict S0) (cylinder (k := k) (List.ofFn xs)) = 0 := by
        have hrestrict' :
            (P.restrict S0) (cylinder (k := k) (List.ofFn xs)) =
              P (cylinder (k := k) (List.ofFn xs) ∩ S0) :=
          Measure.restrict_apply (μ := P) (s := S0)
            (t := cylinder (k := k) (List.ofFn xs)) hmeas
        calc
          (P.restrict S0) (cylinder (k := k) (List.ofFn xs))
              = P (cylinder (k := k) (List.ofFn xs) ∩ S0) := hrestrict'
          _ = 0 := by
                have hdisj' :
                    cylinder (k := k) (List.ofFn xs) ∩ S0 = (∅ : Set (ℕ → Fin k)) := by
                  simpa [Set.inter_comm, -List.ofFn_succ] using hdisj
                simp [hdisj', -List.ofFn_succ]
      have hif :
          (if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) = 0 := by
        simp [hxs, -List.ofFn_succ]
      calc
        (P.restrict S0) (cylinder (k := k) (List.ofFn xs)) = 0 := hrestrict
        _ = (if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
              symm; exact hif
  calc
    P (S0 ∩ rowVisitCylinderEventUpTo (k := k) i S v N)
        = (P.restrict S0) (rowVisitCylinderEventUpTo (k := k) i S v N) := hleft
    _ = Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
          (fun xs => (P.restrict S0) (cylinder (k := k) (List.ofFn xs))) := by
          simpa using hsum
    _ = Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
          (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro xs hx
          exact hterm xs

lemma evidenceOf_start_eq_of_eq {N : ℕ}
    {xs ys : Fin (N + 1) → Fin k}
    (he : evidenceOf (n := N) xs = evidenceOf (n := N) ys) :
    xs 0 = ys 0 := by
  simpa [evidenceOf] using congrArg MarkovEvidence.start he

lemma sum_cylinderProb_eq_of_extension_and_evidencePreservingEquiv_start
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    {N : ℕ}
    (A B : Finset (Fin (N + 1) → Fin k))
    (e : A ≃ B)
    (he : ∀ xs : A, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1)
    (j : Fin k) :
    Finset.sum A (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) =
      Finset.sum B (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) := by
  classical
  have hstart :
      ∀ xs : A, xs.1 0 = j ↔ (e xs).1 0 = j := by
    intro xs
    have heq := he xs
    have hstart_eq := evidenceOf_start_eq_of_eq (k := k) (N := N) heq
    constructor <;> intro h
    · simpa [hstart_eq] using h
    · simpa [hstart_eq] using h
  have hprob :
      ∀ xs : A,
        P (cylinder (k := k) (List.ofFn xs.1)) =
          P (cylinder (k := k) (List.ofFn (e xs).1)) := by
    intro xs
    have heq := he xs
    calc
      P (cylinder (k := k) (List.ofFn xs.1))
          = μ (List.ofFn xs.1) := (hExt (List.ofFn xs.1)).symm
      _ = μ (List.ofFn (e xs).1) := hμ N xs.1 (e xs).1 heq
      _ = P (cylinder (k := k) (List.ofFn (e xs).1)) := hExt (List.ofFn (e xs).1)
  have hsum :
      (∑ xs : A, (if xs.1 0 = j then P (cylinder (k := k) (List.ofFn xs.1)) else 0)) =
        (∑ ys : B, (if ys.1 0 = j then P (cylinder (k := k) (List.ofFn ys.1)) else 0)) := by
    refine Fintype.sum_equiv (e := e)
      (f := fun xs : A =>
        if xs.1 0 = j then P (cylinder (k := k) (List.ofFn xs.1)) else 0)
      (g := fun ys : B =>
        if ys.1 0 = j then P (cylinder (k := k) (List.ofFn ys.1)) else 0) ?_
    intro xs
    by_cases hxs : xs.1 0 = j
    · have hys : (e xs).1 0 = j := (hstart xs).1 hxs
      calc
        (if xs.1 0 = j then P (cylinder (k := k) (List.ofFn xs.1)) else 0)
            = P (cylinder (k := k) (List.ofFn xs.1)) := by simp [hxs]
        _ = P (cylinder (k := k) (List.ofFn (e xs).1)) := hprob xs
        _ = (if (e xs).1 0 = j then P (cylinder (k := k) (List.ofFn (e xs).1)) else 0) := by
            simp [hys]
    · have hys : (e xs).1 0 ≠ j := by
        intro hys
        exact hxs ((hstart xs).2 hys)
      calc
        (if xs.1 0 = j then P (cylinder (k := k) (List.ofFn xs.1)) else 0)
            = 0 := by simp [hxs]
        _ = (if (e xs).1 0 = j then P (cylinder (k := k) (List.ofFn (e xs).1)) else 0) := by
            simp [hys]
  have hA :
      Finset.sum A (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) =
        (∑ xs : A, (if xs.1 0 = j then P (cylinder (k := k) (List.ofFn xs.1)) else 0)) := by
    have hAattach :
        Finset.sum A (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) =
          ∑ xs : A, (if xs.1 0 = j then P (cylinder (k := k) (List.ofFn xs.1)) else 0) := by
      simpa using (Finset.sum_attach (s := A)
        (f := fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0)).symm
    exact hAattach
  have hB :
      Finset.sum B (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) =
        (∑ ys : B, (if ys.1 0 = j then P (cylinder (k := k) (List.ofFn ys.1)) else 0)) := by
    have hBattach :
        Finset.sum B (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) =
          ∑ ys : B, (if ys.1 0 = j then P (cylinder (k := k) (List.ofFn ys.1)) else 0) := by
      simpa using (Finset.sum_attach (s := B)
        (f := fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0)).symm
    exact hBattach
  calc
    Finset.sum A (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0)
        = (∑ xs : A, (if xs.1 0 = j then P (cylinder (k := k) (List.ofFn xs.1)) else 0)) := hA
    _ = (∑ ys : B, (if ys.1 0 = j then P (cylinder (k := k) (List.ofFn ys.1)) else 0)) := hsum
    _ = Finset.sum B (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) := hB.symm

lemma measure_start_inter_rowVisitCylinderEventUpTo_eq_of_evidencePreservingEquiv_start
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i₁ : Fin k) (S₁ : Finset ℕ) (v₁ : ℕ → Fin k)
    (i₂ : Fin k) (S₂ : Finset ℕ) (v₂ : ℕ → Fin k)
    (N : ℕ) (j : Fin k)
    (e :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N ≃
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)
    (he :
      ∀ xs :
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N,
        evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₁ S₁ v₁ N)
      =
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₂ S₂ v₂ N) := by
  have hleft :
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₁ S₁ v₁ N)
        =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
        (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) :=
    measure_start_inter_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
      (k := k) P i₁ S₁ v₁ N j
  have hright :
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₂ S₂ v₂ N)
        =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)
        (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) :=
    measure_start_inter_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
      (k := k) P i₂ S₂ v₂ N j
  have hsum :
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
          (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0)
        =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)
          (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) :=
    sum_cylinderProb_eq_of_extension_and_evidencePreservingEquiv_start
      (k := k) μ hμ P hExt
      (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
      (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)
      e he j
  calc
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₁ S₁ v₁ N)
        =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
        (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := hleft
    _ =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)
        (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) := hsum
    _ =
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowVisitCylinderEventUpTo (k := k) i₂ S₂ v₂ N) := hright.symm

lemma measure_start_inter_rowVisitSingletonUpTo_eq_of_evidencePreservingEquiv_start
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i j b : Fin k) (n n' N : ℕ)
    (e :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
        (fun m => if m = n then b else i) N ≃
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n'} : Finset ℕ)
        (fun m => if m = n' then b else i) N)
    (he :
      ∀ xs :
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
          (fun m => if m = n then b else i) N,
        evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩
        rowVisitCylinderEventUpTo (k := k) i ({n} : Finset ℕ)
          (fun m => if m = n then b else i) N)
      =
    P ({ω : ℕ → Fin k | ω 0 = j} ∩
        rowVisitCylinderEventUpTo (k := k) i ({n'} : Finset ℕ)
          (fun m => if m = n' then b else i) N) := by
  exact
    measure_start_inter_rowVisitCylinderEventUpTo_eq_of_evidencePreservingEquiv_start
      (k := k) μ hμ P hExt
      i ({n} : Finset ℕ) (fun m => if m = n then b else i)
      i ({n'} : Finset ℕ) (fun m => if m = n' then b else i)
      N j e he

/-- Finite-index version of the no-`none` branch witness extraction. -/
lemma rowVisitCylinderEventUpTo_mono
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    Monotone (fun N : ℕ => rowVisitCylinderEventUpTo (k := k) i S v N) := by
  intro N M hNM ω hω n hnS
  rcases hω n hnS with ⟨t, htN, htime, hsucc⟩
  refine ⟨t, lt_of_lt_of_le htN hNM, htime, hsucc⟩

lemma measure_start_inter_rowSuccessorValueEvent_eq_of_evidencePreservingEquiv_start
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i j b : Fin k) (n n' : ℕ)
    (hbi : b ≠ i)
    (hEquiv :
      ∀ N : ℕ,
        ∃ e :
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
            (fun m => if m = n then b else i) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n'} : Finset ℕ)
              (fun m => if m = n' then b else i) N,
          ∀ xs :
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
              (fun m => if m = n then b else i) N,
            evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n b)
      =
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n' b) := by
  let S0 : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = j}
  let A : ℕ → Set (ℕ → Fin k) :=
    fun N =>
      rowVisitCylinderEventUpTo (k := k) i ({n} : Finset ℕ)
        (fun m => if m = n then b else i) N
  let B : ℕ → Set (ℕ → Fin k) :=
    fun N =>
      rowVisitCylinderEventUpTo (k := k) i ({n'} : Finset ℕ)
        (fun m => if m = n' then b else i) N
  have hrowA : rowSuccessorValueEvent (k := k) i n b = ⋃ N : ℕ, A N := by
    simpa [A] using
      (rowSuccessorValueEvent_eq_iUnion_upTo_of_ne (k := k) i n b hbi)
  have hrowB : rowSuccessorValueEvent (k := k) i n' b = ⋃ N : ℕ, B N := by
    simpa [B] using
      (rowSuccessorValueEvent_eq_iUnion_upTo_of_ne (k := k) i n' b hbi)
  have hintA :
      S0 ∩ rowSuccessorValueEvent (k := k) i n b
        =
      ⋃ N : ℕ, S0 ∩ A N := by
    rw [hrowA, Set.inter_iUnion]
  have hintB :
      S0 ∩ rowSuccessorValueEvent (k := k) i n' b
        =
      ⋃ N : ℕ, S0 ∩ B N := by
    rw [hrowB, Set.inter_iUnion]
  have hmonoA : Monotone (fun N : ℕ => S0 ∩ A N) := by
    intro N M hNM ω hω
    refine ⟨hω.1, ?_⟩
    exact (rowVisitCylinderEventUpTo_mono (k := k) i ({n} : Finset ℕ)
      (fun m => if m = n then b else i) hNM) hω.2
  have hmonoB : Monotone (fun N : ℕ => S0 ∩ B N) := by
    intro N M hNM ω hω
    refine ⟨hω.1, ?_⟩
    exact (rowVisitCylinderEventUpTo_mono (k := k) i ({n'} : Finset ℕ)
      (fun m => if m = n' then b else i) hNM) hω.2
  have hNeq : ∀ N : ℕ, P (S0 ∩ A N) = P (S0 ∩ B N) := by
    intro N
    rcases hEquiv N with ⟨e, he⟩
    simpa [S0, A, B] using
      (measure_start_inter_rowVisitSingletonUpTo_eq_of_evidencePreservingEquiv_start
        (k := k) μ hμ P hExt i j b n n' N e he)
  have hSupEq :
      (⨆ N : ℕ, P (S0 ∩ A N)) = ⨆ N : ℕ, P (S0 ∩ B N) := by
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro N
      exact le_iSup_of_le N (hNeq N).le
    · refine iSup_le ?_
      intro N
      exact le_iSup_of_le N (hNeq N).ge
  calc
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n b)
        = P (S0 ∩ rowSuccessorValueEvent (k := k) i n b) := by simp [S0]
    _ = P (⋃ N : ℕ, S0 ∩ A N) := by rw [hintA]
    _ = ⨆ N : ℕ, P (S0 ∩ A N) := hmonoA.measure_iUnion
    _ = ⨆ N : ℕ, P (S0 ∩ B N) := hSupEq
    _ = P (⋃ N : ℕ, S0 ∩ B N) := (hmonoB.measure_iUnion).symm
    _ = P (S0 ∩ rowSuccessorValueEvent (k := k) i n' b) := by rw [hintB]
    _ = P ({ω : ℕ → Fin k | ω 0 = j} ∩ rowSuccessorValueEvent (k := k) i n' b) := by simp [S0]

def rowPermute (σ : Equiv.Perm ℕ) (r : ℕ → Fin k) : ℕ → Fin k :=
  fun n => r (σ n)

theorem rowProcessLaw_exchangeable_of_perm_invariant
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P] (i : Fin k)
    (hperm :
      ∀ σ : Equiv.Perm ℕ,
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i) :
    Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
      (fun n (r : ℕ → Fin k) => r n) := by
  letI : IsProbabilityMeasure (rowProcessLaw (k := k) P i) :=
    Measure.isProbabilityMeasure_map
      ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
  have hmeas : ∀ n : ℕ, Measurable (fun r : ℕ → Fin k => r n) := by
    intro n
    exact measurable_pi_apply n
  have hfull :
      Exchangeability.FullyExchangeable (rowProcessLaw (k := k) P i)
        (fun n (r : ℕ → Fin k) => r n) := by
    intro π
    have h : Measure.map (fun ω i => ω (π i)) (rowProcessLaw (k := k) P i) =
        rowProcessLaw (k := k) P i := hperm π
    simpa [Exchangeability.reindex] using h
  exact (Exchangeability.exchangeable_iff_fullyExchangeable
    (μ := rowProcessLaw (k := k) P i)
    (X := fun n (r : ℕ → Fin k) => r n) hmeas).2 hfull

theorem rowProcessLaw_conditionallyIID_of_perm_invariant
    (hk : 0 < k)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P] (i : Fin k)
    (hperm :
      ∀ σ : Equiv.Perm ℕ,
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i) :
    Exchangeability.ConditionallyIID (rowProcessLaw (k := k) P i)
      (fun n (r : ℕ → Fin k) => r n) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  letI : IsProbabilityMeasure (rowProcessLaw (k := k) P i) :=
    Measure.isProbabilityMeasure_map
      ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
  have hmeas : ∀ n : ℕ, Measurable (fun r : ℕ → Fin k => r n) := by
    intro n
    exact measurable_pi_apply n
  have hexch :
      Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
        (fun n (r : ℕ → Fin k) => r n) :=
    rowProcessLaw_exchangeable_of_perm_invariant (k := k) P i hperm
  exact Exchangeability.DeFinetti.deFinetti
    (μ := rowProcessLaw (k := k) P i)
    (X := fun n (r : ℕ → Fin k) => r n)
    hmeas hexch

/-- Convert an initial-law kernel and row-transition kernels into a Markov
parameter valued map on path space. -/
def rowKernelToMarkovParam
    (initKernel : (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) :
    (ℕ → Fin k) → MarkovParam k :=
  fun ω =>
    { init := initKernel ω
      trans := fun i => rowKernel i ω }

/-- Lift a row-process kernel family to path space by composing with the
visit-indexed row process map. -/
def liftedRowKernelFromRowProcess
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) :
    Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k) :=
  fun i ω => rowKernel i (rowSuccessorVisitProcess (k := k) i ω)

/-- Canonical specialization with Dirac initial law at the path start `ω 0`. -/
def rowKernelToMarkovParam_diracInit
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) :
    (ℕ → Fin k) → MarkovParam k :=
  rowKernelToMarkovParam (k := k)
    (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
    rowKernel

/-- Pointwise identification of the one-step transition mass after lifting a
row-process kernel family to path space. -/
lemma stepProb_rowKernelToMarkovParam_diracInit_lifted_eq
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (ω : ℕ → Fin k) (i b : Fin k) :
    (stepProb (k := k)
      (rowKernelToMarkovParam_diracInit (k := k)
        (rowKernel := liftedRowKernelFromRowProcess (k := k) rowKernel) ω)
      i b : ENNReal)
      =
    ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω) : Measure (Fin k))
      (Set.singleton b)) := by
  simp [rowKernelToMarkovParam_diracInit, rowKernelToMarkovParam,
    liftedRowKernelFromRowProcess, stepProb]

/-! ### AE-measurability of row-kernel-to-MarkovParam map

The following block proves `AEMeasurable` of `rowKernelToMarkovParam_diracInit` by
decomposing `wordProb` into products of `initProb` (measurable, Dirac indicator)
and `stepProb` (AE-measurable via row-kernel evaluations). -/

namespace AemeasurableRowKernel

private lemma aemeasurable_stepProb_ennreal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval : ∀ i b : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (rowProcessLaw (k := k) P i))
    (a b : Fin k) :
    AEMeasurable
      (fun ω : ℕ → Fin k =>
        (stepProb (k := k)
          (rowKernelToMarkovParam_diracInit (k := k)
            (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) a b : ENNReal)) P := by
  have heq : (fun ω : ℕ → Fin k =>
      (stepProb (k := k)
        (rowKernelToMarkovParam_diracInit (k := k)
          (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) a b : ENNReal))
    = (fun ω => (rowKernel a (rowSuccessorVisitProcess (k := k) a ω) : Measure (Fin k))
        ({b} : Set (Fin k))) := by
    ext ω; exact stepProb_rowKernelToMarkovParam_diracInit_lifted_eq _ ω a b
  rw [heq]
  exact (hEval a b).comp_measurable (measurable_rowSuccessorVisitProcess a)

private lemma aemeasurable_wordProbAux_ennreal
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval : ∀ i b : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (rowProcessLaw (k := k) P i))
    (a : Fin k) (xs : List (Fin k)) :
    AEMeasurable
      (fun ω : ℕ → Fin k =>
        (wordProbAux (k := k)
          (rowKernelToMarkovParam_diracInit (k := k)
            (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) a xs : ENNReal)) P := by
  induction xs generalizing a with
  | nil => simp only [wordProbAux]; exact aemeasurable_const
  | cons b xs ih =>
    simp only [wordProbAux, ENNReal.coe_mul]
    exact (aemeasurable_stepProb_ennreal P rowKernel hEval a b).mul (ih b)

private lemma measurable_initProb_ennreal
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a : Fin k) :
    Measurable (fun ω : ℕ → Fin k =>
      (initProb (k := k)
        (rowKernelToMarkovParam_diracInit (k := k)
          (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) a : ENNReal)) := by
  have heq : (fun ω : ℕ → Fin k =>
      (initProb (k := k)
        (rowKernelToMarkovParam_diracInit (k := k)
          (liftedRowKernelFromRowProcess (k := k) rowKernel) ω) a : ENNReal))
    = (fun ω => Measure.dirac (ω 0) ({a} : Set (Fin k))) := by
    ext ω
    simp only [initProb, rowKernelToMarkovParam_diracInit, rowKernelToMarkovParam]
    exact ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure _ _
  rw [heq]
  have heq2 : (fun ω : ℕ → Fin k => Measure.dirac (ω 0) ({a} : Set (Fin k))) =
      (fun ω => if ω 0 = a then (1 : ENNReal) else 0) := by
    ext ω
    rw [Measure.dirac_apply' _ (measurableSet_singleton a)]
    simp [Set.indicator_singleton, Pi.single_apply]
  rw [heq2]
  apply Measurable.ite _ measurable_const measurable_const
  have : {ω : ℕ → Fin k | ω 0 = a} = (fun f : ℕ → Fin k => f 0) ⁻¹' {a} := by ext; simp
  rw [this]
  exact (measurable_pi_apply 0) (measurableSet_singleton a)

end AemeasurableRowKernel

/-- **AE-measurability of the row-kernel-to-MarkovParam map.**
    This discharges the `hθExt` parameter by showing that every `wordProb`
    composition is AE-measurable: `initProb` via Dirac indicator (measurable),
    `stepProb` via `hEval` + `AEMeasurable.comp_measurable`, products via
    `AEMeasurable.mul`, and the NNReal→ENNReal cast via `coe_nnreal_ennreal`. -/
theorem aemeasurable_rowKernelToMarkovParam_diracInit_lifted
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval : ∀ i b : Fin k,
      AEMeasurable
        (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
        (rowProcessLaw (k := k) P i)) :
    AEMeasurable
      (rowKernelToMarkovParam_diracInit (k := k)
        (liftedRowKernelFromRowProcess (k := k) rowKernel)) P := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · haveI : IsEmpty (MarkovParam 0) := by
      constructor; intro ⟨init, _⟩
      have h := init.prop.measure_univ
      rw [show (Set.univ : Set (Fin 0)) = ∅ from Set.eq_empty_of_isEmpty _] at h
      simp at h
    exact aemeasurable_of_subsingleton_codomain
  · set θ₀ : MarkovParam k :=
      { init := ⟨Measure.dirac ⟨0, hk⟩, Measure.dirac.isProbabilityMeasure⟩
        trans := fun _ => ⟨Measure.dirac ⟨0, hk⟩, Measure.dirac.isProbabilityMeasure⟩ }
    exact aemeasurable_into_markovParam _ P θ₀ (fun xs => by
      induction xs with
      | nil =>
        simp only [wordProb, wordProbNN]
        exact aemeasurable_const
      | cons a xs _ =>
        simp only [wordProb, wordProbNN, ENNReal.coe_mul]
        exact (AemeasurableRowKernel.measurable_initProb_ennreal rowKernel a).aemeasurable.mul
          (AemeasurableRowKernel.aemeasurable_wordProbAux_ennreal P rowKernel hEval a xs))

/-- Pushforward law on `MarkovParam k` induced by row kernels. -/
def rowKernelToMarkovParamLaw
    (P : Measure (ℕ → Fin k))
    (initKernel : (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) :
    Measure (MarkovParam k) :=
  Measure.map (rowKernelToMarkovParam (k := k) initKernel rowKernel) P

/-- Change-of-variables form of the `wordProb` integral under the row-kernel
induced `MarkovParam` law. This is the first reconstruction bridge used in the
Fortini path. -/
theorem lintegral_wordProb_rowKernelToMarkovParamLaw
    (P : Measure (ℕ → Fin k))
    (initKernel : (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (xs : List (Fin k))
  (hθ :
      AEMeasurable
        (rowKernelToMarkovParam (k := k) initKernel rowKernel) P) :
    (∫⁻ θ, wordProb (k := k) θ xs
      ∂(rowKernelToMarkovParamLaw (k := k) P initKernel rowKernel))
      =
    ∫⁻ ω, wordProb (k := k)
      (rowKernelToMarkovParam (k := k) initKernel rowKernel ω) xs ∂P := by
  have hwordAemeas :
      AEMeasurable (fun θ : MarkovParam k => wordProb (k := k) θ xs)
        (rowKernelToMarkovParamLaw (k := k) P initKernel rowKernel) :=
    (measurable_wordProb xs).aemeasurable
  simpa [rowKernelToMarkovParamLaw] using
    (MeasureTheory.lintegral_map'
      (μ := P)
      (f := fun θ : MarkovParam k => wordProb (k := k) θ xs)
      (g := rowKernelToMarkovParam (k := k) initKernel rowKernel)
      hwordAemeas hθ)

/-- Base finite-prefix reconstruction (empty prefix) for the row-kernel bridge. -/
theorem rowKernelToMarkovParamLaw_reconstruction_nil
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (initKernel : (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hθ :
      AEMeasurable
        (rowKernelToMarkovParam (k := k) initKernel rowKernel) P) :
    P (MarkovDeFinettiRecurrence.cylinder (k := k) []) =
      (∫⁻ θ, wordProb (k := k) θ []
        ∂(rowKernelToMarkovParamLaw (k := k) P initKernel rowKernel)) := by
  have hcylNil :
      MarkovDeFinettiRecurrence.cylinder (k := k) ([] : List (Fin k)) = Set.univ := by
    ext ω
    simp [MarkovDeFinettiRecurrence.cylinder]
  calc
    P (MarkovDeFinettiRecurrence.cylinder (k := k) []) = P Set.univ := by
      simp [hcylNil]
    _ = 1 := by simp
    _ = (∫⁻ ω, wordProb (k := k)
          (rowKernelToMarkovParam (k := k) initKernel rowKernel ω) [] ∂P) := by
      simp [wordProb, wordProbNN]
    _ = (∫⁻ θ, wordProb (k := k) θ []
          ∂(rowKernelToMarkovParamLaw (k := k) P initKernel rowKernel)) := by
      symm
      exact lintegral_wordProb_rowKernelToMarkovParamLaw
        (k := k) P initKernel rowKernel [] hθ

/-- One-step finite-prefix reconstruction for the Dirac-start row-kernel bridge. -/
theorem rowKernelToMarkovParamLaw_reconstruction_singleton_diracInit
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hθ :
      AEMeasurable
        (rowKernelToMarkovParam (k := k)
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          rowKernel) P)
    (a : Fin k) :
    P (MarkovDeFinettiRecurrence.cylinder (k := k) [a]) =
      (∫⁻ θ, wordProb (k := k) θ [a]
        ∂(rowKernelToMarkovParamLaw (k := k) P
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          rowKernel)) := by
  let s : Set (ℕ → Fin k) := {ω | ω 0 = a}
  let ind : (ℕ → Fin k) → ENNReal := s.indicator (fun _ => (1 : ENNReal))
  have hmeas_s : MeasurableSet s := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' Set.singleton a)
    exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
  have hcyl :
      MarkovDeFinettiRecurrence.cylinder (k := k) [a] = s := by
    ext ω
    simp [MarkovDeFinettiRecurrence.cylinder, s]
  calc
    P (MarkovDeFinettiRecurrence.cylinder (k := k) [a]) = P s := by
      simp [hcyl]
    _ = ∫⁻ ω, ind ω ∂P := by
      have hlin : ∫⁻ ω, ind ω ∂P = P s := by
        simpa [ind, Pi.one_def] using (lintegral_indicator_one (μ := P) (s := s) hmeas_s)
      exact hlin.symm
    _ = ∫⁻ ω, wordProb (k := k)
          (rowKernelToMarkovParam (k := k)
            (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
            rowKernel ω) [a] ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards with ω
      by_cases hω : ω 0 = a
      · have hmem : a ∈ (Set.singleton a : Set (Fin k)) := Set.mem_singleton a
        simp [rowKernelToMarkovParam, wordProb, wordProbNN, wordProbAux, initProb, s, ind,
          Set.indicator, hω, hmem]
      · have hmem : ω 0 ∉ (Set.singleton a : Set (Fin k)) := by
          intro hmem'
          exact hω hmem'
        simp [rowKernelToMarkovParam, wordProb, wordProbNN, wordProbAux, initProb, s, ind,
          Set.indicator, hω, hmem]
    _ = ∫⁻ θ, wordProb (k := k) θ [a]
          ∂(rowKernelToMarkovParamLaw (k := k) P
            (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
            rowKernel) := by
      symm
      exact
        lintegral_wordProb_rowKernelToMarkovParamLaw
          (k := k) P
          (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
          rowKernel [a] hθ

/-- Strengthened extraction from row-wise `ConditionallyIID`:
returns a row-kernel family with (i) finite-dimensional bind law,
(ii) AE-measurability of singleton evaluations, and
(iii) AE-measurability of the `Fin 1` product-kernel map. -/
theorem exists_rowKernelFamily_with_aemeasurableEvalPi_of_rowProcess_conditionallyIID
    (P : Measure (ℕ → Fin k))
    (hciid :
      ∀ i : Fin k,
        Exchangeability.ConditionallyIID (rowProcessLaw (k := k) P i)
          (fun n (r : ℕ → Fin k) => r n)) :
    ∃ rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k),
      (∀ i : Fin k, ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) P i)
          =
        (rowProcessLaw (k := k) P i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k))))) ∧
      (∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i)) ∧
      (∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i)) := by
  classical
  let ν : Fin k → (ℕ → Fin k) → Measure (Fin k) :=
    fun i => Classical.choose (hciid i)
  have hνspec :
      ∀ i : Fin k,
        (∀ r : ℕ → Fin k, IsProbabilityMeasure (ν i r)) ∧
        (∀ B : Set (Fin k), MeasurableSet B → Measurable (fun r => ν i r B)) ∧
        (∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
          Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
              (rowProcessLaw (k := k) P i)
            =
          (rowProcessLaw (k := k) P i).bind
            (fun r => Measure.pi (fun _ : Fin m => ν i r))) := by
    intro i
    exact Classical.choose_spec (hciid i)
  let rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k) :=
    fun i r => ⟨ν i r, (hνspec i).1 r⟩
  refine ⟨rowKernel, ?_, ?_, ?_⟩
  · intro i m sel hsel
    simpa [rowKernel] using (hνspec i).2.2 m sel hsel
  · intro i b
    have hmeas :
        Measurable (fun r : ℕ → Fin k => ν i r ({b} : Set (Fin k))) :=
      (hνspec i).2.1 ({b} : Set (Fin k)) (MeasurableSet.singleton b)
    simpa [rowKernel] using hmeas.aemeasurable
  · intro i
    have hpiMeas :
        Measurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => ν i r)) :=
      measurable_measure_pi (ν i) (fun r => (hνspec i).1 r) (hνspec i).2.1
    simpa [rowKernel] using hpiMeas.aemeasurable

/-- Strengthened variant of `exists_rowKernelFamily_of_rowProcess_permInvariant`
providing AE-measurability of singleton evaluations and `Fin 1` product-kernel
maps, suitable for the pair-reconstruction pipeline. -/
theorem exists_rowKernelFamily_with_aemeasurableEvalPi_of_rowProcess_permInvariant
    (hk : 0 < k)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hpermAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i) :
    ∃ rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k),
      (∀ i : Fin k, ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
        Measure.map (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
            (rowProcessLaw (k := k) P i)
          =
        (rowProcessLaw (k := k) P i).bind
          (fun r => Measure.pi (fun _ : Fin m => (rowKernel i r : Measure (Fin k))))) ∧
      (∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i)) ∧
      (∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i)) := by
  have hciid :
      ∀ i : Fin k,
        Exchangeability.ConditionallyIID (rowProcessLaw (k := k) P i)
          (fun n (r : ℕ → Fin k) => r n) := by
    intro i
    exact
      rowProcessLaw_conditionallyIID_of_perm_invariant
        (k := k) hk P i (fun σ => hpermAll i σ (inferInstance : IsFiniteMeasure P))
  exact
    exists_rowKernelFamily_with_aemeasurableEvalPi_of_rowProcess_conditionallyIID
      (k := k) P hciid

/-- Indicator of a row-successor value event. -/
def rowSuccessorValueIndicator
    (i : Fin k) (n : ℕ) (b : Fin k) : (ℕ → Fin k) → ENNReal :=
  (rowSuccessorValueEvent (k := k) i n b).indicator (fun _ => (1 : ENNReal))

lemma measurable_rowSuccessorValueIndicator
    (i : Fin k) (n : ℕ) (b : Fin k) :
    Measurable (rowSuccessorValueIndicator i n b) := by
  classical
  have hs : MeasurableSet (rowSuccessorValueEvent (k := k) i n b) :=
    measurableSet_rowSuccessorValueEvent (k := k) i n b
  simpa [rowSuccessorValueIndicator] using (measurable_const.indicator hs)

lemma lintegral_indicator_mul_indicator_eq_measure_inter
    {α : Type} [MeasurableSpace α] (P : Measure α)
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ ω, (s.indicator (fun _ => (1 : ENNReal)) ω) *
        (t.indicator (fun _ => (1 : ENNReal)) ω) ∂P =
      P (s ∩ t) := by
  classical
  have hmul :
      (fun ω =>
        (s.indicator (fun _ => (1 : ENNReal)) ω) *
          (t.indicator (fun _ => (1 : ENNReal)) ω))
        =
      (fun ω => (s ∩ t).indicator (fun _ => (1 : ENNReal)) ω) := by
    funext ω
    by_cases hsω : ω ∈ s
    · by_cases htω : ω ∈ t
      · simp [Set.indicator, hsω, htω, Set.mem_inter_iff]
      · simp [Set.indicator, hsω, htω, Set.mem_inter_iff]
    · by_cases htω : ω ∈ t
      · simp [Set.indicator, hsω, htω, Set.mem_inter_iff]
      · simp [Set.indicator, hsω, htω, Set.mem_inter_iff]
  have hmeas : MeasurableSet (s ∩ t) := hs.inter ht
  simpa [hmul, Pi.one_def] using (lintegral_indicator_one (μ := P) (s := s ∩ t) hmeas)

lemma lintegral_start_cesaro_eq_const
    (P : Measure (ℕ → Fin k))
    (i a b : Fin k) (N : ℕ) (c : ENNReal)
    (hconst :
      ∀ n : ℕ,
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) i n b) = c) :
    ∫⁻ ω,
        (if ω 0 = a then
          ((↑(N + 1) : ENNReal)⁻¹ *
            Finset.sum (Finset.range (N + 1))
              (fun n => rowSuccessorValueIndicator i n b ω))
          else 0) ∂P
      = c := by
  classical
  let s : Set (ℕ → Fin k) := {ω | ω 0 = a}
  let S : Finset ℕ := Finset.range (N + 1)
  have hmeas_s : MeasurableSet s := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' Set.singleton a)
    exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
  have hind :
      (fun ω =>
        if ω 0 = a then
          ((↑(N + 1) : ENNReal)⁻¹ *
            Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω))
          else 0)
        =
      s.indicator (fun ω =>
        ((↑(N + 1) : ENNReal)⁻¹ *
          Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω))) := by
    funext ω
    by_cases hω : ω 0 = a
    · simp [s, hω]
    · simp [s, hω]
  -- rewrite as indicator * sum
  have hind_mul :
      s.indicator (fun ω =>
        ((↑(N + 1) : ENNReal)⁻¹ *
          Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω)))
        =
      fun ω =>
        (s.indicator (fun _ => (1 : ENNReal)) ω) *
          ((↑(N + 1) : ENNReal)⁻¹ *
            Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω)) := by
    funext ω
    by_cases hω : ω 0 = a
    · simp [Set.indicator, s, hω]
    · simp [Set.indicator, s, hω]
  have hsum_meas :
      Measurable
        (fun ω =>
          Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω)) := by
    classical
    refine Finset.measurable_sum (s := S) ?_
    intro n hn
    exact measurable_rowSuccessorValueIndicator i n b
  calc
    ∫⁻ ω,
        (if ω 0 = a then
          ((↑(N + 1) : ENNReal)⁻¹ *
            Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω))
          else 0) ∂P
        = ∫⁻ ω,
          s.indicator (fun ω =>
          ((↑(N + 1) : ENNReal)⁻¹ *
              Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω))) ω ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          have h := congrArg (fun f => f ω) hind
          simpa using h
    _ = ∫⁻ ω,
          (s.indicator (fun _ => (1 : ENNReal)) ω) *
            ((↑(N + 1) : ENNReal)⁻¹ *
              Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω)) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          have h := congrArg (fun f => f ω) hind_mul
          simpa using h
    _ = ((↑(N + 1) : ENNReal)⁻¹) *
          Finset.sum S (fun n => P (s ∩ rowSuccessorValueEvent (k := k) i n b)) := by
          -- pull out constant and expand sum
          have hconst_mul :
              ∫⁻ ω,
                  (s.indicator (fun _ => (1 : ENNReal)) ω) *
                    ((↑(N + 1) : ENNReal)⁻¹ *
                      Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω)) ∂P
                =
                ((↑(N + 1) : ENNReal)⁻¹) *
                  ∫⁻ ω,
                    (s.indicator (fun _ => (1 : ENNReal)) ω) *
                      (Finset.sum S (fun n =>
                        rowSuccessorValueIndicator i n b ω)) ∂P := by
            have hmeas_prod :
                Measurable
                  (fun ω =>
                    (s.indicator (fun _ => (1 : ENNReal)) ω) *
                      (Finset.sum S (fun n =>
                        rowSuccessorValueIndicator i n b ω))) := by
              have hmeas_ind :
                  Measurable (s.indicator (fun _ => (1 : ENNReal))) :=
                (measurable_const.indicator hmeas_s)
              exact hmeas_ind.mul hsum_meas
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (lintegral_const_mul (μ := P) (r := (↑(N + 1) : ENNReal)⁻¹) hmeas_prod)
          have hsum :
              ∫⁻ ω,
                (s.indicator (fun _ => (1 : ENNReal)) ω) *
                  (Finset.sum S (fun n =>
                    rowSuccessorValueIndicator i n b ω)) ∂P
                =
                Finset.sum S (fun n =>
                  ∫⁻ ω,
                    (s.indicator (fun _ => (1 : ENNReal)) ω) *
                      rowSuccessorValueIndicator i n b ω ∂P) := by
            have hsum' :
                (fun ω =>
                  (s.indicator (fun _ => (1 : ENNReal)) ω) *
                    (Finset.sum S (fun n => rowSuccessorValueIndicator i n b ω)))
                  =
                (fun ω =>
                  ∑ n ∈ S,
                    (s.indicator (fun _ => (1 : ENNReal)) ω) *
                      rowSuccessorValueIndicator i n b ω) := by
              funext ω
              simp [Finset.mul_sum]
            calc
              ∫⁻ ω,
                (s.indicator (fun _ => (1 : ENNReal)) ω) *
                  (Finset.sum S (fun n =>
                    rowSuccessorValueIndicator i n b ω)) ∂P
                  = ∫⁻ ω,
                    ∑ n ∈ S,
                      (s.indicator (fun _ => (1 : ENNReal)) ω) *
                        rowSuccessorValueIndicator i n b ω ∂P := by
                      simp [hsum']
              _ = Finset.sum S (fun n =>
                    ∫⁻ ω,
                      (s.indicator (fun _ => (1 : ENNReal)) ω) *
                        rowSuccessorValueIndicator i n b ω ∂P) := by
                    refine lintegral_finset_sum' _ ?_
                    intro n hn
                    have hmeas_ind :
                        Measurable (s.indicator (fun _ => (1 : ENNReal))) :=
                      (measurable_const.indicator hmeas_s)
                    have hmeas_ev :
                        Measurable (rowSuccessorValueIndicator i n b) :=
                      measurable_rowSuccessorValueIndicator i n b
                    exact (hmeas_ind.mul hmeas_ev).aemeasurable
          have hpair :
              ∀ n : ℕ,
                ∫⁻ ω,
                    (s.indicator (fun _ => (1 : ENNReal)) ω) *
                      rowSuccessorValueIndicator i n b ω ∂P
                  =
                  P (s ∩ rowSuccessorValueEvent (k := k) i n b) := by
            intro n
            have hs : MeasurableSet s := hmeas_s
            have ht :
                MeasurableSet (rowSuccessorValueEvent (k := k) i n b) :=
              measurableSet_rowSuccessorValueEvent (k := k) i n b
            simpa [rowSuccessorValueIndicator] using
              (lintegral_indicator_mul_indicator_eq_measure_inter
                (P := P)
                (s := s)
                (t := rowSuccessorValueEvent (k := k) i n b)
                hs ht)
          calc
            ∫⁻ ω,
                (s.indicator (fun _ => (1 : ENNReal)) ω) *
                  ((↑(N + 1) : ENNReal)⁻¹ *
                    Finset.sum S (fun n =>
                      rowSuccessorValueIndicator i n b ω)) ∂P
                = ((↑(N + 1) : ENNReal)⁻¹) *
                    Finset.sum S (fun n =>
                      ∫⁻ ω,
                        (s.indicator (fun _ => (1 : ENNReal)) ω) *
                          rowSuccessorValueIndicator i n b ω ∂P) := by
                    simpa [hsum] using hconst_mul
            _ = ((↑(N + 1) : ENNReal)⁻¹) *
                  Finset.sum S (fun n =>
                    P (s ∩ rowSuccessorValueEvent (k := k) i n b)) := by
                    refine congrArg (fun x => ((↑(N + 1) : ENNReal)⁻¹) * x) ?_
                    refine Finset.sum_congr rfl ?_
                    intro n hn
                    exact hpair n
    _ = c := by
          -- use the constancy hypothesis
          have hsum_const :
              Finset.sum S (fun n =>
                P (s ∩ rowSuccessorValueEvent (k := k) i n b))
              =
              (N + 1 : ℕ) • c := by
            classical
            calc
              Finset.sum S (fun n =>
                  P (s ∩ rowSuccessorValueEvent (k := k) i n b))
                  = Finset.sum S (fun _ => c) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      simpa [s] using hconst n
              _ = (S.card : ℕ) • c := by
                    simp [Finset.sum_const]
              _ = (N + 1 : ℕ) • c := by
                    simp [S, Finset.card_range]
          have hpos : (↑(N + 1) : ENNReal) ≠ 0 := by
            simp
          have hinf : (↑(N + 1) : ENNReal) ≠ (⊤ : ENNReal) := by
            exact (ENNReal.natCast_ne_top (N + 1))
          calc
            ((↑(N + 1) : ENNReal)⁻¹) *
                Finset.sum S (fun n => P (s ∩ rowSuccessorValueEvent (k := k) i n b))
                = ((↑(N + 1) : ENNReal)⁻¹) * ((N + 1 : ℕ) • c) := by
                    simp [hsum_const]
            _ = ((↑(N + 1) : ENNReal)⁻¹) * ((↑(N + 1) : ENNReal) * c) := by
                    simp [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
            _ = c := by
                    have hmul0 :
                        (↑(N + 1) : ENNReal)⁻¹ * (↑(N + 1) : ENNReal) = 1 := by
                      simpa [mul_comm] using (ENNReal.mul_inv_cancel hpos hinf)
                    have hmul :
                        (↑N + 1 : ENNReal)⁻¹ * (↑N + 1 : ENNReal) = 1 := by
                      simpa [Nat.cast_add, Nat.cast_one] using hmul0
                    calc
                      (↑(N + 1) : ENNReal)⁻¹ * ((↑(N + 1) : ENNReal) * c)
                          = (↑N + 1 : ENNReal)⁻¹ * ((↑N + 1 : ENNReal) * c) := by
                              simp [Nat.cast_add, Nat.cast_one]
                      _ = (↑N + 1 : ENNReal)⁻¹ * (↑N + 1 : ENNReal) * c := by
                              simp [mul_assoc]
                      _ = 1 * c := by simp [hmul]
                      _ = c := by simp

lemma pair_identity_of_constancy_and_cesaro_limit
    (P : Measure (ℕ → Fin k)) (i a b : Fin k)
    (c L : ENNReal)
    (hconst :
      ∀ n : ℕ,
        P ({ω : ℕ → Fin k | ω 0 = a} ∩
            rowSuccessorValueEvent (k := k) i n b) = c)
    (hlim :
      Filter.Tendsto
        (fun N : ℕ =>
          ∫⁻ ω,
            (if ω 0 = a then
              ((↑(N + 1) : ENNReal)⁻¹ *
                Finset.sum (Finset.range (N + 1))
                  (fun n => rowSuccessorValueIndicator i n b ω))
              else 0) ∂P)
        Filter.atTop (nhds L)) :
    c = L := by
  have hconstN :
      ∀ N : ℕ,
        (∫⁻ ω,
            (if ω 0 = a then
              ((↑(N + 1) : ENNReal)⁻¹ *
                Finset.sum (Finset.range (N + 1))
                  (fun n => rowSuccessorValueIndicator i n b ω))
              else 0) ∂P) = c := by
    intro N
    exact lintegral_start_cesaro_eq_const (k := k) P i a b N c hconst
  have hlim' : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds L) := by
    refine (tendsto_congr' ?_).1 hlim
    exact Filter.Eventually.of_forall (fun N => hconstN N)
  have hconstlim : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c) :=
    tendsto_const_nhds
  exact (tendsto_nhds_unique hconstlim hlim')

/-! ### Class-Based Row Process Infrastructure

Extends row process machinery to handle recurrent classes rather than single states.
-/

section ClassRowProcess

variable (C : Set (Fin k))

/-- The row process law restricted to trajectories starting in class C. -/
noncomputable def rowProcessLaw_restrictClass (P : Measure (ℕ → Fin k)) (i : Fin k) :
    Measure (ℕ → Fin k) :=
  rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 ∈ C}) i

/-- Measurability of the class membership event. -/
lemma measurableSet_start_mem_class :
    MeasurableSet {ω : ℕ → Fin k | ω 0 ∈ C} := by
  show MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' C)
  exact (measurable_pi_apply 0) (Set.Finite.measurableSet (Set.toFinite C))

/-- Class restriction is dominated by the full measure. -/
lemma rowProcessLaw_restrictClass_le (P : Measure (ℕ → Fin k)) (i : Fin k) :
    rowProcessLaw_restrictClass (k := k) C P i ≤ rowProcessLaw (k := k) P i := by
  simp only [rowProcessLaw_restrictClass, rowProcessLaw]
  have hle : P.restrict {ω | ω 0 ∈ C} ≤ P := Measure.restrict_le_self
  have hmeas : AEMeasurable (rowSuccessorVisitProcess (k := k) i) P :=
    (measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable
  exact Measure.map_mono_of_aemeasurable hle hmeas

/-- If a state `a` is in class C, then restricting to {ω₀ = a} is finer than {ω₀ ∈ C}. -/
lemma restrict_singleton_le_restrict_class (P : Measure (ℕ → Fin k)) (a : Fin k) (ha : a ∈ C) :
    P.restrict {ω : ℕ → Fin k | ω 0 = a} ≤ P.restrict {ω : ℕ → Fin k | ω 0 ∈ C} := by
  have hsub : {ω : ℕ → Fin k | ω 0 = a} ⊆ {ω : ℕ → Fin k | ω 0 ∈ C} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω]; exact ha
  exact Measure.restrict_mono hsub le_rfl

/-- The class-restricted row process law decomposes as a finite sum of the
singleton-start restricted row process laws inside the class. -/
lemma rowProcessLaw_restrictClass_eq_finsetSum
    (P : Measure (ℕ → Fin k)) (i : Fin k) :
    rowProcessLaw_restrictClass (k := k) C P i
      =
    (by
      classical
      exact
        ∑ a : Fin k,
          if a ∈ C then
            rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i
          else 0) := by
  classical
  let S : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 ∈ C}
  let s : Fin k → Set (ℕ → Fin k) := fun a => {ω : ℕ → Fin k | ω 0 = a} ∩ S
  have hs_meas : ∀ a : Fin k, MeasurableSet (s a) := by
    intro a
    exact ((measurable_pi_apply 0) (measurableSet_singleton a)).inter
      (measurableSet_start_mem_class (k := k) (C := C))
  have hs_disj : Pairwise (fun a b : Fin k => Disjoint (s a) (s b)) := by
    intro a b hab
    rw [Set.disjoint_iff]
    intro ω hω
    exact hab (hω.1.1.symm.trans hω.2.1)
  have hs_union : (⋃ a : Fin k, s a) = S := by
    ext ω
    simp only [s, S, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hω
      exact hω.choose_spec.2
    · intro hω
      exact ⟨ω 0, by simp [hω]⟩
  have hsum :
      P.restrict S = Measure.sum (fun a : Fin k => P.restrict (s a)) := by
    calc
      P.restrict S = P.restrict (⋃ a : Fin k, s a) := by simp [hs_union]
      _ = Measure.sum (fun a : Fin k => P.restrict (s a)) := by
            simpa using
              (Measure.restrict_iUnion (μ := P) hs_disj hs_meas)
  calc
    rowProcessLaw_restrictClass (k := k) C P i
        = Measure.map (rowSuccessorVisitProcess (k := k) i) (P.restrict S) := rfl
    _ = Measure.map (rowSuccessorVisitProcess (k := k) i)
          (Measure.sum (fun a : Fin k => P.restrict (s a))) := by
            simpa using congrArg
              (Measure.map (rowSuccessorVisitProcess (k := k) i)) hsum
    _ = Measure.sum
          (fun a : Fin k =>
            Measure.map (rowSuccessorVisitProcess (k := k) i) (P.restrict (s a))) := by
              rw [MeasureTheory.Measure.map_sum
                ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)]
    _ = ∑ a : Fin k,
          if a ∈ C then
            rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i
          else 0 := by
            rw [Measure.sum_fintype]
            refine Finset.sum_congr rfl ?_
            intro a ha
            by_cases hCa : a ∈ C
            · have hs_eq : s a = {ω : ℕ → Fin k | ω 0 = a} := by
                ext ω
                constructor
                · intro hω
                  exact hω.1
                · intro hω
                  refine ⟨hω, ?_⟩
                  change ω 0 ∈ C
                  rw [hω]
                  exact hCa
              simp [rowProcessLaw, hs_eq, hCa]
            · have hs_eq : s a = ∅ := by
                ext ω
                constructor
                · intro hω
                  have hωC : ω 0 ∈ C := hω.2
                  rw [hω.1] at hωC
                  exact (hCa hωC).elim
                · intro hω
                  exact False.elim hω
              simp [hs_eq, hCa]

end ClassRowProcess

end MarkovDeFinettiHard
end Mettapedia.Logic
