/-
Copyright-free formalization module of Mettapedia.

# Joint successor-array partial exchangeability via the word ↔ array dictionary

Joint successor-array partial exchangeability via the word ↔ array dictionary,
following Fortini, Ladelli, Petris, Regazzini, "On mixtures of distributions of
Markov chains", Stochastic Process. Appl. 100 (2002) 147-165, Theorem 1 ('if'
direction). This file welds the combinatorial dictionary
(`MarkovDeFinettiSuccessorDictionary`) to the prefix-carrier measure engine
(`MarkovDeFinettiPEBridge`).

This section provides the tuple ↔ list bridge: the dictionary speaks
`List (Fin k)` words, while the measure engine speaks `Fin (N + 1) → Fin k`
tuples and `MarkovExchangeability.evidenceOf` (initial state + transition
counts). The bridge identifies the two transition-count notions and
characterizes evidence equality by head + list transition counts.
-/

import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorDictionary
import Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiPEBridge

namespace Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorArrayPE

open MarkovExchangeability
open MarkovDeFinettiSuccessorDictionary

variable {k : ℕ}

/-! ## Tuple ↔ list transition-count bridge -/

/-- Appending one symbol adds one transition out of the previous last symbol —
the list-side mirror of `MarkovExchangeability.transCount_snoc`. -/
theorem transCountL_append_singleton (l : List (Fin k)) (y a b : Fin k) :
    transCountL (l ++ [y]) a b
      = transCountL l a b + (if l.getLast? = some a ∧ y = b then 1 else 0) := by
  induction l with
  | nil => simp [transCountL]
  | cons x t ih =>
      cases t with
      | nil => simp [transCountL]
      | cons z t' =>
          simp only [List.cons_append] at ih ⊢
          rw [transCountL, ih, transCountL]
          simp only [List.getLast?_cons_cons]
          omega

/-- The Fin-tuple transition count is the list transition count of the
tuple's word. -/
theorem transCount_eq_transCountL {n : ℕ} (xs : Fin (n + 1) → Fin k) (a b : Fin k) :
    transCount xs a b = transCountL (List.ofFn xs) a b := by
  induction n with
  | zero =>
      simp [transCount, List.ofFn_succ, List.ofFn_zero, transCountL]
  | succ n ih =>
      rw [← Fin.snoc_init_self xs]
      rw [transCount_snoc]
      have hofn : List.ofFn (Fin.snoc (Fin.init xs) (xs (Fin.last (n + 1))))
          = List.ofFn (Fin.init xs) ++ [xs (Fin.last (n + 1))] := by
        rw [List.ofFn_succ']
        simp [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hofn, transCountL_append_singleton, ih (Fin.init xs)]
      have hlast : (List.ofFn (Fin.init xs)).getLast? = some (Fin.init xs (Fin.last n)) := by
        rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]
      rw [hlast]
      simp

/-! ## Evidence equality through list transition counts -/

/-- Markov-evidence equality is exactly: same start symbol plus equal LIST
transition counts of the tuples' words. -/
theorem evidenceOf_eq_iff {n : ℕ} (xs ys : Fin (n + 1) → Fin k) :
    evidenceOf xs = evidenceOf ys
      ↔ (xs 0 = ys 0 ∧ ∀ a b,
          transCountL (List.ofFn xs) a b = transCountL (List.ofFn ys) a b) := by
  rw [MarkovEvidence.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, fun a b => ?_⟩
    have h := congrFun (congrFun h2 a) b
    simpa [transCount_eq_transCountL] using h
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, ?_⟩
    funext a b
    simp only [evidenceOf_trans]
    rw [transCount_eq_transCountL, transCount_eq_transCountL]
    exact h2 a b

/-- Downstream form: equal head plus equal list transition counts give equal
Markov evidence. -/
theorem evidenceOf_eq_of_head_transCountL {n : ℕ} (xs ys : Fin (n + 1) → Fin k)
    (hhead : xs 0 = ys 0)
    (htc : ∀ a b, transCountL (List.ofFn xs) a b = transCountL (List.ofFn ys) a b) :
    evidenceOf xs = evidenceOf ys :=
  (evidenceOf_eq_iff xs ys).mpr ⟨hhead, htc⟩

/-! ## Word ↔ tuple sanity

`List.length_ofFn` already gives `(List.ofFn xs).length = n + 1`, and the
round-trip List → tuple is `List.ofFn_get` / `List.ofFn_getElem`. Note for the
downstream weld: the keystone `decode_lastFixed_length` guarantees a decoded
word has the ORIGINAL length, so it re-tuples at the same `Fin (n + 1)`. -/

/-- The head of a tuple's word is the tuple's first entry. -/
theorem head_ofFn_zero {n : ℕ} (xs : Fin (n + 1) → Fin k) :
    (List.ofFn xs).head (by simp) = xs 0 := by
  simp only [List.ofFn_succ, List.head_cons]

/-- Canary: tuple transition count = list transition count on FLPR's
Example 1 word `w₀`. -/
example : transCount (n := 10)
      (fun i : Fin 11 => ExampleOne.w₀.get (Fin.cast (by decide) i))
      (0 : Fin 2) (1 : Fin 2)
    = transCountL ExampleOne.w₀ 0 1 := by decide

/-! ## Visit-time bridge: dictionary rows = tree readings on the in-word range

The measure engine reads successor arrays through
`MarkovDeFinettiHard.rowSuccessorAtNthVisit` (visit times along an infinite
path); the dictionary reads them as `rowSuccessors i w` (lists). On the
in-word range of a prefix-extended tuple the two agree: the `n`-th entry of
the dictionary row is read at the `n`-th visit time, which occurs before `N`.
The path-side work is done by
`MarkovDeFinettiHard.nthVisitTime_eq_some_of_wordPrefix` and `wordVisitIndex`;
the glue below locates the `n`-th row entry at the `n`-th occurrence position
of the word. -/

open MarkovDeFinettiHard

/-- The `n`-th entry of `rowSuccessors i w` is read at a position `t`: the
`n`-th occurrence of `i` in `w` (with a successor), whose successor is that
entry. The occurrence count is phrased as `Nat.count` to match
`wordVisitIndex`. -/
theorem exists_getD_pos_of_lt_rowSuccessors_length (i d : Fin k) (w : List (Fin k)) :
    ∀ n : ℕ, ∀ hn : n < (rowSuccessors i w).length,
      ∃ t : ℕ, t + 1 < w.length ∧ w.getD t d = i ∧
        Nat.count (fun m => w.getD m d = i) t = n ∧
        (rowSuccessors i w)[n] = w.getD (t + 1) d := by
  induction w with
  | nil =>
      intro n hn
      simp at hn
  | cons a rest ih =>
      cases rest with
      | nil =>
          intro n hn
          simp at hn
      | cons b t' =>
          intro n hn
          by_cases hai : a = i
          · have hrow : rowSuccessors i (a :: b :: t') = b :: rowSuccessors i (b :: t') := by
              rw [rowSuccessors_cons_cons, if_pos hai]
            cases n with
            | zero =>
                refine ⟨0, ?_, ?_, ?_, ?_⟩
                · exact Nat.succ_lt_succ (Nat.succ_pos _)
                · exact hai
                · exact Nat.count_zero _
                · simp [hrow]
            | succ n' =>
                have hn' : n' < (rowSuccessors i (b :: t')).length := by
                  rw [hrow] at hn
                  simp only [List.length_cons] at hn
                  omega
                obtain ⟨t, ht1, ht2, ht3, ht4⟩ := ih n' hn'
                refine ⟨t + 1, ?_, ?_, ?_, ?_⟩
                · exact Nat.succ_lt_succ ht1
                · exact ht2
                · rw [Nat.count_succ']
                  show Nat.count (fun m => (b :: t').getD m d = i) t
                      + (if a = i then 1 else 0) = n' + 1
                  rw [if_pos hai]
                  omega
                · simp only [hrow, List.getElem_cons_succ]
                  exact ht4
          · have hrow : rowSuccessors i (a :: b :: t') = rowSuccessors i (b :: t') := by
              rw [rowSuccessors_cons_cons, if_neg hai]
            have hn' : n < (rowSuccessors i (b :: t')).length := by
              rw [hrow] at hn
              exact hn
            obtain ⟨t, ht1, ht2, ht3, ht4⟩ := ih n hn'
            refine ⟨t + 1, ?_, ?_, ?_, ?_⟩
            · exact Nat.succ_lt_succ ht1
            · exact ht2
            · rw [Nat.count_succ']
              show Nat.count (fun m => (b :: t').getD m d = i) t
                  + (if a = i then 1 else 0) = n
              rw [if_neg hai]
              omega
            · simp only [hrow]
              exact ht4

/-- **In-word visits.** The `n`-th visit-with-successor to row `i` along the
prefix-extended path happens at a time `t < N`, and the successor read there
is exactly the dictionary row's `n`-th entry. -/
theorem nthVisitTime_prefixExtend_of_lt_rowLength {N : ℕ} (xs : Fin (N + 1) → Fin k)
    (i : Fin k) (n : ℕ) (hn : n < (rowSuccessors i (List.ofFn xs)).length) :
    ∃ t : ℕ, t < N ∧
      nthVisitTime (prefixExtend N xs) i n = some t ∧
      successorAt (prefixExtend N xs) t = (rowSuccessors i (List.ofFn xs))[n] := by
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ :=
    exists_getD_pos_of_lt_rowSuccessors_length i (xs 0) (List.ofFn xs) n hn
  have hlen : (List.ofFn xs).length = N + 1 := List.length_ofFn
  have htN : t < N := by omega
  have hprefix : ∀ m ≤ t, prefixExtend N xs m = (List.ofFn xs).getD m (xs 0) := by
    intro m hm
    have hmN : m ≤ N := by omega
    have hmlen : m < (List.ofFn xs).length := by omega
    simp only [prefixExtend]
    rw [dif_pos hmN, List.getD_eq_getElem (l := List.ofFn xs) (d := xs 0) hmlen,
      List.getElem_ofFn]
  have hwvi : wordVisitIndex (List.ofFn xs) (xs 0) t = n := by
    have hcongr := congrArg
      (fun z => Nat.count (fun m => (List.ofFn xs).getD m (xs 0) = z) t) ht2
    exact hcongr.trans ht3
  have hNth : nthVisitTime (prefixExtend N xs) i n = some t := by
    have h := nthVisitTime_eq_some_of_wordPrefix (k := k) (List.ofFn xs)
      (prefixExtend N xs) (xs 0) hprefix
    rw [ht2, hwvi] at h
    exact h
  have hsucc : successorAt (prefixExtend N xs) t
      = (rowSuccessors i (List.ofFn xs))[n] := by
    rw [ht4]
    have ht1N : t + 1 ≤ N := by omega
    have ht1len : t + 1 < (List.ofFn xs).length := by omega
    simp only [successorAt, prefixExtend]
    rw [dif_pos ht1N, List.getD_eq_getElem (l := List.ofFn xs) (d := xs 0) ht1len,
      List.getElem_ofFn]
  exact ⟨t, htN, hNth, hsucc⟩

/-- The tree's visit-indexed reading agrees with the dictionary row on the
in-word range. -/
theorem rowSuccessorAtNthVisit_prefixExtend_eq_get {N : ℕ} (xs : Fin (N + 1) → Fin k)
    (i : Fin k) (n : ℕ) (hn : n < (rowSuccessors i (List.ofFn xs)).length) :
    rowSuccessorAtNthVisit i n (prefixExtend N xs)
      = (rowSuccessors i (List.ofFn xs))[n] := by
  obtain ⟨t, _, hNth, hsucc⟩ := nthVisitTime_prefixExtend_of_lt_rowLength xs i n hn
  rw [rowSuccessorAtNthVisit, hNth]
  exact hsucc

/-- Occurrence count of a tuple's word as a `Finset` card (helper for the
visit-count form). -/
theorem count_ofFn_eq_card_filter {m : ℕ} (g : Fin m → Fin k) (a : Fin k) :
    (List.ofFn g).count a = (Finset.univ.filter (fun j => g j = a)).card := by
  induction m with
  | zero => simp [List.ofFn_zero]
  | succ m ih =>
      rw [List.ofFn_succ, List.count_cons, ih (fun j => g j.succ),
        Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      by_cases hg : g 0 = a
      · simp [hg, Nat.add_comm]
      · simp [hg]

/-- The dictionary row length counts the in-word visits-with-successor:
occurrences of `i` among the first `N` coordinates. -/
theorem rowSuccessors_length_eq_visit_count {N : ℕ} (xs : Fin (N + 1) → Fin k) (i : Fin k) :
    (rowSuccessors i (List.ofFn xs)).length
      = (Finset.univ.filter (fun t : Fin N => xs t.castSucc = i)).card := by
  rw [rowSuccessors_length_eq_count_dropLast]
  have hdrop : (List.ofFn xs).dropLast = List.ofFn (fun t : Fin N => xs t.castSucc) := by
    rw [List.ofFn_succ' xs, List.concat_eq_append, List.dropLast_concat]
  rw [hdrop, count_ofFn_eq_card_filter]

/-- Canary (proved, since `nthVisitTime` is noncomputable): on the `w₀` tuple,
the tree reads the third successor of row 0 as `1` — matching the dictionary
row `[0, 1, 1, 0, 1, 1]` at index 2. -/
example :
    rowSuccessorAtNthVisit (0 : Fin 2) 2
      (prefixExtend 10 (fun i : Fin 11 => ExampleOne.w₀.get (Fin.cast (by decide) i)))
      = 1 := by
  have h := rowSuccessorAtNthVisit_prefixExtend_eq_get
    (fun i : Fin 11 => ExampleOne.w₀.get (Fin.cast (by decide) i)) (0 : Fin 2) 2
    (by decide)
  exact h.trans (by decide)

/-! ## Joint (multi-row) truncated events, prefix carrier, and the joint engine

The joint successor-array event constrains ALL rows at once: an intersection
of per-row truncated events. Its prefix carrier, disjoint-cylinder
decomposition, and start-restricted measure formula mirror the single-row
development; the joint measure engine is then a thin wrapper around the fully
generic evidence-preserving-equivalence sum lemma. -/

open MarkovDeFinettiRecurrence
open MeasureTheory
open Mettapedia.UniversalAI.UniversalPrediction
open Mettapedia.UniversalAI.UniversalPrediction.MarkovExchangeabilityBridge

/-- Joint truncated row-visit cylinder event: every row `i` satisfies its
window `W i` of visit-indexed successor constraints `v i`, witnessed before
`N`. Rows with `W i = ∅` contribute a vacuous constraint. -/
def jointRowVisitCylinderEventUpTo (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k)
    (N : ℕ) : Set (ℕ → Fin k) :=
  ⋂ i, rowVisitCylinderEventUpTo (k := k) i (W i) (v i) N

/-- Joint membership only depends on the first `N + 1` coordinates. -/
theorem jointRowVisitCylinderEventUpTo_mem_iff_of_prefixEq (ω ω' : ℕ → Fin k)
    (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) (N : ℕ)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    ω ∈ jointRowVisitCylinderEventUpTo W v N ↔
      ω' ∈ jointRowVisitCylinderEventUpTo W v N := by
  simp only [jointRowVisitCylinderEventUpTo, Set.mem_iInter]
  exact forall_congr' fun i =>
    rowVisitCylinderEventUpTo_mem_iff_of_prefixEq (k := k) ω ω' i (W i) (v i) N hprefix

/-- Prefix trajectories whose `prefixExtend` satisfies the joint event. -/
noncomputable def jointPrefixCarrier (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k)
    (N : ℕ) : Finset (Fin (N + 1) → Fin k) := by
  classical
  exact (Finset.univ : Finset (Fin (N + 1) → Fin k)).filter
    (fun xs => jointRowVisitCylinderEventUpTo W v N (prefixExtend (k := k) N xs))

lemma jointRowVisitCylinderEventUpTo_eq_iUnion_cylinder
    (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) (N : ℕ) :
    jointRowVisitCylinderEventUpTo W v N =
      ⋃ xs ∈ jointPrefixCarrier W v N, cylinder (k := k) (List.ofFn xs) := by
  classical
  ext ω
  constructor
  · intro hω
    let xsω : Fin (N + 1) → Fin k := fun j => ω j
    have hcarrier : xsω ∈ jointPrefixCarrier W v N := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ xsω, ?_⟩
      have hprefix : ∀ m ≤ N, ω m = prefixExtend (k := k) N xsω m := by
        intro m hm
        simp [prefixExtend, hm, xsω]
      exact (jointRowVisitCylinderEventUpTo_mem_iff_of_prefixEq
        ω (prefixExtend (k := k) N xsω) W v N hprefix).1 hω
    refine Set.mem_iUnion.mpr ⟨xsω, Set.mem_iUnion.mpr ⟨hcarrier, ?_⟩⟩
    exact mem_cylinder_of_prefix (k := k) ω N
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨xs, hω⟩
    rcases Set.mem_iUnion.mp hω with ⟨hxs, hmem⟩
    have hxs' : jointRowVisitCylinderEventUpTo W v N (prefixExtend (k := k) N xs) := by
      simpa [jointPrefixCarrier] using (Finset.mem_filter.mp hxs).2
    have hprefix : ∀ m ≤ N, ω m = prefixExtend (k := k) N xs m :=
      eq_prefixExtend_of_mem_cylinder (k := k) ω N xs hmem
    exact (jointRowVisitCylinderEventUpTo_mem_iff_of_prefixEq
      ω (prefixExtend (k := k) N xs) W v N hprefix).2 hxs'

lemma pairwiseDisjoint_cylinder_ofFn_on_jointPrefixCarrier
    (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) (N : ℕ) :
    ((↑(jointPrefixCarrier W v N) : Set (Fin (N + 1) → Fin k))).PairwiseDisjoint
      (fun xs => cylinder (k := k) (List.ofFn xs)) := by
  intro xs _ ys _ hne
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

lemma measurableSet_jointRowVisitCylinderEventUpTo
    (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) (N : ℕ) :
    MeasurableSet (jointRowVisitCylinderEventUpTo W v N) := by
  refine MeasurableSet.iInter ?_
  intro i
  exact measurableSet_rowVisitCylinderEventUpTo (k := k) i (W i) (v i) N

lemma measure_jointRowVisitCylinderEventUpTo_eq_sum_prefixCylinders
    (P : Measure (ℕ → Fin k)) (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k)
    (N : ℕ) :
    P (jointRowVisitCylinderEventUpTo W v N) =
      Finset.sum (jointPrefixCarrier W v N)
        (fun xs => P (cylinder (k := k) (List.ofFn xs))) := by
  rw [jointRowVisitCylinderEventUpTo_eq_iUnion_cylinder W v N]
  exact measure_biUnion_finset
    (μ := P)
    (s := jointPrefixCarrier W v N)
    (f := fun xs => cylinder (k := k) (List.ofFn xs))
    (pairwiseDisjoint_cylinder_ofFn_on_jointPrefixCarrier W v N)
    (fun xs _ => MarkovDeFinettiHard.measurableSet_cylinder (k := k) (List.ofFn xs))

lemma measure_start_inter_joint_eq_sum_prefixCylinders
    (P : Measure (ℕ → Fin k)) (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k)
    (N : ℕ) (j : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpTo W v N) =
      Finset.sum (jointPrefixCarrier W v N)
        (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
  classical
  let S0 : Set (ℕ → Fin k) := {ω : ℕ → Fin k | ω 0 = j}
  have hS0meas : MeasurableSet S0 := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({j} : Set (Fin k)))
    exact (measurable_pi_apply 0) (MeasurableSet.singleton j)
  have hleft :
      P (S0 ∩ jointRowVisitCylinderEventUpTo W v N) =
        (P.restrict S0) (jointRowVisitCylinderEventUpTo W v N) := by
    have h :=
      Measure.restrict_apply (μ := P) (s := S0)
        (t := jointRowVisitCylinderEventUpTo W v N)
        (measurableSet_jointRowVisitCylinderEventUpTo W v N)
    simpa [Set.inter_comm] using h.symm
  have hsum :=
    measure_jointRowVisitCylinderEventUpTo_eq_sum_prefixCylinders
      (P := P.restrict S0) W v N
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
      have hmeas := MarkovDeFinettiHard.measurableSet_cylinder (k := k) (List.ofFn xs)
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
      have hmeas := MarkovDeFinettiHard.measurableSet_cylinder (k := k) (List.ofFn xs)
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
    P (S0 ∩ jointRowVisitCylinderEventUpTo W v N)
        = (P.restrict S0) (jointRowVisitCylinderEventUpTo W v N) := hleft
    _ = Finset.sum (jointPrefixCarrier W v N)
          (fun xs => (P.restrict S0) (cylinder (k := k) (List.ofFn xs))) := by
          simpa using hsum
    _ = Finset.sum (jointPrefixCarrier W v N)
          (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro xs _
          exact hterm xs

/-- **The joint measure engine.** An evidence-preserving equivalence of joint
prefix carriers transports the start-restricted measure of one joint
successor-array event to the other. -/
lemma measure_start_inter_joint_eq_of_evidencePreservingEquiv_start
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (W₁ : Fin k → Finset ℕ) (v₁ : Fin k → ℕ → Fin k)
    (W₂ : Fin k → Finset ℕ) (v₂ : Fin k → ℕ → Fin k)
    (N : ℕ) (j : Fin k)
    (e : jointPrefixCarrier W₁ v₁ N ≃ jointPrefixCarrier W₂ v₂ N)
    (he : ∀ xs : jointPrefixCarrier W₁ v₁ N,
        evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpTo W₁ v₁ N) =
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpTo W₂ v₂ N) := by
  have hleft :
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpTo W₁ v₁ N) =
        Finset.sum (jointPrefixCarrier W₁ v₁ N)
          (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) :=
    measure_start_inter_joint_eq_sum_prefixCylinders P W₁ v₁ N j
  have hright :
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpTo W₂ v₂ N) =
        Finset.sum (jointPrefixCarrier W₂ v₂ N)
          (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) :=
    measure_start_inter_joint_eq_sum_prefixCylinders P W₂ v₂ N j
  have hsum :
      Finset.sum (jointPrefixCarrier W₁ v₁ N)
          (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) =
        Finset.sum (jointPrefixCarrier W₂ v₂ N)
          (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) :=
    sum_cylinderProb_eq_of_extension_and_evidencePreservingEquiv_start
      (k := k) μ hμ P hExt
      (jointPrefixCarrier W₁ v₁ N) (jointPrefixCarrier W₂ v₂ N) e he j
  calc
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpTo W₁ v₁ N)
        = Finset.sum (jointPrefixCarrier W₁ v₁ N)
            (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) :=
          hleft
    _ = Finset.sum (jointPrefixCarrier W₂ v₂ N)
          (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) := hsum
    _ = P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpTo W₂ v₂ N) :=
          hright.symm

/-- Canary: the joint event with all-empty windows is vacuous (everything). -/
example : jointRowVisitCylinderEventUpTo (k := 2) (fun _ => (∅ : Finset ℕ))
    (fun _ _ => (0 : Fin 2)) 5 = Set.univ := by
  ext ω
  simp [jointRowVisitCylinderEventUpTo, rowVisitCylinderEventUpTo]

/-! ## The joint carrier equivalence from row-wise last-fixing permutations

Rows of a carrier element are long enough to host their windows
(`lt_rowLength_of_visit_witness`), their constrained cells read the required
values (`carrier_cell_eq`), and the decode-based map `jointCarrierMapFun`
permutes each row by `(σ i).symm`, preserving evidence (keystone) and carrier
membership. Round-trips come from `permuteList_symm_cancel` + `decode_encode`.

No executable canary here: `jointPrefixCarrier` membership goes through the
noncomputable `nthVisitTime`, so `decide` cannot evaluate it; the ExampleOne
keystone canaries in the dictionary already witness the map's list-level core. -/

/-- A witnessed `n`-th visit before `N` forces the dictionary row to have
more than `n` entries. -/
theorem lt_rowLength_of_visit_witness {N : ℕ} (xs : Fin (N + 1) → Fin k) (i : Fin k)
    (n t : ℕ) (htN : t < N)
    (hsome : nthVisitTime (prefixExtend N xs) i n = some t) :
    n < (rowSuccessors i (List.ofFn xs)).length := by
  have hvisit : prefixExtend (k := k) N xs t = i ∧
      visitCountBefore (k := k) (prefixExtend N xs) i t = n :=
    (nthVisitTime_eq_some_iff (k := k) (prefixExtend N xs) i n t).1 hsome
  obtain ⟨hvis, hcount⟩ := hvisit
  have hstep : visitCountBefore (k := k) (prefixExtend N xs) i (t + 1) = n + 1 := by
    rw [visitCountBefore, Finset.sum_range_succ, ← visitCountBefore, hcount,
      if_pos hvis]
  have hmono : visitCountBefore (k := k) (prefixExtend N xs) i (t + 1)
      ≤ visitCountBefore (k := k) (prefixExtend N xs) i N := by
    rw [visitCountBefore, visitCountBefore]
    have hsub : Finset.range (t + 1) ⊆ Finset.range N :=
      Finset.range_subset_range.mpr (by omega)
    exact Finset.sum_le_sum_of_subset hsub
  have hcard : visitCountBefore (k := k) (prefixExtend N xs) i N
      = (Finset.univ.filter (fun s : Fin N => xs s.castSucc = i)).card := by
    rw [visitCountBefore, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro u _
    have hpe : prefixExtend (k := k) N xs u.1 = xs u.castSucc := by
      simp only [prefixExtend]
      rw [dif_pos (Nat.le_of_lt u.2)]
      rfl
    rw [hpe]
  rw [rowSuccessors_length_eq_visit_count]
  omega

/-- Carrier membership, unfolded to per-row witnessed constraints. -/
theorem mem_jointPrefixCarrier_iff {W : Fin k → Finset ℕ} {v' : Fin k → ℕ → Fin k}
    {N : ℕ} {xs : Fin (N + 1) → Fin k} :
    xs ∈ jointPrefixCarrier W v' N ↔
      ∀ i, ∀ n ∈ W i, ∃ t : ℕ, t < N ∧
        nthVisitTime (prefixExtend N xs) i n = some t ∧
        successorAt (prefixExtend N xs) t = v' i n := by
  classical
  constructor
  · intro h
    have hmem : jointRowVisitCylinderEventUpTo W v' N (prefixExtend (k := k) N xs) := by
      simpa [jointPrefixCarrier] using (Finset.mem_filter.mp h).2
    intro i
    exact Set.mem_iInter.mp hmem i
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    refine Set.mem_iInter.mpr ?_
    intro i
    exact h i

/-- Every windowed index is inside the dictionary row of a carrier element. -/
theorem rowLength_ge_window {W : Fin k → Finset ℕ} {v' : Fin k → ℕ → Fin k} {N : ℕ}
    {xs : Fin (N + 1) → Fin k} (hxs : xs ∈ jointPrefixCarrier W v' N)
    (i : Fin k) {n : ℕ} (hn : n ∈ W i) :
    n < (rowSuccessors i (List.ofFn xs)).length := by
  obtain ⟨t, htN, hsome, _⟩ := (mem_jointPrefixCarrier_iff.mp hxs) i n hn
  exact lt_rowLength_of_visit_witness xs i n t htN hsome

/-- With `Finset.range`-windows: the row is at least window-sized. -/
theorem window_le_rowLength {N : ℕ} {m : Fin k → ℕ} {v' : Fin k → ℕ → Fin k}
    {xs : Fin (N + 1) → Fin k}
    (hxs : xs ∈ jointPrefixCarrier (fun i => Finset.range (m i)) v' N) (i : Fin k) :
    m i ≤ (rowSuccessors i (List.ofFn xs)).length := by
  rcases Nat.eq_zero_or_pos (m i) with h0 | hpos
  · omega
  · have h := rowLength_ge_window hxs i
      (Finset.mem_range.mpr (by omega : m i - 1 < m i))
    omega

/-- A constrained cell of a carrier element reads the required value. -/
theorem carrier_cell_eq [NeZero k] {W : Fin k → Finset ℕ} {v' : Fin k → ℕ → Fin k}
    {N : ℕ} {xs : Fin (N + 1) → Fin k} (hxs : xs ∈ jointPrefixCarrier W v' N)
    (i : Fin k) {n : ℕ} (hnW : n ∈ W i)
    (hn : n < (rowSuccessors i (List.ofFn xs)).length) :
    (rowSuccessors i (List.ofFn xs))[n] = v' i n := by
  obtain ⟨t, htN, hsome, hsucc⟩ := (mem_jointPrefixCarrier_iff.mp hxs) i n hnW
  obtain ⟨t2, ht2N, hsome2, hsucc2⟩ :=
    nthVisitTime_prefixExtend_of_lt_rowLength xs i n hn
  have ht : t2 = t := Option.some.inj (hsome2.symm.trans hsome)
  subst ht
  rw [← hsucc2]
  exact hsucc

/-- The carrier map: decode from the same start, with each row permuted by
`(σ i).symm` (positionally, junk-guarded). Out-of-range coordinates default
to the start symbol; the keystone length theorem shows the guard never fires
on carrier elements. -/
noncomputable def jointCarrierMapFun [NeZero k] (σ : Fin k → Equiv.Perm ℕ) {N : ℕ}
    (xs : Fin (N + 1) → Fin k) : Fin (N + 1) → Fin k :=
  fun t => (decode (xs 0)
    (fun i => permuteList (σ i).symm (rowSuccessors i (List.ofFn xs)))).getD t.1 (xs 0)

theorem jointCarrierMapFun_head [NeZero k] (σ : Fin k → Equiv.Perm ℕ) {N : ℕ}
    (xs : Fin (N + 1) → Fin k) : jointCarrierMapFun σ xs 0 = xs 0 := by
  simp only [jointCarrierMapFun, Fin.val_zero, decode, List.getD_cons_zero]

/-- Support, permutation, and last-fixing package for the rows of a carrier
element under `(σ i).symm`. -/
theorem rowPermLast_of_carrier {N : ℕ} {m : Fin k → ℕ}
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    {v' : Fin k → ℕ → Fin k} {xs : Fin (N + 1) → Fin k}
    (hxs : xs ∈ jointPrefixCarrier (fun i => Finset.range (m i)) v' N) :
    (∀ i n, (rowSuccessors i (List.ofFn xs)).length ≤ n → (σ i).symm n = n)
    ∧ (∀ i, (permuteList (σ i).symm (rowSuccessors i (List.ofFn xs))).Perm
        (rowSuccessors i (xs 0 :: List.ofFn (fun t : Fin N => xs t.succ))))
    ∧ (∀ i, (permuteList (σ i).symm (rowSuccessors i (List.ofFn xs))).getLast?
        = (rowSuccessors i (xs 0 :: List.ofFn (fun t : Fin N => xs t.succ))).getLast?) := by
  have hsupp : ∀ i n, (rowSuccessors i (List.ofFn xs)).length ≤ n → (σ i).symm n = n := by
    intro i n hn
    have hml := window_le_rowLength hxs i
    exact perm_symm_support (σ i) (hσ i) n (by omega)
  refine ⟨hsupp, fun i => ?_, fun i => ?_⟩
  · rw [← List.ofFn_succ]
    exact permuteList_perm (σ i).symm _ (hsupp i)
  · rw [← List.ofFn_succ]
    refine permuteList_getLast? (σ i).symm _ (hsupp i) ?_
    have hml := window_le_rowLength hxs i
    exact perm_symm_support (σ i) (hσ i) _ (by omega)

/-- The word of the mapped tuple is the decoded word (the keystone gives it
full length `N + 1`, so the `getD` guard never fires). -/
theorem ofFn_jointCarrierMapFun [NeZero k] {N : ℕ} {m : Fin k → ℕ}
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    {v' : Fin k → ℕ → Fin k} {xs : Fin (N + 1) → Fin k}
    (hxs : xs ∈ jointPrefixCarrier (fun i => Finset.range (m i)) v' N) :
    List.ofFn (jointCarrierMapFun σ xs)
      = decode (xs 0)
          (fun i => permuteList (σ i).symm (rowSuccessors i (List.ofFn xs))) := by
  obtain ⟨hsupp, hperm, hlast⟩ := rowPermLast_of_carrier σ hσ hxs
  have hlen := decode_lastFixed_length (xs 0) (List.ofFn fun t : Fin N => xs t.succ)
    _ hperm hlast
  rw [← List.ofFn_succ] at hlen
  apply List.ext_getElem
  · rw [List.length_ofFn, hlen, List.length_ofFn]
  · intro t h₁ h₂
    rw [List.getElem_ofFn]
    simp only [jointCarrierMapFun]
    rw [List.getD_eq_getElem _ (xs 0) h₂]

/-- Rows of the mapped tuple are the `(σ i).symm`-permuted rows (keystone
full consumption). -/
theorem jointCarrierMapFun_rowSuccessors [NeZero k] {N : ℕ} {m : Fin k → ℕ}
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    {v' : Fin k → ℕ → Fin k} {xs : Fin (N + 1) → Fin k}
    (hxs : xs ∈ jointPrefixCarrier (fun i => Finset.range (m i)) v' N) (i : Fin k) :
    rowSuccessors i (List.ofFn (jointCarrierMapFun σ xs))
      = permuteList (σ i).symm (rowSuccessors i (List.ofFn xs)) := by
  obtain ⟨hsupp, hperm, hlast⟩ := rowPermLast_of_carrier σ hσ hxs
  rw [ofFn_jointCarrierMapFun σ hσ hxs]
  exact decode_lastFixed_rowSuccessors (xs 0)
    (List.ofFn fun t : Fin N => xs t.succ) _ hperm hlast i

/-- The carrier map lands in the plain-values carrier: cell `(i, n)` of the
image reads `(R xs i)[(σ i).symm n] = v i (σ i ((σ i).symm n)) = v i n`. -/
theorem jointCarrierMapFun_mem [NeZero k] {N : ℕ} {m : Fin k → ℕ}
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    {v : Fin k → ℕ → Fin k} {xs : Fin (N + 1) → Fin k}
    (hxs : xs ∈ jointPrefixCarrier (fun i => Finset.range (m i))
      (fun i n => v i (σ i n)) N) :
    jointCarrierMapFun σ xs ∈ jointPrefixCarrier (fun i => Finset.range (m i)) v N := by
  refine mem_jointPrefixCarrier_iff.mpr ?_
  intro i n hn
  have hnm : n < m i := Finset.mem_range.mp hn
  have hml := window_le_rowLength hxs i
  have hrows := jointCarrierMapFun_rowSuccessors σ hσ hxs i
  have hlen : n < (rowSuccessors i (List.ofFn (jointCarrierMapFun σ xs))).length := by
    rw [hrows, permuteList_length]
    omega
  obtain ⟨t, htN, hsome, hsucc⟩ :=
    nthVisitTime_prefixExtend_of_lt_rowLength (jointCarrierMapFun σ xs) i n hlen
  refine ⟨t, htN, hsome, ?_⟩
  rw [hsucc]
  have hsymm_lt : (σ i).symm n < m i := by
    have hsupp_mi : ∀ j, m i ≤ j → (σ i).symm j = j := fun j hj =>
      perm_symm_support (σ i) (hσ i) j (by omega)
    exact perm_lt_of_support_lt (σ i).symm hsupp_mi n hnm
  have hsupp_len : ∀ j, (rowSuccessors i (List.ofFn xs)).length ≤ j → (σ i).symm j = j :=
    fun j hj => perm_symm_support (σ i) (hσ i) j (by omega)
  have hcell : (rowSuccessors i (List.ofFn (jointCarrierMapFun σ xs)))[n]'hlen
      = (rowSuccessors i (List.ofFn xs))[(σ i).symm n]'(by omega) := by
    simp only [hrows]
    rw [permuteList_getElem (σ i).symm _ hsupp_len n (by omega)
      (by rw [permuteList_length]; omega)]
  rw [hcell]
  have hv := carrier_cell_eq hxs i (Finset.mem_range.mpr hsymm_lt)
    (by omega : (σ i).symm n < (rowSuccessors i (List.ofFn xs)).length)
  rw [hv, Equiv.apply_symm_apply]

/-- The carrier map preserves Markov evidence (same head; keystone transition
counts). -/
theorem evidenceOf_jointCarrierMapFun [NeZero k] {N : ℕ} {m : Fin k → ℕ}
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    {v' : Fin k → ℕ → Fin k} {xs : Fin (N + 1) → Fin k}
    (hxs : xs ∈ jointPrefixCarrier (fun i => Finset.range (m i)) v' N) :
    evidenceOf (n := N) xs = evidenceOf (n := N) (jointCarrierMapFun σ xs) := by
  obtain ⟨hsupp, hperm, hlast⟩ := rowPermLast_of_carrier σ hσ hxs
  refine evidenceOf_eq_of_head_transCountL _ _ (jointCarrierMapFun_head σ xs).symm ?_
  intro a b
  rw [ofFn_jointCarrierMapFun σ hσ hxs,
    decode_lastFixed_transCountL (xs 0) (List.ofFn fun t : Fin N => xs t.succ) _
      hperm hlast a b, List.ofFn_succ]

/-- Round-trip: mapping by `σ` then by `fun i => (σ i).symm` restores the
tuple (`permuteList_symm_cancel` + `decode_encode`). -/
theorem jointCarrierMapFun_leftInv [NeZero k] {N : ℕ} {m : Fin k → ℕ}
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    {v : Fin k → ℕ → Fin k} {xs : Fin (N + 1) → Fin k}
    (hxs : xs ∈ jointPrefixCarrier (fun i => Finset.range (m i))
      (fun i n => v i (σ i n)) N) :
    jointCarrierMapFun (fun i => (σ i).symm) (jointCarrierMapFun σ xs) = xs := by
  have hσ' : ∀ i n, m i - 2 ≤ n → (σ i).symm n = n := fun i n hn =>
    perm_symm_support (σ i) (hσ i) n hn
  have hys : jointCarrierMapFun σ xs
      ∈ jointPrefixCarrier (fun i => Finset.range (m i)) v N :=
    jointCarrierMapFun_mem σ hσ hxs
  obtain ⟨hsupp, _, _⟩ := rowPermLast_of_carrier σ hσ hxs
  have hofn2 : List.ofFn (jointCarrierMapFun (fun i => (σ i).symm)
      (jointCarrierMapFun σ xs)) = List.ofFn xs := by
    rw [ofFn_jointCarrierMapFun (fun i => (σ i).symm) hσ' hys]
    have hrows : (fun i => permuteList ((σ i).symm).symm
        (rowSuccessors i (List.ofFn (jointCarrierMapFun σ xs))))
        = fun i => rowSuccessors i (List.ofFn xs) := by
      funext i
      rw [jointCarrierMapFun_rowSuccessors σ hσ hxs i]
      exact permuteList_symm_cancel ((σ i).symm) _ (hsupp i)
    rw [hrows, jointCarrierMapFun_head σ xs]
    simp only [List.ofFn_succ]
    exact decode_encode (xs 0) _
  exact List.ofFn_injective hofn2

/-- Round-trip the other way. -/
theorem jointCarrierMapFun_rightInv [NeZero k] {N : ℕ} {m : Fin k → ℕ}
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    {v : Fin k → ℕ → Fin k} {ys : Fin (N + 1) → Fin k}
    (hys : ys ∈ jointPrefixCarrier (fun i => Finset.range (m i)) v N) :
    jointCarrierMapFun σ (jointCarrierMapFun (fun i => (σ i).symm) ys) = ys := by
  have hσ' : ∀ i n, m i - 2 ≤ n → (σ i).symm n = n := fun i n hn =>
    perm_symm_support (σ i) (hσ i) n hn
  have hvals : (fun i n => v i (σ i ((σ i).symm n))) = v := by
    funext i n
    rw [Equiv.apply_symm_apply]
  have hys' : ys ∈ jointPrefixCarrier (fun i => Finset.range (m i))
      (fun i n => v i (σ i ((σ i).symm n))) N := by
    rw [hvals]
    exact hys
  exact jointCarrierMapFun_leftInv (fun i => (σ i).symm) hσ'
    (v := fun i n => v i (σ i n)) hys'

/-- **The joint carrier equivalence.** Row-wise support-bounded permutations
(fixing everything from index `m i - 2` on) induce an evidence-preserving
bijection between the σ-composed-values carrier and the plain-values carrier. -/
theorem jointCarrier_equiv_of_rowPerms [NeZero k] (m : Fin k → ℕ)
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    (v : Fin k → ℕ → Fin k) (N : ℕ) :
    ∃ e : jointPrefixCarrier (k := k) (fun i => Finset.range (m i))
          (fun i n => v i (σ i n)) N
        ≃ jointPrefixCarrier (k := k) (fun i => Finset.range (m i)) v N,
      ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 := by
  have hσ' : ∀ i n, m i - 2 ≤ n → (σ i).symm n = n := fun i n hn =>
    perm_symm_support (σ i) (hσ i) n hn
  have hvals : (fun i n => v i (σ i ((σ i).symm n))) = v := by
    funext i n
    rw [Equiv.apply_symm_apply]
  refine ⟨⟨fun xs => ⟨jointCarrierMapFun σ xs.1, jointCarrierMapFun_mem σ hσ xs.2⟩,
    fun ys => ⟨jointCarrierMapFun (fun i => (σ i).symm) ys.1, ?_⟩, ?_, ?_⟩, ?_⟩
  · have hys' : ys.1 ∈ jointPrefixCarrier (fun i => Finset.range (m i))
        (fun i n => v i (σ i ((σ i).symm n))) N := by
      rw [hvals]
      exact ys.2
    exact jointCarrierMapFun_mem (fun i => (σ i).symm) hσ'
      (v := fun i n => v i (σ i n)) hys'
  · intro xs
    exact Subtype.ext (jointCarrierMapFun_leftInv σ hσ xs.2)
  · intro ys
    exact Subtype.ext (jointCarrierMapFun_rightInv σ hσ ys.2)
  · intro xs
    exact evidenceOf_jointCarrierMapFun σ hσ xs.2

/-! ## Avoidance-extended carriers and the per-N permutation workhorse

The V/NV profile partition leaves never-visited factors: the event
additionally requires the rows in a set `A` to be unvisited within the
prefix. Occurrence counts are evidence-determined, so the carrier
equivalence restricts to the avoidance-filtered carriers, and the whole
measure engine mirrors over. -/

/-- Every occurrence of `s`, except at position 0, is entered by exactly one
transition: `count = Σ_a transCount a s + [head = s]`. -/
theorem count_eq_sum_transCount_add_head [NeZero k] {N : ℕ}
    (xs : Fin (N + 1) → Fin k) (s : Fin k) :
    (List.ofFn xs).count s
      = (∑ a, transCount xs a s) + (if xs 0 = s then 1 else 0) := by
  have hsum : (∑ a, transCount xs a s) = (List.ofFn xs).tail.count s := by
    rw [Finset.sum_congr rfl (fun a _ => transCount_eq_transCountL xs a s)]
    rw [Finset.sum_congr rfl (fun a _ => transCountL_eq_count (List.ofFn xs) a s)]
    exact sum_rowSuccessors_count (List.ofFn xs) s
  have hcount := count_tail_add_ite (List.ofFn xs) (by simp) s
  rw [head_ofFn_zero xs] at hcount
  rw [hsum]
  omega

/-- Per-symbol occurrence counts are evidence-determined. -/
theorem occurrences_eq_of_evidenceOf_eq [NeZero k] {N : ℕ}
    (xs ys : Fin (N + 1) → Fin k)
    (h : evidenceOf (n := N) xs = evidenceOf (n := N) ys) (s : Fin k) :
    (List.ofFn xs).count s = (List.ofFn ys).count s := by
  obtain ⟨hhead, htc⟩ := (evidenceOf_eq_iff xs ys).mp h
  rw [count_eq_sum_transCount_add_head xs s, count_eq_sum_transCount_add_head ys s,
    hhead]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [transCount_eq_transCountL, transCount_eq_transCountL]
  exact htc a s

/-- The joint prefix carrier, additionally requiring the rows in `A` to be
unvisited in the prefix word. -/
noncomputable def jointPrefixCarrierAvoid (W : Fin k → Finset ℕ)
    (v : Fin k → ℕ → Fin k) (A : Finset (Fin k)) (N : ℕ) :
    Finset (Fin (N + 1) → Fin k) := by
  classical
  exact (jointPrefixCarrier W v N).filter
    (fun xs => ∀ i ∈ A, (List.ofFn xs).count i = 0)

theorem mem_jointPrefixCarrierAvoid_iff {W : Fin k → Finset ℕ}
    {v : Fin k → ℕ → Fin k} {A : Finset (Fin k)} {N : ℕ}
    {xs : Fin (N + 1) → Fin k} :
    xs ∈ jointPrefixCarrierAvoid W v A N ↔
      xs ∈ jointPrefixCarrier W v N ∧ ∀ i ∈ A, (List.ofFn xs).count i = 0 := by
  classical
  constructor
  · intro h
    exact ⟨Finset.mem_of_mem_filter xs h, (Finset.mem_filter.mp h).2⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨h.1, h.2⟩

/-- The avoidance-extended joint event: the joint truncated constraints plus
"no visit to any row in `A` up to time `N`". -/
def jointRowVisitCylinderEventUpToAvoid (W : Fin k → Finset ℕ)
    (v : Fin k → ℕ → Fin k) (A : Finset (Fin k)) (N : ℕ) : Set (ℕ → Fin k) :=
  jointRowVisitCylinderEventUpTo W v N ∩ {ω | ∀ i ∈ A, ∀ t ≤ N, ω t ≠ i}

/-- Avoidance-extended membership only depends on the first `N + 1`
coordinates. -/
theorem jointRowVisitCylinderEventUpToAvoid_mem_iff_of_prefixEq (ω ω' : ℕ → Fin k)
    (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) (A : Finset (Fin k)) (N : ℕ)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    ω ∈ jointRowVisitCylinderEventUpToAvoid W v A N ↔
      ω' ∈ jointRowVisitCylinderEventUpToAvoid W v A N := by
  simp only [jointRowVisitCylinderEventUpToAvoid, Set.mem_inter_iff]
  refine and_congr
    (jointRowVisitCylinderEventUpTo_mem_iff_of_prefixEq ω ω' W v N hprefix) ?_
  constructor
  · intro h i hi t ht
    rw [← hprefix t ht]
    exact h i hi t ht
  · intro h i hi t ht
    rw [hprefix t ht]
    exact h i hi t ht

/-- The prefix word avoids `i` iff the prefix-extended path avoids `i` up to
`N` (the extension's tail junk is out of range). -/
theorem count_ofFn_eq_zero_iff_prefixExtend_ne {N : ℕ} (xs : Fin (N + 1) → Fin k)
    (i : Fin k) :
    (List.ofFn xs).count i = 0 ↔
      ∀ t ≤ N, prefixExtend (k := k) N xs t ≠ i := by
  rw [List.count_eq_zero]
  constructor
  · intro h t ht hcon
    have hpe : prefixExtend (k := k) N xs t = xs ⟨t, Nat.lt_succ_of_le ht⟩ := by
      simp only [prefixExtend]
      rw [dif_pos ht]
    exact h (List.mem_ofFn.mpr ⟨⟨t, Nat.lt_succ_of_le ht⟩, by rw [← hpe]; exact hcon⟩)
  · intro h hmem
    rw [List.mem_ofFn] at hmem
    obtain ⟨j, hj⟩ := hmem
    have hje : prefixExtend (k := k) N xs j.1 = xs j := by
      simp only [prefixExtend]
      rw [dif_pos (Nat.le_of_lt_succ j.2)]
    exact h j.1 (Nat.le_of_lt_succ j.2) (by rw [hje]; exact hj)

lemma jointRowVisitCylinderEventUpToAvoid_eq_iUnion_cylinder
    (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) (A : Finset (Fin k)) (N : ℕ) :
    jointRowVisitCylinderEventUpToAvoid W v A N =
      ⋃ xs ∈ jointPrefixCarrierAvoid W v A N, cylinder (k := k) (List.ofFn xs) := by
  classical
  ext ω
  constructor
  · intro hω
    let xsω : Fin (N + 1) → Fin k := fun j => ω j
    have hprefix : ∀ m ≤ N, ω m = prefixExtend (k := k) N xsω m := by
      intro m hm
      simp [prefixExtend, hm, xsω]
    obtain ⟨hjoint, havoid⟩ :=
      (jointRowVisitCylinderEventUpToAvoid_mem_iff_of_prefixEq
        ω (prefixExtend (k := k) N xsω) W v A N hprefix).1 hω
    have hcarrier : xsω ∈ jointPrefixCarrierAvoid W v A N := by
      rw [mem_jointPrefixCarrierAvoid_iff]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ xsω, hjoint⟩, ?_⟩
      intro i hi
      exact (count_ofFn_eq_zero_iff_prefixExtend_ne xsω i).mpr (havoid i hi)
    refine Set.mem_iUnion.mpr ⟨xsω, Set.mem_iUnion.mpr ⟨hcarrier, ?_⟩⟩
    exact mem_cylinder_of_prefix (k := k) ω N
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨xs, hω⟩
    rcases Set.mem_iUnion.mp hω with ⟨hxs, hmem⟩
    obtain ⟨hxs1, hxs2⟩ := mem_jointPrefixCarrierAvoid_iff.mp hxs
    have hprefix : ∀ m ≤ N, ω m = prefixExtend (k := k) N xs m :=
      eq_prefixExtend_of_mem_cylinder (k := k) ω N xs hmem
    refine (jointRowVisitCylinderEventUpToAvoid_mem_iff_of_prefixEq
      ω (prefixExtend (k := k) N xs) W v A N hprefix).2 ⟨?_, ?_⟩
    · exact (Finset.mem_filter.mp hxs1).2
    · intro i hi
      exact (count_ofFn_eq_zero_iff_prefixExtend_ne xs i).mp (hxs2 i hi)

lemma pairwiseDisjoint_cylinder_ofFn_on_jointPrefixCarrierAvoid
    (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) (A : Finset (Fin k)) (N : ℕ) :
    ((↑(jointPrefixCarrierAvoid W v A N) : Set (Fin (N + 1) → Fin k))).PairwiseDisjoint
      (fun xs => cylinder (k := k) (List.ofFn xs)) := by
  classical
  refine (pairwiseDisjoint_cylinder_ofFn_on_jointPrefixCarrier W v N).subset ?_
  intro xs hxs
  simp only [Finset.mem_coe] at hxs ⊢
  exact Finset.mem_of_mem_filter xs hxs

lemma measurableSet_jointRowVisitCylinderEventUpToAvoid
    (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) (A : Finset (Fin k)) (N : ℕ) :
    MeasurableSet (jointRowVisitCylinderEventUpToAvoid W v A N) := by
  refine (measurableSet_jointRowVisitCylinderEventUpTo W v N).inter ?_
  have hset : {ω : ℕ → Fin k | ∀ i ∈ A, ∀ t ≤ N, ω t ≠ i}
      = ⋂ i, ⋂ (_ : i ∈ A), ⋂ t, ⋂ (_ : t ≤ N), {ω : ℕ → Fin k | ω t ≠ i} := by
    ext ω
    simp
  rw [hset]
  refine MeasurableSet.iInter fun i => ?_
  refine MeasurableSet.iInter fun _ => ?_
  refine MeasurableSet.iInter fun t => ?_
  refine MeasurableSet.iInter fun _ => ?_
  change MeasurableSet ((fun ω : ℕ → Fin k => ω t) ⁻¹' ({i}ᶜ))
  exact (measurable_pi_apply t) (MeasurableSet.singleton i).compl

lemma measure_jointAvoid_eq_sum_prefixCylinders
    (P : Measure (ℕ → Fin k)) (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k)
    (A : Finset (Fin k)) (N : ℕ) :
    P (jointRowVisitCylinderEventUpToAvoid W v A N) =
      Finset.sum (jointPrefixCarrierAvoid W v A N)
        (fun xs => P (cylinder (k := k) (List.ofFn xs))) := by
  rw [jointRowVisitCylinderEventUpToAvoid_eq_iUnion_cylinder W v A N]
  exact measure_biUnion_finset
    (μ := P)
    (s := jointPrefixCarrierAvoid W v A N)
    (f := fun xs => cylinder (k := k) (List.ofFn xs))
    (pairwiseDisjoint_cylinder_ofFn_on_jointPrefixCarrierAvoid W v A N)
    (fun xs _ => MarkovDeFinettiHard.measurableSet_cylinder (k := k) (List.ofFn xs))

/-- Restricting to a start symbol turns a cylinder measure into its guarded
form (factored from the 5b-ii proof shape). -/
lemma restrict_start_cylinder_apply (P : Measure (ℕ → Fin k)) {N : ℕ} (j : Fin k)
    (xs : Fin (N + 1) → Fin k) :
    (P.restrict {ω : ℕ → Fin k | ω 0 = j}) (cylinder (k := k) (List.ofFn xs)) =
      if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0 := by
  classical
  have hmeas := MarkovDeFinettiHard.measurableSet_cylinder (k := k) (List.ofFn xs)
  by_cases hxs : xs 0 = j
  · have hsubset : cylinder (k := k) (List.ofFn xs) ⊆ {ω : ℕ → Fin k | ω 0 = j} := by
      intro ω hω
      have h0 : ω 0 = xs 0 := by
        have hω' := (mem_cylinder_ofFn_iff (k := k) ω N xs).1 hω
        simpa using hω' ⟨0, Nat.succ_pos _⟩
      simpa [hxs] using h0
    have hinter : {ω : ℕ → Fin k | ω 0 = j} ∩ cylinder (k := k) (List.ofFn xs) =
        cylinder (k := k) (List.ofFn xs) := by
      ext ω
      constructor
      · intro hω
        exact hω.2
      · intro hω
        exact ⟨hsubset hω, hω⟩
    rw [if_pos hxs]
    calc
      (P.restrict {ω : ℕ → Fin k | ω 0 = j}) (cylinder (k := k) (List.ofFn xs))
          = P (cylinder (k := k) (List.ofFn xs) ∩ {ω : ℕ → Fin k | ω 0 = j}) :=
        Measure.restrict_apply (μ := P) hmeas
      _ = P (cylinder (k := k) (List.ofFn xs)) := by
            rw [Set.inter_comm, hinter]
  · have hdisj : cylinder (k := k) (List.ofFn xs) ∩ {ω : ℕ → Fin k | ω 0 = j}
        = (∅ : Set (ℕ → Fin k)) := by
      ext ω
      constructor
      · intro hω
        have h0 : ω 0 = xs 0 := by
          have hω' := (mem_cylinder_ofFn_iff (k := k) ω N xs).1 hω.1
          simpa using hω' ⟨0, Nat.succ_pos _⟩
        exact absurd (by simpa [h0] using hω.2) hxs
      · intro hω
        cases hω
    rw [if_neg hxs]
    calc
      (P.restrict {ω : ℕ → Fin k | ω 0 = j}) (cylinder (k := k) (List.ofFn xs))
          = P (cylinder (k := k) (List.ofFn xs) ∩ {ω : ℕ → Fin k | ω 0 = j}) :=
        Measure.restrict_apply (μ := P) hmeas
      _ = 0 := by
            rw [hdisj]
            simp

lemma measure_start_inter_jointAvoid_eq_sum_prefixCylinders
    (P : Measure (ℕ → Fin k)) (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k)
    (A : Finset (Fin k)) (N : ℕ) (j : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpToAvoid W v A N) =
      Finset.sum (jointPrefixCarrierAvoid W v A N)
        (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
  classical
  have hleft :
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpToAvoid W v A N) =
        (P.restrict {ω : ℕ → Fin k | ω 0 = j})
          (jointRowVisitCylinderEventUpToAvoid W v A N) := by
    have h := Measure.restrict_apply (μ := P) (s := {ω : ℕ → Fin k | ω 0 = j})
      (measurableSet_jointRowVisitCylinderEventUpToAvoid W v A N)
    simpa [Set.inter_comm] using h.symm
  have hsum := measure_jointAvoid_eq_sum_prefixCylinders
    (P := P.restrict {ω : ℕ → Fin k | ω 0 = j}) W v A N
  calc
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpToAvoid W v A N)
        = (P.restrict {ω : ℕ → Fin k | ω 0 = j})
            (jointRowVisitCylinderEventUpToAvoid W v A N) := hleft
    _ = Finset.sum (jointPrefixCarrierAvoid W v A N)
          (fun xs => (P.restrict {ω : ℕ → Fin k | ω 0 = j})
            (cylinder (k := k) (List.ofFn xs))) := hsum
    _ = Finset.sum (jointPrefixCarrierAvoid W v A N)
          (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro xs _
          exact restrict_start_cylinder_apply P j xs

/-- **The avoidance-extended joint measure engine.** -/
lemma measure_start_inter_jointAvoid_eq_of_evidencePreservingEquiv_start
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (W₁ : Fin k → Finset ℕ) (v₁ : Fin k → ℕ → Fin k) (A₁ : Finset (Fin k))
    (W₂ : Fin k → Finset ℕ) (v₂ : Fin k → ℕ → Fin k) (A₂ : Finset (Fin k))
    (N : ℕ) (j : Fin k)
    (e : jointPrefixCarrierAvoid W₁ v₁ A₁ N ≃ jointPrefixCarrierAvoid W₂ v₂ A₂ N)
    (he : ∀ xs : jointPrefixCarrierAvoid W₁ v₁ A₁ N,
        evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpToAvoid W₁ v₁ A₁ N) =
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpToAvoid W₂ v₂ A₂ N) := by
  have hleft := measure_start_inter_jointAvoid_eq_sum_prefixCylinders P W₁ v₁ A₁ N j
  have hright := measure_start_inter_jointAvoid_eq_sum_prefixCylinders P W₂ v₂ A₂ N j
  have hsum :
      Finset.sum (jointPrefixCarrierAvoid W₁ v₁ A₁ N)
          (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) =
        Finset.sum (jointPrefixCarrierAvoid W₂ v₂ A₂ N)
          (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) :=
    sum_cylinderProb_eq_of_extension_and_evidencePreservingEquiv_start
      (k := k) μ hμ P hExt
      (jointPrefixCarrierAvoid W₁ v₁ A₁ N) (jointPrefixCarrierAvoid W₂ v₂ A₂ N) e he j
  calc
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpToAvoid W₁ v₁ A₁ N)
        = Finset.sum (jointPrefixCarrierAvoid W₁ v₁ A₁ N)
            (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) :=
          hleft
    _ = Finset.sum (jointPrefixCarrierAvoid W₂ v₂ A₂ N)
          (fun ys => if ys 0 = j then P (cylinder (k := k) (List.ofFn ys)) else 0) := hsum
    _ = P ({ω : ℕ → Fin k | ω 0 = j}
          ∩ jointRowVisitCylinderEventUpToAvoid W₂ v₂ A₂ N) := hright.symm

/-- **The avoidance-restricted joint carrier equivalence**: the permutation
map preserves evidence, hence occurrence counts, hence avoidance. -/
theorem jointCarrierAvoid_equiv_of_rowPerms [NeZero k] (m : Fin k → ℕ)
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    (v : Fin k → ℕ → Fin k) (A : Finset (Fin k)) (N : ℕ) :
    ∃ e : jointPrefixCarrierAvoid (k := k) (fun i => Finset.range (m i))
          (fun i n => v i (σ i n)) A N
        ≃ jointPrefixCarrierAvoid (k := k) (fun i => Finset.range (m i)) v A N,
      ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1 := by
  have hσ' : ∀ i n, m i - 2 ≤ n → (σ i).symm n = n := fun i n hn =>
    perm_symm_support (σ i) (hσ i) n hn
  have hvals : (fun i n => v i (σ i ((σ i).symm n))) = v := by
    funext i n
    rw [Equiv.apply_symm_apply]
  refine ⟨⟨fun xs => ⟨jointCarrierMapFun σ xs.1, ?_⟩,
    fun ys => ⟨jointCarrierMapFun (fun i => (σ i).symm) ys.1, ?_⟩, ?_, ?_⟩, ?_⟩
  · obtain ⟨hcar, hcount⟩ := mem_jointPrefixCarrierAvoid_iff.mp xs.2
    refine mem_jointPrefixCarrierAvoid_iff.mpr
      ⟨jointCarrierMapFun_mem σ hσ hcar, ?_⟩
    intro i hi
    rw [← occurrences_eq_of_evidenceOf_eq xs.1 (jointCarrierMapFun σ xs.1)
      (evidenceOf_jointCarrierMapFun σ hσ hcar) i]
    exact hcount i hi
  · obtain ⟨hcar, hcount⟩ := mem_jointPrefixCarrierAvoid_iff.mp ys.2
    have hcar' : ys.1 ∈ jointPrefixCarrier (fun i => Finset.range (m i))
        (fun i n => v i (σ i ((σ i).symm n))) N := by
      rw [hvals]
      exact hcar
    refine mem_jointPrefixCarrierAvoid_iff.mpr
      ⟨jointCarrierMapFun_mem (fun i => (σ i).symm) hσ'
        (v := fun i n => v i (σ i n)) hcar', ?_⟩
    intro i hi
    rw [← occurrences_eq_of_evidenceOf_eq ys.1
      (jointCarrierMapFun (fun i => (σ i).symm) ys.1)
      (evidenceOf_jointCarrierMapFun (fun i => (σ i).symm) hσ' hcar) i]
    exact hcount i hi
  · intro xs
    exact Subtype.ext (jointCarrierMapFun_leftInv σ hσ
      (mem_jointPrefixCarrierAvoid_iff.mp xs.2).1)
  · intro ys
    exact Subtype.ext (jointCarrierMapFun_rightInv σ hσ
      (mem_jointPrefixCarrierAvoid_iff.mp ys.2).1)
  · intro xs
    exact evidenceOf_jointCarrierMapFun σ hσ
      (mem_jointPrefixCarrierAvoid_iff.mp xs.2).1

/-- **Per-`N` workhorse**: row-wise last-fixing permutations of the successor
windows do not change the start-restricted measure of the avoidance-extended
joint event. -/
theorem measure_start_inter_jointAvoid_perm_eq [NeZero k]
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (m : Fin k → ℕ) (σ : Fin k → Equiv.Perm ℕ)
    (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    (v : Fin k → ℕ → Fin k) (A : Finset (Fin k)) (N : ℕ) (j : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩
        jointRowVisitCylinderEventUpToAvoid (fun i => Finset.range (m i))
          (fun i n => v i (σ i n)) A N) =
      P ({ω : ℕ → Fin k | ω 0 = j} ∩
        jointRowVisitCylinderEventUpToAvoid (fun i => Finset.range (m i)) v A N) := by
  obtain ⟨e, he⟩ := jointCarrierAvoid_equiv_of_rowPerms m σ hσ v A N
  exact measure_start_inter_jointAvoid_eq_of_evidencePreservingEquiv_start
    μ hμ P hExt _ _ _ _ _ _ N j e he

/-! ## The tail-invariance measure engine

Two evidence-equivalent words (same length, head, last symbol, transition
counts) support the same measure for "cylinder and avoid `A` forever after":
the tail event is a decreasing limit of avoiding bands, each band enumerates
as a disjoint union of extended cylinders, and extended words keep equal
evidence (`transCountL_eq_of_evidence_extend`). -/

open Filter Topology

/-- Avoid the rows in `A` from time `n` onward. -/
def avoidTail (A : Finset (Fin k)) (n : ℕ) : Set (ℕ → Fin k) :=
  {ω | ∀ t, n ≤ t → ω t ∉ A}

/-- Avoid the rows in `A` on the time band `[n, n + M)`. -/
def avoidBand (A : Finset (Fin k)) (n M : ℕ) : Set (ℕ → Fin k) :=
  {ω | ∀ t, n ≤ t → t < n + M → ω t ∉ A}

/-- The `A`-avoiding words of length `M`, as tuples. -/
noncomputable def avoidTuples (A : Finset (Fin k)) (M : ℕ) :
    Finset (Fin M → Fin k) := by
  classical
  exact Finset.univ.filter (fun f => ∀ j, f j ∉ A)

theorem mem_cylinder_iff_getElem (ω : ℕ → Fin k) (xs : List (Fin k)) :
    ω ∈ cylinder (k := k) xs ↔ ∀ i : Fin xs.length, ω i.1 = xs[i.1] := by
  simp [MarkovDeFinettiRecurrence.cylinder, Set.mem_iInter]

theorem getElem_zero_eq_head (l : List (Fin k)) (hl : l ≠ []) (h : 0 < l.length) :
    l[0] = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

/-- A prefix measure never exceeds its root mass `1`. -/
lemma prefixMeasure_apply_le_one (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (w : List (Fin k)) : μ w ≤ 1 := by
  induction w using List.reverseRecOn with
  | nil => exact le_of_eq μ.root_eq_one'
  | append_singleton x a ih =>
      calc μ (x ++ [a]) ≤ ∑ b : Fin k, μ (x ++ [b]) :=
            Finset.single_le_sum (f := fun b => μ (x ++ [b])) (fun b _ => bot_le)
              (Finset.mem_univ a)
      _ = μ x := μ.additive' x
      _ ≤ 1 := ih

/-- Re-tuple a list at an explicitly cast successor length. -/
theorem ofFn_get_cast {n : ℕ} (l : List (Fin k)) (h : n + 1 = l.length) :
    List.ofFn (fun i : Fin (n + 1) => l.get (Fin.cast h i)) = l := by
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact h
  · intro t h₁ h₂
    rw [List.getElem_ofFn]
    rfl

/-- The avoiding band of length `M` after a cylinder enumerates as extended
cylinders over the avoiding words. -/
lemma cylinder_inter_avoidBand_eq_biUnion (w : List (Fin k)) (A : Finset (Fin k))
    (M : ℕ) :
    cylinder (k := k) w ∩ avoidBand A w.length M =
      ⋃ f ∈ avoidTuples (k := k) A M, cylinder (k := k) (w ++ List.ofFn f) := by
  classical
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_iUnion, avoidBand, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcyl, hband⟩
    refine ⟨fun j => ω (w.length + j.1), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro j
      exact hband (w.length + j.1) (Nat.le_add_right _ _) (by have := j.2; omega)
    · rw [mem_cylinder_iff_getElem]
      have key : ∀ n : ℕ,
          ∀ _ : n < (w ++ List.ofFn (fun j : Fin M => ω (w.length + j.1))).length,
          ω n = (w ++ List.ofFn (fun j : Fin M => ω (w.length + j.1)))[n] := by
        intro n hn
        by_cases hi : n < w.length
        · rw [List.getElem_append_left hi]
          exact (mem_cylinder_iff_getElem ω w).mp hcyl ⟨n, hi⟩
        · have hi' : w.length ≤ n := Nat.le_of_not_lt hi
          rw [List.getElem_append_right hi', List.getElem_ofFn]
          congr 1
          show n = w.length + (n - w.length)
          omega
      intro i
      exact key i.1 i.2
  · rintro ⟨f, hfA, hcylwf⟩
    have hmem := (mem_cylinder_iff_getElem ω (w ++ List.ofFn f)).mp hcylwf
    have hflen : (w ++ List.ofFn f).length = w.length + M := by
      rw [List.length_append, List.length_ofFn]
    constructor
    · rw [mem_cylinder_iff_getElem]
      intro i
      have hi' : i.1 < (w ++ List.ofFn f).length := by
        have := i.2
        omega
      have h := hmem ⟨i.1, hi'⟩
      rw [List.getElem_append_left i.2] at h
      exact h
    · intro t ht htM
      have ht' : t < (w ++ List.ofFn f).length := by omega
      have h := hmem ⟨t, ht'⟩
      rw [List.getElem_append_right ht, List.getElem_ofFn] at h
      rw [h]
      exact (Finset.mem_filter.mp hfA).2 ⟨t - w.length, by omega⟩

lemma pairwiseDisjoint_cylinder_append_ofFn (w : List (Fin k)) (A : Finset (Fin k))
    (M : ℕ) :
    ((↑(avoidTuples (k := k) A M) : Set (Fin M → Fin k))).PairwiseDisjoint
      (fun f => cylinder (k := k) (w ++ List.ofFn f)) := by
  intro f _ g _ hfg
  refine Set.disjoint_left.2 ?_
  intro ω hωf hωg
  refine hfg ?_
  funext j
  have h1 := (mem_cylinder_iff_getElem ω (w ++ List.ofFn f)).mp hωf
  have h2 := (mem_cylinder_iff_getElem ω (w ++ List.ofFn g)).mp hωg
  have hj1 : w.length + j.1 < (w ++ List.ofFn f).length := by
    rw [List.length_append, List.length_ofFn]
    have := j.2
    omega
  have hj2 : w.length + j.1 < (w ++ List.ofFn g).length := by
    rw [List.length_append, List.length_ofFn]
    have := j.2
    omega
  have e1 := h1 ⟨w.length + j.1, hj1⟩
  have e2 := h2 ⟨w.length + j.1, hj2⟩
  rw [List.getElem_append_right (Nat.le_add_right _ _), List.getElem_ofFn] at e1 e2
  have hval : w.length + j.1 - w.length = j.1 := by omega
  simp only [hval, Fin.eta] at e1 e2
  exact e1.symm.trans e2

lemma measurableSet_avoidBand (A : Finset (Fin k)) (n M : ℕ) :
    MeasurableSet (avoidBand (k := k) A n M) := by
  have hset : avoidBand (k := k) A n M
      = ⋂ t, ⋂ (_ : n ≤ t), ⋂ (_ : t < n + M), {ω : ℕ → Fin k | ω t ∉ A} := by
    ext ω
    simp [avoidBand]
  rw [hset]
  refine MeasurableSet.iInter fun t => ?_
  refine MeasurableSet.iInter fun _ => ?_
  refine MeasurableSet.iInter fun _ => ?_
  change MeasurableSet ((fun ω : ℕ → Fin k => ω t) ⁻¹' ((↑A : Set (Fin k))ᶜ))
  exact (measurable_pi_apply t) (A.measurableSet.compl)

lemma measure_cylinder_inter_avoidBand_eq_sum (P : Measure (ℕ → Fin k))
    (w : List (Fin k)) (A : Finset (Fin k)) (M : ℕ) :
    P (cylinder (k := k) w ∩ avoidBand A w.length M) =
      Finset.sum (avoidTuples (k := k) A M)
        (fun f => P (cylinder (k := k) (w ++ List.ofFn f))) := by
  rw [cylinder_inter_avoidBand_eq_biUnion w A M]
  exact measure_biUnion_finset
    (μ := P)
    (s := avoidTuples (k := k) A M)
    (f := fun f => cylinder (k := k) (w ++ List.ofFn f))
    (pairwiseDisjoint_cylinder_append_ofFn w A M)
    (fun f _ => MarkovDeFinettiHard.measurableSet_cylinder (k := k) (w ++ List.ofFn f))

/-- **The tail-invariance engine.** Words of equal length, head, last symbol,
and transition counts have equal cylinder-and-avoid-forever measures. -/
lemma measure_cylinder_inter_avoidTail_eq_of_evidence
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    {w w' : List (Fin k)} (hw : w ≠ []) (hw' : w' ≠ [])
    (hlen : w.length = w'.length)
    (hhead : w.head hw = w'.head hw')
    (hlast : w.getLast hw = w'.getLast hw')
    (htc : ∀ a b, transCountL w a b = transCountL w' a b)
    (A : Finset (Fin k)) :
    P (cylinder (k := k) w ∩ avoidTail A w.length) =
      P (cylinder (k := k) w' ∩ avoidTail A w'.length) := by
  classical
  have hw0 : 0 < w.length := by
    rw [← List.ne_nil_iff_length_pos]
    exact hw
  have hw0' : 0 < w'.length := by
    rw [← List.ne_nil_iff_length_pos]
    exact hw'
  have hdecomp : ∀ (x : List (Fin k)),
      cylinder (k := k) x ∩ avoidTail A x.length
        = ⋂ M : ℕ, (cylinder (k := k) x ∩ avoidBand A x.length M) := by
    intro x
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iInter, avoidTail, avoidBand,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨hc, ha⟩ M
      exact ⟨hc, fun t ht _ => ha t ht⟩
    · intro h
      refine ⟨(h 0).1, fun t ht => ?_⟩
      exact (h (t - x.length + 1)).2 t ht (by omega)
  have hseq : (fun M => P (cylinder (k := k) w ∩ avoidBand A w.length M))
      = fun M => P (cylinder (k := k) w' ∩ avoidBand A w'.length M) := by
    funext M
    rw [measure_cylinder_inter_avoidBand_eq_sum P w A M,
      measure_cylinder_inter_avoidBand_eq_sum P w' A M]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← hExt (w ++ List.ofFn f), ← hExt (w' ++ List.ofFn f)]
    have hlen1 : (w.length - 1 + M) + 1 = (w ++ List.ofFn f).length := by
      rw [List.length_append, List.length_ofFn]
      omega
    have hlen2 : (w.length - 1 + M) + 1 = (w' ++ List.ofFn f).length := by
      rw [List.length_append, List.length_ofFn]
      omega
    rw [← ofFn_get_cast (w ++ List.ofFn f) hlen1,
      ← ofFn_get_cast (w' ++ List.ofFn f) hlen2]
    refine hμ (w.length - 1 + M) _ _ ?_
    refine evidenceOf_eq_of_head_transCountL _ _ ?_ ?_
    · -- heads agree
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [Fin.val_cast, Fin.val_zero]
      rw [List.getElem_append_left hw0, List.getElem_append_left hw0',
        getElem_zero_eq_head w hw hw0, getElem_zero_eq_head w' hw' hw0']
      exact hhead
    · intro a b
      rw [ofFn_get_cast (w ++ List.ofFn f) hlen1,
        ofFn_get_cast (w' ++ List.ofFn f) hlen2]
      exact transCountL_eq_of_evidence_extend hw hw' hlast htc (List.ofFn f) a b
  have hmeas : ∀ (x : List (Fin k)) (M : ℕ),
      MeasureTheory.NullMeasurableSet
        (cylinder (k := k) x ∩ avoidBand A x.length M) P :=
    fun x M => ((MarkovDeFinettiHard.measurableSet_cylinder (k := k) x).inter
      (measurableSet_avoidBand A x.length M)).nullMeasurableSet
  have hanti : ∀ (x : List (Fin k)),
      Antitone (fun M => cylinder (k := k) x ∩ avoidBand A x.length M) := by
    intro x M M' hMM' ω hω
    exact ⟨hω.1, fun t ht htM => hω.2 t ht (by omega)⟩
  have hfin : ∀ (x : List (Fin k)),
      ∃ M, P (cylinder (k := k) x ∩ avoidBand A x.length M) ≠ ⊤ := by
    intro x
    refine ⟨0, ?_⟩
    have hle : P (cylinder (k := k) x ∩ avoidBand A x.length 0)
        ≤ P (cylinder (k := k) x) := measure_mono Set.inter_subset_left
    have hfin1 : P (cylinder (k := k) x) ≠ ⊤ := by
      rw [← hExt x]
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (prefixMeasure_apply_le_one μ x)
    exact ne_top_of_le_ne_top hfin1 hle
  have h1' : Tendsto (fun M => P (cylinder (k := k) w ∩ avoidBand A w.length M))
      atTop (𝓝 (P (⋂ M, cylinder (k := k) w ∩ avoidBand A w.length M))) :=
    MeasureTheory.tendsto_measure_iInter_atTop (μ := P)
      (fun M => hmeas w M) (hanti w) (hfin w)
  have h2' : Tendsto (fun M => P (cylinder (k := k) w' ∩ avoidBand A w'.length M))
      atTop (𝓝 (P (⋂ M, cylinder (k := k) w' ∩ avoidBand A w'.length M))) :=
    MeasureTheory.tendsto_measure_iInter_atTop (μ := P)
      (fun M => hmeas w' M) (hanti w') (hfin w')
  rw [← hseq] at h2'
  rw [hdecomp w, hdecomp w']
  exact tendsto_nhds_unique h1' h2'

/-- The mapped tuple's word keeps the last symbol (keystone
`decode_getLast_eq` through the carrier map). -/
theorem jointCarrierMapFun_getLast [NeZero k] {N : ℕ} {m : Fin k → ℕ}
    (σ : Fin k → Equiv.Perm ℕ) (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    {v' : Fin k → ℕ → Fin k} {xs : Fin (N + 1) → Fin k}
    (hxs : xs ∈ jointPrefixCarrier (fun i => Finset.range (m i)) v' N) :
    (List.ofFn (jointCarrierMapFun σ xs)).getLast (by simp)
      = (List.ofFn xs).getLast (by simp) := by
  obtain ⟨hsupp, hperm, hlast⟩ := rowPermLast_of_carrier σ hσ hxs
  have hofn := ofFn_jointCarrierMapFun σ hσ hxs
  have hgl := decode_getLast_eq (xs 0) (List.ofFn fun t : Fin N => xs t.succ)
    (fun i => permuteList (σ i).symm (rowSuccessors i (List.ofFn xs))) hperm
  simp only [hofn]
  rw [hgl]
  simp only [List.ofFn_succ]

/-- Carrier-level tail-invariant sum transport for the row-permutation map:
mirror of the evidence-preserving sum lemma, with the cylinder replaced by
cylinder-and-avoid-forever. -/
lemma sum_cylinderProb_avoidTail_eq_of_rowPerms [NeZero k]
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    {N : ℕ} (m : Fin k → ℕ) (σ : Fin k → Equiv.Perm ℕ)
    (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    (v : Fin k → ℕ → Fin k) (A : Finset (Fin k)) (j : Fin k) :
    Finset.sum (jointPrefixCarrierAvoid (fun i => Finset.range (m i))
        (fun i n => v i (σ i n)) A N)
      (fun xs => if xs 0 = j
        then P (cylinder (k := k) (List.ofFn xs) ∩ avoidTail A (N + 1)) else 0) =
    Finset.sum (jointPrefixCarrierAvoid (fun i => Finset.range (m i)) v A N)
      (fun xs => if xs 0 = j
        then P (cylinder (k := k) (List.ofFn xs) ∩ avoidTail A (N + 1)) else 0) := by
  classical
  have hσ' : ∀ i n, m i - 2 ≤ n → (σ i).symm n = n := fun i n hn =>
    perm_symm_support (σ i) (hσ i) n hn
  have hvals : (fun i n => v i (σ i ((σ i).symm n))) = v := by
    funext i n
    rw [Equiv.apply_symm_apply]
  refine Finset.sum_bij' (fun xs _ => jointCarrierMapFun σ xs)
    (fun ys _ => jointCarrierMapFun (fun i => (σ i).symm) ys) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro xs hxs
    obtain ⟨hcar, hcount⟩ := mem_jointPrefixCarrierAvoid_iff.mp hxs
    refine mem_jointPrefixCarrierAvoid_iff.mpr
      ⟨jointCarrierMapFun_mem σ hσ hcar, ?_⟩
    intro i hi
    rw [← occurrences_eq_of_evidenceOf_eq xs (jointCarrierMapFun σ xs)
      (evidenceOf_jointCarrierMapFun σ hσ hcar) i]
    exact hcount i hi
  · -- backward membership
    intro ys hys
    obtain ⟨hcar, hcount⟩ := mem_jointPrefixCarrierAvoid_iff.mp hys
    have hcar' : ys ∈ jointPrefixCarrier (fun i => Finset.range (m i))
        (fun i n => v i (σ i ((σ i).symm n))) N := by
      rw [hvals]
      exact hcar
    refine mem_jointPrefixCarrierAvoid_iff.mpr
      ⟨jointCarrierMapFun_mem (fun i => (σ i).symm) hσ'
        (v := fun i n => v i (σ i n)) hcar', ?_⟩
    intro i hi
    rw [← occurrences_eq_of_evidenceOf_eq ys
      (jointCarrierMapFun (fun i => (σ i).symm) ys)
      (evidenceOf_jointCarrierMapFun (fun i => (σ i).symm) hσ' hcar) i]
    exact hcount i hi
  · -- left inverse
    intro xs hxs
    exact jointCarrierMapFun_leftInv σ hσ
      (mem_jointPrefixCarrierAvoid_iff.mp hxs).1
  · -- right inverse
    intro ys hys
    exact jointCarrierMapFun_rightInv σ hσ
      (mem_jointPrefixCarrierAvoid_iff.mp hys).1
  · -- per-term equality
    intro xs hxs
    have hcar := (mem_jointPrefixCarrierAvoid_iff.mp hxs).1
    have hhead := jointCarrierMapFun_head σ (N := N) xs
    rw [hhead]
    by_cases hj : xs 0 = j
    · rw [if_pos hj, if_pos hj]
      have hev := evidenceOf_jointCarrierMapFun σ hσ hcar
      obtain ⟨hhead', htc⟩ := (evidenceOf_eq_iff xs (jointCarrierMapFun σ xs)).mp hev
      have h := measure_cylinder_inter_avoidTail_eq_of_evidence μ hμ P hExt
        (w := List.ofFn xs) (w' := List.ofFn (jointCarrierMapFun σ xs))
        (by simp) (by simp) (by simp)
        (by rw [head_ofFn_zero, head_ofFn_zero, jointCarrierMapFun_head])
        (jointCarrierMapFun_getLast σ hσ hcar).symm htc A
      simp only [List.length_ofFn] at h
      exact h
    · rw [if_neg hj, if_neg hj]

/-! ## Toward the un-truncated joint FDD equality: multiJRE and profiles -/

open PerRowJointPE

/-- The multi-row joint row-successor event: every row `i` satisfies its
window of successor-value constraints, un-truncated. -/
def multiJRE (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) : Set (ℕ → Fin k) :=
  ⋂ i, jointRowSuccEvent (k := k) i (W i) (v i)

/-- On the never-visited event, a row's joint successor event collapses to the
(ω-free) condition that all required values equal `i`. -/
lemma jointRowSuccEvent_inter_notVisited (i : Fin k) (S : Finset ℕ)
    (v' : ℕ → Fin k) :
    jointRowSuccEvent (k := k) i S v' ∩ {ω | ∀ t, ω t ≠ i} =
      {_ω : ℕ → Fin k | ∀ n ∈ S, v' n = i} ∩ {ω | ∀ t, ω t ≠ i} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, jointRowSuccEvent,
    Set.mem_iInter, rowSuccessorValueEvent]
  have hall : (∀ t, ω t ≠ i) → ∀ n, rowSuccessorAtNthVisit (k := k) i n ω = i := by
    intro hNV n
    simp only [rowSuccessorAtNthVisit]
    cases hn' : nthVisitTime (k := k) ω i n with
    | none => rfl
    | some t =>
        exact absurd ((nthVisitTime_eq_some_iff (k := k) ω i n t).mp hn').1 (hNV t)
  constructor
  · rintro ⟨hJ, hNV⟩
    refine ⟨fun n hn => ?_, hNV⟩
    have hmem := hJ n hn
    rw [hall hNV n] at hmem
    exact hmem.symm
  · rintro ⟨hv, hNV⟩
    refine ⟨fun n hn => ?_, hNV⟩
    rw [hall hNV n, hv n hn]

/-- σ-invariance of the collapse condition: `σ i` permutes the window. -/
lemma forall_window_comp_perm_iff (m : Fin k → ℕ) (σ : Fin k → Equiv.Perm ℕ)
    (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n) (v : Fin k → ℕ → Fin k) (i : Fin k) :
    (∀ n ∈ Finset.range (m i), v i (σ i n) = i) ↔
      (∀ n ∈ Finset.range (m i), v i n = i) := by
  constructor
  · intro h n hn
    have hn' : (σ i).symm n < m i := by
      have hsupp : ∀ j, m i ≤ j → (σ i).symm j = j := fun j hj =>
        perm_symm_support (σ i) (hσ i) j (by omega)
      exact perm_lt_of_support_lt (σ i).symm hsupp n (Finset.mem_range.mp hn)
    have h' := h ((σ i).symm n) (Finset.mem_range.mpr hn')
    rwa [Equiv.apply_symm_apply] at h'
  · intro h n hn
    have hn' : σ i n < m i := by
      have hsupp : ∀ j, m i ≤ j → σ i j = j := fun j hj => hσ i j (by omega)
      exact perm_lt_of_support_lt (σ i) hsupp n (Finset.mem_range.mp hn)
    exact h (σ i n) (Finset.mem_range.mpr hn')

/-- Visited/never-visited profile over the constrained rows `C`: the rows in
`T` are visited, the rows in `C \ T` never. -/
def profileEvent (C T : Finset (Fin k)) : Set (ℕ → Fin k) :=
  (⋂ i ∈ T, {ω : ℕ → Fin k | ∃ t, ω t = i}) ∩
    (⋂ i ∈ C \ T, {ω : ℕ → Fin k | ∀ t, ω t ≠ i})

lemma mem_profileEvent_iff {C T : Finset (Fin k)} {ω : ℕ → Fin k} :
    ω ∈ profileEvent C T ↔
      (∀ i ∈ T, ∃ t, ω t = i) ∧ (∀ i ∈ C \ T, ∀ t, ω t ≠ i) := by
  simp [profileEvent]

/-- The profiles over subsets of `C` cover everything. -/
lemma iUnion_profileEvent (C : Finset (Fin k)) :
    ⋃ T ∈ C.powerset, profileEvent C T = Set.univ := by
  classical
  ext ω
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨C.filter (fun i => ∃ t, ω t = i),
    Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  rw [mem_profileEvent_iff]
  constructor
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi t hcon
    have hs := Finset.mem_sdiff.mp hi
    exact hs.2 (Finset.mem_filter.mpr ⟨hs.1, ⟨t, hcon⟩⟩)

/-- Distinct profiles are disjoint. -/
lemma pairwiseDisjoint_profileEvent (C : Finset (Fin k)) :
    ((↑C.powerset : Set (Finset (Fin k)))).PairwiseDisjoint (profileEvent C) := by
  intro T₁ h₁ T₂ h₂ hne
  refine Set.disjoint_left.2 fun ω hω₁ hω₂ => ?_
  refine hne ?_
  have m₁ := mem_profileEvent_iff.mp hω₁
  have m₂ := mem_profileEvent_iff.mp hω₂
  simp only [Finset.mem_coe, Finset.mem_powerset] at h₁ h₂
  ext i
  constructor
  · intro hi
    by_contra hni
    obtain ⟨t, ht⟩ := m₁.1 i hi
    exact m₂.2 i (Finset.mem_sdiff.mpr ⟨h₁ hi, hni⟩) t ht
  · intro hi
    by_contra hni
    obtain ⟨t, ht⟩ := m₂.1 i hi
    exact m₁.2 i (Finset.mem_sdiff.mpr ⟨h₂ hi, hni⟩) t ht

lemma measurableSet_profileEvent (C T : Finset (Fin k)) :
    MeasurableSet (profileEvent C T) := by
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun i => ?_
    refine MeasurableSet.iInter fun _ => ?_
    have hset : {ω : ℕ → Fin k | ∃ t, ω t = i}
        = ⋃ t, (fun ω : ℕ → Fin k => ω t) ⁻¹' {i} := by
      ext ω
      simp [Set.mem_iUnion]
    rw [hset]
    exact MeasurableSet.iUnion fun t =>
      (measurable_pi_apply t) (MeasurableSet.singleton i)
  · refine MeasurableSet.iInter fun i => ?_
    refine MeasurableSet.iInter fun _ => ?_
    have hset : {ω : ℕ → Fin k | ∀ t, ω t ≠ i}
        = ⋂ t, (fun ω : ℕ → Fin k => ω t) ⁻¹' ({i}ᶜ) := by
      ext ω
      simp
    rw [hset]
    exact MeasurableSet.iInter fun t =>
      (measurable_pi_apply t) (MeasurableSet.singleton i).compl

/-- Partition of any event's measure over the visited/never-visited profiles. -/
lemma measure_eq_sum_profile (P : Measure (ℕ → Fin k)) (E : Set (ℕ → Fin k))
    (hE : MeasurableSet E) (C : Finset (Fin k)) :
    P E = Finset.sum C.powerset (fun T => P (E ∩ profileEvent C T)) := by
  classical
  have hdecomp : E = ⋃ T ∈ C.powerset, (E ∩ profileEvent C T) := by
    conv_lhs => rw [← Set.inter_univ E, ← iUnion_profileEvent C]
    exact Set.inter_iUnion₂ _ _
  conv_lhs => rw [hdecomp]
  exact measure_biUnion_finset
    (μ := P) (s := C.powerset) (f := fun T => E ∩ profileEvent C T)
    ((pairwiseDisjoint_profileEvent C).mono
      (fun T => Set.inter_subset_right))
    (fun T _ => hE.inter (measurableSet_profileEvent C T))

/-! ## Per-profile reduction, absorption, and assembly

Per profile `T` over the constrained rows `C`, the never-visited rows'
`multiJRE` factors collapse to ω-free conditions plus an `avoidTail` factor;
the visited rows absorb into truncated events by per-row peeling; the
truncated events transport under row permutations per `N` with the tail
factor riding along; the profiles then sum back up. -/

/-- A never-visited row's successor readings all default to the anchor. -/
theorem rowSuccessorAtNthVisit_eq_self_of_never_visited (i : Fin k)
    (ω : ℕ → Fin k) (hNV : ∀ t, ω t ≠ i) (n : ℕ) :
    rowSuccessorAtNthVisit (k := k) i n ω = i := by
  simp only [rowSuccessorAtNthVisit]
  cases hn' : nthVisitTime (k := k) ω i n with
  | none => rfl
  | some t =>
      exact absurd ((nthVisitTime_eq_some_iff (k := k) ω i n t).mp hn').1 (hNV t)

/-- **Good-case profile reduction.** When every never-visited constrained row's
required values equal its anchor, the profile piece of `multiJRE` reduces to
the visited rows' joint events (with visit witnesses) and an avoid factor. -/
lemma multiJRE_inter_profileEvent_of_good (m : Fin k → ℕ) (v' : Fin k → ℕ → Fin k)
    (C T : Finset (Fin k)) (hC : ∀ i, i ∉ C → m i = 0)
    (hgood : ∀ i ∈ C \ T, ∀ n ∈ Finset.range (m i), v' i n = i) :
    multiJRE (fun i => Finset.range (m i)) v' ∩ profileEvent C T =
      (⋂ i ∈ T, (jointRowSuccEvent (k := k) i (Finset.range (m i)) (v' i)
          ∩ {ω : ℕ → Fin k | ∃ t, ω t = i}))
        ∩ avoidTail (C \ T) 0 := by
  ext ω
  simp only [multiJRE, profileEvent, jointRowSuccEvent, rowSuccessorValueEvent,
    avoidTail, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hJ, hV, hNV⟩
    exact ⟨fun i hi => ⟨fun n hn => hJ i n hn, hV i hi⟩,
      fun t _ hmem => hNV (ω t) hmem t rfl⟩
  · rintro ⟨hT, hA⟩
    have hNV : ∀ i ∈ C \ T, ∀ t, ω t ≠ i := fun i hi t hcon =>
      hA t (Nat.zero_le t) (by rw [hcon]; exact hi)
    refine ⟨fun i n hn => ?_, fun i hi => (hT i hi).2, hNV⟩
    by_cases hiT : i ∈ T
    · exact (hT i hiT).1 n hn
    · by_cases hiC : i ∈ C
      · have hi' : i ∈ C \ T := Finset.mem_sdiff.mpr ⟨hiC, hiT⟩
        rw [rowSuccessorAtNthVisit_eq_self_of_never_visited i ω (hNV i hi') n]
        exact (hgood i hi' n hn).symm
      · rw [hC i hiC] at hn
        simp at hn

/-- **Bad-case profile piece is empty**: a never-visited constrained row whose
required value differs from the anchor kills the whole piece. -/
lemma multiJRE_inter_profileEvent_eq_empty_of_bad (m : Fin k → ℕ)
    (v' : Fin k → ℕ → Fin k) (C T : Finset (Fin k)) (i₀ : Fin k)
    (hi₀ : i₀ ∈ C \ T) (n₀ : ℕ) (hn₀ : n₀ ∈ Finset.range (m i₀))
    (hbad : v' i₀ n₀ ≠ i₀) :
    multiJRE (fun i => Finset.range (m i)) v' ∩ profileEvent C T = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun ω hω => ?_
  obtain ⟨hJ, hprof⟩ := hω
  have hNV : ∀ t, ω t ≠ i₀ := (mem_profileEvent_iff.mp hprof).2 i₀ hi₀
  have hval : rowSuccessorAtNthVisit (k := k) i₀ n₀ ω = v' i₀ n₀ :=
    Set.mem_iInter₂.mp (Set.mem_iInter.mp hJ i₀) n₀ hn₀
  rw [rowSuccessorAtNthVisit_eq_self_of_never_visited i₀ ω hNV n₀] at hval
  exact hbad hval.symm

lemma measurableSet_multiJRE (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k) :
    MeasurableSet (multiJRE (k := k) W v) :=
  MeasurableSet.iInter fun i =>
    MeasurableSet.biInter (Finset.countable_toSet (W i)) fun n _ =>
      measurableSet_rowSuccessorValueEvent (k := k) i n (v i n)

/-- **Per-row peeling absorption.** Against an arbitrary rest set `R`, each
visited row's un-truncated joint event (with its visit witness) absorbs into
the union of its truncated approximations, one row at a time. -/
lemma measure_inter_biInter_JRE_visited_eq_iUnion_upTo
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hStrRec : StrongRecurrence (k := k) P)
    (m : Fin k → ℕ) (v' : Fin k → ℕ → Fin k)
    (T : Finset (Fin k)) (hm : ∀ i ∈ T, m i ≠ 0) (R : Set (ℕ → Fin k)) :
    P (R ∩ ⋂ i ∈ T, (jointRowSuccEvent (k := k) i (Finset.range (m i)) (v' i)
        ∩ {ω : ℕ → Fin k | ∃ t, ω t = i})) =
      P (R ∩ ⋂ i ∈ T, ⋃ N : ℕ,
        rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i)) (v' i) N) := by
  classical
  induction T using Finset.induction generalizing R with
  | empty => simp
  | @insert a T' ha ih =>
      have hma : m a ≠ 0 := hm a (Finset.mem_insert_self a T')
      have hm' : ∀ i ∈ T', m i ≠ 0 := fun i hi => hm i (Finset.mem_insert_of_mem hi)
      rw [Finset.set_biInter_insert, Finset.set_biInter_insert]
      set JVa := jointRowSuccEvent (k := k) a (Finset.range (m a)) (v' a)
        ∩ {ω : ℕ → Fin k | ∃ t, ω t = a} with hJVa
      set B := ⋂ i ∈ T', (jointRowSuccEvent (k := k) i (Finset.range (m i)) (v' i)
        ∩ {ω : ℕ → Fin k | ∃ t, ω t = i}) with hB
      set B' := ⋂ i ∈ T', ⋃ N : ℕ,
        rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i)) (v' i) N with hB'
      set Ua := ⋃ N : ℕ,
        rowVisitCylinderEventUpTo (k := k) a (Finset.range (m a)) (v' a) N with hUa
      have e1 : R ∩ (JVa ∩ B) = (R ∩ JVa) ∩ B := (Set.inter_assoc R JVa B).symm
      have h1 : P ((R ∩ JVa) ∩ B) = P ((R ∩ JVa) ∩ B') := ih hm' (R ∩ JVa)
      have e2 : (R ∩ JVa) ∩ B' =
          ((R ∩ B') ∩ jointRowSuccEvent (k := k) a (Finset.range (m a)) (v' a))
            ∩ {ω : ℕ → Fin k | ∃ t, ω t = a} := by
        rw [hJVa]
        ext ω
        simp only [Set.mem_inter_iff]
        tauto
      have h2 : P (((R ∩ B') ∩ jointRowSuccEvent (k := k) a (Finset.range (m a)) (v' a))
            ∩ {ω : ℕ → Fin k | ∃ t, ω t = a}) =
          P ((R ∩ B') ∩ Ua) :=
        measure_JRE_inter_V_eq_upTo_of_rowRecurrence (k := k) P a (hStrRec a)
          (R ∩ B') (Finset.range (m a)) (v' a)
          ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hma)⟩
      have e3 : (R ∩ B') ∩ Ua = R ∩ (Ua ∩ B') := by
        ext ω
        simp only [Set.mem_inter_iff]
        tauto
      rw [e1, h1, e2, h2, e3]

/-- Finitely many monotone unions of truncated events merge into one union. -/
lemma biInter_iUnion_upTo_eq_iUnion_biInter (m : Fin k → ℕ)
    (v' : Fin k → ℕ → Fin k) (T : Finset (Fin k)) :
    (⋂ i ∈ T, ⋃ N : ℕ,
        rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i)) (v' i) N) =
      ⋃ N : ℕ, ⋂ i ∈ T,
        rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i)) (v' i) N := by
  classical
  apply Set.Subset.antisymm
  · intro ω hω
    have h : ∀ i ∈ T, ∃ N : ℕ,
        ω ∈ rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i)) (v' i) N :=
      fun i hi => Set.mem_iUnion.mp (Set.mem_iInter₂.mp hω i hi)
    choose! f hf using h
    refine Set.mem_iUnion.mpr ⟨T.sup f, Set.mem_iInter₂.mpr fun i hi => ?_⟩
    exact rowVisitCylinderEventUpTo_mono' (k := k) i (Finset.range (m i)) (v' i)
      (Finset.le_sup hi) (hf i hi)
  · intro ω hω
    rcases Set.mem_iUnion.mp hω with ⟨N, hN⟩
    exact Set.mem_iInter₂.mpr fun i hi =>
      Set.mem_iUnion.mpr ⟨N, Set.mem_iInter₂.mp hN i hi⟩

lemma measurableSet_avoidTail (A : Finset (Fin k)) (n : ℕ) :
    MeasurableSet (avoidTail (k := k) A n) := by
  have hset : avoidTail (k := k) A n
      = ⋂ t, ⋂ (_ : n ≤ t), {ω : ℕ → Fin k | ω t ∉ A} := by
    ext ω
    simp [avoidTail]
  rw [hset]
  refine MeasurableSet.iInter fun t => ?_
  refine MeasurableSet.iInter fun _ => ?_
  change MeasurableSet ((fun ω : ℕ → Fin k => ω t) ⁻¹' ((↑A : Set (Fin k))ᶜ))
  exact (measurable_pi_apply t) (A.measurableSet.compl)

/-- Avoiding forever splits into the prefix band up to `N` and the tail
from `N + 1` on. -/
lemma avoidTail_zero_eq_band_inter (A : Finset (Fin k)) (N : ℕ) :
    avoidTail (k := k) A 0 =
      {ω : ℕ → Fin k | ∀ i ∈ A, ∀ t ≤ N, ω t ≠ i} ∩ avoidTail A (N + 1) := by
  ext ω
  simp only [avoidTail, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i hi t ht hcon => h t (Nat.zero_le t) (by rw [hcon]; exact hi),
      fun t _ => h t (Nat.zero_le t)⟩
  · rintro ⟨h1, h2⟩ t _
    by_cases ht : t ≤ N
    · intro hmem
      exact h1 (ω t) hmem t ht rfl
    · exact h2 t (by omega)

/-- The visited rows' truncated events assemble to the joint event with
windows emptied off `T`. -/
lemma biInter_upTo_eq_jointUpTo [DecidableEq (Fin k)] (m : Fin k → ℕ)
    (v' : Fin k → ℕ → Fin k) (T : Finset (Fin k)) (N : ℕ) :
    (⋂ i ∈ T, rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i)) (v' i) N) =
      jointRowVisitCylinderEventUpTo
        (fun i => Finset.range (if i ∈ T then m i else 0)) v' N := by
  ext ω
  simp only [jointRowVisitCylinderEventUpTo, Set.mem_iInter,
    rowVisitCylinderEventUpTo, Set.mem_setOf_eq]
  constructor
  · intro h i n hn
    by_cases hi : i ∈ T
    · rw [if_pos hi] at hn
      exact h i hi n hn
    · rw [if_neg hi] at hn
      simp at hn
  · intro h i hi n hn
    have hn' : n ∈ Finset.range (if i ∈ T then m i else 0) := by
      rw [if_pos hi]
      exact hn
    exact h i n hn'

/-- Per-`N` shape conversion: start ∩ avoid-forever ∩ truncated events equals
start ∩ avoidance-extended joint event, with the strict tail riding along. -/
lemma start_inter_avoidTail_inter_biInter_upTo_eq (m : Fin k → ℕ)
    (v' : Fin k → ℕ → Fin k) (T A : Finset (Fin k)) (N : ℕ) (j : Fin k) :
    {ω : ℕ → Fin k | ω 0 = j} ∩ avoidTail A 0 ∩
        (⋂ i ∈ T, rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i)) (v' i) N) =
      ({ω : ℕ → Fin k | ω 0 = j} ∩
          jointRowVisitCylinderEventUpToAvoid
            (fun i => Finset.range (if i ∈ T then m i else 0)) v' A N) ∩
        avoidTail A (N + 1) := by
  rw [avoidTail_zero_eq_band_inter A N, biInter_upTo_eq_jointUpTo m v' T N,
    jointRowVisitCylinderEventUpToAvoid]
  ext ω
  simp only [Set.mem_inter_iff]
  tauto

/-- Sum representation of the avoidance-extended joint event with the strict
tail factor riding through the disjoint cylinder decomposition. -/
lemma measure_start_inter_jointAvoid_inter_avoidTail_eq_sum
    (P : Measure (ℕ → Fin k)) (W : Fin k → Finset ℕ) (v : Fin k → ℕ → Fin k)
    (A : Finset (Fin k)) (N : ℕ) (j : Fin k) :
    P (({ω : ℕ → Fin k | ω 0 = j} ∩ jointRowVisitCylinderEventUpToAvoid W v A N)
        ∩ avoidTail A (N + 1)) =
      Finset.sum (jointPrefixCarrierAvoid W v A N)
        (fun xs => if xs 0 = j
          then P (cylinder (k := k) (List.ofFn xs) ∩ avoidTail A (N + 1)) else 0) := by
  classical
  have hS0meas : MeasurableSet {ω : ℕ → Fin k | ω 0 = j} := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({j} : Set (Fin k)))
    exact (measurable_pi_apply 0) (MeasurableSet.singleton j)
  have hunion : ({ω : ℕ → Fin k | ω 0 = j}
        ∩ jointRowVisitCylinderEventUpToAvoid W v A N) ∩ avoidTail A (N + 1) =
      ⋃ xs ∈ jointPrefixCarrierAvoid W v A N,
        (({ω : ℕ → Fin k | ω 0 = j} ∩ cylinder (k := k) (List.ofFn xs))
          ∩ avoidTail A (N + 1)) := by
    rw [jointRowVisitCylinderEventUpToAvoid_eq_iUnion_cylinder W v A N]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    tauto
  rw [hunion, measure_biUnion_finset
    (μ := P) (s := jointPrefixCarrierAvoid W v A N)
    (f := fun xs => ({ω : ℕ → Fin k | ω 0 = j} ∩ cylinder (k := k) (List.ofFn xs))
      ∩ avoidTail A (N + 1))
    ((pairwiseDisjoint_cylinder_ofFn_on_jointPrefixCarrierAvoid W v A N).mono
      (fun xs => Set.inter_subset_left.trans Set.inter_subset_right))
    (fun xs _ => (hS0meas.inter
      (MarkovDeFinettiHard.measurableSet_cylinder (k := k) (List.ofFn xs))).inter
      (measurableSet_avoidTail A (N + 1)))]
  refine Finset.sum_congr rfl fun xs _ => ?_
  by_cases hxs : xs 0 = j
  · rw [if_pos hxs]
    congr 1
    ext ω
    constructor
    · rintro ⟨⟨_, hcyl⟩, htail⟩
      exact ⟨hcyl, htail⟩
    · rintro ⟨hcyl, htail⟩
      have h0 : ω 0 = xs 0 := by
        have hω' := (mem_cylinder_ofFn_iff (k := k) ω N xs).1 hcyl
        simpa using hω' ⟨0, Nat.succ_pos _⟩
      exact ⟨⟨h0.trans hxs, hcyl⟩, htail⟩
  · rw [if_neg hxs]
    have hempty : ({ω : ℕ → Fin k | ω 0 = j} ∩ cylinder (k := k) (List.ofFn xs))
        ∩ avoidTail A (N + 1) = (∅ : Set (ℕ → Fin k)) := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun ω hω => ?_
      have h0 : ω 0 = xs 0 := by
        have hω' := (mem_cylinder_ofFn_iff (k := k) ω N xs).1 hω.1.2
        simpa using hω' ⟨0, Nat.succ_pos _⟩
      exact hxs (h0.symm.trans hω.1.1)
    rw [hempty]
    exact measure_empty

/-- The avoidance carrier only reads the value function on the window cells. -/
lemma jointPrefixCarrierAvoid_congr (W : Fin k → Finset ℕ)
    {v₁ v₂ : Fin k → ℕ → Fin k} (A : Finset (Fin k)) (N : ℕ)
    (h : ∀ i, ∀ n ∈ W i, v₁ i n = v₂ i n) :
    jointPrefixCarrierAvoid W v₁ A N = jointPrefixCarrierAvoid W v₂ A N := by
  ext xs
  rw [mem_jointPrefixCarrierAvoid_iff, mem_jointPrefixCarrierAvoid_iff]
  constructor
  · rintro ⟨hcar, hcnt⟩
    refine ⟨mem_jointPrefixCarrier_iff.mpr fun i n hn => ?_, hcnt⟩
    obtain ⟨t, ht1, ht2, ht3⟩ := mem_jointPrefixCarrier_iff.mp hcar i n hn
    exact ⟨t, ht1, ht2, ht3.trans (h i n hn)⟩
  · rintro ⟨hcar, hcnt⟩
    refine ⟨mem_jointPrefixCarrier_iff.mpr fun i n hn => ?_, hcnt⟩
    obtain ⟨t, ht1, ht2, ht3⟩ := mem_jointPrefixCarrier_iff.mp hcar i n hn
    exact ⟨t, ht1, ht2, ht3.trans (h i n hn).symm⟩

/-- **Per-`N` permutation step with the riding tail.** Row-wise support-bounded
permutations of the visited rows' windows preserve the measure of
start ∩ avoid-forever ∩ truncated joint event. -/
theorem measure_start_inter_avoidTail_inter_biInter_upTo_perm_eq [NeZero k]
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (m : Fin k → ℕ) (σ : Fin k → Equiv.Perm ℕ)
    (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    (v : Fin k → ℕ → Fin k) (T A : Finset (Fin k)) (N : ℕ) (j : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ avoidTail A 0 ∩
        ⋂ i ∈ T, rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i))
          (fun n => v i (σ i n)) N) =
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ avoidTail A 0 ∩
        ⋂ i ∈ T, rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i)) (v i) N) := by
  classical
  have hσT : ∀ i n, (if i ∈ T then m i else 0) - 2 ≤ n →
      (if i ∈ T then σ i else Equiv.refl ℕ) n = n := by
    intro i n hn
    by_cases hi : i ∈ T
    · rw [if_pos hi] at hn ⊢
      exact hσ i n hn
    · rw [if_neg hi]
      rfl
  have hvcongr : ∀ i, ∀ n ∈ Finset.range (if i ∈ T then m i else 0),
      v i (σ i n) = v i ((if i ∈ T then σ i else Equiv.refl ℕ) n) := by
    intro i n hn
    by_cases hi : i ∈ T
    · rw [if_pos hi]
    · rw [if_neg hi] at hn
      simp at hn
  have hwork := sum_cylinderProb_avoidTail_eq_of_rowPerms (k := k) μ hμ P hExt
    (N := N) (fun i => if i ∈ T then m i else 0)
    (fun i => if i ∈ T then σ i else Equiv.refl ℕ) hσT v A j
  rw [start_inter_avoidTail_inter_biInter_upTo_eq m (fun i n => v i (σ i n)) T A N j,
    start_inter_avoidTail_inter_biInter_upTo_eq m v T A N j,
    measure_start_inter_jointAvoid_inter_avoidTail_eq_sum P
      (fun i => Finset.range (if i ∈ T then m i else 0)) (fun i n => v i (σ i n)) A N j,
    measure_start_inter_jointAvoid_inter_avoidTail_eq_sum P
      (fun i => Finset.range (if i ∈ T then m i else 0)) v A N j,
    jointPrefixCarrierAvoid_congr
      (fun i => Finset.range (if i ∈ T then m i else 0)) A N hvcongr]
  exact hwork

/-- **Per-profile permutation equality.** On each visited/never-visited
profile piece, row-wise support-bounded permutations of the successor windows
preserve the start-restricted measure of the un-truncated joint event. -/
theorem measure_start_inter_multiJRE_inter_profile_perm_eq [NeZero k]
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (m : Fin k → ℕ) (σ : Fin k → Equiv.Perm ℕ)
    (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    (v : Fin k → ℕ → Fin k) (C T : Finset (Fin k))
    (hC : ∀ i, i ∉ C → m i = 0) (hT : ∀ i ∈ T, m i ≠ 0) (j : Fin k) :
    P (({ω : ℕ → Fin k | ω 0 = j} ∩ multiJRE (fun i => Finset.range (m i))
          (fun i n => v i (σ i n))) ∩ profileEvent C T) =
      P (({ω : ℕ → Fin k | ω 0 = j} ∩ multiJRE (fun i => Finset.range (m i)) v)
          ∩ profileEvent C T) := by
  classical
  by_cases hgood : ∀ i ∈ C \ T, ∀ n ∈ Finset.range (m i), v i n = i
  · have hgoodσ : ∀ i ∈ C \ T, ∀ n ∈ Finset.range (m i), v i (σ i n) = i :=
      fun i hi => (forall_window_comp_perm_iff m σ hσ v i).mpr (hgood i hi)
    have h1 : ({ω : ℕ → Fin k | ω 0 = j} ∩ multiJRE (fun i => Finset.range (m i))
          (fun i n => v i (σ i n))) ∩ profileEvent C T =
        ({ω : ℕ → Fin k | ω 0 = j} ∩ avoidTail (C \ T) 0) ∩
          ⋂ i ∈ T, (jointRowSuccEvent (k := k) i (Finset.range (m i))
              (fun n => v i (σ i n)) ∩ {ω : ℕ → Fin k | ∃ t, ω t = i}) := by
      rw [Set.inter_assoc, multiJRE_inter_profileEvent_of_good m
        (fun i n => v i (σ i n)) C T hC hgoodσ]
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    have h2 : ({ω : ℕ → Fin k | ω 0 = j} ∩ multiJRE (fun i => Finset.range (m i)) v)
          ∩ profileEvent C T =
        ({ω : ℕ → Fin k | ω 0 = j} ∩ avoidTail (C \ T) 0) ∩
          ⋂ i ∈ T, (jointRowSuccEvent (k := k) i (Finset.range (m i)) (v i)
              ∩ {ω : ℕ → Fin k | ∃ t, ω t = i}) := by
      rw [Set.inter_assoc, multiJRE_inter_profileEvent_of_good m v C T hC hgood]
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    rw [h1, h2,
      measure_inter_biInter_JRE_visited_eq_iUnion_upTo P hStrRec m
        (fun i n => v i (σ i n)) T hT _,
      measure_inter_biInter_JRE_visited_eq_iUnion_upTo P hStrRec m v T hT _,
      biInter_iUnion_upTo_eq_iUnion_biInter m (fun i n => v i (σ i n)) T,
      biInter_iUnion_upTo_eq_iUnion_biInter m v T,
      Set.inter_iUnion, Set.inter_iUnion]
    have hmonoσ : Monotone (fun N =>
        ({ω : ℕ → Fin k | ω 0 = j} ∩ avoidTail (C \ T) 0) ∩
          ⋂ i ∈ T, rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i))
            (fun n => v i (σ i n)) N) := by
      intro N M hNM ω hω
      exact ⟨hω.1, Set.mem_iInter₂.mpr fun i hi =>
        rowVisitCylinderEventUpTo_mono' (k := k) i (Finset.range (m i)) _ hNM
          (Set.mem_iInter₂.mp hω.2 i hi)⟩
    have hmonov : Monotone (fun N =>
        ({ω : ℕ → Fin k | ω 0 = j} ∩ avoidTail (C \ T) 0) ∩
          ⋂ i ∈ T, rowVisitCylinderEventUpTo (k := k) i (Finset.range (m i)) (v i) N) := by
      intro N M hNM ω hω
      exact ⟨hω.1, Set.mem_iInter₂.mpr fun i hi =>
        rowVisitCylinderEventUpTo_mono' (k := k) i (Finset.range (m i)) _ hNM
          (Set.mem_iInter₂.mp hω.2 i hi)⟩
    rw [hmonoσ.measure_iUnion, hmonov.measure_iUnion]
    exact iSup_congr fun N =>
      measure_start_inter_avoidTail_inter_biInter_upTo_perm_eq μ hμ P hExt
        m σ hσ v T (C \ T) N j
  · push Not at hgood
    obtain ⟨i₀, hi₀, n₀, hn₀, hbad⟩ := hgood
    have hsupp : ∀ n, m i₀ ≤ n → σ i₀ n = n := fun n hn => hσ i₀ n (by omega)
    have hn₀' : (σ i₀).symm n₀ < m i₀ :=
      perm_lt_of_support_lt ((σ i₀).symm) (perm_symm_support (σ i₀) hsupp) n₀
        (Finset.mem_range.mp hn₀)
    have hbadσ : v i₀ (σ i₀ ((σ i₀).symm n₀)) ≠ i₀ := by
      rw [Equiv.apply_symm_apply]
      exact hbad
    rw [Set.inter_assoc, Set.inter_assoc,
      multiJRE_inter_profileEvent_eq_empty_of_bad m (fun i n => v i (σ i n)) C T
        i₀ hi₀ ((σ i₀).symm n₀) (Finset.mem_range.mpr hn₀') hbadσ,
      multiJRE_inter_profileEvent_eq_empty_of_bad m v C T i₀ hi₀ n₀ hn₀ hbad]

/-- **The un-truncated joint FDD permutation equality.** Under Markov
exchangeability and strong recurrence, row-wise support-bounded permutations
of the successor windows preserve the start-restricted measure of the
un-truncated multi-row joint successor event. -/
theorem measure_start_inter_multiJRE_perm_eq [NeZero k]
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (m : Fin k → ℕ) (σ : Fin k → Equiv.Perm ℕ)
    (hσ : ∀ i n, m i - 2 ≤ n → σ i n = n)
    (v : Fin k → ℕ → Fin k) (j : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = j} ∩ multiJRE (fun i => Finset.range (m i))
        (fun i n => v i (σ i n))) =
      P ({ω : ℕ → Fin k | ω 0 = j} ∩ multiJRE (fun i => Finset.range (m i)) v) := by
  classical
  have hS0meas : MeasurableSet {ω : ℕ → Fin k | ω 0 = j} := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({j} : Set (Fin k)))
    exact (measurable_pi_apply 0) (MeasurableSet.singleton j)
  have hC : ∀ i, i ∉ Finset.univ.filter (fun i : Fin k => m i ≠ 0) → m i = 0 := by
    intro i hi
    by_contra hne
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
  rw [measure_eq_sum_profile P _ (hS0meas.inter (measurableSet_multiJRE _ _))
      (Finset.univ.filter (fun i : Fin k => m i ≠ 0)),
    measure_eq_sum_profile P _ (hS0meas.inter (measurableSet_multiJRE _ _))
      (Finset.univ.filter (fun i : Fin k => m i ≠ 0))]
  refine Finset.sum_congr rfl fun T hT => ?_
  exact measure_start_inter_multiJRE_inter_profile_perm_eq μ hμ P hExt hStrRec
    m σ hσ v _ T hC
    (fun i hi => (Finset.mem_filter.mp (Finset.mem_powerset.mp hT hi)).2) j

/-! ## The mint: `SuccessorMatrixPE_of_markovExchangeable_strongRecurrence`

De-WLOG chain: replace `σ` by a finite-support permutation family agreeing on
the finitely many read cells; decompose each singleton FDD preimage as a
disjoint union of full-grid `multiJRE` events; transport per grid assignment
by the joint FDD equality, reindexing assignments along `σ`; reassemble via
the start partition and singleton extensionality. -/

/-- Any permutation of `ℕ` agrees with a finite-support permutation on a
given finite set (built by one swap per point). -/
theorem exists_finiteSupport_perm_agree_on (τ : Equiv.Perm ℕ) (S : Finset ℕ) :
    ∃ (τ' : Equiv.Perm ℕ) (L : ℕ),
      (∀ s ∈ S, τ' s = τ s) ∧ (∀ n, L ≤ n → τ' n = n) := by
  classical
  induction S using Finset.induction with
  | empty =>
      exact ⟨1, 0, fun s hs => absurd hs (Finset.notMem_empty s), fun n _ => rfl⟩
  | @insert a S' ha ih =>
      obtain ⟨τ₀, L₀, hagree, hsupp⟩ := ih
      refine ⟨τ₀ * Equiv.swap a (τ₀.symm (τ a)), max L₀ (max a (τ₀.symm (τ a))) + 1,
        ?_, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs'
        · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
          exact τ₀.apply_symm_apply (τ s)
        · have hsa : s ≠ a := fun h => ha (h ▸ hs')
          have hsc : s ≠ τ₀.symm (τ a) := by
            intro h
            have h1 : τ₀ s = τ a := by
              rw [h]
              exact τ₀.apply_symm_apply (τ a)
            have h2 : τ s = τ a := by
              rw [← hagree s hs']
              exact h1
            exact hsa (τ.injective h2)
          simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hsa hsc]
          exact hagree s hs'
      · intro n hn
        have h1 : L₀ ≤ max L₀ (max a (τ₀.symm (τ a))) := le_max_left _ _
        have h2 : a ≤ max a (τ₀.symm (τ a)) := le_max_left _ _
        have h3 : τ₀.symm (τ a) ≤ max a (τ₀.symm (τ a)) := le_max_right _ _
        have h4 : max a (τ₀.symm (τ a)) ≤ max L₀ (max a (τ₀.symm (τ a))) :=
          le_max_right _ _
        have hna : n ≠ a := by omega
        have hnc : n ≠ τ₀.symm (τ a) := by omega
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hna hnc]
        exact hsupp n (by omega)

/-- Row-wise finite-support replacement with a uniform support bound `M`
that also dominates every read index. -/
theorem exists_rowwise_finiteSupport_agree {m' : ℕ} (σ : Fin k → Equiv.Perm ℕ)
    (anchor : Fin m' → Fin k) (idx : Fin m' → ℕ) :
    ∃ (σ' : Fin k → Equiv.Perm ℕ) (M : ℕ),
      (∀ j, σ' (anchor j) (idx j) = σ (anchor j) (idx j)) ∧
      (∀ i n, M - 2 ≤ n → σ' i n = n) ∧ (∀ j, idx j < M - 2) := by
  classical
  have h : ∀ i : Fin k, ∃ (τ' : Equiv.Perm ℕ) (L : ℕ),
      (∀ s ∈ Finset.image idx (Finset.univ.filter fun j => anchor j = i),
        τ' s = (σ i) s) ∧ (∀ n, L ≤ n → τ' n = n) :=
    fun i => exists_finiteSupport_perm_agree_on (σ i) _
  choose σ' L hagree hsupp using h
  refine ⟨σ', (Finset.univ.sup L ⊔ (Finset.univ.sup idx + 1)) + 2, ?_, ?_, ?_⟩
  · intro j
    exact hagree (anchor j) (idx j) (Finset.mem_image.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩, rfl⟩)
  · intro i n hn
    have h1 : L i ≤ Finset.univ.sup L := Finset.le_sup (Finset.mem_univ i)
    have h2 : Finset.univ.sup L ≤ Finset.univ.sup L ⊔ (Finset.univ.sup idx + 1) :=
      le_sup_left
    exact hsupp i n (by omega)
  · intro j
    have h1 : idx j ≤ Finset.univ.sup idx := Finset.le_sup (Finset.mem_univ j)
    have h2 : Finset.univ.sup idx + 1 ≤ Finset.univ.sup L ⊔ (Finset.univ.sup idx + 1) :=
      le_sup_right
    omega

/-- A total grid assignment read as a value function (junk anchor value off
the grid). -/
def gridVal (M : ℕ) (g : Fin k → Fin M → Fin k) : Fin k → ℕ → Fin k :=
  fun i n => if h : n < M then g i ⟨n, h⟩ else i

theorem gridVal_of_lt {M : ℕ} (g : Fin k → Fin M → Fin k) (i : Fin k) {n : ℕ}
    (h : n < M) : gridVal M g i n = g i ⟨n, h⟩ := dif_pos h

/-- Grid assignments consistent with the read constraints. -/
noncomputable def gridCarrier {m' : ℕ} (M : ℕ) (anchor : Fin m' → Fin k)
    (readIdx : Fin m' → ℕ) (c : Fin m' → Fin k) :
    Finset (Fin k → Fin M → Fin k) := by
  classical
  exact Finset.univ.filter
    (fun g => ∀ j, gridVal M g (anchor j) (readIdx j) = c j)

theorem mem_gridCarrier_iff {m' M : ℕ} {anchor : Fin m' → Fin k}
    {readIdx : Fin m' → ℕ} {c : Fin m' → Fin k} {g : Fin k → Fin M → Fin k} :
    g ∈ gridCarrier M anchor readIdx c ↔
      ∀ j, gridVal M g (anchor j) (readIdx j) = c j := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ g, h⟩

/-- The finite selection event decomposes as the union over consistent full
grid assignments (the total function `rowSuccessorAtNthVisit` fills in every
unread cell with exactly one value). -/
lemma biInter_rsp_eq_biUnion_multiJRE {m' M : ℕ} (anchor : Fin m' → Fin k)
    (readIdx : Fin m' → ℕ) (hread : ∀ j, readIdx j < M) (c : Fin m' → Fin k) :
    (⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j) (readIdx j) ω = c j}) =
      ⋃ g ∈ gridCarrier (k := k) M anchor readIdx c,
        multiJRE (fun _ => Finset.range M) (gridVal M g) := by
  ext ω
  constructor
  · intro hω
    have hω' : ∀ j, rowSuccessorAtNthVisit (k := k) (anchor j) (readIdx j) ω = c j :=
      fun j => Set.mem_iInter.mp hω j
    refine Set.mem_iUnion₂.mpr
      ⟨fun i t => rowSuccessorAtNthVisit (k := k) i t.1 ω, ?_, ?_⟩
    · refine mem_gridCarrier_iff.mpr fun j => ?_
      rw [gridVal_of_lt _ _ (hread j)]
      exact hω' j
    · refine Set.mem_iInter.mpr fun i => Set.mem_iInter₂.mpr fun n hn => ?_
      show rowSuccessorAtNthVisit (k := k) i n ω = gridVal M _ i n
      rw [gridVal_of_lt _ _ (Finset.mem_range.mp hn)]
  · intro hω
    rcases Set.mem_iUnion₂.mp hω with ⟨g, hg, hmem⟩
    refine Set.mem_iInter.mpr fun j => ?_
    have h1 : rowSuccessorAtNthVisit (k := k) (anchor j) (readIdx j) ω
        = gridVal M g (anchor j) (readIdx j) :=
      Set.mem_iInter₂.mp (Set.mem_iInter.mp hmem (anchor j)) (readIdx j)
        (Finset.mem_range.mpr (hread j))
    show rowSuccessorAtNthVisit (k := k) (anchor j) (readIdx j) ω = c j
    rw [h1]
    exact mem_gridCarrier_iff.mp hg j

/-- A full-grid `multiJRE` member determines the grid assignment. -/
lemma grid_eq_of_mem_multiJRE {M : ℕ} {g : Fin k → Fin M → Fin k} {ω : ℕ → Fin k}
    (h : ω ∈ multiJRE (fun _ => Finset.range M) (gridVal M g)) (i : Fin k)
    (t : Fin M) : g i t = rowSuccessorAtNthVisit (k := k) i t.1 ω := by
  have h1 : rowSuccessorAtNthVisit (k := k) i t.1 ω = gridVal M g i t.1 :=
    Set.mem_iInter₂.mp (Set.mem_iInter.mp h i) t.1 (Finset.mem_range.mpr t.2)
  rw [gridVal_of_lt _ _ t.2] at h1
  exact h1.symm

/-- Distinct grid assignments give disjoint full-grid events. -/
lemma pairwiseDisjoint_multiJRE_gridVal {m' M : ℕ} (anchor : Fin m' → Fin k)
    (readIdx : Fin m' → ℕ) (c : Fin m' → Fin k) :
    ((↑(gridCarrier (k := k) M anchor readIdx c) :
        Set (Fin k → Fin M → Fin k))).PairwiseDisjoint
      (fun g => multiJRE (fun _ => Finset.range M) (gridVal M g)) := by
  intro g _ g' _ hne
  refine Set.disjoint_left.mpr fun ω hω hω' => hne ?_
  funext i t
  rw [grid_eq_of_mem_multiJRE hω i t, grid_eq_of_mem_multiJRE hω' i t]

/-- Start-restricted sum form of the finite selection event over consistent
grid assignments. -/
lemma measure_start_inter_biInter_rsp_eq_sum (P : Measure (ℕ → Fin k))
    {m' M : ℕ} (anchor : Fin m' → Fin k) (readIdx : Fin m' → ℕ)
    (hread : ∀ j, readIdx j < M) (c : Fin m' → Fin k) (a : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = a} ∩ ⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j) (readIdx j) ω = c j}) =
      Finset.sum (gridCarrier (k := k) M anchor readIdx c)
        (fun g => P ({ω : ℕ → Fin k | ω 0 = a}
          ∩ multiJRE (fun _ => Finset.range M) (gridVal M g))) := by
  have hS0meas : MeasurableSet {ω : ℕ → Fin k | ω 0 = a} := by
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({a} : Set (Fin k)))
    exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
  rw [biInter_rsp_eq_biUnion_multiJRE anchor readIdx hread c, Set.inter_iUnion₂]
  exact measure_biUnion_finset
    (μ := P) (s := gridCarrier (k := k) M anchor readIdx c)
    (f := fun g => {ω : ℕ → Fin k | ω 0 = a}
      ∩ multiJRE (fun _ => Finset.range M) (gridVal M g))
    ((pairwiseDisjoint_multiJRE_gridVal anchor readIdx c).mono
      (fun g => Set.inter_subset_right))
    (fun g _ => hS0meas.inter (measurableSet_multiJRE _ _))

/-- **Per-start finite-selection permutation equality.** Reading each row's
successor process at permuted visit indices does not change the
start-restricted measure of the finite selection event: grid pieces
transport via `measure_start_inter_multiJRE_perm_eq`, assignments reindex
along the permutations. -/
lemma measure_start_inter_biInter_rsp_perm_eq [NeZero k]
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    {m' : ℕ} (anchor : Fin m' → Fin k) (idx : Fin m' → ℕ)
    (σ' : Fin k → Equiv.Perm ℕ) (M : ℕ)
    (hσ' : ∀ i n, M - 2 ≤ n → σ' i n = n) (hidx : ∀ j, idx j < M - 2)
    (c : Fin m' → Fin k) (a : Fin k) :
    P ({ω : ℕ → Fin k | ω 0 = a} ∩ ⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j)
          (σ' (anchor j) (idx j)) ω = c j}) =
      P ({ω : ℕ → Fin k | ω 0 = a} ∩ ⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j) (idx j) ω = c j}) := by
  classical
  have hsuppM : ∀ i, ∀ n, M ≤ n → σ' i n = n := fun i n hn => hσ' i n (by omega)
  have hltM : ∀ (i : Fin k) (t : Fin M), σ' i t.1 < M := fun i t =>
    perm_lt_of_support_lt (σ' i) (hsuppM i) t.1 t.2
  have hltM' : ∀ (i : Fin k) (t : Fin M), (σ' i).symm t.1 < M := fun i t =>
    perm_lt_of_support_lt ((σ' i).symm) (perm_symm_support (σ' i) (hsuppM i)) t.1 t.2
  have hreadσ : ∀ j, σ' (anchor j) (idx j) < M := fun j => by
    have h1 : σ' (anchor j) (idx j) < M - 2 :=
      perm_lt_of_support_lt (σ' (anchor j)) (hσ' (anchor j)) (idx j) (hidx j)
    omega
  have hread : ∀ j, idx j < M := fun j => by
    have := hidx j
    omega
  rw [measure_start_inter_biInter_rsp_eq_sum P anchor
      (fun j => σ' (anchor j) (idx j)) hreadσ c a,
    measure_start_inter_biInter_rsp_eq_sum P anchor idx hread c a]
  refine Finset.sum_bij' (fun g _ => fun i t => g i ⟨σ' i t.1, hltM i t⟩)
    (fun g _ => fun i t => g i ⟨(σ' i).symm t.1, hltM' i t⟩) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro g hg
    refine mem_gridCarrier_iff.mpr fun j => ?_
    rw [gridVal_of_lt _ _ (hread j)]
    have h1 := mem_gridCarrier_iff.mp hg j
    rw [gridVal_of_lt _ _ (hreadσ j)] at h1
    exact h1
  · -- backward membership
    intro g hg
    refine mem_gridCarrier_iff.mpr fun j => ?_
    rw [gridVal_of_lt _ _ (hreadσ j)]
    have h1 := mem_gridCarrier_iff.mp hg j
    rw [gridVal_of_lt _ _ (hread j)] at h1
    calc g (anchor j) ⟨(σ' (anchor j)).symm (σ' (anchor j) (idx j)),
          hltM' (anchor j) ⟨σ' (anchor j) (idx j), hreadσ j⟩⟩
        = g (anchor j) ⟨idx j, hread j⟩ := by
          congr 1
          exact Fin.ext (Equiv.symm_apply_apply (σ' (anchor j)) (idx j))
      _ = c j := h1
  · -- left inverse
    intro g _
    funext i t
    show g i ⟨σ' i ((σ' i).symm t.1), _⟩ = g i t
    congr 1
    exact Fin.ext (Equiv.apply_symm_apply (σ' i) t.1)
  · -- right inverse
    intro g _
    funext i t
    show g i ⟨(σ' i).symm (σ' i t.1), _⟩ = g i t
    congr 1
    exact Fin.ext (Equiv.symm_apply_apply (σ' i) t.1)
  · -- per-term equality
    intro g hg
    have hcomp : (fun i n => gridVal M g i (σ' i n))
        = gridVal M (fun i t => g i ⟨σ' i t.1, hltM i t⟩) := by
      funext i n
      by_cases hn : n < M
      · rw [gridVal_of_lt _ _ (hltM i ⟨n, hn⟩), gridVal_of_lt _ _ hn]
      · have hfix : σ' i n = n := hsuppM i n (by omega)
        rw [hfix, gridVal, gridVal]
        simp only [dif_neg hn]
    have hkey := measure_start_inter_multiJRE_perm_eq μ hμ P hExt hStrRec
      (fun _ => M) σ' (fun i n hn => hσ' i n hn) (gridVal M g) a
    rw [hcomp] at hkey
    exact hkey.symm

/-- Partition of an event's measure over the start symbol. -/
lemma measure_eq_sum_start_inter (P : Measure (ℕ → Fin k))
    (E : Set (ℕ → Fin k)) (hE : MeasurableSet E) :
    P E = ∑ a : Fin k, P ({ω : ℕ → Fin k | ω 0 = a} ∩ E) := by
  classical
  let fiber : Fin k → Set (ℕ → Fin k) :=
    fun a => (fun ω : ℕ → Fin k => ω 0) ⁻¹' {a} ∩ E
  have hcover : E = ⋃ a : Fin k, fiber a := by
    ext ω
    simp only [fiber, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨ω 0, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  have hdisj : Pairwise (Function.onFun Disjoint fiber) := by
    intro a b hab
    exact Set.disjoint_left.mpr fun ω ⟨ha, _⟩ ⟨hb, _⟩ =>
      hab (by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
        exact ha ▸ hb)
  have hmeas : ∀ a, MeasurableSet (fiber a) :=
    fun a => (measurable_pi_apply 0 (measurableSet_singleton a)).inter hE
  have hfiber_eq : ∀ a, P (fiber a) = P ({ω : ℕ → Fin k | ω 0 = a} ∩ E) := by
    intro a
    congr 1
  rw [hcover, measure_iUnion hdisj hmeas]
  simp_rw [hfiber_eq, ← hcover]
  exact tsum_fintype _

/-- **Joint successor-matrix partial exchangeability** under Markov
exchangeability and strong recurrence (FLPR Theorem 1, 'if' direction). -/
theorem successorMatrixPartialExchangeable_of_markovExchangeable_strongRecurrence
    [NeZero k]
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P) :
    SuccessorMatrixPartialExchangeable (k := k) P := by
  intro m' anchor idx σ
  obtain ⟨σ', M, hagree, hsupp, hidxM⟩ :=
    exists_rowwise_finiteSupport_agree σ anchor idx
  have hmapEq : (fun ω : ℕ → Fin k => fun j : Fin m' =>
      rowSuccessorVisitProcess (k := k) (anchor j) ω ((σ (anchor j)) (idx j))) =
    (fun ω : ℕ → Fin k => fun j : Fin m' =>
      rowSuccessorVisitProcess (k := k) (anchor j) ω (σ' (anchor j) (idx j))) := by
    funext ω j
    rw [hagree j]
  rw [hmapEq]
  have hmeas_rsp : ∀ i : Fin k,
      Measurable (rowSuccessorVisitProcess (k := k) i) :=
    fun i => measurable_rowSuccessorVisitProcess (k := k) i
  have hf : Measurable (fun ω : ℕ → Fin k => fun j : Fin m' =>
      rowSuccessorVisitProcess (k := k) (anchor j) ω (σ' (anchor j) (idx j))) := by
    apply measurable_pi_lambda
    intro j
    show Measurable (fun ω : ℕ → Fin k =>
      rowSuccessorVisitProcess (k := k) (anchor j) ω (σ' (anchor j) (idx j)))
    exact (measurable_pi_apply (σ' (anchor j) (idx j))).comp (hmeas_rsp (anchor j))
  have hg : Measurable (fun ω : ℕ → Fin k => fun j : Fin m' =>
      rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j)) := by
    apply measurable_pi_lambda
    intro j
    show Measurable (fun ω : ℕ → Fin k =>
      rowSuccessorVisitProcess (k := k) (anchor j) ω (idx j))
    exact (measurable_pi_apply (idx j)).comp (hmeas_rsp (anchor j))
  apply MeasureTheory.Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply hf (measurableSet_singleton c),
    Measure.map_apply hg (measurableSet_singleton c)]
  have hpre : ∀ readIdx : Fin m' → ℕ,
      ((fun ω : ℕ → Fin k => fun j : Fin m' =>
        rowSuccessorVisitProcess (k := k) (anchor j) ω (readIdx j)) ⁻¹' {c}) =
      ⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j) (readIdx j) ω = c j} := by
    intro readIdx
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
      Set.mem_setOf_eq, funext_iff]
    exact Iff.rfl
  rw [hpre (fun j => σ' (anchor j) (idx j)), hpre idx]
  have hmeasE : ∀ readIdx : Fin m' → ℕ,
      MeasurableSet (⋂ j : Fin m', {ω : ℕ → Fin k |
        rowSuccessorAtNthVisit (k := k) (anchor j) (readIdx j) ω = c j}) :=
    fun readIdx => MeasurableSet.iInter fun j =>
      measurableSet_rowSuccessorValueEvent (k := k) (anchor j) (readIdx j) (c j)
  rw [measure_eq_sum_start_inter P _ (hmeasE (fun j => σ' (anchor j) (idx j))),
    measure_eq_sum_start_inter P _ (hmeasE idx)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact measure_start_inter_biInter_rsp_perm_eq μ hμ P hExt hStrRec
    anchor idx σ' M hsupp hidxM c a

/-- **The mint (G1).** Markov exchangeability plus a strongly recurrent
extension yield successor-matrix partial exchangeability, for every alphabet
size (`k = 0` is vacuous: the empty path space carries no probability
measure). -/
theorem successorMatrixPE_of_markovExchangeable_strongRecurrence_holds (k : ℕ) :
    SuccessorMatrixPE_of_markovExchangeable_strongRecurrence k := by
  intro μ P hP hμ hExt hStrRec
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exfalso
    haveI : IsEmpty (ℕ → Fin 0) := ⟨fun f => (f 0).elim0⟩
    have h1 : P Set.univ = 1 := hP.measure_univ
    rw [Set.univ_eq_empty_iff.mpr inferInstance, measure_empty] at h1
    exact zero_ne_one h1
  · haveI : NeZero k := NeZero.of_pos hk
    haveI : IsProbabilityMeasure P := hP
    exact successorMatrixPartialExchangeable_of_markovExchangeable_strongRecurrence
      μ hμ P hExt hStrRec

end Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiSuccessorArrayPE
