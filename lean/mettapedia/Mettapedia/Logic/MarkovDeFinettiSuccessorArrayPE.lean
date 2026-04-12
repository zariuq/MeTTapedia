import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCrux
import Mettapedia.Logic.MarkovDeFinettiPEBridge
import Mettapedia.Logic.MarkovDeFinettiHardEulerTrailFiber
import Mettapedia.Logic.MarkovDeFinettiHardCopyPerm

/-!
# Successor-Array / Euler Translation Scratchpad

-- LLM primer: This file records finite successor-array / Euler-trail
-- translation lemmas that survived the earlier PE route exploration.
-- The active plan is no longer "prove SuccessorMatrixPartialExchangeable by
-- multi-row permutation counting". The useful content here is supporting
-- substrate for direct conditioned-prefix counting on fixed evidence fibers.
--
-- STATUS: Sections A-B and the row-multiset lemma in Section C are proved.
-- The file now stops at an honest sound frontier: the naive transCount-
-- preservation route was removed because it appears false for the current
-- `prefixExtend`-based successor-array encoding. Permuting the full row array
-- can move the distinguished "last-exit" edge and change the actual path.
--
-- Strategy note: within an evidence class, a trajectory is uniquely determined
-- by (start state, successor array), but raw multi-row permutations do NOT in
-- general preserve finite evidence. The honest surviving use of this file is
-- to relate fixed finite query sets to the Euler-trail model, not to advertise
-- a complete PE proof route.
--
-- Section A: finSuccArray extraction
-- Section B: finSuccArray_determines_prefix (PROVED)
-- Section C: Reconstruction infrastructure + row multiset lemma
-- Section D: Multi-row carrier + honest consumer measure theorem
-/

noncomputable section

namespace Mettapedia.Logic

open MarkovDeFinettiHard
open MarkovDeFinettiRecurrence
open MeasureTheory Finset
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovExchangeability
open PerRowJointPE
open MarkovDeFinettiHardBESTCore
open MarkovDeFinettiHardEulerTrails
open MarkovDeFinettiHardEulerTrailFiber
open MarkovDeFinettiHardCopyPerm

variable {k : ℕ}

/-! ## Section A: Finite Prefix Successor Array Infrastructure -/

-- finReconstructPrefix: deferred to Section C (needs careful Fin.snoc handling)

/-- Extract the successor array from a finite prefix. For state `i` and visit
index `n`, returns the successor at the `n`-th visit to `i` (or `i` as default). -/
def finSuccArray (xs : Fin (N + 1) → Fin k) (i : Fin k) (n : ℕ) : Fin k :=
  rowSuccessorAtNthVisit (k := k) i n (prefixExtend (k := k) N xs)

/-! ## Section B: Injectivity and Evidence Preservation -/

/-- Visit count agreement: if two prefixes agree up to position `t`, their
visit counts to any state at time `t` agree. -/
theorem visitCountBefore_eq_of_prefix_agree
    (ω₁ ω₂ : ℕ → Fin k) (i : Fin k) (t : ℕ)
    (hagree : ∀ m, m < t → ω₁ m = ω₂ m) :
    visitCountBefore (k := k) ω₁ i t = visitCountBefore (k := k) ω₂ i t := by
  simp only [visitCountBefore]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [hagree m (Finset.mem_range.mp hm)]

/-- Successor array extraction is injective: if two prefixes have the same start
state and the same successor array, they are identical.

Proof by induction on position: at each step, same state (IH) → same visit count
→ same array value → same next state. -/
theorem finSuccArray_determines_prefix
    {N : ℕ} (xs₁ xs₂ : Fin (N + 1) → Fin k)
    (hstart : xs₁ ⟨0, Nat.zero_lt_succ N⟩ = xs₂ ⟨0, Nat.zero_lt_succ N⟩)
    (harray : ∀ i : Fin k, ∀ n : ℕ,
      finSuccArray (k := k) xs₁ i n = finSuccArray (k := k) xs₂ i n) :
    xs₁ = xs₂ := by
  -- Prove ∀ t < N+1, xs₁(t) = xs₂(t) by strong induction
  suffices h : ∀ t (ht : t < N + 1), xs₁ ⟨t, ht⟩ = xs₂ ⟨t, ht⟩ by
    funext ⟨t, ht⟩; exact h t ht
  intro t; induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    match t, ih with
    | 0, _ => exact hstart
    | t + 1, ih =>
    have ht_lt : t < N + 1 := by omega
    have hagree : ∀ m (hm_lt : m < N + 1), m ≤ t →
        xs₁ ⟨m, hm_lt⟩ = xs₂ ⟨m, hm_lt⟩ := by
      intro m hm_lt hm; exact ih m (by omega) hm_lt
    have hstate : xs₁ ⟨t, ht_lt⟩ = xs₂ ⟨t, ht_lt⟩ := hagree t ht_lt le_rfl
    -- prefixExtend agrees on [0, t]
    have hext_agree : ∀ m, m < t + 1 →
        prefixExtend (k := k) N xs₁ m = prefixExtend (k := k) N xs₂ m := by
      intro m hm
      simp only [prefixExtend]
      have hm_le : m ≤ N := by omega
      simp [hm_le]
      exact hagree m (by omega) (by omega)
    -- Visit count at time t agrees
    let i := xs₁ ⟨t, ht_lt⟩
    have hvc : visitCountBefore (k := k) (prefixExtend (k := k) N xs₁) i t =
        visitCountBefore (k := k) (prefixExtend (k := k) N xs₂) i t := by
      exact visitCountBefore_eq_of_prefix_agree
        (prefixExtend (k := k) N xs₁)
        (prefixExtend (k := k) N xs₂) i t
        (fun m hm => hext_agree m (Nat.lt_succ_of_lt hm))
    -- nthVisitTime at the visit count gives time t for both
    -- xs₁(t+1) = finSuccArray(xs₁, xs₁(t), vc) = finSuccArray(xs₂, xs₂(t), vc) = xs₂(t+1)
    -- via the array equality hypothesis
    -- We use: prefixExtend(N, xs)(t) = xs(t) for t ≤ N, and successorAt(ω, t) = ω(t+1)
    -- Key: xs(t+1) = finSuccArray(xs, xs(t), visitCount(..., xs(t), t))
    -- nthVisitTime_eq_some_iff: nthVisitTime ω i n = some t ↔ ω t = i ∧ visitCount ω i t = n
    have hsucc_eq (xs : Fin (N + 1) → Fin k) (ht' : t + 1 < N + 1) (ht_lt' : t < N + 1)
        (hpe : prefixExtend (k := k) N xs t = xs ⟨t, ht_lt'⟩) :
        xs ⟨t + 1, ht'⟩ = finSuccArray (k := k) xs (xs ⟨t, ht_lt'⟩)
          (visitCountBefore (k := k) (prefixExtend (k := k) N xs) (xs ⟨t, ht_lt'⟩) t) := by
      simp only [finSuccArray, rowSuccessorAtNthVisit]
      have hnt : nthVisitTime (k := k) (prefixExtend (k := k) N xs) (xs ⟨t, ht_lt'⟩)
          (visitCountBefore (k := k) (prefixExtend (k := k) N xs) (xs ⟨t, ht_lt'⟩) t) =
            some t := by
        rw [nthVisitTime_eq_some_iff]
        exact ⟨hpe, rfl⟩
      rw [hnt]
      simp [successorAt, prefixExtend, Nat.le_of_lt_succ ht']
    have hpe_eq (xs : Fin (N + 1) → Fin k) (ht_lt' : t < N + 1) :
        prefixExtend (k := k) N xs t = xs ⟨t, ht_lt'⟩ := by
      simp [prefixExtend, Nat.le_of_lt_succ ht_lt']
    have hsucc1 := hsucc_eq xs₁ ht ht_lt (hpe_eq xs₁ ht_lt)
    have hsucc2 := hsucc_eq xs₂ ht ht_lt (hpe_eq xs₂ ht_lt)
    rw [hsucc1, hsucc2, hstate]
    -- Goal: finSuccArray xs₁ (xs₂ ⟨t,_⟩) (vc₁) = finSuccArray xs₂ (xs₂ ⟨t,_⟩) (vc₂)
    -- where vc₁ uses prefixExtend of xs₁ and vc₂ uses prefixExtend of xs₂
    -- hvc : vc₁(for i = xs₁⟨t⟩) = vc₂(for i = xs₁⟨t⟩)
    -- but now i = xs₂⟨t⟩ after the rewrite. Since hstate : xs₁⟨t⟩ = xs₂⟨t⟩,
    -- hvc still applies (after unfolding i).
    change finSuccArray (k := k) xs₁ (xs₂ ⟨t, ht_lt⟩)
        (visitCountBefore (k := k) (prefixExtend (k := k) N xs₁) (xs₂ ⟨t, ht_lt⟩) t) =
      finSuccArray (k := k) xs₂ (xs₂ ⟨t, ht_lt⟩)
        (visitCountBefore (k := k) (prefixExtend (k := k) N xs₂) (xs₂ ⟨t, ht_lt⟩) t)
    have hvc' : visitCountBefore (k := k) (prefixExtend (k := k) N xs₁) (xs₂ ⟨t, ht_lt⟩) t =
        visitCountBefore (k := k) (prefixExtend (k := k) N xs₂) (xs₂ ⟨t, ht_lt⟩) t := by
      rw [← hstate]; exact hvc
    rw [hvc']
    exact harray _ _

/-! ## Section C: Reconstruction and Evidence-Class Bijection

The counting argument needs: for any per-row permutation σ of the successor array,
the map xs ↦ reconstruct(xs.start, σ · extract(xs)) is a bijection on evidence
classes. We prove this via:
1. Reconstruction definition
2. Extract-after-reconstruct = permuted array (partial round-trip)
3. Evidence preservation under array permutation
4. Injectivity on evidence classes (from finSuccArray_determines_prefix)
5. Injective + finite → bijective -/

/-- Reconstruct a trajectory from a start state and successor array.
Builds both the trajectory and per-state visit counts simultaneously.
Returns `(state_at_t, visit_counts_at_t)`. -/
def finReconstructAux (s₀ : Fin k) (A : Fin k → ℕ → Fin k) :
    (t : ℕ) → Fin k × (Fin k → ℕ)
  | 0 => (s₀, fun _ => 0)
  | t + 1 =>
    let (cur, vc) := finReconstructAux s₀ A t
    let next := A cur (vc cur)
    (next, fun i => vc i + if cur = i then 1 else 0)

/-- The reconstructed state at time `t`. -/
def finReconstructAt (s₀ : Fin k) (A : Fin k → ℕ → Fin k) (t : ℕ) : Fin k :=
  (finReconstructAux (k := k) s₀ A t).1

/-- Package the reconstruction as a `Fin (N+1) → Fin k` prefix. -/
def finReconstructPrefix (s₀ : Fin k) (A : Fin k → ℕ → Fin k) (N : ℕ) :
    Fin (N + 1) → Fin k :=
  fun ⟨t, _⟩ => finReconstructAt (k := k) s₀ A t

/-- Reconstruction starts at `s₀`. -/
theorem finReconstructPrefix_zero_eq (s₀ : Fin k) (A : Fin k → ℕ → Fin k) (N : ℕ) :
    finReconstructPrefix (k := k) s₀ A N ⟨0, Nat.zero_lt_succ N⟩ = s₀ := by
  simp [finReconstructPrefix, finReconstructAt, finReconstructAux]

/-- Per-row permutation of a successor array. -/
def permuteSuccArray (A : Fin k → ℕ → Fin k) (σ : Fin k → Equiv.Perm ℕ) :
    Fin k → ℕ → Fin k :=
  fun i n => A i (σ i n)

/-- The visit count tracked by `finReconstructAux` after `t` steps. -/
def finReconstructVC (s₀ : Fin k) (A : Fin k → ℕ → Fin k) (t : ℕ) : Fin k → ℕ :=
  (finReconstructAux (k := k) s₀ A t).2

/-- Sublemma 1: Reconstruction visit-count invariant.
After t steps, the visit count tracked by `finReconstructAux` equals the number
of times each state has been visited in positions [0, t). -/
theorem finReconstructVC_eq_count (s₀ : Fin k) (A : Fin k → ℕ → Fin k) (i : Fin k) :
    ∀ t, finReconstructVC (k := k) s₀ A t i =
      (Finset.range t).sum (fun s => if finReconstructAt (k := k) s₀ A s = i then 1 else 0) := by
  intro t; induction t with
  | zero => simp [finReconstructVC, finReconstructAux]
  | succ t ih =>
    -- Unfold all wrapper definitions to raw finReconstructAux
    unfold finReconstructVC finReconstructAt at ih
    unfold finReconstructVC finReconstructAt
    simp only [finReconstructAux, Finset.sum_range_succ]
    linarith

/-- Sublemma 2: Row multiset invariant.
For each row i, the first V_i entries read by the σ-permuted reconstruction
form a permutation of the first V_i entries of the original array.

Specifically: if the reconstruction visits state i exactly V_i times (same as
the original), then the multiset of successor values {A(i,σ_i(0)),...,A(i,σ_i(V_i-1))}
equals the multiset {A(i,0),...,A(i,V_i-1)}, because σ_i permutes [0,V_i). -/
theorem multiset_permuted_entries_eq
    (A : Fin k → ℕ → Fin k) (σ : Fin k → Equiv.Perm ℕ) (i : Fin k)
    (V : ℕ)
    (hσ : ∀ n, n < V → σ i n < V) :
    Multiset.map (fun n => A i ((σ i) n)) (Multiset.range V) =
    Multiset.map (fun n => A i n) (Multiset.range V) := by
  classical
  let f : Fin V → Fin V := fun n => ⟨σ i n, hσ n n.2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    exact (σ i).injective (congrArg Fin.val hab)
  let σV : Equiv.Perm (Fin V) :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, rfl⟩)
  have hnodup : (Multiset.range V).Nodup := by
    simpa using (List.nodup_range : List.Nodup (List.range V))
  refine Multiset.map_eq_map_of_bij_of_nodup
    (f := fun n => A i ((σ i) n))
    (g := fun n => A i n)
    hnodup hnodup
    (i := fun a _ha => σ i a)
    ?_ ?_ ?_ ?_
  · intro a ha
    simpa [Multiset.mem_range] using hσ a (by simpa [Multiset.mem_range] using ha)
  · intro a₁ _ha₁ a₂ _ha₂ hEq
    exact (σ i).injective hEq
  · intro b hb
    have hb_lt : b < V := by
      simpa [Multiset.mem_range] using hb
    have hsurj : Function.Surjective f := by
      exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, rfl⟩ |>.2
    rcases hsurj ⟨b, hb_lt⟩ with ⟨a, ha⟩
    refine ⟨a, ?_, congrArg Fin.val ha⟩
    rw [Multiset.mem_range]
    exact a.2
  · intro a _ha
    rfl

/-! ### Sound stopping point for the naive successor-array route

The next natural theorem after `multiset_permuted_entries_eq` would claim that
reconstructing from a row-wise permuted successor array preserves finite
transition counts, hence evidence, hence evidence-class cardinalities. That
claim is false for the current `prefixExtend`-based encoding: the full row array
contains a distinguished last-exit edge, and moving it can change the actual
finite path rather than merely reordering independent row data.

Positive example:
- `multiset_permuted_entries_eq` is still correct. If we keep a row's read range
  fixed and permute entries inside that range, the row's successor multiset is
  unchanged.

Negative example:
- For the word `[0, 0, 1]`, swapping the two outgoing row-`0` entries changes
  the reconstructed prefix to `[0, 1, 0]`, so the global transition counts
  change. This breaks naive evidence preservation.

So this file intentionally stops before any theorem asserting:
- transition-count preservation under `permuteSuccArray`
- evidence preservation for the reconstructed prefix
- carrier equivalences built from that false preservation claim

Any corrected counting route must refine the data beyond raw row successor
arrays, for example by keeping the Euler-trail / last-exit structure explicit.
-/

/-! ## Section D: Multi-Row Carrier Equivalence

The key assembly step: define the multi-row prefix carrier (trajectories satisfying
ALL row constraints), build the evidence-preserving equivalence using the
reconstruction map, and derive measure equality. -/

/-- Multi-row prefix carrier: the set of length-(N+1) finite prefixes whose
infinite extension satisfies ALL row-successor constraints. -/
def multiRowPrefixCarrier
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (vals : Fin m → Fin k)
    (N : ℕ) : Finset (Fin (N + 1) → Fin k) := by
  classical
  exact (Finset.univ : Finset (Fin (N + 1) → Fin k)).filter fun xs =>
    ∀ j : Fin m, rowSuccessorAtNthVisit (k := k) (anchor j) (idx j)
      (prefixExtend (k := k) N xs) = vals j

/-! The corresponding carrier-equivalence theorem is intentionally omitted here.
It would rely on the false transition-count/evidence-preservation claim above.
The honest consumer theorem below is still useful: if an evidence-preserving
equivalence is supplied from some other sound route, the finite measure equality
follows immediately. -/

/-- Finite measure equality for multi-row events.
Combines the carrier equivalence with Markov exchangeability to get
measure equality for finite multi-row successor constraints.

The statement mirrors `measure_start_inter_rowVisitCylinderEventUpTo_eq_of_evidencePreservingEquiv_start`
(Core:1229) but for multi-row events: both truncated multi-row events have the
same measure under P, conditioned on start state. -/
theorem measure_start_inter_multiRowEventUpTo_perm_eq
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (m : ℕ) (anchor : Fin m → Fin k) (idx : Fin m → ℕ) (vals : Fin m → Fin k)
    (σ : Fin k → Equiv.Perm ℕ) (N : ℕ) (j : Fin k)
    (_hσ : ∀ (xs : Fin (N + 1) → Fin k),
      xs ∈ multiRowPrefixCarrier (k := k) m anchor idx vals N →
      ∀ i : Fin k, ∀ n : ℕ,
        n < visitCountBefore (k := k) (prefixExtend (k := k) N xs) i (N + 1) →
        σ i n < visitCountBefore (k := k) (prefixExtend (k := k) N xs) i (N + 1))
    (hequiv : ∃ (e : multiRowPrefixCarrier (k := k) m anchor
                        (fun j' => (σ (anchor j')) (idx j')) vals N ≃
                      multiRowPrefixCarrier (k := k) m anchor idx vals N),
                ∀ xs, MarkovExchangeability.evidenceOf (n := N) xs.1 =
                      MarkovExchangeability.evidenceOf (n := N) (e xs).1) :
    Finset.sum (multiRowPrefixCarrier (k := k) m anchor
                  (fun j' => (σ (anchor j')) (idx j')) vals N)
        (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) =
    Finset.sum (multiRowPrefixCarrier (k := k) m anchor idx vals N)
        (fun xs => if xs 0 = j then P (cylinder (k := k) (List.ofFn xs)) else 0) := by
  -- Follows from the carrier equivalence + Markov exchangeability
  -- via sum_cylinderProb_eq_of_extension_and_evidencePreservingEquiv_start
  rcases hequiv with ⟨e, he⟩
  exact sum_cylinderProb_eq_of_extension_and_evidencePreservingEquiv_start
    (k := k) μ hμ P hExt _ _ e he j

/-! ### Word-query fibers in the Euler-trail picture

These are finite Route C translation lemmas: the mixed-row fixed-complement
query on a finite evidence fiber can be viewed on the Euler trails of the
associated multigraph.  They are support lemmas for direct finite counting, not
evidence that the multi-row PE route itself will close. -/

/-- Cast the vertex sequence of an Euler trail on `graphOfState eN` to a
trajectory of length `ys.length`, using that `eN` is realized at that horizon. -/
def wordTupleEulerTraj
    (ys : List (Fin k)) (eN : MarkovState k) (heN : eN ∈ stateFinset k ys.length)
    (f : Fin (totalEdgeTokens (graphOfState (k := k) eN)) →
      edgeTok (graphOfState (k := k) eN)) :
    Traj k ys.length :=
  castTraj
    (G := graphOfState (k := k) eN)
    (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset
      (k := k) (N := ys.length) heN)
    (trailVertexSeq (graphOfState (k := k) eN) eN.start f)

/-- The casted Euler-trail trajectory has evidence state `eN`. -/
lemma stateOfTraj_wordTupleEulerTraj
    (ys : List (Fin k)) (eN : MarkovState k) (heN : eN ∈ stateFinset k ys.length)
    (f : Fin (totalEdgeTokens (graphOfState (k := k) eN)) →
      edgeTok (graphOfState (k := k) eN))
    (hf : IsEulerTrail (graphOfState (k := k) eN) eN.start eN.last f) :
    stateOfTraj (k := k) (wordTupleEulerTraj (k := k) ys eN heN f) = eN := by
  rw [wordTupleEulerTraj]
  rw [stateOfTraj_castTraj]
  exact stateOfTraj_trailVertexSeq (k := k) eN f hf

/-- The mixed-row fixed-complement query viewed on Euler trails of the graph
attached to `eN`. -/
def wordTupleFixedComplementEulerTrailSubset
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (eN : MarkovState k) (heN : eN ∈ stateFinset k ys.length) :
    Finset
      (Fin (totalEdgeTokens (graphOfState (k := k) eN)) →
        edgeTok (graphOfState (k := k) eN)) := by
  classical
  exact
    (eulerTrailFinset (graphOfState (k := k) eN) eN.start eN.last).filter fun f =>
      wordSuccessorTuplePrefixMap (k := k) a ys
          (wordTupleEulerTraj (k := k) ys eN heN f) ∈
        wordTupleFixedComplementSet (k := k) a ys i c

lemma mem_wordTupleFixedComplementEulerTrailSubset_iff
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (eN : MarkovState k) (heN : eN ∈ stateFinset k ys.length)
    (f : Fin (totalEdgeTokens (graphOfState (k := k) eN)) →
      edgeTok (graphOfState (k := k) eN)) :
    f ∈ wordTupleFixedComplementEulerTrailSubset (k := k) a ys i c eN heN ↔
      IsEulerTrail (graphOfState (k := k) eN) eN.start eN.last f ∧
        wordSuccessorTuplePrefixMap (k := k) a ys
          (wordTupleEulerTraj (k := k) ys eN heN f) ∈
            wordTupleFixedComplementSet (k := k) a ys i c := by
  classical
  simp [wordTupleFixedComplementEulerTrailSubset]

/-- A trail satisfying the Euler-side mixed-row query produces a trajectory in
the corresponding evidence-fiber subset. -/
lemma wordTupleEulerTraj_mem_wordTupleFixedComplementFiberSubset_of_mem
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (eN : MarkovState k) (heN : eN ∈ stateFinset k ys.length)
    {f : Fin (totalEdgeTokens (graphOfState (k := k) eN)) →
      edgeTok (graphOfState (k := k) eN)}
    (hf :
      f ∈ wordTupleFixedComplementEulerTrailSubset (k := k) a ys i c eN heN) :
    wordTupleEulerTraj (k := k) ys eN heN f ∈
      wordTupleFixedComplementFiberSubset (k := k) a ys i c eN := by
  rcases (mem_wordTupleFixedComplementEulerTrailSubset_iff
      a ys i c eN heN f).1 hf with ⟨hfTrail, hquery⟩
  rw [mem_wordTupleFixedComplementFiberSubset_iff]
  refine ⟨?_, hquery⟩
  exact Finset.mem_filter.mpr
    ⟨by simp [trajFinset],
      stateOfTraj_wordTupleEulerTraj (k := k) ys eN heN f hfTrail⟩

/-! ## Section E: Honest stopping point

No PE lift is claimed here.

The active downstream route is the direct conditioned-prefix counting path in
`MarkovDeFinettiFiberEventBridge` and `MarkovDeFinettiHardCopyPerm`: count exact
prefix events inside one evidence fiber, convert them to filtered Euler-trail
counts, and then pass to conditional-probability / tail limits. -/

end Mettapedia.Logic
