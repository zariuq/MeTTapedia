import Mathlib.Tactic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Exchangeability.ConditionallyIID
import Exchangeability.DeFinetti.ViaMartingale.DirectingMeasure
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence
import Mettapedia.Logic.MarkovDeFinettiEvidenceBasis
import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCrux
import Mettapedia.Logic.MarkovDeFinettiHardCopyPerm
import Mettapedia.Logic.MarkovDeFinettiKernelUniqueness
import Mettapedia.Logic.MarkovDeFinettiPEBridge

/-! LLM primer:
- This file bridges the finite evidence-fiber layer (EvidenceBasis) with the
  finite word/prefix events needed for the direct conditioned-prefix counting route.
- Key definition: `fiberWordConstraintSubset` — the finite subset of an evidence
  fiber consisting of trajectories whose first |w| positions satisfy a given
  word-tuple fixed-complement constraint.
- This is the finite Route C substrate that connects exact evidence-fiber events
  to Euler-trail counting via `HardCopyPerm:443`. The active downstream goal is
  direct conditioned-prefix counting, not a multi-row permutation proof of PE.

# Connection overview

For word w = a :: ys of length m:
- Finite-fiber subset: {xs ∈ fiber(N,e) | xs(0)=a ∧ xs(j+1) matches constraint for j < |ys|}
- Prefix-conditioned special case: exact word-prefix matching inside a fixed fiber
- Cylinder measure / finite conditional probability are recovered from these
  finite counts by Markov exchangeability and exact Euler-trail cardinality.
- In particular, for fixed evidence `e`, prefix probabilities reduce to exact
  cardinality ratios on `fiber k N e` or equivalently on `eulerTrailFinset`.
- Markov-exchangeable mass on such a subset is
  = Σ_e |{xs ∈ fiberWordConstraintSubset}| * μ(any xs in fiber(e))
  by Markov exchangeability (sum_mu_eq_card_mul_of_subset_fiber).
-/

noncomputable section

namespace Mettapedia.Logic.MarkovDeFinettiHard

open MeasureTheory
open MarkovDeFinettiRecurrence
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovExchangeability
open Exchangeability.DeFinetti.ViaMartingale
open Mettapedia.Logic.PerRowJointPE
open Mettapedia.Logic.MarkovDeFinettiHardBESTCore
open Mettapedia.Logic.MarkovDeFinettiHardEulerTrails
open Mettapedia.Logic.MarkovDeFinettiHardCopyPerm

variable {k : ℕ}

/-! ## Section 1: Core Definition

The finite subset of an evidence fiber at horizon N that corresponds to the
`wordTupleFixedComplementSet` event.

For a word a :: ys and row i with fiber assignment c:
- At positions j where the word visits state i: trajectory has xs(j+1) = c(t)
- At positions j where the word visits state ≠ i: trajectory has xs(j+1) = ys[j]
- Start: xs(0) = a -/

/-- Finite subset of evidence fiber where the trajectory's prefix matches a
word-tuple fixed-complement constraint. Given word `a :: ys`, anchor row `i`,
and fiber assignment `c`, selects trajectories whose first `|ys|+1` positions
satisfy: start at `a`, at i-anchored positions the next state is `c(t)`,
at other positions the next state is `ys[j]`. -/
def fiberWordConstraintSubset
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : Finset (Traj k N) :=
  (fiber k N eN).filter (fun xs =>
    -- Start constraint: trajectory begins at a
    xs ⟨0, Nat.zero_lt_succ N⟩ = a ∧
    -- Anchor-i positions: trajectory successor matches c
    (∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
      xs ⟨((wordAnchorFiberList (k := k) a ys i)[t]).1 + 1,
          Nat.succ_lt_succ (Nat.lt_of_lt_of_le
            ((wordAnchorFiberList (k := k) a ys i)[t]).2 hN)⟩ = c t) ∧
    -- Non-i positions: trajectory successor matches original word
    (∀ j : Fin ys.length,
      (a :: ys).getD j.1 a ≠ i →
      xs ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩ = ys.get j))

/-! ## Section 2: Basic Properties -/

/-- The fiber word constraint subset is a subset of the evidence fiber. -/
lemma fiberWordConstraintSubset_subset_fiber
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    fiberWordConstraintSubset (k := k) a ys i c N hN eN ⊆ fiber k N eN := by
  intro xs hxs
  exact (Finset.mem_filter.mp hxs).1

/-- Membership in the constraint subset unpacks to the three conditions. -/
lemma mem_fiberWordConstraintSubset_iff
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (xs : Traj k N) :
    xs ∈ fiberWordConstraintSubset (k := k) a ys i c N hN eN ↔
      xs ∈ fiber k N eN ∧
      xs ⟨0, Nat.zero_lt_succ N⟩ = a ∧
      (∀ t : Fin (wordAnchorFiberList (k := k) a ys i).length,
        xs ⟨((wordAnchorFiberList (k := k) a ys i)[t]).1 + 1,
            Nat.succ_lt_succ (Nat.lt_of_lt_of_le
              ((wordAnchorFiberList (k := k) a ys i)[t]).2 hN)⟩ = c t) ∧
      (∀ j : Fin ys.length,
        (a :: ys).getD j.1 a ≠ i →
        xs ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩ = ys.get j) := by
  constructor
  · intro hxs
    simp only [fiberWordConstraintSubset, Finset.mem_filter] at hxs
    exact ⟨hxs.1, hxs.2.1, hxs.2.2.1, hxs.2.2.2⟩
  · intro ⟨h1, h2, h3, h4⟩
    simp only [fiberWordConstraintSubset, Finset.mem_filter]
    exact ⟨h1, h2, h3, h4⟩

/-- At the original word target, the constraint subset contains exactly the
trajectories whose prefix matches the word a :: ys. -/
lemma fiberWordConstraintSubset_wordAnchorFiberTarget_eq
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    fiberWordConstraintSubset (k := k) a ys i
        (wordAnchorFiberTarget (k := k) a ys i) N hN eN =
      (fiber k N eN).filter (fun xs =>
        xs ⟨0, Nat.zero_lt_succ N⟩ = a ∧
        ∀ j : Fin ys.length,
          xs ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩ = ys.get j) := by
  classical
  ext xs
  constructor
  · intro hxs
    rcases (mem_fiberWordConstraintSubset_iff
      (k := k) a ys i (wordAnchorFiberTarget (k := k) a ys i) N hN eN xs).1 hxs with
      ⟨hFiber, hStart, hAnchor, hOther⟩
    refine Finset.mem_filter.2 ?_
    refine ⟨hFiber, hStart, ?_⟩
    intro j
    by_cases hj : (a :: ys).getD j.1 a = i
    · have hmem : j ∈ wordAnchorFiberList (k := k) a ys i :=
        (mem_wordAnchorFiberList_iff (k := k) a ys i j).2 hj
      let t : Fin (wordAnchorFiberList (k := k) a ys i).length :=
        ⟨(wordAnchorFiberList (k := k) a ys i).idxOf j,
          List.idxOf_lt_length_iff.2 hmem⟩
      have ht : (wordAnchorFiberList (k := k) a ys i)[t] = j := by
        dsimp [t]
        exact List.getElem_idxOf (xs := wordAnchorFiberList (k := k) a ys i)
          (x := j) (h := List.idxOf_lt_length_iff.2 hmem)
      have hword : wordSuccessorTuple (k := k) a ys j = ys.get j := by
        cases j with
        | mk n hn =>
            simp [wordSuccessorTuple, hn]
      calc
        xs ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩
            = xs ⟨((wordAnchorFiberList (k := k) a ys i)[t]).1 + 1,
                Nat.succ_lt_succ
                  (Nat.lt_of_lt_of_le
                    ((wordAnchorFiberList (k := k) a ys i)[t]).2 hN)⟩ := by
                simp [ht]
        _ = wordAnchorFiberTarget (k := k) a ys i t := hAnchor t
        _ = wordSuccessorTuple (k := k) a ys j := by
              simp [wordAnchorFiberTarget, ht]
        _ = ys.get j := hword
    · exact hOther j hj
  · intro hxs
    rcases Finset.mem_filter.1 hxs with ⟨hFiber, hPrefixStart, hPrefix⟩
    refine (mem_fiberWordConstraintSubset_iff
      (k := k) a ys i (wordAnchorFiberTarget (k := k) a ys i) N hN eN xs).2 ?_
    refine ⟨hFiber, hPrefixStart, ?_, ?_⟩
    · intro t
      have hword :
          wordSuccessorTuple (k := k) a ys ((wordAnchorFiberList (k := k) a ys i)[t]) =
            ys.get ((wordAnchorFiberList (k := k) a ys i)[t]) := by
        cases ((wordAnchorFiberList (k := k) a ys i)[t]) with
        | mk n hn =>
            simp [wordSuccessorTuple, hn]
      calc
        xs ⟨((wordAnchorFiberList (k := k) a ys i)[t]).1 + 1,
            Nat.succ_lt_succ
              (Nat.lt_of_lt_of_le
                ((wordAnchorFiberList (k := k) a ys i)[t]).2 hN)⟩
            = ys.get ((wordAnchorFiberList (k := k) a ys i)[t]) := by
                exact hPrefix ((wordAnchorFiberList (k := k) a ys i)[t])
        _ = wordSuccessorTuple (k := k) a ys ((wordAnchorFiberList (k := k) a ys i)[t]) := by
              exact hword.symm
        _ = wordAnchorFiberTarget (k := k) a ys i t := by
              simp [wordAnchorFiberTarget]
    · intro j hj
      exact hPrefix j

/-! ## Section 2b: Exact prefix events inside a fixed evidence fiber

For the direct conditioned-prefix route we want the simplest finite event:
trajectories in a fixed evidence fiber whose first `|ys|+1` symbols are exactly
the word `a :: ys`. This is the `wordAnchorFiberTarget` specialization of the
more general mixed-row constraint subset above, but it is useful enough to name
directly. -/

/-- Finite subset of a fixed evidence fiber whose first `|ys|+1` symbols are
exactly the word `a :: ys`. -/
def fiberPrefixSubset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    Finset (Traj k N) :=
  (fiber k N eN).filter (fun xs =>
    xs ⟨0, Nat.zero_lt_succ N⟩ = a ∧
    ∀ j : Fin ys.length,
      xs ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩ = ys.get j)

lemma fiberPrefixSubset_subset_fiber
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    fiberPrefixSubset (k := k) a ys N hN eN ⊆ fiber k N eN := by
  intro xs hxs
  exact (Finset.mem_filter.mp hxs).1

lemma mem_fiberPrefixSubset_iff
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (xs : Traj k N) :
    xs ∈ fiberPrefixSubset (k := k) a ys N hN eN ↔
      xs ∈ fiber k N eN ∧
      xs ⟨0, Nat.zero_lt_succ N⟩ = a ∧
      (∀ j : Fin ys.length,
        xs ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩ = ys.get j) := by
  simp [fiberPrefixSubset]

/-- The exact-prefix subset is the `wordAnchorFiberTarget` specialization of the
mixed-row fixed-complement subset, for any chosen anchor row `i`. -/
lemma fiberPrefixSubset_eq_fiberWordConstraintSubset_wordAnchorFiberTarget
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    fiberPrefixSubset (k := k) a ys N hN eN =
      fiberWordConstraintSubset (k := k) a ys i
        (wordAnchorFiberTarget (k := k) a ys i) N hN eN := by
  simpa [fiberPrefixSubset] using
    (fiberWordConstraintSubset_wordAnchorFiberTarget_eq
      (k := k) a ys i N hN eN).symm

/-- Markov-exchangeable mass on the exact-prefix subset is cardinality times the
mass of any representative, because the subset lies inside one evidence fiber. -/
lemma sum_mu_fiberPrefixSubset_eq_card_mul
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    {xs0 : Traj k N}
    (hxs0 : xs0 ∈ fiberPrefixSubset (k := k) a ys N hN eN) :
    (∑ xs ∈ fiberPrefixSubset (k := k) a ys N hN eN,
      μ (trajToList (k := k) xs)) =
      ((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) *
        μ (trajToList (k := k) xs0) := by
  exact
    sum_mu_eq_card_mul_of_subset_fiber μ hμ
      (fiberPrefixSubset_subset_fiber (k := k) a ys N hN eN) hxs0

/-- Euler-trail-side counting formula for exact prefix events inside a fixed
evidence fiber. This is the direct conditioned-prefix counting interface on the
full graph `graphOfState eN`. -/
lemma eulerTrailFinset_card_filter_fiberPrefixSubset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hs : eN ∈ stateFinset k N) :
    ((eulerTrailFinset
        (graphOfState eN) eN.start eN.last).filter
      (fun f =>
        castTraj
            (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
            (trailVertexSeq
              (graphOfState eN) eN.start f) ∈
          fiberPrefixSubset (k := k) a ys N hN eN)).card =
      (fiberPrefixSubset (k := k) a ys N hN eN).card *
        ∏ a : Fin k, ∏ b : Fin k, (graphOfState eN a b).factorial := by
  have hTok : totalEdgeTokens (k := k) (graphOfState eN) = N :=
    totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs
  subst hTok
  have hA :
      fiberPrefixSubset (k := k) a ys
          (totalEdgeTokens (k := k) (graphOfState eN)) hN eN ⊆
        fiber k (totalEdgeTokens (k := k) (graphOfState eN)) eN :=
    fiberPrefixSubset_subset_fiber
      (k := k) a ys (totalEdgeTokens (k := k) (graphOfState eN)) hN eN
  simp only [castTraj]; exact
    eulerTrailFinset_card_filter_trajSubset
      (k := k) (s := eN)
      (A := fiberPrefixSubset (k := k) a ys
        (totalEdgeTokens (k := k) (graphOfState eN)) hN eN) hA

/-- Cross-multiplied form of the exact fixed-fiber conditional-prefix identity:
the prefix fraction inside an evidence fiber equals the corresponding filtered
Euler-trail fraction on `graphOfState eN`. This avoids division bookkeeping and
is the exact finite counting statement behind the ratio interpretation. -/
lemma fiberPrefixSubset_card_mul_eulerTrailFinset_card_eq
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hs : eN ∈ stateFinset k N) :
    (fiberPrefixSubset (k := k) a ys N hN eN).card *
        (eulerTrailFinset (graphOfState eN) eN.start eN.last).card =
      (fiber k N eN).card *
        ((eulerTrailFinset
            (graphOfState eN) eN.start eN.last).filter
          (fun f =>
            castTraj
                (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
                (trailVertexSeq
                  (graphOfState eN) eN.start f) ∈
              fiberPrefixSubset (k := k) a ys N hN eN)).card := by
  let factor : ℕ := ∏ a : Fin k, ∏ b : Fin k, (graphOfState eN a b).factorial
  have hPrefix :
      ((eulerTrailFinset
          (graphOfState eN) eN.start eN.last).filter
        (fun f =>
          castTraj
              (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
              (trailVertexSeq
                (graphOfState eN) eN.start f) ∈
            fiberPrefixSubset (k := k) a ys N hN eN)).card =
        (fiberPrefixSubset (k := k) a ys N hN eN).card * factor := by
    simpa [factor] using
      eulerTrailFinset_card_filter_fiberPrefixSubset
        (k := k) a ys N hN eN hs
  have hTotal :
      (eulerTrailFinset (graphOfState eN) eN.start eN.last).card =
        (fiber k N eN).card * factor := by
    simpa [factor] using eulerTrailFinset_card_eq (k := k) eN hs
  calc
    (fiberPrefixSubset (k := k) a ys N hN eN).card *
        (eulerTrailFinset (graphOfState eN) eN.start eN.last).card
      = (fiberPrefixSubset (k := k) a ys N hN eN).card *
          ((fiber k N eN).card * factor) := by rw [hTotal]
    _ = (fiber k N eN).card *
          ((fiberPrefixSubset (k := k) a ys N hN eN).card * factor) := by
          ac_rfl
    _ = (fiber k N eN).card *
          ((eulerTrailFinset
              (graphOfState eN) eN.start eN.last).filter
            (fun f =>
              castTraj
                  (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
                  (trailVertexSeq
                    (graphOfState eN) eN.start f) ∈
                fiberPrefixSubset (k := k) a ys N hN eN)).card := by
          rw [hPrefix]

/-- Rational-ratio form of the exact fixed-fiber conditional-prefix identity:
the fraction of trajectories in a fixed evidence fiber with prefix `a :: ys`
equals the corresponding fraction of Euler trails on `graphOfState eN`. -/
theorem rat_card_ratio_fiberPrefixSubset_eq_eulerTrail_ratio
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hs : eN ∈ stateFinset k N) :
    ((fiberPrefixSubset (k := k) a ys N hN eN).card : ℚ) /
        (fiber k N eN).card =
      (((eulerTrailFinset
            (graphOfState eN) eN.start eN.last).filter
          (fun f =>
            castTraj
                (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
                (trailVertexSeq
                  (graphOfState eN) eN.start f) ∈
              fiberPrefixSubset (k := k) a ys N hN eN)).card : ℚ) /
        (eulerTrailFinset (graphOfState eN) eN.start eN.last).card := by
  have hfiber : ((fiber k N eN).card : ℚ) ≠ 0 := by
    exact_mod_cast fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) hs
  have hfact_pos : 0 < ∏ a : Fin k, ∏ b : Fin k, (graphOfState eN a b).factorial := by
    classical
    refine Finset.prod_pos ?_
    intro a ha
    refine Finset.prod_pos ?_
    intro b hb
    exact Nat.factorial_pos (graphOfState eN a b)
  have htotal_nat :
      (eulerTrailFinset (graphOfState eN) eN.start eN.last).card ≠ 0 := by
    rw [eulerTrailFinset_card_eq (k := k) eN hs]
    exact Nat.mul_ne_zero
      (fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) hs)
      (Nat.ne_of_gt hfact_pos)
  have htotal : ((eulerTrailFinset (graphOfState eN) eN.start eN.last).card : ℚ) ≠ 0 := by
    exact_mod_cast htotal_nat
  have hcross :
      ((fiberPrefixSubset (k := k) a ys N hN eN).card : ℚ) *
          (eulerTrailFinset (graphOfState eN) eN.start eN.last).card =
        (fiber k N eN).card *
          (((eulerTrailFinset
              (graphOfState eN) eN.start eN.last).filter
            (fun f =>
              castTraj
                  (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
                  (trailVertexSeq
                    (graphOfState eN) eN.start f) ∈
                fiberPrefixSubset (k := k) a ys N hN eN)).card : ℚ) := by
    exact_mod_cast
      fiberPrefixSubset_card_mul_eulerTrailFinset_card_eq
        (k := k) a ys N hN eN hs
  field_simp [hfiber, htotal]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

/-! ## Section 3a: Canonical residual evidence after deleting a prefix

The residual finite event should eventually land in one canonical smaller
evidence fiber.  We first package that target evidence object itself: take the
evidence state of the prefix word `a :: ys`, subtract its transition counts from
`eN`, keep the original final state `eN.last`, and use the prefix endpoint as
the new start. -/

/-- Evidence state of the prescribed prefix word `a :: ys`. -/
def prefixWordState
    (a : Fin k) (ys : List (Fin k)) : MarkovState k :=
  stateOfTraj (k := k) (wordTraj (k := k) a ys)

@[simp] lemma prefixWordState_start
    (a : Fin k) (ys : List (Fin k)) :
    (prefixWordState (k := k) a ys).start = a := by
  rfl

@[simp] lemma prefixWordState_last
    (a : Fin k) (ys : List (Fin k)) :
    (prefixWordState (k := k) a ys).last =
      (wordTraj (k := k) a ys) (Fin.last ys.length) := by
  rfl

@[simp] lemma prefixWordState_counts
    (a : Fin k) (ys : List (Fin k)) (i j : Fin k) :
    (prefixWordState (k := k) a ys).counts.counts i j =
      (MarkovExchangeabilityBridge.countsOfFn (k := k)
        (wordTraj (k := k) a ys)).counts i j := by
  rfl

lemma prefixWordState_mem_stateFinset
    (a : Fin k) (ys : List (Fin k)) :
    prefixWordState (k := k) a ys ∈ stateFinset k ys.length := by
  simpa [prefixWordState] using
    stateOfTraj_mem_stateFinset (k := k) (xs := wordTraj (k := k) a ys)

/-- Pointwise residual transition counts after removing the prefix word
`a :: ys` from a larger evidence state `eN`. -/
def residualCountsOfPrefix
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : TransCounts k :=
  ⟨fun i j =>
    eN.counts.counts i j - (prefixWordState (k := k) a ys).counts.counts i j⟩

@[simp] lemma residualCountsOfPrefix_apply
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) (i j : Fin k) :
    (residualCountsOfPrefix (k := k) a ys eN).counts i j =
      eN.counts.counts i j - (prefixWordState (k := k) a ys).counts.counts i j := by
  rfl

/-- Canonical residual evidence state obtained by deleting the prescribed prefix
word `a :: ys` from the ambient evidence state `eN`. -/
def residualStateOfPrefix
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : MarkovState k :=
  { start := (prefixWordState (k := k) a ys).last
    counts := residualCountsOfPrefix (k := k) a ys eN
    last := eN.last }

@[simp] lemma residualStateOfPrefix_start
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    (residualStateOfPrefix (k := k) a ys eN).start =
      (prefixWordState (k := k) a ys).last := by
  rfl

@[simp] lemma residualStateOfPrefix_last
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    (residualStateOfPrefix (k := k) a ys eN).last = eN.last := by
  rfl

@[simp] lemma residualStateOfPrefix_counts
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) (i j : Fin k) :
    (residualStateOfPrefix (k := k) a ys eN).counts.counts i j =
      eN.counts.counts i j - (prefixWordState (k := k) a ys).counts.counts i j := by
  rfl

lemma prefixWordState_counts_le_of_residualState_mem_stateFinset
    {N : ℕ} (a : Fin k) (ys : List (Fin k)) (hN : ys.length ≤ N)
    {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N)
    (hres : residualStateOfPrefix (k := k) a ys eN ∈ stateFinset k (N - ys.length)) :
    ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j := by
  classical
  have hsumE :
      ∑ p : Fin k × Fin k, eN.counts.counts p.1 p.2 = N := by
    calc
      ∑ p : Fin k × Fin k, eN.counts.counts p.1 p.2
          = ∑ a : Fin k, ∑ b : Fin k, eN.counts.counts a b := by
              simpa using (Fintype.sum_prod_type' (f := fun a b => eN.counts.counts a b))
      _ = N := MarkovDeFinettiHardEuler.sum_counts_of_mem_stateFinset
          (k := k) (N := N) (eN := eN) heN
  have hsumP :
      ∑ p : Fin k × Fin k, (prefixWordState (k := k) a ys).counts.counts p.1 p.2 =
        ys.length := by
    calc
      ∑ p : Fin k × Fin k, (prefixWordState (k := k) a ys).counts.counts p.1 p.2
          = ∑ a' : Fin k, ∑ b : Fin k,
              (prefixWordState (k := k) a ys).counts.counts a' b := by
                simpa using
                  (Fintype.sum_prod_type'
                    (f := fun a' b =>
                      (prefixWordState (k := k) a ys).counts.counts a' b))
      _ = ys.length := by
          exact MarkovDeFinettiHardEuler.sum_counts_of_mem_stateFinset
            (k := k) (N := ys.length)
            (eN := prefixWordState (k := k) a ys)
            (prefixWordState_mem_stateFinset (k := k) a ys)
  have hsumR :
      ∑ p : Fin k × Fin k,
        (residualStateOfPrefix (k := k) a ys eN).counts.counts p.1 p.2 =
          N - ys.length := by
    calc
      ∑ p : Fin k × Fin k,
          (residualStateOfPrefix (k := k) a ys eN).counts.counts p.1 p.2
          = ∑ a' : Fin k, ∑ b : Fin k,
              (residualStateOfPrefix (k := k) a ys eN).counts.counts a' b := by
                simpa using
                  (Fintype.sum_prod_type'
                    (f := fun a' b =>
                      (residualStateOfPrefix (k := k) a ys eN).counts.counts a' b))
      _ = N - ys.length := MarkovDeFinettiHardEuler.sum_counts_of_mem_stateFinset
          (k := k) (N := N - ys.length)
          (eN := residualStateOfPrefix (k := k) a ys eN) hres
  have hsumMax :
      ∑ p : Fin k × Fin k,
        max (eN.counts.counts p.1 p.2)
          ((prefixWordState (k := k) a ys).counts.counts p.1 p.2) = N := by
    calc
      ∑ p : Fin k × Fin k,
          max (eN.counts.counts p.1 p.2)
            ((prefixWordState (k := k) a ys).counts.counts p.1 p.2)
          =
            ∑ p : Fin k × Fin k,
              ((eN.counts.counts p.1 p.2 -
                  (prefixWordState (k := k) a ys).counts.counts p.1 p.2) +
                (prefixWordState (k := k) a ys).counts.counts p.1 p.2) := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              symm
              exact Nat.sub_add_eq_max _ _
      _ =
          (∑ p : Fin k × Fin k,
              (eN.counts.counts p.1 p.2 -
                (prefixWordState (k := k) a ys).counts.counts p.1 p.2)) +
            ∑ p : Fin k × Fin k,
              (prefixWordState (k := k) a ys).counts.counts p.1 p.2 := by
                rw [Finset.sum_add_distrib]
      _ =
          (∑ p : Fin k × Fin k,
              (residualStateOfPrefix (k := k) a ys eN).counts.counts p.1 p.2) +
            ∑ p : Fin k × Fin k,
              (prefixWordState (k := k) a ys).counts.counts p.1 p.2 := by
                refine congrArg (fun t => t + ∑ p : Fin k × Fin k,
                  (prefixWordState (k := k) a ys).counts.counts p.1 p.2) ?_
                refine Finset.sum_congr rfl ?_
                intro p hp
                rfl
      _ = (N - ys.length) + ys.length := by rw [hsumR, hsumP]
      _ = N := Nat.sub_add_cancel hN
  intro i j
  by_contra hij
  have hlt :
      eN.counts.counts i j <
        max (eN.counts.counts i j)
          ((prefixWordState (k := k) a ys).counts.counts i j) := by
    have hij' :
        eN.counts.counts i j <
          (prefixWordState (k := k) a ys).counts.counts i j := lt_of_not_ge hij
    simpa [Nat.max_eq_right (Nat.le_of_lt hij')] using hij'
  have hsumLt :
      ∑ p : Fin k × Fin k, eN.counts.counts p.1 p.2 <
        ∑ p : Fin k × Fin k,
          max (eN.counts.counts p.1 p.2)
            ((prefixWordState (k := k) a ys).counts.counts p.1 p.2) := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro p hp
      exact Nat.le_max_left _ _
    · exact ⟨(i, j), Finset.mem_univ _, hlt⟩
  exact (ne_of_lt hsumLt) (hsumE.trans hsumMax.symm)

/-! ## Section 3b: Residual suffix event after a prescribed prefix

To move toward the residual-graph formula without over-claiming, we first
package the honest finite residual object: the suffix trajectory remaining after
deleting the prescribed prefix from a member of `fiberPrefixSubset`.  This gives
an exact cardinality-preserving reduction of the prefix event to a residual
finite event. -/

/-- Glue a residual suffix trajectory back onto the prescribed prefix word.
The suffix takes over at time `ys.length`, so dropping the prefix recovers the
original residual trajectory literally. -/
def trajGluePrefix
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (zs : Traj k (N - ys.length)) :
    Traj k N :=
  fun i =>
    if hi : i.1 < ys.length then
      wordTraj (k := k) a ys ⟨i.1, by omega⟩
    else
      zs ⟨i.1 - ys.length, by
        have hiN := i.2
        omega⟩

/-- Drop the first `n` transitions of a trajectory, keeping the vertex at time
`n` as the new start. -/
def trajDrop
    {N : ℕ} (n : ℕ) (h : n ≤ N) (xs : Traj k N) : Traj k (N - n) :=
  fun i => xs ⟨i.1 + n, by
    have hi := i.2
    omega⟩

lemma trajDrop_trajGluePrefix
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (zs : Traj k (N - ys.length)) :
    trajDrop (k := k) ys.length hN
        (trajGluePrefix (k := k) a ys N hN zs) = zs := by
  funext i
  have hnot : ¬ i.1 + ys.length < ys.length := by
    omega
  simp [trajDrop, trajGluePrefix, hnot]

/-- Transition counts split exactly into the first `n` transitions and the
remaining dropped suffix transitions. -/
lemma transCount_eq_transCount_trajPrefix_add_transCount_trajDrop
    {N n : ℕ} (h : n ≤ N) (xs : Traj k N) (a b : Fin k) :
    transCount (n := N) xs a b =
      transCount (n := n) (trajPrefix (k := k) (n := n) (N := N) h xs) a b +
        transCount (n := N - n) (trajDrop (k := k) n h xs) a b := by
  classical
  let S : Finset (Fin N) :=
    Finset.univ.filter (fun i : Fin N => xs (Fin.castSucc i) = a ∧ xs (Fin.succ i) = b)
  let dropEmb : Fin (N - n) ↪ Fin N :=
    ⟨fun j => ⟨j.1 + n, by
        have hj := j.2
        omega⟩,
      by
        intro i j hij
        exact Fin.ext (by simpa using congrArg Fin.val hij)⟩
  have hsplit :
      (S.filter (fun i : Fin N => i.1 < n)).card +
          (S.filter (fun i : Fin N => ¬ i.1 < n)).card = S.card := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := S) (p := fun i : Fin N => i.1 < n))
  have hleft :
      S.filter (fun i : Fin N => i.1 < n) =
        ((Finset.univ.filter fun j : Fin n =>
            trajPrefix (k := k) (n := n) (N := N) h xs (Fin.castSucc j) = a ∧
              trajPrefix (k := k) (n := n) (N := N) h xs (Fin.succ j) = b)).map
          (Fin.castLEEmb h) := by
    ext i
    constructor
    · intro hi
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with ⟨hpair, hi_lt⟩
      let j : Fin n := ⟨i.1, hi_lt⟩
      have hji : Fin.castLE h j = i := by
        ext
        simp [j]
      refine Finset.mem_map.2 ?_
      refine ⟨j, ?_, by simpa using hji⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · calc
          trajPrefix (k := k) (n := n) (N := N) h xs (Fin.castSucc j)
              = xs (Fin.castSucc (Fin.castLE h j)) := by
                  simp [trajPrefix, Fin.castLE_castSucc]
          _ = xs (Fin.castSucc i) := by rw [hji]
          _ = a := hpair.1
      · calc
          trajPrefix (k := k) (n := n) (N := N) h xs (Fin.succ j)
              = xs (Fin.succ (Fin.castLE h j)) := by
                  simp [trajPrefix, Fin.castLE_succ]
          _ = xs (Fin.succ i) := by rw [hji]
          _ = b := hpair.2
    · intro hi
      rcases Finset.mem_map.1 hi with ⟨j, hj, hji⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hji' : Fin.castLE h j = i := by
        simpa using hji
      refine Finset.mem_filter.2 ?_
      refine ⟨?_, ?_⟩
      · dsimp [S]
        refine Finset.mem_filter.2 ?_
        refine ⟨Finset.mem_univ _, ?_⟩
        constructor
        · calc
            xs (Fin.castSucc i)
                = xs (Fin.castSucc (Fin.castLE h j)) := by rw [← hji']
            _ = trajPrefix (k := k) (n := n) (N := N) h xs (Fin.castSucc j) := by
                  simp [trajPrefix, Fin.castLE_castSucc]
            _ = a := hj.1
        · calc
            xs (Fin.succ i)
                = xs (Fin.succ (Fin.castLE h j)) := by rw [← hji']
            _ = trajPrefix (k := k) (n := n) (N := N) h xs (Fin.succ j) := by
                  simp [trajPrefix, Fin.castLE_succ]
            _ = b := hj.2
      · have hval : i.1 = j.1 := by
            simpa using (congrArg Fin.val hji').symm
        omega
  have hright :
      S.filter (fun i : Fin N => ¬ i.1 < n) =
        ((Finset.univ.filter fun j : Fin (N - n) =>
            trajDrop (k := k) n h xs (Fin.castSucc j) = a ∧
              trajDrop (k := k) n h xs (Fin.succ j) = b)).map dropEmb := by
    ext i
    constructor
    · intro hi
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with ⟨hpair, hi_nlt⟩
      have hge : n ≤ i.1 := Nat.le_of_not_lt hi_nlt
      let j : Fin (N - n) := ⟨i.1 - n, by
        have hiN := i.2
        omega⟩
      have hji : dropEmb j = i := by
        ext
        simp [dropEmb, j, Nat.sub_add_cancel hge]
      refine Finset.mem_map.2 ?_
      refine ⟨j, ?_, by simpa using hji⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · calc
          trajDrop (k := k) n h xs (Fin.castSucc j)
              = xs (Fin.castSucc (dropEmb j)) := by
                  simp [trajDrop, dropEmb, j]
          _ = xs (Fin.castSucc i) := by rw [hji]
          _ = a := hpair.1
      · calc
          trajDrop (k := k) n h xs (Fin.succ j)
              = xs (Fin.succ (dropEmb j)) := by
                  have hidx :
                      (⟨j.1 + 1 + n, by
                        have hj := j.2
                        omega⟩ : Fin (N + 1)) = Fin.succ (dropEmb j) := by
                    ext
                    simp [dropEmb]
                    omega
                  calc
                    trajDrop (k := k) n h xs (Fin.succ j)
                        = xs ⟨j.1 + 1 + n, by
                            have hj := j.2
                            omega⟩ := by
                              rfl
                    _ = xs (Fin.succ (dropEmb j)) := by rw [hidx]
          _ = xs (Fin.succ i) := by rw [hji]
          _ = b := hpair.2
    · intro hi
      rcases Finset.mem_map.1 hi with ⟨j, hj, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine Finset.mem_filter.2 ?_
      refine ⟨?_, ?_⟩
      · dsimp [S]
        refine Finset.mem_filter.2 ?_
        refine ⟨Finset.mem_univ _, ?_⟩
        constructor
        · calc
            xs (Fin.castSucc (dropEmb j))
                = trajDrop (k := k) n h xs (Fin.castSucc j) := by
                    simp [trajDrop, dropEmb]
            _ = a := hj.1
        · have hidx :
              (⟨j.1 + 1 + n, by
                have hj' := j.2
                omega⟩ : Fin (N + 1)) = Fin.succ (dropEmb j) := by
            ext
            simp [dropEmb]
            omega
          calc
            xs (Fin.succ (dropEmb j))
                = xs ⟨j.1 + 1 + n, by
                    have hj' := j.2
                    omega⟩ := by rw [← hidx]
            _ = trajDrop (k := k) n h xs (Fin.succ j) := by
                  rfl
            _ = b := hj.2
      · change ¬ (j.1 + n < n)
        omega
  have hleft_card :
      (S.filter (fun i : Fin N => i.1 < n)).card =
        transCount (n := n) (trajPrefix (k := k) (n := n) (N := N) h xs) a b := by
    rw [hleft, Finset.card_map]
    rfl
  have hright_card :
      (S.filter (fun i : Fin N => ¬ i.1 < n)).card =
        transCount (n := N - n) (trajDrop (k := k) n h xs) a b := by
    rw [hright, Finset.card_map]
    rfl
  calc
    transCount (n := N) xs a b = S.card := by
      rfl
    _ = (S.filter (fun i : Fin N => i.1 < n)).card +
          (S.filter (fun i : Fin N => ¬ i.1 < n)).card := by
            exact hsplit.symm
    _ = transCount (n := n) (trajPrefix (k := k) (n := n) (N := N) h xs) a b +
          transCount (n := N - n) (trajDrop (k := k) n h xs) a b := by
            rw [hleft_card, hright_card]

lemma trajPrefix_eq_wordTraj_of_mem_fiberPrefixSubset
    {a : Fin k} {ys : List (Fin k)} {N : ℕ} {hN : ys.length ≤ N}
    {eN : MarkovState k} {xs : Traj k N}
    (hxs : xs ∈ fiberPrefixSubset (k := k) a ys N hN eN) :
    trajPrefix (k := k) (n := ys.length) (N := N) hN xs =
      wordTraj (k := k) a ys := by
  rcases (mem_fiberPrefixSubset_iff
      (k := k) a ys N hN eN xs).1 hxs with ⟨_, hstart, hprefix⟩
  funext i
  cases i using Fin.cases with
  | zero =>
      simpa [trajPrefix, wordTraj] using hstart
  | succ j =>
      simpa [trajPrefix, wordTraj, Fin.castLE] using hprefix j

lemma prefixState_eq_prefixWordState_of_mem_fiberPrefixSubset
    {a : Fin k} {ys : List (Fin k)} {N : ℕ} {hN : ys.length ≤ N}
    {eN : MarkovState k} {xs : Traj k N}
    (hxs : xs ∈ fiberPrefixSubset (k := k) a ys N hN eN) :
    prefixState (k := k) (n := ys.length) (N := N) hN xs =
      prefixWordState (k := k) a ys := by
  simp [prefixState, prefixWordState, trajPrefix_eq_wordTraj_of_mem_fiberPrefixSubset
    (k := k) hxs]

lemma trajPrefix_trajGluePrefix_eq_wordTraj
    {a : Fin k} {ys : List (Fin k)} {N : ℕ} {hN : ys.length ≤ N}
    {zs : Traj k (N - ys.length)}
    (hz0 : zs 0 = (prefixWordState (k := k) a ys).last) :
    trajPrefix (k := k) (n := ys.length) (N := N) hN
        (trajGluePrefix (k := k) a ys N hN zs) =
      wordTraj (k := k) a ys := by
  funext i
  by_cases hi : i.1 < ys.length
  · simp [trajPrefix, trajGluePrefix, hi, wordTraj]
  · have hi_eq : i.1 = ys.length := by
      have hi_le : i.1 ≤ ys.length := Nat.le_of_lt_succ i.2
      omega
    have hz0' : zs 0 = wordTraj (k := k) a ys (Fin.last ys.length) := by
      simpa [prefixWordState] using hz0
    have hi_last : i = Fin.last ys.length := by
      apply Fin.ext
      simp [hi_eq]
    subst hi_last
    simp [trajPrefix, trajGluePrefix, hz0']

lemma stateOfTraj_trajDrop_eq_residualStateOfPrefix_of_mem_fiberPrefixSubset
    {a : Fin k} {ys : List (Fin k)} {N : ℕ} {hN : ys.length ≤ N}
    {eN : MarkovState k} {xs : Traj k N}
    (hxs : xs ∈ fiberPrefixSubset (k := k) a ys N hN eN) :
    stateOfTraj (k := k) (trajDrop (k := k) ys.length hN xs) =
      residualStateOfPrefix (k := k) a ys eN := by
  have hxsFiber : xs ∈ fiber k N eN :=
    (mem_fiberPrefixSubset_iff (k := k) a ys N hN eN xs).1 hxs |>.1
  have hFiber : stateOfTraj (k := k) xs = eN :=
    (Finset.mem_filter.1 hxsFiber).2
  have hPrefixState :
      prefixState (k := k) (n := ys.length) (N := N) hN xs =
        prefixWordState (k := k) a ys :=
    prefixState_eq_prefixWordState_of_mem_fiberPrefixSubset (k := k) hxs
  refine MarkovState.ext ?_ ?_ ?_
  · have hlastPrefix :
        trajPrefix (k := k) (n := ys.length) (N := N) hN xs (Fin.last ys.length) =
          (wordTraj (k := k) a ys) (Fin.last ys.length) := by
      simpa [prefixState, prefixWordState, stateOfTraj_last] using
        congrArg MarkovState.last hPrefixState
    simpa [stateOfTraj, trajDrop, residualStateOfPrefix, trajPrefix, Fin.last] using hlastPrefix
  · ext i j
    have hTotal :
        eN.counts.counts i j = transCount (n := N) xs i j := by
      simpa [stateOfTraj, MarkovExchangeabilityBridge.countsOfFn] using
        (congrArg (fun s : MarkovState k => s.counts.counts i j) hFiber).symm
    have hPrefix :
        (prefixWordState (k := k) a ys).counts.counts i j =
          transCount (n := ys.length)
            (trajPrefix (k := k) (n := ys.length) (N := N) hN xs) i j := by
      simpa [prefixState, prefixWordState, stateOfTraj, MarkovExchangeabilityBridge.countsOfFn]
        using congrArg (fun s : MarkovState k => s.counts.counts i j) hPrefixState.symm
    have hSplit :
        transCount (n := N) xs i j =
          transCount (n := ys.length)
              (trajPrefix (k := k) (n := ys.length) (N := N) hN xs) i j +
            transCount (n := N - ys.length)
              (trajDrop (k := k) ys.length hN xs) i j :=
      transCount_eq_transCount_trajPrefix_add_transCount_trajDrop
        (k := k) (h := hN) xs i j
    have hCountEq :
        eN.counts.counts i j =
          (prefixWordState (k := k) a ys).counts.counts i j +
            transCount (n := N - ys.length)
              (trajDrop (k := k) ys.length hN xs) i j := by
      calc
        eN.counts.counts i j = transCount (n := N) xs i j := hTotal
        _ = transCount (n := ys.length)
              (trajPrefix (k := k) (n := ys.length) (N := N) hN xs) i j +
            transCount (n := N - ys.length)
              (trajDrop (k := k) ys.length hN xs) i j := hSplit
        _ = (prefixWordState (k := k) a ys).counts.counts i j +
            transCount (n := N - ys.length)
              (trajDrop (k := k) ys.length hN xs) i j := by
              rw [← hPrefix]
    calc
      (stateOfTraj (k := k) (trajDrop (k := k) ys.length hN xs)).counts.counts i j
          = transCount (n := N - ys.length)
              (trajDrop (k := k) ys.length hN xs) i j := by
                  rfl
      _ = eN.counts.counts i j - (prefixWordState (k := k) a ys).counts.counts i j := by
            exact (tsub_eq_of_eq_add_rev hCountEq).symm
      _ = (residualStateOfPrefix (k := k) a ys eN).counts.counts i j := by
            rfl
  · have hLast :
        xs (Fin.last N) = eN.last := by
      simpa [stateOfTraj] using congrArg MarkovState.last hFiber
    simpa [stateOfTraj, trajDrop, residualStateOfPrefix, Nat.sub_add_cancel hN, Fin.last] using hLast

lemma stateOfTraj_trajGluePrefix_eq_of_stateOfTraj_eq_residualStateOfPrefix
    {a : Fin k} {ys : List (Fin k)} {N : ℕ} {hN : ys.length ≤ N}
    {eN : MarkovState k} {zs : Traj k (N - ys.length)}
    (hz : stateOfTraj (k := k) zs = residualStateOfPrefix (k := k) a ys eN)
    (hstart : eN.start = a)
    (hle : ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j) :
    stateOfTraj (k := k) (trajGluePrefix (k := k) a ys N hN zs) = eN := by
  have hz0 :
      zs 0 = (prefixWordState (k := k) a ys).last := by
    simpa [stateOfTraj, residualStateOfPrefix] using congrArg MarkovState.start hz
  have hPrefix :
      trajPrefix (k := k) (n := ys.length) (N := N) hN
          (trajGluePrefix (k := k) a ys N hN zs) =
        wordTraj (k := k) a ys :=
    trajPrefix_trajGluePrefix_eq_wordTraj (k := k) (hN := hN) hz0
  have hDrop :
      trajDrop (k := k) ys.length hN
          (trajGluePrefix (k := k) a ys N hN zs) = zs :=
    trajDrop_trajGluePrefix (k := k) a ys N hN zs
  refine MarkovState.ext ?_ ?_ ?_
  · have hStart :
        trajPrefix (k := k) (n := ys.length) (N := N) hN
            (trajGluePrefix (k := k) a ys N hN zs) 0 =
          wordTraj (k := k) a ys 0 := by
      simpa using congrArg (fun f : Traj k ys.length => f 0) hPrefix
    simpa [trajPrefix, wordTraj, hstart] using hStart
  · ext i j
    have hPrefixCount :
        (prefixWordState (k := k) a ys).counts.counts i j =
          transCount (n := ys.length)
            (trajPrefix (k := k) (n := ys.length) (N := N) hN
              (trajGluePrefix (k := k) a ys N hN zs)) i j := by
      simpa [prefixWordState, stateOfTraj, MarkovExchangeabilityBridge.countsOfFn] using
        congrArg (fun s : MarkovState k => s.counts.counts i j)
          (congrArg (stateOfTraj (k := k)) hPrefix).symm
    have hResidualCount :
        transCount (n := N - ys.length)
            (trajDrop (k := k) ys.length hN
              (trajGluePrefix (k := k) a ys N hN zs)) i j =
          (residualStateOfPrefix (k := k) a ys eN).counts.counts i j := by
      calc
        transCount (n := N - ys.length)
            (trajDrop (k := k) ys.length hN
              (trajGluePrefix (k := k) a ys N hN zs)) i j
            = transCount (n := N - ys.length) zs i j := by
                rw [hDrop]
        _ = (stateOfTraj (k := k) zs).counts.counts i j := by
              rfl
        _ = (residualStateOfPrefix (k := k) a ys eN).counts.counts i j := by
              simpa using congrArg (fun s : MarkovState k => s.counts.counts i j) hz
    have hSplit :
        transCount (n := N) (trajGluePrefix (k := k) a ys N hN zs) i j =
          transCount (n := ys.length)
              (trajPrefix (k := k) (n := ys.length) (N := N) hN
                (trajGluePrefix (k := k) a ys N hN zs)) i j +
            transCount (n := N - ys.length)
              (trajDrop (k := k) ys.length hN
                (trajGluePrefix (k := k) a ys N hN zs)) i j :=
      transCount_eq_transCount_trajPrefix_add_transCount_trajDrop
        (k := k) (h := hN) (trajGluePrefix (k := k) a ys N hN zs) i j
    calc
      (stateOfTraj (k := k) (trajGluePrefix (k := k) a ys N hN zs)).counts.counts i j
          = transCount (n := N) (trajGluePrefix (k := k) a ys N hN zs) i j := by
              rfl
      _ = transCount (n := ys.length)
            (trajPrefix (k := k) (n := ys.length) (N := N) hN
              (trajGluePrefix (k := k) a ys N hN zs)) i j +
          transCount (n := N - ys.length)
            (trajDrop (k := k) ys.length hN
              (trajGluePrefix (k := k) a ys N hN zs)) i j := hSplit
      _ = (prefixWordState (k := k) a ys).counts.counts i j +
          (residualStateOfPrefix (k := k) a ys eN).counts.counts i j := by
              rw [← hPrefixCount, hResidualCount]
      _ = (prefixWordState (k := k) a ys).counts.counts i j +
          (eN.counts.counts i j - (prefixWordState (k := k) a ys).counts.counts i j) := by
              rfl
      _ = eN.counts.counts i j := by
              exact Nat.add_sub_of_le (hle i j)
  · have hLastDrop :
        (trajGluePrefix (k := k) a ys N hN zs) (Fin.last N) =
          zs (Fin.last (N - ys.length)) := by
      have hlastIdx :
          (Fin.last N : Fin (N + 1)) =
            ⟨(Fin.last (N - ys.length)).1 + ys.length, by
              have hlast := (Fin.last (N - ys.length)).2
              omega⟩ := by
        apply Fin.ext
        simp [Nat.sub_add_cancel hN]
      calc
        (trajGluePrefix (k := k) a ys N hN zs) (Fin.last N)
            = trajDrop (k := k) ys.length hN
                (trajGluePrefix (k := k) a ys N hN zs) (Fin.last (N - ys.length)) := by
                    rw [trajDrop, hlastIdx]
        _ = zs (Fin.last (N - ys.length)) := by
              simpa using congrArg
                (fun f : Traj k (N - ys.length) => f (Fin.last (N - ys.length))) hDrop
    have hLastResidual :
        zs (Fin.last (N - ys.length)) = eN.last := by
      simpa [stateOfTraj, residualStateOfPrefix] using congrArg MarkovState.last hz
    calc
      (stateOfTraj (k := k) (trajGluePrefix (k := k) a ys N hN zs)).last
          = (trajGluePrefix (k := k) a ys N hN zs) (Fin.last N) := by
              rfl
      _ = zs (Fin.last (N - ys.length)) := hLastDrop
      _ = eN.last := hLastResidual

lemma mem_fiberPrefixSubset_of_mem_fiber_residualStateOfPrefix
    {a : Fin k} {ys : List (Fin k)} {N : ℕ} {hN : ys.length ≤ N}
    {eN : MarkovState k} {zs : Traj k (N - ys.length)}
    (hzs : zs ∈ fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN))
    (hstart : eN.start = a)
    (hle : ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j) :
    trajGluePrefix (k := k) a ys N hN zs ∈
      fiberPrefixSubset (k := k) a ys N hN eN := by
  have hz :
      stateOfTraj (k := k) zs = residualStateOfPrefix (k := k) a ys eN :=
    (Finset.mem_filter.1 hzs).2
  have hState :
      stateOfTraj (k := k) (trajGluePrefix (k := k) a ys N hN zs) = eN :=
    stateOfTraj_trajGluePrefix_eq_of_stateOfTraj_eq_residualStateOfPrefix
      (k := k) (hN := hN) hz hstart hle
  have hz0 :
      zs 0 = (prefixWordState (k := k) a ys).last := by
    simpa [stateOfTraj, residualStateOfPrefix] using congrArg MarkovState.start hz
  have hPrefix :
      trajPrefix (k := k) (n := ys.length) (N := N) hN
          (trajGluePrefix (k := k) a ys N hN zs) =
        wordTraj (k := k) a ys :=
    trajPrefix_trajGluePrefix_eq_wordTraj (k := k) (hN := hN) hz0
  refine (mem_fiberPrefixSubset_iff (k := k) a ys N hN eN _).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.mem_filter.2 ⟨by simp [trajFinset], hState⟩
  · have hStart :
        trajPrefix (k := k) (n := ys.length) (N := N) hN
            (trajGluePrefix (k := k) a ys N hN zs) 0 =
          wordTraj (k := k) a ys 0 := by
      simpa using congrArg (fun f : Traj k ys.length => f 0) hPrefix
    simpa [trajPrefix, wordTraj] using hStart
  · intro j
    have hStep :
        trajPrefix (k := k) (n := ys.length) (N := N) hN
            (trajGluePrefix (k := k) a ys N hN zs) (Fin.succ j) =
          wordTraj (k := k) a ys (Fin.succ j) := by
      simpa using congrArg (fun f : Traj k ys.length => f (Fin.succ j)) hPrefix
    simpa [trajPrefix, wordTraj, Fin.castLE] using hStep

/-- Residual suffix trajectories obtained by deleting the prescribed prefix
`a :: ys` from members of the exact-prefix subset inside a fixed evidence fiber. -/
def fiberPrefixResidualSubset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    Finset (Traj k (N - ys.length)) :=
  (fiberPrefixSubset (k := k) a ys N hN eN).image
    (trajDrop (k := k) ys.length hN)

lemma fiberPrefixResidualSubset_eq_fiber_residualStateOfPrefix
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hstart : eN.start = a)
    (hle : ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j) :
    fiberPrefixResidualSubset (k := k) a ys N hN eN =
      fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN) := by
  ext zs
  constructor
  · intro hzs
    rcases Finset.mem_image.1 hzs with ⟨xs, hxs, rfl⟩
    refine Finset.mem_filter.2 ⟨by simp [trajFinset], ?_⟩
    exact stateOfTraj_trajDrop_eq_residualStateOfPrefix_of_mem_fiberPrefixSubset
      (k := k) hxs
  · intro hzs
    refine Finset.mem_image.2 ?_
    refine ⟨trajGluePrefix (k := k) a ys N hN zs, ?_, ?_⟩
    · exact mem_fiberPrefixSubset_of_mem_fiber_residualStateOfPrefix
        (k := k) (hN := hN) hzs hstart hle
    · exact trajDrop_trajGluePrefix (k := k) a ys N hN zs

lemma fiberPrefixResidualSubset_eq_fiber_residualStateOfPrefix_of_mem_stateFinset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (heN : eN ∈ stateFinset k N)
    (hres : residualStateOfPrefix (k := k) a ys eN ∈ stateFinset k (N - ys.length))
    (hstart : eN.start = a) :
    fiberPrefixResidualSubset (k := k) a ys N hN eN =
      fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN) := by
  exact fiberPrefixResidualSubset_eq_fiber_residualStateOfPrefix
    (k := k) a ys N hN eN hstart
    (prefixWordState_counts_le_of_residualState_mem_stateFinset
      (k := k) (N := N) a ys hN heN hres)

lemma card_fiberPrefixResidualSubset_eq_card_fiber_residualStateOfPrefix
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hstart : eN.start = a)
    (hle : ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j) :
    (fiberPrefixResidualSubset (k := k) a ys N hN eN).card =
      (fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN)).card := by
  rw [fiberPrefixResidualSubset_eq_fiber_residualStateOfPrefix
    (k := k) a ys N hN eN hstart hle]

lemma trajDrop_injOn_fiberPrefixSubset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    Set.InjOn (trajDrop (k := k) ys.length hN)
      ↑(fiberPrefixSubset (k := k) a ys N hN eN) := by
  intro xs₁ hx₁ xs₂ hx₂ hdrop
  rcases (mem_fiberPrefixSubset_iff
      (k := k) a ys N hN eN xs₁).1 hx₁ with ⟨_, hstart₁, hprefix₁⟩
  rcases (mem_fiberPrefixSubset_iff
      (k := k) a ys N hN eN xs₂).1 hx₂ with ⟨_, hstart₂, hprefix₂⟩
  funext i
  by_cases hi : i.1 < ys.length
  · cases i using Fin.cases with
    | zero =>
        exact hstart₁.trans hstart₂.symm
    | succ j =>
        have hj : j.1 < ys.length := Nat.lt_of_succ_lt hi
        exact (hprefix₁ ⟨j.1, hj⟩).trans (hprefix₂ ⟨j.1, hj⟩).symm
  · have hge : ys.length ≤ i.1 := Nat.le_of_not_lt hi
    let j : Fin (N - ys.length + 1) :=
      ⟨i.1 - ys.length, by
        have hi' := i.2
        omega⟩
    simpa [trajDrop, j, Nat.sub_add_cancel hge] using congrArg (fun f => f j) hdrop

lemma card_fiberPrefixResidualSubset_eq_card_fiberPrefixSubset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    (fiberPrefixResidualSubset (k := k) a ys N hN eN).card =
      (fiberPrefixSubset (k := k) a ys N hN eN).card := by
  exact (Finset.card_image_iff).2
    (trajDrop_injOn_fiberPrefixSubset (k := k) a ys N hN eN)

/-- Residual-suffix counting formula: the filtered Euler-trail count attached to
the exact prefix event is equally the cardinality of the residual suffix event
times the universal copy-permutation factor of `graphOfState eN`. This is the
honest finite precursor to a later canonical residual-state / residual-graph
formula. -/
lemma eulerTrailFinset_card_filter_fiberPrefixSubset_eq_residualSubset_card_mul
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hs : eN ∈ stateFinset k N) :
    ((eulerTrailFinset
        (graphOfState eN) eN.start eN.last).filter
      (fun f =>
        castTraj
            (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
            (trailVertexSeq
              (graphOfState eN) eN.start f) ∈
          fiberPrefixSubset (k := k) a ys N hN eN)).card =
      (fiberPrefixResidualSubset (k := k) a ys N hN eN).card *
        ∏ a : Fin k, ∏ b : Fin k, (graphOfState eN a b).factorial := by
  rw [card_fiberPrefixResidualSubset_eq_card_fiberPrefixSubset (k := k) a ys N hN eN]
  exact eulerTrailFinset_card_filter_fiberPrefixSubset
    (k := k) a ys N hN eN hs

lemma eulerTrailFinset_card_filter_fiberPrefixSubset_eq_residualFiber_card_mul
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hs : eN ∈ stateFinset k N)
    (hstart : eN.start = a)
    (hle : ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j) :
    ((eulerTrailFinset
        (graphOfState eN) eN.start eN.last).filter
      (fun f =>
        castTraj
            (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
            (trailVertexSeq
              (graphOfState eN) eN.start f) ∈
          fiberPrefixSubset (k := k) a ys N hN eN)).card =
      (fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN)).card *
        ∏ a : Fin k, ∏ b : Fin k, (graphOfState eN a b).factorial := by
  rw [← card_fiberPrefixResidualSubset_eq_card_fiber_residualStateOfPrefix
    (k := k) a ys N hN eN hstart hle]
  exact eulerTrailFinset_card_filter_fiberPrefixSubset_eq_residualSubset_card_mul
    (k := k) a ys N hN eN hs

lemma eulerTrailFinset_card_filter_fiberPrefixSubset_eq_residualFiber_card_mul_of_mem_stateFinset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hs : eN ∈ stateFinset k N)
    (hres : residualStateOfPrefix (k := k) a ys eN ∈ stateFinset k (N - ys.length))
    (hstart : eN.start = a) :
    ((eulerTrailFinset
        (graphOfState eN) eN.start eN.last).filter
      (fun f =>
        castTraj
            (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
            (trailVertexSeq
              (graphOfState eN) eN.start f) ∈
          fiberPrefixSubset (k := k) a ys N hN eN)).card =
      (fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN)).card *
        ∏ a : Fin k, ∏ b : Fin k, (graphOfState eN a b).factorial := by
  exact eulerTrailFinset_card_filter_fiberPrefixSubset_eq_residualFiber_card_mul
    (k := k) a ys N hN eN hs hstart
    (prefixWordState_counts_le_of_residualState_mem_stateFinset
      (k := k) (N := N) a ys hN hs hres)

/-! ## Section 2d: Exact fixed-fiber prefix ratio

We now package the exact finite conditional-prefix fraction as a function of the
evidence state itself. This is the honest finite object that will later be
averaged over evidence classes. -/

/-- Compatibility predicate for the exact finite prefix-ratio function:
the ambient evidence must live at horizon `N`, start at `a`, and admit the
canonical residual evidence after deleting the prescribed prefix. -/
def prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (_hN : ys.length ≤ N) (eN : MarkovState k) : Prop :=
  eN ∈ stateFinset k N ∧
    eN.start = a ∧
      residualStateOfPrefix (k := k) a ys eN ∈ stateFinset k (N - ys.length)

/-- Exact fixed-fiber prefix ratio as a function of the evidence state. On a
compatible evidence class, it is the residual-fiber/full-fiber cardinality
ratio; otherwise it is defined to be `0`. -/
noncomputable def prefixRatioFn
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : ℚ :=
  by
    classical
    exact if hcomp : prefixCompatibleState (k := k) a ys N hN eN then
      ((fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN)).card : ℚ) /
        (fiber k N eN).card
    else 0

@[simp] lemma prefixRatioFn_eq_zero_of_not_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : ¬ prefixCompatibleState (k := k) a ys N hN eN) :
    prefixRatioFn (k := k) a ys N hN eN = 0 := by
  classical
  simp [prefixRatioFn, hcomp]

lemma prefixRatioFn_eq_residualFiber_ratio_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixRatioFn (k := k) a ys N hN eN =
      ((fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN)).card : ℚ) /
        (fiber k N eN).card := by
  classical
  simp [prefixRatioFn, hcomp]

lemma prefixRatioFn_eq_fiberPrefixSubset_ratio_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixRatioFn (k := k) a ys N hN eN =
      ((fiberPrefixSubset (k := k) a ys N hN eN).card : ℚ) /
        (fiber k N eN).card := by
  rcases hcomp with ⟨heN, hstart, hres⟩
  calc
    prefixRatioFn (k := k) a ys N hN eN
        = ((fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN)).card : ℚ) /
            (fiber k N eN).card := by
              exact prefixRatioFn_eq_residualFiber_ratio_of_prefixCompatibleState
                (k := k) a ys N hN eN ⟨heN, hstart, hres⟩
    _ = ((fiberPrefixResidualSubset (k := k) a ys N hN eN).card : ℚ) /
          (fiber k N eN).card := by
            rw [card_fiberPrefixResidualSubset_eq_card_fiber_residualStateOfPrefix
              (k := k) a ys N hN eN hstart
              (prefixWordState_counts_le_of_residualState_mem_stateFinset
                (k := k) (N := N) a ys hN heN hres)]
    _ = ((fiberPrefixSubset (k := k) a ys N hN eN).card : ℚ) /
          (fiber k N eN).card := by
            rw [card_fiberPrefixResidualSubset_eq_card_fiberPrefixSubset (k := k) a ys N hN eN]

lemma prefixRatioFn_eq_eulerTrail_ratio_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixRatioFn (k := k) a ys N hN eN =
      (((eulerTrailFinset
            (graphOfState eN) eN.start eN.last).filter
          (fun f =>
            castTraj
                (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset
                  (k := k) hcomp.1)
                (trailVertexSeq
                  (graphOfState eN) eN.start f) ∈
              fiberPrefixSubset (k := k) a ys N hN eN)).card : ℚ) /
        (eulerTrailFinset (graphOfState eN) eN.start eN.last).card := by
  calc
    prefixRatioFn (k := k) a ys N hN eN
        = ((fiberPrefixSubset (k := k) a ys N hN eN).card : ℚ) /
            (fiber k N eN).card := by
              exact prefixRatioFn_eq_fiberPrefixSubset_ratio_of_prefixCompatibleState
                (k := k) a ys N hN eN hcomp
    _ = (((eulerTrailFinset
              (graphOfState eN) eN.start eN.last).filter
            (fun f =>
              castTraj
                  (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset
                    (k := k) hcomp.1)
                  (trailVertexSeq
                    (graphOfState eN) eN.start f) ∈
                fiberPrefixSubset (k := k) a ys N hN eN)).card : ℚ) /
          (eulerTrailFinset (graphOfState eN) eN.start eN.last).card := by
            exact rat_card_ratio_fiberPrefixSubset_eq_eulerTrail_ratio
              (k := k) a ys N hN eN hcomp.1

lemma prefixCompatibleState_of_mem_fiberPrefixSubset
    {a : Fin k} {ys : List (Fin k)} {N : ℕ} {hN : ys.length ≤ N}
    {eN : MarkovState k} {xs : Traj k N}
    (hxs : xs ∈ fiberPrefixSubset (k := k) a ys N hN eN) :
    prefixCompatibleState (k := k) a ys N hN eN := by
  have hxsFiber : xs ∈ fiber k N eN :=
    (mem_fiberPrefixSubset_iff (k := k) a ys N hN eN xs).1 hxs |>.1
  have hFiber : stateOfTraj (k := k) xs = eN :=
    (Finset.mem_filter.1 hxsFiber).2
  rcases (mem_fiberPrefixSubset_iff (k := k) a ys N hN eN xs).1 hxs with
    ⟨_, hstartXs, _⟩
  have heN : eN ∈ stateFinset k N := by
    simpa [hFiber] using stateOfTraj_mem_stateFinset (k := k) (xs := xs)
  have hstart : eN.start = a := by
    calc
      eN.start = xs 0 := by
        simpa [stateOfTraj] using congrArg MarkovState.start hFiber.symm
      _ = a := hstartXs
  have hresEq :
      stateOfTraj (k := k) (trajDrop (k := k) ys.length hN xs) =
        residualStateOfPrefix (k := k) a ys eN :=
    stateOfTraj_trajDrop_eq_residualStateOfPrefix_of_mem_fiberPrefixSubset
      (k := k) hxs
  have hres :
      residualStateOfPrefix (k := k) a ys eN ∈ stateFinset k (N - ys.length) := by
    simpa [hresEq] using
      stateOfTraj_mem_stateFinset
        (k := k) (xs := trajDrop (k := k) ys.length hN xs)
  exact ⟨heN, hstart, hres⟩

lemma prefixRatioFn_eq_fiberPrefixSubset_ratio_of_mem_fiberPrefixSubset
    {a : Fin k} {ys : List (Fin k)} {N : ℕ} {hN : ys.length ≤ N}
    {eN : MarkovState k} {xs : Traj k N}
    (hxs : xs ∈ fiberPrefixSubset (k := k) a ys N hN eN) :
    prefixRatioFn (k := k) a ys N hN eN =
      ((fiberPrefixSubset (k := k) a ys N hN eN).card : ℚ) /
        (fiber k N eN).card := by
  exact prefixRatioFn_eq_fiberPrefixSubset_ratio_of_prefixCompatibleState
    (k := k) a ys N hN eN
    (prefixCompatibleState_of_mem_fiberPrefixSubset (k := k) hxs)

/-! ## Section 2e: Exact zero cases and finite prefix partitions

We now package the incompatible evidence classes as honest empty sets, then prove
the finite-horizon partition theorem for exact prefix events.  The latter is the
clean evidence-state decomposition needed before turning the fixed-fiber ratio
into an actual expectation identity. -/

@[simp] lemma trajToList_wordTraj
    (a : Fin k) (ys : List (Fin k)) :
    trajToList (k := k) (wordTraj (k := k) a ys) = a :: ys := by
  have hword :
      wordTraj (k := k) a ys = List.get (a :: ys) := by
    funext j
    simpa [wordTraj] using
      (List.getD_eq_get (l := a :: ys) (d := a) j)
  rw [trajToList, hword]
  exact List.ofFn_get (a :: ys)

lemma fiberPrefixSubset_eq_empty_of_not_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : ¬ prefixCompatibleState (k := k) a ys N hN eN) :
    fiberPrefixSubset (k := k) a ys N hN eN = ∅ := by
  ext xs
  constructor
  · intro hxs
    exact (hcomp (prefixCompatibleState_of_mem_fiberPrefixSubset (k := k) hxs)).elim
  · intro hxs
    simp at hxs

lemma fiberPrefixSubset_card_eq_zero_of_not_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : ¬ prefixCompatibleState (k := k) a ys N hN eN) :
    (fiberPrefixSubset (k := k) a ys N hN eN).card = 0 := by
  simp [fiberPrefixSubset_eq_empty_of_not_prefixCompatibleState
    (k := k) a ys N hN eN hcomp]

lemma fiberPrefixSubset_eq_empty_of_start_ne
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hstart : eN.start ≠ a) :
    fiberPrefixSubset (k := k) a ys N hN eN = ∅ := by
  refine fiberPrefixSubset_eq_empty_of_not_prefixCompatibleState
    (k := k) a ys N hN eN ?_
  intro hcomp
  exact hstart hcomp.2.1

lemma fiberPrefixSubset_eq_empty_of_residualState_not_mem_stateFinset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hres :
      residualStateOfPrefix (k := k) a ys eN ∉ stateFinset k (N - ys.length)) :
    fiberPrefixSubset (k := k) a ys N hN eN = ∅ := by
  refine fiberPrefixSubset_eq_empty_of_not_prefixCompatibleState
    (k := k) a ys N hN eN ?_
  intro hcomp
  exact hres hcomp.2.2

lemma prefixRatioFn_eq_fiberPrefixSubset_ratio
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixRatioFn (k := k) a ys N hN eN =
      ((fiberPrefixSubset (k := k) a ys N hN eN).card : ℚ) /
        (fiber k N eN).card := by
  by_cases hcomp : prefixCompatibleState (k := k) a ys N hN eN
  · exact prefixRatioFn_eq_fiberPrefixSubset_ratio_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp
  · rw [prefixRatioFn_eq_zero_of_not_prefixCompatibleState
      (k := k) a ys N hN eN hcomp]
    rw [fiberPrefixSubset_card_eq_zero_of_not_prefixCompatibleState
      (k := k) a ys N hN eN hcomp]
    simp

/-- The full horizon-`N` exact-prefix event, before partitioning by evidence
state. -/
def prefixTrajSet
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) :
    Finset (Traj k N) :=
  (trajFinset k N).filter (fun xs =>
    xs ⟨0, Nat.zero_lt_succ N⟩ = a ∧
    ∀ j : Fin ys.length,
      xs ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩ = ys.get j)

lemma mem_prefixTrajSet_iff
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (xs : Traj k N) :
    xs ∈ prefixTrajSet (k := k) a ys N hN ↔
      xs ⟨0, Nat.zero_lt_succ N⟩ = a ∧
      (∀ j : Fin ys.length,
        xs ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩ = ys.get j) := by
  simp [prefixTrajSet, trajFinset]

lemma prefixTrajSet_eq_singleton_wordTraj
    (a : Fin k) (ys : List (Fin k)) :
    prefixTrajSet (k := k) a ys ys.length le_rfl =
      {wordTraj (k := k) a ys} := by
  ext xs
  constructor
  · intro hxs
    rcases (mem_prefixTrajSet_iff
      (k := k) a ys ys.length le_rfl xs).1 hxs with
      ⟨hstart, hstep⟩
    have hEq : xs = wordTraj (k := k) a ys := by
      funext i
      cases i using Fin.cases with
      | zero =>
          simpa [wordTraj] using hstart
      | succ j =>
          rw [show (Fin.succ j) = (⟨↑j + 1, by omega⟩ : Fin (ys.length + 1)) from rfl]
          simpa [wordTraj] using hstep j
    simp [hEq]
  · intro hxs
    simp only [Finset.mem_singleton] at hxs
    subst hxs
    refine (mem_prefixTrajSet_iff
      (k := k) a ys ys.length le_rfl (wordTraj (k := k) a ys)).2 ?_
    refine ⟨by simp [wordTraj], ?_⟩
    intro j
    simp [wordTraj]

lemma prefixTrajSet_succ_eq_biUnion_snoc
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) :
    prefixTrajSet (k := k) a ys (N + 1) (Nat.le_trans hN (Nat.le_succ N)) =
      (Finset.univ : Finset (Fin k)).biUnion
        (fun b => (prefixTrajSet (k := k) a ys N hN).image
          (fun xs => trajSnoc (k := k) xs b)) := by
  classical
  ext zs
  constructor
  · intro hzs
    rcases (mem_prefixTrajSet_iff
      (k := k) a ys (N + 1) (Nat.le_trans hN (Nat.le_succ N)) zs).1 hzs with
      ⟨hz0, hzstep⟩
    refine Finset.mem_biUnion.2 ?_
    refine ⟨zs (Fin.last (N + 1)), by simp, ?_⟩
    refine Finset.mem_image.2 ?_
    refine ⟨trajInit (k := k) zs, ?_, trajSnoc_trajInit (k := k) zs⟩
    refine (mem_prefixTrajSet_iff (k := k) a ys N hN (trajInit (k := k) zs)).2 ?_
    refine ⟨by simpa [trajInit] using hz0, ?_⟩
    intro j
    let iN : Fin (N + 1) :=
      ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩
    have hi :
        Fin.castSucc iN =
          ⟨j.1 + 1,
            Nat.succ_lt_succ
              (Nat.lt_of_lt_of_le j.2 (Nat.le_trans hN (Nat.le_succ N)))⟩ := by
      ext
      simp [iN]
    calc
      trajInit (k := k) zs iN = zs (Fin.castSucc iN) := by
        rfl
      _ = zs ⟨j.1 + 1,
            Nat.succ_lt_succ
              (Nat.lt_of_lt_of_le j.2 (Nat.le_trans hN (Nat.le_succ N)))⟩ := by
            rw [hi]
      _ = ys.get j := hzstep j
  · intro hzs
    rcases Finset.mem_biUnion.1 hzs with ⟨b, _, hzs⟩
    rcases Finset.mem_image.1 hzs with ⟨xs, hxs, rfl⟩
    rcases (mem_prefixTrajSet_iff (k := k) a ys N hN xs).1 hxs with
      ⟨hx0, hxstep⟩
    refine (mem_prefixTrajSet_iff
      (k := k) a ys (N + 1) (Nat.le_trans hN (Nat.le_succ N))
      (trajSnoc (k := k) xs b)).2 ?_
    refine ⟨by simpa [trajSnoc] using hx0, ?_⟩
    intro j
    let iN : Fin (N + 1) :=
      ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hN)⟩
    have hi :
        Fin.castSucc iN =
          ⟨j.1 + 1,
            Nat.succ_lt_succ
              (Nat.lt_of_lt_of_le j.2 (Nat.le_trans hN (Nat.le_succ N)))⟩ := by
      ext
      simp [iN]
    calc
      trajSnoc (k := k) xs b
          ⟨j.1 + 1,
            Nat.succ_lt_succ
              (Nat.lt_of_lt_of_le j.2 (Nat.le_trans hN (Nat.le_succ N)))⟩
          = trajSnoc (k := k) xs b (Fin.castSucc iN) := by
              rw [← hi]
      _ = xs iN := by
            simp [trajSnoc]
      _ = ys.get j := hxstep j

lemma pairwiseDisjoint_prefixTrajSet_image_trajSnoc
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) :
    Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin k)))
      (fun b =>
        (prefixTrajSet (k := k) a ys N hN).image
          (fun xs => trajSnoc (k := k) xs b)) := by
  intro b _ b' _ hne
  refine Finset.disjoint_left.2 ?_
  intro zs hzs hzsp
  rcases Finset.mem_image.1 hzs with ⟨xs, _, rfl⟩
  rcases Finset.mem_image.1 hzsp with ⟨xs', _, hEq⟩
  have hlast : b' = b := by
    simpa [trajSnoc] using
      congrArg (fun f : Traj k (N + 1) => f (Fin.last (N + 1))) hEq
  exact hne hlast.symm

lemma sum_mu_prefixTrajSet_eq_prefix_aux
    (μ : PrefixMeasure (Fin k))
    (a : Fin k) (ys : List (Fin k)) :
    ∀ r : ℕ,
      (∑ xs ∈ prefixTrajSet (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r),
        μ (trajToList (k := k) xs)) = μ (a :: ys)
  | 0 => by
      simpa using
        (show
          (∑ xs ∈ prefixTrajSet (k := k) a ys ys.length le_rfl,
            μ (trajToList (k := k) xs)) = μ (a :: ys) by
          rw [prefixTrajSet_eq_singleton_wordTraj (k := k) a ys]
          simp [trajToList_wordTraj])
  | r + 1 => by
      let N := ys.length + r
      have hN : ys.length ≤ N := Nat.le_add_right ys.length r
      have hbi :
          (∑ zs ∈ (Finset.univ : Finset (Fin k)).biUnion
              (fun b =>
                (prefixTrajSet (k := k) a ys N hN).image
                  (fun xs => trajSnoc (k := k) xs b)),
            μ (trajToList (k := k) zs)) =
            ∑ b : Fin k,
              ∑ zs ∈ (prefixTrajSet (k := k) a ys N hN).image
                  (fun xs => trajSnoc (k := k) xs b),
                μ (trajToList (k := k) zs) := by
        simpa using
          (Finset.sum_biUnion
            (s := (Finset.univ : Finset (Fin k)))
            (t := fun b =>
              (prefixTrajSet (k := k) a ys N hN).image
                (fun xs => trajSnoc (k := k) xs b))
            (f := fun zs => μ (trajToList (k := k) zs))
            (hs := pairwiseDisjoint_prefixTrajSet_image_trajSnoc
              (k := k) a ys N hN))
      calc
        (∑ zs ∈ prefixTrajSet (k := k) a ys (N + 1)
            (Nat.le_trans hN (Nat.le_succ N)),
          μ (trajToList (k := k) zs))
            =
          (∑ zs ∈ (Finset.univ : Finset (Fin k)).biUnion
              (fun b =>
                (prefixTrajSet (k := k) a ys N hN).image
                  (fun xs => trajSnoc (k := k) xs b)),
            μ (trajToList (k := k) zs)) := by
              rw [prefixTrajSet_succ_eq_biUnion_snoc (k := k) a ys N hN]
        _ =
          ∑ b : Fin k,
            ∑ zs ∈ (prefixTrajSet (k := k) a ys N hN).image
                (fun xs => trajSnoc (k := k) xs b),
              μ (trajToList (k := k) zs) := hbi
        _ =
          ∑ b : Fin k,
            ∑ xs ∈ prefixTrajSet (k := k) a ys N hN,
              μ (trajToList (k := k) (trajSnoc (k := k) xs b)) := by
                refine Fintype.sum_congr
                  (fun b : Fin k =>
                    ∑ zs ∈ (prefixTrajSet (k := k) a ys N hN).image
                        (fun xs => trajSnoc (k := k) xs b),
                      μ (trajToList (k := k) zs))
                  (fun b : Fin k =>
                    ∑ xs ∈ prefixTrajSet (k := k) a ys N hN,
                      μ (trajToList (k := k) (trajSnoc (k := k) xs b))) ?_
                intro b
                simpa using
                  (Finset.sum_image
                    (s := prefixTrajSet (k := k) a ys N hN)
                    (g := fun xs => trajSnoc (k := k) xs b)
                    (f := fun zs => μ (trajToList (k := k) zs))
                    (show Set.InjOn (fun xs => trajSnoc (k := k) xs b)
                      (↑(prefixTrajSet (k := k) a ys N hN) : Set (Traj k N)) from
                      (trajSnoc_inj (k := k) b).injOn))
        _ =
          ∑ xs ∈ prefixTrajSet (k := k) a ys N hN,
            ∑ b : Fin k,
              μ (trajToList (k := k) (trajSnoc (k := k) xs b)) := by
                simpa using
                  (Finset.sum_comm
                    (s := (Finset.univ : Finset (Fin k)))
                    (t := prefixTrajSet (k := k) a ys N hN)
                    (f := fun b xs =>
                      μ (trajToList (k := k) (trajSnoc (k := k) xs b))))
        _ =
          ∑ xs ∈ prefixTrajSet (k := k) a ys N hN,
            ∑ b : Fin k, μ (trajToList (k := k) xs ++ [b]) := by
                refine Finset.sum_congr rfl ?_
                intro xs hxs
                simp [trajToList_trajSnoc]
        _ =
          ∑ xs ∈ prefixTrajSet (k := k) a ys N hN,
            μ (trajToList (k := k) xs) := by
              refine Finset.sum_congr rfl ?_
              intro xs hxs
              simpa using μ.additive' (trajToList (k := k) xs)
        _ = μ (a :: ys) := by
              simpa [N] using
                (sum_mu_prefixTrajSet_eq_prefix_aux
                  (μ := μ) (a := a) (ys := ys) r)

lemma prefixTrajSet_eq_biUnion_fiberPrefixSubset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) :
    prefixTrajSet (k := k) a ys N hN =
      (stateFinset k N).biUnion
        (fun eN => fiberPrefixSubset (k := k) a ys N hN eN) := by
  classical
  ext xs
  constructor
  · intro hxs
    refine Finset.mem_biUnion.2 ?_
    refine ⟨stateOfTraj (k := k) xs, stateOfTraj_mem_stateFinset (k := k) xs, ?_⟩
    rcases (mem_prefixTrajSet_iff (k := k) a ys N hN xs).1 hxs with
      ⟨hstart, hstep⟩
    refine (mem_fiberPrefixSubset_iff
      (k := k) a ys N hN (stateOfTraj (k := k) xs) xs).2 ?_
    refine ⟨Finset.mem_filter.2 ⟨by simp [trajFinset], rfl⟩, hstart, hstep⟩
  · intro hxs
    rcases Finset.mem_biUnion.1 hxs with ⟨eN, _, hxs⟩
    rcases (mem_fiberPrefixSubset_iff (k := k) a ys N hN eN xs).1 hxs with
      ⟨_, hstart, hstep⟩
    exact (mem_prefixTrajSet_iff (k := k) a ys N hN xs).2 ⟨hstart, hstep⟩

lemma pairwiseDisjoint_fiberPrefixSubset
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) :
    Set.PairwiseDisjoint
      (↑(stateFinset k N))
      (fun eN => fiberPrefixSubset (k := k) a ys N hN eN) := by
  intro e _ e' _ hne
  refine Finset.disjoint_left.2 ?_
  intro xs hxs hxs'
  have hFiber :
      xs ∈ fiber k N e :=
    (mem_fiberPrefixSubset_iff (k := k) a ys N hN e xs).1 hxs |>.1
  have hFiber' :
      xs ∈ fiber k N e' :=
    (mem_fiberPrefixSubset_iff (k := k) a ys N hN e' xs).1 hxs' |>.1
  have hs : stateOfTraj (k := k) xs = e :=
    (Finset.mem_filter.1 hFiber).2
  have hs' : stateOfTraj (k := k) xs = e' :=
    (Finset.mem_filter.1 hFiber').2
  exact hne (hs.symm.trans hs')

lemma sum_sum_mu_fiberPrefixSubset_eq_prefix_aux
    (μ : PrefixMeasure (Fin k))
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) :
    (∑ eN ∈ stateFinset k (ys.length + r),
      ∑ xs ∈ fiberPrefixSubset (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r) eN,
        μ (trajToList (k := k) xs)) = μ (a :: ys) := by
  classical
  have hbi :
      (∑ xs ∈ (stateFinset k (ys.length + r)).biUnion
          (fun eN => fiberPrefixSubset (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r) eN),
        μ (trajToList (k := k) xs)) =
        ∑ eN ∈ stateFinset k (ys.length + r),
          ∑ xs ∈ fiberPrefixSubset (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r) eN,
            μ (trajToList (k := k) xs) := by
    simpa using
      (Finset.sum_biUnion
        (s := stateFinset k (ys.length + r))
        (t := fun eN => fiberPrefixSubset (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r) eN)
        (f := fun xs => μ (trajToList (k := k) xs))
        (hs := pairwiseDisjoint_fiberPrefixSubset
          (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r)))
  calc
    (∑ eN ∈ stateFinset k (ys.length + r),
      ∑ xs ∈ fiberPrefixSubset (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r) eN,
        μ (trajToList (k := k) xs))
        =
      (∑ xs ∈ (stateFinset k (ys.length + r)).biUnion
          (fun eN => fiberPrefixSubset (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r) eN),
        μ (trajToList (k := k) xs)) := hbi.symm
    _ =
      (∑ xs ∈ prefixTrajSet (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r),
        μ (trajToList (k := k) xs)) := by
          rw [prefixTrajSet_eq_biUnion_fiberPrefixSubset
            (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r)]
    _ = μ (a :: ys) :=
      sum_mu_prefixTrajSet_eq_prefix_aux (μ := μ) (a := a) (ys := ys) r

/-! ## Section 2f: Weighted evidence-state expectation and BEST-form ratio

We now connect the finite evidence-state partition to the exact ratio
`prefixRatioFn`.  First we package the mass of an evidence class, then show the
prefix-event mass on each class is exactly `prefixRatioFn × stateMass`.  This
immediately yields the weighted evidence-state expectation theorem.  Finally, on
compatible evidence classes, we rewrite `prefixRatioFn` into the full/residual
Euler-trail numerator-denominator form that prepares the later BEST expansion. -/

/-- Total `μ`-mass of a fixed evidence fiber. -/
def stateMass
    (μ : PrefixMeasure (Fin k))
    (N : ℕ) (eN : MarkovState k) : ENNReal :=
  ∑ xs ∈ fiber k N eN, μ (trajToList (k := k) xs)

lemma fiberPrefixSubset_nonempty_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    (fiberPrefixSubset (k := k) a ys N hN eN).Nonempty := by
  rcases hcomp with ⟨heN, hstart, hres⟩
  rcases fiber_nonempty_of_mem_stateFinset
      (k := k) (N := N - ys.length)
      (eN := residualStateOfPrefix (k := k) a ys eN) hres with ⟨zs, hzs⟩
  refine ⟨trajGluePrefix (k := k) a ys N hN zs, ?_⟩
  exact mem_fiberPrefixSubset_of_mem_fiber_residualStateOfPrefix
    (k := k) hzs hstart
    (prefixWordState_counts_le_of_residualState_mem_stateFinset
      (k := k) (N := N) a ys hN heN hres)

lemma stateMass_eq_card_mul_of_mem_fiber
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {N : ℕ} {eN : MarkovState k} {xs0 : Traj k N}
    (hxs0 : xs0 ∈ fiber k N eN) :
    stateMass (k := k) μ N eN =
      ((fiber k N eN).card : ENNReal) * μ (trajToList (k := k) xs0) := by
  simpa [stateMass] using
    (sum_mu_eq_card_mul_of_subset_fiber
      (k := k) (μ := μ) hμ
      (A := fiber k N eN) (xs0 := xs0)
      (fun _ hx => hx) hxs0)

/-- The exact rational `prefixRatioFn` viewed as an `ENNReal` card ratio. -/
lemma ennreal_ofReal_prefixRatioFn_eq_card_ratio_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    ENNReal.ofReal (prefixRatioFn (k := k) a ys N hN eN) =
      ((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) /
        (fiber k N eN).card := by
  have hfiber_pos : 0 < ((fiber k N eN).card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fiber_card_ne_zero_of_mem_stateFinset
        (k := k) (N := N) (eN := eN) hcomp.1)
  calc
    ENNReal.ofReal (prefixRatioFn (k := k) a ys N hN eN)
        =
      ENNReal.ofReal
        ((((fiberPrefixSubset (k := k) a ys N hN eN).card : ℚ) /
          (fiber k N eN).card : ℚ) : ℝ) := by
            rw [prefixRatioFn_eq_fiberPrefixSubset_ratio_of_prefixCompatibleState
              (k := k) a ys N hN eN hcomp]
    _ =
      ENNReal.ofReal
        (((fiberPrefixSubset (k := k) a ys N hN eN).card : ℝ) /
          ((fiber k N eN).card : ℝ)) := by
            norm_num [Rat.cast_div]
    _ =
      ((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) /
        (fiber k N eN).card := by
            rw [ENNReal.ofReal_div_of_pos hfiber_pos, ENNReal.ofReal_natCast,
              ENNReal.ofReal_natCast]

lemma ennreal_ofReal_prefixRatioFn_eq_card_ratio
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    ENNReal.ofReal (prefixRatioFn (k := k) a ys N hN eN) =
      ((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) /
        (fiber k N eN).card := by
  by_cases hcomp : prefixCompatibleState (k := k) a ys N hN eN
  · exact ennreal_ofReal_prefixRatioFn_eq_card_ratio_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp
  · rw [prefixRatioFn_eq_zero_of_not_prefixCompatibleState
      (k := k) a ys N hN eN hcomp]
    rw [fiberPrefixSubset_card_eq_zero_of_not_prefixCompatibleState
      (k := k) a ys N hN eN hcomp]
    simp

lemma sum_mu_fiberPrefixSubset_eq_prefixRatioFn_mul_stateMass
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    (∑ xs ∈ fiberPrefixSubset (k := k) a ys N hN eN,
      μ (trajToList (k := k) xs)) =
      ENNReal.ofReal (prefixRatioFn (k := k) a ys N hN eN) *
        stateMass (k := k) μ N eN := by
  by_cases hcomp : prefixCompatibleState (k := k) a ys N hN eN
  · rcases fiberPrefixSubset_nonempty_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp with ⟨xs0, hxs0⟩
    have hprefixMass :
        (∑ xs ∈ fiberPrefixSubset (k := k) a ys N hN eN,
          μ (trajToList (k := k) xs)) =
          ((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) *
            μ (trajToList (k := k) xs0) :=
      sum_mu_fiberPrefixSubset_eq_card_mul
        (k := k) (μ := μ) hμ a ys N hN eN hxs0
    have hstateMass :
        stateMass (k := k) μ N eN =
          ((fiber k N eN).card : ENNReal) * μ (trajToList (k := k) xs0) :=
      stateMass_eq_card_mul_of_mem_fiber
        (k := k) (μ := μ) hμ
        ((fiberPrefixSubset_subset_fiber (k := k) a ys N hN eN) hxs0)
    have hratio :
        ENNReal.ofReal (prefixRatioFn (k := k) a ys N hN eN) =
          ((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) /
            (fiber k N eN).card :=
      ennreal_ofReal_prefixRatioFn_eq_card_ratio_of_prefixCompatibleState
        (k := k) a ys N hN eN hcomp
    have hfiber :
        ((fiber k N eN).card : ENNReal) ≠ 0 := by
      exact_mod_cast fiber_card_ne_zero_of_mem_stateFinset
        (k := k) (N := N) (eN := eN) hcomp.1
    calc
      (∑ xs ∈ fiberPrefixSubset (k := k) a ys N hN eN,
        μ (trajToList (k := k) xs))
          =
        ((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) *
          μ (trajToList (k := k) xs0) := hprefixMass
      _ =
        (((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) /
            (fiber k N eN).card) *
          stateMass (k := k) μ N eN := by
            rw [hstateMass]
            symm
            calc
              (((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) /
                    (fiber k N eN).card) *
                  (((fiber k N eN).card : ENNReal) *
                    μ (trajToList (k := k) xs0))
                  =
                ((((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) /
                    (fiber k N eN).card) *
                  (fiber k N eN).card) *
                    μ (trajToList (k := k) xs0) := by
                      rw [mul_assoc]
              _ =
                ((fiberPrefixSubset (k := k) a ys N hN eN).card : ENNReal) *
                  μ (trajToList (k := k) xs0) := by
                    exact congrArg
                      (fun t : ENNReal => t * μ (trajToList (k := k) xs0))
                      (ENNReal.div_mul_cancel hfiber ENNReal.coe_ne_top)
      _ =
        ENNReal.ofReal (prefixRatioFn (k := k) a ys N hN eN) *
          stateMass (k := k) μ N eN := by
            rw [hratio]
  · rw [fiberPrefixSubset_eq_empty_of_not_prefixCompatibleState
      (k := k) a ys N hN eN hcomp]
    rw [prefixRatioFn_eq_zero_of_not_prefixCompatibleState
      (k := k) a ys N hN eN hcomp]
    simp [stateMass]

lemma sum_stateMass_mul_prefixRatioFn_eq_prefix_aux
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) :
    (∑ eN ∈ stateFinset k (ys.length + r),
      ENNReal.ofReal
          (prefixRatioFn (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r) eN) *
        stateMass (k := k) μ (ys.length + r) eN) = μ (a :: ys) := by
  calc
    (∑ eN ∈ stateFinset k (ys.length + r),
      ENNReal.ofReal
          (prefixRatioFn (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r) eN) *
        stateMass (k := k) μ (ys.length + r) eN)
        =
      (∑ eN ∈ stateFinset k (ys.length + r),
        ∑ xs ∈ fiberPrefixSubset (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r) eN,
          μ (trajToList (k := k) xs)) := by
            refine Finset.sum_congr rfl ?_
            intro eN heN
            symm
            exact sum_mu_fiberPrefixSubset_eq_prefixRatioFn_mul_stateMass
              (k := k) (μ := μ) hμ a ys (ys.length + r)
              (Nat.le_add_right ys.length r) eN
    _ = μ (a :: ys) :=
      sum_sum_mu_fiberPrefixSubset_eq_prefix_aux
        (μ := μ) (a := a) (ys := ys) r

/-- Product of factorial edge multiplicities in the graph attached to an
evidence state. This is the explicit combinatorial factor appearing in the
finite BEST count `|eulerTrailFinset| = |fiber| * graphFactorialWeight`. -/
def graphFactorialWeight
    (eN : MarkovState k) : ℕ :=
  ∏ a : Fin k, ∏ b : Fin k, (graphOfState eN a b).factorial

lemma graphFactorialWeight_pos
    (eN : MarkovState k) : 0 < graphFactorialWeight (k := k) eN := by
  classical
  dsimp [graphFactorialWeight]
  refine Finset.prod_pos ?_
  intro a ha
  refine Finset.prod_pos ?_
  intro b hb
  exact Nat.factorial_pos (graphOfState eN a b)

lemma graphFactorialWeight_ne_zero
    (eN : MarkovState k) : graphFactorialWeight (k := k) eN ≠ 0 :=
  Nat.ne_of_gt (graphFactorialWeight_pos (k := k) eN)

lemma prefixRatioFn_eq_fullResidualBEST_ratio_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixRatioFn (k := k) a ys N hN eN =
      (((eulerTrailFinset
            (graphOfState (residualStateOfPrefix (k := k) a ys eN))
            (residualStateOfPrefix (k := k) a ys eN).start
            (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ) *
          graphFactorialWeight (k := k) eN) /
        (((eulerTrailFinset
              (graphOfState eN) eN.start eN.last).card : ℚ) *
          graphFactorialWeight (k := k)
            (residualStateOfPrefix (k := k) a ys eN)) := by
  rcases hcomp with ⟨heN, hstart, hres⟩
  have hfiber :
      ((fiber k N eN).card : ℚ) ≠ 0 := by
    exact_mod_cast fiber_card_ne_zero_of_mem_stateFinset
      (k := k) (N := N) (eN := eN) heN
  have hfullFactor :
      (graphFactorialWeight (k := k) eN : ℚ) ≠ 0 := by
    exact_mod_cast graphFactorialWeight_ne_zero (k := k) eN
  have hresFactor :
      (graphFactorialWeight (k := k)
          (residualStateOfPrefix (k := k) a ys eN) : ℚ) ≠ 0 := by
    exact_mod_cast graphFactorialWeight_ne_zero
      (k := k) (residualStateOfPrefix (k := k) a ys eN)
  have hfullEuler :
      ((eulerTrailFinset (graphOfState eN) eN.start eN.last).card : ℚ) =
        (fiber k N eN).card * graphFactorialWeight (k := k) eN := by
    exact_mod_cast eulerTrailFinset_card_eq (k := k) eN heN
  have hresEuler :
      ((eulerTrailFinset
            (graphOfState (residualStateOfPrefix (k := k) a ys eN))
            (residualStateOfPrefix (k := k) a ys eN).start
            (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ) =
        (fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN)).card *
          graphFactorialWeight (k := k)
            (residualStateOfPrefix (k := k) a ys eN) := by
    exact_mod_cast eulerTrailFinset_card_eq
      (k := k) (residualStateOfPrefix (k := k) a ys eN) hres
  calc
    prefixRatioFn (k := k) a ys N hN eN
        =
      ((fiber k (N - ys.length) (residualStateOfPrefix (k := k) a ys eN)).card : ℚ) /
        (fiber k N eN).card := by
            exact prefixRatioFn_eq_residualFiber_ratio_of_prefixCompatibleState
              (k := k) a ys N hN eN ⟨heN, hstart, hres⟩
    _ =
      (((eulerTrailFinset
            (graphOfState (residualStateOfPrefix (k := k) a ys eN))
            (residualStateOfPrefix (k := k) a ys eN).start
            (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ) *
          graphFactorialWeight (k := k) eN) /
        (((eulerTrailFinset
              (graphOfState eN) eN.start eN.last).card : ℚ) *
          graphFactorialWeight (k := k)
            (residualStateOfPrefix (k := k) a ys eN)) := by
          rw [hresEuler, hfullEuler]
          field_simp [hfiber, hfullFactor, hresFactor]

/-! ### Hypergeometric / bridge factorization -/

/-- The exact full/residual Euler-trail ratio appearing in the finite prefix
count theorem. This is the explicit RHS of
`prefixRatioFn_eq_fullResidualBEST_ratio_of_prefixCompatibleState`. -/
def prefixBESTRatioExplicit
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (_hN : ys.length ≤ N) (eN : MarkovState k) : ℚ :=
  (((eulerTrailFinset
        (graphOfState (residualStateOfPrefix (k := k) a ys eN))
        (residualStateOfPrefix (k := k) a ys eN).start
        (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ) *
      graphFactorialWeight (k := k) eN) /
    (((eulerTrailFinset
          (graphOfState eN) eN.start eN.last).card : ℚ) *
      graphFactorialWeight (k := k)
        (residualStateOfPrefix (k := k) a ys eN))

lemma prefixRatioFn_eq_prefixBESTRatioExplicit_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixRatioFn (k := k) a ys N hN eN =
      prefixBESTRatioExplicit (k := k) a ys N hN eN := by
  simpa [prefixBESTRatioExplicit] using
    prefixRatioFn_eq_fullResidualBEST_ratio_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp

/-- Prefix edge-count of `i → j` is bounded by the total number of prefix
departures from `i`. -/
lemma prefixWordState_count_le_outdeg
    (a : Fin k) (ys : List (Fin k)) (i j : Fin k) :
    (prefixWordState (k := k) a ys).counts.counts i j ≤
      MarkovDeFinettiHardEuler.outdeg (k := k)
        (prefixWordState (k := k) a ys) i := by
  classical
  simp [MarkovDeFinettiHardEuler.outdeg, TransCounts.rowTotal]
  exact Finset.single_le_sum
    (fun j' _ => Nat.zero_le _)
    (by simp)

lemma prefixWordState_outdeg_pos_of_count_pos
    (a : Fin k) (ys : List (Fin k)) (i j : Fin k)
    (hpos : 0 < (prefixWordState (k := k) a ys).counts.counts i j) :
    0 < MarkovDeFinettiHardEuler.outdeg (k := k)
      (prefixWordState (k := k) a ys) i := by
  exact lt_of_lt_of_le hpos
    (prefixWordState_count_le_outdeg (k := k) a ys i j)

lemma prefixWordState_outdeg_le_of_counts_le
    (a : Fin k) (ys : List (Fin k))
    {eN : MarkovState k}
    (hle : ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j)
    (i : Fin k) :
    MarkovDeFinettiHardEuler.outdeg (k := k)
      (prefixWordState (k := k) a ys) i ≤
      MarkovDeFinettiHardEuler.outdeg (k := k) eN i := by
  classical
  simp [MarkovDeFinettiHardEuler.outdeg, TransCounts.rowTotal]
  refine Finset.sum_le_sum ?_
  intro j hj
  exact hle i j

lemma prefixWordState_outdeg_le_of_residualState_mem_stateFinset
    (a : Fin k) (ys : List (Fin k))
    {N : ℕ} {eN : MarkovState k}
    (hN : ys.length ≤ N)
    (heN : eN ∈ stateFinset k N)
    (hres : residualStateOfPrefix (k := k) a ys eN ∈ stateFinset k (N - ys.length))
    (i : Fin k) :
    MarkovDeFinettiHardEuler.outdeg (k := k)
      (prefixWordState (k := k) a ys) i ≤
      MarkovDeFinettiHardEuler.outdeg (k := k) eN i := by
  exact prefixWordState_outdeg_le_of_counts_le
    (k := k) a ys
    (fun i j =>
      prefixWordState_counts_le_of_residualState_mem_stateFinset
        (k := k) (a := a) (ys := ys) (N := N) (hN := hN) (eN := eN) heN hres i j)
    i

/-- Edge-level hypergeometric factor for the fixed prefix word `a :: ys`. -/
def prefixHypergeometricEdgeFactor
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k)
    (i j : Fin k) : ℚ :=
  ((((eN.counts.counts i j).descFactorial
      ((prefixWordState (k := k) a ys).counts.counts i j)) : ℕ) : ℚ) /
    (((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℚ) ^
      ((prefixWordState (k := k) a ys).counts.counts i j))

/-- Row-level correction factor for the fixed prefix word `a :: ys`. -/
def prefixHypergeometricRowCorrection
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k)
    (i : Fin k) : ℚ :=
  ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℚ) ^
      (MarkovDeFinettiHardEuler.outdeg (k := k)
        (prefixWordState (k := k) a ys) i))) /
    ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
        (MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i)) : ℕ) : ℚ)

/-- The explicit hypergeometric factor `H` for the fixed prefix word
`a :: ys`. It captures the without-replacement part of the exact prefix ratio. -/
def prefixHypergeometricFactor
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : ℚ :=
  ∏ i : Fin k,
    (∏ j : Fin k, prefixHypergeometricEdgeFactor (k := k) a ys eN i j) *
      prefixHypergeometricRowCorrection (k := k) a ys eN i

/-- The residual bridge factor `B` obtained after dividing the exact
full/residual ratio by the hypergeometric factor. -/
def prefixBridgeCorrection
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : ℚ :=
  prefixBESTRatioExplicit (k := k) a ys N hN eN /
    prefixHypergeometricFactor (k := k) a ys eN

/-- The pure Euler-trail-cardinality ratio between the residual and full graphs. -/
def prefixEulerTrailRatio
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (_hN : ys.length ≤ N) (eN : MarkovState k) : ℚ :=
  (((eulerTrailFinset
        (graphOfState (residualStateOfPrefix (k := k) a ys eN))
        (residualStateOfPrefix (k := k) a ys eN).start
        (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ) /
    ((eulerTrailFinset
          (graphOfState eN) eN.start eN.last).card : ℚ))

/-- Product of edge-level descending factorials removed by the prefix word
`a :: ys`. -/
def prefixEdgeDescFactorProduct
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : ℚ :=
  ∏ i : Fin k, ∏ j : Fin k,
    ((((eN.counts.counts i j).descFactorial
        ((prefixWordState (k := k) a ys).counts.counts i j)) : ℕ) : ℚ)

/-- Product of row-level descending factorials corresponding to the total number
of prefix departures from each row. -/
def prefixRowDescFactorialProduct
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : ℚ :=
  ∏ i : Fin k,
    ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
        (MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i)) : ℕ) : ℚ)

lemma prefixHypergeometricEdgeFactor_ne_zero_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (i j : Fin k) :
    prefixHypergeometricEdgeFactor (k := k) a ys eN i j ≠ 0 := by
  classical
  rcases hcomp with ⟨heN, _, hres⟩
  let c : ℕ := (prefixWordState (k := k) a ys).counts.counts i j
  by_cases hc : c = 0
  · have hc' :
        (prefixWordState (k := k) a ys).counts.counts i j = 0 := by
      simpa [c] using hc
    have hc'' : transCount (wordTraj (k := k) a ys) i j = 0 := by
      simpa [prefixWordState_counts] using hc'
    have hval :
        prefixHypergeometricEdgeFactor (k := k) a ys eN i j = 1 := by
      simp [prefixHypergeometricEdgeFactor, prefixWordState_counts, hc'']
    exact hval.symm ▸ (by norm_num : (1 : ℚ) ≠ 0)
  have hcpos : 0 < c := Nat.pos_iff_ne_zero.mpr hc
  have hrowPrefixPos :
      0 < MarkovDeFinettiHardEuler.outdeg (k := k)
        (prefixWordState (k := k) a ys) i := by
    simpa [c] using
      prefixWordState_outdeg_pos_of_count_pos (k := k) a ys i j hcpos
  have hrowLe :
      MarkovDeFinettiHardEuler.outdeg (k := k)
        (prefixWordState (k := k) a ys) i ≤
      MarkovDeFinettiHardEuler.outdeg (k := k) eN i :=
    prefixWordState_outdeg_le_of_residualState_mem_stateFinset
      (k := k) (a := a) (ys := ys) (N := N) (eN := eN) hN heN hres i
  have hOutPos :
      0 < MarkovDeFinettiHardEuler.outdeg (k := k) eN i :=
    lt_of_lt_of_le hrowPrefixPos hrowLe
  have hcountLe :
      c ≤ eN.counts.counts i j := by
    simpa [c] using
      prefixWordState_counts_le_of_residualState_mem_stateFinset
        (k := k) (a := a) (ys := ys) (N := N) (hN := hN) (eN := eN) heN hres i j
  have hnum :
      ((((eN.counts.counts i j).descFactorial c : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt ((Nat.descFactorial_pos).2 hcountLe)
  have hden :
      (((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℚ) ^ c) ≠ 0 := by
    exact pow_ne_zero c (by exact_mod_cast (Nat.ne_of_gt hOutPos))
  simpa [prefixHypergeometricEdgeFactor, c] using div_ne_zero hnum hden

lemma prefixHypergeometricRowCorrection_ne_zero_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (i : Fin k) :
    prefixHypergeometricRowCorrection (k := k) a ys eN i ≠ 0 := by
  classical
  rcases hcomp with ⟨heN, _, hres⟩
  let r : ℕ := MarkovDeFinettiHardEuler.outdeg (k := k)
    (prefixWordState (k := k) a ys) i
  by_cases hr : r = 0
  · have hr' :
        MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i = 0 := by
      simpa [r] using hr
    have hr'' : (prefixWordState (k := k) a ys).counts.rowTotal i = 0 := by
      simpa [MarkovDeFinettiHardEuler.outdeg, TransCounts.rowTotal] using hr'
    have hr''' : ∑ x, transCount (wordTraj (k := k) a ys) i x = 0 := by
      simpa [prefixWordState_counts, TransCounts.rowTotal] using hr''
    have hval :
        prefixHypergeometricRowCorrection (k := k) a ys eN i = 1 := by
      simp [prefixHypergeometricRowCorrection, MarkovDeFinettiHardEuler.outdeg,
        TransCounts.rowTotal, hr''']
    exact hval.symm ▸ (by norm_num : (1 : ℚ) ≠ 0)
  have hrpos : 0 < r := Nat.pos_iff_ne_zero.mpr hr
  have hrowLe :
      r ≤ MarkovDeFinettiHardEuler.outdeg (k := k) eN i := by
    simpa [r] using
      prefixWordState_outdeg_le_of_residualState_mem_stateFinset
        (k := k) (a := a) (ys := ys) (N := N) (eN := eN) hN heN hres i
  have hOutPos :
      0 < MarkovDeFinettiHardEuler.outdeg (k := k) eN i :=
    lt_of_lt_of_le hrpos hrowLe
  have hnum :
      ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℚ) ^ r)) ≠ 0 := by
    exact pow_ne_zero r (by exact_mod_cast (Nat.ne_of_gt hOutPos))
  have hden :
      (((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial r) : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt ((Nat.descFactorial_pos).2 hrowLe)
  simpa [prefixHypergeometricRowCorrection, r] using div_ne_zero hnum hden

lemma prefixHypergeometricFactor_ne_zero_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixHypergeometricFactor (k := k) a ys eN ≠ 0 := by
  classical
  unfold prefixHypergeometricFactor
  refine Finset.prod_ne_zero_iff.2 ?_
  intro i hi
  have hedge :
      (∏ j : Fin k, prefixHypergeometricEdgeFactor (k := k) a ys eN i j) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 ?_
    intro j hj
    exact prefixHypergeometricEdgeFactor_ne_zero_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp i j
  have hrow :
      prefixHypergeometricRowCorrection (k := k) a ys eN i ≠ 0 :=
    prefixHypergeometricRowCorrection_ne_zero_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp i
  exact mul_ne_zero hedge hrow

lemma prefixEulerTrailRatio_ne_zero_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixEulerTrailRatio (k := k) a ys N hN eN ≠ 0 := by
  rcases hcomp with ⟨heN, _, hres⟩
  have hresCardPos :
      0 <
        (eulerTrailFinset
          (graphOfState (residualStateOfPrefix (k := k) a ys eN))
          (residualStateOfPrefix (k := k) a ys eN).start
          (residualStateOfPrefix (k := k) a ys eN).last).card := by
    rw [eulerTrailFinset_card_eq (k := k)
      (residualStateOfPrefix (k := k) a ys eN) hres]
    exact Nat.mul_pos
      (Nat.pos_iff_ne_zero.mpr <| fiber_card_ne_zero_of_mem_stateFinset
        (k := k) (N := N - ys.length)
        (eN := residualStateOfPrefix (k := k) a ys eN) hres)
      (graphFactorialWeight_pos (k := k)
        (residualStateOfPrefix (k := k) a ys eN))
  have hfullCardPos :
      0 < (eulerTrailFinset (graphOfState eN) eN.start eN.last).card := by
    rw [eulerTrailFinset_card_eq (k := k) eN heN]
    exact Nat.mul_pos
      (Nat.pos_iff_ne_zero.mpr <|
        fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN)
      (graphFactorialWeight_pos (k := k) eN)
  have hnum :
      (((eulerTrailFinset
            (graphOfState (residualStateOfPrefix (k := k) a ys eN))
            (residualStateOfPrefix (k := k) a ys eN).start
            (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hresCardPos
  have hden :
      (((eulerTrailFinset (graphOfState eN) eN.start eN.last).card : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hfullCardPos
  simpa [prefixEulerTrailRatio] using div_ne_zero hnum hden

lemma prefixEdgeDescFactorProduct_ne_zero_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixEdgeDescFactorProduct (k := k) a ys eN ≠ 0 := by
  classical
  unfold prefixEdgeDescFactorProduct
  refine Finset.prod_ne_zero_iff.2 ?_
  intro i hi
  refine Finset.prod_ne_zero_iff.2 ?_
  intro j hj
  rcases hcomp with ⟨heN, _, hres⟩
  have hcountLe :
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j := by
    exact prefixWordState_counts_le_of_residualState_mem_stateFinset
      (k := k) (a := a) (ys := ys) (N := N) (hN := hN) (eN := eN) heN hres i j
  exact_mod_cast Nat.ne_of_gt ((Nat.descFactorial_pos).2 hcountLe)

lemma prefixRowDescFactorialProduct_ne_zero_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixRowDescFactorialProduct (k := k) a ys eN ≠ 0 := by
  classical
  unfold prefixRowDescFactorialProduct
  refine Finset.prod_ne_zero_iff.2 ?_
  intro i hi
  rcases hcomp with ⟨heN, _, hres⟩
  have hrowLe :
      MarkovDeFinettiHardEuler.outdeg (k := k)
        (prefixWordState (k := k) a ys) i ≤
      MarkovDeFinettiHardEuler.outdeg (k := k) eN i := by
    exact prefixWordState_outdeg_le_of_residualState_mem_stateFinset
      (k := k) (a := a) (ys := ys) (N := N) (eN := eN) hN heN hres i
  exact_mod_cast Nat.ne_of_gt ((Nat.descFactorial_pos).2 hrowLe)

lemma graphFactorialWeight_eq_prefixEdgeDescFactorProduct_mul_residual_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    (graphFactorialWeight (k := k) eN : ℚ) =
      prefixEdgeDescFactorProduct (k := k) a ys eN *
        graphFactorialWeight (k := k)
          (residualStateOfPrefix (k := k) a ys eN) := by
  classical
  rcases hcomp with ⟨heN, _, hres⟩
  unfold prefixEdgeDescFactorProduct
  calc
    (graphFactorialWeight (k := k) eN : ℚ)
        = ∏ a' : Fin k, ∏ b : Fin k, ((graphOfState eN a' b).factorial : ℚ) := by
            simp [graphFactorialWeight]
    _ = ∏ a' : Fin k, ∏ b : Fin k,
            (((eN.counts.counts a' b).descFactorial
                ((prefixWordState (k := k) a ys).counts.counts a' b) : ℕ) : ℚ) *
              (((graphOfState
                  (residualStateOfPrefix (k := k) a ys eN) a' b).factorial : ℚ)) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            refine Finset.prod_congr rfl ?_
            intro j hj
            have hcountLe :
                (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j := by
              exact prefixWordState_counts_le_of_residualState_mem_stateFinset
                (k := k) (a := a) (ys := ys) (N := N) (hN := hN) (eN := eN) heN hres i j
            have hfac :
                (((eN.counts.counts i j).descFactorial
                    ((prefixWordState (k := k) a ys).counts.counts i j) : ℕ) : ℚ) *
                  (((graphOfState
                      (residualStateOfPrefix (k := k) a ys eN) i j).factorial : ℚ)) =
                  (((graphOfState eN i j).factorial : ℚ)) := by
              have hfacNat :=
                Nat.factorial_mul_descFactorial hcountLe
              have hfacRat :
                  ((((eN.counts.counts i j -
                        (prefixWordState (k := k) a ys).counts.counts i j).factorial : ℕ) : ℚ)) *
                    (((eN.counts.counts i j).descFactorial
                      ((prefixWordState (k := k) a ys).counts.counts i j) : ℕ) : ℚ) =
                    (((eN.counts.counts i j).factorial : ℕ) : ℚ) := by
                exact_mod_cast hfacNat
              simpa [graphOfState, residualStateOfPrefix_counts, mul_comm, mul_left_comm,
                mul_assoc] using hfacRat
            simpa [graphOfState] using hfac.symm
    _ = (∏ a' : Fin k, ∏ b : Fin k,
            (((eN.counts.counts a' b).descFactorial
                ((prefixWordState (k := k) a ys).counts.counts a' b) : ℕ) : ℚ)) *
          (∏ a' : Fin k, ∏ b : Fin k,
            (((graphOfState
                (residualStateOfPrefix (k := k) a ys eN) a' b).factorial : ℚ))) := by
          simp [Finset.prod_mul_distrib]
    _ = prefixEdgeDescFactorProduct (k := k) a ys eN *
          graphFactorialWeight (k := k)
            (residualStateOfPrefix (k := k) a ys eN) := by
          simp [graphFactorialWeight, prefixEdgeDescFactorProduct]

lemma prefixBESTRatioExplicit_eq_prefixEulerTrailRatio_mul_prefixEdgeDescFactorProduct_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixBESTRatioExplicit (k := k) a ys N hN eN =
      prefixEulerTrailRatio (k := k) a ys N hN eN *
        prefixEdgeDescFactorProduct (k := k) a ys eN := by
  have hcomp' := hcomp
  rcases hcomp with ⟨heN, _, hres⟩
  have hresFactor :
      (graphFactorialWeight (k := k)
          (residualStateOfPrefix (k := k) a ys eN) : ℚ) ≠ 0 := by
    exact_mod_cast graphFactorialWeight_ne_zero
      (k := k) (residualStateOfPrefix (k := k) a ys eN)
  have hfullCardPos :
      0 < (eulerTrailFinset (graphOfState eN) eN.start eN.last).card := by
    rw [eulerTrailFinset_card_eq (k := k) eN heN]
    exact Nat.mul_pos
      (Nat.pos_iff_ne_zero.mpr <|
        fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN)
      (graphFactorialWeight_pos (k := k) eN)
  have hfullCard :
      (((eulerTrailFinset (graphOfState eN) eN.start eN.last).card : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hfullCardPos
  have hgraph :
      (graphFactorialWeight (k := k) eN : ℚ) /
          (graphFactorialWeight (k := k)
            (residualStateOfPrefix (k := k) a ys eN) : ℚ) =
        prefixEdgeDescFactorProduct (k := k) a ys eN := by
    have hmul :=
      graphFactorialWeight_eq_prefixEdgeDescFactorProduct_mul_residual_of_prefixCompatibleState
        (k := k) a ys N hN eN hcomp'
    exact (div_eq_iff hresFactor).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  unfold prefixBESTRatioExplicit prefixEulerTrailRatio
  have hmain :
      ((((eulerTrailFinset
              (graphOfState (residualStateOfPrefix (k := k) a ys eN))
              (residualStateOfPrefix (k := k) a ys eN).start
              (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ) *
            graphFactorialWeight (k := k) eN) /
          ((((eulerTrailFinset
                  (graphOfState eN) eN.start eN.last).card : ℚ) *
              graphFactorialWeight (k := k)
                (residualStateOfPrefix (k := k) a ys eN)))) =
        ((((eulerTrailFinset
                (graphOfState (residualStateOfPrefix (k := k) a ys eN))
                (residualStateOfPrefix (k := k) a ys eN).start
                (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ) /
            ((eulerTrailFinset
                (graphOfState eN) eN.start eN.last).card : ℚ)) *
          ((graphFactorialWeight (k := k) eN : ℚ) /
            (graphFactorialWeight (k := k)
              (residualStateOfPrefix (k := k) a ys eN) : ℚ))) := by
    field_simp [hfullCard, hresFactor]
  calc
    ((((eulerTrailFinset
            (graphOfState (residualStateOfPrefix (k := k) a ys eN))
            (residualStateOfPrefix (k := k) a ys eN).start
            (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ) *
          graphFactorialWeight (k := k) eN) /
        ((((eulerTrailFinset
                (graphOfState eN) eN.start eN.last).card : ℚ) *
            graphFactorialWeight (k := k)
              (residualStateOfPrefix (k := k) a ys eN)))) =
        ((((eulerTrailFinset
                (graphOfState (residualStateOfPrefix (k := k) a ys eN))
                (residualStateOfPrefix (k := k) a ys eN).start
                (residualStateOfPrefix (k := k) a ys eN).last).card : ℚ) /
            ((eulerTrailFinset
                (graphOfState eN) eN.start eN.last).card : ℚ)) *
          ((graphFactorialWeight (k := k) eN : ℚ) /
            (graphFactorialWeight (k := k)
              (residualStateOfPrefix (k := k) a ys eN) : ℚ))) := hmain
    _ = prefixEulerTrailRatio (k := k) a ys N hN eN *
          prefixEdgeDescFactorProduct (k := k) a ys eN := by
          simp [hgraph, prefixEulerTrailRatio]

lemma prefixHypergeometricFactor_eq_prefixEdgeDescFactorProduct_div_prefixRowDescFactorialProduct_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixHypergeometricFactor (k := k) a ys eN =
      prefixEdgeDescFactorProduct (k := k) a ys eN /
        prefixRowDescFactorialProduct (k := k) a ys eN := by
  classical
  rcases hcomp with ⟨heN, _, hres⟩
  unfold prefixHypergeometricFactor prefixEdgeDescFactorProduct prefixRowDescFactorialProduct
  calc
    ∏ i : Fin k,
        (∏ j : Fin k, prefixHypergeometricEdgeFactor (k := k) a ys eN i j) *
          prefixHypergeometricRowCorrection (k := k) a ys eN i
        = ∏ i : Fin k,
            ((∏ j : Fin k,
                ((((eN.counts.counts i j).descFactorial
                    ((prefixWordState (k := k) a ys).counts.counts i j)) : ℕ) : ℚ)) /
              ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℚ) ^
                (MarkovDeFinettiHardEuler.outdeg (k := k)
                  (prefixWordState (k := k) a ys) i))) *
              (((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℚ) ^
                  (MarkovDeFinettiHardEuler.outdeg (k := k)
                    (prefixWordState (k := k) a ys) i))) /
                ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
                    (MarkovDeFinettiHardEuler.outdeg (k := k)
                      (prefixWordState (k := k) a ys) i)) : ℕ) : ℚ))) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            have hprodDiv :
                (∏ j : Fin k, prefixHypergeometricEdgeFactor (k := k) a ys eN i j) =
                  (∏ j : Fin k,
                    ((((eN.counts.counts i j).descFactorial
                        ((prefixWordState (k := k) a ys).counts.counts i j)) : ℕ) : ℚ)) /
                    ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℚ) ^
                      (MarkovDeFinettiHardEuler.outdeg (k := k)
                        (prefixWordState (k := k) a ys) i))) := by
              simp [prefixHypergeometricEdgeFactor, Finset.prod_div_distrib,
                Finset.prod_pow_eq_pow_sum,
                MarkovDeFinettiHardEuler.outdeg, TransCounts.rowTotal]
            simp [hprodDiv, prefixHypergeometricRowCorrection]
    _ = ∏ i : Fin k,
          ((∏ j : Fin k,
              ((((eN.counts.counts i j).descFactorial
                  ((prefixWordState (k := k) a ys).counts.counts i j)) : ℕ) : ℚ)) /
            ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
                (MarkovDeFinettiHardEuler.outdeg (k := k)
                  (prefixWordState (k := k) a ys) i)) : ℕ) : ℚ)) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          let r : ℕ := MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i
          have hrowLe :
              r ≤ MarkovDeFinettiHardEuler.outdeg (k := k) eN i := by
            simpa [r] using
              prefixWordState_outdeg_le_of_residualState_mem_stateFinset
                (k := k) (a := a) (ys := ys) (N := N) (eN := eN) hN heN hres i
          have hpowNe :
              ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℚ) ^ r)) ≠ 0 := by
            by_cases hr : r = 0
            · simp [hr]
            · have hrpos : 0 < r := Nat.pos_iff_ne_zero.mpr hr
              have hOutPos :
                  0 < MarkovDeFinettiHardEuler.outdeg (k := k) eN i :=
                lt_of_lt_of_le hrpos hrowLe
              exact pow_ne_zero r (by exact_mod_cast (Nat.ne_of_gt hOutPos))
          have hrowDescNe :
              (((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial r) : ℕ) : ℚ)) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt ((Nat.descFactorial_pos).2 hrowLe)
          field_simp [hpowNe, hrowDescNe, r]
    _ = (∏ i : Fin k, ∏ j : Fin k,
            ((((eN.counts.counts i j).descFactorial
                ((prefixWordState (k := k) a ys).counts.counts i j)) : ℕ) : ℚ)) /
          (∏ i : Fin k,
            ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
                (MarkovDeFinettiHardEuler.outdeg (k := k)
                  (prefixWordState (k := k) a ys) i)) : ℕ) : ℚ)) := by
          rw [Finset.prod_div_distrib]
    _ = prefixEdgeDescFactorProduct (k := k) a ys eN /
          prefixRowDescFactorialProduct (k := k) a ys eN := by
          simp [prefixEdgeDescFactorProduct, prefixRowDescFactorialProduct]

lemma prefixBridgeCorrection_eq_prefixEulerTrailRatio_mul_prefixRowDescFactorialProduct_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixBridgeCorrection (k := k) a ys N hN eN =
      prefixEulerTrailRatio (k := k) a ys N hN eN *
        prefixRowDescFactorialProduct (k := k) a ys eN := by
  have hEdgeNe :
      prefixEdgeDescFactorProduct (k := k) a ys eN ≠ 0 :=
    prefixEdgeDescFactorProduct_ne_zero_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp
  have hRowNe :
      prefixRowDescFactorialProduct (k := k) a ys eN ≠ 0 :=
    prefixRowDescFactorialProduct_ne_zero_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp
  have hR :=
    prefixBESTRatioExplicit_eq_prefixEulerTrailRatio_mul_prefixEdgeDescFactorProduct_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp
  have hH :=
    prefixHypergeometricFactor_eq_prefixEdgeDescFactorProduct_div_prefixRowDescFactorialProduct_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp
  unfold prefixBridgeCorrection
  rw [hR, hH]
  field_simp [hEdgeNe, hRowNe]

/-- Real-valued bridge correction for asymptotic analysis. -/
def prefixBridgeCorrectionReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : ℝ :=
  (prefixBridgeCorrection (k := k) a ys N hN eN : ℝ)

/-- Real-valued Euler-trail ratio appearing in the normalized bridge factor. -/
def prefixEulerTrailRatioReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : ℝ :=
  (prefixEulerTrailRatio (k := k) a ys N hN eN : ℝ)

/-- Real-valued row descending-factorial correction appearing in the normalized
bridge factor. -/
def prefixRowDescFactorialProductReal
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : ℝ :=
  (prefixRowDescFactorialProduct (k := k) a ys eN : ℝ)

/-- The normalized real-valued bridge product whose convergence to `1`
is sufficient for the full bridge correction limit. -/
def prefixNormalizedBridgeProductReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : ℝ :=
  prefixEulerTrailRatioReal (k := k) a ys N hN eN *
    prefixRowDescFactorialProductReal (k := k) a ys eN

@[simp] lemma prefixBridgeCorrectionReal_eq_ratCast
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixBridgeCorrectionReal (k := k) a ys N hN eN =
      (prefixBridgeCorrection (k := k) a ys N hN eN : ℝ) := rfl

@[simp] lemma prefixEulerTrailRatioReal_eq_ratCast
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixEulerTrailRatioReal (k := k) a ys N hN eN =
      (prefixEulerTrailRatio (k := k) a ys N hN eN : ℝ) := rfl

@[simp] lemma prefixRowDescFactorialProductReal_eq_ratCast
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    prefixRowDescFactorialProductReal (k := k) a ys eN =
      (prefixRowDescFactorialProduct (k := k) a ys eN : ℝ) := rfl

lemma prefixBridgeCorrectionReal_eq_prefixNormalizedBridgeProductReal_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixBridgeCorrectionReal (k := k) a ys N hN eN =
      prefixNormalizedBridgeProductReal (k := k) a ys N hN eN := by
  simp [prefixBridgeCorrectionReal, prefixNormalizedBridgeProductReal,
    prefixEulerTrailRatioReal, prefixRowDescFactorialProductReal,
    prefixBridgeCorrection_eq_prefixEulerTrailRatio_mul_prefixRowDescFactorialProduct_of_prefixCompatibleState,
    hcomp]

/-- Reduction theorem for the remaining bridge limit. Once the normalized
Euler-trail / row-descending-factorial product tends to `1`, the full bridge
correction tends to `1` as well. -/
lemma tendsto_prefixBridgeCorrectionReal_of_tendsto_prefixNormalizedBridgeProductReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ → ℕ) (hN : ∀ n, ys.length ≤ N n)
    (e : ℕ → MarkovState k)
    (hcomp : ∀ n, prefixCompatibleState (k := k) a ys (N n) (hN n) (e n))
    (hlim :
      Filter.Tendsto
        (fun n => prefixNormalizedBridgeProductReal (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun n => prefixBridgeCorrectionReal (k := k) a ys (N n) (hN n) (e n))
      Filter.atTop (nhds (1 : ℝ)) := by
  have hEq :
      (fun n => prefixBridgeCorrectionReal (k := k) a ys (N n) (hN n) (e n)) =ᶠ[Filter.atTop]
        (fun n => prefixNormalizedBridgeProductReal (k := k) a ys (N n) (hN n) (e n)) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    exact prefixBridgeCorrectionReal_eq_prefixNormalizedBridgeProductReal_of_prefixCompatibleState
      (k := k) a ys (N n) (hN n) (e n) (hcomp n)
  exact hlim.congr' hEq.symm

/-- Product of factorial row outdegrees for the evidence state. This is the
normalizing factor that turns raw Euler-trail counts into the finite graph
correction quantity underlying the remaining bridge limit. -/
def outdegFactorialWeight
    (eN : MarkovState k) : ℕ :=
  ∏ i : Fin k, (MarkovDeFinettiHardEuler.outdeg (k := k) eN i).factorial

lemma outdegFactorialWeight_pos
    (eN : MarkovState k) : 0 < outdegFactorialWeight (k := k) eN := by
  classical
  dsimp [outdegFactorialWeight]
  refine Finset.prod_pos ?_
  intro i hi
  exact Nat.factorial_pos _

lemma outdegFactorialWeight_ne_zero
    (eN : MarkovState k) : outdegFactorialWeight (k := k) eN ≠ 0 :=
  Nat.ne_of_gt (outdegFactorialWeight_pos (k := k) eN)

lemma residualStateOfPrefix_outdeg
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (i : Fin k) :
    MarkovDeFinettiHardEuler.outdeg (k := k)
      (residualStateOfPrefix (k := k) a ys eN) i =
      MarkovDeFinettiHardEuler.outdeg (k := k) eN i -
        MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i := by
  rcases hcomp with ⟨heN, _, hres⟩
  unfold MarkovDeFinettiHardEuler.outdeg TransCounts.rowTotal
  simp only [residualStateOfPrefix_counts]
  rw [Finset.sum_tsub_distrib]
  intro j hj
  exact prefixWordState_counts_le_of_residualState_mem_stateFinset
    (k := k) (a := a) (ys := ys) (N := N) (hN := hN) (eN := eN) heN hres i j

lemma residualStateOfPrefix_outdeg_of_counts_le
    (a : Fin k) (ys : List (Fin k))
    (eN : MarkovState k)
    (hle : ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j)
    (i : Fin k) :
    MarkovDeFinettiHardEuler.outdeg (k := k)
      (residualStateOfPrefix (k := k) a ys eN) i =
      MarkovDeFinettiHardEuler.outdeg (k := k) eN i -
        MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i := by
  unfold MarkovDeFinettiHardEuler.outdeg TransCounts.rowTotal
  simp only [residualStateOfPrefix_counts]
  rw [Finset.sum_tsub_distrib]
  intro j hj
  exact hle i j

lemma totalEdgeTokens_graphOfState_residualStateOfPrefix_eq_of_counts_le
    (a : Fin k) (ys : List (Fin k))
    {N : ℕ} (_hN : ys.length ≤ N) {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N)
    (hle : ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j) :
    totalEdgeTokens (k := k)
      (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) =
        N - ys.length := by
  calc
    totalEdgeTokens (k := k)
        (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN))
        =
      ∑ i : Fin k,
        MarkovDeFinettiHardEuler.outdeg (k := k)
          (residualStateOfPrefix (k := k) a ys eN) i := by
            simp [totalEdgeTokens, outDeg_graphOfState_eq]
    _ =
      ∑ i : Fin k,
        (MarkovDeFinettiHardEuler.outdeg (k := k) eN i -
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact residualStateOfPrefix_outdeg_of_counts_le
                (k := k) a ys eN hle i
    _ =
      (∑ i : Fin k, MarkovDeFinettiHardEuler.outdeg (k := k) eN i) -
        ∑ i : Fin k,
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i := by
              rw [Finset.sum_tsub_distrib]
              intro i hi
              exact prefixWordState_outdeg_le_of_counts_le
                (k := k) a ys hle i
    _ = N - ys.length := by
      rw [MarkovDeFinettiHardEuler.sum_outdeg_of_mem_stateFinset
        (k := k) (N := N) (eN := eN) heN]
      rw [MarkovDeFinettiHardEuler.sum_outdeg_of_mem_stateFinset
        (k := k) (N := ys.length)
        (eN := prefixWordState (k := k) a ys)
        (prefixWordState_mem_stateFinset (k := k) a ys)]

lemma outdegFactorialWeight_eq_prefixRowDescFactorialProduct_mul_residual_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    (outdegFactorialWeight (k := k) eN : ℚ) =
      prefixRowDescFactorialProduct (k := k) a ys eN *
        outdegFactorialWeight (k := k)
          (residualStateOfPrefix (k := k) a ys eN) := by
  classical
  have hcomp' := hcomp
  rcases hcomp with ⟨heN, _, hres⟩
  unfold outdegFactorialWeight prefixRowDescFactorialProduct
  calc
    (outdegFactorialWeight (k := k) eN : ℚ)
        =
      (∏ i : Fin k,
        (((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).factorial : ℕ) : ℚ)) := by
          simp [outdegFactorialWeight]
    _ =
      ∏ i : Fin k,
        ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
            (MarkovDeFinettiHardEuler.outdeg (k := k)
              (prefixWordState (k := k) a ys) i)) : ℕ) : ℚ) *
          (((MarkovDeFinettiHardEuler.outdeg (k := k)
              (residualStateOfPrefix (k := k) a ys eN) i).factorial : ℕ) : ℚ) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          have hrowLe :
              MarkovDeFinettiHardEuler.outdeg (k := k)
                (prefixWordState (k := k) a ys) i ≤
              MarkovDeFinettiHardEuler.outdeg (k := k) eN i := by
            exact prefixWordState_outdeg_le_of_residualState_mem_stateFinset
              (k := k) (a := a) (ys := ys) (N := N) (eN := eN) hN heN hres i
          have hfacNat :
              (MarkovDeFinettiHardEuler.outdeg (k := k) eN i -
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (prefixWordState (k := k) a ys) i).factorial *
                (MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
                  (MarkovDeFinettiHardEuler.outdeg (k := k)
                  (prefixWordState (k := k) a ys) i) =
              (MarkovDeFinettiHardEuler.outdeg (k := k) eN i).factorial :=
            Nat.factorial_mul_descFactorial hrowLe
          have hfacRat' :
              ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i -
                    MarkovDeFinettiHardEuler.outdeg (k := k)
                      (prefixWordState (k := k) a ys) i).factorial : ℕ) : ℚ)) *
                ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
                    (MarkovDeFinettiHardEuler.outdeg (k := k)
                      (prefixWordState (k := k) a ys) i)) : ℕ) : ℚ) =
                ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).factorial : ℕ) : ℚ)) := by
            exact_mod_cast hfacNat
          have hfacRat :
              ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
                  (MarkovDeFinettiHardEuler.outdeg (k := k)
                    (prefixWordState (k := k) a ys) i)) : ℕ) : ℚ) *
                ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i -
                    MarkovDeFinettiHardEuler.outdeg (k := k)
                      (prefixWordState (k := k) a ys) i).factorial : ℕ) : ℚ)) =
                ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).factorial : ℕ) : ℚ)) := by
            simpa [mul_comm] using hfacRat'
          rw [residualStateOfPrefix_outdeg (k := k) a ys N hN eN hcomp' i]
          exact hfacRat.symm
    _ =
      (∏ i : Fin k,
        ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
            (MarkovDeFinettiHardEuler.outdeg (k := k)
              (prefixWordState (k := k) a ys) i)) : ℕ) : ℚ)) *
        (∏ i : Fin k,
          (((MarkovDeFinettiHardEuler.outdeg (k := k)
              (residualStateOfPrefix (k := k) a ys eN) i).factorial : ℕ) : ℚ)) := by
          simp [Finset.prod_mul_distrib]
    _ =
      prefixRowDescFactorialProduct (k := k) a ys eN *
        outdegFactorialWeight (k := k)
          (residualStateOfPrefix (k := k) a ys eN) := by
          simp [outdegFactorialWeight, prefixRowDescFactorialProduct]

/-- Finite graph correction quantity: Euler-trail count normalized by the
factorial row-outdegree weight. The remaining bridge theorem can be phrased as
stability of this quantity under deleting the fixed prefix. -/
def normalizedEulerTrailCorrection
    (eN : MarkovState k) : ℚ :=
  ((eulerTrailFinset (graphOfState eN) eN.start eN.last).card : ℚ) /
    (outdegFactorialWeight (k := k) eN : ℚ)

lemma normalizedEulerTrailCorrection_ne_zero_of_mem_stateFinset
    {N : ℕ} {eN : MarkovState k} (heN : eN ∈ stateFinset k N) :
    normalizedEulerTrailCorrection (k := k) eN ≠ 0 := by
  have hcardPos :
      0 < (eulerTrailFinset (graphOfState eN) eN.start eN.last).card := by
    rw [eulerTrailFinset_card_eq (k := k) eN heN]
    exact Nat.mul_pos
      (Nat.pos_iff_ne_zero.mpr <|
        fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN)
      (graphFactorialWeight_pos (k := k) eN)
  have hnum :
      (((eulerTrailFinset (graphOfState eN) eN.start eN.last).card : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcardPos
  have hden :
      ((outdegFactorialWeight (k := k) eN : ℚ)) ≠ 0 := by
    exact_mod_cast outdegFactorialWeight_ne_zero (k := k) eN
  exact div_ne_zero hnum hden

/-- Residual/full ratio of the normalized Euler-trail correction quantity. This
is the precise finite graph object behind the normalized bridge limit. -/
def prefixNormalizedEulerTrailCorrectionRatio
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (_hN : ys.length ≤ N) (eN : MarkovState k) : ℚ :=
  normalizedEulerTrailCorrection (k := k)
      (residualStateOfPrefix (k := k) a ys eN) /
    normalizedEulerTrailCorrection (k := k) eN

/-- Real-valued normalized Euler-trail correction. -/
def normalizedEulerTrailCorrectionReal
    (eN : MarkovState k) : ℝ :=
  (normalizedEulerTrailCorrection (k := k) eN : ℝ)

/-- Real-valued residual/full ratio of the normalized Euler-trail correction
quantity. Proving this tends to `1` is the exact finite graph correction theorem
behind the bridge limit. -/
def prefixNormalizedEulerTrailCorrectionRatioReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : ℝ :=
  (prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN : ℝ)

@[simp] lemma normalizedEulerTrailCorrectionReal_eq_ratCast
    (eN : MarkovState k) :
    normalizedEulerTrailCorrectionReal (k := k) eN =
      (normalizedEulerTrailCorrection (k := k) eN : ℝ) := rfl

@[simp] lemma prefixNormalizedEulerTrailCorrectionRatioReal_eq_ratCast
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys N hN eN =
      (prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN : ℝ) := rfl

/-! ## Token-rooted arborescences on the `edgeTok` model

This is the narrow rooted-arborescence counting layer we need for the bridge
correction.  Each non-root vertex chooses one outgoing edge token; the induced
target map must drive every vertex to the root in at most `k` steps. -/

/-- Vertices other than the designated root `t`. -/
abbrev NonrootVertex (t : Fin k) := {v : Fin k // v ≠ t}

/-- A parent-target choice for every non-root vertex. -/
abbrev TargetParentAssignment (t : Fin k) := NonrootVertex t → Fin k

/-- The self-map on vertices induced by a target-parent assignment. The root is
fixed, and every other vertex follows its chosen outgoing target. -/
def targetParentStep
    (t : Fin k) (p : TargetParentAssignment t) : Fin k → Fin k :=
  fun v =>
    if h : v = t then
      t
    else
      p ⟨v, h⟩

/-- A target-parent assignment is rooted if every vertex reaches the root in at
most `k` steps under the induced map. -/
def IsTargetRootedArborescence
    (t : Fin k) (p : TargetParentAssignment t) : Prop :=
  ∀ v : Fin k, ∃ n : ℕ, n ≤ k ∧ ((targetParentStep (k := k) t p)^[n]) v = t

/-- Non-root vertices with positive outgoing mass. This is the support-local
domain for rooted arborescences that ignore dormant rows. -/
abbrev PositiveNonrootVertex (G : EulerGraph k) (t : Fin k) :=
  {v : Fin k // v ≠ t ∧ 0 < outDegG (k := k) G v}

/-- A parent-target choice for every active non-root vertex. -/
abbrev PositiveTargetParentAssignment
    (G : EulerGraph k) (t : Fin k) :=
  PositiveNonrootVertex (k := k) G t → Fin k

/-- The self-map induced by an active-support target-parent assignment. Dormant
non-root vertices are sent directly to the root because they are outside the
local arborescence support. -/
def positiveTargetParentStep
    (G : EulerGraph k) (t : Fin k)
    (p : PositiveTargetParentAssignment (k := k) G t) : Fin k → Fin k :=
  fun v =>
    if h : v = t then
      t
    else if hpos : 0 < outDegG (k := k) G v then
      p ⟨v, h, hpos⟩
    else
      t

/-- A support-local target-parent assignment is rooted if every active
non-root vertex reaches the root in at most `k` steps. -/
def IsPositiveTargetRootedArborescence
    (G : EulerGraph k) (t : Fin k)
    (p : PositiveTargetParentAssignment (k := k) G t) : Prop :=
  ∀ v : PositiveNonrootVertex (k := k) G t,
    ∃ n : ℕ, n ≤ k ∧
      ((positiveTargetParentStep (k := k) G t p)^[n]) v.1 = t

/-- A token-parent assignment chooses one concrete outgoing edge token for every
non-root vertex. -/
abbrev TokenParentAssignment (G : EulerGraph k) (t : Fin k) :=
  ∀ x : NonrootVertex t, outTok (k := k) G x.1

/-- Forget the copy index of a token-parent assignment, keeping only its target
profile. -/
def tokenParentTargets
    (G : EulerGraph k) (t : Fin k)
    (A : TokenParentAssignment (k := k) G t) : TargetParentAssignment t :=
  fun x => (A x).1

/-- A token-parent assignment is rooted exactly when its target profile is. -/
def IsTokenRootedArborescence
    (G : EulerGraph k) (t : Fin k)
    (A : TokenParentAssignment (k := k) G t) : Prop :=
  IsTargetRootedArborescence (k := k) t (tokenParentTargets (k := k) G t A)

/-- A token-parent assignment on the active non-root support. -/
abbrev PositiveTokenParentAssignment
    (G : EulerGraph k) (t : Fin k) :=
  ∀ x : PositiveNonrootVertex (k := k) G t, outTok (k := k) G x.1

/-- Forget the copy index of an active-support token-parent assignment. -/
def positiveTokenParentTargets
    (G : EulerGraph k) (t : Fin k)
    (A : PositiveTokenParentAssignment (k := k) G t) :
    PositiveTargetParentAssignment (k := k) G t :=
  fun x => (A x).1

/-- An active-support token-parent assignment is rooted exactly when its target
profile is. -/
def IsPositiveTokenRootedArborescence
    (G : EulerGraph k) (t : Fin k)
    (A : PositiveTokenParentAssignment (k := k) G t) : Prop :=
  IsPositiveTargetRootedArborescence (k := k) G t
    (positiveTokenParentTargets (k := k) G t A)

/-- Copy choices over a fixed target profile. -/
abbrev TokenCopyAssignment
    (G : EulerGraph k) (t : Fin k)
    (p : TargetParentAssignment t) :=
  ∀ x : NonrootVertex t, Fin (G x.1 (p x))

/-- Copy choices over a fixed active-support target profile. -/
abbrev PositiveTokenCopyAssignment
    (G : EulerGraph k) (t : Fin k)
    (p : PositiveTargetParentAssignment (k := k) G t) :=
  ∀ x : PositiveNonrootVertex (k := k) G t, Fin (G x.1 (p x))

/-- Weighted target-profile count of rooted arborescences, where the weight is
the number of compatible concrete token choices. -/
noncomputable def weightedTargetRootedArborescenceCount
    (G : EulerGraph k) (t : Fin k) : ℕ :=
  by
    classical
    exact
      ∑ p : {p : TargetParentAssignment t // IsTargetRootedArborescence (k := k) t p},
        ∏ x : NonrootVertex t, G x.1 (p.1 x)

/-- Support-local weighted target-profile count of rooted arborescences, where
completely dormant non-root rows are omitted from the domain. -/
noncomputable def positiveWeightedTargetRootedArborescenceCount
    (G : EulerGraph k) (t : Fin k) : ℕ :=
  by
    classical
    exact
      ∑ p : {p : PositiveTargetParentAssignment (k := k) G t //
          IsPositiveTargetRootedArborescence (k := k) G t p},
        ∏ x : PositiveNonrootVertex (k := k) G t, G x.1 (p.1 x)

/-- Token-level rooted arborescence count on the concrete `edgeTok` model. -/
def tokenRootedArborescenceCount
    (G : EulerGraph k) (t : Fin k) : ℕ :=
  Nat.card {A : TokenParentAssignment (k := k) G t //
    IsTokenRootedArborescence (k := k) G t A}

/-- Support-local token-level rooted arborescence count on the concrete
`edgeTok` model. Dormant non-root rows are excluded from the assignment domain.
-/
def positiveTokenRootedArborescenceCount
    (G : EulerGraph k) (t : Fin k) : ℕ :=
  Nat.card {A : PositiveTokenParentAssignment (k := k) G t //
    IsPositiveTokenRootedArborescence (k := k) G t A}

/-- Remove one copy of the directed edge `u → v`.  The source is restricted to
`NonrootVertex t`, because rooted arborescences never choose an outgoing parent
edge from the root. -/
def deleteOneCopy
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k) : EulerGraph k :=
  fun a b =>
    if a = u.1 ∧ b = v then
      G a b - 1
    else
      G a b

@[simp] lemma deleteOneCopy_apply_same
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k) :
    deleteOneCopy (k := k) G u v u.1 v = G u.1 v - 1 := by
  simp [deleteOneCopy]

@[simp] lemma deleteOneCopy_apply_of_ne_source
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v a b : Fin k)
    (ha : a ≠ u.1) :
    deleteOneCopy (k := k) G u v a b = G a b := by
  simp [deleteOneCopy, ha]

lemma card_tokenCopyAssignment
    (G : EulerGraph k) (t : Fin k) (p : TargetParentAssignment t) :
    Nat.card (TokenCopyAssignment (k := k) G t p) =
      ∏ x : NonrootVertex t, G x.1 (p x) := by
  classical
  rw [Nat.card_pi]
  simp

lemma card_positiveTokenCopyAssignment
    (G : EulerGraph k) (t : Fin k)
    (p : PositiveTargetParentAssignment (k := k) G t) :
    Nat.card (PositiveTokenCopyAssignment (k := k) G t p) =
      ∏ x : PositiveNonrootVertex (k := k) G t, G x.1 (p x) := by
  classical
  rw [Nat.card_pi]
  simp

/-- Token-rooted arborescences are equivalent to a rooted target profile plus a
copy choice on each selected edge. -/
noncomputable def tokenRootedArborescenceEquivSigma
    (G : EulerGraph k) (t : Fin k) :
    {A : TokenParentAssignment (k := k) G t //
        IsTokenRootedArborescence (k := k) G t A} ≃
      Σ p : {p : TargetParentAssignment t //
          IsTargetRootedArborescence (k := k) t p},
        TokenCopyAssignment (k := k) G t p.1 where
  toFun A :=
    ⟨⟨tokenParentTargets (k := k) G t A.1, A.2⟩, fun x => (A.1 x).2⟩
  invFun q :=
    ⟨fun x => ⟨q.1.1 x, q.2 x⟩, q.1.2⟩
  left_inv A := by
    ext x
    rfl
  right_inv q := by
    cases q
    rfl

/-- Support-local token-rooted arborescences are equivalent to an active rooted
target profile plus a copy choice on each selected edge. -/
noncomputable def positiveTokenRootedArborescenceEquivSigma
    (G : EulerGraph k) (t : Fin k) :
    {A : PositiveTokenParentAssignment (k := k) G t //
        IsPositiveTokenRootedArborescence (k := k) G t A} ≃
      Σ p : {p : PositiveTargetParentAssignment (k := k) G t //
          IsPositiveTargetRootedArborescence (k := k) G t p},
        PositiveTokenCopyAssignment (k := k) G t p.1 where
  toFun A :=
    ⟨⟨positiveTokenParentTargets (k := k) G t A.1, A.2⟩, fun x => (A.1 x).2⟩
  invFun q :=
    ⟨fun x => ⟨q.1.1 x, q.2 x⟩, q.1.2⟩
  left_inv A := by
    ext x
    rfl
  right_inv q := by
    cases q
    rfl

lemma tokenRootedArborescenceCount_eq_weightedTargetRootedArborescenceCount
    (G : EulerGraph k) (t : Fin k) :
    tokenRootedArborescenceCount (k := k) G t =
      weightedTargetRootedArborescenceCount (k := k) G t := by
  classical
  unfold tokenRootedArborescenceCount weightedTargetRootedArborescenceCount
  rw [Nat.card_congr (tokenRootedArborescenceEquivSigma (k := k) G t)]
  rw [Nat.card_sigma]
  congr with p
  exact card_tokenCopyAssignment (k := k) G t p.1

lemma positiveTokenRootedArborescenceCount_eq_positiveWeightedTargetRootedArborescenceCount
    (G : EulerGraph k) (t : Fin k) :
    positiveTokenRootedArborescenceCount (k := k) G t =
      positiveWeightedTargetRootedArborescenceCount (k := k) G t := by
  classical
  unfold positiveTokenRootedArborescenceCount
    positiveWeightedTargetRootedArborescenceCount
  rw [Nat.card_congr (positiveTokenRootedArborescenceEquivSigma (k := k) G t)]
  rw [Nat.card_sigma]
  congr with p
  exact card_positiveTokenCopyAssignment (k := k) G t p.1

private lemma isEmpty_positiveNonrootVertex_of_forall_nonroot_outdeg_zero
    (G : EulerGraph k) (t : Fin k)
    (hzero : ∀ u : NonrootVertex t, outDegG (k := k) G u.1 = 0) :
    IsEmpty (PositiveNonrootVertex (k := k) G t) := by
  refine ⟨?_⟩
  intro u
  have hu0 : outDegG (k := k) G u.1 = 0 := hzero ⟨u.1, u.2.1⟩
  exact (Nat.ne_of_gt u.2.2) hu0

lemma positiveWeightedTargetRootedArborescenceCount_eq_one_of_forall_nonroot_outdeg_zero
    (G : EulerGraph k) (t : Fin k)
    (hzero : ∀ u : NonrootVertex t, outDegG (k := k) G u.1 = 0) :
    positiveWeightedTargetRootedArborescenceCount (k := k) G t = 1 := by
  classical
  letI : IsEmpty (PositiveNonrootVertex (k := k) G t) :=
    isEmpty_positiveNonrootVertex_of_forall_nonroot_outdeg_zero
      (k := k) G t hzero
  let p0 : PositiveTargetParentAssignment (k := k) G t := fun x => (isEmptyElim x)
  have hp0 : IsPositiveTargetRootedArborescence (k := k) G t p0 := by
    intro v
    exact (isEmptyElim v)
  haveI :
      Subsingleton
        {p : PositiveTargetParentAssignment (k := k) G t //
          IsPositiveTargetRootedArborescence (k := k) G t p} := by
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    funext v
    exact (isEmptyElim v)
  have huniv :
      (Finset.univ :
        Finset {p : PositiveTargetParentAssignment (k := k) G t //
          IsPositiveTargetRootedArborescence (k := k) G t p}) = {⟨p0, hp0⟩} := by
    ext x
    simp [Subsingleton.elim x ⟨p0, hp0⟩]
  unfold positiveWeightedTargetRootedArborescenceCount
  rw [huniv]
  simp [p0]

lemma positiveTokenRootedArborescenceCount_eq_one_of_forall_nonroot_outdeg_zero
    (G : EulerGraph k) (t : Fin k)
    (hzero : ∀ u : NonrootVertex t, outDegG (k := k) G u.1 = 0) :
    positiveTokenRootedArborescenceCount (k := k) G t = 1 := by
  rw [positiveTokenRootedArborescenceCount_eq_positiveWeightedTargetRootedArborescenceCount]
  exact
    positiveWeightedTargetRootedArborescenceCount_eq_one_of_forall_nonroot_outdeg_zero
      (k := k) G t hzero

lemma outDegG_eq_of_nonroot_rows_eq
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v)
    (u : NonrootVertex t) :
    outDegG (k := k) G u.1 = outDegG (k := k) G' u.1 := by
  simp [outDegG, hrow]

lemma outDegG_deleteOneCopy_eq_of_ne_source
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v a : Fin k)
    (ha : a ≠ u.1) :
    outDegG (k := k) (deleteOneCopy (k := k) G u v) a =
      outDegG (k := k) G a := by
  simp [outDegG, deleteOneCopy, ha]

lemma outDegG_deleteOneCopy_le
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v a : Fin k) :
    outDegG (k := k) (deleteOneCopy (k := k) G u v) a ≤
      outDegG (k := k) G a := by
  by_cases ha : a = u.1
  · subst ha
    unfold outDegG
    refine Finset.sum_le_sum ?_
    intro b _hb
    by_cases hb : b = v
    · simp [deleteOneCopy, hb]
    · simp [deleteOneCopy, hb]
  · rw [outDegG_deleteOneCopy_eq_of_ne_source (k := k) G u v a ha]

noncomputable def positiveNonrootVertexEquiv_of_nonroot_rows_eq
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v) :
    PositiveNonrootVertex (k := k) G t ≃ PositiveNonrootVertex (k := k) G' t where
  toFun u :=
    ⟨u.1, u.2.1, by
      rw [← outDegG_eq_of_nonroot_rows_eq (k := k) hrow ⟨u.1, u.2.1⟩]
      exact u.2.2⟩
  invFun u :=
    ⟨u.1, u.2.1, by
      rw [← outDegG_eq_of_nonroot_rows_eq (k := k)
        (G := G') (G' := G) (fun u v => (hrow u v).symm) ⟨u.1, u.2.1⟩]
      exact u.2.2⟩
  left_inv u := by
    cases u
    rfl
  right_inv u := by
    cases u
    rfl

noncomputable def positiveTargetParentAssignmentEquiv_of_nonroot_rows_eq
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v) :
    PositiveTargetParentAssignment (k := k) G t ≃
      PositiveTargetParentAssignment (k := k) G' t where
  toFun p := fun x =>
    p ((positiveNonrootVertexEquiv_of_nonroot_rows_eq (k := k) hrow).symm x)
  invFun p := fun x =>
    p ((positiveNonrootVertexEquiv_of_nonroot_rows_eq (k := k) hrow) x)
  left_inv p := by
    funext x
    simp [positiveNonrootVertexEquiv_of_nonroot_rows_eq]
  right_inv p := by
    funext x
    simp [positiveNonrootVertexEquiv_of_nonroot_rows_eq]

lemma positiveTargetParentStep_eq_of_nonroot_rows_eq
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v)
    (p : PositiveTargetParentAssignment (k := k) G t) :
    positiveTargetParentStep (k := k) G t p =
      positiveTargetParentStep (k := k) G' t
        ((positiveTargetParentAssignmentEquiv_of_nonroot_rows_eq
          (k := k) hrow) p) := by
  funext v
  by_cases hv : v = t
  · simp [positiveTargetParentStep, hv]
  · have hdeg :
      outDegG (k := k) G v = outDegG (k := k) G' v := by
      exact outDegG_eq_of_nonroot_rows_eq (k := k) hrow ⟨v, hv⟩
    by_cases hpos : 0 < outDegG (k := k) G v
    · have hpos' : 0 < outDegG (k := k) G' v := by
        rwa [← hdeg]
      have heq :
          ((positiveNonrootVertexEquiv_of_nonroot_rows_eq (k := k) hrow).symm
            ⟨v, hv, hpos'⟩) = ⟨v, hv, hpos⟩ := by
        rfl
      simp [positiveTargetParentStep, hv, hpos, hpos', heq,
        positiveTargetParentAssignmentEquiv_of_nonroot_rows_eq]
    · have hpos' : ¬ 0 < outDegG (k := k) G' v := by
        rwa [← hdeg]
      simp [positiveTargetParentStep, hv, hpos, hpos']

lemma isPositiveTargetRootedArborescence_iff_of_nonroot_rows_eq
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v)
    (p : PositiveTargetParentAssignment (k := k) G t) :
    IsPositiveTargetRootedArborescence (k := k) G t p ↔
      IsPositiveTargetRootedArborescence (k := k) G' t
        ((positiveTargetParentAssignmentEquiv_of_nonroot_rows_eq
          (k := k) hrow) p) := by
  constructor
  · intro hroot v
    let v' :=
      (positiveNonrootVertexEquiv_of_nonroot_rows_eq (k := k) hrow).symm v
    rcases hroot v' with ⟨n, hn, hstep⟩
    refine ⟨n, hn, ?_⟩
    simpa [v', positiveNonrootVertexEquiv_of_nonroot_rows_eq,
      positiveTargetParentStep_eq_of_nonroot_rows_eq (k := k) hrow p] using hstep
  · intro hroot v
    let hrow' :
        ∀ u : NonrootVertex t, ∀ w : Fin k, G' u.1 w = G u.1 w := by
      intro u w
      exact (hrow u w).symm
    let p' :=
      (positiveTargetParentAssignmentEquiv_of_nonroot_rows_eq
        (k := k) hrow) p
    let v' :=
      (positiveNonrootVertexEquiv_of_nonroot_rows_eq (k := k) hrow) v
    rcases hroot v' with ⟨n, hn, hstep⟩
    refine ⟨n, hn, ?_⟩
    rw [positiveTargetParentStep_eq_of_nonroot_rows_eq (k := k) hrow p]
    simpa [v', positiveNonrootVertexEquiv_of_nonroot_rows_eq] using hstep

noncomputable def positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k)
    (hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1) :
    PositiveNonrootVertex (k := k) G t ≃
      PositiveNonrootVertex (k := k) (deleteOneCopy (k := k) G u v) t where
  toFun x := by
    by_cases hx : x.1 = u.1
    · exact ⟨u.1, u.2, by simpa [hx] using hstay⟩
    · exact ⟨x.1, x.2.1, by
        rw [outDegG_deleteOneCopy_eq_of_ne_source (k := k) G u v x.1 hx]
        exact x.2.2⟩
  invFun x := by
    by_cases hx : x.1 = u.1
    · exact ⟨u.1, u.2, by
        have hle := outDegG_deleteOneCopy_le (k := k) G u v u.1
        exact lt_of_lt_of_le (by simpa [hx] using x.2.2) hle⟩
    · exact ⟨x.1, x.2.1, by
        simpa [outDegG_deleteOneCopy_eq_of_ne_source (k := k) G u v x.1 hx]
          using x.2.2⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    by_cases hx : x.1 = u.1 <;> simp [hx]
  right_inv x := by
    apply Subtype.ext
    dsimp
    by_cases hx : x.1 = u.1 <;> simp [hx]

noncomputable def positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k)
    (hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1) :
    PositiveTargetParentAssignment (k := k) G t ≃
      PositiveTargetParentAssignment (k := k) (deleteOneCopy (k := k) G u v) t where
  toFun p := fun x =>
    p ((positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
      (k := k) G u v hstay).symm x)
  invFun p := fun x =>
    p ((positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
      (k := k) G u v hstay) x)
  left_inv p := by
    funext x
    exact congrArg p
      ((positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay).left_inv x)
  right_inv p := by
    funext x
    exact congrArg p
      ((positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay).right_inv x)

lemma positiveTargetParentStep_eq_deleteOneCopy_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k)
    (hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1)
    (p : PositiveTargetParentAssignment (k := k) G t) :
    positiveTargetParentStep (k := k) G t p =
      positiveTargetParentStep (k := k) (deleteOneCopy (k := k) G u v) t
        ((positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
          (k := k) G u v hstay) p) := by
  funext a
  by_cases ha : a = t
  · simp [positiveTargetParentStep, ha]
  · by_cases hau : a = u.1
    · subst a
      have hpos :
        0 < outDegG (k := k) G u.1 := by
        have hle :
            outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1 ≤
              outDegG (k := k) G u.1 := by
          exact outDegG_deleteOneCopy_le (k := k) G u v u.1
        exact lt_of_lt_of_le hstay hle
      have hpos' :
          0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1 := hstay
      have heq :
          ((positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
            (k := k) G u v hstay).symm ⟨u.1, u.2, hpos'⟩) = ⟨u.1, u.2, hpos⟩ := by
        apply Subtype.ext
        dsimp [positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive]
        simp
      simpa [positiveTargetParentStep, u.2, hpos, hpos',
        positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive] using
        congrArg p heq.symm
    · have hdeg :
        outDegG (k := k) (deleteOneCopy (k := k) G u v) a =
          outDegG (k := k) G a := by
        rw [outDegG_deleteOneCopy_eq_of_ne_source (k := k) G u v a hau]
      by_cases hpos : 0 < outDegG (k := k) G a
      · have hpos' :
          0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) a := by
          simpa [hdeg] using hpos
        have heq :
            ((positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
              (k := k) G u v hstay).symm ⟨a, ha, hpos'⟩) = ⟨a, ha, hpos⟩ := by
          apply Subtype.ext
          dsimp [positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive]
          simp [hau]
        simpa [positiveTargetParentStep, ha, hau, hpos, hpos',
          positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive] using
          congrArg p heq.symm
      · have hpos' :
          ¬ 0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) a := by
          simpa [hdeg] using hpos
        simp [positiveTargetParentStep, ha, hpos, hpos']

lemma isPositiveTargetRootedArborescence_iff_deleteOneCopy_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k)
    (hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1)
    (p : PositiveTargetParentAssignment (k := k) G t) :
    IsPositiveTargetRootedArborescence (k := k) G t p ↔
      IsPositiveTargetRootedArborescence
        (k := k) (deleteOneCopy (k := k) G u v) t
        ((positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
          (k := k) G u v hstay) p) := by
  constructor
  · intro hroot x
    let x' :=
      (positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay).symm x
    rcases hroot x' with ⟨n, hn, hstep⟩
    have hx : x'.1 = x.1 := by
      dsimp [x', positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive]
      by_cases hxu : x.1 = u.1 <;> simp [hxu]
    refine ⟨n, hn, ?_⟩
    simpa [x', hx,
      positiveTargetParentStep_eq_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay p] using hstep
  · intro hroot x
    let p' :=
      (positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay) p
    let x' :=
      (positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay) x
    rcases hroot x' with ⟨n, hn, hstep⟩
    have hx : x'.1 = x.1 := by
      dsimp [x', positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive]
      by_cases hxu : x.1 = u.1 <;> simp [hxu]
    refine ⟨n, hn, ?_⟩
    simpa [p', x', hx,
      positiveTargetParentStep_eq_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay p] using hstep

noncomputable def positiveTargetRootedArborescenceEquiv_deleteOneCopy_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k)
    (hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1) :
    {p : PositiveTargetParentAssignment (k := k) G t //
        IsPositiveTargetRootedArborescence (k := k) G t p} ≃
      {p : PositiveTargetParentAssignment (k := k) (deleteOneCopy (k := k) G u v) t //
        IsPositiveTargetRootedArborescence
          (k := k) (deleteOneCopy (k := k) G u v) t p} where
  toFun p :=
    ⟨(positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay) p.1,
      (isPositiveTargetRootedArborescence_iff_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay p.1).1 p.2⟩
  invFun p :=
    ⟨(positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay).symm p.1,
      by
        have hp :
            IsPositiveTargetRootedArborescence
              (k := k) G t
              ((positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
                (k := k) G u v hstay).symm p.1) := by
          exact
            (isPositiveTargetRootedArborescence_iff_deleteOneCopy_of_source_stays_positive
              (k := k) G u v hstay
              ((positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
                (k := k) G u v hstay).symm p.1)).2 (by
                  simpa [positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive] using p.2)
        exact hp⟩
  left_inv p := by
    cases p
    simp [positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive]
  right_inv p := by
    cases p
    simp [positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive]

private lemma positiveDeleteOneCopy_transport_term_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k)
    (hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1)
    (p : PositiveTargetParentAssignment (k := k) G t) :
    (∏ x : PositiveNonrootVertex (k := k) (deleteOneCopy (k := k) G u v) t,
        deleteOneCopy (k := k) G u v x.1
          ((positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
            (k := k) G u v hstay) p x)) =
      ∏ x : PositiveNonrootVertex (k := k) G t,
        deleteOneCopy (k := k) G u v x.1 (p x) := by
  symm
  refine Fintype.prod_equiv
    (positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
      (k := k) G u v hstay)
    (fun x : PositiveNonrootVertex (k := k) G t =>
      deleteOneCopy (k := k) G u v x.1 (p x))
    (fun x : PositiveNonrootVertex (k := k) (deleteOneCopy (k := k) G u v) t =>
      deleteOneCopy (k := k) G u v x.1
        ((positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
          (k := k) G u v hstay) p x)) ?_
  intro x
  have hx :
      ((positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay) x).1 = x.1 := by
    dsimp [positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive]
    by_cases hxu : x.1 = u.1 <;> simp [hxu]
  have hp :
      ((positiveTargetParentAssignmentEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay) p)
        ((positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
          (k := k) G u v hstay) x) = p x := by
    exact congrArg p
      ((positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive
        (k := k) G u v hstay).left_inv x)
  simp [hx, hp]

lemma positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_eq_transportSum_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k)
    (hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1) :
    positiveWeightedTargetRootedArborescenceCount
        (k := k) (deleteOneCopy (k := k) G u v) t =
      (by
        classical
        exact
          ∑ p : {p : PositiveTargetParentAssignment (k := k) G t //
              IsPositiveTargetRootedArborescence (k := k) G t p},
            ∏ x : PositiveNonrootVertex (k := k) G t,
              deleteOneCopy (k := k) G u v x.1 (p.1 x)) := by
  classical
  unfold positiveWeightedTargetRootedArborescenceCount
  refine (Fintype.sum_equiv
    (positiveTargetRootedArborescenceEquiv_deleteOneCopy_of_source_stays_positive
      (k := k) G u v hstay)
    (fun p : {p : PositiveTargetParentAssignment (k := k) G t //
        IsPositiveTargetRootedArborescence (k := k) G t p} =>
      ∏ x : PositiveNonrootVertex (k := k) G t,
        deleteOneCopy (k := k) G u v x.1 (p.1 x))
    (fun p : {p : PositiveTargetParentAssignment (k := k) (deleteOneCopy (k := k) G u v) t //
        IsPositiveTargetRootedArborescence
          (k := k) (deleteOneCopy (k := k) G u v) t p} =>
      ∏ x : PositiveNonrootVertex (k := k) (deleteOneCopy (k := k) G u v) t,
        deleteOneCopy (k := k) G u v x.1 (p.1 x)) ?_
    ).symm
  intro p
  exact
    (positiveDeleteOneCopy_transport_term_of_source_stays_positive
      (k := k) G u v hstay p.1).symm

private lemma positiveTargetRootedArborescenceWeight_eq_sourceFactor_mul
    {t : Fin k} (G : EulerGraph k)
    (u : PositiveNonrootVertex (k := k) G t)
    (p : PositiveTargetParentAssignment (k := k) G t) :
    (∏ x : PositiveNonrootVertex (k := k) G t, G x.1 (p x)) =
      G u.1 (p u) *
        ((Finset.univ.erase u).prod
          fun x : PositiveNonrootVertex (k := k) G t => G x.1 (p x)) := by
  classical
  calc
    (∏ x : PositiveNonrootVertex (k := k) G t, G x.1 (p x)) =
        ((Finset.univ.erase u).prod
          fun x : PositiveNonrootVertex (k := k) G t => G x.1 (p x)) * G u.1 (p u) := by
          simpa using
            (Finset.prod_erase_mul
              (s := Finset.univ)
              (f := fun x : PositiveNonrootVertex (k := k) G t => G x.1 (p x))
              (h := Finset.mem_univ u)).symm
    _ = G u.1 (p u) *
        ((Finset.univ.erase u).prod
          fun x : PositiveNonrootVertex (k := k) G t => G x.1 (p x)) := by
          ac_rfl

private lemma positiveDeleteOneCopy_prod_erase_eq_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : PositiveNonrootVertex (k := k) G t) (v : Fin k)
    (p : PositiveTargetParentAssignment (k := k) G t) :
    ((Finset.univ.erase u).prod fun x : PositiveNonrootVertex (k := k) G t =>
        deleteOneCopy (k := k) G ⟨u.1, u.2.1⟩ v x.1 (p x)) =
      ((Finset.univ.erase u).prod fun x : PositiveNonrootVertex (k := k) G t =>
        G x.1 (p x)) := by
  classical
  refine Finset.prod_congr rfl ?_
  intro x hx
  have hxne : x ≠ u := (Finset.mem_erase.mp hx).1
  have hsrc : x.1 ≠ u.1 := by
    intro hxu
    apply hxne
    exact Subtype.ext hxu
  simp [deleteOneCopy, hsrc]

private lemma positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_lower_term_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k)
    (hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1)
    (p : {p : PositiveTargetParentAssignment (k := k) G t //
      IsPositiveTargetRootedArborescence (k := k) G t p}) :
    (G u.1 v - 1) *
        (∏ x : PositiveNonrootVertex (k := k) G t, G x.1 (p.1 x)) ≤
      G u.1 v *
        (∏ x : PositiveNonrootVertex (k := k) G t,
          deleteOneCopy (k := k) G u v x.1 (p.1 x)) := by
  classical
  have hupos :
      0 < outDegG (k := k) G u.1 := by
    have hle := outDegG_deleteOneCopy_le (k := k) G u v u.1
    exact lt_of_lt_of_le hstay hle
  let uG : PositiveNonrootVertex (k := k) G t := ⟨u.1, u.2, hupos⟩
  let rest : ℕ :=
    ((Finset.univ.erase uG).prod fun x : PositiveNonrootVertex (k := k) G t => G x.1 (p.1 x))
  have hfull :
      (∏ x : PositiveNonrootVertex (k := k) G t, G x.1 (p.1 x)) =
        G u.1 (p.1 uG) * rest := by
    simpa [uG, rest] using
      positiveTargetRootedArborescenceWeight_eq_sourceFactor_mul
        (k := k) G uG p.1
  have herase :
      ((Finset.univ.erase uG).prod fun x : PositiveNonrootVertex (k := k) G t =>
          deleteOneCopy (k := k) G u v x.1 (p.1 x)) = rest := by
    simpa [uG, rest] using
      positiveDeleteOneCopy_prod_erase_eq_of_source_stays_positive
        (k := k) G uG v p.1
  have hdel :
      (∏ x : PositiveNonrootVertex (k := k) G t,
          deleteOneCopy (k := k) G u v x.1 (p.1 x)) =
        deleteOneCopy (k := k) G u v u.1 (p.1 uG) * rest := by
    calc
      (∏ x : PositiveNonrootVertex (k := k) G t,
          deleteOneCopy (k := k) G u v x.1 (p.1 x)) =
            deleteOneCopy (k := k) G u v u.1 (p.1 uG) *
              ((Finset.univ.erase uG).prod fun x : PositiveNonrootVertex (k := k) G t =>
                deleteOneCopy (k := k) G u v x.1 (p.1 x)) := by
              calc
                (∏ x : PositiveNonrootVertex (k := k) G t,
                    deleteOneCopy (k := k) G u v x.1 (p.1 x)) =
                  ((Finset.univ.erase uG).prod
                      fun x : PositiveNonrootVertex (k := k) G t =>
                        deleteOneCopy (k := k) G u v x.1 (p.1 x)) *
                    deleteOneCopy (k := k) G u v u.1 (p.1 uG) := by
                      simpa using
                        (Finset.prod_erase_mul
                          (s := Finset.univ)
                          (f := fun x : PositiveNonrootVertex (k := k) G t =>
                            deleteOneCopy (k := k) G u v x.1 (p.1 x))
                          (h := Finset.mem_univ uG)).symm
                _ = deleteOneCopy (k := k) G u v u.1 (p.1 uG) *
                    ((Finset.univ.erase uG).prod
                      fun x : PositiveNonrootVertex (k := k) G t =>
                        deleteOneCopy (k := k) G u v x.1 (p.1 x)) := by
                      ac_rfl
      _ = deleteOneCopy (k := k) G u v u.1 (p.1 uG) * rest := by
            rw [herase]
  by_cases hmatch : p.1 uG = v
  · have hsame :
        deleteOneCopy (k := k) G u v u.1 (p.1 uG) = G u.1 v - 1 := by
      simp [deleteOneCopy, hmatch]
    have heq :
        (G u.1 v - 1) * (G u.1 (p.1 uG) * rest) =
          G u.1 v * (deleteOneCopy (k := k) G u v u.1 (p.1 uG) * rest) := by
      simp [hmatch]
      ac_rfl
    simpa [hfull, hdel] using le_of_eq heq
  · have hsame :
        deleteOneCopy (k := k) G u v u.1 (p.1 uG) = G u.1 (p.1 uG) := by
      simp [deleteOneCopy, hmatch]
    have hm : G u.1 v - 1 ≤ G u.1 v := Nat.sub_le _ _
    have hmono :
        (G u.1 v - 1) * (G u.1 (p.1 uG) * rest) ≤
          G u.1 v * (G u.1 (p.1 uG) * rest) :=
      Nat.mul_le_mul_right (G u.1 (p.1 uG) * rest) hm
    simpa [hfull, hdel, hsame] using hmono

lemma positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_lower_of_source_stays_positive
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k)
    (hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1) :
    (G u.1 v - 1) *
        positiveWeightedTargetRootedArborescenceCount (k := k) G t ≤
      G u.1 v *
        positiveWeightedTargetRootedArborescenceCount
          (k := k) (deleteOneCopy (k := k) G u v) t := by
  classical
  have htransport :=
    positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_eq_transportSum_of_source_stays_positive
      (k := k) G u v hstay
  calc
    (G u.1 v - 1) * positiveWeightedTargetRootedArborescenceCount (k := k) G t =
        ∑ p : {p : PositiveTargetParentAssignment (k := k) G t //
            IsPositiveTargetRootedArborescence (k := k) G t p},
          (G u.1 v - 1) *
            ∏ x : PositiveNonrootVertex (k := k) G t, G x.1 (p.1 x) := by
              simpa [positiveWeightedTargetRootedArborescenceCount] using
                (Finset.mul_sum
                  (s := Finset.univ)
                  (f := fun p : {p : PositiveTargetParentAssignment (k := k) G t //
                      IsPositiveTargetRootedArborescence (k := k) G t p} =>
                    ∏ x : PositiveNonrootVertex (k := k) G t, G x.1 (p.1 x))
                  (a := G u.1 v - 1))
    _ ≤ ∑ p : {p : PositiveTargetParentAssignment (k := k) G t //
            IsPositiveTargetRootedArborescence (k := k) G t p},
          G u.1 v *
            ∏ x : PositiveNonrootVertex (k := k) G t,
              deleteOneCopy (k := k) G u v x.1 (p.1 x) := by
            apply Finset.sum_le_sum
            intro p hp
            exact
              positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_lower_term_of_source_stays_positive
                (k := k) G u v hstay p
    _ = G u.1 v *
          (by
            classical
            exact
              ∑ p : {p : PositiveTargetParentAssignment (k := k) G t //
                  IsPositiveTargetRootedArborescence (k := k) G t p},
                ∏ x : PositiveNonrootVertex (k := k) G t,
                  deleteOneCopy (k := k) G u v x.1 (p.1 x)) := by
            simpa [positiveWeightedTargetRootedArborescenceCount] using
              (Finset.mul_sum
                (s := Finset.univ)
                (f := fun p : {p : PositiveTargetParentAssignment (k := k) G t //
                    IsPositiveTargetRootedArborescence (k := k) G t p} =>
                  ∏ x : PositiveNonrootVertex (k := k) G t,
                    deleteOneCopy (k := k) G u v x.1 (p.1 x))
                (a := G u.1 v)).symm
    _ = G u.1 v *
          positiveWeightedTargetRootedArborescenceCount
            (k := k) (deleteOneCopy (k := k) G u v) t := by
            rw [htransport]

lemma positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_lower
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k) :
    (G u.1 v - 1) *
        positiveWeightedTargetRootedArborescenceCount (k := k) G t ≤
      G u.1 v *
        positiveWeightedTargetRootedArborescenceCount
          (k := k) (deleteOneCopy (k := k) G u v) t := by
  by_cases hstay :
      0 < outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1
  · exact
      positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_lower_of_source_stays_positive
        (k := k) G u v hstay
  · have hzeroOut :
      outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1 = 0 := by
      exact Nat.eq_zero_of_not_pos hstay
    have hterm_le :
        deleteOneCopy (k := k) G u v u.1 v ≤
          outDegG (k := k) (deleteOneCopy (k := k) G u v) u.1 := by
      unfold outDegG
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    have hterm_zero :
        deleteOneCopy (k := k) G u v u.1 v = 0 := by
      have hle0 :
          deleteOneCopy (k := k) G u v u.1 v ≤ 0 := by
        simpa [hzeroOut] using hterm_le
      exact Nat.eq_zero_of_le_zero hle0
    have hfactor_zero : G u.1 v - 1 = 0 := by
      simpa [deleteOneCopy] using hterm_zero
    simp [hfactor_zero]

lemma positiveTokenRootedArborescenceCount_deleteOneCopy_lower
    {t : Fin k} (G : EulerGraph k)
    (u : NonrootVertex t) (v : Fin k) :
    (G u.1 v - 1) * positiveTokenRootedArborescenceCount (k := k) G t ≤
      G u.1 v * positiveTokenRootedArborescenceCount
        (k := k) (deleteOneCopy (k := k) G u v) t := by
  rw [positiveTokenRootedArborescenceCount_eq_positiveWeightedTargetRootedArborescenceCount,
    positiveTokenRootedArborescenceCount_eq_positiveWeightedTargetRootedArborescenceCount]
  exact positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_lower
    (k := k) G u v

noncomputable def positiveOutTokEquiv_of_nonroot_rows_eq
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v)
    (u : PositiveNonrootVertex (k := k) G t) :
    outTok (k := k) G u.1 ≃ outTok (k := k) G' u.1 where
  toFun x :=
    ⟨x.1, Fin.cast (by
      simpa using hrow ⟨u.1, u.2.1⟩ x.1) x.2⟩
  invFun x :=
    ⟨x.1, Fin.cast (by
      simpa using (hrow ⟨u.1, u.2.1⟩ x.1).symm) x.2⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl

noncomputable def positiveTokenParentAssignmentEquiv_of_nonroot_rows_eq
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v) :
    PositiveTokenParentAssignment (k := k) G t ≃
      PositiveTokenParentAssignment (k := k) G' t where
  toFun A := fun x =>
    (positiveOutTokEquiv_of_nonroot_rows_eq (k := k) hrow
      ((positiveNonrootVertexEquiv_of_nonroot_rows_eq (k := k) hrow).symm x))
        (A ((positiveNonrootVertexEquiv_of_nonroot_rows_eq (k := k) hrow).symm x))
  invFun A := fun x =>
    (positiveOutTokEquiv_of_nonroot_rows_eq (k := k)
      (G := G') (G' := G) (fun u v => (hrow u v).symm)
      ((positiveNonrootVertexEquiv_of_nonroot_rows_eq (k := k) hrow) x))
        (A ((positiveNonrootVertexEquiv_of_nonroot_rows_eq (k := k) hrow) x))
  left_inv A := by
    funext x
    rfl
  right_inv A := by
    funext x
    rfl

lemma isPositiveTokenRootedArborescence_iff_of_nonroot_rows_eq
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v)
    (A : PositiveTokenParentAssignment (k := k) G t) :
    IsPositiveTokenRootedArborescence (k := k) G t A ↔
      IsPositiveTokenRootedArborescence (k := k) G' t
        ((positiveTokenParentAssignmentEquiv_of_nonroot_rows_eq
          (k := k) hrow) A) := by
  simp only [IsPositiveTokenRootedArborescence, positiveTokenParentTargets,
    positiveTokenParentAssignmentEquiv_of_nonroot_rows_eq,
    positiveOutTokEquiv_of_nonroot_rows_eq]
  exact isPositiveTargetRootedArborescence_iff_of_nonroot_rows_eq
    (k := k) hrow (positiveTokenParentTargets (k := k) G t A)

lemma positiveTokenRootedArborescenceCount_congr_nonroot_rows
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v) :
    positiveTokenRootedArborescenceCount (k := k) G t =
      positiveTokenRootedArborescenceCount (k := k) G' t := by
  classical
  unfold positiveTokenRootedArborescenceCount
  refine Nat.card_congr ?_
  refine
    { toFun := fun A =>
        ⟨(positiveTokenParentAssignmentEquiv_of_nonroot_rows_eq
            (k := k) hrow) A.1, ?_⟩
      , invFun := fun A =>
        ⟨(positiveTokenParentAssignmentEquiv_of_nonroot_rows_eq
            (k := k) hrow).symm A.1, ?_⟩
      , left_inv := ?_
      , right_inv := ?_ }
  · exact
      (isPositiveTokenRootedArborescence_iff_of_nonroot_rows_eq
        (k := k) hrow A.1).1 A.2
  · exact
      (isPositiveTokenRootedArborescence_iff_of_nonroot_rows_eq
        (k := k) (G := G') (G' := G) (fun u v => (hrow u v).symm)
        A.1).1 A.2
  · intro A
    ext x
    rfl
  · intro A
    ext x
    rfl

noncomputable def positiveNonrootVertexEquivNonrootVertex_of_forall_pos
    (G : EulerGraph k) (t : Fin k)
    (hpos : ∀ u : NonrootVertex t, 0 < outDegG (k := k) G u.1) :
    PositiveNonrootVertex (k := k) G t ≃ NonrootVertex t where
  toFun u := ⟨u.1, u.2.1⟩
  invFun u := ⟨u.1, u.2, hpos u⟩
  left_inv u := by
    cases u
    rfl
  right_inv u := by
    cases u
    rfl

lemma positiveTargetParentStep_eq_targetParentStep_of_forall_pos
    (G : EulerGraph k) (t : Fin k)
    (hpos : ∀ u : NonrootVertex t, 0 < outDegG (k := k) G u.1)
    (p : TargetParentAssignment t) :
    positiveTargetParentStep (k := k) G t
        (fun x => p ((positiveNonrootVertexEquivNonrootVertex_of_forall_pos
          (k := k) G t hpos) x)) =
      targetParentStep (k := k) t p := by
  funext v
  by_cases hv : v = t
  · simp [positiveTargetParentStep, targetParentStep, hv]
  · have hvpos : 0 < outDegG (k := k) G v := hpos ⟨v, hv⟩
    have heq :
        ((positiveNonrootVertexEquivNonrootVertex_of_forall_pos
          (k := k) G t hpos) ⟨v, hv, hvpos⟩) = ⟨v, hv⟩ := by
      rfl
    simp [positiveTargetParentStep, targetParentStep, hv, hvpos, heq]

lemma isPositiveTargetRootedArborescence_iff_isTargetRootedArborescence_of_forall_pos
    (G : EulerGraph k) (t : Fin k)
    (hpos : ∀ u : NonrootVertex t, 0 < outDegG (k := k) G u.1)
    (p : TargetParentAssignment t) :
    IsPositiveTargetRootedArborescence (k := k) G t
        (fun x => p ((positiveNonrootVertexEquivNonrootVertex_of_forall_pos
          (k := k) G t hpos) x)) ↔
      IsTargetRootedArborescence (k := k) t p := by
  constructor
  · intro hroot v
    by_cases hv : v = t
    · refine ⟨0, Nat.zero_le _, ?_⟩
      simp [hv]
    · have hvpos : 0 < outDegG (k := k) G v := hpos ⟨v, hv⟩
      rcases hroot ⟨v, hv, hvpos⟩ with ⟨n, hn, hstep⟩
      refine ⟨n, hn, ?_⟩
      simpa [positiveTargetParentStep_eq_targetParentStep_of_forall_pos
        (k := k) G t hpos p] using hstep
  · intro hroot v
    rcases hroot v.1 with ⟨n, hn, hstep⟩
    refine ⟨n, hn, ?_⟩
    simpa [positiveTargetParentStep_eq_targetParentStep_of_forall_pos
      (k := k) G t hpos p] using hstep

noncomputable def positiveTokenParentAssignmentEquivTokenParentAssignment_of_forall_pos
    (G : EulerGraph k) (t : Fin k)
    (hpos : ∀ u : NonrootVertex t, 0 < outDegG (k := k) G u.1) :
    PositiveTokenParentAssignment (k := k) G t ≃
      TokenParentAssignment (k := k) G t where
  toFun A := fun x =>
    A ((positiveNonrootVertexEquivNonrootVertex_of_forall_pos
      (k := k) G t hpos).symm x)
  invFun A := fun x =>
    A ((positiveNonrootVertexEquivNonrootVertex_of_forall_pos
      (k := k) G t hpos) x)
  left_inv A := by
    funext x
    rfl
  right_inv A := by
    funext x
    rfl

lemma isPositiveTokenRootedArborescence_iff_isTokenRootedArborescence_of_forall_pos
    (G : EulerGraph k) (t : Fin k)
    (hpos : ∀ u : NonrootVertex t, 0 < outDegG (k := k) G u.1)
    (A : TokenParentAssignment (k := k) G t) :
    IsPositiveTokenRootedArborescence (k := k) G t
        ((positiveTokenParentAssignmentEquivTokenParentAssignment_of_forall_pos
          (k := k) G t hpos).symm A) ↔
      IsTokenRootedArborescence (k := k) G t A := by
  simp only [IsPositiveTokenRootedArborescence, positiveTokenParentTargets,
    IsTokenRootedArborescence, tokenParentTargets,
    positiveTokenParentAssignmentEquivTokenParentAssignment_of_forall_pos,
    Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk]
  exact isPositiveTargetRootedArborescence_iff_isTargetRootedArborescence_of_forall_pos
    (k := k) G t hpos (tokenParentTargets (k := k) G t A)

lemma isTokenRootedArborescence_iff_isPositiveTokenRootedArborescence_of_forall_pos
    (G : EulerGraph k) (t : Fin k)
    (hpos : ∀ u : NonrootVertex t, 0 < outDegG (k := k) G u.1)
    (A : PositiveTokenParentAssignment (k := k) G t) :
    IsTokenRootedArborescence (k := k) G t
        ((positiveTokenParentAssignmentEquivTokenParentAssignment_of_forall_pos
          (k := k) G t hpos) A) ↔
      IsPositiveTokenRootedArborescence (k := k) G t A := by
  simpa using
    (isPositiveTokenRootedArborescence_iff_isTokenRootedArborescence_of_forall_pos
      (k := k) G t hpos
      ((positiveTokenParentAssignmentEquivTokenParentAssignment_of_forall_pos
        (k := k) G t hpos) A)).symm

lemma positiveTokenRootedArborescenceCount_eq_tokenRootedArborescenceCount_of_forall_pos
    (G : EulerGraph k) (t : Fin k)
    (hpos : ∀ u : NonrootVertex t, 0 < outDegG (k := k) G u.1) :
    positiveTokenRootedArborescenceCount (k := k) G t =
      tokenRootedArborescenceCount (k := k) G t := by
  classical
  unfold positiveTokenRootedArborescenceCount tokenRootedArborescenceCount
  refine Nat.card_congr ?_
  refine
    { toFun := fun A =>
        ⟨(positiveTokenParentAssignmentEquivTokenParentAssignment_of_forall_pos
            (k := k) G t hpos) A.1, ?_⟩
      , invFun := fun A =>
        ⟨(positiveTokenParentAssignmentEquivTokenParentAssignment_of_forall_pos
            (k := k) G t hpos).symm A.1, ?_⟩
      , left_inv := ?_
      , right_inv := ?_ }
  · exact
      (isTokenRootedArborescence_iff_isPositiveTokenRootedArborescence_of_forall_pos
        (k := k) G t hpos A.1).2 A.2
  · exact
      (isPositiveTokenRootedArborescence_iff_isTokenRootedArborescence_of_forall_pos
        (k := k) G t hpos A.1).2 A.2
  · intro A
    ext x
    rfl
  · intro A
    ext x
    rfl

lemma weightedTargetRootedArborescenceCount_eq_zero_of_exists_nonroot_zero_row
    (G : EulerGraph k) (t : Fin k)
    (hzero : ∃ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = 0) :
    weightedTargetRootedArborescenceCount (k := k) G t = 0 := by
  classical
  rcases hzero with ⟨u, hu⟩
  unfold weightedTargetRootedArborescenceCount
  refine Finset.sum_eq_zero ?_
  intro p hp
  refine Finset.prod_eq_zero (i := u) (by simp) ?_
  exact hu (p.1 u)

lemma tokenRootedArborescenceCount_eq_zero_of_exists_nonroot_zero_row
    (G : EulerGraph k) (t : Fin k)
    (hzero : ∃ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = 0) :
    tokenRootedArborescenceCount (k := k) G t = 0 := by
  rw [tokenRootedArborescenceCount_eq_weightedTargetRootedArborescenceCount]
  exact
    weightedTargetRootedArborescenceCount_eq_zero_of_exists_nonroot_zero_row
      (k := k) G t hzero

private lemma targetRootedArborescenceWeight_eq_sourceFactor_mul
    (G : EulerGraph k) (t : Fin k)
    (p : TargetParentAssignment t) (u : NonrootVertex t) :
    (∏ x : NonrootVertex t, G x.1 (p x)) =
      G u.1 (p u) * ((Finset.univ.erase u).prod fun x : NonrootVertex t => G x.1 (p x)) := by
  classical
  calc
    (∏ x : NonrootVertex t, G x.1 (p x))
        = ((Finset.univ.erase u).prod fun x : NonrootVertex t => G x.1 (p x)) * G u.1 (p u) := by
            simpa using
              (Finset.prod_erase_mul
                (s := Finset.univ)
                (f := fun x : NonrootVertex t => G x.1 (p x))
                (h := Finset.mem_univ u)).symm
    _ = G u.1 (p u) * ((Finset.univ.erase u).prod fun x : NonrootVertex t => G x.1 (p x)) := by
          ac_rfl

private lemma deleteOneCopy_prod_erase_eq
    (G : EulerGraph k) (t : Fin k) (u : NonrootVertex t) (v : Fin k)
    (p : TargetParentAssignment t) :
    ((Finset.univ.erase u).prod fun x : NonrootVertex t =>
        deleteOneCopy (k := k) G u v x.1 (p x)) =
      ((Finset.univ.erase u).prod fun x : NonrootVertex t => G x.1 (p x)) := by
  classical
  refine Finset.prod_congr rfl ?_
  intro x hx
  have hxne : x ≠ u := (Finset.mem_erase.mp hx).1
  have hsrc : x.1 ≠ u.1 := by
    intro hxu
    apply hxne
    exact Subtype.ext hxu
  simp [deleteOneCopy, hsrc]

private lemma weightedTargetRootedArborescenceCount_deleteOneCopy_lower_term
    (G : EulerGraph k) (t : Fin k) (u : NonrootVertex t) (v : Fin k)
    (p : {p : TargetParentAssignment t //
      IsTargetRootedArborescence (k := k) t p}) :
    (G u.1 v - 1) * (∏ x : NonrootVertex t, G x.1 (p.1 x)) ≤
      G u.1 v * (∏ x : NonrootVertex t, deleteOneCopy (k := k) G u v x.1 (p.1 x)) := by
  classical
  let rest : ℕ := ((Finset.univ.erase u).prod fun x : NonrootVertex t => G x.1 (p.1 x))
  have hfull :
      (∏ x : NonrootVertex t, G x.1 (p.1 x)) =
        G u.1 (p.1 u) * rest := by
    simpa [rest] using
      targetRootedArborescenceWeight_eq_sourceFactor_mul
        (k := k) G t p.1 u
  have herase :
      ((Finset.univ.erase u).prod fun x : NonrootVertex t =>
          deleteOneCopy (k := k) G u v x.1 (p.1 x)) = rest := by
    simpa [rest] using deleteOneCopy_prod_erase_eq (k := k) G t u v p.1
  have hdel :
      (∏ x : NonrootVertex t, deleteOneCopy (k := k) G u v x.1 (p.1 x)) =
        deleteOneCopy (k := k) G u v u.1 (p.1 u) * rest := by
    calc
      (∏ x : NonrootVertex t, deleteOneCopy (k := k) G u v x.1 (p.1 x))
          = deleteOneCopy (k := k) G u v u.1 (p.1 u) *
              ((Finset.univ.erase u).prod fun x : NonrootVertex t =>
                deleteOneCopy (k := k) G u v x.1 (p.1 x)) := by
                simpa [mul_comm] using
                  targetRootedArborescenceWeight_eq_sourceFactor_mul
                    (k := k) (G := deleteOneCopy (k := k) G u v) t p.1 u
      _ = deleteOneCopy (k := k) G u v u.1 (p.1 u) * rest := by
            rw [herase]
  by_cases hmatch : p.1 u = v
  · have hsame :
        deleteOneCopy (k := k) G u v u.1 (p.1 u) = G u.1 v - 1 := by
      simp [deleteOneCopy, hmatch]
    have heq :
        (G u.1 v - 1) * (G u.1 (p.1 u) * rest) =
          G u.1 v * (deleteOneCopy (k := k) G u v u.1 (p.1 u) * rest) := by
      simp [hmatch]
      ac_rfl
    simpa [hfull, hdel] using le_of_eq heq
  · have hsame :
        deleteOneCopy (k := k) G u v u.1 (p.1 u) = G u.1 (p.1 u) := by
      simp [deleteOneCopy, hmatch]
    have hm : G u.1 v - 1 ≤ G u.1 v := Nat.sub_le _ _
    have hmono :
        (G u.1 v - 1) * (G u.1 (p.1 u) * rest) ≤
          G u.1 v * (G u.1 (p.1 u) * rest) :=
      Nat.mul_le_mul_right (G u.1 (p.1 u) * rest) hm
    simpa [hfull, hdel, hsame] using hmono

lemma weightedTargetRootedArborescenceCount_deleteOneCopy_lower
    (G : EulerGraph k) (t : Fin k) (u : NonrootVertex t) (v : Fin k) :
    (G u.1 v - 1) * weightedTargetRootedArborescenceCount (k := k) G t ≤
      G u.1 v * weightedTargetRootedArborescenceCount
        (k := k) (deleteOneCopy (k := k) G u v) t := by
  classical
  calc
    (G u.1 v - 1) * weightedTargetRootedArborescenceCount (k := k) G t
        = ∑ p : {p : TargetParentAssignment t //
            IsTargetRootedArborescence (k := k) t p},
            (G u.1 v - 1) * ∏ x : NonrootVertex t, G x.1 (p.1 x) := by
              simpa [weightedTargetRootedArborescenceCount] using
                (Finset.mul_sum
                  (s := Finset.univ)
                  (f := fun p : {p : TargetParentAssignment t //
                      IsTargetRootedArborescence (k := k) t p} =>
                    ∏ x : NonrootVertex t, G x.1 (p.1 x))
                  (a := G u.1 v - 1))
    _ ≤ ∑ p : {p : TargetParentAssignment t //
            IsTargetRootedArborescence (k := k) t p},
            G u.1 v * ∏ x : NonrootVertex t,
              deleteOneCopy (k := k) G u v x.1 (p.1 x) := by
              apply Finset.sum_le_sum
              intro p hp
              exact weightedTargetRootedArborescenceCount_deleteOneCopy_lower_term
                (k := k) G t u v p
    _ = G u.1 v * weightedTargetRootedArborescenceCount
          (k := k) (deleteOneCopy (k := k) G u v) t := by
            simpa [weightedTargetRootedArborescenceCount] using
              (Finset.mul_sum
                (s := Finset.univ)
                (f := fun p : {p : TargetParentAssignment t //
                    IsTargetRootedArborescence (k := k) t p} =>
                  ∏ x : NonrootVertex t,
                    deleteOneCopy (k := k) G u v x.1 (p.1 x))
                (a := G u.1 v)).symm

lemma tokenRootedArborescenceCount_deleteOneCopy_lower
    (G : EulerGraph k) (t : Fin k) (u : NonrootVertex t) (v : Fin k) :
    (G u.1 v - 1) * tokenRootedArborescenceCount (k := k) G t ≤
      G u.1 v * tokenRootedArborescenceCount
        (k := k) (deleteOneCopy (k := k) G u v) t := by
  rw [tokenRootedArborescenceCount_eq_weightedTargetRootedArborescenceCount,
    tokenRootedArborescenceCount_eq_weightedTargetRootedArborescenceCount]
  exact weightedTargetRootedArborescenceCount_deleteOneCopy_lower
    (k := k) G t u v

/-- Residual/full ratio of token-rooted arborescence counts. This is the
specialized rooted-tree ratio that the normalized Euler correction is expected
to match on balanced `graphOfState` graphs. -/
def prefixTokenRootedArborescenceRatio
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (_hN : ys.length ≤ N) (eN : MarkovState k) : ℚ :=
  (tokenRootedArborescenceCount (k := k)
      (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN))
      (residualStateOfPrefix (k := k) a ys eN).last : ℚ) /
    tokenRootedArborescenceCount (k := k) (graphOfState (k := k) eN) eN.last

/-- Real-valued version of the token-rooted arborescence ratio. -/
def prefixTokenRootedArborescenceRatioReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : ℝ :=
  (prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN : ℝ)

@[simp] lemma prefixTokenRootedArborescenceRatioReal_eq_ratCast
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixTokenRootedArborescenceRatioReal (k := k) a ys N hN eN =
      (prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN : ℝ) := rfl

/-- Residual/full ratio of the support-local token-rooted arborescence counts.
This is the honest replacement target for dormant-row states. -/
def prefixPositiveTokenRootedArborescenceRatio
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (_hN : ys.length ≤ N) (eN : MarkovState k) : ℚ :=
  (positiveTokenRootedArborescenceCount (k := k)
      (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN))
      (residualStateOfPrefix (k := k) a ys eN).last : ℚ) /
    positiveTokenRootedArborescenceCount (k := k) (graphOfState (k := k) eN) eN.last

/-- Real-valued version of the support-local token-rooted arborescence ratio. -/
def prefixPositiveTokenRootedArborescenceRatioReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : ℝ :=
  (prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN : ℝ)

@[simp] lemma prefixPositiveTokenRootedArborescenceRatioReal_eq_ratCast
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys N hN eN =
      (prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN : ℝ) := rfl

lemma prefixPositiveTokenRootedArborescenceRatio_eq_prefixTokenRootedArborescenceRatio_of_forall_pos
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hres :
      ∀ u : NonrootVertex (residualStateOfPrefix (k := k) a ys eN).last,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (residualStateOfPrefix (k := k) a ys eN) u.1)
    (hfull :
      ∀ u : NonrootVertex eN.last,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k) eN u.1) :
    prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN =
      prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  have hres' :
      ∀ u : NonrootVertex (residualStateOfPrefix (k := k) a ys eN).last,
        0 < outDegG (k := k)
          (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) u.1 := by
    intro u
    simpa [outDeg_graphOfState_eq] using hres u
  have hfull' :
      ∀ u : NonrootVertex eN.last,
        0 < outDegG (k := k) (graphOfState (k := k) eN) u.1 := by
    intro u
    simpa [outDeg_graphOfState_eq] using hfull u
  unfold prefixPositiveTokenRootedArborescenceRatio
    prefixTokenRootedArborescenceRatio
  rw [positiveTokenRootedArborescenceCount_eq_tokenRootedArborescenceCount_of_forall_pos
    (k := k)
    (G := graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN))
    (t := (residualStateOfPrefix (k := k) a ys eN).last) hres']
  · rw [positiveTokenRootedArborescenceCount_eq_tokenRootedArborescenceCount_of_forall_pos
      (k := k) (G := graphOfState (k := k) eN) (t := eN.last) hfull']

lemma prefixPositiveTokenRootedArborescenceRatioReal_eq_prefixTokenRootedArborescenceRatioReal_of_forall_pos
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hres :
      ∀ u : NonrootVertex (residualStateOfPrefix (k := k) a ys eN).last,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (residualStateOfPrefix (k := k) a ys eN) u.1)
    (hfull :
      ∀ u : NonrootVertex eN.last,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k) eN u.1) :
    prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys N hN eN =
      prefixTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  exact congrArg (fun q : ℚ => (q : ℝ))
    (prefixPositiveTokenRootedArborescenceRatio_eq_prefixTokenRootedArborescenceRatio_of_forall_pos
      (k := k) a ys N hN eN hres hfull)

/-- Legacy exact finite bridge statement for one evidence state: the Euler-trail
count matches the token-rooted arborescence count times the full
outdegree-factorial weight.

This normalization is kept as a historical surface because downstream ratio
lemmas still factor through it. It is not a valid global theorem target:
`positiveTokenRootedBridgeCardEq_false_on_counterexample_0101` refutes the
support-local version on an active state, and the same double-counting issue
applies to the all-vertices variant. -/
def tokenRootedBridgeCardEq
    (s : MarkovState k) : Prop :=
  (eulerTrailFinset (graphOfState s) s.start s.last).card =
    tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
      outdegFactorialWeight (k := k) s

/-- Legacy support-local exact finite bridge statement for one evidence state:
the Euler-trail count matches the active-support token-rooted arborescence
count times the full outdegree-factorial weight.

This predicate is now known to be false in general:
`positiveTokenRootedBridgeCardEq_false_on_counterexample_0101` gives a concrete
active counterexample. The direct-route repair must replace the weight, not
merely prove this predicate for more cases. -/
def positiveTokenRootedBridgeCardEq
    (s : MarkovState k) : Prop :=
  (eulerTrailFinset (graphOfState s) s.start s.last).card =
    positiveTokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
      outdegFactorialWeight (k := k) s

/-- Corrected support-local BEST weight suggested by the concrete refutation of
`positiveTokenRootedBridgeCardEq`.

The root contributes `outdeg(last)!`, while each active non-root row
contributes `(outdeg(v) - 1)!`. This is a concrete normalization factor only;
the corresponding exact bridge theorem is still open and should be treated as a
conjectural replacement target until it is actually proved. -/
def positiveTokenRootedBestWeight
    (s : MarkovState k) : ℕ :=
  (MarkovDeFinettiHardEuler.outdeg (k := k) s s.last).factorial *
    ∏ u : PositiveNonrootVertex (k := k) (graphOfState (k := k) s) s.last,
      (MarkovDeFinettiHardEuler.outdeg (k := k) s u.1 - 1).factorial

/-- Exact finite-state bridge input in cardinality form. If the Euler-trail
count factors as token-rooted arborescences times the outdegree-factorial
weight, then the normalized Euler correction is exactly the token-rooted
arborescence count. This is the more concrete finite combinatorial surface
behind the later bridge theorems. -/
lemma normalizedEulerTrailCorrection_eq_tokenRootedArborescenceCount_of_card_eq
    {s : MarkovState k}
    (hcard :
      (eulerTrailFinset (graphOfState s) s.start s.last).card =
        tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
          outdegFactorialWeight (k := k) s) :
    normalizedEulerTrailCorrection (k := k) s =
      tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last := by
  unfold normalizedEulerTrailCorrection
  have hden :
      ((outdegFactorialWeight (k := k) s : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast outdegFactorialWeight_ne_zero (k := k) s
  apply (div_eq_iff hden).2
  exact_mod_cast hcard

lemma normalizedEulerTrailCorrection_eq_tokenRootedArborescenceCount_of_tokenRootedBridgeCardEq
    {s : MarkovState k}
    (hs : tokenRootedBridgeCardEq (k := k) s) :
    normalizedEulerTrailCorrection (k := k) s =
      tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last :=
  normalizedEulerTrailCorrection_eq_tokenRootedArborescenceCount_of_card_eq
    (k := k) hs

lemma normalizedEulerTrailCorrection_eq_positiveTokenRootedArborescenceCount_of_positiveTokenRootedBridgeCardEq
    {s : MarkovState k}
    (hs : positiveTokenRootedBridgeCardEq (k := k) s) :
    normalizedEulerTrailCorrection (k := k) s =
      positiveTokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last :=
  by
    unfold normalizedEulerTrailCorrection
    have hden :
        ((outdegFactorialWeight (k := k) s : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast outdegFactorialWeight_ne_zero (k := k) s
    apply (div_eq_iff hden).2
    exact_mod_cast hs

lemma tokenRootedBridgeCardEq_of_positiveTokenRootedBridgeCardEq_of_forall_pos
    {s : MarkovState k}
    (hs : positiveTokenRootedBridgeCardEq (k := k) s)
    (hpos :
      ∀ u : NonrootVertex s.last,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k) s u.1) :
    tokenRootedBridgeCardEq (k := k) s := by
  have hpos' :
      ∀ u : NonrootVertex s.last,
        0 < outDegG (k := k) (graphOfState (k := k) s) u.1 := by
    intro u
    simpa [outDeg_graphOfState_eq] using hpos u
  change
    (eulerTrailFinset (graphOfState s) s.start s.last).card =
      tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
        outdegFactorialWeight (k := k) s
  change
    (eulerTrailFinset (graphOfState s) s.start s.last).card =
      positiveTokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
        outdegFactorialWeight (k := k) s at hs
  rw [positiveTokenRootedArborescenceCount_eq_tokenRootedArborescenceCount_of_forall_pos
    (k := k) (G := graphOfState (k := k) s) (t := s.last) hpos'] at hs
  exact hs

lemma positiveTokenRootedBridgeCardEq_of_tokenRootedBridgeCardEq_of_forall_pos
    {s : MarkovState k}
    (hs : tokenRootedBridgeCardEq (k := k) s)
    (hpos :
      ∀ u : NonrootVertex s.last,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k) s u.1) :
    positiveTokenRootedBridgeCardEq (k := k) s := by
  have hpos' :
      ∀ u : NonrootVertex s.last,
        0 < outDegG (k := k) (graphOfState (k := k) s) u.1 := by
    intro u
    simpa [outDeg_graphOfState_eq] using hpos u
  change
    (eulerTrailFinset (graphOfState s) s.start s.last).card =
      positiveTokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
        outdegFactorialWeight (k := k) s
  change
    (eulerTrailFinset (graphOfState s) s.start s.last).card =
      tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
        outdegFactorialWeight (k := k) s at hs
  rw [positiveTokenRootedArborescenceCount_eq_tokenRootedArborescenceCount_of_forall_pos
    (k := k) (G := graphOfState (k := k) s) (t := s.last) hpos']
  exact hs

lemma positiveTokenRootedBridgeCardEq_iff_tokenRootedBridgeCardEq_of_forall_pos
    {s : MarkovState k}
    (hpos :
      ∀ u : NonrootVertex s.last,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k) s u.1) :
    positiveTokenRootedBridgeCardEq (k := k) s ↔ tokenRootedBridgeCardEq (k := k) s := by
  constructor
  · intro hs
    exact tokenRootedBridgeCardEq_of_positiveTokenRootedBridgeCardEq_of_forall_pos
      (k := k) hs hpos
  · intro hs
    exact positiveTokenRootedBridgeCardEq_of_tokenRootedBridgeCardEq_of_forall_pos
      (k := k) hs hpos

lemma positiveTokenRootedBridgeCardEq_iff_card_eq_outdegFactorialWeight_of_forall_nonroot_outdeg_zero
    {s : MarkovState k}
    (hzero :
      ∀ u : NonrootVertex s.last,
        MarkovDeFinettiHardEuler.outdeg (k := k) s u.1 = 0) :
    positiveTokenRootedBridgeCardEq (k := k) s ↔
      (eulerTrailFinset (graphOfState s) s.start s.last).card =
        outdegFactorialWeight (k := k) s := by
  have hzero' :
      ∀ u : NonrootVertex s.last,
        outDegG (k := k) (graphOfState (k := k) s) u.1 = 0 := by
    intro u
    simpa [outDeg_graphOfState_eq] using hzero u
  rw [positiveTokenRootedBridgeCardEq]
  rw [positiveTokenRootedArborescenceCount_eq_one_of_forall_nonroot_outdeg_zero
    (k := k) (G := graphOfState (k := k) s) (t := s.last) hzero']
  simp

/-! ## Permanent counterexample to the legacy support-local bridge weight

The direct-route bridge predicate `positiveTokenRootedBridgeCardEq` is not just
unproved; it is false on the concrete active evidence state induced by the word
`0,1,0,1`. This section records that fact permanently so future work does not
keep trying to prove the wrong normalization. The corrected weight
`positiveTokenRootedBestWeight` does match the same example, but the general
BEST theorem for that corrected normalization remains open. -/

/-- Concrete four-symbol trajectory `0,1,0,1` used to refute the legacy
support-local bridge weight. -/
def positiveTokenRootedBridgeCounterexampleTraj0101 : Traj 2 3 := ![0, 1, 0, 1]

/-- Evidence state of `positiveTokenRootedBridgeCounterexampleTraj0101`. -/
def positiveTokenRootedBridgeCounterexampleState0101 : MarkovState 2 :=
  stateOfTraj (k := 2) positiveTokenRootedBridgeCounterexampleTraj0101

lemma positiveTokenRootedBridgeCounterexampleState0101_mem_stateFinset :
    positiveTokenRootedBridgeCounterexampleState0101 ∈ stateFinset 2 3 :=
  stateOfTraj_mem_stateFinset
    (k := 2) positiveTokenRootedBridgeCounterexampleTraj0101

lemma eulerTrailFinset_card_counterexample_0101 :
    (eulerTrailFinset
        (graphOfState positiveTokenRootedBridgeCounterexampleState0101)
        positiveTokenRootedBridgeCounterexampleState0101.start
        positiveTokenRootedBridgeCounterexampleState0101.last).card = 2 := by
  rw [eulerTrailFinset_card_eq
    (k := 2) positiveTokenRootedBridgeCounterexampleState0101
    positiveTokenRootedBridgeCounterexampleState0101_mem_stateFinset]
  decide

lemma positiveTokenRootedArborescenceCount_counterexample_0101 :
    positiveTokenRootedArborescenceCount
        (k := 2) (graphOfState positiveTokenRootedBridgeCounterexampleState0101) 1 = 2 := by
  have htok :
      ∀ tok : outTok (k := 2) (graphOfState positiveTokenRootedBridgeCounterexampleState0101) 0,
        tok.1 = 1 := by
    rintro ⟨b, i⟩
    fin_cases b
    · exact i.elim0
    · rfl
  have hall :
      ∀ A : PositiveTokenParentAssignment
          (k := 2) (graphOfState positiveTokenRootedBridgeCounterexampleState0101) 1,
        IsPositiveTokenRootedArborescence
          (k := 2) (graphOfState positiveTokenRootedBridgeCounterexampleState0101) 1 A := by
    intro A v
    obtain ⟨v, hv1, hv2⟩ := v
    have hv0 : v = 0 := by
      omega
    subst hv0
    refine ⟨1, by norm_num, ?_⟩
    simp only [Function.iterate_one, positiveTargetParentStep, positiveTokenParentTargets]
    rw [dif_neg (by decide), dif_pos (by decide)]
    exact htok _
  unfold positiveTokenRootedArborescenceCount
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [card_outTok]
  decide

/-- The legacy support-local bridge predicate is refuted by the active evidence
state coming from the word `0,1,0,1`. -/
theorem positiveTokenRootedBridgeCardEq_false_on_counterexample_0101 :
    ¬ positiveTokenRootedBridgeCardEq (k := 2) positiveTokenRootedBridgeCounterexampleState0101 := by
  intro hbridge
  unfold positiveTokenRootedBridgeCardEq at hbridge
  rw [eulerTrailFinset_card_counterexample_0101,
      show outdegFactorialWeight (k := 2) positiveTokenRootedBridgeCounterexampleState0101 = 2 by
        decide,
      show positiveTokenRootedBridgeCounterexampleState0101.last = 1 by
        decide,
      positiveTokenRootedArborescenceCount_counterexample_0101] at hbridge
  omega

/-- The corrected support-local BEST weight matches the same example. This does
not prove the corrected bridge theorem in general; it only pins the right local
constant on the concrete counterexample state. -/
theorem corrected_positiveTokenRootedBestWeight_bridge_holds_on_counterexample_0101 :
    (eulerTrailFinset
        (graphOfState positiveTokenRootedBridgeCounterexampleState0101)
        positiveTokenRootedBridgeCounterexampleState0101.start
        positiveTokenRootedBridgeCounterexampleState0101.last).card =
      positiveTokenRootedArborescenceCount
          (k := 2) (graphOfState positiveTokenRootedBridgeCounterexampleState0101)
          positiveTokenRootedBridgeCounterexampleState0101.last *
        positiveTokenRootedBestWeight
          (k := 2) positiveTokenRootedBridgeCounterexampleState0101 := by
  rw [eulerTrailFinset_card_counterexample_0101,
      show positiveTokenRootedBridgeCounterexampleState0101.last = 1 by
        decide,
      positiveTokenRootedArborescenceCount_counterexample_0101]
  decide

lemma row_eq_zero_of_outDegG_eq_zero
    {t : Fin k} {G : EulerGraph k} {u : NonrootVertex t}
    (hout : outDegG (k := k) G u.1 = 0) :
    ∀ v : Fin k, G u.1 v = 0 := by
  intro v
  have hvle : G u.1 v ≤ outDegG (k := k) G u.1 := by
    unfold outDegG
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  exact Nat.eq_zero_of_le_zero (by simpa [hout] using hvle)

lemma col_eq_zero_of_inDegG_eq_zero
    {t : Fin k} {G : EulerGraph k} {u : NonrootVertex t}
    (hin : inDegG (k := k) G u.1 = 0) :
    ∀ v : Fin k, G v u.1 = 0 := by
  intro v
  have hvle : G v u.1 ≤ inDegG (k := k) G u.1 := by
    unfold inDegG
    exact
      Finset.single_le_sum
        (f := fun a : Fin k => G a u.1)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ v)
  exact Nat.eq_zero_of_le_zero (by simpa [hin] using hvle)

lemma inDegG_eq_zero_of_outdeg_eq_zero_of_mem_stateFinset
    {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N)
    {u : NonrootVertex eN.last}
    (hout : MarkovDeFinettiHardEuler.outdeg (k := k) eN u.1 = 0) :
    inDegG (k := k) (graphOfState (k := k) eN) u.1 = 0 := by
  have hout' : outDegG (k := k) (graphOfState (k := k) eN) u.1 = 0 := by
    simpa [outDeg_graphOfState_eq] using hout
  have hlast_ne : eN.last ≠ u.1 := u.2.symm
  have hbal :=
    MarkovDeFinettiHardBESTCore.flow_balance_graphOfState_of_mem_stateFinset
      (k := k) heN u.1
  have hstart_ne : eN.start ≠ u.1 := by
    intro hstart
    have hzero :
        0 = inDegG (k := k) (graphOfState (k := k) eN) u.1 + 1 := by
      have hbal' := hbal
      simp [hout', hlast_ne, hstart] at hbal'
    have hsucc :
        inDegG (k := k) (graphOfState (k := k) eN) u.1 + 1 ≠ 0 := by
      simp [Nat.add_comm]
    exact hsucc hzero.symm
  have hzero :
      0 = inDegG (k := k) (graphOfState (k := k) eN) u.1 + 0 := by
    have hbal' := hbal
    simp [hout', hlast_ne, hstart_ne] at hbal'
    exact hbal'
  simp at hzero
  exact hzero.symm

lemma start_ne_of_outdeg_eq_zero_of_mem_stateFinset
    {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N)
    {u : NonrootVertex eN.last}
    (hout : MarkovDeFinettiHardEuler.outdeg (k := k) eN u.1 = 0) :
    eN.start ≠ u.1 := by
  have hout' : outDegG (k := k) (graphOfState (k := k) eN) u.1 = 0 := by
    simpa [outDeg_graphOfState_eq] using hout
  have hlast_ne : eN.last ≠ u.1 := u.2.symm
  have hbal :=
    MarkovDeFinettiHardBESTCore.flow_balance_graphOfState_of_mem_stateFinset
      (k := k) heN u.1
  intro hstart
  have hzero :
      0 = inDegG (k := k) (graphOfState (k := k) eN) u.1 + 1 := by
    have hbal' := hbal
    simp [hout', hlast_ne, hstart] at hbal'
  have hsucc :
      inDegG (k := k) (graphOfState (k := k) eN) u.1 + 1 ≠ 0 := by
    simp [Nat.add_comm]
  exact hsucc hzero.symm

lemma graphOfState_col_eq_zero_of_outdeg_eq_zero_of_mem_stateFinset
    {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N)
    {u : NonrootVertex eN.last}
    (hout : MarkovDeFinettiHardEuler.outdeg (k := k) eN u.1 = 0) :
    ∀ v : Fin k, graphOfState eN v u.1 = 0 := by
  exact
    col_eq_zero_of_inDegG_eq_zero
      (k := k) (G := graphOfState (k := k) eN) (u := u)
      (inDegG_eq_zero_of_outdeg_eq_zero_of_mem_stateFinset
        (k := k) heN hout)

lemma graphOfState_row_eq_zero_of_outdeg_eq_zero
    {eN : MarkovState k} {u : NonrootVertex eN.last}
    (hout : MarkovDeFinettiHardEuler.outdeg (k := k) eN u.1 = 0) :
    ∀ v : Fin k, graphOfState eN u.1 v = 0 := by
  have hout' : outDegG (k := k) (graphOfState (k := k) eN) u.1 = 0 := by
    simpa [outDeg_graphOfState_eq] using hout
  exact row_eq_zero_of_outDegG_eq_zero (k := k) (G := graphOfState (k := k) eN) hout'

lemma not_tokenRootedBridgeCardEq_of_exists_nonroot_zero_row_of_mem_stateFinset
    {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N)
    (hzero : ∃ u : NonrootVertex eN.last, ∀ v : Fin k, graphOfState eN u.1 v = 0) :
    ¬ tokenRootedBridgeCardEq (k := k) eN := by
  intro hBridge
  have hcard_pos :
      0 < (eulerTrailFinset (graphOfState eN) eN.start eN.last).card := by
    rw [eulerTrailFinset_card_eq (k := k) eN heN]
    exact Nat.mul_pos
      (Nat.pos_iff_ne_zero.mpr <|
        fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN)
      (graphFactorialWeight_pos (k := k) eN)
  have harb_zero :
      tokenRootedArborescenceCount (k := k) (graphOfState eN) eN.last = 0 := by
    exact
      tokenRootedArborescenceCount_eq_zero_of_exists_nonroot_zero_row
        (k := k) (G := graphOfState eN) (t := eN.last) hzero
  have hcard_zero :
      (eulerTrailFinset (graphOfState eN) eN.start eN.last).card = 0 := by
    simpa [tokenRootedBridgeCardEq, harb_zero] using hBridge
  exact (Nat.ne_of_gt hcard_pos) hcard_zero

lemma not_tokenRootedBridgeCardEq_of_exists_nonroot_outdeg_zero_of_mem_stateFinset
    {N : ℕ} {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N)
    (hzero :
      ∃ u : NonrootVertex eN.last,
        MarkovDeFinettiHardEuler.outdeg (k := k) eN u.1 = 0) :
    ¬ tokenRootedBridgeCardEq (k := k) eN := by
  apply not_tokenRootedBridgeCardEq_of_exists_nonroot_zero_row_of_mem_stateFinset
    (k := k) heN
  rcases hzero with ⟨u, hu⟩
  exact ⟨u, graphOfState_row_eq_zero_of_outdeg_eq_zero (k := k) hu⟩

/-- Legacy bridge reduction: any specialized theorem identifying
`normalizedEulerTrailCorrection` with token-rooted arborescence counts on
balanced `graphOfState` graphs immediately transfers the normalized correction
ratio to the token-rooted arborescence ratio.

This transport lemma remains mathematically valid, but it sits on top of the
refuted `outdegFactorialWeight` normalization. The live direct-route repair is
to rebuild the same transport around `positiveTokenRootedBestWeight`, not to
keep strengthening the old bridge predicate. -/
lemma prefixNormalizedEulerTrailCorrectionRatio_eq_prefixTokenRootedArborescenceRatio_of_bridge
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN =
      prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  rcases hcomp with ⟨heN, _, hres⟩
  unfold prefixNormalizedEulerTrailCorrectionRatio prefixTokenRootedArborescenceRatio
  rw [hBridge (M := N - ys.length) hres, hBridge (M := N) heN]

/-- Real-valued bridge reduction for the normalized correction ratio. -/
lemma prefixNormalizedEulerTrailCorrectionRatioReal_eq_prefixTokenRootedArborescenceRatioReal_of_bridge
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys N hN eN =
      prefixTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  change ((prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN : ℚ) : ℝ) =
      ((prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN : ℚ) : ℝ)
  exact congrArg (fun q : ℚ => (q : ℝ))
    (prefixNormalizedEulerTrailCorrectionRatio_eq_prefixTokenRootedArborescenceRatio_of_bridge
      (k := k) a ys N hN eN hcomp hBridge)

/-- Exact bridge reduction through the support-local rooted-arborescence count. -/
lemma prefixNormalizedEulerTrailCorrectionRatio_eq_prefixPositiveTokenRootedArborescenceRatio_of_positiveBridge
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            positiveTokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN =
      prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  rcases hcomp with ⟨heN, _, hres⟩
  unfold prefixNormalizedEulerTrailCorrectionRatio
    prefixPositiveTokenRootedArborescenceRatio
  rw [hBridge (M := N - ys.length) hres, hBridge (M := N) heN]

/-- Real-valued support-local bridge reduction for the normalized correction
ratio. -/
lemma prefixNormalizedEulerTrailCorrectionRatioReal_eq_prefixPositiveTokenRootedArborescenceRatioReal_of_positiveBridge
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            positiveTokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys N hN eN =
      prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  change ((prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN : ℚ) : ℝ) =
      ((prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN : ℚ) : ℝ)
  exact congrArg (fun q : ℚ => (q : ℝ))
    (prefixNormalizedEulerTrailCorrectionRatio_eq_prefixPositiveTokenRootedArborescenceRatio_of_positiveBridge
      (k := k) a ys N hN eN hcomp hBridge)

/-- Tendsto reduction through the specialized token-rooted BEST bridge. -/
lemma tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_tendsto_prefixTokenRootedArborescenceRatioReal_of_bridge
    (a : Fin k) (ys : List (Fin k))
    (e : ℕ → MarkovState k) (Nf : ℕ → ℕ)
    (hN : ∀ n, ys.length ≤ Nf n)
    (hcomp : ∀ᶠ n in Filter.atTop, prefixCompatibleState (k := k) a ys (Nf n) (hN n) (e n))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last)
    (hlim :
      Filter.Tendsto
        (fun n => prefixTokenRootedArborescenceRatioReal (k := k) a ys (Nf n) (hN n) (e n))
        Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun n => prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys (Nf n) (hN n) (e n))
      Filter.atTop (nhds 1) := by
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [hcomp] with n hn
  exact (prefixNormalizedEulerTrailCorrectionRatioReal_eq_prefixTokenRootedArborescenceRatioReal_of_bridge
    (k := k) a ys (Nf n) (hN n) (e n) hn hBridge).symm

lemma prefixNormalizedEulerTrailCorrectionRatio_eq_prefixTokenRootedArborescenceRatio_of_bridgeCardEq_pair
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hfull : tokenRootedBridgeCardEq (k := k) eN)
    (hres :
      tokenRootedBridgeCardEq (k := k)
        (residualStateOfPrefix (k := k) a ys eN)) :
    prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN =
      prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  unfold prefixNormalizedEulerTrailCorrectionRatio prefixTokenRootedArborescenceRatio
  rw [normalizedEulerTrailCorrection_eq_tokenRootedArborescenceCount_of_tokenRootedBridgeCardEq
        (k := k) hres]
  rw [normalizedEulerTrailCorrection_eq_tokenRootedArborescenceCount_of_tokenRootedBridgeCardEq
        (k := k) hfull]

lemma prefixNormalizedEulerTrailCorrectionRatioReal_eq_prefixTokenRootedArborescenceRatioReal_of_bridgeCardEq_pair
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hfull : tokenRootedBridgeCardEq (k := k) eN)
    (hres :
      tokenRootedBridgeCardEq (k := k)
        (residualStateOfPrefix (k := k) a ys eN)) :
    prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys N hN eN =
      prefixTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  change ((prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN : ℚ) : ℝ) =
      ((prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN : ℚ) : ℝ)
  exact congrArg (fun q : ℚ => (q : ℝ))
    (prefixNormalizedEulerTrailCorrectionRatio_eq_prefixTokenRootedArborescenceRatio_of_bridgeCardEq_pair
      (k := k) a ys N hN eN hfull hres)

lemma prefixNormalizedEulerTrailCorrectionRatioReal_eq_prefixPositiveTokenRootedArborescenceRatioReal_of_positiveBridgeCardEq_pair
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hfull : positiveTokenRootedBridgeCardEq (k := k) eN)
    (hres :
      positiveTokenRootedBridgeCardEq (k := k)
        (residualStateOfPrefix (k := k) a ys eN)) :
    prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys N hN eN =
      prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  change ((prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN : ℚ) : ℝ) =
      ((prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN : ℚ) : ℝ)
  unfold prefixNormalizedEulerTrailCorrectionRatio
    prefixPositiveTokenRootedArborescenceRatio
  rw [normalizedEulerTrailCorrection_eq_positiveTokenRootedArborescenceCount_of_positiveTokenRootedBridgeCardEq
      (k := k) hres]
  rw [normalizedEulerTrailCorrection_eq_positiveTokenRootedArborescenceCount_of_positiveTokenRootedBridgeCardEq
      (k := k) hfull]

lemma tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_tendsto_prefixTokenRootedArborescenceRatioReal_of_bridgeCardEq_pair
    (a : Fin k) (ys : List (Fin k))
    (e : ℕ → MarkovState k) (Nf : ℕ → ℕ)
    (hN : ∀ n, ys.length ≤ Nf n)
    (hBridgePair :
      ∀ᶠ n in Filter.atTop,
        tokenRootedBridgeCardEq (k := k) (e n) ∧
          tokenRootedBridgeCardEq (k := k)
            (residualStateOfPrefix (k := k) a ys (e n)))
    (hlim :
      Filter.Tendsto
        (fun n => prefixTokenRootedArborescenceRatioReal (k := k) a ys (Nf n) (hN n) (e n))
        Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun n => prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys (Nf n) (hN n) (e n))
      Filter.atTop (nhds 1) := by
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [hBridgePair] with n hn
  exact
    (prefixNormalizedEulerTrailCorrectionRatioReal_eq_prefixTokenRootedArborescenceRatioReal_of_bridgeCardEq_pair
      (k := k) a ys (Nf n) (hN n) (e n) hn.1 hn.2).symm

lemma tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_positiveBridgeCardEq_pair
    (a : Fin k) (ys : List (Fin k))
    (e : ℕ → MarkovState k) (Nf : ℕ → ℕ)
    (hN : ∀ n, ys.length ≤ Nf n)
    (hBridgePair :
      ∀ᶠ n in Filter.atTop,
        positiveTokenRootedBridgeCardEq (k := k) (e n) ∧
          positiveTokenRootedBridgeCardEq (k := k)
            (residualStateOfPrefix (k := k) a ys (e n)))
    (hlim :
      Filter.Tendsto
        (fun n => prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys (Nf n) (hN n) (e n))
        Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun n => prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys (Nf n) (hN n) (e n))
      Filter.atTop (nhds 1) := by
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [hBridgePair] with n hn
  exact
    (prefixNormalizedEulerTrailCorrectionRatioReal_eq_prefixPositiveTokenRootedArborescenceRatioReal_of_positiveBridgeCardEq_pair
      (k := k) a ys (Nf n) (hN n) (e n) hn.1 hn.2).symm

lemma prefixRatioFn_eq_prefixHypergeometricFactor_mul_prefixBridgeCorrection_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixRatioFn (k := k) a ys N hN eN =
      prefixHypergeometricFactor (k := k) a ys eN *
        prefixBridgeCorrection (k := k) a ys N hN eN := by
  have hH :
      prefixHypergeometricFactor (k := k) a ys eN ≠ 0 :=
    prefixHypergeometricFactor_ne_zero_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp
  calc
    prefixRatioFn (k := k) a ys N hN eN
        = prefixBESTRatioExplicit (k := k) a ys N hN eN := by
            exact prefixRatioFn_eq_prefixBESTRatioExplicit_of_prefixCompatibleState
              (k := k) a ys N hN eN hcomp
    _ = prefixHypergeometricFactor (k := k) a ys eN *
          prefixBridgeCorrection (k := k) a ys N hN eN := by
          unfold prefixBridgeCorrection
          field_simp [hH]

/-- Real version of the edge-level hypergeometric factor. -/
def prefixHypergeometricEdgeFactorReal
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k)
    (i j : Fin k) : ℝ :=
  ((((eN.counts.counts i j).descFactorial
      ((prefixWordState (k := k) a ys).counts.counts i j)) : ℕ) : ℝ) /
    (((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℝ) ^
      ((prefixWordState (k := k) a ys).counts.counts i j))

/-- Real version of the row-level hypergeometric correction. -/
def prefixHypergeometricRowCorrectionReal
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k)
    (i : Fin k) : ℝ :=
  ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i : ℕ) : ℝ) ^
      (MarkovDeFinettiHardEuler.outdeg (k := k)
        (prefixWordState (k := k) a ys) i))) /
    ((((MarkovDeFinettiHardEuler.outdeg (k := k) eN i).descFactorial
        (MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i)) : ℕ) : ℝ)

/-- Real hypergeometric factor for asymptotic analysis. -/
def prefixHypergeometricFactorReal
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : ℝ :=
  ∏ i : Fin k,
    (∏ j : Fin k, prefixHypergeometricEdgeFactorReal (k := k) a ys eN i j) *
      prefixHypergeometricRowCorrectionReal (k := k) a ys eN i

/-- Count-form target for the hypergeometric limit. This is the prefix-step
product regrouped by edge multiplicities in the fixed word `a :: ys`. -/
def prefixThetaPowerProduct
    (a : Fin k) (ys : List (Fin k)) (Θ : Fin k → Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, ∏ j : Fin k,
    (Θ i j) ^ ((prefixWordState (k := k) a ys).counts.counts i j)

/-! ### Connection between prefixThetaPowerProduct and rowKernelStepProd

The grouped power-product `prefixThetaPowerProduct` equals the sequential
`rowKernelStepProd` when `Θ` encodes the row-kernel transition probabilities.
This is the usual regrouping identity for a finite word:
the product over successive transitions equals the product over edge labels,
with each label raised to its transition count in the word.
-/

/-- Key count decomposition: prepending `a` to word `b :: rest` adds exactly
one transition count for (a, b), leaving all other counts unchanged. -/
lemma prefixWordState_counts_cons (a b : Fin k) (rest : List (Fin k)) (i j : Fin k) :
    (prefixWordState (k := k) a (b :: rest)).counts.counts i j =
      (if i = a ∧ j = b then 1 else 0) +
        (prefixWordState (k := k) b rest).counts.counts i j := by
  have hsplit :=
    transCount_eq_transCount_trajPrefix_add_transCount_trajDrop
      (k := k) (N := rest.length + 1) (n := 1)
      (h := Nat.succ_le_succ (Nat.zero_le rest.length))
      (xs := wordTraj (k := k) a (b :: rest)) i j
  have hdrop :
      trajDrop (k := k) 1 (Nat.succ_le_succ (Nat.zero_le rest.length))
        (wordTraj (k := k) a (b :: rest)) =
        wordTraj (k := k) b rest := by
    funext t
    change (a :: b :: rest).getD (t.1 + 1) a = (b :: rest).getD t.1 b
    rw [List.getD_cons_succ]
    have ht : t.1 < (b :: rest).length := by
      simpa using t.2
    rw [List.getD_eq_getElem (l := b :: rest) (d := a) ht]
    rw [List.getD_eq_getElem (l := b :: rest) (d := b) ht]
  have hpref :
      transCount (n := 1)
        (trajPrefix (k := k) (n := 1) (N := rest.length + 1)
          (Nat.succ_le_succ (Nat.zero_le rest.length))
          (wordTraj (k := k) a (b :: rest))) i j =
        (if i = a ∧ j = b then 1 else 0) := by
    by_cases h : i = a ∧ j = b
    · rcases h with ⟨rfl, rfl⟩
      simp [transCount, trajPrefix, wordTraj]
    · have h' : ¬ (a = i ∧ b = j) := by
        intro hab
        exact h ⟨hab.1.symm, hab.2.symm⟩
      simp [transCount, trajPrefix, wordTraj, h, h']
  simpa [prefixWordState, stateOfTraj, countsOfFn, hdrop, hpref]
    using hsplit

/-- The grouped power-product decomposes when prepending to a word. -/
lemma prefixThetaPowerProduct_cons (a b : Fin k) (rest : List (Fin k))
    (Θ : Fin k → Fin k → ℝ) :
    prefixThetaPowerProduct (k := k) a (b :: rest) Θ =
      Θ a b * prefixThetaPowerProduct (k := k) b rest Θ := by
  classical
  unfold prefixThetaPowerProduct
  conv_lhs =>
    congr
    · skip
    · ext i
      congr
      · skip
      · ext j
        rw [prefixWordState_counts_cons (k := k) a b rest i j]
  simp only [pow_add]
  calc
    (∏ i : Fin k,
        ∏ j : Fin k,
          (Θ i j ^ (if i = a ∧ j = b then 1 else 0)) *
            Θ i j ^ (prefixWordState (k := k) b rest).counts.counts i j) =
      (∏ i : Fin k, ∏ j : Fin k, Θ i j ^ (if i = a ∧ j = b then 1 else 0)) *
        (∏ i : Fin k, ∏ j : Fin k,
          Θ i j ^ (prefixWordState (k := k) b rest).counts.counts i j) := by
        simp_rw [Finset.prod_mul_distrib]
    _ = Θ a b * ∏ i : Fin k, ∏ j : Fin k,
          Θ i j ^ (prefixWordState (k := k) b rest).counts.counts i j := by
        congr 1
        rw [Fintype.prod_eq_single a]
        · rw [Fintype.prod_eq_single b]
          · simp
          · intro j hj
            simp [hj]
        · intro i hi
          have hfalse : ∀ j : Fin k, ¬ (i = a ∧ j = b) := by
            intro j hij
            exact hi hij.1
          simp [hfalse]

/-- When Θ encodes row-kernel probabilities, `prefixThetaPowerProduct` equals
`rowKernelStepProd.toReal`. This is the key identity connecting the asymptotic
limit of prefix ratios to the row-kernel mixture formula.
-/
theorem prefixThetaPowerProduct_eq_rowKernelStepProd_toReal
    (a : Fin k) (ys : List (Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (ω : ℕ → Fin k)
    (Θ : Fin k → Fin k → ℝ)
    (hΘ : ∀ i j, Θ i j =
      ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal) :
    prefixThetaPowerProduct (k := k) a ys Θ =
      (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal := by
  induction ys generalizing a with
  | nil =>
      simp only [prefixThetaPowerProduct, rowKernelStepProd, ENNReal.toReal_one]
      simp only [prefixWordState, stateOfTraj, countsOfFn, transCount]
      simp [Finset.prod_eq_one]
  | cons b rest ih =>
      rw [prefixThetaPowerProduct_cons (k := k) a b rest Θ]
      simp only [rowKernelStepProd]
      rw [ENNReal.toReal_mul]
      congr 1
      · exact hΘ a b
      · exact ih b

@[simp] lemma prefixHypergeometricFactorReal_eq_ratCast
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    prefixHypergeometricFactorReal (k := k) a ys eN =
      (prefixHypergeometricFactor (k := k) a ys eN : ℝ) := by
  simp [prefixHypergeometricFactorReal, prefixHypergeometricFactor,
    prefixHypergeometricEdgeFactorReal, prefixHypergeometricEdgeFactor,
    prefixHypergeometricRowCorrectionReal, prefixHypergeometricRowCorrection]

private lemma prod_nat_sub_div_by_const (u v r : ℕ) :
    (∏ i ∈ Finset.range r, (((u - i : ℕ) : ℝ) / (v : ℝ))) =
      (∏ i ∈ Finset.range r, ((u - i : ℕ) : ℝ)) / (v : ℝ) ^ r := by
  classical
  simp [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, mul_comm]

private lemma cast_descFactorial_div_pow_eq_prod_nat_sub_div (u v r : ℕ) :
    ((u.descFactorial r : ℝ) / (v : ℝ) ^ r) =
      ∏ i ∈ Finset.range r, (((u - i : ℕ) : ℝ) / (v : ℝ)) := by
  have hnat : u.descFactorial r = ∏ i ∈ Finset.range r, (u - i) :=
    Nat.descFactorial_eq_prod_range u r
  have hcast :
      ((u.descFactorial r : ℕ) : ℝ) =
        ∏ i ∈ Finset.range r, ((u - i : ℕ) : ℝ) := by
    simpa using congrArg (fun t : ℕ => (t : ℝ)) hnat
  calc
    ((u.descFactorial r : ℝ) / (v : ℝ) ^ r)
        = (∏ i ∈ Finset.range r, ((u - i : ℕ) : ℝ)) / (v : ℝ) ^ r := by
            simp [hcast]
    _ = ∏ i ∈ Finset.range r, (((u - i : ℕ) : ℝ) / (v : ℝ)) := by
          symm
          exact prod_nat_sub_div_by_const u v r

private lemma tendsto_const_div_natcast_atTop_zero
    (c : ℝ) {v : ℕ → ℕ}
    (hv : Filter.Tendsto (fun n => (v n : ℝ)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => c / (v n : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
  have hinv :
      Filter.Tendsto (fun n => ((v n : ℝ)⁻¹))
        Filter.atTop (nhds (0 : ℝ)) := by
    exact (tendsto_inv_atTop_zero.comp hv)
  simpa [div_eq_mul_inv, zero_mul] using
    (tendsto_const_nhds.mul hinv)

private lemma tendsto_nat_sub_cast_div_of_div
    {u v : ℕ → ℕ} {θ : ℝ} (c : ℕ)
    (hdiv :
      Filter.Tendsto (fun n => (u n : ℝ) / (v n : ℝ))
        Filter.atTop (nhds θ))
    (hv : Filter.Tendsto (fun n => (v n : ℝ)) Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => (((u n - c : ℕ) : ℝ) / (v n : ℝ)))
      Filter.atTop (nhds θ) := by
  have hminZero :
      Filter.Tendsto
        (fun n => (((Nat.min (u n) c : ℕ) : ℝ) / (v n : ℝ)))
        Filter.atTop (nhds (0 : ℝ)) := by
    have hupper :
        Filter.Tendsto (fun n => (c : ℝ) / (v n : ℝ))
          Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_const_div_natcast_atTop_zero (c := c) hv
    refine squeeze_zero
      (fun n => by positivity)
      (fun n => ?_)
      hupper
    by_cases hv0 : v n = 0
    · simp [hv0]
    · have hvpos : 0 ≤ (v n : ℝ) := by positivity
      have hminLe : (((Nat.min (u n) c : ℕ) : ℝ)) ≤ (c : ℝ) := by
        exact_mod_cast (Nat.min_le_right (u n) c)
      exact div_le_div_of_nonneg_right hminLe hvpos
  have hEq :
      (fun n => (((u n - c : ℕ) : ℝ) / (v n : ℝ))) =ᶠ[Filter.atTop]
        (fun n => (u n : ℝ) / (v n : ℝ) -
          (((Nat.min (u n) c : ℕ) : ℝ) / (v n : ℝ))) := by
    have hv1 : ∀ᶠ n in Filter.atTop, (1 : ℝ) ≤ (v n : ℝ) := by
      have hmem : Set.Ici (1 : ℝ) ∈ (Filter.atTop : Filter ℝ) := by
        refine Filter.mem_atTop_sets.2 ?_
        exact ⟨1, fun b hb => hb⟩
      exact hv hmem
    filter_upwards [hv1] with n hn
    have hvpos : 0 < (v n : ℝ) := by linarith
    have hvne : (v n : ℝ) ≠ 0 := ne_of_gt hvpos
    have hsubNat : (u n - c) + Nat.min (u n) c = u n := by
      exact tsub_add_min
    have hsubReal :
        (((u n - c : ℕ) : ℝ)) =
          (u n : ℝ) - (((Nat.min (u n) c : ℕ) : ℝ)) := by
      have hcast :
          (((u n - c : ℕ) : ℝ) + (((Nat.min (u n) c : ℕ) : ℝ))) = (u n : ℝ) := by
        exact_mod_cast hsubNat
      linarith
    have hfirst :
        (((u n - c : ℕ) : ℝ) / (v n : ℝ)) =
          (((u n : ℝ) - (((Nat.min (u n) c : ℕ) : ℝ))) / (v n : ℝ)) :=
      congrArg (fun t : ℝ => t / (v n : ℝ)) hsubReal
    have hsecond :
        (((u n : ℝ) - (((Nat.min (u n) c : ℕ) : ℝ))) / (v n : ℝ)) =
          (u n : ℝ) / (v n : ℝ) -
            (((Nat.min (u n) c : ℕ) : ℝ) / (v n : ℝ)) := by
      field_simp [hvne]
    have hdivEq :
        (((u n - c : ℕ) : ℝ) / (v n : ℝ)) =
          (u n : ℝ) / (v n : ℝ) -
            (((Nat.min (u n) c : ℕ) : ℝ) / (v n : ℝ)) := by
      exact hfirst.trans hsecond
    exact hdivEq
  have hlim :
      Filter.Tendsto
        (fun n => (u n : ℝ) / (v n : ℝ) -
          (((Nat.min (u n) c : ℕ) : ℝ) / (v n : ℝ)))
        Filter.atTop (nhds (θ - 0)) := by
    exact hdiv.sub hminZero
  have hlim' := hlim.congr' hEq.symm
  simpa [sub_zero] using hlim'

private lemma tendsto_self_div_of_tendsto_atTop
    {v : ℕ → ℕ}
    (hv : Filter.Tendsto (fun n => (v n : ℝ)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => (v n : ℝ) / (v n : ℝ))
      Filter.atTop (nhds (1 : ℝ)) := by
  have hEq :
      (fun n => (v n : ℝ) / (v n : ℝ)) =ᶠ[Filter.atTop]
        fun _ => (1 : ℝ) := by
    have hv1 : ∀ᶠ n in Filter.atTop, (1 : ℝ) ≤ (v n : ℝ) := by
      have hmem : Set.Ici (1 : ℝ) ∈ (Filter.atTop : Filter ℝ) := by
        refine Filter.mem_atTop_sets.2 ?_
        exact ⟨1, fun b hb => hb⟩
      exact hv hmem
    filter_upwards [hv1] with n hn
    have hvpos : 0 < (v n : ℝ) := by linarith
    have hvne : (v n : ℝ) ≠ 0 := ne_of_gt hvpos
    field_simp [hvne]
  exact (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
    Filter.atTop (nhds (1 : ℝ))).congr' hEq.symm

private lemma tendsto_descFactorial_div_pow_of_ratio
    {u v : ℕ → ℕ} {θ : ℝ} (r : ℕ)
    (hdiv :
      Filter.Tendsto (fun n => (u n : ℝ) / (v n : ℝ))
        Filter.atTop (nhds θ))
    (hv : Filter.Tendsto (fun n => (v n : ℝ)) Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => ((u n).descFactorial r : ℝ) / (v n : ℝ) ^ r)
      Filter.atTop (nhds (θ ^ r)) := by
  have hEq :
      (fun n => ((u n).descFactorial r : ℝ) / (v n : ℝ) ^ r) =ᶠ[Filter.atTop]
        (fun n => ∏ i ∈ Finset.range r, (((u n - i : ℕ) : ℝ) / (v n : ℝ))) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    exact cast_descFactorial_div_pow_eq_prod_nat_sub_div (u n) (v n) r
  have hprod :
      Filter.Tendsto
        (fun n => ∏ i ∈ Finset.range r, (((u n - i : ℕ) : ℝ) / (v n : ℝ)))
        Filter.atTop
        (nhds (∏ i ∈ Finset.range r, θ)) := by
    refine tendsto_finset_prod (s := Finset.range r) ?_
    intro i hi
    exact tendsto_nat_sub_cast_div_of_div (c := i) hdiv hv
  have htarget : (∏ i ∈ Finset.range r, θ) = θ ^ r := by
    simp
  have hprod' :
      Filter.Tendsto
        (fun n => ∏ i ∈ Finset.range r, (((u n - i : ℕ) : ℝ) / (v n : ℝ)))
        Filter.atTop (nhds (θ ^ r)) := by
    simpa [htarget] using hprod
  exact hprod'.congr' hEq.symm

lemma tendsto_prefixHypergeometricFactorReal
    (a : Fin k) (ys : List (Fin k))
    (e : ℕ → MarkovState k)
    (Θ : Fin k → Fin k → ℝ)
    (hout :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop Filter.atTop)
    (hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun n =>
            ((e n).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop (nhds (Θ i j))) :
    Filter.Tendsto
      (fun n => prefixHypergeometricFactorReal (k := k) a ys (e n))
      Filter.atTop
      (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) := by
  classical
  unfold prefixHypergeometricFactorReal prefixThetaPowerProduct
  refine tendsto_finset_prod (s := Finset.univ) ?_
  intro i hi
  have hedge :
      Filter.Tendsto
        (fun n => ∏ j : Fin k, prefixHypergeometricEdgeFactorReal (k := k) a ys (e n) i j)
        Filter.atTop
        (nhds
          (∏ j : Fin k,
            (Θ i j) ^ ((prefixWordState (k := k) a ys).counts.counts i j))) := by
    refine tendsto_finset_prod (s := Finset.univ) ?_
    intro j hj
    let c : ℕ := (prefixWordState (k := k) a ys).counts.counts i j
    by_cases hc : c = 0
    · have hc' :
          (prefixWordState (k := k) a ys).counts.counts i j = 0 := by
        simpa [c] using hc
      have hc'' : transCount (wordTraj (k := k) a ys) i j = 0 := by
        simpa [prefixWordState_counts] using hc'
      have hconst :
        (fun n => prefixHypergeometricEdgeFactorReal (k := k) a ys (e n) i j)
          = fun _ : ℕ => (1 : ℝ) := by
          funext n
          simp [prefixHypergeometricEdgeFactorReal, prefixWordState_counts, hc'']
      have hconstT :
          Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
            Filter.atTop
            (nhds ((Θ i j) ^ ((prefixWordState (k := k) a ys).counts.counts i j))) := by
        convert (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
          Filter.atTop (nhds (1 : ℝ))) using 1
        simp [hc'']
      exact hconstT.congr' (Filter.EventuallyEq.of_eq hconst.symm)
    · have hcpos : 0 < c := Nat.pos_iff_ne_zero.mpr hc
      have hrowPrefixPos :
          0 < MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i := by
        simpa [c] using
          prefixWordState_outdeg_pos_of_count_pos (k := k) a ys i j hcpos
      have hv :
          Filter.Tendsto
            (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
            Filter.atTop Filter.atTop :=
        hout i hrowPrefixPos
      change Filter.Tendsto
        (fun n =>
          ((((e n).counts.counts i j).descFactorial
              ((prefixWordState (k := k) a ys).counts.counts i j) : ℕ) : ℝ) /
            ((MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℕ) : ℝ) ^
              ((prefixWordState (k := k) a ys).counts.counts i j))
        Filter.atTop
        (nhds
          ((Θ i j) ^ ((prefixWordState (k := k) a ys).counts.counts i j)))
      simpa [c] using
        (tendsto_descFactorial_div_pow_of_ratio
          (r := c) (u := fun n => (e n).counts.counts i j)
          (v := fun n => MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i)
          (θ := Θ i j) (hratio i j) hv)
  have hrow :
      Filter.Tendsto
        (fun n => prefixHypergeometricRowCorrectionReal (k := k) a ys (e n) i)
        Filter.atTop (nhds (1 : ℝ)) := by
    let r : ℕ := MarkovDeFinettiHardEuler.outdeg (k := k)
      (prefixWordState (k := k) a ys) i
    by_cases hr : r = 0
    · have hr' :
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i = 0 := by
        simpa [r] using hr
      have hr'' : (prefixWordState (k := k) a ys).counts.rowTotal i = 0 := by
        simpa [MarkovDeFinettiHardEuler.outdeg, TransCounts.rowTotal] using hr'
      have hr''' : ∑ x, transCount (wordTraj (k := k) a ys) i x = 0 := by
        simpa [prefixWordState_counts, TransCounts.rowTotal] using hr''
      have hconst :
        (fun n => prefixHypergeometricRowCorrectionReal (k := k) a ys (e n) i)
          = fun _ : ℕ => (1 : ℝ) := by
          funext n
          simp [prefixHypergeometricRowCorrectionReal, MarkovDeFinettiHardEuler.outdeg,
            TransCounts.rowTotal, hr''']
      exact (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds (1 : ℝ))).congr' (Filter.EventuallyEq.of_eq hconst.symm)
    · have hrpos : 0 < r := Nat.pos_iff_ne_zero.mpr hr
      have hv :
          Filter.Tendsto
            (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
            Filter.atTop Filter.atTop :=
        hout i (by simpa [r] using hrpos)
      have hdesc :
          Filter.Tendsto
            (fun n =>
              (((MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i).descFactorial r : ℕ) : ℝ) /
                ((MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℕ) : ℝ) ^ r)
            Filter.atTop (nhds (1 : ℝ)) := by
          simpa using tendsto_descFactorial_div_pow_of_ratio
            (r := r)
            (u := fun n => MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i)
            (v := fun n => MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i)
            (θ := (1 : ℝ))
            (tendsto_self_div_of_tendsto_atTop (v := fun n =>
              MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i) hv)
            hv
      have hinv := hdesc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
      simpa [prefixHypergeometricRowCorrectionReal, r]
        using hinv
  have hmul :
      Filter.Tendsto
        (fun n =>
          (∏ j : Fin k, prefixHypergeometricEdgeFactorReal (k := k) a ys (e n) i j) *
            prefixHypergeometricRowCorrectionReal (k := k) a ys (e n) i)
        Filter.atTop
        (nhds
          ((∏ j : Fin k,
              (Θ i j) ^ ((prefixWordState (k := k) a ys).counts.counts i j)) * 1)) := by
    exact hedge.mul hrow
  convert hmul using 1
  simp

/-! ## Section 2g: Ratio convergence under a bridge-limit hypothesis

With the exact factorization `prefixRatioFn = H * B` and the proved hypergeometric
limit for `H`, the remaining asymptotic work can be isolated in the bridge term.
The next two lemmas package that assembly in real-valued form:

- first assuming a limit for `prefixBridgeCorrectionReal`
- then assuming the even sharper normalized bridge-product limit, using the
  earlier reduction theorem.

This keeps the global finite-graph correction theorem as a single remaining
input, rather than letting it leak into the rest of the convergence stack. -/

/-- Real-valued prefix ratio. -/
def prefixRatioFnReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) : ℝ :=
  (prefixRatioFn (k := k) a ys N hN eN : ℝ)

@[simp] lemma prefixRatioFnReal_eq_ratCast
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixRatioFnReal (k := k) a ys N hN eN =
      (prefixRatioFn (k := k) a ys N hN eN : ℝ) := rfl

lemma prefixRatioFnReal_eq_prefixHypergeometricFactorReal_mul_prefixBridgeCorrectionReal_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixRatioFnReal (k := k) a ys N hN eN =
      prefixHypergeometricFactorReal (k := k) a ys eN *
        prefixBridgeCorrectionReal (k := k) a ys N hN eN := by
  rw [prefixRatioFnReal_eq_ratCast, prefixHypergeometricFactorReal_eq_ratCast,
    prefixBridgeCorrectionReal_eq_ratCast]
  exact_mod_cast
    prefixRatioFn_eq_prefixHypergeometricFactor_mul_prefixBridgeCorrection_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp

/-- Once the bridge correction tends to `1`, the exact prefix ratio tends to the
target edge-power product. -/
lemma tendsto_prefixRatioFnReal_of_tendsto_prefixBridgeCorrectionReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ → ℕ) (hN : ∀ n, ys.length ≤ N n)
    (e : ℕ → MarkovState k)
    (Θ : Fin k → Fin k → ℝ)
    (hcomp : ∀ n, prefixCompatibleState (k := k) a ys (N n) (hN n) (e n))
    (hout :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop Filter.atTop)
    (hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun n =>
            ((e n).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop (nhds (Θ i j)))
    (hbridge :
      Filter.Tendsto
        (fun n => prefixBridgeCorrectionReal (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun n => prefixRatioFnReal (k := k) a ys (N n) (hN n) (e n))
      Filter.atTop
      (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) := by
  have hH :
      Filter.Tendsto
        (fun n => prefixHypergeometricFactorReal (k := k) a ys (e n))
        Filter.atTop
        (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) :=
    tendsto_prefixHypergeometricFactorReal
      (k := k) a ys e Θ hout hratio
  have hMul :
      Filter.Tendsto
        (fun n =>
          prefixHypergeometricFactorReal (k := k) a ys (e n) *
            prefixBridgeCorrectionReal (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop
        (nhds (prefixThetaPowerProduct (k := k) a ys Θ * 1)) := by
    exact hH.mul hbridge
  have hEq :
      (fun n => prefixRatioFnReal (k := k) a ys (N n) (hN n) (e n)) =ᶠ[Filter.atTop]
        (fun n =>
          prefixHypergeometricFactorReal (k := k) a ys (e n) *
            prefixBridgeCorrectionReal (k := k) a ys (N n) (hN n) (e n)) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    exact prefixRatioFnReal_eq_prefixHypergeometricFactorReal_mul_prefixBridgeCorrectionReal_of_prefixCompatibleState
      (k := k) a ys (N n) (hN n) (e n) (hcomp n)
  have hMul' :
      Filter.Tendsto
        (fun n =>
          prefixHypergeometricFactorReal (k := k) a ys (e n) *
            prefixBridgeCorrectionReal (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop
        (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) := by
    simpa using hMul
  exact hMul'.congr' hEq.symm

/-- It is enough to prove the sharper normalized bridge-product limit; the exact
prefix ratio convergence then follows automatically. -/
lemma tendsto_prefixRatioFnReal_of_tendsto_prefixNormalizedBridgeProductReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ → ℕ) (hN : ∀ n, ys.length ≤ N n)
    (e : ℕ → MarkovState k)
    (Θ : Fin k → Fin k → ℝ)
    (hcomp : ∀ n, prefixCompatibleState (k := k) a ys (N n) (hN n) (e n))
    (hout :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop Filter.atTop)
    (hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun n =>
            ((e n).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop (nhds (Θ i j)))
    (hbridgeNorm :
      Filter.Tendsto
        (fun n => prefixNormalizedBridgeProductReal (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun n => prefixRatioFnReal (k := k) a ys (N n) (hN n) (e n))
      Filter.atTop
      (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) := by
  have hbridge :
      Filter.Tendsto
        (fun n => prefixBridgeCorrectionReal (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop (nhds (1 : ℝ)) :=
    tendsto_prefixBridgeCorrectionReal_of_tendsto_prefixNormalizedBridgeProductReal
      (k := k) a ys N hN e hcomp hbridgeNorm
  exact tendsto_prefixRatioFnReal_of_tendsto_prefixBridgeCorrectionReal
    (k := k) a ys N hN e Θ hcomp hout hratio hbridge

lemma prefixNormalizedBridgeProduct_eq_prefixNormalizedEulerTrailCorrectionRatio_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixEulerTrailRatio (k := k) a ys N hN eN *
      prefixRowDescFactorialProduct (k := k) a ys eN =
        prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN := by
  have hcomp' := hcomp
  rcases hcomp with ⟨heN, _, hres⟩
  have hrow :
      ((outdegFactorialWeight (k := k) eN : ℚ) /
          (outdegFactorialWeight (k := k)
            (residualStateOfPrefix (k := k) a ys eN) : ℚ)) =
        prefixRowDescFactorialProduct (k := k) a ys eN := by
    have hmul :=
      outdegFactorialWeight_eq_prefixRowDescFactorialProduct_mul_residual_of_prefixCompatibleState
        (k := k) a ys N hN eN hcomp'
    have hresFact :
        ((outdegFactorialWeight (k := k)
            (residualStateOfPrefix (k := k) a ys eN) : ℚ)) ≠ 0 := by
      exact_mod_cast outdegFactorialWeight_ne_zero
        (k := k) (residualStateOfPrefix (k := k) a ys eN)
    exact (div_eq_iff hresFact).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hfullCard :
      (((eulerTrailFinset (graphOfState eN) eN.start eN.last).card : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt <| by
      rw [eulerTrailFinset_card_eq (k := k) eN heN]
      exact Nat.mul_pos
        (Nat.pos_iff_ne_zero.mpr <|
          fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := eN) heN)
        (graphFactorialWeight_pos (k := k) eN)
  have hfullFact :
      ((outdegFactorialWeight (k := k) eN : ℚ)) ≠ 0 := by
    exact_mod_cast outdegFactorialWeight_ne_zero (k := k) eN
  have hresFact :
      ((outdegFactorialWeight (k := k)
          (residualStateOfPrefix (k := k) a ys eN) : ℚ)) ≠ 0 := by
    exact_mod_cast outdegFactorialWeight_ne_zero
      (k := k) (residualStateOfPrefix (k := k) a ys eN)
  have hmain :
      prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN =
        prefixEulerTrailRatio (k := k) a ys N hN eN *
          (((outdegFactorialWeight (k := k) eN : ℚ) /
            (outdegFactorialWeight (k := k)
              (residualStateOfPrefix (k := k) a ys eN) : ℚ))) := by
    unfold prefixNormalizedEulerTrailCorrectionRatio normalizedEulerTrailCorrection prefixEulerTrailRatio
    field_simp [hfullCard, hfullFact, hresFact]
  calc
    prefixEulerTrailRatio (k := k) a ys N hN eN *
        prefixRowDescFactorialProduct (k := k) a ys eN
      =
        prefixEulerTrailRatio (k := k) a ys N hN eN *
          (((outdegFactorialWeight (k := k) eN : ℚ) /
            (outdegFactorialWeight (k := k)
              (residualStateOfPrefix (k := k) a ys eN) : ℚ))) := by
          simp [hrow]
    _ = prefixNormalizedEulerTrailCorrectionRatio (k := k) a ys N hN eN := by
          exact hmain.symm

lemma prefixNormalizedBridgeProductReal_eq_prefixNormalizedEulerTrailCorrectionRatioReal_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN) :
    prefixNormalizedBridgeProductReal (k := k) a ys N hN eN =
      prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys N hN eN := by
  unfold prefixNormalizedBridgeProductReal
  rw [prefixEulerTrailRatioReal_eq_ratCast, prefixRowDescFactorialProductReal_eq_ratCast,
    prefixNormalizedEulerTrailCorrectionRatioReal_eq_ratCast]
  exact_mod_cast
    prefixNormalizedBridgeProduct_eq_prefixNormalizedEulerTrailCorrectionRatio_of_prefixCompatibleState
      (k := k) a ys N hN eN hcomp

/-- Reduction theorem for the finite graph correction target: if the
residual/full normalized Euler-trail correction ratio tends to `1`, then so does
the normalized bridge product. -/
lemma tendsto_prefixNormalizedBridgeProductReal_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ → ℕ) (hN : ∀ n, ys.length ≤ N n)
    (e : ℕ → MarkovState k)
    (hcomp : ∀ n, prefixCompatibleState (k := k) a ys (N n) (hN n) (e n))
    (hgraph :
      Filter.Tendsto
        (fun n =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun n => prefixNormalizedBridgeProductReal (k := k) a ys (N n) (hN n) (e n))
      Filter.atTop (nhds (1 : ℝ)) := by
  have hEq :
      (fun n => prefixNormalizedBridgeProductReal (k := k) a ys (N n) (hN n) (e n)) =ᶠ[Filter.atTop]
        (fun n =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (N n) (hN n) (e n)) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    exact prefixNormalizedBridgeProductReal_eq_prefixNormalizedEulerTrailCorrectionRatioReal_of_prefixCompatibleState
      (k := k) a ys (N n) (hN n) (e n) (hcomp n)
  exact hgraph.congr' hEq.symm

/-- High-level reduction: proving stability of the finite graph correction
ratio is enough to obtain convergence of the exact prefix ratio. -/
lemma tendsto_prefixRatioFnReal_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ → ℕ) (hN : ∀ n, ys.length ≤ N n)
    (e : ℕ → MarkovState k)
    (Θ : Fin k → Fin k → ℝ)
    (hcomp : ∀ n, prefixCompatibleState (k := k) a ys (N n) (hN n) (e n))
    (hout :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop Filter.atTop)
    (hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun n =>
            ((e n).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop (nhds (Θ i j)))
    (hgraph :
      Filter.Tendsto
        (fun n =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun n => prefixRatioFnReal (k := k) a ys (N n) (hN n) (e n))
      Filter.atTop
      (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) := by
  have hbridge :
      Filter.Tendsto
        (fun n => prefixNormalizedBridgeProductReal (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop (nhds (1 : ℝ)) :=
    tendsto_prefixNormalizedBridgeProductReal_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
      (k := k) a ys N hN e hcomp hgraph
  exact tendsto_prefixRatioFnReal_of_tendsto_prefixNormalizedBridgeProductReal
    (k := k) a ys N hN e Θ hcomp hout hratio hbridge

lemma tendsto_prefixRatioFnReal_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_eventually_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ → ℕ) (hN : ∀ n, ys.length ≤ N n)
    (e : ℕ → MarkovState k)
    (Θ : Fin k → Fin k → ℝ)
    (hcomp :
      ∀ᶠ n in Filter.atTop,
        prefixCompatibleState (k := k) a ys (N n) (hN n) (e n))
    (hout :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop Filter.atTop)
    (hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun n =>
            ((e n).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop (nhds (Θ i j)))
    (hgraph :
      Filter.Tendsto
        (fun n =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (N n) (hN n) (e n))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun n => prefixRatioFnReal (k := k) a ys (N n) (hN n) (e n))
      Filter.atTop
      (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) := by
  rw [Filter.eventually_atTop] at hcomp
  rcases hcomp with ⟨n0, hn0⟩
  have htail :
      Filter.Tendsto
        (fun n => prefixRatioFnReal (k := k) a ys (N (n + n0)) (hN (n + n0)) (e (n + n0)))
        Filter.atTop
        (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) := by
    have hcomp' :
        ∀ n,
          prefixCompatibleState (k := k) a ys (N (n + n0)) (hN (n + n0)) (e (n + n0)) := by
      intro n
      exact hn0 (n + n0) (by omega)
    have hout' :
        ∀ i : Fin k,
          0 < MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i →
          Filter.Tendsto
            (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e (n + n0)) i : ℝ))
            Filter.atTop Filter.atTop := by
      intro i hi
      exact (hout i hi).comp (Filter.tendsto_add_atTop_nat n0)
    have hratio' :
        ∀ i j : Fin k,
          Filter.Tendsto
            (fun n =>
              ((e (n + n0)).counts.counts i j : ℝ) /
                (MarkovDeFinettiHardEuler.outdeg (k := k) (e (n + n0)) i : ℝ))
            Filter.atTop (nhds (Θ i j)) := by
      intro i j
      exact (hratio i j).comp (Filter.tendsto_add_atTop_nat n0)
    have hgraph' :
        Filter.Tendsto
          (fun n =>
            prefixNormalizedEulerTrailCorrectionRatioReal
              (k := k) a ys (N (n + n0)) (hN (n + n0)) (e (n + n0)))
          Filter.atTop (nhds (1 : ℝ)) := by
      exact hgraph.comp (Filter.tendsto_add_atTop_nat n0)
    exact tendsto_prefixRatioFnReal_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
      (k := k) a ys
      (fun n => N (n + n0))
      (fun n => hN (n + n0))
      (fun n => e (n + n0))
      Θ hcomp' hout' hratio' hgraph'
  exact (Filter.tendsto_add_atTop_iff_nat n0).mp htail

/-! ## Section 2h: Token deletion stability substrate

This section isolates the remaining finite graph correction into a concrete
non-root deletion problem on token-rooted arborescences.

- `pathPrefixState` packages concrete path prefixes so that strong recurrence
  can be turned into row-outdegree growth along evidence states.
- `deleteCopies` lifts the one-token deletion bound to finite sequences of
  non-root deletions.
- `prefixNonrootDeletionList` records exactly the non-root prefix deletions,
  leaving root-source deletions outside the token-arborescence theorem.
-/

/-- The length-`N` trajectory obtained from the first `N + 1` coordinates of an
infinite path. -/
def pathPrefixTraj (ω : ℕ → Fin k) (N : ℕ) : Traj k N :=
  fun i => ω i.1

/-- Evidence state of the first `N + 1` coordinates of an infinite path. -/
def pathPrefixState (ω : ℕ → Fin k) (N : ℕ) : MarkovState k :=
  stateOfTraj (k := k) (pathPrefixTraj (k := k) ω N)

@[simp] lemma pathPrefixState_start
    (ω : ℕ → Fin k) (N : ℕ) :
    (pathPrefixState (k := k) ω N).start = ω 0 := by
  rfl

@[simp] lemma pathPrefixState_last
    (ω : ℕ → Fin k) (N : ℕ) :
    (pathPrefixState (k := k) ω N).last = ω N := by
  rfl

lemma pathPrefixState_outdeg_eq_visitCountBefore
    (ω : ℕ → Fin k) (N : ℕ) (i : Fin k) :
    MarkovDeFinettiHardEuler.outdeg (k := k)
        (pathPrefixState (k := k) ω N) i =
      visitCountBefore (k := k) ω i N := by
  unfold pathPrefixState
  classical
  let A : Finset (Fin N) := Finset.univ.filter fun j : Fin N => ω j.1 = i
  let e : Fin N ↪ ℕ := ⟨fun j => j.1, Fin.val_injective⟩
  have hmap :
      A.map e = (Finset.range N).filter fun m : ℕ => ω m = i := by
    ext m
    constructor
    · intro hm
      rcases Finset.mem_map.mp hm with ⟨j, hj, rfl⟩
      exact Finset.mem_filter.mpr ⟨by
        exact Finset.mem_range.mpr j.2, by
        simpa [A, e] using (Finset.mem_filter.mp hj).2⟩
    · intro hm
      rcases Finset.mem_filter.mp hm with ⟨hmN, hωm⟩
      have hmN' : m < N := Finset.mem_range.mp hmN
      refine Finset.mem_map.mpr ?_
      refine ⟨⟨m, hmN'⟩, ?_, rfl⟩
      simpa [A] using Finset.mem_filter.mpr ⟨Finset.mem_univ _, hωm⟩
  rw [MarkovDeFinettiHardEuler.outdeg_eq_card_prev
    (k := k) (xs := pathPrefixTraj (k := k) ω N) (a := i)]
  rw [visitCountBefore_eq_natCount (k := k) ω i N, Nat.count_eq_card_filter_range]
  change A.card = ((Finset.range N).filter fun m : ℕ => ω m = i).card
  calc
    A.card = (A.map e).card := by
      symm
      exact Finset.card_map e
    _ = ((Finset.range N).filter fun m : ℕ => ω m = i).card := by
      rw [hmap]

/-- Number of visit indices `< m` for row `i` whose successor value is `j`. -/
def rowSuccessorEmpiricalCount
    (i j : Fin k) (ω : ℕ → Fin k) (m : ℕ) : ℕ :=
  Nat.count (fun n => rowSuccessorVisitProcess (k := k) i ω n = j) m

/-- Empirical successor frequency among the first `m` visits to row `i`. -/
def rowSuccessorEmpiricalFreq
    (i j : Fin k) (ω : ℕ → Fin k) (m : ℕ) : ℝ :=
  (rowSuccessorEmpiricalCount (k := k) i j ω m : ℝ) / m

/-- Empirical coordinate frequency for the first `m` coordinates of a row process. -/
def rowProcessEmpiricalFreq
    (j : Fin k) (r : ℕ → Fin k) (m : ℕ) : ℝ :=
  (Nat.count (fun n => r n = j) m : ℝ) / m

/-- Strong law on an i.i.d. row fiber for the singleton indicator of `j`. -/
lemma strong_law_indicator_iidProduct
    (ν : ProbabilityMeasure (Fin k)) (j : Fin k) :
    ∀ᵐ r ∂Exchangeability.Probability.iidProduct (ν : Measure (Fin k)),
      Filter.Tendsto
        (fun m => rowProcessEmpiricalFreq (k := k) j r m)
        Filter.atTop
        (nhds ((ν ({j} : Set (Fin k))).toReal)) := by
  let X : ℕ → (ℕ → Fin k) → ℝ := fun n r => if r n = j then 1 else 0
  have hX_int :
      Integrable (X 0) (Exchangeability.Probability.iidProduct (ν : Measure (Fin k))) := by
    have hEq :
        X 0 = Set.indicator {r : ℕ → Fin k | r 0 = j} (fun _ => (1 : ℝ)) := by
      funext r
      by_cases h : r 0 = j <;> simp [X, h]
    rw [hEq]
    refine Integrable.indicator (integrable_const 1) ?_
    change MeasurableSet ((fun r : ℕ → Fin k => r 0) ⁻¹' ({j} : Set (Fin k)))
    exact (measurable_pi_apply 0) (MeasurableSet.singleton j)
  have hF_meas : Measurable (fun x : Fin k => if x = j then (1 : ℝ) else 0) :=
    measurable_of_countable _
  have h_indep_eval :
      ProbabilityTheory.iIndepFun
        (fun n (r : ℕ → Fin k) => r n)
        (Exchangeability.Probability.iidProduct (ν : Measure (Fin k))) := by
    simpa [Exchangeability.Probability.iidProduct] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : ℕ => (ν : Measure (Fin k)))
        (X := fun _ x => x)
        (fun _ => measurable_id))
  have hInt :
      (∫ r, X 0 r ∂Exchangeability.Probability.iidProduct (ν : Measure (Fin k))) =
        ((ν ({j} : Set (Fin k))).toReal) := by
    have hEq :
        X 0 = Set.indicator {r : ℕ → Fin k | r 0 = j} (fun _ => (1 : ℝ)) := by
      funext r
      by_cases h : r 0 = j <;> simp [X, h]
    rw [hEq]
    calc
      (∫ r : ℕ → Fin k, {r : ℕ → Fin k | r 0 = j}.indicator (fun _ => (1 : ℝ)) r
          ∂Exchangeability.Probability.iidProduct (ν : Measure (Fin k)))
          =
        (Exchangeability.Probability.iidProduct (ν : Measure (Fin k))).real
          {r : ℕ → Fin k | r 0 = j} := by
            exact
              (MeasureTheory.integral_indicator_one
                (μ := Exchangeability.Probability.iidProduct (ν : Measure (Fin k)))
                (s := {r : ℕ → Fin k | r 0 = j})
                (by
                  change MeasurableSet ((fun r : ℕ → Fin k => r 0) ⁻¹' ({j} : Set (Fin k)))
                  exact (measurable_pi_apply 0) (MeasurableSet.singleton j)))
      _ = ((ν ({j} : Set (Fin k))).toReal) := by
        have h_map :=
          congrArg
            (fun M : Measure (Fin k) => M ({j} : Set (Fin k)))
            (MeasureTheory.Measure.infinitePi_map_eval
              (μ := fun _ : ℕ => (ν : Measure (Fin k))) 0)
        have h_eval' :
            (Measure.infinitePi (fun _ : ℕ => (ν : Measure (Fin k))))
                {r : ℕ → Fin k | r 0 = j}
              =
            (ν : Measure (Fin k)) ({j} : Set (Fin k)) := by
          simpa [Measure.map_apply, measurable_pi_apply, MeasurableSet.singleton,
            Set.preimage, Set.mem_singleton_iff] using h_map
        rw [Measure.real, Exchangeability.Probability.iidProduct, h_eval']
        rfl
  have hX_indep :
      Pairwise
        (Function.onFun
          (fun x1 x2 =>
            ProbabilityTheory.IndepFun x1 x2
              (Exchangeability.Probability.iidProduct (ν : Measure (Fin k))))
          X) := by
    intro a b hab
    have hab' := h_indep_eval.indepFun hab
    exact
      (ProbabilityTheory.IndepFun.comp hab' hF_meas hF_meas)
  have hX_ident :
      ∀ n : ℕ,
        ProbabilityTheory.IdentDistrib
          (X n)
          (X 0)
          (Exchangeability.Probability.iidProduct (ν : Measure (Fin k)))
          (Exchangeability.Probability.iidProduct (ν : Measure (Fin k))) := by
    intro n
    have h_eval_ident_n :
        ProbabilityTheory.IdentDistrib
          (fun r : ℕ → Fin k => r n)
          (fun r : ℕ → Fin k => r 0)
          (Exchangeability.Probability.iidProduct (ν : Measure (Fin k)))
          (Exchangeability.Probability.iidProduct (ν : Measure (Fin k))) := by
      refine ⟨(measurable_pi_apply n).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
      calc
        Measure.map
            (fun r : ℕ → Fin k => r n)
            (Exchangeability.Probability.iidProduct (ν : Measure (Fin k)))
            =
          (ν : Measure (Fin k)) := by
                simpa [Exchangeability.Probability.iidProduct] using
                  (MeasureTheory.Measure.infinitePi_map_eval
                    (μ := fun _ : ℕ => (ν : Measure (Fin k))) n)
        _ =
          Measure.map
            (fun r : ℕ → Fin k => r 0)
            (Exchangeability.Probability.iidProduct (ν : Measure (Fin k))) := by
                symm
                simpa [Exchangeability.Probability.iidProduct] using
                  (MeasureTheory.Measure.infinitePi_map_eval
                    (μ := fun _ : ℕ => (ν : Measure (Fin k))) 0)
    exact h_eval_ident_n.comp hF_meas
  have hsl :=
    ProbabilityTheory.strong_law_ae_real X hX_int hX_indep hX_ident
  rw [hInt] at hsl
  simpa [X, rowProcessEmpiricalFreq, Nat.count_eq_card_filter_range] using hsl

/-- Strong law on `iidProduct`: empirical frequency of value `j` converges a.e.
to `ν({j})`. This is the row-fiber SLLN in the exact empirical-frequency form. -/
lemma ae_tendsto_empiricalFreq_iidProduct
    (ν : ProbabilityMeasure (Fin k)) (j : Fin k) :
    ∀ᵐ r ∂Exchangeability.Probability.iidProduct (ν : Measure (Fin k)),
      Filter.Tendsto
        (fun n => rowProcessEmpiricalFreq (k := k) j r n)
        Filter.atTop
        (nhds ((ν ({j} : Set (Fin k))).toReal)) := by
  simpa using strong_law_indicator_iidProduct (k := k) ν j

/-- Fiberwise a.e. strong law for a random `iidProduct` kernel over row paths. -/
lemma ae_ae_tendsto_rowProcessEmpiricalFreq_iidProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i j : Fin k)
    (ν : (ℕ → Fin k) → ProbabilityMeasure (Fin k)) :
    ∀ᵐ r0 ∂rowProcessLaw (k := k) P i,
      ∀ᵐ r ∂Exchangeability.Probability.iidProduct (ν r0 : Measure (Fin k)),
        Filter.Tendsto
          (fun m => rowProcessEmpiricalFreq (k := k) j r m)
          Filter.atTop
          (nhds (((ν r0) ({j} : Set (Fin k))).toReal)) := by
  refine Filter.Eventually.of_forall ?_
  intro r0
  exact ae_tendsto_empiricalFreq_iidProduct (k := k) (ν r0) j

/-- Promote fiberwise almost-everywhere properties through `Measure.bind`.
This is the forward direction complementary to `ae_ae_of_ae_bind`. -/
lemma ae_of_ae_bind
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (m : Measure α) (f : α → Measure β)
    (hf : AEMeasurable f m)
    {p : β → Prop}
    (hp : MeasurableSet {b : β | p b})
    (h : ∀ᵐ a ∂m, ∀ᵐ b ∂f a, p b) :
    ∀ᵐ b ∂m.bind f, p b := by
  have hzero :
      ∀ᵐ a ∂m, f a ({b : β | ¬ p b}) = 0 := by
    filter_upwards [h] with a ha
    exact (ae_iff.1 ha)
  have hlin : ∫⁻ a, f a ({b : β | ¬ p b}) ∂m = 0 := by
    exact lintegral_eq_zero_of_ae_eq_zero hzero
  refine (ae_iff.2 ?_)
  calc
    m.bind f ({b : β | ¬ p b})
        = ∫⁻ a, f a ({b : β | ¬ p b}) ∂m := by
            exact Measure.bind_apply (m := m) (f := f)
              (s := {b : β | ¬ p b}) hp.compl hf
    _ = 0 := hlin

/-- Measurability of an infinite `iidProduct` kernel follows from the prefix-cylinder
π-system: on each prefix cylinder, the infinite product reduces to a finite product
kernel, whose measurability is already available. -/
lemma measurable_iidProduct_of_measurable_eval
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Ω → ProbabilityMeasure (Fin k))
    (hν_meas :
      ∀ B : Set (Fin k), MeasurableSet B →
        Measurable (fun ω => (ν ω : Measure (Fin k)) B)) :
    Measurable
      (fun ω => Exchangeability.Probability.iidProduct (ν ω : Measure (Fin k))) := by
  classical
  refine
    Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (μ := fun ω => Exchangeability.Probability.iidProduct (ν ω : Measure (Fin k)))
      (S := Exchangeability.prefixCylinders (α := Fin k))
      (Exchangeability.generateFrom_prefixCylinders (α := Fin k)).symm
      (Exchangeability.isPiSystem_prefixCylinders (α := Fin k))
      ?_
  intro A hA
  rcases hA with ⟨n, S, hS, rfl⟩
  have hpi_meas :
      Measurable (fun ω => Measure.pi (fun _ : Fin n => (ν ω : Measure (Fin k)))) :=
    measurable_measure_pi
      (ν := fun ω => (ν ω : Measure (Fin k)))
      (fun ω => by
        change IsProbabilityMeasure ((ν ω : ProbabilityMeasure (Fin k)) : Measure (Fin k))
        infer_instance)
      hν_meas
  have hEq :
      (fun ω =>
        Exchangeability.Probability.iidProduct (ν ω : Measure (Fin k))
          (Exchangeability.prefixCylinder (α := Fin k) S))
        =
      (fun ω => (Measure.pi (fun _ : Fin n => (ν ω : Measure (Fin k)))) S) := by
    funext ω
    calc
      Exchangeability.Probability.iidProduct (ν ω : Measure (Fin k))
          (Exchangeability.prefixCylinder (α := Fin k) S)
          =
        ((Exchangeability.Probability.iidProduct (ν ω : Measure (Fin k))).map
          (Exchangeability.prefixProj (α := Fin k) n)) S := by
            exact
              (Measure.map_apply
                (Exchangeability.measurable_prefixProj (α := Fin k) (n := n)) hS).symm
      _ = (Measure.pi (fun _ : Fin n => (ν ω : Measure (Fin k)))) S := by
        exact
          congrArg
            (fun M : Measure (Fin n → Fin k) => M S)
            (Exchangeability.Probability.iidProduct.cylinder_fintype
              (ν := (ν ω : Measure (Fin k))) (n := n))
  rw [hEq]
  exact (Measure.measurable_coe hS).comp hpi_meas

/-- Pull the row-fiber SLLN through a bind representation to obtain a.e.
existence of Cesàro limits under the bound row-process law. -/
lemma ae_exists_tendsto_rowProcessEmpiricalFreq_of_bind_iidProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i j : Fin k)
    (ν : (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hν :
      AEMeasurable
        (fun r : ℕ → Fin k =>
          Exchangeability.Probability.iidProduct (ν r : Measure (Fin k)))
        (rowProcessLaw (k := k) P i))
    (hbind :
      rowProcessLaw (k := k) P i =
        (rowProcessLaw (k := k) P i).bind
          (fun r : ℕ → Fin k =>
            Exchangeability.Probability.iidProduct (ν r : Measure (Fin k))))
    (hlimitMeas :
      MeasurableSet
        {r : ℕ → Fin k |
          ∃ q : ℝ,
            Filter.Tendsto
              (fun m => rowProcessEmpiricalFreq (k := k) j r m)
              Filter.atTop
              (nhds q)}) :
    ∀ᵐ r ∂rowProcessLaw (k := k) P i,
      ∃ q : ℝ,
        Filter.Tendsto
          (fun m => rowProcessEmpiricalFreq (k := k) j r m)
          Filter.atTop
          (nhds q) := by
  have hfiber :
      ∀ᵐ r0 ∂rowProcessLaw (k := k) P i,
        ∀ᵐ r ∂Exchangeability.Probability.iidProduct (ν r0 : Measure (Fin k)),
          ∃ q : ℝ,
            Filter.Tendsto
              (fun m => rowProcessEmpiricalFreq (k := k) j r m)
              Filter.atTop
              (nhds q) := by
    filter_upwards
      [ae_ae_tendsto_rowProcessEmpiricalFreq_iidProduct (k := k) P i j ν] with r0 hr0
    filter_upwards [hr0] with r hr
    exact ⟨((ν r0) ({j} : Set (Fin k))).toReal, hr⟩
  have hbind_ae :
      ∀ᵐ r ∂(rowProcessLaw (k := k) P i).bind
          (fun r0 : ℕ → Fin k =>
            Exchangeability.Probability.iidProduct (ν r0 : Measure (Fin k))),
        ∃ q : ℝ,
          Filter.Tendsto
            (fun m => rowProcessEmpiricalFreq (k := k) j r m)
            Filter.atTop
            (nhds q) := by
    exact ae_of_ae_bind
      (m := rowProcessLaw (k := k) P i)
      (f := fun r0 : ℕ → Fin k =>
        Exchangeability.Probability.iidProduct (ν r0 : Measure (Fin k)))
      hν hlimitMeas hfiber
  rw [hbind]
  exact hbind_ae

/-- Canonical row-kernel candidate from row-process directing measures. -/
def directingRowKernel
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P] :
    Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k) :=
  fun i r =>
    by
      letI : Nonempty (Fin k) := ⟨i⟩
      letI : IsProbabilityMeasure (rowProcessLaw (k := k) P i) :=
        Measure.isProbabilityMeasure_map
          ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
      exact
        ⟨directingMeasure
            (μ := rowProcessLaw (k := k) P i)
            (fun n (ω : ℕ → Fin k) => ω n)
            (fun n => measurable_pi_apply n) r,
          directingMeasure_isProb
            (μ := rowProcessLaw (k := k) P i)
            (X := fun n (ω : ℕ → Fin k) => ω n)
            (hX := fun n => measurable_pi_apply n) r⟩

/-- Canonical de Finetti bind law on the full row-process path space: the row-process
law is the mixture of i.i.d. fibers directed by its own directing measure. -/
theorem rowProcessLaw_eq_bind_directingRowKernel_iidProduct
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i : Fin k)
    (hExch :
      Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
        (fun n (r : ℕ → Fin k) => r n)) :
    rowProcessLaw (k := k) P i
      =
    (rowProcessLaw (k := k) P i).bind
      (fun r : ℕ → Fin k =>
        Exchangeability.Probability.iidProduct
          (directingRowKernel (k := k) P i r : Measure (Fin k))) := by
  classical
  let ρ : Measure (ℕ → Fin k) := rowProcessLaw (k := k) P i
  letI : Nonempty (Fin k) := ⟨i⟩
  letI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map
      ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
  let X : ℕ → (ℕ → Fin k) → Fin k := fun n r => r n
  have hX_meas : ∀ n : ℕ, Measurable (X n) := fun n => measurable_pi_apply n
  have hContr : Exchangeability.Contractable ρ X :=
    Exchangeability.contractable_of_exchangeable hExch hX_meas
  have hdir_eval_meas :
      ∀ B : Set (Fin k), MeasurableSet B →
        Measurable
          (fun r : ℕ → Fin k =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)) B) := by
    intro B hB
    simpa [ρ, X, directingRowKernel] using
      (directingMeasure_measurable_eval
        (μ := ρ) (X := X) (hX := hX_meas) B hB)
  have hiid_meas :
      Measurable
        (fun r : ℕ → Fin k =>
          Exchangeability.Probability.iidProduct
            (directingRowKernel (k := k) P i r : Measure (Fin k))) :=
    measurable_iidProduct_of_measurable_eval
      (k := k) (ν := directingRowKernel (k := k) P i) hdir_eval_meas
  have hiid_prob :
      ∀ r : ℕ → Fin k,
        IsProbabilityMeasure
          (Exchangeability.Probability.iidProduct
            (directingRowKernel (k := k) P i r : Measure (Fin k))) := by
    intro r
    infer_instance
  let κ : (ℕ → Fin k) → Measure (ℕ → Fin k) :=
    fun r =>
      Exchangeability.Probability.iidProduct
        (directingRowKernel (k := k) P i r : Measure (Fin k))
  haveI : IsProbabilityMeasure (ρ.bind κ) :=
    isProbabilityMeasure_bind (m := ρ) (f := κ) hiid_meas.aemeasurable
      (Filter.Eventually.of_forall hiid_prob)
  apply Exchangeability.measure_eq_of_fin_marginals_eq_prob (α := Fin k)
  intro n S hS
  have hfin_dir :
      Measure.map (Exchangeability.prefixProj (α := Fin k) n) ρ
        =
      ρ.bind
        (fun r : ℕ → Fin k =>
          Measure.pi
            (fun _ : Fin n => (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
    simp only [directingRowKernel]
    exact
      (finite_product_formula_with_directing
        (μ := ρ) (X := X) hContr hX_meas n (fun j : Fin n => j.1)
        (fun _ _ h => h))
  have hbind_map :
      Measure.map (Exchangeability.prefixProj (α := Fin k) n) (ρ.bind κ)
        =
      ρ.bind
        (fun r : ℕ → Fin k =>
          Measure.map (Exchangeability.prefixProj (α := Fin k) n) (κ r)) := by
    exact
      MeasureTheory.Measure.bind_map_comm
        hiid_meas
        (Exchangeability.measurable_prefixProj (α := Fin k) (n := n))
  have hmap_iid :
      (fun r : ℕ → Fin k =>
        Measure.map (Exchangeability.prefixProj (α := Fin k) n) (κ r))
        =
      (fun r : ℕ → Fin k =>
        Measure.pi
          (fun _ : Fin n => (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
    funext r
    exact
      (Exchangeability.Probability.iidProduct.cylinder_fintype
        (ν := (directingRowKernel (k := k) P i r : Measure (Fin k))) (n := n))
  calc
    Measure.map (Exchangeability.prefixProj (α := Fin k) n) ρ S
        =
      (ρ.bind
        (fun r : ℕ → Fin k =>
          Measure.pi
            (fun _ : Fin n => (directingRowKernel (k := k) P i r : Measure (Fin k))))) S := by
              exact congrArg (fun M : Measure (Fin n → Fin k) => M S) hfin_dir
    _ = Measure.map (Exchangeability.prefixProj (α := Fin k) n) (ρ.bind κ) S := by
      rw [hbind_map, hmap_iid]
    _ = Measure.map (Exchangeability.prefixProj (α := Fin k) n)
          ((rowProcessLaw (k := k) P i).bind
            (fun r : ℕ → Fin k =>
              Exchangeability.Probability.iidProduct
                (directingRowKernel (k := k) P i r : Measure (Fin k)))) S := by
                  rfl

/-- The canonical directing-row `iidProduct` kernel is measurable. -/
lemma measurable_iidProduct_directingRowKernel
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i : Fin k) :
    Measurable
      (fun r : ℕ → Fin k =>
        Exchangeability.Probability.iidProduct
          (directingRowKernel (k := k) P i r : Measure (Fin k))) := by
  let ρ : Measure (ℕ → Fin k) := rowProcessLaw (k := k) P i
  letI : Nonempty (Fin k) := ⟨i⟩
  letI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map
      ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
  have hdir_eval_meas :
      ∀ B : Set (Fin k), MeasurableSet B →
        Measurable
          (fun r : ℕ → Fin k =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)) B) := by
    intro B hB
    simpa [ρ, directingRowKernel] using
      (directingMeasure_measurable_eval
        (μ := ρ)
        (X := fun n (r : ℕ → Fin k) => r n)
        (hX := fun n => measurable_pi_apply n)
        B hB)
  exact
    measurable_iidProduct_of_measurable_eval
      (k := k) (ν := directingRowKernel (k := k) P i) hdir_eval_meas

/-- Exchangeability plus the canonical directing-row bind law yields a.e. existence
of Cesàro limits for empirical row frequencies, under the explicit measurability
of the convergence event. The remaining gap is to identify this limit pointwise with
the canonical directing-row singleton evaluation. -/
theorem ae_exists_tendsto_rowProcessEmpiricalFreq_of_exchangeable
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i j : Fin k)
    (hExch :
      Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
        (fun n (r : ℕ → Fin k) => r n))
    (hlimitMeas :
      MeasurableSet
        {r : ℕ → Fin k |
          ∃ q : ℝ,
            Filter.Tendsto
              (fun m => rowProcessEmpiricalFreq (k := k) j r m)
              Filter.atTop
              (nhds q)}) :
    ∀ᵐ r ∂rowProcessLaw (k := k) P i,
      ∃ q : ℝ,
        Filter.Tendsto
          (fun m => rowProcessEmpiricalFreq (k := k) j r m)
          Filter.atTop
          (nhds q) := by
  exact
    ae_exists_tendsto_rowProcessEmpiricalFreq_of_bind_iidProduct
      (k := k) (P := P) (i := i) (j := j)
      (ν := directingRowKernel (k := k) P i)
      (measurable_iidProduct_directingRowKernel (k := k) P i).aemeasurable
      (rowProcessLaw_eq_bind_directingRowKernel_iidProduct
        (k := k) P i hExch)
      hlimitMeas

/-- **Crown identification theorem**: The a.e. existing Cesàro limit of row-process
empirical frequencies equals the directingRowKernel singleton evaluation.

This theorem provides the pathwise identification needed for `RowProcessCoordwiseCesaroLimit`
and ultimately for `hLocal` in the crown theorem assembly.

**Proof route**: Uses the L¹ Cesàro-to-condExp machinery from KernelUniqueness,
which embeds `Fin k` into ℝ and applies `cesaro_to_condexp_L1`. The directing
measure equals the condExp by `directingMeasure_X0_marginal`, and L¹/a.e. limit
identification follows from `ae_limit_eq_L1_limit_of_ae_tendsto_and_L1_tendsto`.

**Status**: Infrastructure exists; remaining work is detailed type-matching plumbing
between the abstract L¹ machinery and our concrete row-process definitions. -/
theorem ae_tendsto_rowProcessEmpiricalFreq_to_directingRowKernel
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i j : Fin k)
    (hExch :
      Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
        (fun n (r : ℕ → Fin k) => r n)) :
    ∀ᵐ r ∂rowProcessLaw (k := k) P i,
      Filter.Tendsto
        (fun m => rowProcessEmpiricalFreq (k := k) j r m)
        Filter.atTop
        (nhds (((directingRowKernel (k := k) P i r) ({j} : Set (Fin k))).toReal)) := by
  classical
  let ρ : Measure (ℕ → Fin k) := rowProcessLaw (k := k) P i
  letI : Nonempty (Fin k) := ⟨i⟩
  letI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map
      ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
  let X : ℕ → (ℕ → Fin k) → Fin k := fun n r => r n
  have hX_meas : ∀ n : ℕ, Measurable (X n) := fun n => measurable_pi_apply n
  have hContr : Exchangeability.Contractable ρ X :=
    Exchangeability.contractable_of_exchangeable hExch hX_meas
  let emb : Fin k → ℝ := fun a => (a : ℝ)
  have hemb_inj : Function.Injective emb := by
    intro a b hab
    have hreal : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by
      simpa [emb] using hab
    have hval : (a : ℕ) = (b : ℕ) := by
      exact_mod_cast hreal
    exact Fin.ext hval
  have hemb_meas : Measurable emb := measurable_of_finite _
  let Y : ℕ → (ℕ → Fin k) → ℝ := fun n r => emb (X n r)
  have hY_meas : ∀ n : ℕ, Measurable (Y n) := fun n => hemb_meas.comp (hX_meas n)
  have hY_contr : Exchangeability.Contractable ρ Y :=
    Mettapedia.Logic.DirectingMeasureL1Transfer.contractable_comp_measurable
      hContr hX_meas emb hemb_meas
  let fb : ℝ → ℝ := fun x => if x = emb j then 1 else 0
  have hfb_meas : Measurable fb :=
    Measurable.ite (measurableSet_singleton (emb j)) measurable_const measurable_const
  have hfb_bdd : ∀ x, |fb x| ≤ 1 := fun x => by
    simp [fb]
    split_ifs <;> norm_num
  have htail : Exchangeability.Tail.tailProcess Y = tailSigma X := by
    rw [Mettapedia.Logic.DirectingMeasureL1Transfer.tailProcess_comp_injective
          X emb hemb_inj hemb_meas,
        ← tailSigma_eq_canonical X]
  have hfbY_eq : ∀ n r, fb (Y n r) = if r n = j then 1 else 0 := by
    intro n r
    by_cases h : r n = j
    · simp [fb, Y, X, emb, h]
    · have h' : emb (r n) ≠ emb j := by
        intro hEq
        exact h (hemb_inj hEq)
      simp [fb, Y, X, emb, h, h']
  have hfun_eq :
      ∀ r,
        (fb ∘ Y 0) r =
          (Set.indicator ({j} : Set (Fin k)) (fun _ => (1 : ℝ)) ∘ X 0) r := by
    intro r
    by_cases h : X 0 r = j
    · simp [Function.comp, X, hfbY_eq, h]
    · simp [Function.comp, X, hfbY_eq, h]
  have hfun_ext :
      fb ∘ Y 0 = Set.indicator ({j} : Set (Fin k)) (fun _ => (1 : ℝ)) ∘ X 0 :=
    funext hfun_eq
  let cesaro : ℕ → (ℕ → Fin k) → ℝ :=
    fun m r => 1 / (m : ℝ) * ∑ n : Fin m, fb (Y n r)
  have hcesaro_eq :
      ∀ m r, cesaro m r = rowProcessEmpiricalFreq (k := k) j r m := by
    intro m r
    have hsum :
        (∑ n : Fin m, (if r n = j then (1 : ℝ) else 0)) =
          Fintype.card {n : Fin m // r n = j} := by
      rw [Fintype.card_subtype]
      simp
    let p : ℕ → Prop := fun n => n < m ∧ r n = j
    let e : {n : Fin m // r n = j} ≃ {n : ℕ // p n} :=
      { toFun := fun n => ⟨n.1, n.1.2, by simpa [p] using n.2⟩
        invFun := fun n => ⟨⟨n.1, n.2.1⟩, by simpa [p] using n.2.2⟩
        left_inv := by intro n; cases n; rfl
        right_inv := by intro n; cases n; rfl }
    let s : Finset ℕ := (Finset.range m).filter fun n => r n = j
    have hs : ∀ n : ℕ, n ∈ s ↔ p n := by
      intro n
      simp [s, p]
    letI : Fintype {n : ℕ // p n} := Fintype.subtype s hs
    have hcard :
        Fintype.card {n : Fin m // r n = j} = Nat.count (fun n => r n = j) m := by
      calc
        Fintype.card {n : Fin m // r n = j} = Fintype.card {n : ℕ // p n} :=
          Fintype.card_congr e
        _ = s.card := by rw [Fintype.card_of_subtype s hs]
        _ = Nat.count (fun n => r n = j) m := by
              rw [Nat.count_eq_card_filter_range]
    calc
      cesaro m r
          = 1 / (m : ℝ) * ∑ n : Fin m, (if r n = j then (1 : ℝ) else 0) := by
              simp [cesaro, hfbY_eq]
      _ = 1 / (m : ℝ) * (Fintype.card {n : Fin m // r n = j} : ℝ) := by
            rw [hsum]
      _ = (Nat.count (fun n => r n = j) m : ℝ) / m := by
            simp [hcard, div_eq_mul_inv, mul_comm]
      _ = rowProcessEmpiricalFreq (k := k) j r m := by
            simp [rowProcessEmpiricalFreq]
  have hcesaro_meas : ∀ m : ℕ, Measurable (cesaro m) := by
    intro m
    exact
      (Finset.measurable_sum (Finset.univ : Finset (Fin m))
        (fun n _ => hfb_meas.comp (hY_meas n))).const_mul _
  have hfbY_int : ∀ n : ℕ, Integrable (fun r => fb (Y n r)) ρ := by
    intro n
    exact
      (integrable_const (1 : ℝ)).mono
        ((hfb_meas.comp (hY_meas n)).aestronglyMeasurable)
        (ae_of_all ρ fun r => by
          simp only [Real.norm_eq_abs, norm_one]
          exact hfb_bdd _)
  have hcesaro_int : ∀ m : ℕ, Integrable (cesaro m) ρ := by
    intro m
    exact
      (integrable_finset_sum (Finset.univ : Finset (Fin m))
        (f := fun n r => fb (Y n r))
        (fun n _ => hfbY_int n)).const_mul _
  have hlimitMeas_cesaro :
      MeasurableSet
        {r : ℕ → Fin k |
          ∃ q : ℝ,
            Filter.Tendsto (fun m => cesaro m r) Filter.atTop (nhds q)} :=
    MeasureTheory.measurableSet_exists_tendsto hcesaro_meas
  have hlimitMeas :
      MeasurableSet
        {r : ℕ → Fin k |
          ∃ q : ℝ,
            Filter.Tendsto
              (fun m => rowProcessEmpiricalFreq (k := k) j r m)
              Filter.atTop
              (nhds q)} := by
    have hEq :
        {r : ℕ → Fin k |
          ∃ q : ℝ,
            Filter.Tendsto
              (fun m => rowProcessEmpiricalFreq (k := k) j r m)
              Filter.atTop
              (nhds q)}
          =
        {r : ℕ → Fin k |
          ∃ q : ℝ,
            Filter.Tendsto (fun m => cesaro m r) Filter.atTop (nhds q)} := by
      ext r
      constructor
      · rintro ⟨q, hq⟩
        exact ⟨q, by simpa [hcesaro_eq] using hq⟩
      · rintro ⟨q, hq⟩
        exact ⟨q, by simpa [hcesaro_eq] using hq⟩
    rw [hEq]
    exact hlimitMeas_cesaro
  have hae_row :
      ∀ᵐ r ∂ρ,
        ∃ q : ℝ,
          Filter.Tendsto
            (fun m => rowProcessEmpiricalFreq (k := k) j r m)
            Filter.atTop
            (nhds q) :=
    ae_exists_tendsto_rowProcessEmpiricalFreq_of_exchangeable
      (k := k) (P := P) (i := i) (j := j) hExch hlimitMeas
  have hae_cesaro :
      ∀ᵐ r ∂ρ,
        ∃ q : ℝ,
          Filter.Tendsto (fun m => cesaro m r) Filter.atTop (nhds q) := by
    filter_upwards [hae_row] with r hr
    rcases hr with ⟨q, hq⟩
    exact ⟨q, by simpa [hcesaro_eq] using hq⟩
  let g : (ℕ → Fin k) → ℝ :=
    fun r => (((directingRowKernel (k := k) P i r) ({j} : Set (Fin k))).toReal)
  have hg_meas : Measurable g := by
    have hdir_eval_meas :
        Measurable
          (fun r : ℕ → Fin k =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)) ({j} : Set (Fin k))) := by
      simpa [ρ, X, directingRowKernel] using
        (directingMeasure_measurable_eval
          (μ := ρ) (X := X) (hX := hX_meas) ({j} : Set (Fin k))
          (measurableSet_singleton j))
    exact hdir_eval_meas.ennreal_toReal
  have hdir_ae :
      g =ᵐ[ρ]
        ρ[Set.indicator ({j} : Set (Fin k)) (fun _ => (1 : ℝ)) ∘ X 0 | tailSigma X] := by
    exact
      (@directingMeasure_X0_marginal
        _ _ _ ρ _ _ _ _ _ X hX_meas ({j} : Set (Fin k))
        (measurableSet_singleton j))
  have hg_int : Integrable g ρ := integrable_condExp.congr hdir_ae.symm
  have hces_L1 :=
    _root_.Exchangeability.DeFinetti.ViaL2.cesaro_to_condexp_L1
      hY_contr hY_meas fb hfb_meas hfb_bdd
  simp only [_root_.Exchangeability.DeFinetti.ViaL2.TailSigma.tailSigma,
             show Exchangeability.Tail.tailProcess Y = tailSigma X from htail,
             hfun_ext] at hces_L1
  have hL1 :
      ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M, ∫ r, |cesaro m r - g r| ∂ρ < ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := hces_L1 ε hε
    refine ⟨M, fun m hm => ?_⟩
    have habs_eq :
        (fun r =>
          |cesaro m r -
              (ρ[Set.indicator ({j} : Set (Fin k)) (fun _ => (1 : ℝ)) ∘ X 0
                | tailSigma X] r)|)
          =ᵐ[ρ]
        (fun r => |cesaro m r - g r|) := by
      filter_upwards [hdir_ae] with r hr
      simp [hr]
    calc
      ∫ r, |cesaro m r - g r| ∂ρ
          =
        ∫ r,
          |cesaro m r -
              (ρ[Set.indicator ({j} : Set (Fin k)) (fun _ => (1 : ℝ)) ∘ X 0
                | tailSigma X] r)| ∂ρ := by
              symm
              exact integral_congr_ae habs_eq
      _ < ε := hM m hm
  have huniq :
      ∀ᵐ r ∂ρ,
        ∀ q : ℝ,
          Filter.Tendsto (fun n => cesaro n r) Filter.atTop (nhds q) →
          q = g r := by
    exact
      _root_.Mettapedia.Logic.DirectingMeasureL1Transfer.ae_limit_eq_L1_limit_of_ae_tendsto_and_L1_tendsto
        hcesaro_meas hg_meas hcesaro_int hg_int hL1 hae_cesaro
  filter_upwards [hae_row, huniq] with r hr huniq_r
  rcases hr with ⟨q, hq⟩
  have hq_cesaro : Filter.Tendsto (fun n => cesaro n r) Filter.atTop (nhds q) := by
    simpa [hcesaro_eq] using hq
  have hq_eq : q = g r := huniq_r q hq_cesaro
  have hq' : Filter.Tendsto
      (fun m => rowProcessEmpiricalFreq (k := k) j r m) Filter.atTop (nhds (g r)) :=
    hq_eq ▸ hq
  simpa [g] using hq'

@[simp] lemma rowSuccessorEmpiricalFreq_eq_rowProcessEmpiricalFreq
    (i j : Fin k) (ω : ℕ → Fin k) (m : ℕ) :
  rowSuccessorEmpiricalFreq (k := k) i j ω m =
      rowProcessEmpiricalFreq (k := k) j
        (rowSuccessorVisitProcess (k := k) i ω) m := rfl

@[simp] lemma pathPrefixTraj_succ_eq_trajSnoc
    (ω : ℕ → Fin k) (N : ℕ) :
    pathPrefixTraj (k := k) ω (N + 1) =
      trajSnoc (k := k) (pathPrefixTraj (k := k) ω N) (ω (N + 1)) := by
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp [pathPrefixTraj, trajSnoc]
  | cast j =>
      simp [pathPrefixTraj, trajSnoc]

lemma rowSuccessorAtNthVisit_visitCountBefore_eq_successor_of_eq
    (ω : ℕ → Fin k) (i : Fin k) (N : ℕ)
    (hvisit : ω N = i) :
    rowSuccessorAtNthVisit (k := k) i (visitCountBefore (k := k) ω i N) ω =
      successorAt (k := k) ω N := by
  have hNth :
      nthVisitTime (k := k) ω i (visitCountBefore (k := k) ω i N) = some N := by
    exact
      (nthVisitTime_eq_some_iff (k := k) ω i (visitCountBefore (k := k) ω i N) N).2
        ⟨hvisit, rfl⟩
  simp [rowSuccessorAtNthVisit, hNth]

lemma pathPrefixState_counts_eq_rowSuccessorEmpiricalCount
    (ω : ℕ → Fin k) (N : ℕ) (i j : Fin k) :
    (pathPrefixState (k := k) ω N).counts.counts i j =
      rowSuccessorEmpiricalCount (k := k) i j ω
        (visitCountBefore (k := k) ω i N) := by
  induction N with
  | zero =>
      simp [pathPrefixState, pathPrefixTraj, rowSuccessorEmpiricalCount,
        visitCountBefore, stateOfTraj, countsOfFn, transCount]
  | succ N ih =>
      have hcountState :
          (pathPrefixState (k := k) ω (N + 1)).counts.counts i j =
            (pathPrefixState (k := k) ω N).counts.counts i j +
              (if ω N = i ∧ ω (N + 1) = j then 1 else 0) := by
        rw [pathPrefixState, pathPrefixTraj_succ_eq_trajSnoc]
        exact
          (transCount_snoc
            (n := N)
            (xs := pathPrefixTraj (k := k) ω N)
            (x := ω (N + 1))
            (a := i) (b := j))
      by_cases hvisit : ω N = i
      · have hvisitCount :
            visitCountBefore (k := k) ω i (N + 1) =
              visitCountBefore (k := k) ω i N + 1 := by
          rw [visitCountBefore_eq_natCount (k := k) ω i (N + 1),
            visitCountBefore_eq_natCount (k := k) ω i N]
          exact Nat.count_succ_eq_succ_count hvisit
        have hrow :
            rowSuccessorVisitProcess (k := k) i ω
                (visitCountBefore (k := k) ω i N) = j ↔
              ω (N + 1) = j := by
          unfold rowSuccessorVisitProcess
          rw [rowSuccessorAtNthVisit_visitCountBefore_eq_successor_of_eq
            (k := k) ω i N hvisit]
          rfl
        rw [hcountState, ih, hvisitCount]
        by_cases hnext : ω (N + 1) = j
        · have hsuccCount :
              rowSuccessorEmpiricalCount (k := k) i j ω
                  (visitCountBefore (k := k) ω i N + 1) =
                rowSuccessorEmpiricalCount (k := k) i j ω
                  (visitCountBefore (k := k) ω i N) + 1 := by
            unfold rowSuccessorEmpiricalCount
            exact Nat.count_succ_eq_succ_count (hrow.mpr hnext)
          rw [hsuccCount]
          simp [hvisit, hnext]
        · have hstayCount :
              rowSuccessorEmpiricalCount (k := k) i j ω
                  (visitCountBefore (k := k) ω i N + 1) =
                rowSuccessorEmpiricalCount (k := k) i j ω
                  (visitCountBefore (k := k) ω i N) := by
            unfold rowSuccessorEmpiricalCount
            exact Nat.count_succ_eq_count (by
              intro hrowEq
              exact hnext (hrow.mp hrowEq))
          rw [hstayCount]
          simp [hvisit, hnext]
      · have hvisitCount :
            visitCountBefore (k := k) ω i (N + 1) =
              visitCountBefore (k := k) ω i N := by
          rw [visitCountBefore_eq_natCount (k := k) ω i (N + 1),
            visitCountBefore_eq_natCount (k := k) ω i N]
          exact Nat.count_succ_eq_count hvisit
        rw [hcountState, ih, hvisitCount]
        simp [rowSuccessorEmpiricalCount, hvisit]

lemma pathPrefixState_countRatio_eq_rowSuccessorEmpiricalFreq
    (ω : ℕ → Fin k) (N : ℕ) (i j : Fin k) :
    ((pathPrefixState (k := k) ω N).counts.counts i j : ℝ) /
        (MarkovDeFinettiHardEuler.outdeg (k := k)
          (pathPrefixState (k := k) ω N) i : ℝ) =
      rowSuccessorEmpiricalFreq (k := k) i j ω
        (visitCountBefore (k := k) ω i N) := by
  rw [pathPrefixState_counts_eq_rowSuccessorEmpiricalCount,
    pathPrefixState_outdeg_eq_visitCountBefore]
  rfl

lemma tendsto_pathPrefixState_countRatio_of_tendsto_rowSuccessorEmpiricalFreq
    (ω : ℕ → Fin k) (Nf : ℕ → ℕ) (i j : Fin k) (θ : ℝ)
    (hout :
      Filter.Tendsto
        (fun n => visitCountBefore (k := k) ω i (Nf n))
        Filter.atTop Filter.atTop)
    (hfreq :
      Filter.Tendsto
        (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
        Filter.atTop (nhds θ)) :
    Filter.Tendsto
      (fun n =>
        ((pathPrefixState (k := k) ω (Nf n)).counts.counts i j : ℝ) /
          (MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (Nf n)) i : ℝ))
      Filter.atTop (nhds θ) := by
  have hEq :
      (fun n =>
        ((pathPrefixState (k := k) ω (Nf n)).counts.counts i j : ℝ) /
          (MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (Nf n)) i : ℝ)) =
      (fun n =>
        rowSuccessorEmpiricalFreq (k := k) i j ω
          (visitCountBefore (k := k) ω i (Nf n))) := by
    funext n
    exact pathPrefixState_countRatio_eq_rowSuccessorEmpiricalFreq
      (k := k) ω (Nf n) i j
  rw [hEq]
  exact hfreq.comp hout

lemma pathPrefixState_ratioData_of_tendsto_rowSuccessorEmpiricalFreq
    (ω : ℕ → Fin k) (Nf : ℕ → ℕ) (Θ : Fin k → Fin k → ℝ)
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun n => visitCountBefore (k := k) ω i (Nf n))
          Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop (nhds (Θ i j))) :
    ∀ i j : Fin k,
      Filter.Tendsto
        (fun n =>
          ((pathPrefixState (k := k) ω (Nf n)).counts.counts i j : ℝ) /
            (MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (Nf n)) i : ℝ))
        Filter.atTop (nhds (Θ i j)) := by
  intro i j
  exact tendsto_pathPrefixState_countRatio_of_tendsto_rowSuccessorEmpiricalFreq
    (k := k) ω Nf i j (Θ i j) (hout i) (hfreq i j)

/-- Package the ratio-data limit along a path-prefix subsequence directly from
outdegree growth of the prefix states and Cesaro convergence of the row-successor
empirical frequencies. -/
lemma pathPrefixState_ratioData_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_outdeg
    (ω : ℕ → Fin k) (Nf : ℕ → ℕ) (Θ : Fin k → Fin k → ℝ)
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun n =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (Nf n)) i)
          Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop (nhds (Θ i j))) :
    ∀ i j : Fin k,
      Filter.Tendsto
        (fun n =>
          ((pathPrefixState (k := k) ω (Nf n)).counts.counts i j : ℝ) /
            (MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (Nf n)) i : ℝ))
        Filter.atTop (nhds (Θ i j)) := by
  refine pathPrefixState_ratioData_of_tendsto_rowSuccessorEmpiricalFreq
    (k := k) ω Nf Θ ?_ hfreq
  intro i
  have hEq :
      (fun n => visitCountBefore (k := k) ω i (Nf n)) =
        (fun n =>
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (Nf n)) i) := by
    funext n
    symm
    exact pathPrefixState_outdeg_eq_visitCountBefore (k := k) ω (Nf n) i
  rw [hEq]
  exact hout i

lemma succ_le_outdeg_pathPrefixState_of_nthVisitTime_lt
    (ω : ℕ → Fin k) (i : Fin k) (n t N : ℕ)
    (ht : nthVisitTime (k := k) ω i n = some t)
    (htN : t < N) :
    n + 1 ≤ MarkovDeFinettiHardEuler.outdeg (k := k)
      (pathPrefixState (k := k) ω N) i := by
  have his : isNthVisitTime (k := k) ω i n t :=
    (nthVisitTime_eq_some_iff (k := k) ω i n t).1 ht
  rcases his with ⟨hvisit, hcount⟩
  have hsucc :
      n + 1 = visitCountBefore (k := k) ω i (t + 1) := by
    calc
      n + 1 = Nat.count (fun s => ω s = i) t + 1 := by
        simpa [visitCountBefore_eq_natCount (k := k) ω i t] using congrArg Nat.succ hcount.symm
      _ = Nat.count (fun s => ω s = i) (t + 1) := by
        symm
        exact Nat.count_succ_eq_succ_count hvisit
      _ = visitCountBefore (k := k) ω i (t + 1) := by
        symm
        exact visitCountBefore_eq_natCount (k := k) ω i (t + 1)
  have hmono :
      visitCountBefore (k := k) ω i (t + 1) ≤ visitCountBefore (k := k) ω i N := by
    rw [visitCountBefore_eq_natCount (k := k) ω i (t + 1),
      visitCountBefore_eq_natCount (k := k) ω i N]
    exact Nat.count_monotone _ (Nat.succ_le_of_lt htN)
  calc
    n + 1 = visitCountBefore (k := k) ω i (t + 1) := hsucc
    _ ≤ visitCountBefore (k := k) ω i N := hmono
    _ = MarkovDeFinettiHardEuler.outdeg (k := k)
          (pathPrefixState (k := k) ω N) i := by
            symm
            exact pathPrefixState_outdeg_eq_visitCountBefore (k := k) ω N i

lemma tendsto_outdeg_pathPrefixState_atTop_of_all_nthVisitTimeExists
    (ω : ℕ → Fin k) (i : Fin k)
    (hall : ∀ n : ℕ, nthVisitTimeExists (k := k) ω i n)
    {Nf : ℕ → ℕ}
    (hNf : Filter.Tendsto Nf Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n =>
        MarkovDeFinettiHardEuler.outdeg (k := k)
          (pathPrefixState (k := k) ω (Nf n)) i)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro m
  rcases hall m with ⟨t, ht⟩
  have hsome : nthVisitTime (k := k) ω i m = some t :=
    (nthVisitTime_eq_some_iff (k := k) ω i m t).2 ht
  have hlarge : ∀ᶠ n in Filter.atTop, t + 1 ≤ Nf n := by
    have hmem : Set.Ici (t + 1) ∈ (Filter.atTop : Filter ℕ) := by
      exact Filter.mem_atTop_sets.2 ⟨t + 1, fun b hb => hb⟩
    exact hNf hmem
  filter_upwards [hlarge] with n hn
  have htN : t < Nf n := lt_of_lt_of_le (Nat.lt_succ_self t) hn
  have hbound :=
    succ_le_outdeg_pathPrefixState_of_nthVisitTime_lt
      (k := k) (ω := ω) (i := i) (n := m) (t := t) (N := Nf n) hsome htN
  exact le_trans (Nat.le_succ m) hbound

theorem ae_tendsto_outdeg_pathPrefixState_atTop_of_strongRecurrence
    (P : MeasureTheory.Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (i : Fin k) {Nf : ℕ → ℕ}
    (hNf : Filter.Tendsto Nf Filter.atTop Filter.atTop) :
    ∀ᵐ ω ∂P, (∃ t : ℕ, ω t = i) →
      Filter.Tendsto
        (fun n =>
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (Nf n)) i)
        Filter.atTop Filter.atTop := by
  filter_upwards [hStrong i] with ω hω
  intro hvisit
  exact tendsto_outdeg_pathPrefixState_atTop_of_all_nthVisitTimeExists
    (k := k) (ω := ω) (i := i) (hω hvisit) hNf

theorem ae_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_of_exists_visit
    (P : MeasureTheory.Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (i : Fin k) (n0 : ℕ) :
    ∀ᵐ ω ∂P, (∃ t : ℕ, ω t = i) →
      Filter.Tendsto
        (fun r =>
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (n0 + r)) i)
        Filter.atTop Filter.atTop := by
  have hNf : Filter.Tendsto (fun r : ℕ => n0 + r) Filter.atTop Filter.atTop := by
    simpa [add_comm] using (Filter.tendsto_add_atTop_nat n0)
  exact ae_tendsto_outdeg_pathPrefixState_atTop_of_strongRecurrence
    (k := k) P hStrong i (hNf := hNf)

theorem ae_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_of_start
    (P : MeasureTheory.Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (a : Fin k) (n0 : ℕ) :
    ∀ᵐ ω ∂P, ω 0 = a →
      Filter.Tendsto
        (fun r =>
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (n0 + r)) a)
        Filter.atTop Filter.atTop := by
  filter_upwards
    [ae_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_of_exists_visit
      (k := k) P hStrong a n0] with ω hω hstart
  exact hω ⟨0, hstart⟩

lemma ae_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_on_start_of_ae_exists_visit
    (P : MeasureTheory.Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (a i : Fin k) (n0 : ℕ)
    (hvisit : ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i) :
    ∀ᵐ ω ∂P, ω 0 = a →
      Filter.Tendsto
        (fun r =>
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (n0 + r)) i)
        Filter.atTop Filter.atTop := by
  filter_upwards
    [hvisit,
      ae_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_of_exists_visit
        (k := k) P hStrong i n0] with ω hvisitω hgrow hstart
  exact hgrow (hvisitω hstart)

lemma ae_coordwise_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_on_start_of_ae_exists_visit
    (P : MeasureTheory.Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (a : Fin k) (n0 : ℕ)
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i) :
    ∀ i : Fin k,
      ∀ᵐ ω ∂P, ω 0 = a →
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (n0 + r)) i)
          Filter.atTop Filter.atTop := by
  intro i
  exact
    ae_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_on_start_of_ae_exists_visit
      (k := k) P hStrong a i n0 (hvisit i)

lemma ae_exists_visit_on_start_of_ae_infinite_visits
    (P : MeasureTheory.Measure (ℕ → Fin k))
    (a i : Fin k)
    (hinf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i := by
  filter_upwards [hinf] with ω hω _hstart
  exact hω.nonempty

lemma ae_coordwise_exists_visit_on_start_of_ae_infinite_visits
    (P : MeasureTheory.Measure (ℕ → Fin k))
    (a : Fin k)
    (hinf : ∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    ∀ i : Fin k, ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i := by
  intro i
  exact ae_exists_visit_on_start_of_ae_infinite_visits
    (k := k) P a i (hinf i)

/-- Delete a finite sequence of non-root edge copies from an Euler graph. -/
def deleteCopies
    {t : Fin k} (G : EulerGraph k) :
    List (NonrootVertex t × Fin k) → EulerGraph k
  | [] => G
  | (u, v) :: ds =>
      deleteCopies (deleteOneCopy (k := k) G u v) ds

/-- Lower-bound numerator accumulated from repeated one-token deletions. -/
def tokenDeletionLowerNumerator
    {t : Fin k} (G : EulerGraph k) :
    List (NonrootVertex t × Fin k) → ℕ
  | [] => 1
  | (u, v) :: ds =>
      (G u.1 v - 1) *
        tokenDeletionLowerNumerator (deleteOneCopy (k := k) G u v) ds

/-- Lower-bound denominator accumulated from repeated one-token deletions. -/
def tokenDeletionLowerDenominator
    {t : Fin k} (G : EulerGraph k) :
    List (NonrootVertex t × Fin k) → ℕ
  | [] => 1
  | (u, v) :: ds =>
      G u.1 v *
        tokenDeletionLowerDenominator (deleteOneCopy (k := k) G u v) ds

private lemma weightedTargetRootedArborescenceCount_deleteOneCopy_upper_term
    (G : EulerGraph k) (t : Fin k) (u : NonrootVertex t) (v : Fin k)
    (p : {p : TargetParentAssignment t //
      IsTargetRootedArborescence (k := k) t p}) :
    (∏ x : NonrootVertex t, deleteOneCopy (k := k) G u v x.1 (p.1 x)) ≤
      (∏ x : NonrootVertex t, G x.1 (p.1 x)) := by
  classical
  let rest : ℕ := ((Finset.univ.erase u).prod fun x : NonrootVertex t => G x.1 (p.1 x))
  have hfull :
      (∏ x : NonrootVertex t, G x.1 (p.1 x)) =
        G u.1 (p.1 u) * rest := by
    simpa [rest] using
      targetRootedArborescenceWeight_eq_sourceFactor_mul
        (k := k) G t p.1 u
  have herase :
      ((Finset.univ.erase u).prod fun x : NonrootVertex t =>
          deleteOneCopy (k := k) G u v x.1 (p.1 x)) = rest := by
    simpa [rest] using deleteOneCopy_prod_erase_eq (k := k) G t u v p.1
  have hdel :
      (∏ x : NonrootVertex t, deleteOneCopy (k := k) G u v x.1 (p.1 x)) =
        deleteOneCopy (k := k) G u v u.1 (p.1 u) * rest := by
    calc
      (∏ x : NonrootVertex t, deleteOneCopy (k := k) G u v x.1 (p.1 x))
          = deleteOneCopy (k := k) G u v u.1 (p.1 u) *
              ((Finset.univ.erase u).prod fun x : NonrootVertex t =>
                deleteOneCopy (k := k) G u v x.1 (p.1 x)) := by
                simpa [mul_comm] using
                  targetRootedArborescenceWeight_eq_sourceFactor_mul
                    (k := k) (G := deleteOneCopy (k := k) G u v) t p.1 u
      _ = deleteOneCopy (k := k) G u v u.1 (p.1 u) * rest := by
            rw [herase]
  by_cases hmatch : p.1 u = v
  · have hsame :
        deleteOneCopy (k := k) G u v u.1 (p.1 u) = G u.1 v - 1 := by
      simp [deleteOneCopy, hmatch]
    have hle :
        (G u.1 v - 1) * rest ≤ G u.1 v * rest :=
      Nat.mul_le_mul_right rest (Nat.sub_le _ _)
    simpa [hfull, hdel, hsame, hmatch] using hle
  · have hsame :
        deleteOneCopy (k := k) G u v u.1 (p.1 u) = G u.1 (p.1 u) := by
      simp [deleteOneCopy, hmatch]
    simp [hfull, hdel, hsame]

lemma weightedTargetRootedArborescenceCount_deleteOneCopy_le
    (G : EulerGraph k) (t : Fin k) (u : NonrootVertex t) (v : Fin k) :
    weightedTargetRootedArborescenceCount (k := k)
        (deleteOneCopy (k := k) G u v) t ≤
      weightedTargetRootedArborescenceCount (k := k) G t := by
  classical
  unfold weightedTargetRootedArborescenceCount
  refine Finset.sum_le_sum ?_
  intro p hp
  exact weightedTargetRootedArborescenceCount_deleteOneCopy_upper_term
    (k := k) G t u v p

lemma tokenRootedArborescenceCount_deleteOneCopy_le
    (G : EulerGraph k) (t : Fin k) (u : NonrootVertex t) (v : Fin k) :
    tokenRootedArborescenceCount (k := k)
        (deleteOneCopy (k := k) G u v) t ≤
      tokenRootedArborescenceCount (k := k) G t := by
  rw [tokenRootedArborescenceCount_eq_weightedTargetRootedArborescenceCount,
    tokenRootedArborescenceCount_eq_weightedTargetRootedArborescenceCount]
  exact weightedTargetRootedArborescenceCount_deleteOneCopy_le
    (k := k) G t u v

lemma tokenRootedArborescenceCount_deleteCopies_lower
    {t : Fin k} (G : EulerGraph k) (ds : List (NonrootVertex t × Fin k)) :
    tokenDeletionLowerNumerator (k := k) G ds *
        tokenRootedArborescenceCount (k := k) G t ≤
      tokenDeletionLowerDenominator (k := k) G ds *
        tokenRootedArborescenceCount (k := k) (deleteCopies (k := k) G ds) t := by
  induction ds generalizing G with
  | nil =>
      simp [deleteCopies, tokenDeletionLowerNumerator, tokenDeletionLowerDenominator]
  | cons uv ds ih =>
      rcases uv with ⟨u, v⟩
      let G' : EulerGraph k := deleteOneCopy (k := k) G u v
      have hstep :
          (G u.1 v - 1) * tokenRootedArborescenceCount (k := k) G t ≤
            G u.1 v * tokenRootedArborescenceCount (k := k) G' t := by
        simpa [G'] using
          tokenRootedArborescenceCount_deleteOneCopy_lower
            (k := k) (G := G) (t := t) (u := u) (v := v)
      have hstepMul :
          tokenDeletionLowerNumerator (k := k) G' ds *
              ((G u.1 v - 1) * tokenRootedArborescenceCount (k := k) G t) ≤
            tokenDeletionLowerNumerator (k := k) G' ds *
              (G u.1 v * tokenRootedArborescenceCount (k := k) G' t) :=
        Nat.mul_le_mul_left _ hstep
      have hrestMul :
          G u.1 v *
              (tokenDeletionLowerNumerator (k := k) G' ds *
                tokenRootedArborescenceCount (k := k) G' t) ≤
            G u.1 v *
              (tokenDeletionLowerDenominator (k := k) G' ds *
                tokenRootedArborescenceCount (k := k)
                  (deleteCopies (k := k) G' ds) t) :=
        Nat.mul_le_mul_left _ (ih (G := G'))
      calc
        tokenDeletionLowerNumerator (k := k) G ((u, v) :: ds) *
            tokenRootedArborescenceCount (k := k) G t
            =
              tokenDeletionLowerNumerator (k := k) G' ds *
                ((G u.1 v - 1) * tokenRootedArborescenceCount (k := k) G t) := by
                  simp [tokenDeletionLowerNumerator, G']
                  ac_rfl
        _ ≤ tokenDeletionLowerNumerator (k := k) G' ds *
              (G u.1 v * tokenRootedArborescenceCount (k := k) G' t) := hstepMul
        _ = G u.1 v *
              (tokenDeletionLowerNumerator (k := k) G' ds *
                tokenRootedArborescenceCount (k := k) G' t) := by
                ac_rfl
        _ ≤ G u.1 v *
              (tokenDeletionLowerDenominator (k := k) G' ds *
                tokenRootedArborescenceCount (k := k)
                  (deleteCopies (k := k) G' ds) t) := hrestMul
        _ = tokenDeletionLowerDenominator (k := k) G ((u, v) :: ds) *
              tokenRootedArborescenceCount (k := k)
                (deleteCopies (k := k) G ((u, v) :: ds)) t := by
                simp [tokenDeletionLowerDenominator, deleteCopies, G']
                ac_rfl

lemma positiveTokenRootedArborescenceCount_deleteCopies_lower
    {t : Fin k} (G : EulerGraph k) (ds : List (NonrootVertex t × Fin k)) :
    tokenDeletionLowerNumerator (k := k) G ds *
        positiveTokenRootedArborescenceCount (k := k) G t ≤
      tokenDeletionLowerDenominator (k := k) G ds *
        positiveTokenRootedArborescenceCount
          (k := k) (deleteCopies (k := k) G ds) t := by
  induction ds generalizing G with
  | nil =>
      simp [deleteCopies, tokenDeletionLowerNumerator, tokenDeletionLowerDenominator]
  | cons uv ds ih =>
      rcases uv with ⟨u, v⟩
      let G' : EulerGraph k := deleteOneCopy (k := k) G u v
      have hstep :
          (G u.1 v - 1) * positiveTokenRootedArborescenceCount (k := k) G t ≤
            G u.1 v * positiveTokenRootedArborescenceCount (k := k) G' t := by
        simpa [G'] using
          positiveTokenRootedArborescenceCount_deleteOneCopy_lower
            (k := k) (G := G) (t := t) (u := u) (v := v)
      have hstepMul :
          tokenDeletionLowerNumerator (k := k) G' ds *
              ((G u.1 v - 1) * positiveTokenRootedArborescenceCount (k := k) G t) ≤
            tokenDeletionLowerNumerator (k := k) G' ds *
              (G u.1 v * positiveTokenRootedArborescenceCount (k := k) G' t) :=
        Nat.mul_le_mul_left _ hstep
      have hrestMul :
          G u.1 v *
              (tokenDeletionLowerNumerator (k := k) G' ds *
                positiveTokenRootedArborescenceCount (k := k) G' t) ≤
            G u.1 v *
              (tokenDeletionLowerDenominator (k := k) G' ds *
                positiveTokenRootedArborescenceCount (k := k)
                  (deleteCopies (k := k) G' ds) t) :=
        Nat.mul_le_mul_left _ (ih (G := G'))
      calc
        tokenDeletionLowerNumerator (k := k) G ((u, v) :: ds) *
            positiveTokenRootedArborescenceCount (k := k) G t
            =
              tokenDeletionLowerNumerator (k := k) G' ds *
                ((G u.1 v - 1) * positiveTokenRootedArborescenceCount (k := k) G t) := by
                  simp [tokenDeletionLowerNumerator, G']
                  ac_rfl
        _ ≤ tokenDeletionLowerNumerator (k := k) G' ds *
              (G u.1 v * positiveTokenRootedArborescenceCount (k := k) G' t) := hstepMul
        _ = G u.1 v *
              (tokenDeletionLowerNumerator (k := k) G' ds *
                positiveTokenRootedArborescenceCount (k := k) G' t) := by
                ac_rfl
        _ ≤ G u.1 v *
              (tokenDeletionLowerDenominator (k := k) G' ds *
                positiveTokenRootedArborescenceCount (k := k)
                  (deleteCopies (k := k) G' ds) t) := hrestMul
        _ = tokenDeletionLowerDenominator (k := k) G ((u, v) :: ds) *
              positiveTokenRootedArborescenceCount (k := k)
                (deleteCopies (k := k) G ((u, v) :: ds)) t := by
                simp [tokenDeletionLowerDenominator, deleteCopies, G']
                ac_rfl

lemma tokenRootedArborescenceCount_deleteCopies_le
    {t : Fin k} (G : EulerGraph k) (ds : List (NonrootVertex t × Fin k)) :
    tokenRootedArborescenceCount (k := k) (deleteCopies (k := k) G ds) t ≤
      tokenRootedArborescenceCount (k := k) G t := by
  induction ds generalizing G with
  | nil =>
      simp [deleteCopies]
  | cons uv ds ih =>
      rcases uv with ⟨u, v⟩
      let G' : EulerGraph k := deleteOneCopy (k := k) G u v
      have hstep :
          tokenRootedArborescenceCount (k := k) G' t ≤
            tokenRootedArborescenceCount (k := k) G t := by
        simpa [G'] using
          tokenRootedArborescenceCount_deleteOneCopy_le
            (k := k) (G := G) (t := t) (u := u) (v := v)
      exact le_trans (ih (G := G')) hstep

lemma tokenRootedArborescenceCount_congr_nonroot_rows
    {t : Fin k} {G G' : EulerGraph k}
    (hrow : ∀ u : NonrootVertex t, ∀ v : Fin k, G u.1 v = G' u.1 v) :
    tokenRootedArborescenceCount (k := k) G t =
      tokenRootedArborescenceCount (k := k) G' t := by
  rw [tokenRootedArborescenceCount_eq_weightedTargetRootedArborescenceCount,
    tokenRootedArborescenceCount_eq_weightedTargetRootedArborescenceCount]
  unfold weightedTargetRootedArborescenceCount
  refine Finset.sum_congr rfl ?_
  intro p hp
  refine Finset.prod_congr rfl ?_
  intro u hu
  exact hrow u (p.1 u)

private lemma count_flatMap_replicate_of_nodup
    {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} (hnodup : l.Nodup) (f : α → ℕ) (a : α) :
    (l.flatMap fun x => List.replicate (f x) x).count a =
      if a ∈ l then f a else 0 := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hx, hxs⟩
      by_cases hax : a = x
      · subst hax
        have hnotMem :
            a ∉ xs.flatMap (fun y => List.replicate (f y) y) := by
          intro hmem
          rcases List.mem_flatMap.1 hmem with ⟨y, hy, hyrep⟩
          have hay : a = y := by
            exact (List.mem_replicate.mp hyrep).2
          exact hx (hay.symm ▸ hy)
        have hcountTail :
            (xs.flatMap fun y => List.replicate (f y) y).count a = 0 := by
          exact List.count_eq_zero_of_not_mem hnotMem
        simpa [List.flatMap, hcountTail]
      · have hcountRep : (List.replicate (f x) x).count a = 0 := by
          have hxa : x ≠ a := fun h => hax h.symm
          simp [List.count_replicate, hxa]
        simpa [List.flatMap, hcountRep, hax] using ih hxs

/-- Ordered list of all non-root edge pairs. -/
noncomputable def nonrootEdgePairList (t : Fin k) :
    List (NonrootVertex t × Fin k) :=
  (((Finset.univ : Finset (NonrootVertex t)).product
      (Finset.univ : Finset (Fin k))).toList)

lemma nonrootEdgePairList_nodup (t : Fin k) :
    (nonrootEdgePairList (k := k) t).Nodup := by
  unfold nonrootEdgePairList
  exact Finset.nodup_toList _

lemma mem_nonrootEdgePairList (t : Fin k) (uv : NonrootVertex t × Fin k) :
    uv ∈ nonrootEdgePairList (k := k) t := by
  unfold nonrootEdgePairList
  exact Finset.mem_toList.2 (by simp)

/-- The finite multiset of non-root prefix deletions, grouped by edge type. -/
noncomputable def prefixNonrootDeletionList
    (t : Fin k) (a : Fin k) (ys : List (Fin k)) :
    List (NonrootVertex t × Fin k) :=
  (nonrootEdgePairList (k := k) t).flatMap fun uv =>
    List.replicate
      ((prefixWordState (k := k) a ys).counts.counts uv.1.1 uv.2) uv

lemma count_prefixNonrootDeletionList
    (t : Fin k) (a : Fin k) (ys : List (Fin k))
    (u : NonrootVertex t) (v : Fin k) :
    (prefixNonrootDeletionList (k := k) t a ys).count (u, v) =
      (prefixWordState (k := k) a ys).counts.counts u.1 v := by
  unfold prefixNonrootDeletionList
  simpa [mem_nonrootEdgePairList (k := k) t (u, v)] using
    count_flatMap_replicate_of_nodup
      (l := nonrootEdgePairList (k := k) t)
      (hnodup := nonrootEdgePairList_nodup (k := k) t)
      (f := fun uv =>
        (prefixWordState (k := k) a ys).counts.counts uv.1.1 uv.2)
      (a := (u, v))

lemma deleteCopies_apply_nonroot_eq_sub_count
    {t : Fin k} (G : EulerGraph k)
    (ds : List (NonrootVertex t × Fin k))
    (u : NonrootVertex t) (v : Fin k) :
    deleteCopies (k := k) G ds u.1 v =
      G u.1 v - ds.count (u, v) := by
  induction ds generalizing G with
  | nil =>
      simp [deleteCopies]
  | cons uv ds ih =>
      rcases uv with ⟨u', v'⟩
      by_cases hsame : (u', v') = (u, v)
      · have hsame' : u' = u := congrArg Prod.fst hsame
        have hsame'' : v' = v := congrArg Prod.snd hsame
        have hdel :
            deleteOneCopy (k := k) G u' v' u.1 v = G u.1 v - 1 := by
          rw [hsame', hsame'']
          exact deleteOneCopy_apply_same (k := k) G u v
        calc
          deleteCopies (k := k) G ((u', v') :: ds) u.1 v
              = deleteCopies (k := k) (deleteOneCopy (k := k) G u' v') ds u.1 v := by
                  rfl
          _ = deleteOneCopy (k := k) G u' v' u.1 v - ds.count (u, v) := by
                exact ih (deleteOneCopy (k := k) G u' v')
          _ = (G u.1 v - 1) - ds.count (u, v) := by rw [hdel]
          _ = G u.1 v - (ds.count (u, v) + 1) := by
                rw [Nat.sub_sub, Nat.add_comm]
          _ = G u.1 v - ((u', v') :: ds).count (u, v) := by
                simp [hsame', hsame'']
      · have hneq :
            ¬ (u.1 = u'.1 ∧ v = v') := by
          intro hpair
          apply hsame
          rcases hpair with ⟨hsrc, htgt⟩
          apply Prod.ext
          · exact (Subtype.ext hsrc).symm
          · exact htgt.symm
        have hdel :
            deleteOneCopy (k := k) G u' v' u.1 v = G u.1 v := by
          simp [deleteOneCopy, hneq]
        calc
          deleteCopies (k := k) G ((u', v') :: ds) u.1 v
              = deleteCopies (k := k) (deleteOneCopy (k := k) G u' v') ds u.1 v := by
                  rfl
          _ = deleteOneCopy (k := k) G u' v' u.1 v - ds.count (u, v) := by
                exact ih (deleteOneCopy (k := k) G u' v')
          _ = G u.1 v - ds.count (u, v) := by rw [hdel]
          _ = G u.1 v - ((u', v') :: ds).count (u, v) := by
                have hcount :
                    List.count (u, v) ((u', v') :: ds) = List.count (u, v) ds := by
                  by_cases hpair : (u', v') = (u, v)
                  · exact (False.elim (hsame hpair))
                  · simp [hpair]
                rw [hcount]

lemma deleteCopies_prefixNonrootDeletionList_apply
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k)
    (u : NonrootVertex eN.last) (v : Fin k) :
    deleteCopies (k := k)
        (graphOfState (k := k) eN)
        (prefixNonrootDeletionList (k := k) eN.last a ys) u.1 v =
      graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN) u.1 v := by
  rw [deleteCopies_apply_nonroot_eq_sub_count]
  simp [graphOfState, residualStateOfPrefix_counts, count_prefixNonrootDeletionList]

lemma tokenRootedArborescenceCount_residualStateOfPrefix_eq_deleteCopies_prefixNonrootDeletionList
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    tokenRootedArborescenceCount (k := k)
        (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) eN.last =
      tokenRootedArborescenceCount (k := k)
        (deleteCopies (k := k)
          (graphOfState (k := k) eN)
          (prefixNonrootDeletionList (k := k) eN.last a ys))
        eN.last := by
  symm
  apply tokenRootedArborescenceCount_congr_nonroot_rows (k := k)
  intro u v
  exact deleteCopies_prefixNonrootDeletionList_apply (k := k) a ys eN u v

lemma positiveTokenRootedArborescenceCount_residualStateOfPrefix_eq_deleteCopies_prefixNonrootDeletionList
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    positiveTokenRootedArborescenceCount (k := k)
        (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) eN.last =
      positiveTokenRootedArborescenceCount (k := k)
        (deleteCopies (k := k)
          (graphOfState (k := k) eN)
          (prefixNonrootDeletionList (k := k) eN.last a ys))
        eN.last := by
  symm
  apply positiveTokenRootedArborescenceCount_congr_nonroot_rows (k := k)
  intro u v
  exact deleteCopies_prefixNonrootDeletionList_apply (k := k) a ys eN u v

lemma prefixTokenRootedArborescenceRatio_eq_deleteCopies_prefixNonroot_ratio
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN =
      ((tokenRootedArborescenceCount (k := k)
          (deleteCopies (k := k)
            (graphOfState (k := k) eN)
            (prefixNonrootDeletionList (k := k) eN.last a ys))
          eN.last : ℚ) /
        tokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) eN) eN.last) := by
  unfold prefixTokenRootedArborescenceRatio
  simpa [residualStateOfPrefix_last] using
    congrArg
      (fun m : ℕ =>
        (m : ℚ) /
          tokenRootedArborescenceCount (k := k)
            (graphOfState (k := k) eN) eN.last)
      (tokenRootedArborescenceCount_residualStateOfPrefix_eq_deleteCopies_prefixNonrootDeletionList
        (k := k) a ys eN)

lemma prefixPositiveTokenRootedArborescenceRatio_eq_deleteCopies_prefixNonroot_ratio
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN =
      ((positiveTokenRootedArborescenceCount (k := k)
          (deleteCopies (k := k)
            (graphOfState (k := k) eN)
            (prefixNonrootDeletionList (k := k) eN.last a ys))
          eN.last : ℚ) /
        positiveTokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) eN) eN.last) := by
  unfold prefixPositiveTokenRootedArborescenceRatio
  simpa [residualStateOfPrefix_last] using
    congrArg
      (fun m : ℕ =>
        (m : ℚ) /
          positiveTokenRootedArborescenceCount (k := k)
            (graphOfState (k := k) eN) eN.last)
      (positiveTokenRootedArborescenceCount_residualStateOfPrefix_eq_deleteCopies_prefixNonrootDeletionList
        (k := k) a ys eN)

/-- Prefix-specific lower-bound numerator for the non-root deletion problem. -/
def prefixTokenDeletionLowerNumerator
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : ℕ :=
  tokenDeletionLowerNumerator (k := k)
    (graphOfState (k := k) eN)
    (prefixNonrootDeletionList (k := k) eN.last a ys)

/-- Prefix-specific lower-bound denominator for the non-root deletion problem. -/
def prefixTokenDeletionLowerDenominator
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : ℕ :=
  tokenDeletionLowerDenominator (k := k)
    (graphOfState (k := k) eN)
    (prefixNonrootDeletionList (k := k) eN.last a ys)

/-- Prefix-specific lower factor for the non-root token deletion ratio. -/
def prefixTokenDeletionLowerFactor
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : ℚ :=
  (prefixTokenDeletionLowerNumerator (k := k) a ys eN : ℚ) /
    (prefixTokenDeletionLowerDenominator (k := k) a ys eN : ℚ)

/-- Real-valued version of the prefix-specific lower factor. -/
def prefixTokenDeletionLowerFactorReal
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) : ℝ :=
  (prefixTokenDeletionLowerFactor (k := k) a ys eN : ℝ)

@[simp] lemma prefixTokenDeletionLowerFactorReal_eq_ratCast
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    prefixTokenDeletionLowerFactorReal (k := k) a ys eN =
      (prefixTokenDeletionLowerFactor (k := k) a ys eN : ℝ) := rfl

lemma prefixTokenDeletionLowerNumerator_mul_full_le_denominator_mul_residual
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    prefixTokenDeletionLowerNumerator (k := k) a ys eN *
        tokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) eN) eN.last ≤
      prefixTokenDeletionLowerDenominator (k := k) a ys eN *
        tokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) eN.last := by
  unfold prefixTokenDeletionLowerNumerator prefixTokenDeletionLowerDenominator
  rw [tokenRootedArborescenceCount_residualStateOfPrefix_eq_deleteCopies_prefixNonrootDeletionList]
  exact tokenRootedArborescenceCount_deleteCopies_lower
    (k := k)
    (G := graphOfState (k := k) eN)
    (t := eN.last)
    (ds := prefixNonrootDeletionList (k := k) eN.last a ys)

lemma prefixTokenDeletionLowerNumerator_mul_positiveFull_le_denominator_mul_positiveResidual
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    prefixTokenDeletionLowerNumerator (k := k) a ys eN *
        positiveTokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) eN) eN.last ≤
      prefixTokenDeletionLowerDenominator (k := k) a ys eN *
        positiveTokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) eN.last := by
  unfold prefixTokenDeletionLowerNumerator prefixTokenDeletionLowerDenominator
  rw [positiveTokenRootedArborescenceCount_residualStateOfPrefix_eq_deleteCopies_prefixNonrootDeletionList]
  exact positiveTokenRootedArborescenceCount_deleteCopies_lower
    (k := k)
    (G := graphOfState (k := k) eN)
    (t := eN.last)
    (ds := prefixNonrootDeletionList (k := k) eN.last a ys)

lemma tokenRootedArborescenceCount_residualStateOfPrefix_le
    (a : Fin k) (ys : List (Fin k)) (eN : MarkovState k) :
    tokenRootedArborescenceCount (k := k)
        (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) eN.last ≤
      tokenRootedArborescenceCount (k := k)
        (graphOfState (k := k) eN) eN.last := by
  rw [tokenRootedArborescenceCount_residualStateOfPrefix_eq_deleteCopies_prefixNonrootDeletionList]
  exact tokenRootedArborescenceCount_deleteCopies_le
    (k := k)
    (G := graphOfState (k := k) eN)
    (t := eN.last)
    (ds := prefixNonrootDeletionList (k := k) eN.last a ys)

lemma prefixTokenRootedArborescenceRatio_le_one
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN ≤ 1 := by
  unfold prefixTokenRootedArborescenceRatio
  exact div_le_one_of_le₀
    (by
      exact_mod_cast
        tokenRootedArborescenceCount_residualStateOfPrefix_le
          (k := k) a ys eN)
    (by positivity)

lemma prefixTokenRootedArborescenceRatioReal_le_one
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k) :
    prefixTokenRootedArborescenceRatioReal (k := k) a ys N hN eN ≤ 1 := by
  change ((prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN : ℚ) : ℝ) ≤ (1 : ℝ)
  exact_mod_cast
    (prefixTokenRootedArborescenceRatio_le_one
      (k := k) a ys N hN eN)

lemma prefixTokenDeletionLowerFactor_le_prefixTokenRootedArborescenceRatio_of_prefixCompatibleState_of_bridge
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
          tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    prefixTokenDeletionLowerFactor (k := k) a ys eN ≤
      prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  rcases hcomp with ⟨heN, _, _⟩
  have hfull_ne_zero :
      tokenRootedArborescenceCount (k := k)
        (graphOfState (k := k) eN) eN.last ≠ 0 := by
    intro hzero
    have hcorr_zero : normalizedEulerTrailCorrection (k := k) eN = 0 := by
      simpa [hzero] using (hBridge (M := N) heN)
    exact
      (normalizedEulerTrailCorrection_ne_zero_of_mem_stateFinset
        (k := k) heN) hcorr_zero
  have hfull_pos :
      0 <
        (tokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) eN) eN.last : ℚ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hfull_ne_zero
  by_cases hdenom_zero :
      prefixTokenDeletionLowerDenominator (k := k) a ys eN = 0
  · have hratio_nonneg :
        0 ≤ prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
      unfold prefixTokenRootedArborescenceRatio
      exact div_nonneg (by positivity) (by positivity)
    simpa [prefixTokenDeletionLowerFactor, hdenom_zero] using hratio_nonneg
  · have hdenom_pos :
        0 < (prefixTokenDeletionLowerDenominator (k := k) a ys eN : ℚ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hdenom_zero
    rw [prefixTokenDeletionLowerFactor, prefixTokenRootedArborescenceRatio]
    rw [div_le_div_iff₀ hdenom_pos hfull_pos]
    have hmul :
        ((prefixTokenDeletionLowerNumerator (k := k) a ys eN *
            tokenRootedArborescenceCount (k := k)
              (graphOfState (k := k) eN) eN.last : ℕ) : ℚ) ≤
          ((prefixTokenDeletionLowerDenominator (k := k) a ys eN *
              tokenRootedArborescenceCount (k := k)
                (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) eN.last :
              ℕ) : ℚ) := by
      exact_mod_cast
        (prefixTokenDeletionLowerNumerator_mul_full_le_denominator_mul_residual
          (k := k) a ys eN)
    simpa [residualStateOfPrefix_last, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma prefixTokenDeletionLowerFactor_le_prefixTokenRootedArborescenceRatio_of_prefixCompatibleState_of_bridgeCardEq
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge : tokenRootedBridgeCardEq (k := k) eN) :
    prefixTokenDeletionLowerFactor (k := k) a ys eN ≤
      prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  rcases hcomp with ⟨heN, _, _⟩
  have hfull_ne_zero :
      tokenRootedArborescenceCount (k := k)
        (graphOfState (k := k) eN) eN.last ≠ 0 := by
    intro hzero
    have hcorr_zero : normalizedEulerTrailCorrection (k := k) eN = 0 := by
      simpa [hzero] using
        (normalizedEulerTrailCorrection_eq_tokenRootedArborescenceCount_of_tokenRootedBridgeCardEq
          (k := k) hBridge)
    exact
      (normalizedEulerTrailCorrection_ne_zero_of_mem_stateFinset
        (k := k) heN) hcorr_zero
  have hfull_pos :
      0 <
        (tokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) eN) eN.last : ℚ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hfull_ne_zero
  by_cases hdenom_zero :
      prefixTokenDeletionLowerDenominator (k := k) a ys eN = 0
  · have hratio_nonneg :
        0 ≤ prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
      unfold prefixTokenRootedArborescenceRatio
      exact div_nonneg (by positivity) (by positivity)
    simpa [prefixTokenDeletionLowerFactor, hdenom_zero] using hratio_nonneg
  · have hdenom_pos :
      0 < (prefixTokenDeletionLowerDenominator (k := k) a ys eN : ℚ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hdenom_zero
    rw [prefixTokenDeletionLowerFactor, prefixTokenRootedArborescenceRatio]
    rw [div_le_div_iff₀ hdenom_pos hfull_pos]
    have hmul :
        ((prefixTokenDeletionLowerNumerator (k := k) a ys eN *
            tokenRootedArborescenceCount (k := k)
              (graphOfState (k := k) eN) eN.last : ℕ) : ℚ) ≤
          ((prefixTokenDeletionLowerDenominator (k := k) a ys eN *
              tokenRootedArborescenceCount (k := k)
                (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) eN.last :
              ℕ) : ℚ) := by
      exact_mod_cast
        (prefixTokenDeletionLowerNumerator_mul_full_le_denominator_mul_residual
          (k := k) a ys eN)
    simpa [residualStateOfPrefix_last, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma prefixTokenDeletionLowerFactor_le_prefixTokenRootedArborescenceRatio_of_prefixCompatibleState_of_bridgeCard
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s) :
    prefixTokenDeletionLowerFactor (k := k) a ys eN ≤
      prefixTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  exact
    prefixTokenDeletionLowerFactor_le_prefixTokenRootedArborescenceRatio_of_prefixCompatibleState_of_bridge
      (k := k) a ys N hN eN hcomp
      (fun {_M} {_s} hs =>
        normalizedEulerTrailCorrection_eq_tokenRootedArborescenceCount_of_card_eq
          (k := k) (hBridgeCard hs))

lemma prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_bridge
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    prefixTokenDeletionLowerFactorReal (k := k) a ys eN ≤
      prefixTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  simpa [prefixTokenDeletionLowerFactorReal, prefixTokenRootedArborescenceRatioReal] using
    (prefixTokenDeletionLowerFactor_le_prefixTokenRootedArborescenceRatio_of_prefixCompatibleState_of_bridge
      (k := k) a ys N hN eN hcomp hBridge)

lemma prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_bridgeCard
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s) :
    prefixTokenDeletionLowerFactorReal (k := k) a ys eN ≤
      prefixTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  simpa [prefixTokenDeletionLowerFactorReal, prefixTokenRootedArborescenceRatioReal] using
    (prefixTokenDeletionLowerFactor_le_prefixTokenRootedArborescenceRatio_of_prefixCompatibleState_of_bridgeCard
      (k := k) a ys N hN eN hcomp hBridgeCard)

lemma prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_bridgeCardEq
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge : tokenRootedBridgeCardEq (k := k) eN) :
    prefixTokenDeletionLowerFactorReal (k := k) a ys eN ≤
      prefixTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  simpa [prefixTokenDeletionLowerFactorReal, prefixTokenRootedArborescenceRatioReal] using
    (prefixTokenDeletionLowerFactor_le_prefixTokenRootedArborescenceRatio_of_prefixCompatibleState_of_bridgeCardEq
      (k := k) a ys N hN eN hcomp hBridge)

lemma prefixTokenDeletionLowerFactor_le_prefixPositiveTokenRootedArborescenceRatio_of_prefixCompatibleState_of_positiveBridge
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            positiveTokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    prefixTokenDeletionLowerFactor (k := k) a ys eN ≤
      prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  rcases hcomp with ⟨heN, _, _⟩
  have hfull_ne_zero :
      positiveTokenRootedArborescenceCount (k := k)
        (graphOfState (k := k) eN) eN.last ≠ 0 := by
    intro hzero
    have hcorr_zero : normalizedEulerTrailCorrection (k := k) eN = 0 := by
      simpa [hzero] using (hBridge (M := N) heN)
    exact
      (normalizedEulerTrailCorrection_ne_zero_of_mem_stateFinset
        (k := k) heN) hcorr_zero
  have hfull_pos :
      0 <
        (positiveTokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) eN) eN.last : ℚ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hfull_ne_zero
  by_cases hdenom_zero :
      prefixTokenDeletionLowerDenominator (k := k) a ys eN = 0
  · have hratio_nonneg :
        0 ≤ prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
      unfold prefixPositiveTokenRootedArborescenceRatio
      exact div_nonneg (by positivity) (by positivity)
    simpa [prefixTokenDeletionLowerFactor, hdenom_zero] using hratio_nonneg
  · have hdenom_pos :
        0 < (prefixTokenDeletionLowerDenominator (k := k) a ys eN : ℚ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hdenom_zero
    rw [prefixTokenDeletionLowerFactor, prefixPositiveTokenRootedArborescenceRatio]
    rw [div_le_div_iff₀ hdenom_pos hfull_pos]
    have hmul :
        ((prefixTokenDeletionLowerNumerator (k := k) a ys eN *
            positiveTokenRootedArborescenceCount (k := k)
              (graphOfState (k := k) eN) eN.last : ℕ) : ℚ) ≤
          ((prefixTokenDeletionLowerDenominator (k := k) a ys eN *
              positiveTokenRootedArborescenceCount (k := k)
                (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) eN.last :
              ℕ) : ℚ) := by
      exact_mod_cast
        (prefixTokenDeletionLowerNumerator_mul_positiveFull_le_denominator_mul_positiveResidual
          (k := k) a ys eN)
    simpa [residualStateOfPrefix_last, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma prefixTokenDeletionLowerFactor_le_prefixPositiveTokenRootedArborescenceRatio_of_prefixCompatibleState_of_positiveBridgeCard
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s) :
    prefixTokenDeletionLowerFactor (k := k) a ys eN ≤
      prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  exact
    prefixTokenDeletionLowerFactor_le_prefixPositiveTokenRootedArborescenceRatio_of_prefixCompatibleState_of_positiveBridge
      (k := k) a ys N hN eN hcomp
      (fun {_M} {_s} hs =>
        normalizedEulerTrailCorrection_eq_positiveTokenRootedArborescenceCount_of_positiveTokenRootedBridgeCardEq
          (k := k) (hBridgeCard hs))

lemma prefixTokenDeletionLowerFactor_le_prefixPositiveTokenRootedArborescenceRatio_of_prefixCompatibleState_of_positiveBridgeCardEq
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge : positiveTokenRootedBridgeCardEq (k := k) eN) :
    prefixTokenDeletionLowerFactor (k := k) a ys eN ≤
      prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
  rcases hcomp with ⟨heN, _, _⟩
  have hfull_ne_zero :
      positiveTokenRootedArborescenceCount (k := k)
        (graphOfState (k := k) eN) eN.last ≠ 0 := by
    intro hzero
    have hcorr_zero : normalizedEulerTrailCorrection (k := k) eN = 0 := by
      simpa [hzero] using
        (normalizedEulerTrailCorrection_eq_positiveTokenRootedArborescenceCount_of_positiveTokenRootedBridgeCardEq
          (k := k) hBridge)
    exact
      (normalizedEulerTrailCorrection_ne_zero_of_mem_stateFinset
        (k := k) heN) hcorr_zero
  have hfull_pos :
      0 <
        (positiveTokenRootedArborescenceCount (k := k)
          (graphOfState (k := k) eN) eN.last : ℚ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hfull_ne_zero
  by_cases hdenom_zero :
      prefixTokenDeletionLowerDenominator (k := k) a ys eN = 0
  · have hratio_nonneg :
        0 ≤ prefixPositiveTokenRootedArborescenceRatio (k := k) a ys N hN eN := by
      unfold prefixPositiveTokenRootedArborescenceRatio
      exact div_nonneg (by positivity) (by positivity)
    simpa [prefixTokenDeletionLowerFactor, hdenom_zero] using hratio_nonneg
  · have hdenom_pos :
      0 < (prefixTokenDeletionLowerDenominator (k := k) a ys eN : ℚ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hdenom_zero
    rw [prefixTokenDeletionLowerFactor, prefixPositiveTokenRootedArborescenceRatio]
    rw [div_le_div_iff₀ hdenom_pos hfull_pos]
    have hmul :
        ((prefixTokenDeletionLowerNumerator (k := k) a ys eN *
            positiveTokenRootedArborescenceCount (k := k)
              (graphOfState (k := k) eN) eN.last : ℕ) : ℚ) ≤
          ((prefixTokenDeletionLowerDenominator (k := k) a ys eN *
              positiveTokenRootedArborescenceCount (k := k)
                (graphOfState (k := k) (residualStateOfPrefix (k := k) a ys eN)) eN.last :
              ℕ) : ℚ) := by
      exact_mod_cast
        (prefixTokenDeletionLowerNumerator_mul_positiveFull_le_denominator_mul_positiveResidual
          (k := k) a ys eN)
    simpa [residualStateOfPrefix_last, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma prefixTokenDeletionLowerFactorReal_le_prefixPositiveTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_positiveBridge
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            positiveTokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    prefixTokenDeletionLowerFactorReal (k := k) a ys eN ≤
      prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  simpa [prefixTokenDeletionLowerFactorReal, prefixPositiveTokenRootedArborescenceRatioReal] using
    (prefixTokenDeletionLowerFactor_le_prefixPositiveTokenRootedArborescenceRatio_of_prefixCompatibleState_of_positiveBridge
      (k := k) a ys N hN eN hcomp hBridge)

lemma prefixTokenDeletionLowerFactorReal_le_prefixPositiveTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_positiveBridgeCard
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s) :
    prefixTokenDeletionLowerFactorReal (k := k) a ys eN ≤
      prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  simpa [prefixTokenDeletionLowerFactorReal, prefixPositiveTokenRootedArborescenceRatioReal] using
    (prefixTokenDeletionLowerFactor_le_prefixPositiveTokenRootedArborescenceRatio_of_prefixCompatibleState_of_positiveBridgeCard
      (k := k) a ys N hN eN hcomp hBridgeCard)

lemma prefixTokenDeletionLowerFactorReal_le_prefixPositiveTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_positiveBridgeCardEq
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hcomp : prefixCompatibleState (k := k) a ys N hN eN)
    (hBridge : positiveTokenRootedBridgeCardEq (k := k) eN) :
    prefixTokenDeletionLowerFactorReal (k := k) a ys eN ≤
      prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys N hN eN := by
  simpa [prefixTokenDeletionLowerFactorReal, prefixPositiveTokenRootedArborescenceRatioReal] using
    (prefixTokenDeletionLowerFactor_le_prefixPositiveTokenRootedArborescenceRatio_of_prefixCompatibleState_of_positiveBridgeCardEq
      (k := k) a ys N hN eN hcomp hBridge)

/-- Exact squeeze boundary for the remaining token-rooted stability problem. If
the concrete lower factor tends to `1`, and the token-rooted ratio is
eventually trapped between that lower factor and `1`, then the token-rooted
ratio also tends to `1`. -/
lemma tendsto_prefixTokenRootedArborescenceRatioReal_of_tendsto_prefixTokenDeletionLowerFactorReal
    (a : Fin k) (ys : List (Fin k))
    (N : ℕ → ℕ) (hN : ∀ n, ys.length ≤ N n)
    (e : ℕ → MarkovState k)
    (hlower :
      ∀ᶠ n in Filter.atTop,
        prefixTokenDeletionLowerFactorReal (k := k) a ys (e n) ≤
          prefixTokenRootedArborescenceRatioReal (k := k) a ys (N n) (hN n) (e n))
    (hupper :
      ∀ᶠ n in Filter.atTop,
        prefixTokenRootedArborescenceRatioReal (k := k) a ys (N n) (hN n) (e n) ≤ 1)
    (hlim :
      Filter.Tendsto
        (fun n => prefixTokenDeletionLowerFactorReal (k := k) a ys (e n))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun n => prefixTokenRootedArborescenceRatioReal (k := k) a ys (N n) (hN n) (e n))
      Filter.atTop (nhds (1 : ℝ)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlim tendsto_const_nhds hlower hupper

/-! ## Section 2i: Prefix deletion-factor limits -/

/-- Generic rational lower factor attached to a fixed deletion list. -/
private def tokenDeletionLowerFactorRatAux
    {t : Fin k} (G : EulerGraph k) (ds : List (NonrootVertex t × Fin k)) : ℚ :=
  (tokenDeletionLowerNumerator (k := k) G ds : ℚ) /
    (tokenDeletionLowerDenominator (k := k) G ds : ℚ)

/-- Real-valued version of the generic lower factor for a fixed deletion list. -/
private def tokenDeletionLowerFactorRealAux
    {t : Fin k} (G : EulerGraph k) (ds : List (NonrootVertex t × Fin k)) : ℝ :=
  (tokenDeletionLowerFactorRatAux (k := k) G ds : ℝ)

@[simp] private lemma tokenDeletionLowerFactorRatAux_nil
    {t : Fin k} (G : EulerGraph k) :
    tokenDeletionLowerFactorRatAux (k := k) (t := t) G
      ([] : List (NonrootVertex t × Fin k)) = 1 := by
  simp [tokenDeletionLowerFactorRatAux, tokenDeletionLowerNumerator,
    tokenDeletionLowerDenominator]

@[simp] private lemma tokenDeletionLowerFactorRealAux_nil
    {t : Fin k} (G : EulerGraph k) :
    tokenDeletionLowerFactorRealAux (k := k) (t := t) G
      ([] : List (NonrootVertex t × Fin k)) = 1 := by
  simp [tokenDeletionLowerFactorRealAux, tokenDeletionLowerFactorRatAux_nil]

private lemma tokenDeletionLowerFactorRatAux_cons
    {t : Fin k} (G : EulerGraph k) (u : NonrootVertex t) (v : Fin k)
    (ds : List (NonrootVertex t × Fin k)) :
    tokenDeletionLowerFactorRatAux (k := k) G ((u, v) :: ds) =
      (((G u.1 v - 1 : ℕ) : ℚ) / (G u.1 v : ℚ)) *
        tokenDeletionLowerFactorRatAux (k := k)
          (deleteOneCopy (k := k) G u v) ds := by
  unfold tokenDeletionLowerFactorRatAux
  simp [tokenDeletionLowerNumerator, tokenDeletionLowerDenominator]
  set numTail : ℕ := tokenDeletionLowerNumerator (k := k)
    (deleteOneCopy (k := k) G u v) ds
  set denTail : ℕ := tokenDeletionLowerDenominator (k := k)
    (deleteOneCopy (k := k) G u v) ds
  by_cases hG : G u.1 v = 0
  · simp [hG, numTail, denTail]
  · by_cases hden : denTail = 0
    · simp [hden, numTail, denTail]
    · field_simp [hG, hden]

private lemma tokenDeletionLowerFactorRealAux_cons
    {t : Fin k} (G : EulerGraph k) (u : NonrootVertex t) (v : Fin k)
    (ds : List (NonrootVertex t × Fin k)) :
    tokenDeletionLowerFactorRealAux (k := k) G ((u, v) :: ds) =
      ((((G u.1 v - 1 : ℕ) : ℚ) / (G u.1 v : ℚ) : ℚ) : ℝ) *
        tokenDeletionLowerFactorRealAux (k := k)
          (deleteOneCopy (k := k) G u v) ds := by
  simp [tokenDeletionLowerFactorRealAux, tokenDeletionLowerFactorRatAux_cons,
    Rat.cast_mul]

private lemma tendsto_nat_sub_cast_atTop_of_tendsto_atTop
    {u : ℕ → ℕ} (c : ℕ)
    (hu : Filter.Tendsto (fun n => (u n : ℝ)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => ((u n - c : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro m
  let mNat : ℕ := Nat.ceil m
  have hlarge :
      ∀ᶠ n in Filter.atTop, ((mNat + c : ℕ) : ℝ) ≤ (u n : ℝ) := by
    have hmem : Set.Ici (((mNat + c : ℕ) : ℝ)) ∈ (Filter.atTop : Filter ℝ) := by
      refine Filter.mem_atTop_sets.2 ?_
      exact ⟨((mNat + c : ℕ) : ℝ), fun y hy => hy⟩
    exact hu hmem
  filter_upwards [hlarge] with n hn
  have hnat : mNat + c ≤ u n := by exact_mod_cast hn
  have hsub : mNat ≤ u n - c := by
    omega
  have hmceil : m ≤ (mNat : ℝ) := by
    exact Nat.le_ceil m
  exact le_trans hmceil (by exact_mod_cast hsub)

private lemma tendsto_natcast_atTop_of_pos_ratio
    {u v : ℕ → ℕ} {θ : ℝ}
    (hθ : 0 < θ)
    (hdiv :
      Filter.Tendsto (fun n => (u n : ℝ) / (v n : ℝ))
        Filter.atTop (nhds θ))
    (hv : Filter.Tendsto (fun n => (v n : ℝ)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => (u n : ℝ)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro m
  have hhalf : 0 < θ / 2 := by positivity
  have hratio :
      ∀ᶠ n in Filter.atTop, θ / 2 < (u n : ℝ) / (v n : ℝ) := by
    have hmem : Metric.ball θ (θ / 2) ∈ nhds θ := Metric.ball_mem_nhds _ hhalf
    filter_upwards [hdiv hmem] with n hn
    have habs :
        |(u n : ℝ) / (v n : ℝ) - θ| < θ / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hn
    by_contra hle
    have hnonpos : (u n : ℝ) / (v n : ℝ) - θ ≤ 0 := by linarith
    have hdist' : θ - (u n : ℝ) / (v n : ℝ) < θ / 2 := by
      simpa [abs_of_nonpos hnonpos] using habs
    linarith
  have hvlarge :
      ∀ᶠ n in Filter.atTop, ((2 * m / θ) + 1 : ℝ) ≤ (v n : ℝ) := by
    have hmem : Set.Ici (((2 * m / θ) + 1 : ℝ)) ∈ (Filter.atTop : Filter ℝ) := by
      refine Filter.mem_atTop_sets.2 ?_
      exact ⟨((2 * m / θ) + 1 : ℝ), fun y hy => hy⟩
    exact hv hmem
  filter_upwards [hratio, hvlarge] with n hnRatio hnV
  have hvnonneg : 0 ≤ (v n : ℝ) := by positivity
  have hvpos : 0 < (v n : ℝ) := by
    by_contra hnot
    have hvzero : (v n : ℝ) = 0 := by linarith
    have hratioZero : (u n : ℝ) / (v n : ℝ) = 0 := by simp [hvzero]
    linarith [hnRatio]
  have hmul₁ : (θ / 2) * (v n : ℝ) < (u n : ℝ) := by
    have hvne : (v n : ℝ) ≠ 0 := ne_of_gt hvpos
    have htmp := hnRatio
    field_simp [hvne] at htmp
    nlinarith
  have hmul₂ : (m : ℝ) < (θ / 2) * (v n : ℝ) := by
    have hcalc : (θ / 2) * (((2 * m / θ) + 1 : ℝ)) = m + θ / 2 := by
      field_simp [hθ.ne']
    have htmp :
        m + θ / 2 ≤ (θ / 2) * (v n : ℝ) := by
      rw [← hcalc]
      exact mul_le_mul_of_nonneg_left hnV (by positivity)
    have hm_lt : m < m + θ / 2 := by
      linarith
    exact lt_of_lt_of_le hm_lt htmp
  exact le_of_lt (lt_trans hmul₂ hmul₁)

private lemma tendsto_deleteOneCopy_entry_atTop_of_tendsto_atTop
    {t : Fin k} {G : ℕ → EulerGraph k}
    (u : NonrootVertex t) (v a b : Fin k)
    (hG : Filter.Tendsto (fun n => (G n a b : ℝ)) Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => (deleteOneCopy (k := k) (G n) u v a b : ℝ))
      Filter.atTop Filter.atTop := by
  by_cases hpair : a = u.1 ∧ b = v
  · rcases hpair with ⟨ha, hb⟩
    subst a
    subst b
    simpa [deleteOneCopy_apply_same] using
      tendsto_nat_sub_cast_atTop_of_tendsto_atTop (c := 1) hG
  · have hEq :
      (fun n => (deleteOneCopy (k := k) (G n) u v a b : ℝ)) =ᶠ[Filter.atTop]
        (fun n => (G n a b : ℝ)) := by
      refine Filter.Eventually.of_forall ?_
      intro n
      simp [deleteOneCopy, hpair]
    exact hG.congr' hEq.symm

private lemma tendsto_tokenDeletionLowerFactorRealAux_of_edgeGrowth
    {t : Fin k} (ds : List (NonrootVertex t × Fin k))
    (G : ℕ → EulerGraph k)
    (hgrow :
      ∀ uv : NonrootVertex t × Fin k, uv ∈ ds →
        Filter.Tendsto (fun n => (G n uv.1.1 uv.2 : ℝ))
          Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => tokenDeletionLowerFactorRealAux (k := k) (G n) ds)
      Filter.atTop (nhds (1 : ℝ)) := by
  induction ds generalizing G with
  | nil =>
      simp [tokenDeletionLowerFactorRealAux_nil]
  | cons uv ds ih =>
      rcases uv with ⟨u, v⟩
      have hheadCount :
          Filter.Tendsto (fun n => (G n u.1 v : ℝ)) Filter.atTop Filter.atTop :=
        hgrow (u, v) (by simp)
      have hhead :
          Filter.Tendsto
            (fun n => ((((G n u.1 v - 1 : ℕ) : ℚ) / (G n u.1 v : ℚ) : ℚ) : ℝ))
            Filter.atTop (nhds (1 : ℝ)) := by
        have hself :
            Filter.Tendsto
              (fun n => (G n u.1 v : ℝ) / (G n u.1 v : ℝ))
              Filter.atTop (nhds (1 : ℝ)) :=
          tendsto_self_div_of_tendsto_atTop (v := fun n => G n u.1 v) hheadCount
        simpa using
          tendsto_nat_sub_cast_div_of_div
            (c := 1) (u := fun n => G n u.1 v) (v := fun n => G n u.1 v)
            (θ := (1 : ℝ)) hself hheadCount
      have htailGrow :
          ∀ uv' : NonrootVertex t × Fin k, uv' ∈ ds →
            Filter.Tendsto
              (fun n =>
                (deleteOneCopy (k := k) (G n) u v uv'.1.1 uv'.2 : ℝ))
              Filter.atTop Filter.atTop := by
        intro uv' huv'
        exact tendsto_deleteOneCopy_entry_atTop_of_tendsto_atTop
          (k := k) (u := u) (v := v) (a := uv'.1.1) (b := uv'.2)
          (hgrow uv' (by simp [huv']))
      have htail :
          Filter.Tendsto
            (fun n =>
              tokenDeletionLowerFactorRealAux (k := k)
                (deleteOneCopy (k := k) (G n) u v) ds)
            Filter.atTop (nhds (1 : ℝ)) :=
        ih (G := fun n => deleteOneCopy (k := k) (G n) u v) htailGrow
      have hEq :
          (fun n => tokenDeletionLowerFactorRealAux (k := k) (G n) ((u, v) :: ds)) =ᶠ[Filter.atTop]
            (fun n =>
              ((((G n u.1 v - 1 : ℕ) : ℚ) / (G n u.1 v : ℚ) : ℚ) : ℝ) *
                tokenDeletionLowerFactorRealAux (k := k)
                  (deleteOneCopy (k := k) (G n) u v) ds) := by
        refine Filter.Eventually.of_forall ?_
        intro n
        exact tokenDeletionLowerFactorRealAux_cons (k := k) (G := G n) u v ds
      simpa [one_mul] using (hhead.mul htail).congr' hEq.symm

private lemma tendsto_prefixEdgeCount_atTop_of_pos_ratio
    (a : Fin k) (ys : List (Fin k))
    (e : ℕ → MarkovState k)
    (Θ : Fin k → Fin k → ℝ)
    (hout :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop Filter.atTop)
    (hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun n =>
            ((e n).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop (nhds (Θ i j)))
    (i j : Fin k)
    (hcountPos : 0 < (prefixWordState (k := k) a ys).counts.counts i j)
    (hΘPos : 0 < Θ i j) :
    Filter.Tendsto
      (fun n => ((e n).counts.counts i j : ℝ))
      Filter.atTop Filter.atTop := by
  have hrowPos :
      0 < MarkovDeFinettiHardEuler.outdeg (k := k)
        (prefixWordState (k := k) a ys) i := by
    exact prefixWordState_outdeg_pos_of_count_pos (k := k) a ys i j hcountPos
  exact tendsto_natcast_atTop_of_pos_ratio hΘPos (hratio i j) (hout i hrowPos)

private lemma tendsto_prefixTokenDeletionLowerFactorRealAtRoot_of_edgeGrowth
    (t : Fin k) (a : Fin k) (ys : List (Fin k))
    (e : ℕ → MarkovState k)
    (hcountGrow :
      ∀ i j : Fin k,
        0 < (prefixWordState (k := k) a ys).counts.counts i j →
          Filter.Tendsto
            (fun n => ((e n).counts.counts i j : ℝ))
            Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n =>
        tokenDeletionLowerFactorRealAux (k := k)
          (graphOfState (k := k) (e n))
          (prefixNonrootDeletionList (k := k) t a ys))
      Filter.atTop (nhds (1 : ℝ)) := by
  refine tendsto_tokenDeletionLowerFactorRealAux_of_edgeGrowth
    (k := k)
    (ds := prefixNonrootDeletionList (k := k) t a ys)
    (G := fun n => graphOfState (k := k) (e n)) ?_
  intro uv huv
  have hcountPosList :
      0 < (prefixNonrootDeletionList (k := k) t a ys).count uv := by
    simpa [List.count_pos_iff] using huv
  have hcountPosPrefix :
      0 < (prefixWordState (k := k) a ys).counts.counts uv.1.1 uv.2 := by
    rw [← count_prefixNonrootDeletionList (k := k) t a ys uv.1 uv.2]
    exact hcountPosList
  simpa [graphOfState] using hcountGrow uv.1.1 uv.2 hcountPosPrefix

/-- If every prefix-used edge count tends to infinity, then the concrete
non-root deletion lower factor also tends to `1`. -/
lemma tendsto_prefixTokenDeletionLowerFactorReal_of_edgeGrowth
    (a : Fin k) (ys : List (Fin k))
    (e : ℕ → MarkovState k)
    (hcountGrow :
      ∀ i j : Fin k,
        0 < (prefixWordState (k := k) a ys).counts.counts i j →
          Filter.Tendsto
            (fun n => ((e n).counts.counts i j : ℝ))
            Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => prefixTokenDeletionLowerFactorReal (k := k) a ys (e n))
      Filter.atTop (nhds (1 : ℝ)) := by
  let f : Fin k → ℕ → ℝ := fun t n =>
    tokenDeletionLowerFactorRealAux (k := k)
      (graphOfState (k := k) (e n))
      (prefixNonrootDeletionList (k := k) t a ys)
  have hlimf :
      ∀ t : Fin k, Filter.Tendsto (fun n => f t n) Filter.atTop (nhds (1 : ℝ)) := by
    intro t
    exact tendsto_prefixTokenDeletionLowerFactorRealAtRoot_of_edgeGrowth
      (k := k) t a ys e hcountGrow
  have hsum :
      Filter.Tendsto
        (fun n => ∑ t : Fin k, |f t n - 1|)
        Filter.atTop (nhds (0 : ℝ)) := by
    have hsum' :
        Filter.Tendsto
          (fun n => Finset.sum (Finset.univ : Finset (Fin k)) (fun t => |f t n - 1|))
          Filter.atTop
            (nhds (Finset.sum (Finset.univ : Finset (Fin k)) (fun _ => (0 : ℝ)))) := by
      refine tendsto_finset_sum
        (s := (Finset.univ : Finset (Fin k)))
        (f := fun t n => |f t n - 1|)
        (a := fun _ => (0 : ℝ)) ?_
      intro t ht
      simpa [Real.norm_eq_abs] using
        (((hlimf t).sub
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
            Filter.atTop (nhds (1 : ℝ)))).norm)
    simpa using hsum'
  have hbound :
      ∀ n,
        |prefixTokenDeletionLowerFactorReal (k := k) a ys (e n) - 1| ≤
          ∑ t : Fin k, |f t n - 1| := by
    intro n
    have hmem : (e n).last ∈ (Finset.univ : Finset (Fin k)) := by simp
    have hsingle :
        |f (e n).last n - 1| ≤ ∑ t : Fin k, |f t n - 1| := by
      simpa using
        (Finset.single_le_sum
          (fun t _ => abs_nonneg (f t n - 1))
          hmem)
    have hEq :
        prefixTokenDeletionLowerFactorReal (k := k) a ys (e n) =
          f (e n).last n := by
      simp [f, prefixTokenDeletionLowerFactorReal, prefixTokenDeletionLowerFactor,
        prefixTokenDeletionLowerNumerator, prefixTokenDeletionLowerDenominator,
        tokenDeletionLowerFactorRealAux, tokenDeletionLowerFactorRatAux]
    rw [hEq]
    exact hsingle
  have habs :
      Filter.Tendsto
        (fun n => |prefixTokenDeletionLowerFactorReal (k := k) a ys (e n) - 1|)
        Filter.atTop (nhds (0 : ℝ)) := by
    refine squeeze_zero
      (fun n => abs_nonneg _)
      hbound
      hsum
  have hnorm :
      Filter.Tendsto
        (fun n => ‖prefixTokenDeletionLowerFactorReal (k := k) a ys (e n) - 1‖)
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa [Real.norm_eq_abs] using habs
  exact (tendsto_iff_norm_sub_tendsto_zero).2 hnorm

/-- Prefix-specific version of the lower-factor limit obtained from asymptotic
row-ratio data: if every prefix-used edge has a positive limit ratio, then the
deleted non-root edge counts grow, hence the lower factor tends to `1`. -/
lemma tendsto_prefixTokenDeletionLowerFactorReal_of_ratioData
    (a : Fin k) (ys : List (Fin k))
    (e : ℕ → MarkovState k)
    (Θ : Fin k → Fin k → ℝ)
    (hout :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun n => (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop Filter.atTop)
    (hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun n =>
            ((e n).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i : ℝ))
          Filter.atTop (nhds (Θ i j)))
    (hΘpos :
      ∀ i j : Fin k,
        0 < (prefixWordState (k := k) a ys).counts.counts i j →
          0 < Θ i j) :
    Filter.Tendsto
      (fun n => prefixTokenDeletionLowerFactorReal (k := k) a ys (e n))
      Filter.atTop (nhds (1 : ℝ)) := by
  refine tendsto_prefixTokenDeletionLowerFactorReal_of_edgeGrowth
    (k := k) a ys e ?_
  intro i j hcountPos
  exact tendsto_prefixEdgeCount_atTop_of_pos_ratio
    (k := k) a ys e Θ hout hratio i j hcountPos (hΘpos i j hcountPos)

/-! ## Section 3: Measure Connection -/

/-- Key measure identity: the sum of μ over the constraint subset
equals |subset| * μ(any representative), by Markov exchangeability. -/
lemma sum_mu_fiberWordConstraintSubset_eq_card_mul
    (μ : PrefixMeasure (Fin k)) (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (xs0 : Traj k N)
    (hxs0 : xs0 ∈ fiberWordConstraintSubset (k := k) a ys i c N hN eN) :
    (∑ xs ∈ fiberWordConstraintSubset (k := k) a ys i c N hN eN,
      μ (trajToList (k := k) xs)) =
    ((fiberWordConstraintSubset (k := k) a ys i c N hN eN).card : ENNReal) *
      μ (trajToList (k := k) xs0) :=
  sum_mu_eq_card_mul_of_subset_fiber μ hμ
    (fiberWordConstraintSubset_subset_fiber (k := k) a ys i c N hN eN)
    hxs0

/-- Euler-trail-side cardinality formula for the fiber word-constraint subset. -/
lemma eulerTrailFinset_card_filter_fiberWordConstraintSubset
    (a : Fin k) (ys : List (Fin k)) (i : Fin k)
    (c : Fin (wordAnchorFiberList (k := k) a ys i).length → Fin k)
    (N : ℕ) (hN : ys.length ≤ N) (eN : MarkovState k)
    (hs : eN ∈ stateFinset k N) :
    ((eulerTrailFinset
        (graphOfState eN) eN.start eN.last).filter
      (fun f =>
        castTraj
            (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
            (trailVertexSeq
              (graphOfState eN) eN.start f) ∈
          fiberWordConstraintSubset (k := k) a ys i c N hN eN)).card =
      (fiberWordConstraintSubset (k := k) a ys i c N hN eN).card *
        ∏ a : Fin k, ∏ b : Fin k, (graphOfState eN a b).factorial := by
  have hTok : totalEdgeTokens (k := k) (graphOfState eN) = N :=
    totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs
  subst hTok
  have hA :
      fiberWordConstraintSubset (k := k) a ys i c
          (totalEdgeTokens (k := k) (graphOfState eN)) hN eN ⊆
        fiber k (totalEdgeTokens (k := k) (graphOfState eN)) eN :=
    fiberWordConstraintSubset_subset_fiber
      (k := k) a ys i c (totalEdgeTokens (k := k) (graphOfState eN)) hN eN
  simp only [castTraj]; exact
    eulerTrailFinset_card_filter_trajSubset
      (k := k) (s := eN)
      (A := fiberWordConstraintSubset (k := k) a ys i c
        (totalEdgeTokens (k := k) (graphOfState eN)) hN eN) hA

/-! ## Section 4: Path-Space Expectation Packaging

We now turn the exact finite state-sum identity into a path-space expectation
identity for the prefix-ratio approximants. This is the deterministic measure
bridge needed for the final dominated-convergence step. -/

@[simp] lemma pathPrefixState_mem_stateFinset
    (ω : ℕ → Fin k) (N : ℕ) :
    pathPrefixState (k := k) ω N ∈ stateFinset k N := by
  exact stateOfTraj_mem_stateFinset (k := k) (xs := pathPrefixTraj (k := k) ω N)

/-- The exact finite bridge-cardinality data actually used along one path:
the full path-prefix state and its residual-after-prefix state both satisfy the
token-rooted bridge identity. -/
def pathPrefixBridgeCardEqPair
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (r : ℕ) : Prop :=
  tokenRootedBridgeCardEq (k := k)
      (pathPrefixState (k := k) ω (ys.length + r)) ∧
    tokenRootedBridgeCardEq (k := k)
      (residualStateOfPrefix (k := k) a ys
        (pathPrefixState (k := k) ω (ys.length + r)))

/-- Support-local exact finite bridge-cardinality data actually used along one
path: the full path-prefix state and its residual-after-prefix state both
satisfy the support-local rooted-arborescence bridge identity. -/
def pathPrefixPositiveBridgeCardEqPair
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (r : ℕ) : Prop :=
  positiveTokenRootedBridgeCardEq (k := k)
      (pathPrefixState (k := k) ω (ys.length + r)) ∧
    positiveTokenRootedBridgeCardEq (k := k)
      (residualStateOfPrefix (k := k) a ys
        (pathPrefixState (k := k) ω (ys.length + r)))

lemma pathPrefixBridgeCardEqPair_of_globalBridgeCard_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (r : ℕ)
    (hcomp :
      prefixCompatibleState (k := k) a ys (ys.length + r)
        (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          tokenRootedBridgeCardEq (k := k) s) :
    pathPrefixBridgeCardEqPair (k := k) a ys ω r := by
  rcases hcomp with ⟨_, _, hres⟩
  constructor
  · exact hBridgeCard (pathPrefixState_mem_stateFinset (k := k) ω (ys.length + r))
  · exact hBridgeCard hres

lemma ae_eventually_pathPrefixBridgeCardEqPair_of_globalBridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          tokenRootedBridgeCardEq (k := k) s) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop, pathPrefixBridgeCardEqPair (k := k) a ys ω r := by
  filter_upwards [hcomp] with ω hcompω hstart
  filter_upwards [hcompω hstart] with r hr
  exact
    pathPrefixBridgeCardEqPair_of_globalBridgeCard_of_prefixCompatibleState
      (k := k) a ys ω r hr hBridgeCard

lemma pathPrefixPositiveBridgeCardEqPair_of_globalPositiveBridgeCard_of_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (r : ℕ)
    (hcomp :
      prefixCompatibleState (k := k) a ys (ys.length + r)
        (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s) :
    pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r := by
  rcases hcomp with ⟨_, _, hres⟩
  constructor
  · exact hBridgeCard (pathPrefixState_mem_stateFinset (k := k) ω (ys.length + r))
  · exact hBridgeCard hres

lemma ae_eventually_pathPrefixPositiveBridgeCardEqPair_of_globalPositiveBridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop, pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r := by
  filter_upwards [hcomp] with ω hcompω hstart
  filter_upwards [hcompω hstart] with r hr
  exact
    pathPrefixPositiveBridgeCardEqPair_of_globalPositiveBridgeCard_of_prefixCompatibleState
      (k := k) a ys ω r hr hBridgeCard

lemma pathPrefixBridgeCardEqPair_of_pathPrefixPositiveBridgeCardEqPair_of_prefixCompatibleState_of_forall_outdeg_gt_prefixWordState_outdeg
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (r : ℕ)
    (hcomp :
      prefixCompatibleState (k := k) a ys (ys.length + r)
        (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)))
    (hgt :
      ∀ i : Fin k,
        MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i <
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (ys.length + r)) i)
    (hBridgePos :
      pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r) :
    pathPrefixBridgeCardEqPair (k := k) a ys ω r := by
  rcases hBridgePos with ⟨hfullPos, hresPos⟩
  constructor
  · exact
      tokenRootedBridgeCardEq_of_positiveTokenRootedBridgeCardEq_of_forall_pos
        (k := k) hfullPos
        (hpos := by
          intro u
          exact lt_of_le_of_lt (Nat.zero_le _) (hgt u.1))
  · exact
      tokenRootedBridgeCardEq_of_positiveTokenRootedBridgeCardEq_of_forall_pos
        (k := k) hresPos
        (hpos := by
          intro u
          rw [residualStateOfPrefix_outdeg
            (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)) hcomp u.1]
          exact Nat.sub_pos_of_lt (hgt u.1))

lemma pathPrefixPositiveBridgeCardEqPair_of_pathPrefixBridgeCardEqPair_of_prefixCompatibleState_of_forall_outdeg_gt_prefixWordState_outdeg
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (r : ℕ)
    (hcomp :
      prefixCompatibleState (k := k) a ys (ys.length + r)
        (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)))
    (hgt :
      ∀ i : Fin k,
        MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i <
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (ys.length + r)) i)
    (hBridge :
      pathPrefixBridgeCardEqPair (k := k) a ys ω r) :
    pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r := by
  rcases hBridge with ⟨hfull, hres⟩
  constructor
  · exact
      positiveTokenRootedBridgeCardEq_of_tokenRootedBridgeCardEq_of_forall_pos
        (k := k) hfull
        (hpos := by
          intro u
          exact lt_of_le_of_lt (Nat.zero_le _) (hgt u.1))
  · exact
      positiveTokenRootedBridgeCardEq_of_tokenRootedBridgeCardEq_of_forall_pos
        (k := k) hres
        (hpos := by
          intro u
          rw [residualStateOfPrefix_outdeg
            (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)) hcomp u.1]
          exact Nat.sub_pos_of_lt (hgt u.1))

lemma pathPrefixPositiveBridgeCardEqPair_iff_pathPrefixBridgeCardEqPair_of_prefixCompatibleState_of_forall_outdeg_gt_prefixWordState_outdeg
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (r : ℕ)
    (hcomp :
      prefixCompatibleState (k := k) a ys (ys.length + r)
        (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)))
    (hgt :
      ∀ i : Fin k,
        MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i <
          MarkovDeFinettiHardEuler.outdeg (k := k)
            (pathPrefixState (k := k) ω (ys.length + r)) i) :
    pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r ↔
      pathPrefixBridgeCardEqPair (k := k) a ys ω r := by
  constructor
  · intro hBridgePos
    exact
      pathPrefixBridgeCardEqPair_of_pathPrefixPositiveBridgeCardEqPair_of_prefixCompatibleState_of_forall_outdeg_gt_prefixWordState_outdeg
        (k := k) a ys ω r hcomp hgt hBridgePos
  · intro hBridge
    exact
      pathPrefixPositiveBridgeCardEqPair_of_pathPrefixBridgeCardEqPair_of_prefixCompatibleState_of_forall_outdeg_gt_prefixWordState_outdeg
        (k := k) a ys ω r hcomp hgt hBridge

lemma ae_eventually_pathPrefixBridgeCardEqPair_of_globalPositiveBridgeCard_of_eventually_prefixCompatibleState_of_ae_tendsto_outdeg
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s)
    (hout :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω (ys.length + r)) i)
              Filter.atTop Filter.atTop) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop, pathPrefixBridgeCardEqPair (k := k) a ys ω r := by
  have hBridgePos :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop, pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r :=
    ae_eventually_pathPrefixPositiveBridgeCardEqPair_of_globalPositiveBridgeCard_of_eventually_prefixCompatibleState
      (k := k) P a ys hcomp hBridgeCard
  have houtAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k,
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω (ys.length + r)) i)
              Filter.atTop Filter.atTop := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k,
            ω 0 = a →
              Filter.Tendsto
                (fun r =>
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (pathPrefixState (k := k) ω (ys.length + r)) i)
                Filter.atTop Filter.atTop := by
      rw [ae_all_iff]
      intro i
      exact hout i
    filter_upwards [hpack] with ω hω hstart i
    exact hω i hstart
  filter_upwards [hcomp, hBridgePos, houtAll] with ω hcompω hBridgePosω houtω hstart
  have hgt :
      ∀ᶠ r in Filter.atTop,
        ∀ i : Fin k,
          MarkovDeFinettiHardEuler.outdeg (k := k)
              (prefixWordState (k := k) a ys) i <
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i := by
    rw [Filter.eventually_all]
    intro i
    have hmem :
        Set.Ici
          (MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i + 1) ∈
          (Filter.atTop : Filter ℕ) := by
      exact Filter.mem_atTop_sets.2
        ⟨MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i + 1,
          fun b hb => hb⟩
    filter_upwards [houtω hstart i hmem] with r hr
    exact lt_of_lt_of_le (Nat.lt_succ_self _) hr
  filter_upwards [hcompω hstart, hBridgePosω hstart, hgt] with r hrcomp hrBridgePos hrgt
  exact
    pathPrefixBridgeCardEqPair_of_pathPrefixPositiveBridgeCardEqPair_of_prefixCompatibleState_of_forall_outdeg_gt_prefixWordState_outdeg
      (k := k) a ys ω r hrcomp hrgt hrBridgePos

lemma ae_eventually_pathPrefixBridgeCardEqPair_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState_of_ae_tendsto_outdeg
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgePos :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop, pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r)
    (hout :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω (ys.length + r)) i)
              Filter.atTop Filter.atTop) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop, pathPrefixBridgeCardEqPair (k := k) a ys ω r := by
  have houtAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k,
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω (ys.length + r)) i)
              Filter.atTop Filter.atTop := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k,
            ω 0 = a →
              Filter.Tendsto
                (fun r =>
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (pathPrefixState (k := k) ω (ys.length + r)) i)
                Filter.atTop Filter.atTop := by
      rw [ae_all_iff]
      intro i
      exact hout i
    filter_upwards [hpack] with ω hω hstart i
    exact hω i hstart
  filter_upwards [hcomp, hBridgePos, houtAll] with ω hcompω hBridgePosω houtω hstart
  have hgt :
      ∀ᶠ r in Filter.atTop,
        ∀ i : Fin k,
          MarkovDeFinettiHardEuler.outdeg (k := k)
              (prefixWordState (k := k) a ys) i <
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i := by
    rw [Filter.eventually_all]
    intro i
    have hmem :
        Set.Ici
          (MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i + 1) ∈
          (Filter.atTop : Filter ℕ) := by
      exact Filter.mem_atTop_sets.2
        ⟨MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i + 1,
          fun b hb => hb⟩
    filter_upwards [houtω hstart i hmem] with r hr
    exact lt_of_lt_of_le (Nat.lt_succ_self _) hr
  filter_upwards [hcompω hstart, hBridgePosω hstart, hgt] with r hrcomp hrBridgePos hrgt
  exact
    pathPrefixBridgeCardEqPair_of_pathPrefixPositiveBridgeCardEqPair_of_prefixCompatibleState_of_forall_outdeg_gt_prefixWordState_outdeg
      (k := k) a ys ω r hrcomp hrgt hrBridgePos

lemma ae_eventually_pathPrefixPositiveBridgeCardEqPair_of_globalBridgeCard_of_eventually_prefixCompatibleState_of_ae_tendsto_outdeg
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          tokenRootedBridgeCardEq (k := k) s)
    (hout :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω (ys.length + r)) i)
              Filter.atTop Filter.atTop) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop, pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r := by
  have hBridge :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop, pathPrefixBridgeCardEqPair (k := k) a ys ω r :=
    ae_eventually_pathPrefixBridgeCardEqPair_of_globalBridgeCard_of_eventually_prefixCompatibleState
      (k := k) P a ys hcomp hBridgeCard
  have houtAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k,
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω (ys.length + r)) i)
              Filter.atTop Filter.atTop := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k,
            ω 0 = a →
              Filter.Tendsto
                (fun r =>
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (pathPrefixState (k := k) ω (ys.length + r)) i)
                Filter.atTop Filter.atTop := by
      rw [ae_all_iff]
      intro i
      exact hout i
    filter_upwards [hpack] with ω hω hstart i
    exact hω i hstart
  filter_upwards [hcomp, hBridge, houtAll] with ω hcompω hBridgeω houtω hstart
  have hgt :
      ∀ᶠ r in Filter.atTop,
        ∀ i : Fin k,
          MarkovDeFinettiHardEuler.outdeg (k := k)
              (prefixWordState (k := k) a ys) i <
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i := by
    rw [Filter.eventually_all]
    intro i
    have hmem :
        Set.Ici
          (MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i + 1) ∈
          (Filter.atTop : Filter ℕ) := by
      exact Filter.mem_atTop_sets.2
        ⟨MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i + 1,
          fun b hb => hb⟩
    filter_upwards [houtω hstart i hmem] with r hr
    exact lt_of_lt_of_le (Nat.lt_succ_self _) hr
  filter_upwards [hcompω hstart, hBridgeω hstart, hgt] with r hrcomp hrBridge hrgt
  exact
    pathPrefixPositiveBridgeCardEqPair_of_pathPrefixBridgeCardEqPair_of_prefixCompatibleState_of_forall_outdeg_gt_prefixWordState_outdeg
      (k := k) a ys ω r hrcomp hrgt hrBridge

lemma eventually_forall_outdeg_gt_prefixWordState_outdeg_of_tendsto
    (a : Fin k) (ys : List (Fin k))
    (e : ℕ → MarkovState k)
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun n => MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i)
          Filter.atTop Filter.atTop) :
    ∀ᶠ n in Filter.atTop,
      ∀ i : Fin k,
        MarkovDeFinettiHardEuler.outdeg (k := k)
            (prefixWordState (k := k) a ys) i <
          MarkovDeFinettiHardEuler.outdeg (k := k) (e n) i := by
  rw [Filter.eventually_all]
  intro i
  have hmem :
      Set.Ici
        (MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i + 1) ∈
        (Filter.atTop : Filter ℕ) := by
    exact Filter.mem_atTop_sets.2
      ⟨MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i + 1,
        fun b hb => hb⟩
  filter_upwards [hout i hmem] with n hn
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hn

lemma eventually_eq_prefixPositiveTokenRootedArborescenceRatioReal_of_prefixTokenRootedArborescenceRatioReal_of_eventually_prefixCompatibleState_of_eventually_forall_outdeg_gt_prefixWordState_outdeg
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k)
    (hcomp :
      ∀ᶠ r in Filter.atTop,
        prefixCompatibleState (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)))
    (hgt :
      ∀ᶠ r in Filter.atTop,
        ∀ i : Fin k,
          MarkovDeFinettiHardEuler.outdeg (k := k)
              (prefixWordState (k := k) a ys) i <
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i) :
    (fun r =>
      prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys
        (ys.length + r) (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r))) =ᶠ[Filter.atTop]
      (fun r =>
        prefixTokenRootedArborescenceRatioReal (k := k) a ys
          (ys.length + r) (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r))) := by
  filter_upwards [hcomp, hgt] with r hcomp_r hgt_r
  exact
    prefixPositiveTokenRootedArborescenceRatioReal_eq_prefixTokenRootedArborescenceRatioReal_of_forall_pos
      (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r)
      (pathPrefixState (k := k) ω (ys.length + r))
      (hres := by
        intro u
        rw [residualStateOfPrefix_outdeg
          (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)) hcomp_r u.1]
        exact Nat.sub_pos_of_lt (hgt_r u.1))
      (hfull := by
        intro u
        exact lt_of_le_of_lt (Nat.zero_le _) (hgt_r u.1))

lemma pairwiseDisjoint_cylinder_on_trajSet
    {N : ℕ} (A : Finset (Traj k N)) :
    Set.PairwiseDisjoint (↑A : Set (Traj k N))
      (fun xs => MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs)) := by
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

/-- The event that the first `N + 1` coordinates of `ω` have evidence state
`eN`. -/
def pathPrefixStateEvent
    (N : ℕ) (eN : MarkovState k) : Set (ℕ → Fin k) :=
  {ω : ℕ → Fin k | pathPrefixState (k := k) ω N = eN}

lemma mem_pathPrefixStateEvent_iff
    (ω : ℕ → Fin k) (N : ℕ) (eN : MarkovState k) :
    ω ∈ pathPrefixStateEvent (k := k) N eN ↔
      pathPrefixState (k := k) ω N = eN := by
  rfl

lemma pathPrefixStateEvent_eq_biUnion_fiber_cylinders
    (N : ℕ) (eN : MarkovState k) :
    pathPrefixStateEvent (k := k) N eN =
      ⋃ xs ∈ fiber k N eN,
        MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs) := by
  ext ω
  constructor
  · intro hω
    refine Set.mem_iUnion.2 ?_
    refine ⟨pathPrefixTraj (k := k) ω N, ?_⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨?_, ?_⟩
    · refine Finset.mem_filter.2 ?_
      refine ⟨by simp [trajFinset], ?_⟩
      exact hω
    · exact (mem_cylinder_ofFn_iff (k := k) ω N (pathPrefixTraj (k := k) ω N)).2
        (fun j => rfl)
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨xs, hω⟩
    rcases Set.mem_iUnion.1 hω with ⟨hxs, hωxs⟩
    have hprefix : pathPrefixTraj (k := k) ω N = xs := by
      funext j
      exact (mem_cylinder_ofFn_iff (k := k) ω N xs).1 hωxs j
    have hstate : stateOfTraj (k := k) xs = eN := (Finset.mem_filter.1 hxs).2
    have hstate' : pathPrefixState (k := k) ω N = eN := by
      simpa [pathPrefixState, hprefix] using hstate
    exact hstate'

lemma measurableSet_pathPrefixStateEvent
    (N : ℕ) (eN : MarkovState k) :
    MeasurableSet (pathPrefixStateEvent (k := k) N eN) := by
  rw [pathPrefixStateEvent_eq_biUnion_fiber_cylinders]
  exact Finset.measurableSet_biUnion _ (fun xs hxs =>
    measurableSet_cylinder (k := k) (trajToList (k := k) xs))

lemma measure_pathPrefixStateEvent_eq_stateMass
    (μ : PrefixMeasure (Fin k))
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k),
      μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (N : ℕ) (eN : MarkovState k) :
    P (pathPrefixStateEvent (k := k) N eN) =
      stateMass (k := k) μ N eN := by
  rw [pathPrefixStateEvent_eq_biUnion_fiber_cylinders]
  rw [measure_biUnion_finset
      (μ := P)
      (s := fiber k N eN)
      (f := fun xs =>
        MarkovDeFinettiRecurrence.cylinder (k := k) (trajToList (k := k) xs))]
  · refine Finset.sum_congr rfl ?_
    intro xs hxs
    exact (hExt (trajToList (k := k) xs)).symm
  · exact pairwiseDisjoint_cylinder_on_trajSet (k := k) (A := fiber k N eN)
  · intro xs hxs
    exact measurableSet_cylinder (k := k) (trajToList (k := k) xs)

/-- The ENNReal-valued finite prefix-ratio approximant at horizon `|ys| + r`. -/
def prefixRatioApproxENN
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) (ω : ℕ → Fin k) : ENNReal :=
  ENNReal.ofReal
    (prefixRatioFnReal (k := k) a ys (ys.length + r)
      (Nat.le_add_right ys.length r)
      (pathPrefixState (k := k) ω (ys.length + r)))

@[simp] lemma prefixRatioApproxENN_eq
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) (ω : ℕ → Fin k) :
    prefixRatioApproxENN (k := k) a ys r ω =
      ENNReal.ofReal
        (prefixRatioFnReal (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r))) := rfl

lemma prefixRatioApproxENN_eq_sum_stateIndicators
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) (ω : ℕ → Fin k) :
    prefixRatioApproxENN (k := k) a ys r ω =
      ∑ eN ∈ stateFinset k (ys.length + r),
        ENNReal.ofReal
            (prefixRatioFnReal (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r) eN) *
          Set.indicator
            (pathPrefixStateEvent (k := k) (ys.length + r) eN)
            (fun _ : ℕ → Fin k => (1 : ENNReal)) ω := by
  let eω : MarkovState k := pathPrefixState (k := k) ω (ys.length + r)
  have heω : eω ∈ stateFinset k (ys.length + r) := by
    exact pathPrefixState_mem_stateFinset (k := k) ω (ys.length + r)
  have hsingle :
      ∑ eN ∈ stateFinset k (ys.length + r),
        ENNReal.ofReal
            (prefixRatioFnReal (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r) eN) *
          Set.indicator
            (pathPrefixStateEvent (k := k) (ys.length + r) eN)
            (fun _ : ℕ → Fin k => (1 : ENNReal)) ω
        =
      ENNReal.ofReal
          (prefixRatioFnReal (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r) eω) *
        Set.indicator
          (pathPrefixStateEvent (k := k) (ys.length + r) eω)
          (fun _ : ℕ → Fin k => (1 : ENNReal)) ω := by
    refine Finset.sum_eq_single_of_mem eω heω ?_
    intro eN heN hne
    have hnot : ¬ pathPrefixState (k := k) ω (ys.length + r) = eN := by
      simpa [eω] using hne.symm
    simp [pathPrefixStateEvent, hnot]
  rw [hsingle]
  simp [prefixRatioApproxENN, pathPrefixStateEvent, eω]

lemma measurable_prefixRatioApproxENN
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) :
    Measurable (prefixRatioApproxENN (k := k) a ys r) := by
  classical
  have hEq :
      prefixRatioApproxENN (k := k) a ys r =
        fun ω =>
          ∑ eN ∈ stateFinset k (ys.length + r),
            ENNReal.ofReal
                (prefixRatioFnReal (k := k) a ys (ys.length + r)
                  (Nat.le_add_right ys.length r) eN) *
              Set.indicator
                (pathPrefixStateEvent (k := k) (ys.length + r) eN)
                (fun _ : ℕ → Fin k => (1 : ENNReal)) ω := by
    funext ω
    exact prefixRatioApproxENN_eq_sum_stateIndicators (k := k) a ys r ω
  rw [hEq]
  refine Finset.measurable_sum _ ?_
  intro eN heN
  have hind :
      Measurable
        (Set.indicator
          (pathPrefixStateEvent (k := k) (ys.length + r) eN)
          (fun _ : ℕ → Fin k => (1 : ENNReal))) :=
    measurable_const.indicator
      (measurableSet_pathPrefixStateEvent (k := k) (ys.length + r) eN)
  exact measurable_const.mul hind

lemma aemeasurable_prefixRatioApproxENN
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) :
    AEMeasurable (prefixRatioApproxENN (k := k) a ys r) P :=
  (measurable_prefixRatioApproxENN (k := k) a ys r).aemeasurable

lemma prefixRatioApproxENN_le_one
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) (ω : ℕ → Fin k) :
    prefixRatioApproxENN (k := k) a ys r ω ≤ 1 := by
  let eω : MarkovState k := pathPrefixState (k := k) ω (ys.length + r)
  have heω : eω ∈ stateFinset k (ys.length + r) := by
    exact pathPrefixState_mem_stateFinset (k := k) ω (ys.length + r)
  have hratio :
      prefixRatioApproxENN (k := k) a ys r ω =
        ((fiberPrefixSubset (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r) eω).card : ENNReal) /
          (fiber k (ys.length + r) eω).card := by
    simpa [prefixRatioApproxENN, prefixRatioFnReal_eq_ratCast, eω] using
      ennreal_ofReal_prefixRatioFn_eq_card_ratio
        (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r) eω
  have hcard_le :
      ((fiberPrefixSubset (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r) eω).card : ENNReal) ≤
        (fiber k (ys.length + r) eω).card := by
    exact_mod_cast Finset.card_le_card
      (fiberPrefixSubset_subset_fiber
        (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r) eω)
  have hfiber_ne_zero :
      (fiber k (ys.length + r) eω).card ≠ 0 := by
    exact fiber_card_ne_zero_of_mem_stateFinset
      (k := k) (N := ys.length + r) (eN := eω) heω
  have hfiber_ne_zero' :
      ((fiber k (ys.length + r) eω).card : ENNReal) ≠ 0 := by
    exact_mod_cast hfiber_ne_zero
  rw [hratio]
  have hself :
      ((fiber k (ys.length + r) eω).card : ENNReal) /
          (fiber k (ys.length + r) eω).card = 1 := by
    simpa using
      (ENNReal.div_self hfiber_ne_zero' ENNReal.coe_ne_top :
        ((fiber k (ys.length + r) eω).card : ENNReal) /
            (fiber k (ys.length + r) eω).card = 1)
  calc
    ((fiberPrefixSubset (k := k) a ys (ys.length + r)
        (Nat.le_add_right ys.length r) eω).card : ENNReal) /
      (fiber k (ys.length + r) eω).card
        ≤ ((fiber k (ys.length + r) eω).card : ENNReal) /
            (fiber k (ys.length + r) eω).card :=
          ENNReal.div_le_div_right hcard_le ((fiber k (ys.length + r) eω).card)
    _ = 1 := hself

lemma lintegral_prefixRatioApproxENN_eq_prefix
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k),
      μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) :
    ∫⁻ ω, prefixRatioApproxENN (k := k) a ys r ω ∂P = μ (a :: ys) := by
  classical
  calc
    ∫⁻ ω, prefixRatioApproxENN (k := k) a ys r ω ∂P
        =
      ∫⁻ ω,
        ∑ eN ∈ stateFinset k (ys.length + r),
          ENNReal.ofReal
              (prefixRatioFnReal (k := k) a ys (ys.length + r)
                (Nat.le_add_right ys.length r) eN) *
            Set.indicator
              (pathPrefixStateEvent (k := k) (ys.length + r) eN)
              (fun _ : ℕ → Fin k => (1 : ENNReal)) ω ∂P := by
            refine lintegral_congr_ae ?_
            exact Filter.Eventually.of_forall
              (fun ω => prefixRatioApproxENN_eq_sum_stateIndicators (k := k) a ys r ω)
    _ =
      ∑ eN ∈ stateFinset k (ys.length + r),
        ENNReal.ofReal
            (prefixRatioFnReal (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r) eN) *
          P (pathPrefixStateEvent (k := k) (ys.length + r) eN) := by
            rw [MeasureTheory.lintegral_finset_sum]
            · refine Finset.sum_congr rfl ?_
              intro eN heN
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              rw [lintegral_indicator
                (measurableSet_pathPrefixStateEvent (k := k) (ys.length + r) eN)]
              simp
            · intro eN heN
              exact (measurable_const.mul
                ((measurable_const.indicator
                  (measurableSet_pathPrefixStateEvent (k := k) (ys.length + r) eN))))
    _ =
      ∑ eN ∈ stateFinset k (ys.length + r),
        ENNReal.ofReal
            (prefixRatioFn (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r) eN) *
          stateMass (k := k) μ (ys.length + r) eN := by
            refine Finset.sum_congr rfl ?_
            intro eN heN
            rw [measure_pathPrefixStateEvent_eq_stateMass
              (k := k) (μ := μ) (P := P) hExt (ys.length + r) eN]
            rw [prefixRatioFnReal_eq_ratCast]
    _ = μ (a :: ys) :=
      sum_stateMass_mul_prefixRatioFn_eq_prefix_aux
        (k := k) μ hμ a ys r

lemma tendsto_lintegral_prefixRatioApproxENN
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k),
      μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (a : Fin k) (ys : List (Fin k)) :
    Filter.Tendsto
      (fun r => ∫⁻ ω, prefixRatioApproxENN (k := k) a ys r ω ∂P)
      Filter.atTop (nhds (μ (a :: ys))) := by
  have hconst :
      (fun r => ∫⁻ ω, prefixRatioApproxENN (k := k) a ys r ω ∂P) =
        fun _ : ℕ => μ (a :: ys) := by
    funext r
    exact lintegral_prefixRatioApproxENN_eq_prefix
      (k := k) (μ := μ) hμ P hExt a ys r
  rw [hconst]
  exact tendsto_const_nhds

lemma prefixRatioApproxENN_eq_zero_of_start_ne
    (a : Fin k) (ys : List (Fin k))
    (r : ℕ) (ω : ℕ → Fin k)
    (hstart : ω 0 ≠ a) :
    prefixRatioApproxENN (k := k) a ys r ω = 0 := by
  unfold prefixRatioApproxENN
  rw [prefixRatioFnReal_eq_ratCast]
  have hnot :
      ¬ prefixCompatibleState (k := k) a ys (ys.length + r)
        (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)) := by
    intro hcomp
    exact hstart (by simpa using hcomp.2.1)
  rw [prefixRatioFn_eq_zero_of_not_prefixCompatibleState (k := k)
    (a := a) (ys := ys) (N := ys.length + r)
    (hN := Nat.le_add_right ys.length r)
    (eN := pathPrefixState (k := k) ω (ys.length + r)) hnot]
  simp

lemma prefixCompatibleState_of_mem_stateFinset_of_start_eq_of_counts_le_of_pos_prefixNormalizedEulerTrailCorrectionRatioReal
    (a : Fin k) (ys : List (Fin k))
    {N : ℕ} (hN : ys.length ≤ N) {eN : MarkovState k}
    (heN : eN ∈ stateFinset k N)
    (hstart : eN.start = a)
    (hle : ∀ i j : Fin k,
      (prefixWordState (k := k) a ys).counts.counts i j ≤ eN.counts.counts i j)
    (hgraphPos :
      0 < prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys N hN eN) :
    prefixCompatibleState (k := k) a ys N hN eN := by
  let s := residualStateOfPrefix (k := k) a ys eN
  have hs_ne_zero : normalizedEulerTrailCorrection (k := k) s ≠ 0 := by
    intro hs_zero
    have hratio_zero :
        prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys N hN eN = 0 := by
      simp [prefixNormalizedEulerTrailCorrectionRatioReal,
        prefixNormalizedEulerTrailCorrectionRatio, s, hs_zero]
    exact (ne_of_gt hgraphPos) hratio_zero
  have hs_card_ne_zero :
      (eulerTrailFinset (graphOfState s) s.start s.last).card ≠ 0 := by
    intro hs_card_zero
    apply hs_ne_zero
    simp [normalizedEulerTrailCorrection, hs_card_zero]
  rcases Finset.card_ne_zero.1 hs_card_ne_zero with ⟨f, hf_mem⟩
  rw [mem_eulerTrailFinset] at hf_mem
  have hTok :
      totalEdgeTokens (k := k) (graphOfState (k := k) s) = N - ys.length :=
    totalEdgeTokens_graphOfState_residualStateOfPrefix_eq_of_counts_le
      (k := k) (a := a) (ys := ys) (N := N) hN heN hle
  let xs : Traj k (N - ys.length) :=
    castTraj hTok (trailVertexSeq (graphOfState s) s.start f)
  have htrail_state :
      stateOfTraj (k := k) (trailVertexSeq (graphOfState s) s.start f) = s := by
    exact (Finset.mem_filter.1 (trailVertexSeq_mem_fiber (k := k) hf_mem)).2
  have hxs_state : stateOfTraj (k := k) xs = s := by
    dsimp [xs]
    rw [stateOfTraj_castTraj]
    simpa [hTok] using htrail_state
  refine ⟨heN, hstart, ?_⟩
  simpa [hxs_state] using stateOfTraj_mem_stateFinset (k := k) (xs := xs)

lemma eventually_prefixCompatibleState_pathPrefixState_of_start_eq_of_edgeGrowth_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k)
    (hstart : ω 0 = a)
    (hcountGrow :
      ∀ i j : Fin k,
        0 < (prefixWordState (k := k) a ys).counts.counts i j →
          Filter.Tendsto
            (fun r =>
              ((pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j : ℝ))
            Filter.atTop Filter.atTop)
    (hgraph :
      Filter.Tendsto
        (fun r =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop (nhds (1 : ℝ))) :
    ∀ᶠ r in Filter.atTop,
      prefixCompatibleState (k := k) a ys (ys.length + r)
        (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)) := by
  have hcounts_le :
      ∀ᶠ r in Filter.atTop,
        ∀ p ∈ (Finset.univ : Finset (Fin k × Fin k)),
          (prefixWordState (k := k) a ys).counts.counts p.1 p.2 ≤
            (pathPrefixState (k := k) ω (ys.length + r)).counts.counts p.1 p.2 := by
    rw [Finset.eventually_all]
    intro p hp
    rcases p with ⟨i, j⟩
    by_cases hpos : 0 < (prefixWordState (k := k) a ys).counts.counts i j
    · have hlarge :=
          hcountGrow i j hpos
            (Filter.mem_atTop_sets.2
              ⟨((prefixWordState (k := k) a ys).counts.counts i j : ℝ),
                fun x hx => hx⟩)
      filter_upwards [hlarge] with r hr
      have hr' :
          ((prefixWordState (k := k) a ys).counts.counts i j : ℝ) ≤
            ((pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j : ℝ) := by
        have hr'' := hr
        change ((prefixWordState (k := k) a ys).counts.counts i j : ℝ) ≤
          ((pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j : ℝ) at hr''
        exact hr''
      exact_mod_cast hr'
    · have hzero :
          (prefixWordState (k := k) a ys).counts.counts i j = 0 :=
        Nat.eq_zero_of_not_pos hpos
      exact Filter.Eventually.of_forall (fun r => by
        have hzeroTraj : transCount (wordTraj (k := k) a ys) i j = 0 := by
          simpa [prefixWordState, stateOfTraj, countsOfFn] using hzero
        have hzeroState :
            (stateOfTraj (k := k) (wordTraj (k := k) a ys)).counts.counts i j = 0 := by
          simpa [stateOfTraj, countsOfFn] using hzeroTraj
        show (stateOfTraj (k := k) (wordTraj (k := k) a ys)).counts.counts i j ≤
            (pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j
        calc
          (stateOfTraj (k := k) (wordTraj (k := k) a ys)).counts.counts i j = 0 := hzeroState
          _ ≤ (pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j :=
            Nat.zero_le _
        )
  have hgraphPos :
      ∀ᶠ r in Filter.atTop,
        0 <
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)) := by
    exact hgraph (Ioi_mem_nhds zero_lt_one)
  filter_upwards [hcounts_le, hgraphPos] with r hcounts hpos
  have hle :
      ∀ i j : Fin k,
        (prefixWordState (k := k) a ys).counts.counts i j ≤
          (pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j := by
    intro i j
    exact hcounts (i, j) (by simp)
  exact prefixCompatibleState_of_mem_stateFinset_of_start_eq_of_counts_le_of_pos_prefixNormalizedEulerTrailCorrectionRatioReal
    (k := k) (a := a) (ys := ys)
    (N := ys.length + r) (hN := Nat.le_add_right ys.length r)
    (eN := pathPrefixState (k := k) ω (ys.length + r))
    (pathPrefixState_mem_stateFinset (k := k) ω (ys.length + r))
    (by simp [pathPrefixState_start, hstart])
    hle hpos

lemma eventually_prefixCompatibleState_pathPrefixState_of_start_eq_of_ratioData
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (Θ : Fin k → Fin k → ℝ)
    (hstart : ω 0 = a)
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i)
          Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop (nhds (Θ i j)))
    (hΘpos :
      ∀ i j : Fin k,
        0 < (prefixWordState (k := k) a ys).counts.counts i j →
          0 < Θ i j)
    (hgraph :
      Filter.Tendsto
        (fun r =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop (nhds (1 : ℝ))) :
    ∀ᶠ r in Filter.atTop,
      prefixCompatibleState (k := k) a ys (ys.length + r)
        (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)) := by
  have hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun r =>
            ((pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k)
                (pathPrefixState (k := k) ω (ys.length + r)) i : ℝ))
          Filter.atTop (nhds (Θ i j)) :=
    pathPrefixState_ratioData_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_outdeg
      (k := k) ω (fun r => ys.length + r) Θ hout hfreq
  have houtReal :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun r =>
            (MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i : ℝ))
          Filter.atTop Filter.atTop := by
    intro i _
    exact tendsto_natCast_atTop_atTop.comp (hout i)
  have hcountGrow :
      ∀ i j : Fin k,
        0 < (prefixWordState (k := k) a ys).counts.counts i j →
          Filter.Tendsto
            (fun r =>
              ((pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j : ℝ))
            Filter.atTop Filter.atTop := by
    intro i j hcountPos
    exact tendsto_prefixEdgeCount_atTop_of_pos_ratio
      (k := k) a ys
      (fun r => pathPrefixState (k := k) ω (ys.length + r))
      Θ houtReal hratio i j hcountPos (hΘpos i j hcountPos)
  exact
    eventually_prefixCompatibleState_pathPrefixState_of_start_eq_of_edgeGrowth_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
      (k := k) a ys ω hstart hcountGrow hgraph

def rowKernelVisitProbReal
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i j : Fin k) (ω : ℕ → Fin k) : ℝ :=
  ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal

/-- Finite support of the transitions actually used by the fixed prefix word
`a :: ys`. -/
def prefixUsedTransitionSet
    (a : Fin k) (ys : List (Fin k)) : Finset (Fin k × Fin k) :=
  (Finset.univ.product Finset.univ).filter
    (fun p =>
      0 < (prefixWordState (k := k) a ys).counts.counts p.1 p.2)

lemma mem_prefixUsedTransitionSet_iff
    (a : Fin k) (ys : List (Fin k)) (i j : Fin k) :
    (i, j) ∈ prefixUsedTransitionSet (k := k) a ys ↔
      0 < (prefixWordState (k := k) a ys).counts.counts i j := by
  simp [prefixUsedTransitionSet]

lemma prefixThetaPowerProduct_eq_zero_of_mem_prefixUsedTransitionSet_zero
    (a : Fin k) (ys : List (Fin k)) (Θ : Fin k → Fin k → ℝ)
    {p : Fin k × Fin k}
    (hp : p ∈ prefixUsedTransitionSet (k := k) a ys)
    (hzero : Θ p.1 p.2 = 0) :
    prefixThetaPowerProduct (k := k) a ys Θ = 0 := by
  classical
  rcases p with ⟨i, j⟩
  have hcount :
      0 < (prefixWordState (k := k) a ys).counts.counts i j := by
    simpa [mem_prefixUsedTransitionSet_iff] using hp
  have hcount_ne :
      transCount (wordTraj (k := k) a ys) i j ≠ 0 := by
    simpa [prefixWordState_counts] using hcount.ne'
  unfold prefixThetaPowerProduct
  refine Finset.prod_eq_zero (i := i) (by simp) ?_
  refine Finset.prod_eq_zero (i := j) (by simp) ?_
  simp [hzero, prefixWordState_counts, hcount_ne]

lemma prefixThetaPowerProduct_eq_zero_of_exists_mem_prefixUsedTransitionSet_zero
    (a : Fin k) (ys : List (Fin k)) (Θ : Fin k → Fin k → ℝ)
    (hzero :
      ∃ p ∈ prefixUsedTransitionSet (k := k) a ys, Θ p.1 p.2 = 0) :
    prefixThetaPowerProduct (k := k) a ys Θ = 0 := by
  rcases hzero with ⟨p, hp, hpzero⟩
  exact prefixThetaPowerProduct_eq_zero_of_mem_prefixUsedTransitionSet_zero
    (a := a) (ys := ys) (Θ := Θ) hp hpzero

lemma prefixThetaPos_of_forall_mem_prefixUsedTransitionSet
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k)
    (hpos :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a ys,
        0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) :
    ∀ i j : Fin k,
      0 < (prefixWordState (k := k) a ys).counts.counts i j →
        0 < rowKernelVisitProbReal (k := k) rowKernel i j ω := by
  intro i j hcount
  have hmem :
      (i, j) ∈ prefixUsedTransitionSet (k := k) a ys := by
    simpa [mem_prefixUsedTransitionSet_iff] using hcount
  exact hpos (i, j) hmem

lemma ae_prefixThetaPos_of_forall_mem_prefixUsedTransitionSet
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hpos :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a ys,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) :
    ∀ i j : Fin k,
      ∀ᵐ ω ∂P,
        ω 0 = a →
          0 < (prefixWordState (k := k) a ys).counts.counts i j →
            0 < rowKernelVisitProbReal (k := k) rowKernel i j ω := by
  intro i j
  by_cases hcount :
      0 < (prefixWordState (k := k) a ys).counts.counts i j
  · have hmem :
        (i, j) ∈ prefixUsedTransitionSet (k := k) a ys := by
      simpa [mem_prefixUsedTransitionSet_iff] using hcount
    filter_upwards [hpos (i, j) hmem] with ω hω hstart _
    exact hω hstart
  · exact Filter.Eventually.of_forall (fun ω _ hcountPos => (hcount hcountPos).elim)

lemma ae_forall_mem_prefixUsedTransitionSet_of_ae_prefixThetaPos
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a ys).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω) :
    ∀ p ∈ prefixUsedTransitionSet (k := k) a ys,
      ∀ᵐ ω ∂P,
        ω 0 = a →
          0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω := by
  intro p hp
  have hpcount :
      0 < (prefixWordState (k := k) a ys).counts.counts p.1 p.2 := by
    exact
      (mem_prefixUsedTransitionSet_iff (k := k) a ys p.1 p.2).1
        (by simpa using hp)
  filter_upwards [hΘpos p.1 p.2] with ω hω hstart
  exact hω hstart hpcount

/-- One-row singleton Cesàro limit interface on `rowProcessLaw`.
This is the local target used to feed `hfreq` in the prefix-ratio builder. -/
def RowProcessSingletonCesaroLimit
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i j : Fin k) : Prop :=
  ∀ᵐ r ∂rowProcessLaw (k := k) P i,
    Filter.Tendsto
      (fun m => rowProcessEmpiricalFreq (k := k) j r m)
      Filter.atTop
      (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal))

/-- Coordwise packaging of one-row singleton Cesàro limits. -/
def RowProcessCoordwiseCesaroLimit
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)) : Prop :=
  ∀ i j : Fin k, RowProcessSingletonCesaroLimit (k := k) P rowKernel i j

/-- Canonical i,j specialization of the row-process Cesàro target when
`rowKernel` is instantiated by directing measures. -/
lemma rowProcessSingletonCesaroLimit_of_directingRowKernel
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i j : Fin k)
    (hlim :
      ∀ᵐ r ∂rowProcessLaw (k := k) P i,
        Filter.Tendsto
          (fun m => rowProcessEmpiricalFreq (k := k) j r m)
          Filter.atTop
          (nhds (((directingRowKernel (k := k) P i r) ({j} : Set (Fin k))).toReal))) :
    RowProcessSingletonCesaroLimit (k := k) P (directingRowKernel (k := k) P) i j := by
  simpa [RowProcessSingletonCesaroLimit] using hlim

/-- Coordwise packaging of canonical directing-kernel row-process Cesàro limits. -/
lemma rowProcessCoordwiseCesaroLimit_of_directingRowKernel
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hlim :
      ∀ i j : Fin k,
        ∀ᵐ r ∂rowProcessLaw (k := k) P i,
          Filter.Tendsto
            (fun m => rowProcessEmpiricalFreq (k := k) j r m)
            Filter.atTop
            (nhds (((directingRowKernel (k := k) P i r) ({j} : Set (Fin k))).toReal))) :
    RowProcessCoordwiseCesaroLimit (k := k) P (directingRowKernel (k := k) P) := by
  intro i j
  exact
    rowProcessSingletonCesaroLimit_of_directingRowKernel
      (k := k) P i j (hlim i j)

/-- Exchangeability packages the canonical directing-row Cesàro theorem into the
coordwise row-process limit structure. -/
lemma rowProcessCoordwiseCesaroLimit_of_directingRowKernel_of_exchangeable
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExch :
      ∀ i : Fin k,
        Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
          (fun n (r : ℕ → Fin k) => r n)) :
    RowProcessCoordwiseCesaroLimit (k := k) P (directingRowKernel (k := k) P) := by
  intro i j
  exact
    rowProcessSingletonCesaroLimit_of_directingRowKernel
      (k := k) P i j
      (ae_tendsto_rowProcessEmpiricalFreq_to_directingRowKernel
        (k := k) (P := P) i j (hExch i))

/-- The unrestricted row-process law decomposes as the finite sum of its
start-restricted components. -/
lemma rowProcessLaw_eq_finsetSum_startRestricted
    (P : Measure (ℕ → Fin k))
    (i : Fin k) :
    rowProcessLaw (k := k) P i
      =
    ∑ a : Fin k,
      rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i := by
  let s : Fin k → Set (ℕ → Fin k) := fun a => {ω : ℕ → Fin k | ω 0 = a}
  have hs_meas : ∀ a : Fin k, MeasurableSet (s a) := by
    intro a
    change MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' ({a} : Set (Fin k)))
    exact (measurable_pi_apply 0) (MeasurableSet.singleton a)
  have hs_disj : Pairwise (fun a b : Fin k => Disjoint (s a) (s b)) := by
    intro a b hab
    rw [Set.disjoint_iff]
    intro ω hω
    exact hab (hω.1.symm.trans hω.2)
  have hs_union : (⋃ a : Fin k, s a) = Set.univ := by
    ext ω
    simp [s]
  have hsum :
      P = Measure.sum (fun a : Fin k => P.restrict (s a)) := by
    calc
      P = P.restrict (⋃ a : Fin k, s a) := by simp [hs_union]
      _ = Measure.sum (fun a : Fin k => P.restrict (s a)) := by
            simpa using
              (Measure.restrict_iUnion (μ := P) hs_disj hs_meas)
  calc
    rowProcessLaw (k := k) P i
        = Measure.map (rowSuccessorVisitProcess (k := k) i) P := rfl
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
          rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i := by
            rw [Measure.sum_fintype]
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [rowProcessLaw, s]

/-- If row-kernel singleton evaluations agree with the canonical
`directingRowKernel` on each start-restricted row law, then the canonical a.e.
Cesàro theorem transports to a global `RowProcessCoordwiseCesaroLimit`. -/
lemma rowProcessCoordwiseCesaroLimit_of_startRestricted_eval_eq_directingRowKernel
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEq :
      ∀ a i j : Fin k,
        (fun r : ℕ → Fin k => ((rowKernel i r : Measure (Fin k)) ({j} : Set (Fin k))).toReal)
          =ᵐ[rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i]
        (fun r : ℕ → Fin k =>
          ((directingRowKernel (k := k) P i r : Measure (Fin k)) ({j} : Set (Fin k))).toReal))
    (hExch :
      ∀ i : Fin k,
        Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
          (fun n (r : ℕ → Fin k) => r n)) :
    RowProcessCoordwiseCesaroLimit (k := k) P rowKernel := by
  intro i j
  rw [RowProcessSingletonCesaroLimit]
  rw [rowProcessLaw_eq_finsetSum_startRestricted (k := k) (P := P) (i := i)]
  rw [MeasureTheory.ae_finsetSum_measure_iff]
  intro a ha
  have hcanon :
      ∀ᵐ r ∂rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i,
        Filter.Tendsto
          (fun m => rowProcessEmpiricalFreq (k := k) j r m)
          Filter.atTop
          (nhds (((directingRowKernel (k := k) P i r) ({j} : Set (Fin k))).toReal)) := by
    exact
      (ae_tendsto_rowProcessEmpiricalFreq_to_directingRowKernel
        (k := k) (P := P) i j (hExch i)).filter_mono
        (MeasureTheory.ae_mono
          (rowProcessLaw_restrict_le (k := k) P {ω : ℕ → Fin k | ω 0 = a} i))
  filter_upwards [hcanon, hEq a i j] with r hcanon_r hEq_r
  convert hcanon_r using 1
  exact congrArg nhds hEq_r

/-- Class-restricted analogue of
`rowProcessCoordwiseCesaroLimit_of_startRestricted_eval_eq_directingRowKernel`.
The class-restricted row law is assembled from the singleton-start fibers using
`rowProcessLaw_restrictClass_eq_finsetSum`. -/
lemma rowProcessCoordwiseCesaroLimit_restrictClass_of_startRestricted_eval_eq_directingRowKernel
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (C : Set (Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEq :
      ∀ a i j : Fin k,
        (fun r : ℕ → Fin k => ((rowKernel i r : Measure (Fin k)) ({j} : Set (Fin k))).toReal)
          =ᵐ[rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i]
        (fun r : ℕ → Fin k =>
          ((directingRowKernel (k := k) P i r : Measure (Fin k)) ({j} : Set (Fin k))).toReal))
    (hExch :
      ∀ i : Fin k,
        Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
          (fun n (r : ℕ → Fin k) => r n)) :
    RowProcessCoordwiseCesaroLimit
      (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 ∈ C}) rowKernel := by
  intro i j
  rw [RowProcessSingletonCesaroLimit]
  change
    ∀ᵐ r ∂Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass (k := k) C P i,
      Filter.Tendsto
        (fun m => rowProcessEmpiricalFreq (k := k) j r m)
        Filter.atTop
        (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal))
  rw [Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass_eq_finsetSum
    (k := k) (C := C) (P := P) (i := i)]
  rw [MeasureTheory.ae_finsetSum_measure_iff]
  intro a ha
  by_cases hCa : a ∈ C
  · have hcanon :
        ∀ᵐ r ∂rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i,
          Filter.Tendsto
            (fun m => rowProcessEmpiricalFreq (k := k) j r m)
            Filter.atTop
            (nhds (((directingRowKernel (k := k) P i r) ({j} : Set (Fin k))).toReal)) := by
      exact
        (ae_tendsto_rowProcessEmpiricalFreq_to_directingRowKernel
          (k := k) (P := P) i j (hExch i)).filter_mono
          (MeasureTheory.ae_mono
            (rowProcessLaw_restrict_le (k := k) P {ω : ℕ → Fin k | ω 0 = a} i))
    have hbranch :
        ∀ᵐ r ∂rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i,
          Filter.Tendsto
            (fun m => rowProcessEmpiricalFreq (k := k) j r m)
            Filter.atTop
            (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal)) := by
      filter_upwards [hcanon, hEq a i j] with r hcanon_r hEq_r
      convert hcanon_r using 1
      exact congrArg nhds hEq_r
    simpa [hCa] using hbranch
  · simp [hCa]

/-- Canonical class-restricted coordwise Cesàro theorem for the unrestricted
directing row kernel, assembled from the singleton-start fibers. -/
lemma rowProcessCoordwiseCesaroLimit_restrictClass_of_directingRowKernel_of_exchangeable
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (C : Set (Fin k))
    (hExch :
      ∀ i : Fin k,
        Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
          (fun n (r : ℕ → Fin k) => r n)) :
    RowProcessCoordwiseCesaroLimit
      (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 ∈ C})
      (directingRowKernel (k := k) P) := by
  exact
    rowProcessCoordwiseCesaroLimit_restrictClass_of_startRestricted_eval_eq_directingRowKernel
      (k := k) (P := P) (C := C) (rowKernel := directingRowKernel (k := k) P)
      (hEq := fun _ _ _ => Filter.EventuallyEq.rfl)
      hExch

/-- The canonical `directingRowKernel` satisfies `StartRestrictedRowKernelData`:
for each start state `a`, the restricted row-process law factors through the
directing kernel computed from the full measure.

**Proof strategy**:
1. If P({ω₀=a}) = 0: both sides are zero (trivial)
2. If P({ω₀=a}) > 0:
   - Normalize restricted row-process law to probability measure
   - Apply finite_product_formula_with_directing (ViaMartingale:417)
   - Use directingMeasure_singleton_ae_eq_of_smul_le (KernelUniqueness:714)
     to show directing measures agree a.e.
   - Scale back to unnormalized measure

**Available infrastructure**:
- exchangeable_rowProcess_restrict (PEBridge:2057)
- finite_product_formula_with_directing (ViaMartingale:417)
- directingMeasure_singleton_ae_eq_of_smul_le (KernelUniqueness:714)
-- rowProcessLaw_restrict_le (FortiniBridgeCrux:335) -/
theorem startRestrictedRowLaw_factorizes_directingRowKernel_of_exchangeable
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (i a : Fin k)
    (m : ℕ) (sel : Fin m → ℕ) (hsel : StrictMono sel)
    (hExch :
      Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
        (fun n (r : ℕ → Fin k) => r n))
    (hExchRestr :
      Exchangeability.Exchangeable (P.restrict {ω : ℕ → Fin k | ω 0 = a})
        (fun n (ω : ℕ → Fin k) =>
          rowSuccessorVisitProcess (k := k) i ω n)) :
    Measure.map
        (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
        (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
      =
    (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
      (fun r =>
        Measure.pi
          (fun _ : Fin m =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
  let S := {ω : ℕ → Fin k | ω 0 = a}
  let Pa := P.restrict S
  let c := P S
  by_cases hc : c = 0
  · have hS_meas : MeasurableSet S := by
      show MeasurableSet ((fun ω : ℕ → Fin k => ω 0) ⁻¹' {a})
      exact (measurable_pi_apply 0) (measurableSet_singleton a)
    have hPa_zero : Pa = 0 := by
      ext T hT
      simp only [Measure.coe_zero, Pi.zero_apply]
      have h1 : Pa T = P (T ∩ S) := Measure.restrict_apply hT
      have h2 : P (T ∩ S) ≤ P S := measure_mono Set.inter_subset_right
      apply le_antisymm
      · calc
          Pa T = P (T ∩ S) := h1
          _ ≤ P S := h2
          _ = c := rfl
          _ = 0 := hc
      · exact bot_le
    have hρa_zero : rowProcessLaw (k := k) Pa i = 0 := by
      simp only [rowProcessLaw, hPa_zero, Measure.map_zero]
    show Measure.map _ (rowProcessLaw (k := k) Pa i) =
         (rowProcessLaw (k := k) Pa i).bind _
    rw [hρa_zero, Measure.map_zero, Measure.bind_zero_left]
  · have hc_pos : 0 < c := pos_iff_ne_zero.mpr hc
    have hc_ne_top : c ≠ ⊤ := by
      have h1 : P S ≤ P Set.univ := measure_mono (Set.subset_univ _)
      have h2 : P Set.univ = 1 := measure_univ
      have h3 : (1 : ENNReal) < ⊤ := ENNReal.one_lt_top
      exact ne_top_of_lt (lt_of_le_of_lt (h2 ▸ h1) h3)
    let ρa := rowProcessLaw (k := k) Pa i
    let ρ := rowProcessLaw (k := k) P i
    have hρa_le : ρa ≤ ρ := rowProcessLaw_restrict_le (k := k) P S i
    have hρa_mass : ρa Set.univ = c := by
      simp only [rowProcessLaw, ρa]
      rw [Measure.map_apply (measurable_rowSuccessorVisitProcess (k := k) i) MeasurableSet.univ]
      simp only [Set.preimage_univ]
      exact Measure.restrict_apply_univ (μ := P) S
    let ρa_norm := c⁻¹ • ρa
    have hρa_norm_prob : IsProbabilityMeasure ρa_norm := by
      constructor
      calc
        ρa_norm Set.univ = c⁻¹ * ρa Set.univ := Measure.smul_apply c⁻¹ ρa Set.univ
        _ = c⁻¹ * c := by rw [hρa_mass]
        _ = 1 := ENNReal.inv_mul_cancel hc hc_ne_top
    have hρa_eq : ρa = c • ρa_norm := by
      ext T hT
      simp only [ρa_norm, Measure.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ENNReal.mul_inv_cancel hc hc_ne_top, one_mul]
    have hExch_ρa : Exchangeability.Exchangeable ρa (fun n (r : ℕ → Fin k) => r n) := by
      intro n' σ'
      have hmeas1 : Measurable (fun r : ℕ → Fin k => fun j : Fin n' => r (σ' j)) := by
        apply measurable_pi_lambda
        intro j
        exact measurable_pi_apply _
      have hmeas2 : Measurable (fun r : ℕ → Fin k => fun j : Fin n' => r j) := by
        apply measurable_pi_lambda
        intro j
        exact measurable_pi_apply _
      have hmeas_rsp := measurable_rowSuccessorVisitProcess (k := k) i
      simp only [ρa, rowProcessLaw]
      rw [Measure.map_map hmeas1 hmeas_rsp, Measure.map_map hmeas2 hmeas_rsp]
      exact hExchRestr n' σ'
    have hExch_ρa_norm : Exchangeability.Exchangeable ρa_norm (fun n (r : ℕ → Fin k) => r n) := by
      intro n' σ'
      simp only [ρa_norm, Measure.map_smul]
      exact congrArg (c⁻¹ • ·) (hExch_ρa n' σ')
    have hContr_ρa_norm : Exchangeability.Contractable ρa_norm (fun n (r : ℕ → Fin k) => r n) :=
      Exchangeability.contractable_of_exchangeable hExch_ρa_norm (fun n => measurable_pi_apply n)
    haveI : Nonempty (Fin k) := ⟨i⟩
    have hX_meas : ∀ n, Measurable (fun r : ℕ → Fin k => r n) := fun n => measurable_pi_apply n
    have hprod_ρa_norm : Measure.map (fun r => fun j => r (sel j)) ρa_norm =
        ρa_norm.bind (fun r => Measure.pi (fun _ : Fin m =>
          directingMeasure (μ := ρa_norm) (fun n (r : ℕ → Fin k) => r n) hX_meas r)) := by
      letI := hρa_norm_prob
      exact finite_product_formula_with_directing (X := fun n (r : ℕ → Fin k) => r n)
        hContr_ρa_norm hX_meas m sel hsel
    have hρa_norm_le : ρa_norm ≤ c⁻¹ • ρ := by
      intro T
      simp only [ρa_norm, Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_right (hρa_le T) _
    have hc_inv_ne_top : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc
    haveI hρ_prob : IsProbabilityMeasure ρ :=
      Measure.isProbabilityMeasure_map
        ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
    have hdir_eq : ∀ b : Fin k,
        (fun r => (directingMeasure (μ := ρ) (fun n (r : ℕ → Fin k) => r n) hX_meas r {b}).toReal)
          =ᵐ[ρa_norm]
        (fun r => (directingMeasure (μ := ρa_norm) (fun n (r : ℕ → Fin k) => r n) hX_meas r {b}).toReal) := by
      intro b
      letI := hρa_norm_prob
      exact
        Mettapedia.Logic.DirectingMeasureL1Transfer.directingMeasure_singleton_ae_eq_of_smul_le
          (X := fun n (r : ℕ → Fin k) => r n) hX_meas
          hExch hExch_ρa_norm hc_inv_ne_top hρa_norm_le b
    have hpi_eq :
        (fun r => Measure.pi (fun _ : Fin m =>
          @directingMeasure _ _ _ ρa_norm hρa_norm_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r)) =ᵐ[ρa_norm]
        (fun r => Measure.pi (fun _ : Fin m =>
          @directingMeasure _ _ _ ρ hρ_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r)) := by
      have hfin_eq : ∀ᵐ r ∂ρa_norm, ∀ b : Fin k,
          (@directingMeasure _ _ _ ρ hρ_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r {b}).toReal =
          (@directingMeasure _ _ _ ρa_norm hρa_norm_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r {b}).toReal := by
        rw [ae_all_iff]
        intro b
        exact hdir_eq b
      filter_upwards [hfin_eq] with r hr
      have hdir_r_eq :
          @directingMeasure _ _ _ ρa_norm hρa_norm_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r =
          @directingMeasure _ _ _ ρ hρ_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r := by
        apply Measure.ext_of_singleton
        intro b
        have hrb := hr b
        haveI : IsProbabilityMeasure
            (@directingMeasure _ _ _ ρ hρ_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r) :=
          directingMeasure_isProb (fun n (r : ℕ → Fin k) => r n) hX_meas r
        haveI : IsProbabilityMeasure
            (@directingMeasure _ _ _ ρa_norm hρa_norm_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r) :=
          directingMeasure_isProb (fun n (r : ℕ → Fin k) => r n) hX_meas r
        have h1 :
            (@directingMeasure _ _ _ ρ hρ_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r {b}) ≠ ⊤ :=
          measure_ne_top _ _
        have h2 :
            (@directingMeasure _ _ _ ρa_norm hρa_norm_prob _ _ _ _ (fun n (r : ℕ → Fin k) => r n) hX_meas r {b}) ≠ ⊤ :=
          measure_ne_top _ _
        rw [← ENNReal.toReal_eq_toReal_iff' h2 h1]
        exact hrb.symm
      simp only [hdir_r_eq]
    have hdirK_eq_dirM :
        (fun r => Measure.pi (fun _ : Fin m =>
          directingMeasure (μ := ρ) (fun n (r : ℕ → Fin k) => r n) hX_meas r)) =ᵐ[ρa_norm]
        (fun r => Measure.pi (fun _ : Fin m =>
          (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
      filter_upwards with r
      congr 1
    have hbind_eq : ρa_norm.bind (fun r => Measure.pi (fun _ : Fin m =>
          directingMeasure (μ := ρa_norm) (fun n (r : ℕ → Fin k) => r n) hX_meas r)) =
        ρa_norm.bind (fun r => Measure.pi (fun _ : Fin m =>
          (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
      apply Measure.bind_congr_right
      exact hpi_eq.trans hdirK_eq_dirM
    have hprod_ρa_norm' : Measure.map (fun r => fun j => r (sel j)) ρa_norm =
        ρa_norm.bind (fun r => Measure.pi (fun _ : Fin m =>
          (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
      rw [hprod_ρa_norm, hbind_eq]
    have hmap_scale : Measure.map (fun r => fun j => r (sel j)) ρa =
        c • Measure.map (fun r => fun j => r (sel j)) ρa_norm := by
      rw [hρa_eq]
      exact Measure.map_smul _ _ _
    have hbind_scale : ρa.bind (fun r => Measure.pi (fun _ : Fin m =>
          (directingRowKernel (k := k) P i r : Measure (Fin k)))) =
        c • ρa_norm.bind (fun r => Measure.pi (fun _ : Fin m =>
          (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
      rw [hρa_eq]
      exact Measure.bind_smul _ _ _
    rw [hmap_scale, hbind_scale, hprod_ρa_norm']

theorem startRestrictedRowKernelData_directingRowKernel
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (hExch :
      ∀ i : Fin k,
        Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
          (fun n (r : ℕ → Fin k) => r n)) :
    StartRestrictedRowKernelData (k := k) P (directingRowKernel (k := k) P) := by
  intro i a m sel hsel
  exact
    startRestrictedRowLaw_factorizes_directingRowKernel_of_exchangeable
      (k := k) (P := P) i a m sel hsel
      (hExch i)
      (exchangeable_rowProcess_restrict (k := k) μ hμ P hExt hStrRec i a)

/-- Class-restricted finite-coordinate factorization for the canonical
`directingRowKernel`, assembled from per-start factorization on the singleton
fibers that actually occur inside the class. -/
theorem rowProcessLaw_restrictClass_factorizes_directingRowKernel_of_startRestricted
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (C : Set (Fin k))
    (i : Fin k)
    (hstart :
      ∀ a : Fin k, a ∈ C →
        ∀ (m : ℕ) (sel : Fin m → ℕ), StrictMono sel →
          Measure.map
              (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
              (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i)
            =
          (rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i).bind
            (fun r =>
              Measure.pi
                (fun _ : Fin m =>
                  (directingRowKernel (k := k) P i r : Measure (Fin k)))))
    (m : ℕ) (sel : Fin m → ℕ) (hsel : StrictMono sel) :
    Measure.map
        (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
        (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass (k := k) C P i)
      =
    (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass (k := k) C P i).bind
      (fun r =>
        Measure.pi
          (fun _ : Fin m =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
  classical
  let ρC : Measure (ℕ → Fin k) :=
    Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass (k := k) C P i
  let μC : Fin k → Measure (ℕ → Fin k) := fun a =>
    if a ∈ C then
      rowProcessLaw (k := k) (P.restrict {ω : ℕ → Fin k | ω 0 = a}) i
    else 0
  let proj : (ℕ → Fin k) → (Fin m → Fin k) := fun r => fun j : Fin m => r (sel j)
  let κ : (ℕ → Fin k) → Measure (Fin m → Fin k) := fun r =>
    Measure.pi
      (fun _ : Fin m =>
        (directingRowKernel (k := k) P i r : Measure (Fin k)))
  have hρC :
      ρC = Measure.sum μC := by
    rw [Measure.sum_fintype]
    simpa [ρC, μC] using
      (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass_eq_finsetSum
        (k := k) (C := C) (P := P) (i := i))
  have hproj_meas : Measurable proj := by
    change Measurable (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
    exact measurable_pi_lambda _ (fun j => measurable_pi_apply (sel j))
  haveI : Nonempty (Fin k) := ⟨i⟩
  haveI : IsProbabilityMeasure (rowProcessLaw (k := k) P i) :=
    Measure.isProbabilityMeasure_map
      ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
  have hdir_eval_meas :
      ∀ B : Set (Fin k), MeasurableSet B →
        Measurable
          (fun r : ℕ → Fin k =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)) B) := by
    intro B hB
    simpa [directingRowKernel] using
      (directingMeasure_measurable_eval
        (μ := rowProcessLaw (k := k) P i)
        (X := fun n (r : ℕ → Fin k) => r n)
        (hX := fun n => measurable_pi_apply n)
        B hB)
  have hκ_meas : Measurable κ := by
    exact
      measurable_measure_pi
        (fun r : ℕ → Fin k =>
          (directingRowKernel (k := k) P i r : Measure (Fin k)))
        (fun r => by infer_instance)
        hdir_eval_meas
  have hfiber :
      (fun a : Fin k => Measure.map proj (μC a)) =
        (fun a : Fin k => (μC a).bind κ) := by
    funext a
    by_cases hCa : a ∈ C
    · simp [μC, proj, κ, hCa, hstart a hCa m sel hsel]
    · simp [μC, κ, hCa]
  calc
    Measure.map proj ρC = Measure.map proj (Measure.sum μC) := by rw [hρC]
    _ = Measure.sum (fun a : Fin k => Measure.map proj (μC a)) := by
          exact MeasureTheory.Measure.map_sum hproj_meas.aemeasurable
    _ = Measure.sum (fun a : Fin k => (μC a).bind κ) := by rw [hfiber]
    _ = (Measure.sum μC).bind κ := by
          symm
          exact Measure.bind_sum μC κ hκ_meas.aemeasurable
    _ = ρC.bind κ := by rw [hρC]

/-- Class-restricted finite-coordinate factorization from fixed-row
exchangeability data: one unrestricted exchangeability hypothesis for row `i`,
plus singleton-start exchangeability on the class fibers. -/
theorem rowProcessLaw_restrictClass_factorizes_directingRowKernel_of_exchangeable
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (C : Set (Fin k))
    (i : Fin k)
    (hExch :
      Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
        (fun n (r : ℕ → Fin k) => r n))
    (hExchRestr :
      ∀ a : Fin k, a ∈ C →
        Exchangeability.Exchangeable (P.restrict {ω : ℕ → Fin k | ω 0 = a})
          (fun n (ω : ℕ → Fin k) =>
            rowSuccessorVisitProcess (k := k) i ω n))
    (m : ℕ) (sel : Fin m → ℕ) (hsel : StrictMono sel) :
    Measure.map
        (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
        (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass (k := k) C P i)
      =
    (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass (k := k) C P i).bind
      (fun r =>
        Measure.pi
          (fun _ : Fin m =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
  exact
    rowProcessLaw_restrictClass_factorizes_directingRowKernel_of_startRestricted
      (k := k) (P := P) (C := C) (i := i)
      (hstart := fun a ha =>
        startRestrictedRowLaw_factorizes_directingRowKernel_of_exchangeable
          (k := k) (P := P) i a
          (hExch := hExch) (hExchRestr := hExchRestr a ha))
      m sel hsel

/-- Class-restricted finite-coordinate factorization for the canonical
`directingRowKernel`, assembled from the singleton-start factorization theorem. -/
theorem rowProcessLaw_restrictClass_factorizes_directingRowKernel
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hStrRec : StrongRecurrence (k := k) P)
    (hExch :
      ∀ i : Fin k,
        Exchangeability.Exchangeable (rowProcessLaw (k := k) P i)
          (fun n (r : ℕ → Fin k) => r n))
    (C : Set (Fin k))
    (i : Fin k) (m : ℕ) (sel : Fin m → ℕ) (hsel : StrictMono sel) :
    Measure.map
        (fun r : ℕ → Fin k => fun j : Fin m => r (sel j))
        (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass (k := k) C P i)
      =
    (Mettapedia.Logic.MarkovDeFinettiHard.rowProcessLaw_restrictClass (k := k) C P i).bind
      (fun r =>
        Measure.pi
          (fun _ : Fin m =>
            (directingRowKernel (k := k) P i r : Measure (Fin k)))) := by
  exact
    rowProcessLaw_restrictClass_factorizes_directingRowKernel_of_startRestricted
      (k := k) (P := P) (C := C) (i := i)
      (hstart := fun a ha =>
        startRestrictedRowKernelData_directingRowKernel
          (k := k) μ hμ P hExt hStrRec hExch i a)
      m sel hsel

lemma ae_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_of_ae_tendsto_rowProcessEmpiricalFreq
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (i j : Fin k)
    (hrow :
      ∀ᵐ r ∂rowProcessLaw (k := k) P i,
        Filter.Tendsto
          (fun m => rowProcessEmpiricalFreq (k := k) j r m)
          Filter.atTop
          (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
        Filter.atTop
        (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) := by
  have hpre :
      ∀ᵐ ω ∂P,
        Filter.Tendsto
          (fun m =>
            rowProcessEmpiricalFreq (k := k) j
              (rowSuccessorVisitProcess (k := k) i ω) m)
          Filter.atTop
          (nhds (((rowKernel i (rowSuccessorVisitProcess (k := k) i ω))
            ({j} : Set (Fin k))).toReal)) := by
    simpa [rowProcessLaw] using
      (MeasureTheory.ae_of_ae_map
        (μ := P)
        (f := rowSuccessorVisitProcess (k := k) i)
        ((measurable_rowSuccessorVisitProcess (k := k) i).aemeasurable)
        hrow)
  filter_upwards [hpre] with ω hω
  simpa [rowKernelVisitProbReal, rowSuccessorEmpiricalFreq_eq_rowProcessEmpiricalFreq] using hω

lemma ae_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_on_start_of_ae_tendsto_rowProcessEmpiricalFreq
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a i j : Fin k)
    (hrow :
      ∀ᵐ r ∂rowProcessLaw (k := k) P i,
        Filter.Tendsto
          (fun m => rowProcessEmpiricalFreq (k := k) j r m)
          Filter.atTop
          (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop
          (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) := by
  filter_upwards
    [ae_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_of_ae_tendsto_rowProcessEmpiricalFreq
      (k := k) P rowKernel i j hrow] with ω hω _
  exact hω

lemma ae_coordwise_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_on_start_of_ae_coordwise_tendsto_rowProcessEmpiricalFreq
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a : Fin k)
    (hrow :
      ∀ i j : Fin k,
        ∀ᵐ r ∂rowProcessLaw (k := k) P i,
          Filter.Tendsto
            (fun m => rowProcessEmpiricalFreq (k := k) j r m)
            Filter.atTop
            (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal))) :
    ∀ i j : Fin k,
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
            Filter.atTop
            (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) := by
  intro i j
  exact
    ae_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_on_start_of_ae_tendsto_rowProcessEmpiricalFreq
      (k := k) P rowKernel a i j (hrow i j)

lemma ae_coordwise_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_on_start_of_rowProcessCoordwiseCesaroLimit
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a : Fin k)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel) :
    ∀ i j : Fin k,
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
            Filter.atTop
            (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) := by
  exact
    ae_coordwise_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_on_start_of_ae_coordwise_tendsto_rowProcessEmpiricalFreq
      (k := k) P rowKernel a hrow

lemma ae_all_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_of_coordwise
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a : Fin k)
    (hfreq :
      ∀ i : Fin k, ∀ j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ i : Fin k, ∀ j : Fin k,
          Filter.Tendsto
            (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
            Filter.atTop
            (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) := by
  have hpack :
      ∀ᵐ ω ∂P,
        ∀ i : Fin k, ∀ j : Fin k,
          ω 0 = a →
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hfreq i j
  filter_upwards [hpack] with ω hω hstart i j
  exact hω i j hstart

lemma tendsto_prefixRatioApproxENN_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (Θ : Fin k → Fin k → ℝ)
    (hcomp :
      ∀ r,
        prefixCompatibleState (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)))
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i)
          Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop (nhds (Θ i j)))
    (hgraph :
      Filter.Tendsto
        (fun r =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun r => prefixRatioApproxENN (k := k) a ys r ω)
      Filter.atTop
      (nhds (ENNReal.ofReal (prefixThetaPowerProduct (k := k) a ys Θ))) := by
  have hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun r =>
            ((pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k)
                (pathPrefixState (k := k) ω (ys.length + r)) i : ℝ))
          Filter.atTop (nhds (Θ i j)) :=
    pathPrefixState_ratioData_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_outdeg
      (k := k) ω (fun r => ys.length + r) Θ hout hfreq
  have houtReal :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun r =>
            (MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i : ℝ))
          Filter.atTop Filter.atTop := by
    intro i _
    exact tendsto_natCast_atTop_atTop.comp (hout i)
  have hmain :
      Filter.Tendsto
        (fun r =>
          prefixRatioFnReal (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop
        (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) :=
    tendsto_prefixRatioFnReal_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
      (k := k) a ys
      (fun r => ys.length + r)
      (fun r => Nat.le_add_right ys.length r)
      (fun r => pathPrefixState (k := k) ω (ys.length + r))
      Θ hcomp houtReal hratio hgraph
  have hofReal :
      Filter.Tendsto
        (fun r =>
          ENNReal.ofReal
            (prefixRatioFnReal (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r))))
        Filter.atTop
        (nhds (ENNReal.ofReal (prefixThetaPowerProduct (k := k) a ys Θ))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hmain
  simpa [prefixRatioApproxENN] using hofReal

lemma tendsto_prefixRatioApproxENN_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_eventually_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k) (Θ : Fin k → Fin k → ℝ)
    (hcomp :
      ∀ᶠ r in Filter.atTop,
        prefixCompatibleState (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)))
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i)
          Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop (nhds (Θ i j)))
    (hgraph :
      Filter.Tendsto
        (fun r =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun r => prefixRatioApproxENN (k := k) a ys r ω)
      Filter.atTop
      (nhds (ENNReal.ofReal (prefixThetaPowerProduct (k := k) a ys Θ))) := by
  have hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun r =>
            ((pathPrefixState (k := k) ω (ys.length + r)).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k)
                (pathPrefixState (k := k) ω (ys.length + r)) i : ℝ))
          Filter.atTop (nhds (Θ i j)) :=
    pathPrefixState_ratioData_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_outdeg
      (k := k) ω (fun r => ys.length + r) Θ hout hfreq
  have houtReal :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a ys) i →
        Filter.Tendsto
          (fun r =>
            (MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i : ℝ))
          Filter.atTop Filter.atTop := by
    intro i _
    exact tendsto_natCast_atTop_atTop.comp (hout i)
  have hmain :
      Filter.Tendsto
        (fun r =>
          prefixRatioFnReal (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop
        (nhds (prefixThetaPowerProduct (k := k) a ys Θ)) :=
    tendsto_prefixRatioFnReal_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_eventually_prefixCompatibleState
      (k := k) a ys
      (fun r => ys.length + r)
      (fun r => Nat.le_add_right ys.length r)
      (fun r => pathPrefixState (k := k) ω (ys.length + r))
      Θ hcomp houtReal hratio hgraph
  have hofReal :
      Filter.Tendsto
        (fun r =>
          ENNReal.ofReal
            (prefixRatioFnReal (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r))))
        Filter.atTop
        (nhds (ENNReal.ofReal (prefixThetaPowerProduct (k := k) a ys Θ))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hmain
  simpa [prefixRatioApproxENN] using hofReal

lemma tendsto_prefixRatioApproxENN_of_start_eq_to_rowKernelStepProd
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (Θ : Fin k → Fin k → ℝ)
    (hstart : ω 0 = a)
    (hcomp :
      ∀ r,
        prefixCompatibleState (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)))
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i)
          Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop (nhds (Θ i j)))
    (hgraph :
      Filter.Tendsto
        (fun r =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop (nhds (1 : ℝ)))
    (hΘ :
      ∀ i j, Θ i j =
        ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω))
          ({j} : Set (Fin k))).toReal) :
    Filter.Tendsto
      (fun r => prefixRatioApproxENN (k := k) a ys r ω)
      Filter.atTop
      (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: ys) else 0)) := by
  have hmain :=
    tendsto_prefixRatioApproxENN_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
      (k := k) a ys ω Θ hcomp hout hfreq hgraph
  have hstep_ne_top :
      rowKernelStepProd (k := k) rowKernel ω (a :: ys) ≠ ⊤ := by
    exact ne_of_lt <| lt_of_le_of_lt
      (rowKernelStepProd_le_one (k := k) rowKernel ω (a :: ys))
      (by simp)
  have htarget :
      ENNReal.ofReal (prefixThetaPowerProduct (k := k) a ys Θ) =
        rowKernelStepProd (k := k) rowKernel ω (a :: ys) := by
    rw [prefixThetaPowerProduct_eq_rowKernelStepProd_toReal
      (k := k) a ys rowKernel ω Θ hΘ]
    exact ENNReal.ofReal_toReal hstep_ne_top
  simpa [hstart, htarget] using hmain

theorem ae_tendsto_prefixRatioApproxENN_of_coordwise_component_limits
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hout :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (((rowKernel i
                (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)))
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < ((rowKernel i
                (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have houtAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k,
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k,
            ω 0 = a →
              Filter.Tendsto
                (fun r =>
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
                Filter.atTop Filter.atTop := by
      rw [ae_all_iff]
      intro i
      exact hout i
    filter_upwards [hpack] with ω hω hstart i
    exact hω i hstart
  have hfreqAll :=
    ae_all_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_of_coordwise
      (k := k) P rowKernel a hfreq
  have hΘposAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i j : Fin k,
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < ((rowKernel i
                (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k, ∀ j : Fin k,
            ω 0 = a →
              0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
                0 < ((rowKernel i
                  (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal := by
      rw [ae_all_iff]
      intro i
      rw [ae_all_iff]
      intro j
      exact hΘpos i j
    filter_upwards [hpack] with ω hω hstart i j hij
    exact hω i j hstart hij
  filter_upwards [houtAll, hfreqAll, hΘposAll, hgraph] with ω houtω hfreqω hΘposω hgraphω
  by_cases hstart : ω 0 = a
  · have hcomp :
        ∀ᶠ r in Filter.atTop,
          prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
            (Nat.le_add_right (b :: xs).length r)
            (pathPrefixState (k := k) ω ((b :: xs).length + r)) :=
      eventually_prefixCompatibleState_pathPrefixState_of_start_eq_of_ratioData
        (k := k) a (b :: xs) ω
        (fun i j =>
          ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω))
            ({j} : Set (Fin k))).toReal)
        hstart
        (fun i => houtω hstart i)
        (fun i j => hfreqω hstart i j)
        (fun i j => hΘposω hstart i j)
        (hgraphω hstart)
    have hmain :=
      tendsto_prefixRatioApproxENN_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_eventually_prefixCompatibleState
        (k := k) a (b :: xs) ω
        (fun i j =>
          ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω))
            ({j} : Set (Fin k))).toReal)
        hcomp
        (fun i => houtω hstart i)
        (fun i j => hfreqω hstart i j)
        (hgraphω hstart)
    have hstep_ne_top :
        rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) ≠ ⊤ := by
      exact ne_of_lt <| lt_of_le_of_lt
        (rowKernelStepProd_le_one (k := k) rowKernel ω (a :: b :: xs))
        (by simp)
    have htarget :
        ENNReal.ofReal
            (prefixThetaPowerProduct (k := k) a (b :: xs)
              (fun i j =>
                ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω))
                  ({j} : Set (Fin k))).toReal)) =
          rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) := by
      rw [prefixThetaPowerProduct_eq_rowKernelStepProd_toReal
        (k := k) a (b :: xs) rowKernel ω
        (fun i j =>
          ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω))
            ({j} : Set (Fin k))).toReal)
        (fun i j => rfl)]
      exact ENNReal.ofReal_toReal hstep_ne_top
    simpa [hstart, htarget] using hmain
  · have hzeroEv :
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω) =ᶠ[Filter.atTop]
          (fun _ : ℕ => (0 : ENNReal)) := by
      exact Filter.Eventually.of_forall (fun r =>
        prefixRatioApproxENN_eq_zero_of_start_ne
          (k := k) a (b :: xs) r ω hstart)
    have hconst :
        Filter.Tendsto (fun _ : ℕ => (0 : ENNReal))
          Filter.atTop
          (nhds
            (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
      simp [hstart]
    exact hconst.congr' hzeroEv.symm

lemma ae_tendsto_prefixRatioApproxENN_of_coordwise_component_limits_of_prefixUsedTransitionSet
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hout :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)))
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  exact
    ae_tendsto_prefixRatioApproxENN_of_coordwise_component_limits
      (k := k) P rowKernel a b xs hout hfreq
      (ae_prefixThetaPos_of_forall_mem_prefixUsedTransitionSet
        (k := k) P rowKernel a (b :: xs) hΘposUsed)
      hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcess_components
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow :
      ∀ i j : Fin k,
        ∀ᵐ r ∂rowProcessLaw (k := k) P i,
          Filter.Tendsto
            (fun m => rowProcessEmpiricalFreq (k := k) j r m)
            Filter.atTop
            (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal)))
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  refine
    ae_tendsto_prefixRatioApproxENN_of_coordwise_component_limits_of_prefixUsedTransitionSet
      (k := k) P rowKernel a b xs
      ?_ ?_ hΘposUsed hgraph
  · exact
      ae_coordwise_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_on_start_of_ae_exists_visit
        (k := k) P hStrong a (b :: xs).length hvisit
  · exact
      ae_coordwise_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_on_start_of_ae_coordwise_tendsto_rowProcessEmpiricalFreq
        (k := k) P rowKernel a hrow

lemma ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcess_components
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hinf :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hrow :
      ∀ i j : Fin k,
        ∀ᵐ r ∂rowProcessLaw (k := k) P i,
          Filter.Tendsto
            (fun m => rowProcessEmpiricalFreq (k := k) j r m)
            Filter.atTop
            (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal)))
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hStrong : StrongRecurrence (k := k) P :=
    strongRecurrence_of_ae_infinite_visits (k := k) P hinf
  have hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i :=
    ae_coordwise_exists_visit_on_start_of_ae_infinite_visits
      (k := k) P a hinf
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcess_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcess_components_of_ae_prefixThetaPos
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hinf :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hrow :
      ∀ i j : Fin k,
        ∀ᵐ r ∂rowProcessLaw (k := k) P i,
          Filter.Tendsto
            (fun m => rowProcessEmpiricalFreq (k := k) j r m)
            Filter.atTop
            (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal)))
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  exact
    ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcess_components
      (k := k) P rowKernel a b xs hinf hrow
      (ae_forall_mem_prefixUsedTransitionSet_of_ae_prefixThetaPos
        (k := k) P rowKernel a (b :: xs) hΘpos)
      hgraph

lemma ae_prefixThetaPosUsed_of_ae_prefixThetaPos
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω) :
    ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
      ∀ᵐ ω ∂P,
        ω 0 = a →
          0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω := by
  exact
    ae_forall_mem_prefixUsedTransitionSet_of_ae_prefixThetaPos
      (k := k) P rowKernel a (b :: xs) hΘpos

lemma rowKernelStepProd_eq_zero_of_exists_mem_prefixUsedTransitionSet_zero
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a : Fin k) (ys : List (Fin k)) (ω : ℕ → Fin k)
    (hzero :
      ∃ p ∈ prefixUsedTransitionSet (k := k) a ys,
        rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω = 0) :
    rowKernelStepProd (k := k) rowKernel ω (a :: ys) = 0 := by
  have htargetZero :
      prefixThetaPowerProduct (k := k) a ys
        (fun i j =>
          ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal) = 0 := by
    exact
      prefixThetaPowerProduct_eq_zero_of_exists_mem_prefixUsedTransitionSet_zero
        (k := k) a ys
        (fun i j =>
          ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)
        hzero
  have hstep_ne_top :
      rowKernelStepProd (k := k) rowKernel ω (a :: ys) ≠ ⊤ := by
    exact ne_of_lt <| lt_of_le_of_lt
      (rowKernelStepProd_le_one (k := k) rowKernel ω (a :: ys))
      (by simp)
  have htoReal :
      (rowKernelStepProd (k := k) rowKernel ω (a :: ys)).toReal = 0 := by
    rw [← prefixThetaPowerProduct_eq_rowKernelStepProd_toReal
      (k := k) a ys rowKernel ω
      (fun i j =>
        ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)
      (fun i j => rfl)]
    exact htargetZero
  rcases (ENNReal.toReal_eq_zero_iff _).1 htoReal with hzeroStep | htop
  · exact hzeroStep
  · exact (hstep_ne_top htop).elim

lemma forall_mem_prefixUsedTransitionSet_pos_or_exists_zero_rowKernelVisitProbReal
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a : Fin k) (ys : List (Fin k)) (ω : ℕ → Fin k) :
    (∀ p ∈ prefixUsedTransitionSet (k := k) a ys,
      0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∨
      ∃ p ∈ prefixUsedTransitionSet (k := k) a ys,
        rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω = 0 := by
  classical
  by_cases hpos :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a ys,
        0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω
  · exact Or.inl hpos
  · push_neg at hpos
    rcases hpos with ⟨p, hp, hnotpos⟩
    have hnonneg :
        0 ≤ rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω := by
      exact ENNReal.toReal_nonneg
    have hzero :
        rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω = 0 := by
      linarith
    exact Or.inr ⟨p, hp, hzero⟩

lemma ae_hout_pathPrefixState_shift_of_strongRecurrence_on_start_of_ae_exists_visit
    (P : MeasureTheory.Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i) :
    ∀ i : Fin k,
      ∀ᵐ ω ∂P, ω 0 = a →
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
          Filter.atTop Filter.atTop := by
  exact
    ae_coordwise_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_on_start_of_ae_exists_visit
      (k := k) P hStrong a (b :: xs).length hvisit

lemma ae_eventually_prefixCompatibleState_pathPrefixState_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop,
          prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
            (Nat.le_add_right (b :: xs).length r)
            (pathPrefixState (k := k) ω ((b :: xs).length + r)) := by
  have houtAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k,
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k,
            ω 0 = a →
              Filter.Tendsto
                (fun r =>
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
                Filter.atTop Filter.atTop := by
      rw [ae_all_iff]
      intro i
      exact
        ae_hout_pathPrefixState_shift_of_strongRecurrence_on_start_of_ae_exists_visit
          (k := k) P hStrong a b xs hvisit i
    filter_upwards [hpack] with ω hω hstart i
    exact hω i hstart
  have hfreqCoord :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) :=
    ae_coordwise_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_on_start_of_rowProcessCoordwiseCesaroLimit
      (k := k) P rowKernel a hrow
  have hfreqAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k, ∀ j : Fin k,
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) :=
    ae_all_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_of_coordwise
      (k := k) P rowKernel a hfreqCoord
  have hΘposAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i j : Fin k,
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω :=
    by
      have hΘposCoord :
          ∀ i j : Fin k,
            ∀ᵐ ω ∂P,
              ω 0 = a →
                0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
                  0 < rowKernelVisitProbReal (k := k) rowKernel i j ω :=
        ae_prefixThetaPos_of_forall_mem_prefixUsedTransitionSet
          (k := k) P rowKernel a (b :: xs) hΘposUsed
      have hpack :
          ∀ᵐ ω ∂P,
            ∀ i : Fin k, ∀ j : Fin k,
              ω 0 = a →
                0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
                  0 < rowKernelVisitProbReal (k := k) rowKernel i j ω := by
        rw [ae_all_iff]
        intro i
        rw [ae_all_iff]
        intro j
        exact hΘposCoord i j
      filter_upwards [hpack] with ω hω hstart i j hij
      exact hω i j hstart hij
  filter_upwards [houtAll, hfreqAll, hΘposAll, hgraph] with ω houtω hfreqω hΘposω hgraphω hstart
  exact
    eventually_prefixCompatibleState_pathPrefixState_of_start_eq_of_ratioData
      (k := k) a (b :: xs) ω
      (fun i j => rowKernelVisitProbReal (k := k) rowKernel i j ω)
      hstart
      (fun i => houtω hstart i)
      (fun i j => hfreqω hstart i j)
      (fun i j => hΘposω hstart i j)
      (hgraphω hstart)

lemma ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixTokenDeletionLowerFactorReal (k := k) a (b :: xs)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have houtAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k,
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k,
            ω 0 = a →
              Filter.Tendsto
                (fun r =>
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
                Filter.atTop Filter.atTop := by
      rw [ae_all_iff]
      intro i
      exact
        ae_hout_pathPrefixState_shift_of_strongRecurrence_on_start_of_ae_exists_visit
          (k := k) P hStrong a b xs hvisit i
    filter_upwards [hpack] with ω hω hstart i
    exact hω i hstart
  have hfreqCoord :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) :=
    ae_coordwise_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_on_start_of_rowProcessCoordwiseCesaroLimit
      (k := k) P rowKernel a hrow
  have hfreqAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k, ∀ j : Fin k,
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) :=
    ae_all_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_of_coordwise
      (k := k) P rowKernel a hfreqCoord
  have hΘposAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i j : Fin k,
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k, ∀ j : Fin k,
            ω 0 = a →
              0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
                0 < rowKernelVisitProbReal (k := k) rowKernel i j ω := by
      rw [ae_all_iff]
      intro i
      rw [ae_all_iff]
      intro j
      exact hΘpos i j
    filter_upwards [hpack] with ω hω hstart i j hij
    exact hω i j hstart hij
  filter_upwards [houtAll, hfreqAll, hΘposAll] with ω houtω hfreqω hΘposω hstart
  have hratio :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun r =>
            ((pathPrefixState (k := k) ω ((b :: xs).length + r)).counts.counts i j : ℝ) /
              (MarkovDeFinettiHardEuler.outdeg (k := k)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)) i : ℝ))
          Filter.atTop
          (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) :=
    pathPrefixState_ratioData_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_outdeg
      (k := k) ω (fun r => (b :: xs).length + r)
      (fun i j => rowKernelVisitProbReal (k := k) rowKernel i j ω)
      (houtω hstart) (hfreqω hstart)
  have houtReal :
      ∀ i : Fin k,
        0 < MarkovDeFinettiHardEuler.outdeg (k := k)
          (prefixWordState (k := k) a (b :: xs)) i →
        Filter.Tendsto
          (fun r =>
            (MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)) i : ℝ))
          Filter.atTop Filter.atTop := by
    intro i _
    exact tendsto_natCast_atTop_atTop.comp (houtω hstart i)
  exact
    tendsto_prefixTokenDeletionLowerFactorReal_of_ratioData
      (k := k) a (b :: xs)
      (e := fun r => pathPrefixState (k := k) ω ((b :: xs).length + r))
      (Θ := fun i j => rowKernelVisitProbReal (k := k) rowKernel i j ω)
      houtReal hratio (hΘposω hstart)

lemma ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixTokenDeletionLowerFactorReal (k := k) a (b :: xs)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  exact
    ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos
      (k := k) P hStrong rowKernel a b xs hvisit hrow
      (ae_prefixThetaPos_of_forall_mem_prefixUsedTransitionSet
        (k := k) P rowKernel a (b :: xs) hΘposUsed)

lemma ae_tendsto_prefixTokenRootedArborescenceRatioReal_shift_of_ae_tendsto_prefixTokenDeletionLowerFactorReal
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hlower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixTokenDeletionLowerFactorReal (k := k) a ys
                (pathPrefixState (k := k) ω (ys.length + r)) ≤
              prefixTokenRootedArborescenceRatioReal (k := k) a ys
                (ys.length + r) (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
    (hupper :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixTokenRootedArborescenceRatioReal (k := k) a ys
                (ys.length + r) (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)) ≤ (1 : ℝ))
    (hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a ys
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixTokenRootedArborescenceRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  filter_upwards [hlower, hupper, hlimLower] with ω hlowω huppω hlimω hstart
  exact
    tendsto_prefixTokenRootedArborescenceRatioReal_of_tendsto_prefixTokenDeletionLowerFactorReal
      (k := k) a ys
      (N := fun r => ys.length + r)
      (hN := fun r => Nat.le_add_right ys.length r)
      (e := fun r => pathPrefixState (k := k) ω (ys.length + r))
      (hlower := hlowω hstart)
      (hupper := huppω hstart)
      (hlim := hlimω hstart)

lemma ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_shift_of_bridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop,
          prefixTokenDeletionLowerFactorReal (k := k) a ys
              (pathPrefixState (k := k) ω (ys.length + r)) ≤
            prefixTokenRootedArborescenceRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)) := by
  filter_upwards [hcomp] with ω hcompω hstart
  exact (hcompω hstart).mono fun r hr =>
    prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_bridge
      (k := k) a ys
      (ys.length + r) (Nat.le_add_right ys.length r)
      (pathPrefixState (k := k) ω (ys.length + r))
      hr hBridge

lemma ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_shift_of_bridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop,
          prefixTokenDeletionLowerFactorReal (k := k) a ys
              (pathPrefixState (k := k) ω (ys.length + r)) ≤
            prefixTokenRootedArborescenceRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)) := by
  filter_upwards [hcomp] with ω hcompω hstart
  exact (hcompω hstart).mono fun r hr =>
    prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_bridgeCard
      (k := k) a ys
      (ys.length + r) (Nat.le_add_right ys.length r)
      (pathPrefixState (k := k) ω (ys.length + r))
      hr hBridgeCard

lemma ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_shift_of_ae_pathPrefixBridgeCardEq_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridge :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            tokenRootedBridgeCardEq (k := k)
              (pathPrefixState (k := k) ω (ys.length + r))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop,
          prefixTokenDeletionLowerFactorReal (k := k) a ys
              (pathPrefixState (k := k) ω (ys.length + r)) ≤
            prefixTokenRootedArborescenceRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)) := by
  filter_upwards [hcomp, hBridge] with ω hcompω hBridgeω hstart
  filter_upwards [hcompω hstart, hBridgeω hstart] with r hrComp hrBridge
  exact
    prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_bridgeCardEq
      (k := k) a ys
      (ys.length + r) (Nat.le_add_right ys.length r)
      (pathPrefixState (k := k) ω (ys.length + r))
      hrComp hrBridge

lemma ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixPositiveTokenRootedArborescenceRatioReal_shift_of_positiveBridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hPositiveBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop,
          prefixTokenDeletionLowerFactorReal (k := k) a ys
              (pathPrefixState (k := k) ω (ys.length + r)) ≤
            prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)) := by
  filter_upwards [hcomp] with ω hcompω hstart
  exact (hcompω hstart).mono fun r hr =>
    prefixTokenDeletionLowerFactorReal_le_prefixPositiveTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_positiveBridgeCard
      (k := k) a ys
      (ys.length + r) (Nat.le_add_right ys.length r)
      (pathPrefixState (k := k) ω (ys.length + r))
      hr hPositiveBridgeCard

lemma ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixPositiveTokenRootedArborescenceRatioReal_shift_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridge :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop,
          prefixTokenDeletionLowerFactorReal (k := k) a ys
              (pathPrefixState (k := k) ω (ys.length + r)) ≤
            prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)) := by
  filter_upwards [hcomp, hBridge] with ω hcompω hBridgeω hstart
  filter_upwards [hcompω hstart, hBridgeω hstart] with r hrComp hrBridge
  exact
    prefixTokenDeletionLowerFactorReal_le_prefixPositiveTokenRootedArborescenceRatioReal_of_prefixCompatibleState_of_positiveBridgeCardEq
      (k := k) a ys
      (ys.length + r) (Nat.le_add_right ys.length r)
      (pathPrefixState (k := k) ω (ys.length + r))
      hrComp hrBridge.1

lemma ae_eventually_prefixTokenRootedArborescenceRatioReal_le_one_shift
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k)) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        ∀ᶠ r in Filter.atTop,
          prefixTokenRootedArborescenceRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)) ≤ (1 : ℝ) := by
  refine Filter.Eventually.of_forall ?_
  intro ω _
  exact Filter.Eventually.of_forall fun r =>
    prefixTokenRootedArborescenceRatioReal_le_one
      (k := k) a ys
      (ys.length + r) (Nat.le_add_right ys.length r)
      (pathPrefixState (k := k) ω (ys.length + r))

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixTokenRootedArborescenceRatioReal_of_bridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last)
    (htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenRootedArborescenceRatioReal (k := k) a ys
                (ys.length + r) (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  filter_upwards [hcomp, htok] with ω hcompω htokω hstart
  exact
    tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_tendsto_prefixTokenRootedArborescenceRatioReal_of_bridge
      (k := k) a ys
      (e := fun r => pathPrefixState (k := k) ω (ys.length + r))
      (Nf := fun r => ys.length + r)
      (hN := fun r => Nat.le_add_right ys.length r)
      (hcomp := hcompω hstart)
      (hBridge := hBridge)
      (hlim := htokω hstart)

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixTokenRootedArborescenceRatioReal_of_bridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s)
    (htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenRootedArborescenceRatioReal (k := k) a ys
                (ys.length + r) (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  filter_upwards [hcomp, htok] with ω hcompω htokω hstart
  exact
    tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_tendsto_prefixTokenRootedArborescenceRatioReal_of_bridge
      (k := k) a ys
      (e := fun r => pathPrefixState (k := k) ω (ys.length + r))
      (Nf := fun r => ys.length + r)
      (hN := fun r => Nat.le_add_right ys.length r)
      (hcomp := hcompω hstart)
      (hBridge := fun {_M} {_s} hs =>
        normalizedEulerTrailCorrection_eq_tokenRootedArborescenceCount_of_card_eq
          (k := k) (hBridgeCard hs))
      (hlim := htokω hstart)

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last)
    (hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a ys
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
          (fun r =>
              prefixTokenRootedArborescenceRatioReal (k := k) a ys
                (ys.length + r) (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenRootedArborescenceRatioReal_shift_of_ae_tendsto_prefixTokenDeletionLowerFactorReal
      (k := k) P a ys
      (ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_shift_of_bridge_of_eventually_prefixCompatibleState
        (k := k) P a ys hcomp hBridge)
      (ae_eventually_prefixTokenRootedArborescenceRatioReal_le_one_shift
        (k := k) P a ys)
      hlimLower
  exact
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixTokenRootedArborescenceRatioReal_of_bridge_of_eventually_prefixCompatibleState
      (k := k) P a ys hcomp hBridge htok

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s)
    (hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a ys
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
          (fun r =>
              prefixTokenRootedArborescenceRatioReal (k := k) a ys
                (ys.length + r) (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenRootedArborescenceRatioReal_shift_of_ae_tendsto_prefixTokenDeletionLowerFactorReal
      (k := k) P a ys
      (ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_shift_of_bridgeCard_of_eventually_prefixCompatibleState
        (k := k) P a ys hcomp hBridgeCard)
      (ae_eventually_prefixTokenRootedArborescenceRatioReal_le_one_shift
        (k := k) P a ys)
      hlimLower
  exact
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixTokenRootedArborescenceRatioReal_of_bridgeCard_of_eventually_prefixCompatibleState
      (k := k) P a ys hcomp hBridgeCard htok

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixTokenRootedArborescenceRatioReal_of_ae_pathPrefixBridgeCardEqPair
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hBridgePair :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop, pathPrefixBridgeCardEqPair (k := k) a ys ω r)
    (htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenRootedArborescenceRatioReal (k := k) a ys
                (ys.length + r) (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  filter_upwards [hBridgePair, htok] with ω hBridgeω htokω hstart
  exact
    tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_tendsto_prefixTokenRootedArborescenceRatioReal_of_bridgeCardEq_pair
      (k := k) a ys
      (e := fun r => pathPrefixState (k := k) ω (ys.length + r))
      (Nf := fun r => ys.length + r)
      (hN := fun r => Nat.le_add_right ys.length r)
      (hBridgePair := hBridgeω hstart)
      (hlim := htokω hstart)

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixBridgeCardEqPair_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgePair :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            pathPrefixBridgeCardEqPair (k := k) a (b :: xs) ω r) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal
              (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a (b :: xs)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed
  have hBridgeFull :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            tokenRootedBridgeCardEq (k := k)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)) := by
    filter_upwards [hBridgePair] with ω hBridgeω hstart
    filter_upwards [hBridgeω hstart] with r hr
    exact hr.1
  have htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenRootedArborescenceRatioReal (k := k) a (b :: xs)
                ((b :: xs).length + r) (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenRootedArborescenceRatioReal_shift_of_ae_tendsto_prefixTokenDeletionLowerFactorReal
      (k := k) P a (b :: xs)
      (ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_shift_of_ae_pathPrefixBridgeCardEq_of_eventually_prefixCompatibleState
        (k := k) P a (b :: xs) hcomp hBridgeFull)
      (ae_eventually_prefixTokenRootedArborescenceRatioReal_le_one_shift
        (k := k) P a (b :: xs))
      hlimLower
  exact
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixTokenRootedArborescenceRatioReal_of_ae_pathPrefixBridgeCardEqPair
      (k := k) P a (b :: xs) hBridgePair htok

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_ae_pathPrefixPositiveBridgeCardEqPair
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hBridgePair :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop, pathPrefixPositiveBridgeCardEqPair (k := k) a ys ω r)
    (htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys
                (ys.length + r) (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  filter_upwards [hBridgePair, htok] with ω hBridgeω htokω hstart
  exact
    tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_positiveBridgeCardEq_pair
      (k := k) a ys
      (e := fun r => pathPrefixState (k := k) ω (ys.length + r))
      (Nf := fun r => ys.length + r)
      (hN := fun r => Nat.le_add_right ys.length r)
      (hBridgePair := hBridgeω hstart)
      (hlim := htokω hstart)

lemma tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_tendsto_prefixTokenRootedArborescenceRatioReal_of_eventually_prefixCompatibleState_of_tendsto_outdeg
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k)
    (hcomp :
      ∀ᶠ r in Filter.atTop,
        prefixCompatibleState (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)))
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i)
          Filter.atTop Filter.atTop)
    (htok :
      Filter.Tendsto
        (fun r =>
          prefixTokenRootedArborescenceRatioReal (k := k) a ys
            (ys.length + r) (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun r =>
        prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys
          (ys.length + r) (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)))
      Filter.atTop (nhds (1 : ℝ)) := by
  apply Filter.Tendsto.congr' ?_ htok
  exact
    (eventually_eq_prefixPositiveTokenRootedArborescenceRatioReal_of_prefixTokenRootedArborescenceRatioReal_of_eventually_prefixCompatibleState_of_eventually_forall_outdeg_gt_prefixWordState_outdeg
      (k := k) a ys ω hcomp
      (eventually_forall_outdeg_gt_prefixWordState_outdeg_of_tendsto
        (k := k) a ys
        (e := fun r => pathPrefixState (k := k) ω (ys.length + r)) hout)).symm

lemma ae_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_shift_of_ae_tendsto_prefixTokenRootedArborescenceRatioReal_of_ae_eventually_prefixCompatibleState_of_ae_tendsto_outdeg
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hout :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω (ys.length + r)) i)
              Filter.atTop Filter.atTop)
    (htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenRootedArborescenceRatioReal (k := k) a ys
                (ys.length + r) (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixPositiveTokenRootedArborescenceRatioReal (k := k) a ys
              (ys.length + r) (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have houtAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k,
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω (ys.length + r)) i)
              Filter.atTop Filter.atTop := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k,
            ω 0 = a →
              Filter.Tendsto
                (fun r =>
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (pathPrefixState (k := k) ω (ys.length + r)) i)
                Filter.atTop Filter.atTop := by
      rw [ae_all_iff]
      intro i
      exact hout i
    filter_upwards [hpack] with ω hω hstart i
    exact hω i hstart
  filter_upwards [hcomp, houtAll, htok] with ω hcompω houtω htokω hstart
  exact
    tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_tendsto_prefixTokenRootedArborescenceRatioReal_of_eventually_prefixCompatibleState_of_tendsto_outdeg
      (k := k) a ys ω (hcompω hstart) (houtω hstart) (htokω hstart)

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal
              (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a (b :: xs)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘpos
  exact
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
      (k := k) P a (b :: xs) hcomp hBridge hlimLower

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal
              (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a (b :: xs)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘpos
  exact
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
      (k := k) P a (b :: xs) hcomp hBridgeCard hlimLower

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal
              (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a (b :: xs)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed
  exact
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
      (k := k) P a (b :: xs) hcomp hBridge hlimLower

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal
              (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a (b :: xs)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed
  exact
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
      (k := k) P a (b :: xs) hcomp hBridgeCard hlimLower

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgePos :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            pathPrefixPositiveBridgeCardEqPair (k := k) a (b :: xs) ω r) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal
              (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  have hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a (b :: xs)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed
  have hout :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop :=
    fun i =>
      ae_hout_pathPrefixState_shift_of_strongRecurrence_on_start_of_ae_exists_visit
        (k := k) P hStrong a b xs hvisit i
  have hBridgePair :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            pathPrefixBridgeCardEqPair (k := k) a (b :: xs) ω r :=
    ae_eventually_pathPrefixBridgeCardEqPair_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState_of_ae_tendsto_outdeg
      (k := k) P a (b :: xs) hcomp hBridgePos hout
  have hBridgeFull :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            tokenRootedBridgeCardEq (k := k)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)) := by
    filter_upwards [hBridgePair] with ω hBridgeω hstart
    filter_upwards [hBridgeω hstart] with r hr
    exact hr.1
  have htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenRootedArborescenceRatioReal (k := k) a (b :: xs)
                ((b :: xs).length + r) (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenRootedArborescenceRatioReal_shift_of_ae_tendsto_prefixTokenDeletionLowerFactorReal
      (k := k) P a (b :: xs)
      (ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_shift_of_ae_pathPrefixBridgeCardEq_of_eventually_prefixCompatibleState
        (k := k) P a (b :: xs) hcomp hBridgeFull)
      (ae_eventually_prefixTokenRootedArborescenceRatioReal_le_one_shift
        (k := k) P a (b :: xs))
      hlimLower
  have htokPos :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixPositiveTokenRootedArborescenceRatioReal (k := k) a (b :: xs)
                ((b :: xs).length + r) (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_shift_of_ae_tendsto_prefixTokenRootedArborescenceRatioReal_of_ae_eventually_prefixCompatibleState_of_ae_tendsto_outdeg
      (k := k) P a (b :: xs) hcomp hout htok
  exact
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_ae_pathPrefixPositiveBridgeCardEqPair
      (k := k) P a (b :: xs) hBridgePos htokPos

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hPositiveBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal
              (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  exact
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hcomp
      (ae_eventually_pathPrefixPositiveBridgeCardEqPair_of_globalPositiveBridgeCard_of_eventually_prefixCompatibleState
        (k := k) P a (b :: xs) hcomp
        (fun {_M} {_s} hs => hPositiveBridgeCard hs))

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcess_components
      (k := k) P hStrong rowKernel a b xs hvisit
      (fun i j => hrow i j) hΘposUsed hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow
      (ae_prefixThetaPosUsed_of_ae_prefixThetaPos
        (k := k) P rowKernel a b xs hΘpos)
      hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcessCoordwise_components
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hinf :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  exact
    ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcess_components
      (k := k) P rowKernel a b xs hinf (fun i j => hrow i j) hΘposUsed hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcessCoordwise_components_of_ae_prefixThetaPos
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hinf :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω)
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  exact
    ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcessCoordwise_components
      (k := k) P rowKernel a b xs hinf hrow
      (ae_prefixThetaPosUsed_of_ae_prefixThetaPos
        (k := k) P rowKernel a b xs hΘpos)
      hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘpos hcomp hBridge
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘpos hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘpos hcomp hBridgeCard
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘpos hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hcomp hBridge
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
      (k := k) P a (b :: xs) hcomp hBridgeCard
      (ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed
        (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed)
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixBridgeCardEqPair_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgePair :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            pathPrefixBridgeCardEqPair (k := k) a (b :: xs) ω r) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hlimLower :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenDeletionLowerFactorReal (k := k) a (b :: xs)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenDeletionLowerFactorReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed
  have hBridgeFull :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            tokenRootedBridgeCardEq (k := k)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)) := by
    filter_upwards [hBridgePair] with ω hBridgeω hstart
    filter_upwards [hBridgeω hstart] with r hr
    exact hr.1
  have htok :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixTokenRootedArborescenceRatioReal (k := k) a (b :: xs)
                ((b :: xs).length + r) (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixTokenRootedArborescenceRatioReal_shift_of_ae_tendsto_prefixTokenDeletionLowerFactorReal
      (k := k) P a (b :: xs)
      (ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixTokenRootedArborescenceRatioReal_shift_of_ae_pathPrefixBridgeCardEq_of_eventually_prefixCompatibleState
        (k := k) P a (b :: xs) hcomp hBridgeFull)
      (ae_eventually_prefixTokenRootedArborescenceRatioReal_le_one_shift
        (k := k) P a (b :: xs))
      hlimLower
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixTokenRootedArborescenceRatioReal_of_ae_pathPrefixBridgeCardEqPair
      (k := k) P a (b :: xs) hBridgePair htok
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hPositiveBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hcomp hPositiveBridgeCard
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgePos :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            pathPrefixPositiveBridgeCardEqPair (k := k) a (b :: xs) ω r) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hcomp hBridgePos
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_ae_pathPrefixPositiveBridgeCardEqPair
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hBridgePair :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            pathPrefixPositiveBridgeCardEqPair (k := k) a (b :: xs) ω r)
    (htokPos :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixPositiveTokenRootedArborescenceRatioReal (k := k) a (b :: xs)
                ((b :: xs).length + r) (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_ae_pathPrefixPositiveBridgeCardEqPair
      (k := k) P a (b :: xs) hBridgePair htokPos
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hinf :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hStrong : StrongRecurrence (k := k) P :=
    strongRecurrence_of_ae_infinite_visits (k := k) P hinf
  have hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i :=
    ae_coordwise_exists_visit_on_start_of_ae_infinite_visits
      (k := k) P a hinf
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘpos hcomp hBridge

lemma ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hinf :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridge :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          normalizedEulerTrailCorrection (k := k) s =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hStrong : StrongRecurrence (k := k) P :=
    strongRecurrence_of_ae_infinite_visits (k := k) P hinf
  have hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i :=
    ae_coordwise_exists_visit_on_start_of_ae_infinite_visits
      (k := k) P a hinf
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hcomp hBridge

lemma ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hinf :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘpos :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
              0 < rowKernelVisitProbReal (k := k) rowKernel i j ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i :=
    ae_coordwise_exists_visit_on_start_of_ae_infinite_visits
      (k := k) P a hinf
  have hStrong : StrongRecurrence (k := k) P :=
    strongRecurrence_of_ae_infinite_visits (k := k) P hinf
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPos_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘpos hcomp hBridgeCard

lemma ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hinf :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i :=
    ae_coordwise_exists_visit_on_start_of_ae_infinite_visits
      (k := k) P a hinf
  have hStrong : StrongRecurrence (k := k) P :=
    strongRecurrence_of_ae_infinite_visits (k := k) P hinf
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hcomp hBridgeCard

lemma tendsto_prefixRatioApproxENN_of_start_eq_to_rowKernelStepProd_of_eventually_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (Θ : Fin k → Fin k → ℝ)
    (hstart : ω 0 = a)
    (hcomp :
      ∀ᶠ r in Filter.atTop,
        prefixCompatibleState (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)))
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i)
          Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop (nhds (Θ i j)))
    (hgraph :
      Filter.Tendsto
        (fun r =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop (nhds (1 : ℝ)))
    (hΘ :
      ∀ i j, Θ i j =
        ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω))
          ({j} : Set (Fin k))).toReal) :
    Filter.Tendsto
      (fun r => prefixRatioApproxENN (k := k) a ys r ω)
      Filter.atTop
      (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: ys) else 0)) := by
  have hmain :=
    tendsto_prefixRatioApproxENN_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_eventually_prefixCompatibleState
      (k := k) a ys ω Θ hcomp hout hfreq hgraph
  have hstep_ne_top :
      rowKernelStepProd (k := k) rowKernel ω (a :: ys) ≠ ⊤ := by
    exact ne_of_lt <| lt_of_le_of_lt
      (rowKernelStepProd_le_one (k := k) rowKernel ω (a :: ys))
      (by simp)
  have htarget :
      ENNReal.ofReal (prefixThetaPowerProduct (k := k) a ys Θ) =
        rowKernelStepProd (k := k) rowKernel ω (a :: ys) := by
    rw [prefixThetaPowerProduct_eq_rowKernelStepProd_toReal
      (k := k) a ys rowKernel ω Θ hΘ]
    exact ENNReal.ofReal_toReal hstep_ne_top
  simpa [hstart, htarget] using hmain

lemma tendsto_prefixRatioApproxENN_to_zero_of_eventually_prefixCompatibleState_of_exists_zero_rowKernelVisitProbReal
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hcomp :
      ∀ᶠ r in Filter.atTop,
        prefixCompatibleState (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)))
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i)
          Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop
          (nhds (((rowKernel i
            (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)))
    (hgraph :
      Filter.Tendsto
        (fun r =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop (nhds (1 : ℝ)))
    (hzero :
      ∃ p ∈ prefixUsedTransitionSet (k := k) a ys,
        rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω = 0) :
    Filter.Tendsto
      (fun r => prefixRatioApproxENN (k := k) a ys r ω)
      Filter.atTop (nhds (0 : ENNReal)) := by
  have hmain :=
    tendsto_prefixRatioApproxENN_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_eventually_prefixCompatibleState
      (k := k) a ys ω
      (fun i j =>
        ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)
      hcomp hout hfreq hgraph
  have htargetZero :
      prefixThetaPowerProduct (k := k) a ys
        (fun i j =>
          ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal) = 0 := by
    exact
      prefixThetaPowerProduct_eq_zero_of_exists_mem_prefixUsedTransitionSet_zero
        (k := k) a ys
        (fun i j =>
          ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)
        hzero
  simpa [htargetZero] using hmain

lemma tendsto_prefixRatioApproxENN_of_start_eq_of_rowKernelVisitSupportSplit_of_eventually_prefixCompatibleState
    (a : Fin k) (ys : List (Fin k))
    (ω : ℕ → Fin k)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hstart : ω 0 = a)
    (hcomp :
      ∀ᶠ r in Filter.atTop,
        prefixCompatibleState (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r)))
    (hout :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun r =>
            MarkovDeFinettiHardEuler.outdeg (k := k)
              (pathPrefixState (k := k) ω (ys.length + r)) i)
          Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        Filter.Tendsto
          (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
          Filter.atTop
          (nhds (((rowKernel i
            (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)))
    (hgraph :
      Filter.Tendsto
        (fun r =>
          prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) a ys (ys.length + r)
            (Nat.le_add_right ys.length r)
            (pathPrefixState (k := k) ω (ys.length + r)))
        Filter.atTop (nhds (1 : ℝ))) :
    Filter.Tendsto
      (fun r => prefixRatioApproxENN (k := k) a ys r ω)
      Filter.atTop
      (nhds (rowKernelStepProd (k := k) rowKernel ω (a :: ys))) := by
  rcases forall_mem_prefixUsedTransitionSet_pos_or_exists_zero_rowKernelVisitProbReal
      (k := k) rowKernel a ys ω with hposUsed | hzero
  · have hΘpos :
        ∀ i j : Fin k,
          0 < (prefixWordState (k := k) a ys).counts.counts i j →
            0 < rowKernelVisitProbReal (k := k) rowKernel i j ω :=
      prefixThetaPos_of_forall_mem_prefixUsedTransitionSet
        (k := k) rowKernel a ys ω hposUsed
    have hlimLower :
        Filter.Tendsto
          (fun r =>
            prefixTokenDeletionLowerFactorReal (k := k) a ys
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) :=
      tendsto_prefixTokenDeletionLowerFactorReal_of_ratioData
        (k := k) a ys
        (e := fun r => pathPrefixState (k := k) ω (ys.length + r))
        (Θ := fun i j => rowKernelVisitProbReal (k := k) rowKernel i j ω)
        (hout := by
          intro i _
          exact tendsto_natCast_atTop_atTop.comp (hout i))
        (hratio := by
          exact pathPrefixState_ratioData_of_tendsto_rowSuccessorEmpiricalFreq_of_tendsto_outdeg
            (k := k) ω (fun r => ys.length + r)
            (fun i j => rowKernelVisitProbReal (k := k) rowKernel i j ω)
            hout hfreq)
        hΘpos
    have _ :
        Filter.Tendsto
          (fun r =>
            prefixTokenDeletionLowerFactorReal (k := k) a ys
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := hlimLower
    simpa [hstart] using
      tendsto_prefixRatioApproxENN_of_start_eq_to_rowKernelStepProd_of_eventually_prefixCompatibleState
        (k := k) a ys ω rowKernel
        (fun i j =>
          ((rowKernel i (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)
        hstart hcomp hout hfreq hgraph (fun i j => rfl)
  · have hzeroLim :
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a ys r ω)
        Filter.atTop (nhds (0 : ENNReal)) :=
      tendsto_prefixRatioApproxENN_to_zero_of_eventually_prefixCompatibleState_of_exists_zero_rowKernelVisitProbReal
        (k := k) a ys ω rowKernel hcomp hout hfreq hgraph hzero
    have hstepZero :
        rowKernelStepProd (k := k) rowKernel ω (a :: ys) = 0 :=
      rowKernelStepProd_eq_zero_of_exists_mem_prefixUsedTransitionSet_zero
        (k := k) rowKernel a ys ω hzero
    simpa [hstepZero] using hzeroLim

lemma ae_tendsto_prefixRatioApproxENN_to_zero_of_ae_eventually_prefixCompatibleState_of_ae_exists_zero_rowKernelVisitProbReal
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hout :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)))
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)))
    (hzero :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∃ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
            rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω = 0) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
          Filter.atTop (nhds (0 : ENNReal)) := by
  have houtAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k,
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k,
            ω 0 = a →
              Filter.Tendsto
                (fun r =>
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
                Filter.atTop Filter.atTop := by
      rw [ae_all_iff]
      intro i
      exact hout i
    filter_upwards [hpack] with ω hω hstart i
    exact hω i hstart
  have hfreqAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k, ∀ j : Fin k,
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (rowKernelVisitProbReal (k := k) rowKernel i j ω)) :=
    ae_all_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_of_coordwise
      (k := k) P rowKernel a hfreq
  filter_upwards [hcomp, houtAll, hfreqAll, hgraph, hzero] with
    ω hcompω houtω hfreqω hgraphω hzeroω hstart
  exact
    tendsto_prefixRatioApproxENN_to_zero_of_eventually_prefixCompatibleState_of_exists_zero_rowKernelVisitProbReal
      (k := k) a (b :: xs) ω rowKernel
      (hcompω hstart)
      (fun i => houtω hstart i)
      (fun i j => hfreqω hstart i j)
      (hgraphω hstart)
      (hzeroω hstart)

lemma ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixNormalizedBridgeProductReal_of_ae_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hbridgeNorm :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedBridgeProductReal
                (k := k) a ys (ys.length + r)
                (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedEulerTrailCorrectionRatioReal
              (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  filter_upwards [hcomp, hbridgeNorm] with ω hcompω hbridgeω hstart
  have hEq :
      (fun r =>
        prefixNormalizedBridgeProductReal
          (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r))) =ᶠ[Filter.atTop]
      (fun r =>
        prefixNormalizedEulerTrailCorrectionRatioReal
          (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r))) := by
    exact (hcompω hstart).mono fun r hr =>
      prefixNormalizedBridgeProductReal_eq_prefixNormalizedEulerTrailCorrectionRatioReal_of_prefixCompatibleState
        (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)) hr
  exact (hbridgeω hstart).congr' hEq

lemma ae_tendsto_prefixNormalizedBridgeProductReal_shift_of_ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_of_ae_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (a : Fin k) (ys : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a ys (ys.length + r)
                (Nat.le_add_right ys.length r)
                (pathPrefixState (k := k) ω (ys.length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      ω 0 = a →
        Filter.Tendsto
          (fun r =>
            prefixNormalizedBridgeProductReal
              (k := k) a ys (ys.length + r)
              (Nat.le_add_right ys.length r)
              (pathPrefixState (k := k) ω (ys.length + r)))
          Filter.atTop (nhds (1 : ℝ)) := by
  filter_upwards [hcomp, hgraph] with ω hcompω hgraphω hstart
  have hEq :
      (fun r =>
        prefixNormalizedBridgeProductReal
          (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r))) =ᶠ[Filter.atTop]
      (fun r =>
        prefixNormalizedEulerTrailCorrectionRatioReal
          (k := k) a ys (ys.length + r)
          (Nat.le_add_right ys.length r)
          (pathPrefixState (k := k) ω (ys.length + r))) := by
    exact (hcompω hstart).mono fun r hr =>
      prefixNormalizedBridgeProductReal_eq_prefixNormalizedEulerTrailCorrectionRatioReal_of_prefixCompatibleState
        (k := k) a ys (ys.length + r) (Nat.le_add_right ys.length r)
        (pathPrefixState (k := k) ω (ys.length + r)) hr
  exact (hgraphω hstart).congr' hEq.symm

theorem ae_tendsto_prefixRatioApproxENN_of_coordwise_component_limits_of_ae_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hout :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop)
    (hfreq :
      ∀ i j : Fin k,
        ∀ᵐ ω ∂P,
          ω 0 = a →
            Filter.Tendsto
              (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
              Filter.atTop
              (nhds (((rowKernel i
                (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal)))
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have houtAll :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ i : Fin k,
            Filter.Tendsto
              (fun r =>
                MarkovDeFinettiHardEuler.outdeg (k := k)
                  (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
              Filter.atTop Filter.atTop := by
    have hpack :
        ∀ᵐ ω ∂P,
          ∀ i : Fin k,
            ω 0 = a →
              Filter.Tendsto
                (fun r =>
                  MarkovDeFinettiHardEuler.outdeg (k := k)
                    (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
                Filter.atTop Filter.atTop := by
      rw [ae_all_iff]
      intro i
      exact hout i
    filter_upwards [hpack] with ω hω hstart i
    exact hω i hstart
  have hfreqAll :=
    ae_all_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_of_coordwise
      (k := k) P rowKernel a hfreq
  filter_upwards [hcomp, houtAll, hfreqAll, hgraph] with ω hcompω houtω hfreqω hgraphω
  by_cases hstart : ω 0 = a
  · simpa [hstart] using
      tendsto_prefixRatioApproxENN_of_start_eq_of_rowKernelVisitSupportSplit_of_eventually_prefixCompatibleState
        (k := k) a (b :: xs) ω rowKernel hstart
        (hcompω hstart)
        (fun i => houtω hstart i)
        (fun i j => hfreqω hstart i j)
        (hgraphω hstart)
  · have hzeroEv :
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω) =ᶠ[Filter.atTop]
          (fun _ : ℕ => (0 : ENNReal)) := by
      exact Filter.Eventually.of_forall (fun r =>
        prefixRatioApproxENN_eq_zero_of_start_ne
          (k := k) a (b :: xs) r ω hstart)
    have hconst :
        Filter.Tendsto (fun _ : ℕ => (0 : ENNReal))
          Filter.atTop
          (nhds
            (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
      simp [hstart]
    exact hconst.congr' hzeroEv.symm

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  refine
    ae_tendsto_prefixRatioApproxENN_of_coordwise_component_limits_of_ae_eventually_prefixCompatibleState
      (k := k) P rowKernel a b xs hcomp ?_ ?_ hgraph
  · exact
      ae_coordwise_tendsto_outdeg_pathPrefixState_shift_atTop_of_strongRecurrence_on_start_of_ae_exists_visit
        (k := k) P hStrong a (b :: xs).length hvisit
  · exact
      ae_coordwise_tendsto_rowSuccessorEmpiricalFreq_to_rowKernelEval_on_start_of_rowProcessCoordwiseCesaroLimit
        (k := k) P rowKernel a hrow

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState_of_ae_tendsto_prefixNormalizedBridgeProductReal
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hbridgeNorm :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedBridgeProductReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ))) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hcomp
      (ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixNormalizedBridgeProductReal_of_ae_eventually_prefixCompatibleState
        (k := k) P a (b :: xs) hcomp hbridgeNorm)

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState_via_supportSplit
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hPositiveBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hcomp hPositiveBridgeCard
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hcomp hgraph

lemma ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState_via_supportSplit
    (P : Measure (ℕ → Fin k))
    (hStrong : StrongRecurrence (k := k) P)
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hvisit :
      ∀ i : Fin k,
        ∀ᵐ ω ∂P, ω 0 = a → ∃ t : ℕ, ω t = i)
    (hrow : RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hΘposUsed :
      ∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
        ∀ᵐ ω ∂P,
          ω 0 = a →
            0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω)
    (hcomp :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
              (Nat.le_add_right (b :: xs).length r)
              (pathPrefixState (k := k) ω ((b :: xs).length + r)))
    (hBridgePos :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          ∀ᶠ r in Filter.atTop,
            pathPrefixPositiveBridgeCardEqPair (k := k) a (b :: xs) ω r) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
        Filter.atTop
        (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)) := by
  have hgraph :
      ∀ᵐ ω ∂P,
        ω 0 = a →
          Filter.Tendsto
            (fun r =>
              prefixNormalizedEulerTrailCorrectionRatioReal
                (k := k) a (b :: xs) ((b :: xs).length + r)
                (Nat.le_add_right (b :: xs).length r)
                (pathPrefixState (k := k) ω ((b :: xs).length + r)))
            Filter.atTop (nhds (1 : ℝ)) :=
    ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hcomp hBridgePos
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit hrow hcomp hgraph

/-- Conditional DCT step for the direct conditioned-prefix route: once the
prefix-ratio approximants converge almost surely to the start-indicator
row-kernel product, the length-≥2 cylinder identity follows. -/
lemma cylinder_cons_eq_lintegral_startIndicator_rowKernelStepProd_of_ae_tendsto_prefixRatioApproxENN
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k),
      μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (a b : Fin k) (xs : List (Fin k))
    (hlim :
      ∀ᵐ ω ∂P,
        Filter.Tendsto
          (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
          Filter.atTop
          (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0))) :
    P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: xs)) =
      ∫⁻ ω,
        (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P := by
  have hFmeas :
      ∀ r, AEMeasurable (prefixRatioApproxENN (k := k) a (b :: xs) r) P := by
    intro r
    exact aemeasurable_prefixRatioApproxENN (k := k) P a (b :: xs) r
  have hbound :
      ∀ r,
        prefixRatioApproxENN (k := k) a (b :: xs) r ≤ᵐ[P]
          (fun _ : ℕ → Fin k => (1 : ENNReal)) := by
    intro r
    exact Filter.Eventually.of_forall
      (fun ω => prefixRatioApproxENN_le_one (k := k) a (b :: xs) r ω)
  have hfin :
      (∫⁻ ω, (1 : ENNReal) ∂P) ≠ ⊤ := by
    have hI : (∫⁻ ω, (1 : ENNReal) ∂P) = 1 := by
      simp
    rw [hI]
    simp
  have hconv :
      Filter.Tendsto
        (fun r => ∫⁻ ω, prefixRatioApproxENN (k := k) a (b :: xs) r ω ∂P)
        Filter.atTop
        (nhds
          (∫⁻ ω,
            (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P)) := by
    exact MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun _ : ℕ → Fin k => (1 : ENNReal))
      hFmeas hbound hfin hlim
  have hexact :
      Filter.Tendsto
        (fun r => ∫⁻ ω, prefixRatioApproxENN (k := k) a (b :: xs) r ω ∂P)
        Filter.atTop
        (nhds (μ (a :: b :: xs))) :=
    tendsto_lintegral_prefixRatioApproxENN
      (k := k) (μ := μ) hμ P hExt a (b :: xs)
  have hEqIntegral :
      μ (a :: b :: xs) =
        ∫⁻ ω,
          (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P := by
    exact tendsto_nhds_unique hexact hconv
  exact (hExt (a :: b :: xs)).symm.trans hEqIntegral

lemma cylinderMixingIdentity_P_of_ae_tendsto_prefixRatioApproxENN
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k),
      μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hlim :
      ∀ (a b : Fin k) (xs : List (Fin k)),
        ∀ᵐ ω ∂P,
          Filter.Tendsto
            (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
            Filter.atTop
            (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0))) :
    CylinderMixingIdentity_P (k := k) P rowKernel := by
  intro ws hlen
  cases ws with
  | nil =>
      simp at hlen
  | cons a rest =>
      cases rest with
      | nil =>
          simp at hlen
      | cons b xs =>
          calc
            P (MarkovDeFinettiRecurrence.cylinder (k := k) (a :: b :: xs)) =
              ∫⁻ ω,
                (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0) ∂P := by
                  exact
                    cylinder_cons_eq_lintegral_startIndicator_rowKernelStepProd_of_ae_tendsto_prefixRatioApproxENN
                      (k := k) (μ := μ) hμ P hExt rowKernel a b xs (hlim a b xs)
            _ =
              ∫⁻ ω,
                wordProb (k := k)
                  (rowKernelToMarkovParam (k := k)
                    (initKernel := fun ω => ⟨Measure.dirac (ω 0), Measure.dirac.isProbabilityMeasure⟩)
                    (liftedRowKernelFromRowProcess (k := k) rowKernel) ω)
                  (a :: b :: xs) ∂P := by
                    refine lintegral_congr_ae ?_
                    filter_upwards with ω
                    symm
                    exact wordProb_rowKernelToMarkovParam_eq_indicator_stepProd
                      (k := k) rowKernel ω a b xs

theorem rowSuccessorMatrixInvariance_of_ae_tendsto_prefixRatioApproxENN
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k),
      μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hlim :
      ∀ (a b : Fin k) (xs : List (Fin k)),
        ∀ᵐ ω ∂P,
          Filter.Tendsto
            (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
            Filter.atTop
            (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0))) :
    RowSuccessorMatrixInvariance (k := k) P rowKernel := by
  exact cylinderMixingIdentity_P_of_ae_tendsto_prefixRatioApproxENN
    (k := k) (μ := μ) hμ P hExt rowKernel hlim

theorem builtRowKernelOnExtension_of_ae_tendsto_prefixRatioApproxENN
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k)) [IsProbabilityMeasure P]
    (hExt : ∀ xs : List (Fin k),
      μ xs = P (MarkovDeFinettiRecurrence.cylinder (k := k) xs))
    (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k))
    (hEval :
      ∀ i : Fin k, ∀ b : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
          (rowProcessLaw (k := k) P i))
    (hstart : StartRestrictedRowKernelData (k := k) P rowKernel)
    (hPi :
      ∀ i : Fin k,
        AEMeasurable
          (fun r : ℕ → Fin k =>
            Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
          (rowProcessLaw (k := k) P i))
    (hlim :
      ∀ (a b : Fin k) (xs : List (Fin k)),
        ∀ᵐ ω ∂P,
          Filter.Tendsto
            (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
            Filter.atTop
            (nhds (if ω 0 = a then rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0))) :
    BuiltRowKernelOnExtension (k := k) P rowKernel := by
  refine builtRowKernelOnExtension_of_components
    (k := k) P rowKernel hEval hstart hPi ?_
  exact rowSuccessorMatrixInvariance_of_ae_tendsto_prefixRatioApproxENN
    (k := k) (μ := μ) hμ P hExt rowKernel hlim

theorem buildRowKernelOnRecurrentExtension_of_coordwise_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hrecAe : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0}),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    Filter.Tendsto
                      (fun r =>
                        MarkovDeFinettiHardEuler.outdeg (k := k)
                          (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
                      Filter.atTop Filter.atTop) ∧
              (∀ i j : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    Filter.Tendsto
                      (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
                      Filter.atTop
                      (nhds (((rowKernel i
                        (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal))) ∧
              (∀ i j : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
                      0 < ((rowKernel i
                        (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    BuildRowKernelOnRecurrentExtension k := by
  intro μ hμ P hP hExt hrecAe
  rcases hLocal μ hμ P hP hExt hrecAe with
    ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
  refine ⟨rowKernel, ?_⟩
  refine builtRowKernelOnExtension_of_ae_tendsto_prefixRatioApproxENN
    (k := k) (μ := μ) hμ P hExt rowKernel hEval hstart hPi ?_
  intro a b xs
  rcases hcomp a b xs with ⟨hout, hfreq, hΘpos, hgraph⟩
  exact ae_tendsto_prefixRatioApproxENN_of_coordwise_component_limits
    (k := k) P rowKernel a b xs hout hfreq hΘpos hgraph

theorem fortiniSuccessorMatrixInvarianceTheorem_of_coordwise_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hrecAe : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0}),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    Filter.Tendsto
                      (fun r =>
                        MarkovDeFinettiHardEuler.outdeg (k := k)
                          (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
                      Filter.atTop Filter.atTop) ∧
              (∀ i j : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    Filter.Tendsto
                      (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
                      Filter.atTop
                      (nhds (((rowKernel i
                        (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal))) ∧
              (∀ i j : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
                      0 < ((rowKernel i
                        (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheorem k := by
  have hBuild :
      BuildRowKernelOnRecurrentExtension k :=
    buildRowKernelOnRecurrentExtension_of_coordwise_component_builder
      (k := k) hLocal
  exact fortiniSuccessorMatrixInvarianceTheorem_of_recurrentLatentCoherenceBridge
    (k := k)
    (recurrentLatentCoherenceBridgeTheorem_proved (k := k) hBuild)

theorem buildRowKernelOnRecurrentExtension_of_prefixRatioApproxENN_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hrecAe : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0}),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              ∀ᵐ ω ∂P,
                Filter.Tendsto
                  (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
                  Filter.atTop
                  (nhds (if ω 0 = a then
                    rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)))) :
    BuildRowKernelOnRecurrentExtension k := by
  intro μ hμ P hP hExt hrecAe
  rcases hLocal μ hμ P hP hExt hrecAe with
    ⟨rowKernel, hEval, hstart, hPi, hlim⟩
  refine ⟨rowKernel, ?_⟩
  exact builtRowKernelOnExtension_of_ae_tendsto_prefixRatioApproxENN
    (k := k) (μ := μ) hμ P hExt rowKernel hEval hstart hPi hlim

theorem fortiniSuccessorMatrixInvarianceTheorem_of_prefixRatioApproxENN_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hrecAe : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = ω 0}),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              ∀ᵐ ω ∂P,
                Filter.Tendsto
                  (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
                  Filter.atTop
                  (nhds (if ω 0 = a then
                    rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)))) :
    FortiniSuccessorMatrixInvarianceTheorem k := by
  have hBuild : BuildRowKernelOnRecurrentExtension k :=
    buildRowKernelOnRecurrentExtension_of_prefixRatioApproxENN_builder
      (k := k) hLocal
  exact fortiniSuccessorMatrixInvarianceTheorem_of_recurrentLatentCoherenceBridge
    (k := k)
    (recurrentLatentCoherenceBridgeTheorem_proved (k := k) hBuild)

theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              ∀ᵐ ω ∂P,
                Filter.Tendsto
                  (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
                  Filter.atTop
                  (nhds (if ω 0 = a then
                    rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0)))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  intro μ hμ hExtStrong
  rcases hExtStrong with ⟨P, hP, hExt, hStrong⟩
  letI : IsProbabilityMeasure P := hP
  rcases hLocal μ hμ P hP hExt hStrong with
    ⟨rowKernel, hEval, hstart, hPi, hlim⟩
  have hbuilt :
      BuiltRowKernelOnExtension (k := k) P rowKernel :=
    builtRowKernelOnExtension_of_ae_tendsto_prefixRatioApproxENN
      (k := k) (μ := μ) hμ P hExt rowKernel hEval hstart hPi hlim
  rcases hbuilt with ⟨hEval, _hstart, _hPi, hInv⟩
  rcases exists_markovParamLaw_of_hEval_and_rowSuccessorMatrixInvariance
      (k := k) (P := P) rowKernel hEval hInv with ⟨pi, hpi, hreprP⟩
  exact ⟨pi, hpi, fun xs => (hExt xs).trans (hreprP xs)⟩

theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_coordwise_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    Filter.Tendsto
                      (fun r =>
                        MarkovDeFinettiHardEuler.outdeg (k := k)
                          (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
                      Filter.atTop Filter.atTop) ∧
              (∀ i j : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    Filter.Tendsto
                      (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
                      Filter.atTop
                      (nhds (((rowKernel i
                        (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal))) ∧
              (∀ i j : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
                      0 < ((rowKernel i
                        (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  refine
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k) ?_
  intro μ hμ P hP hExt hStrong
  rcases hLocal μ hμ P hP hExt hStrong with
    ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
  refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
  intro a b xs
  rcases hcomp a b xs with ⟨hout, hfreq, hΘpos, hgraph⟩
  exact ae_tendsto_prefixRatioApproxENN_of_coordwise_component_limits
    (k := k) P rowKernel a b xs hout hfreq hΘpos hgraph

theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcess_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ i j : Fin k,
                ∀ᵐ r ∂rowProcessLaw (k := k) P i,
                  Filter.Tendsto
                    (fun m => rowProcessEmpiricalFreq (k := k) j r m)
                    Filter.atTop
                    (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal))) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  refine
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k) ?_
  intro μ hμ P hP hExt hStrong
  rcases hLocal μ hμ P hP hExt hStrong with
    ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
  refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
  intro a b xs
  rcases hcomp a b xs with ⟨hvisit, hrow, hΘposUsed, hgraph⟩
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcess_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph

theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              RowProcessCoordwiseCesaroLimit (k := k) P rowKernel ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  refine
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k) ?_
  intro μ hμ P hP hExt hStrong
  rcases hLocal μ hμ P hP hExt hStrong with
    ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
  refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
  intro a b xs
  rcases hcomp a b xs with ⟨hvisit, hrow, hΘposUsed, hgraph⟩
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
      (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph

/-- Intrinsic-row-Cesàro variant of the visit-based coordwise component builder.
`hLocal` no longer carries `RowProcessCoordwiseCesaroLimit`; it is supplied once
from `hRowCoord`. At this public intrinsic surface, `hLocal` also no longer
asks for positivity on the finite `prefixUsedTransitionSet`; it is enough to
provide eventual prefix compatibility and the normalized Euler-trail correction
limit. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  refine
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k) ?_
  intro μ hμ P hP hExt hStrong
  rcases hLocal μ hμ P hP hExt hStrong with
    ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
  refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
  intro a b xs
  rcases hcomp a b xs with ⟨hvisit, hprefixComp, hgraph⟩
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit
      (hRowCoord P hP rowKernel hEval hstart hPi)
      hprefixComp
      hgraph

/-- Intrinsic-row-Cesàro builder that keeps the normalized-Euler limit public
while deriving eventual prefix compatibility internally from used-transition
positivity. This makes the plain intrinsic route available directly over the
smaller `hΘposUsed + hgraph` seam instead of forcing callers to package
eventual compatibility separately. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  refine
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k) ?_
  intro μ hμ P hP hExt hStrong
  rcases hLocal μ hμ P hP hExt hStrong with
    ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
  refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
  intro a b xs
  rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hgraph⟩
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
      (k := k) P hStrong rowKernel a b xs hvisit
      (hRowCoord P hP rowKernel hEval hstart hPi)
      hΘposUsed hgraph

/-- Builder variant that isolates the live residual local seam explicitly:
eventual prefix compatibility plus the normalized Euler-trail correction limit,
with row-Cesàro data supplied intrinsically by `hRowCoord`. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  refine
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k) ?_
  intro μ hμ P hP hExt hStrong
  rcases hLocal μ hμ P hP hExt hStrong with
    ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
  refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
  intro a b xs
  rcases hcomp a b xs with ⟨hvisit, hprefixComp, hgraph⟩
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState
      (k := k) P hStrong rowKernel a b xs hvisit
      (hRowCoord P hP rowKernel hEval hstart hPi) hprefixComp hgraph

/-- Bridge-product-facing intrinsic-row-Cesàro builder. This states the live
residual local convergence seam in the more intrinsic normalized bridge-product
language, while still using eventual prefix compatibility as the exact place
where bridge-product and normalized-Euler correction coincide. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_eventually_prefixCompatibleState_of_tendsto_prefixNormalizedBridgeProductReal
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedBridgeProductReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  refine
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k) ?_
  intro μ hμ P hP hExt hStrong
  rcases hLocal μ hμ P hP hExt hStrong with
    ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
  refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
  intro a b xs
  rcases hcomp a b xs with ⟨hvisit, hprefixComp, hbridgeNorm⟩
  exact
    ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState_of_ae_tendsto_prefixNormalizedBridgeProductReal
      (k := k) P hStrong rowKernel a b xs hvisit
      (hRowCoord P hP rowKernel hEval hstart hPi)
      hprefixComp hbridgeNorm

/-- Public intrinsic builder that removes the explicit normalized-Euler /
bridge-product convergence input by deriving it internally from the
token-deletion squeeze, used-transition positivity, and the specialized bridge
theorem. What still remains external at this layer is eventual prefix
compatibility together with the bridge theorem itself. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_pathLocalBridgeCardEqPair_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    pathPrefixBridgeCardEqPair (k := k) a (b :: xs) ω r))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
      (k := k)
      hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp, hBridgePair⟩
        refine ⟨hvisit, hΘposUsed, ?_⟩
        exact
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixBridgeCardEqPair_of_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp hBridgePair)

/-- Path-local support-local bridge-facing intrinsic-row-Cesàro builder with no
separate support-local arborescence-ratio limit input. This keeps eventual
prefix compatibility explicit, but once that is available the smaller
support-local bridge object is already enough for the AE convergence route. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_pathLocalPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    pathPrefixPositiveBridgeCardEqPair (k := k) a (b :: xs) ω r))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
      (k := k)
      hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp, hBridgePair⟩
        refine ⟨hvisit, hΘposUsed, ?_⟩
        exact
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp hBridgePair)

/-- Support-local bridge-facing intrinsic-row-Cesàro compatibility wrapper.
The stronger no-extra-ratio path-local support-local builder now exists just
above it, so this older interface keeps the explicit ratio-limit hypothesis
only as a compatibility surface and factors through the smaller theorem by
deriving the needed eventual prefix compatibility from the induced normalized-
Euler limit. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_pathLocalPositiveBridgeCardEqPair
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    pathPrefixPositiveBridgeCardEqPair (k := k) a (b :: xs) ω r) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixPositiveTokenRootedArborescenceRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_pathLocalPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
      (k := k) hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hBridgePair, htokPos⟩
        have hgraph :
            ∀ᵐ ω ∂P,
              ω 0 = a →
                Filter.Tendsto
                  (fun r =>
                    prefixNormalizedEulerTrailCorrectionRatioReal
                      (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                  Filter.atTop (nhds (1 : ℝ)) :=
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_ae_pathPrefixPositiveBridgeCardEqPair
            (k := k) P a (b :: xs) hBridgePair htokPos
        have hprefixComp :
            ∀ᵐ ω ∂P,
              ω 0 = a →
                ∀ᶠ r in Filter.atTop,
                  prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                    (Nat.le_add_right (b :: xs).length r)
                    (pathPrefixState (k := k) ω ((b :: xs).length + r)) :=
          ae_eventually_prefixCompatibleState_pathPrefixState_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hgraph
        exact ⟨hvisit, hΘposUsed, hprefixComp, hBridgePair⟩)

/-- Public support-local bridge-facing intrinsic-row-Cesàro compatibility
wrapper. The stronger no-extra-ratio support-local builder now exists just
below it, so this theorem keeps the older interface without adding a distinct
mathematical seam. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_positiveBridge_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hPositiveBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixPositiveTokenRootedArborescenceRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp, _htokPos⟩
        exact
          ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState_via_supportSplit
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp
            (fun {_M} {_s} hs => hPositiveBridgeCard hs))

/-- Public support-local bridge-facing intrinsic-row-Cesàro builder with no
separate support-local ratio-limit input. On the eventually fully active
path-prefix states forced by recurrence/outdegree growth, the support-local
bridge data collapses back to the old path-local bridge data, so the existing
token-deletion route suffices. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hPositiveBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
      (k := k) hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp⟩
        refine ⟨hvisit, hΘposUsed, ?_⟩
        exact
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp
            (fun {_M} {_s} hs => hPositiveBridgeCard hs))

/-- Public intrinsic builder that removes the explicit normalized-Euler /
bridge-product convergence input by deriving it internally from the
token-deletion squeeze, used-transition positivity, and the specialized bridge
theorem. What still remains external at this layer is eventual prefix
compatibility together with the bridge theorem itself. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_bridge_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
      (k := k) hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp⟩
        refine ⟨hvisit, hΘposUsed, ?_⟩
        exact
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp
            (fun {_M} {_s} hs => hBridgeCard hs))

/-- Legacy token-deletion/bridge builder, now collapsed to the stronger
coordwise intrinsic route. At this public layer, `hLocal` no longer carries
an external normalized-Euler limit. It is enough to provide visit data,
positivity on the finite used-transition set, and eventual prefix
compatibility; the remaining normalized-Euler convergence step is derived
internally from the token-deletion squeeze plus the specialized bridge
theorem. -/
theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  exact
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_bridge_of_eventually_prefixCompatibleState
      (k := k) hRowCoord hBridgeCard
      (hLocal := fun μ hμ P hP hExt hStrong => by
        exact hLocal μ hμ P hP hExt hStrong)

theorem fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_infiniteVisits_rowProcess_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) ∧
              (∀ i j : Fin k,
                ∀ᵐ r ∂rowProcessLaw (k := k) P i,
                  Filter.Tendsto
                    (fun m => rowProcessEmpiricalFreq (k := k) j r m)
                    Filter.atTop
                    (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal))) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) :
    FortiniSuccessorMatrixInvarianceTheoremStrongRecurrence k := by
  refine
    fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k) ?_
  intro μ hμ P hP hExt hStrong
  rcases hLocal μ hμ P hP hExt hStrong with
    ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
  refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
  intro a b xs
  rcases hcomp a b xs with ⟨hinf, hrow, hΘposUsed, hgraph⟩
  exact
    ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcess_components
      (k := k) P rowKernel a b xs hinf hrow hΘposUsed hgraph

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              ∀ᵐ ω ∂P,
                Filter.Tendsto
                  (fun r => prefixRatioApproxENN (k := k) a (b :: xs) r ω)
                  Filter.atTop
                  (nhds (if ω 0 = a then
                    rowKernelStepProd (k := k) rowKernel ω (a :: b :: xs) else 0))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  rcases exists_extension_strongRecurrence_of_markovRowRecurrent (k := k) μ hrow with
    ⟨P, hP, hExt, hStrong⟩
  exact
    (fortiniSuccessorMatrixInvarianceTheoremStrongRecurrence_of_prefixRatioApproxENN_builder
      (k := k) hLocal) μ hμ ⟨P, hP, hExt, hStrong⟩

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcess_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ i j : Fin k,
                ∀ᵐ r ∂rowProcessLaw (k := k) P i,
                  Filter.Tendsto
                    (fun m => rowProcessEmpiricalFreq (k := k) j r m)
                    Filter.atTop
                    (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal))) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hrow, hΘposUsed, hgraph⟩
        exact
          ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcess_components
            (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph)
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              RowProcessCoordwiseCesaroLimit (k := k) P rowKernel ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hrow, hΘposUsed, hgraph⟩
        exact
          ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
            (k := k) P hStrong rowKernel a b xs hvisit hrow hΘposUsed hgraph)
      μ hμ hrow

/-- Intrinsic-row-Cesàro variant of the markov-parameter reconstruction builder.
`hLocal` omits `RowProcessCoordwiseCesaroLimit`; that component is supplied by
`hRowCoord`. As above, the public intrinsic surface now uses eventual prefix
compatibility plus the normalized Euler-trail correction limit rather than
finite-used-transition positivity. -/
theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hprefixComp, hgraph⟩
        exact
          ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hprefixComp
            hgraph)
      μ hμ hrow

/-- Intrinsic-row-Cesàro markov-parameter builder over the smaller plain
normalized-Euler seam. As with the Fortini builder above, used-transition
positivity plus the normalized-Euler limit are enough here; eventual prefix
compatibility is derived internally rather than supplied at the theorem
surface. -/
theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hgraph⟩
        exact
          ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hgraph)
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hprefixComp, hgraph⟩
        exact
          ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi) hprefixComp hgraph)
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_eventually_prefixCompatibleState_of_tendsto_prefixNormalizedBridgeProductReal
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedBridgeProductReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hprefixComp, hbridgeNorm⟩
        exact
          ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_eventually_prefixCompatibleState_of_ae_tendsto_prefixNormalizedBridgeProductReal
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hprefixComp hbridgeNorm)
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_pathLocalBridgeCardEqPair_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    pathPrefixBridgeCardEqPair (k := k) a (b :: xs) ω r)))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
      (k := k)
      hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp, hBridgePair⟩
        refine ⟨hvisit, hΘposUsed, ?_⟩
        exact
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixBridgeCardEqPair_of_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp hBridgePair)
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_bridge_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
      (k := k)
      hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp⟩
        refine ⟨hvisit, hΘposUsed, ?_⟩
        exact
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tokenDeletionSqueeze_of_bridgeCard_of_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp
            (fun {_M} {_s} hs => hBridgeCard hs))
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_pathLocalPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    pathPrefixPositiveBridgeCardEqPair (k := k) a (b :: xs) ω r)))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
      (k := k)
      hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp, hBridgePair⟩
        refine ⟨hvisit, hΘposUsed, ?_⟩
        exact
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp hBridgePair)
      μ hμ hrow

/-- Support-local bridge-facing row-recurrent compatibility wrapper. The
stronger no-extra-ratio path-local support-local route already exists, so this
older interface now factors through it by deriving eventual prefix
compatibility from the induced normalized-Euler limit. -/
theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_pathLocalPositiveBridgeCardEqPair
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    pathPrefixPositiveBridgeCardEqPair (k := k) a (b :: xs) ω r) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixPositiveTokenRootedArborescenceRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_pathLocalPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState
      (k := k) hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hBridgePair, htokPos⟩
        have hgraph :
            ∀ᵐ ω ∂P,
              ω 0 = a →
                Filter.Tendsto
                  (fun r =>
                    prefixNormalizedEulerTrailCorrectionRatioReal
                      (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                  Filter.atTop (nhds (1 : ℝ)) :=
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_ae_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_ae_pathPrefixPositiveBridgeCardEqPair
            (k := k) P a (b :: xs) hBridgePair htokPos
        have hprefixComp :
            ∀ᵐ ω ∂P,
              ω 0 = a →
                ∀ᶠ r in Filter.atTop,
                  prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                    (Nat.le_add_right (b :: xs).length r)
                    (pathPrefixState (k := k) ω ((b :: xs).length + r)) :=
          ae_eventually_prefixCompatibleState_pathPrefixState_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hgraph
        exact ⟨hvisit, hΘposUsed, hprefixComp, hBridgePair⟩)
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_positiveBridge_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hPositiveBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r))) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixPositiveTokenRootedArborescenceRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp, _htokPos⟩
        exact
          ae_tendsto_prefixRatioApproxENN_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState_via_supportSplit
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp
            (fun {_M} {_s} hs => hPositiveBridgeCard hs))
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hPositiveBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          positiveTokenRootedBridgeCardEq (k := k) s)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed
      (k := k) hRowCoord
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hvisit, hΘposUsed, hprefixComp⟩
        refine ⟨hvisit, hΘposUsed, ?_⟩
        exact
          ae_tendsto_prefixNormalizedEulerTrailCorrectionRatioReal_shift_of_strongRecurrence_visit_rowProcessCoordwise_components_of_ae_prefixThetaPosUsed_of_positiveBridge_of_eventually_prefixCompatibleState
            (k := k) P hStrong rowKernel a b xs hvisit
            (hRowCoord P hP rowKernel hEval hstart hPi)
            hΘposUsed hprefixComp
            (fun {_M} {_s} hs => hPositiveBridgeCard hs))
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_tokenDeletionSqueeze_of_bridge_of_eventually_prefixCompatibleState
    (hRowCoord :
      ∀ (P : Measure (ℕ → Fin k)) (_hP : IsProbabilityMeasure P)
        (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
          (∀ i : Fin k, ∀ b : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
              (rowProcessLaw (k := k) P i)) →
          StartRestrictedRowKernelData (k := k) P rowKernel →
          (∀ i : Fin k,
            AEMeasurable
              (fun r : ℕ → Fin k =>
                Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
              (rowProcessLaw (k := k) P i)) →
          RowProcessCoordwiseCesaroLimit (k := k) P rowKernel)
    (hBridgeCard :
      ∀ {M : ℕ} {s : MarkovState k},
        s ∈ stateFinset k M →
          (eulerTrailFinset (graphOfState s) s.start s.last).card =
            tokenRootedArborescenceCount (k := k) (graphOfState (k := k) s) s.last *
              outdegFactorialWeight (k := k) s)
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a → ∃ t : ℕ, ω t = i) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  ∀ᶠ r in Filter.atTop,
                    prefixCompatibleState (k := k) a (b :: xs) ((b :: xs).length + r)
                      (Nat.le_add_right (b :: xs).length r)
                      (pathPrefixState (k := k) ω ((b :: xs).length + r)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_visit_rowProcessCoordwise_component_builder_intrinsic_of_prefixThetaPosUsed_of_bridge_of_eventually_prefixCompatibleState
      (k := k) hRowCoord hBridgeCard
      (hLocal := fun μ hμ P hP hExt hStrong => by
        exact hLocal μ hμ P hP hExt hStrong)
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_infiniteVisits_rowProcess_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) ∧
              (∀ i j : Fin k,
                ∀ᵐ r ∂rowProcessLaw (k := k) P i,
                  Filter.Tendsto
                    (fun m => rowProcessEmpiricalFreq (k := k) j r m)
                    Filter.atTop
                    (nhds (((rowKernel i r) ({j} : Set (Fin k))).toReal))) ∧
              (∀ p ∈ prefixUsedTransitionSet (k := k) a (b :: xs),
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < rowKernelVisitProbReal (k := k) rowKernel p.1 p.2 ω) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ)))))
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hinf, hrow, hΘposUsed, hgraph⟩
        exact
          ae_tendsto_prefixRatioApproxENN_of_ae_infinite_visits_rowProcess_components
            (k := k) P rowKernel a b xs hinf hrow hΘposUsed hgraph)
      μ hμ hrow

theorem exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_coordwise_component_builder
    (hLocal :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k))
        (_hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
        (P : Measure (ℕ → Fin k))
        (_hP : IsProbabilityMeasure P)
        (_hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
        (_hStrong : StrongRecurrence (k := k) P),
          ∃ (rowKernel : Fin k → (ℕ → Fin k) → ProbabilityMeasure (Fin k)),
            (∀ i : Fin k, ∀ b : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k => (rowKernel i r : Measure (Fin k)) ({b} : Set (Fin k)))
                (rowProcessLaw (k := k) P i)) ∧
            StartRestrictedRowKernelData (k := k) P rowKernel ∧
            (∀ i : Fin k,
              AEMeasurable
                (fun r : ℕ → Fin k =>
                  Measure.pi (fun _ : Fin 1 => (rowKernel i r : Measure (Fin k))))
                (rowProcessLaw (k := k) P i)) ∧
            (∀ (a b : Fin k) (xs : List (Fin k)),
              (∀ i : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    Filter.Tendsto
                      (fun r =>
                        MarkovDeFinettiHardEuler.outdeg (k := k)
                          (pathPrefixState (k := k) ω ((b :: xs).length + r)) i)
                      Filter.atTop Filter.atTop) ∧
              (∀ i j : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    Filter.Tendsto
                      (fun m => rowSuccessorEmpiricalFreq (k := k) i j ω m)
                      Filter.atTop
                      (nhds (((rowKernel i
                        (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal))) ∧
              (∀ i j : Fin k,
                ∀ᵐ ω ∂P,
                  ω 0 = a →
                    0 < (prefixWordState (k := k) a (b :: xs)).counts.counts i j →
                      0 < ((rowKernel i
                        (rowSuccessorVisitProcess (k := k) i ω)) ({j} : Set (Fin k))).toReal) ∧
              (∀ᵐ ω ∂P,
                ω 0 = a →
                  Filter.Tendsto
                    (fun r =>
                      prefixNormalizedEulerTrailCorrectionRatioReal
                        (k := k) a (b :: xs) ((b :: xs).length + r)
                        (Nat.le_add_right (b :: xs).length r)
                        (pathPrefixState (k := k) ω ((b :: xs).length + r)))
                    Filter.atTop (nhds (1 : ℝ))))) 
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrow : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact
    exists_markovParamLaw_of_markovExchangeable_rowRecurrent_of_prefixRatioApproxENN_builder
      (k := k)
      (hLocal := fun μ hμ P hP hExt hStrong => by
        rcases hLocal μ hμ P hP hExt hStrong with
          ⟨rowKernel, hEval, hstart, hPi, hcomp⟩
        refine ⟨rowKernel, hEval, hstart, hPi, ?_⟩
        intro a b xs
        rcases hcomp a b xs with ⟨hout, hfreq, hΘpos, hgraph⟩
        exact ae_tendsto_prefixRatioApproxENN_of_coordwise_component_limits
          (k := k) P rowKernel a b xs hout hfreq hΘpos hgraph)
      μ hμ hrow

/-! ## Section 5: Sound Stopping Point

This file deliberately stops short of any claim that raw pointwise permutations
of selected row-successor values preserve finite evidence fibers.

That stronger claim is false in general: changing the successor chosen at an
early visit to state `i` can change which states are visited later, so the
trajectory may leave the original evidence fiber. The row-wise constraints are
dynamically coupled through the trajectory, and naive permutation transport is
not a sound route.

What remains sound and usable here:
- exact finite prefix-conditioned counting inside one evidence fiber
- the residual-state and BEST-ratio decomposition for those counts
- the token-rooted deletion squeeze and lower-factor limit machinery
- the path-space expectation packaging
- the conditional DCT route from prefix-ratio convergence to
  `CylinderMixingIdentity_P`
- the builder-level composition into `BuiltRowKernelOnExtension` and the public
  recurrent Fortini theorem path

What still remains open is the larger local extension-level builder package:
the supported-vs-unsupported prefix split is now explicit at both the pointwise
and AE levels, and eventual prefix compatibility is now derived from the
strong-recurrence / row-Cesàro / finite-used-transition-positivity package once
the normalized-Euler correction limit is supplied. The main intrinsic public
Fortini / markov-parameter routes now also use that smaller seam: there is now
a plain intrinsic public route stated directly over finite-used-transition
positivity plus the normalized-Euler limit, with eventual prefix compatibility
derived internally, and there are also smaller eventual-compatibility-facing
routes over either the normalized-Euler limit or, more intrinsically, the
normalized bridge-product limit. The live remaining seam is therefore the
intrinsic source of that local convergence input itself. There is now also a
public route that avoids an external `hgraph` hypothesis by deriving the
normalized-Euler limit internally from used-transition positivity, the
token-deletion squeeze, and the specialized bridge theorem; on the support-
local side, once that `hgraph` input is available the strong-recurrence
`prefixRatioApproxENN` route now explicitly factors through the general
supported-vs-unsupported split instead of carrying a separate specialized
endgame, and the support-local Fortini / markov-parameter builders now factor
through the plain intrinsic `hΘposUsed + hgraph` seam once their bridge data
has produced that local convergence input. The older token-rooted path-local
and global bridge-facing Fortini / markov-parameter builders now also derive
that local convergence input and then reuse the same plain intrinsic
`hΘposUsed + hgraph` seam instead of standing as parallel public proof lanes.
At the public builder surface, that bridge input is now exposed in the more concrete finite
cardinality form saying that `eulerTrailFinset.card` equals the token-rooted
arborescence count times the outdegree-factorial weight. More sharply, the
public bridge-based route can now be phrased using only the eventual full and
residual path-prefix instances of that exact bridge-cardinality identity,
rather than a global all-states bridge assumption. The new obstruction theorems
`not_tokenRootedBridgeCardEq_of_exists_nonroot_zero_row_of_mem_stateFinset`
and
`not_tokenRootedBridgeCardEq_of_exists_nonroot_outdeg_zero_of_mem_stateFinset`
show why that sharpening matters: on a state in `stateFinset`, the exact
bridge-cardinality identity cannot hold as soon as a non-root vertex becomes
dormant, because the Euler-trail count is still positive while the all-vertices
token-rooted arborescence count collapses to zero. The new state-balance
lemmas `inDegG_eq_zero_of_outdeg_eq_zero_of_mem_stateFinset`,
`start_ne_of_outdeg_eq_zero_of_mem_stateFinset`, and
`graphOfState_col_eq_zero_of_outdeg_eq_zero_of_mem_stateFinset` sharpen that
picture further: in an actual evidence state, a dormant non-root row has no
incoming edges either and cannot be the start vertex. So the remaining gap is
not merely to "prove the old global theorem"; it is to internalize the right
support-local finite bridge-cardinality source itself.
The file originally named that replacement target as
`positiveTokenRootedBridgeCardEq`, built from
`positiveTokenRootedArborescenceCount`, where dormant non-root rows are removed
from the rooted-arborescence domain. The permanent theorem
`positiveTokenRootedBridgeCardEq_false_on_counterexample_0101` now shows that
this support-local bridge still uses the wrong normalization: the full
`outdegFactorialWeight` double-counts parent-edge copy choices already present
in `positiveTokenRootedArborescenceCount`. The live conjectural replacement is
the same cardinality identity with `positiveTokenRootedBestWeight` instead of
`outdegFactorialWeight`. Consequently the normalized-Euler bridge layer is now
best read as legacy transport scaffolding around a refuted normalization, not
as a closable endgame for the direct route. What still remains is to rebuild
that transport stack around the corrected BEST weight, prove the genuine
support-local BEST theorem for the corrected normalization, and only then
finish the cleanup of any residual wrapper stack so the recurrent Fortini path
depends on row-kernel asymptotics plus true local combinatorics rather than on
a residual `hLocal` bundle. The comparison theorem
`positiveTokenRootedArborescenceCount_eq_tokenRootedArborescenceCount_of_forall_pos`
still shows that the support-local count object itself is conservative on
states where every non-root row is active: in that case the support-local and
old all-vertices rooted counts coincide exactly. The new ratio-transport lemmas
`prefixPositiveTokenRootedArborescenceRatio_eq_prefixTokenRootedArborescenceRatio_of_forall_pos`
and
`tendsto_prefixPositiveTokenRootedArborescenceRatioReal_of_tendsto_prefixTokenRootedArborescenceRatioReal_of_eventually_prefixCompatibleState_of_tendsto_outdeg`
push that conservativity further up the stack: once path-prefix outdegrees are
eventually strictly larger than the finite prefix outdegrees, the support-local
arborescence ratio is eventually equal to the old token-rooted ratio and hence
inherits its `→ 1` limit. Those transport results still matter for the future
corrected route, but not as evidence that the legacy bridge predicate itself is
salvageable. At
the opposite extreme, the new finite lemmas
`positiveWeightedTargetRootedArborescenceCount_eq_one_of_forall_nonroot_outdeg_zero`,
`positiveTokenRootedArborescenceCount_eq_one_of_forall_nonroot_outdeg_zero`,
and
`positiveTokenRootedBridgeCardEq_iff_card_eq_outdegFactorialWeight_of_forall_nonroot_outdeg_zero`
also settle the completely dormant non-root regime exactly: there the
support-local rooted-arborescence count is `1`, so the support-local bridge
equation reduces to a bare Euler-trail/cardinality identity. So the live
finite support-local bridge seam is now the genuinely mixed case, with some
active non-root rows and some dormant ones. The new support-local transport
lemmas
`positiveTokenRootedArborescenceCount_congr_nonroot_rows`,
`positiveTokenRootedArborescenceCount_residualStateOfPrefix_eq_deleteCopies_prefixNonrootDeletionList`,
and
`prefixPositiveTokenRootedArborescenceRatio_eq_deleteCopies_prefixNonroot_ratio`
also mean that this mixed seam is no longer "just" a new count object: the
support-local rooted count and its prefix ratio now satisfy the same exact
residual/delete-copies finite rewrite pattern that the old token-rooted route
used. The new active-source transport lemmas
`positiveNonrootVertexEquiv_deleteOneCopy_of_source_stays_positive`,
`positiveTargetParentStep_eq_deleteOneCopy_of_source_stays_positive`, and
`isPositiveTargetRootedArborescence_iff_deleteOneCopy_of_source_stays_positive`
push that one step further: in the mixed case branch where deleting one copy
does not extinguish the source row, the active support and rootedness data now
transport exactly across `deleteOneCopy`. The new weighted rewrite
`positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_eq_transportSum_of_source_stays_positive`
then lifts that transport to the support-local finite counting surface itself:
in the same active-source branch, the delete-one-copy weighted count is now
literally a sum over the original rooted support-local assignments with the
updated edge multiplicities substituted into each term. The new active-source
lower inequality
`positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_lower_of_source_stays_positive`
shows that this branch is no longer just a transport statement: it already has
the exact one-copy multiplicative lower bound needed for the deletion-squeeze
route, as long as the deleted source row stays active. And the new full
one-copy support-local lower theorem
`positiveWeightedTargetRootedArborescenceCount_deleteOneCopy_lower`, together
with its token-level corollary
`positiveTokenRootedArborescenceCount_deleteOneCopy_lower`, now folds in the
complementary branch where the deleted source row goes dormant by showing that
the deleted multiplicity factor itself collapses to `0` there. So the
support-local finite deletion engine is now present one level higher too:
`positiveTokenRootedArborescenceCount_deleteCopies_lower` lifts that one-copy
support-local lower theorem through the full `deleteCopies` induction. So the
support-local finite deletion engine is no longer stranded below the prefix
ratio layer either: the new lemmas
`prefixTokenDeletionLowerNumerator_mul_positiveFull_le_denominator_mul_positiveResidual`
and
`prefixTokenDeletionLowerFactor_le_prefixPositiveTokenRootedArborescenceRatio_of_prefixCompatibleState_of_positiveBridgeCardEq`,
together with their AE path-local support-local transport
`ae_eventually_prefixTokenDeletionLowerFactorReal_le_prefixPositiveTokenRootedArborescenceRatioReal_shift_of_ae_pathPrefixPositiveBridgeCardEqPair_of_eventually_prefixCompatibleState`,
show that the same concrete lower factor now feeds directly into the
support-local prefix ratio whenever the full path-prefix bridge-cardinality
input is available. So the remaining mixed support-local gap is narrower than
before: it is to prove the mixed-case BEST-style bridge theorem and the
matching intrinsic support-local asymptotic route on top of that
now-internalized delete-copies exactness, rather than to recover the
residual-state combinatorics from scratch.

The new bridge-transport theorem
`ae_eventually_pathPrefixBridgeCardEqPair_of_globalPositiveBridgeCard_of_eventually_prefixCompatibleState_of_ae_tendsto_outdeg`
pushes that same fully-active reduction to the lower convergence layer too:
from a global support-local bridge theorem, eventual prefix compatibility, and
the intrinsic outdegree-growth route from strong recurrence, the file now
recovers the old path-local bridge data automatically on eventual path
prefixes. As a result, the support-local positive-bridge seam now reaches the
normalized-Euler limit directly at both the path-local and global AE layers,
and the strong-recurrence AE convergence theorem plus both the path-local and
global-support-local public Fortini / markov-parameter builder routes no
longer need a separate external support-local arborescence-ratio limit input.
So the remaining support-local asymptotic gap is now isolated even more
sharply to the dormant-row case itself, together with the finite support-local
BEST-style theorem. The global support-local public routes also now factor
through the path-local support-local builders instead of maintaining a separate
parallel proof stack, and the older path-local/global support-local
ratio-limit-flavored compatibility wrappers now route through those smaller
no-extra-ratio support-local seams rather than carrying distinct proof paths. -/
end Mettapedia.Logic.MarkovDeFinettiHard
