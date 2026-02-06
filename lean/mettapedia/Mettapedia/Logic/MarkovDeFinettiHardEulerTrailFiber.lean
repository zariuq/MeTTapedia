import Mettapedia.Logic.MarkovDeFinettiHardEulerTrails

/-! LLM primer:
- `graphOfState (stateOfTraj xs) a b = transCount xs a b` (definitionally via rfl chain)
- `totalEdgeTokens (graphOfState s) = N` when `s ∈ stateFinset k N` (propositional, NOT def.)
- `stateOfTraj xs = ⟨xs 0, countsOfFn xs, xs (Fin.last n)⟩`
- `fiber k N s = Finset.univ.filter (stateOfTraj · = s)`
- The `Fin M` vs `Fin (totalEdgeTokens G)` mismatch requires casts throughout.
  `trajToEdgeTok` works with `Fin M`; `trajToEdgeTokN` wraps the cast for `IsEulerTrail`.

# Euler Trail ↔ Fiber Bridge (Phase B, Step 2)

## Main results

- `stateOfTraj_trailVertexSeq` : vertex seq of Euler trail on graphOfState has state s
- `trajToEdgeTokN` : canonical edge labeling (correctly typed for IsEulerTrail)
- `trajToEdgeTokN_isEulerTrail` : the canonical labeling is an Euler trail
- `trailVertexSeq_trajToEdgeTokN` : left inverse (trail of canonical labeling = original traj)
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardEulerTrailFiber

open Finset
open MarkovDeFinettiHardBESTCore
open MarkovDeFinettiHardEulerTrails
open MarkovExchangeability
open UniversalPrediction.FiniteAlphabet
open UniversalPrediction.MarkovExchangeabilityBridge
open MarkovDeFinettiHard

variable {k : ℕ}

/-! ## Trail → Fiber direction -/

/-- The vertex sequence of an Euler trail on `graphOfState s` from `s.start` to `s.last`
has `stateOfTraj` equal to `s`. -/
theorem stateOfTraj_trailVertexSeq
    (s : MarkovState k)
    (f : Fin (totalEdgeTokens (graphOfState s)) → edgeTok (graphOfState s))
    (hf : IsEulerTrail (graphOfState s) s.start s.last f) :
    stateOfTraj (k := k) (trailVertexSeq (graphOfState s) s.start f) = s := by
  refine MarkovState.ext ?_ ?_ ?_
  · -- start
    simp [stateOfTraj, trailVertexSeq_start]
  · -- counts
    ext a b
    simp only [stateOfTraj, countsOfFn_apply]
    rw [transCount_trailVertexSeq (graphOfState s) s.start s.last f hf a b]
    rfl
  · -- last
    simp only [stateOfTraj]
    exact trailVertexSeq_end (graphOfState s) s.start s.last f hf

/-! ## Canonical edge labeling: Trajectory → Euler Trail -/

/-- Number of times transition `(a, b)` appears strictly before position `i`. -/
def prefixTransCount {M : ℕ} (xs : Fin (M + 1) → Fin k) (i : Fin M) (a b : Fin k) : ℕ :=
  (Finset.univ.filter (fun j : Fin M =>
    j.1 < i.1 ∧ xs (Fin.castSucc j) = a ∧ xs (Fin.succ j) = b)).card

/-- The copy index at position `i`: how many times the same transition appeared before `i`. -/
def copyIndexAt {M : ℕ} (xs : Fin (M + 1) → Fin k) (i : Fin M) : ℕ :=
  prefixTransCount xs i (xs (Fin.castSucc i)) (xs (Fin.succ i))

/-- The prefix count at position `i` for the transition at `i` is strictly less
than the total count of that transition. -/
lemma copyIndexAt_lt_transCount {M : ℕ} (xs : Fin (M + 1) → Fin k) (i : Fin M) :
    copyIndexAt xs i < transCount (n := M) xs (xs (Fin.castSucc i)) (xs (Fin.succ i)) := by
  unfold copyIndexAt prefixTransCount transCount
  apply Finset.card_lt_card
  constructor
  · intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro ⟨_, ha, hb⟩
    exact ⟨ha, hb⟩
  · simp only [Finset.not_subset]
    refine ⟨i, ?_, ?_⟩
    · simp [Finset.mem_filter]
    · simp [Finset.mem_filter]

/-- Canonical edge labeling on `Fin M` (internal helper). -/
def trajToEdgeTok {M : ℕ} (xs : Fin (M + 1) → Fin k) (i : Fin M) :
    edgeTok (graphOfState (stateOfTraj (k := k) xs)) :=
  ⟨xs (Fin.castSucc i), ⟨xs (Fin.succ i),
    ⟨copyIndexAt xs i, copyIndexAt_lt_transCount xs i⟩⟩⟩

@[simp] lemma trajToEdgeTok_src {M : ℕ} (xs : Fin (M + 1) → Fin k) (i : Fin M) :
    edgeSrc (trajToEdgeTok (k := k) xs i) = xs (Fin.castSucc i) := rfl

@[simp] lemma trajToEdgeTok_tgt {M : ℕ} (xs : Fin (M + 1) → Fin k) (i : Fin M) :
    edgeTgt (trajToEdgeTok (k := k) xs i) = xs (Fin.succ i) := rfl

/-! ## Injectivity of the canonical labeling -/

/-- If the same transition occurs at positions `i < j`, then the prefix count at `j` is
strictly greater than at `i`. -/
lemma prefixTransCount_strict_mono {M : ℕ} (xs : Fin (M + 1) → Fin k) (i j : Fin M)
    (hij : i.1 < j.1) (ha : xs (Fin.castSucc i) = xs (Fin.castSucc j))
    (hb : xs (Fin.succ i) = xs (Fin.succ j)) :
    copyIndexAt xs i < copyIndexAt xs j := by
  unfold copyIndexAt prefixTransCount
  apply Finset.card_lt_card
  constructor
  · intro m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro ⟨hlt, hma, hmb⟩
    exact ⟨by omega, by rwa [← ha], by rwa [← hb]⟩
  · simp only [Finset.not_subset]
    refine ⟨i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hij, ha, hb⟩
    · simp [Finset.mem_filter]

/-- The canonical edge labeling is injective. -/
theorem trajToEdgeTok_injective {M : ℕ} (xs : Fin (M + 1) → Fin k) :
    Function.Injective (trajToEdgeTok (k := k) xs) := by
  intro i j hij
  have hsrc : xs (Fin.castSucc i) = xs (Fin.castSucc j) := by
    have := congr_arg edgeSrc hij; simpa using this
  have htgt : xs (Fin.succ i) = xs (Fin.succ j) := by
    have := congr_arg edgeTgt hij; simpa using this
  have hcopy : copyIndexAt xs i = copyIndexAt xs j := by
    have := congr_arg (fun e : edgeTok _ => (e.2.2 : ℕ)) hij
    simpa [trajToEdgeTok] using this
  rcases lt_trichotomy i.1 j.1 with h | h | h
  · exact absurd hcopy (ne_of_lt (prefixTransCount_strict_mono xs i j h hsrc htgt))
  · exact Fin.ext h
  · exact absurd hcopy (ne_of_gt (prefixTransCount_strict_mono xs j i h hsrc.symm htgt.symm))

/-! ## Cast to `totalEdgeTokens`-indexed domain -/

/-- Total transition count equals `M`. -/
lemma totalEdgeTokens_graphOfState_stateOfTraj {M : ℕ} (xs : Fin (M + 1) → Fin k) :
    totalEdgeTokens (graphOfState (stateOfTraj (k := k) xs)) = M :=
  totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k)
    (stateOfTraj_mem_stateFinset (k := k) xs)

/-- The canonical edge labeling, cast to `Fin (totalEdgeTokens G)` for use with `IsEulerTrail`. -/
def trajToEdgeTokN {M : ℕ} (xs : Fin (M + 1) → Fin k) :
    Fin (totalEdgeTokens (graphOfState (stateOfTraj (k := k) xs))) →
    edgeTok (graphOfState (stateOfTraj (k := k) xs)) :=
  fun i => trajToEdgeTok xs
    ⟨i.1, by have := totalEdgeTokens_graphOfState_stateOfTraj (k := k) xs; omega⟩

/-- `trajToEdgeTokN` is injective. -/
theorem trajToEdgeTokN_injective {M : ℕ} (xs : Fin (M + 1) → Fin k) :
    Function.Injective (trajToEdgeTokN (k := k) xs) := by
  intro i j hij
  have hinj := trajToEdgeTok_injective (k := k) xs
  have hmk : (⟨i.1, _⟩ : Fin M) = ⟨j.1, _⟩ := hinj hij
  exact Fin.ext (Fin.mk.inj hmk)

/-- `trajToEdgeTokN` is bijective. -/
theorem trajToEdgeTokN_bijective {M : ℕ} (xs : Fin (M + 1) → Fin k) :
    Function.Bijective (trajToEdgeTokN (k := k) xs) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨trajToEdgeTokN_injective xs, by
    rw [Fintype.card_fin, card_edgeTok]⟩

/-- Chain condition for `trajToEdgeTok`: target of edge `i` = source of edge `i+1`. -/
lemma trajToEdgeTok_chain {M : ℕ} (xs : Fin (M + 1) → Fin k) (i : ℕ) (hi : i + 1 < M) :
    edgeTgt (trajToEdgeTok (k := k) xs ⟨i, by omega⟩) =
      edgeSrc (trajToEdgeTok (k := k) xs ⟨i + 1, hi⟩) := rfl

/-! ## The canonical labeling is an Euler trail -/

/-- The canonical edge labeling of a trajectory is an Euler trail on `graphOfState`. -/
theorem trajToEdgeTokN_isEulerTrail {M : ℕ} (xs : Fin (M + 1) → Fin k) :
    IsEulerTrail (graphOfState (stateOfTraj (k := k) xs))
      (xs 0) (xs (Fin.last M))
      (trajToEdgeTokN (k := k) xs) := by
  have hN := totalEdgeTokens_graphOfState_stateOfTraj (k := k) xs
  refine ⟨trajToEdgeTokN_bijective xs, ?_, ?_, ?_, ?_⟩
  · -- empty → start = end
    intro h0
    rw [hN] at h0
    simp [Fin.last, h0]
  · -- start: edgeSrc (f ⟨0, _⟩) = xs 0
    intro h
    simp [trajToEdgeTokN, trajToEdgeTok, edgeSrc]
  · -- chain: edgeTgt (f ⟨i, _⟩) = edgeSrc (f ⟨i+1, _⟩)
    intro i hi
    exact trajToEdgeTok_chain xs i (by omega)
  · -- end: edgeTgt (f ⟨N-1, _⟩) = xs (Fin.last M)
    intro h
    simp only [trajToEdgeTokN, trajToEdgeTok, edgeTgt]
    congr 1
    ext
    simp only [Fin.val_succ, Fin.val_last]
    omega

/-! ## Left inverse: trailVertexSeq ∘ trajToEdgeTokN = identity -/

/-- The vertex sequence of the canonical edge labeling recovers the original trajectory
(up to the natural Fin cast). -/
theorem trailVertexSeq_trajToEdgeTokN {M : ℕ} (xs : Fin (M + 1) → Fin k)
    (i : Fin (totalEdgeTokens (graphOfState (stateOfTraj (k := k) xs)) + 1)) :
    trailVertexSeq (graphOfState (stateOfTraj (k := k) xs)) (xs 0)
      (trajToEdgeTokN (k := k) xs) i =
    xs ⟨i.1, by have := totalEdgeTokens_graphOfState_stateOfTraj (k := k) xs; omega⟩ := by
  rcases i with ⟨n, hn⟩
  cases n with
  | zero => simp [trailVertexSeq]
  | succ m =>
    have hm : m < totalEdgeTokens (graphOfState (stateOfTraj (k := k) xs)) := by omega
    rw [show (⟨m + 1, hn⟩ : Fin (_ + 1)) = ⟨m + 1, by omega⟩ from rfl,
        trailVertexSeq_succ _ (xs 0) (trajToEdgeTokN (k := k) xs) m hm]
    -- Goal: edgeTgt (trajToEdgeTokN xs ⟨m, hm⟩) = xs ⟨m + 1, _⟩
    rfl

end MarkovDeFinettiHardEulerTrailFiber

end Mettapedia.Logic
