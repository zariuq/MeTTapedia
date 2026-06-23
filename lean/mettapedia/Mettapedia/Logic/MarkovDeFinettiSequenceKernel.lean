import Mathlib.Data.List.OfFn
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.MarkovDeFinettiRecurrence

/-!
# Canonical Sequence Law of a Markov Parameter

For a fixed `θ : MarkovParam k`, this file builds the canonical sequence law on
`ℕ → Fin k` using `ProbabilityTheory.Kernel.trajMeasure`, and proves that its
finite-prefix cylinder probabilities are exactly `wordProb θ`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic

open MeasureTheory
open ProbabilityTheory
open Preorder
open scoped NNReal ENNReal
open MarkovDeFinettiHard
open MarkovDeFinettiRecurrence

namespace MarkovDeFinettiSequenceKernel

variable {k : ℕ}

/-- Prefixes indexed by `Iic n`, matching the shape expected by `trajMeasure`. -/
abbrev PrefixState (k : ℕ) (n : ℕ) := ∀ _ : Finset.Iic n, Fin k

/-- The last coordinate of an `Iic n` prefix. -/
def lastCoord (n : ℕ) : PrefixState k n → Fin k :=
  fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩

theorem measurable_lastCoord (n : ℕ) : Measurable (lastCoord (k := k) n) := by
  unfold lastCoord
  exact measurable_pi_apply _

/-- Convert an `Iic n` prefix into the equivalent `Fin (n+1)` tuple. -/
def dropPrefix (n : ℕ) : PrefixState k n → Fin (n + 1) → Fin k :=
  fun x i => x ⟨i.1, Finset.mem_Iic.2 (Nat.le_of_lt_succ i.2)⟩

theorem measurable_dropPrefix (n : ℕ) : Measurable (dropPrefix (k := k) n) := by
  unfold dropPrefix
  fun_prop

/-- The list corresponding to an `Iic n` prefix. -/
def listOfPrefix (n : ℕ) (x : PrefixState k n) : List (Fin k) :=
  List.ofFn (dropPrefix (k := k) n x)

/-- Rebuild an `Iic n` prefix from a `Fin (n+1)` tuple. -/
def prefixOfFin (n : ℕ) (x : Fin (n + 1) → Fin k) : PrefixState k n :=
  fun i => x ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2)⟩

@[simp] theorem dropPrefix_prefixOfFin (n : ℕ) (x : Fin (n + 1) → Fin k) :
    dropPrefix (k := k) n (prefixOfFin (k := k) n x) = x := by
  funext i
  simp [dropPrefix, prefixOfFin]

@[simp] theorem prefixOfFin_dropPrefix (n : ℕ) (x : PrefixState k n) :
    prefixOfFin (k := k) n (dropPrefix (k := k) n x) = x := by
  funext i
  simp [dropPrefix, prefixOfFin]

@[simp] theorem listOfPrefix_prefixOfFin (n : ℕ) (x : Fin (n + 1) → Fin k) :
    listOfPrefix (k := k) n (prefixOfFin (k := k) n x) = List.ofFn x := by
  simp [listOfPrefix]

/-- Prefix event on the first `n + 1` coordinates, in the `Iic` presentation. -/
def prefixEvent (n : ℕ) (x : PrefixState k n) : Set (ℕ → Fin k) :=
  (frestrictLe n) ⁻¹' ({x} : Set (PrefixState k n))

/-- Decompose a length `n+2` prefix into its first `n+1` coordinates and final
coordinate. -/
def nextPairMap (n : ℕ) : PrefixState k (n + 1) → PrefixState k n × Fin k :=
  fun x => (frestrictLe₂ (π := fun _ : ℕ => Fin k) (Nat.le_succ n) x, lastCoord (k := k) (n + 1) x)

/-- Reassemble a length `n+2` prefix from its first `n+1` coordinates and final
coordinate. -/
noncomputable def succAssemble (n : ℕ) : PrefixState k n × Fin k → PrefixState k (n + 1) :=
  fun x =>
    (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Fin k) (Nat.le_succ n))
      (x.1, (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Fin k) n) x.2)

@[simp]
theorem succAssemble_apply_le (n : ℕ) (x : PrefixState k n × Fin k)
    {i : Finset.Iic (n + 1)} (hi : i.1 ≤ n) :
    succAssemble (k := k) n x i = x.1 ⟨i.1, Finset.mem_Iic.2 hi⟩ := by
  unfold succAssemble
  simp [MeasurableEquiv.IicProdIoc, hi]

@[simp]
theorem succAssemble_apply_last (n : ℕ) (x : PrefixState k n × Fin k) :
    succAssemble (k := k) n x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ = x.2 := by
  unfold succAssemble
  simp [MeasurableEquiv.IicProdIoc, MeasurableEquiv.piSingleton]

@[simp]
theorem nextPairMap_succAssemble (n : ℕ) (x : PrefixState k n × Fin k) :
    nextPairMap (k := k) n (succAssemble (k := k) n x) = x := by
  rcases x with ⟨x, b⟩
  apply Prod.ext
  · funext i
    exact succAssemble_apply_le (k := k) n (x := (x, b)) (hi := Finset.mem_Iic.1 i.2)
  · simp [nextPairMap, lastCoord]

@[simp]
theorem succAssemble_nextPairMap (n : ℕ) :
    succAssemble (k := k) n ∘ nextPairMap (k := k) n = id := by
  funext x
  funext i
  by_cases hi : i.1 ≤ n
  · simpa [nextPairMap, lastCoord] using
      (succAssemble_apply_le (k := k) n (x := nextPairMap (k := k) n x) hi)
  · have hi_eq : i = ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
      apply Subtype.ext
      have hi_lt : n < i.1 := Nat.lt_of_not_ge hi
      exact le_antisymm (Finset.mem_Iic.1 i.2) (Nat.succ_le_of_lt hi_lt)
    subst hi_eq
    calc
      succAssemble (k := k) n (nextPairMap (k := k) n x) ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ =
          (nextPairMap (k := k) n x).2 :=
        succAssemble_apply_last (k := k) n (x := nextPairMap (k := k) n x)
      _ = x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := rfl

@[simp]
theorem succAssemble_worldPair (n : ℕ) :
    succAssemble (k := k) n ∘
        (fun x : ℕ → Fin k => (frestrictLe n x, x (n + 1))) =
      frestrictLe (π := fun _ : ℕ => Fin k) (n + 1) := by
  funext x
  funext i
  by_cases hi : i.1 ≤ n
  · simpa using
      (succAssemble_apply_le (k := k) n (x := (frestrictLe n x, x (n + 1))) hi)
  · have hi_eq : i = ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
      apply Subtype.ext
      have hi_lt : n < i.1 := Nat.lt_of_not_ge hi
      exact le_antisymm (Finset.mem_Iic.1 i.2) (Nat.succ_le_of_lt hi_lt)
    subst hi_eq
    simp [Function.comp_apply]

/-- The one-step Markov kernel indexed by prefixes. Since the prefix space is
finite, the kernel measurability is automatic. -/
noncomputable def nextKernel (θ : MarkovParam k) (n : ℕ) :
    ProbabilityTheory.Kernel (PrefixState k n) (Fin k) :=
  ProbabilityTheory.Kernel.ofFunOfCountable
    (fun x => (θ.trans (lastCoord (k := k) n x) : Measure (Fin k)))

instance nextKernel_isMarkov (θ : MarkovParam k) (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (nextKernel (k := k) θ n) := by
  refine ⟨?_⟩
  intro x
  change IsProbabilityMeasure (((θ.trans (lastCoord (k := k) n x) : ProbabilityMeasure (Fin k)) :
    Measure (Fin k)))
  infer_instance

/-- The canonical sequence law of `θ`. -/
noncomputable def markovSequenceMeasure (θ : MarkovParam k) : Measure (ℕ → Fin k) :=
  ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : ℕ => Fin k)
    ((θ.init : ProbabilityMeasure (Fin k)) : Measure (Fin k))
    (nextKernel (k := k) θ)

instance markovSequenceMeasure_isProbability (θ : MarkovParam k) :
    IsProbabilityMeasure (markovSequenceMeasure (k := k) θ) := by
  unfold markovSequenceMeasure
  infer_instance

/-- The initial `Iic 0` prefix law induced by `θ.init`. -/
noncomputable def initialPrefixMeasure (θ : MarkovParam k) : Measure (PrefixState k 0) :=
  ((θ.init : ProbabilityMeasure (Fin k)) : Measure (Fin k)).map
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin k)).symm

theorem markovSequenceMeasure_map_frestrictLe_zero (θ : MarkovParam k) :
    (markovSequenceMeasure (k := k) θ).map (frestrictLe (π := fun _ : ℕ => Fin k) 0) =
      initialPrefixMeasure (k := k) θ := by
  unfold markovSequenceMeasure ProbabilityTheory.Kernel.trajMeasure initialPrefixMeasure
  rw [Measure.map_comp _ _ (by fun_prop)]
  rw [ProbabilityTheory.Kernel.traj_map_frestrictLe (X := fun _ : ℕ => Fin k)]
  rw [ProbabilityTheory.Kernel.partialTraj_self, Measure.id_comp]

theorem initialPrefixMeasure_apply_singleton (θ : MarkovParam k) (x : PrefixState k 0) :
    initialPrefixMeasure (k := k) θ ({x} : Set (PrefixState k 0)) =
      wordProb (k := k) θ (listOfPrefix (k := k) 0 x) := by
  let i0 : Finset.Iic 0 := ⟨0, Finset.mem_Iic.2 le_rfl⟩
  rw [initialPrefixMeasure, Measure.map_apply
      ((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin k)).symm.measurable)
      (MeasurableSet.singleton x)]
  let a : Fin k := x i0
  have hpre :
      ((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin k)).symm) ⁻¹' ({x} : Set (PrefixState k 0))
        = ({a} : Set (Fin k)) := by
    ext y
    constructor
    · intro hy
      have : (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Fin k)).symm y = x := by simpa using hy
      change y = a
      simpa [a, i0] using congrArg (fun z : PrefixState k 0 => z i0) this
    · intro hy
      have : y = a := by simpa [a] using hy
      subst this
      have hx : uniqueElim a = x := by
        funext i
        have : i = i0 := Subsingleton.elim _ _
        subst this
        simp [a]
      simp [a, hx]
  rw [hpre]
  change (θ.init : Measure (Fin k)) ({a} : Set (Fin k)) =
    wordProb (k := k) θ (listOfPrefix (k := k) 0 x)
  have hlist : listOfPrefix (k := k) 0 x = [a] := by
    simp [listOfPrefix, dropPrefix, a, i0]
  rw [hlist]
  change ((θ.init : Measure (Fin k)) (Set.singleton a) : ℝ≥0∞) =
    wordProb (k := k) θ [a]
  simp [wordProb, wordProbNN, wordProbAux, initProb]

/-- The first strict prefix cylinder has the expected mass. -/
theorem markovSequenceMeasure_prefix_apply_zero (θ : MarkovParam k) (x : PrefixState k 0) :
    markovSequenceMeasure (k := k) θ (prefixEvent (k := k) 0 x) =
      wordProb (k := k) θ (listOfPrefix (k := k) 0 x) := by
  calc
    markovSequenceMeasure (k := k) θ (prefixEvent (k := k) 0 x)
        = ((markovSequenceMeasure (k := k) θ).map
            (frestrictLe (π := fun _ : ℕ => Fin k) 0)) ({x} : Set (PrefixState k 0)) := by
              exact (Measure.map_apply
                (measurable_frestrictLe (X := fun _ : ℕ => Fin k) 0)
                (MeasurableSet.singleton x)).symm
    _ = initialPrefixMeasure (k := k) θ ({x} : Set (PrefixState k 0)) := by
          rw [markovSequenceMeasure_map_frestrictLe_zero (k := k) θ]
    _ = wordProb (k := k) θ (listOfPrefix (k := k) 0 x) :=
          initialPrefixMeasure_apply_singleton (k := k) θ x

/-- Appending one final state to a strict prefix corresponds to appending one
final entry to the associated list. -/
@[simp] theorem dropPrefix_succAssemble (n : ℕ) (x : PrefixState k n) (b : Fin k) :
    dropPrefix (k := k) (n + 1) (succAssemble (k := k) n (x, b)) =
      Fin.snoc (dropPrefix (k := k) n x) b := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hsnoc :
        (Fin.snoc (α := fun _ : Fin (n + 1 + 1) => Fin k)
          (dropPrefix (k := k) n x) b) (Fin.last (n + 1)) = b := by
        exact
          @Fin.snoc_last (n + 1) (fun _ : Fin (n + 1 + 1) => Fin k)
            b (dropPrefix (k := k) n x)
    calc
      dropPrefix (k := k) (n + 1) (succAssemble (k := k) n (x, b)) (Fin.last (n + 1))
          = succAssemble (k := k) n (x, b) ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
              rfl
      _ = b := succAssemble_apply_last (k := k) n (x := (x, b))
      _ = (Fin.snoc (α := fun _ : Fin (n + 1 + 1) => Fin k)
            (dropPrefix (k := k) n x) b) (Fin.last (n + 1)) := hsnoc.symm
  · change
      succAssemble (k := k) n (x, b)
          ⟨(j.castSucc : Fin (n + 1 + 1)).1,
            Finset.mem_Iic.2 (Nat.le_of_lt_succ (j.castSucc : Fin (n + 1 + 1)).2)⟩ =
        (Fin.snoc (α := fun _ : Fin (n + 1 + 1) => Fin k)
          (dropPrefix (k := k) n x) b) j.castSucc
    rw [Fin.snoc_castSucc]
    simpa [dropPrefix] using
      (succAssemble_apply_le (k := k) n
        (x := (x, b))
        (i := ⟨(j.castSucc : Fin (n + 1 + 1)).1,
          Finset.mem_Iic.2 (Nat.le_of_lt_succ (j.castSucc : Fin (n + 1 + 1)).2)⟩)
        (hi := Nat.le_of_lt_succ j.2))

theorem listOfPrefix_succAssemble (n : ℕ) (x : PrefixState k n) (b : Fin k) :
    listOfPrefix (k := k) (n + 1) (succAssemble (k := k) n (x, b)) =
      listOfPrefix (k := k) n x ++ [b] := by
  rw [listOfPrefix, dropPrefix_succAssemble, List.ofFn_succ', List.concat_eq_append]
  congr
  · funext i
    simp
  · simp

/-- Snoc recursion for the auxiliary Markov word probability along any nonempty
tail. -/
theorem wordProbAux_append_singleton_of_ne_nil
    (θ : MarkovParam k) (a b : Fin k) :
    ∀ ys : List (Fin k), ∀ hys : ys ≠ [],
      wordProbAux (k := k) θ a (ys ++ [b]) =
        wordProbAux (k := k) θ a ys *
          stepProb (k := k) θ (ys.getLast hys) b
  | [], hys => False.elim (hys rfl)
  | [c], _ => by
      simp [wordProbAux, stepProb]
  | c :: d :: ys, hys => by
      have htail : d :: ys ≠ [] := List.cons_ne_nil _ _
      rw [show (c :: d :: ys ++ [b]) = c :: ((d :: ys) ++ [b]) by rfl]
      rw [wordProbAux, wordProbAux_append_singleton_of_ne_nil
        (θ := θ) (a := c) (b := b) (ys := d :: ys) htail]
      simp [wordProbAux, List.getLast_cons, mul_assoc]

/-- Snoc recursion for `wordProb` along any nonempty word. -/
theorem wordProb_append_singleton_of_ne_nil
    (θ : MarkovParam k) (ys : List (Fin k)) (hys : ys ≠ []) (b : Fin k) :
    wordProb (k := k) θ (ys ++ [b]) =
      wordProb (k := k) θ ys * stepProb (k := k) θ (ys.getLast hys) b := by
  rcases ys with _ | ⟨a, ys⟩
  · contradiction
  cases ys with
  | nil =>
      simp [wordProb, wordProbNN, wordProbAux, stepProb]
  | cons c ys =>
      rw [show (a :: c :: ys) ++ [b] = a :: ((c :: ys) ++ [b]) by rfl]
      rw [wordProb, wordProbNN, wordProb, wordProbNN]
      rw [wordProbAux_append_singleton_of_ne_nil (θ := θ) (a := a) (b := b)
        (ys := c :: ys) (List.cons_ne_nil _ _)]
      simp [wordProbAux, List.getLast_cons, mul_assoc]

/-- The final entry of a strict prefix list is its last coordinate. -/
theorem getLast_listOfPrefix
    (n : ℕ) (x : PrefixState k n) (hxne : listOfPrefix (k := k) n x ≠ []) :
    (listOfPrefix (k := k) n x).getLast hxne = lastCoord (k := k) n x := by
  cases n with
  | zero =>
      simp [listOfPrefix, dropPrefix, lastCoord]
  | succ n =>
      let xPrev : PrefixState k n := frestrictLe₂ (π := fun _ : ℕ => Fin k) (Nat.le_succ n) x
      let b : Fin k := lastCoord (k := k) (n + 1) x
      have hx :
          succAssemble (k := k) n (xPrev, b) = x := by
        simpa [xPrev, b, nextPairMap] using
          congrArg (fun f => f x) (succAssemble_nextPairMap (k := k) n)
      calc
        (listOfPrefix (k := k) (n + 1) x).getLast hxne
            = (listOfPrefix (k := k) (n + 1) (succAssemble (k := k) n (xPrev, b))).getLast
                (by simpa [hx] using hxne) := by simp [hx]
        _ = b := by
              simp [listOfPrefix_succAssemble]
        _ = lastCoord (k := k) (n + 1) x := by
              simp [b]

/-- Snoc recursion for `wordProb` along strict prefixes. -/
theorem wordProb_listOfPrefix_succAssemble
    (θ : MarkovParam k) (n : ℕ) (x : PrefixState k n) (b : Fin k) :
    wordProb (k := k) θ (listOfPrefix (k := k) (n + 1) (succAssemble (k := k) n (x, b))) =
      wordProb (k := k) θ (listOfPrefix (k := k) n x) *
        stepProb (k := k) θ (lastCoord (k := k) n x) b := by
  rw [listOfPrefix_succAssemble]
  have hxne : listOfPrefix (k := k) n x ≠ [] := by
    simp [listOfPrefix]
  simpa [getLast_listOfPrefix (k := k) n x hxne] using
    wordProb_append_singleton_of_ne_nil (k := k) θ (listOfPrefix (k := k) n x) hxne b

/-- Pair-preimage description of a strict-prefix event after appending one final
state. -/
theorem prefixEvent_succAssemble_eq_pairPreimage
    (n : ℕ) (x : PrefixState k n) (b : Fin k) :
    prefixEvent (k := k) (n + 1) (succAssemble (k := k) n (x, b)) =
      (fun ω : ℕ → Fin k => (frestrictLe n ω, ω (n + 1))) ⁻¹' ({(x, b)} : Set (PrefixState k n × Fin k)) := by
  ext ω
  constructor
  · intro h
    have h' : frestrictLe (π := fun _ : ℕ => Fin k) (n + 1) ω = succAssemble (k := k) n (x, b) := by
      simpa [prefixEvent] using h
    apply Prod.ext
    · funext i
      have hi :=
        congrArg (fun f : PrefixState k (n + 1) =>
          f ⟨i.1, Finset.mem_Iic.2 (Nat.le_trans (Finset.mem_Iic.1 i.2) (Nat.le_succ n))⟩) h'
      calc
        ω i.1 = succAssemble (k := k) n (x, b)
            ⟨i.1, Finset.mem_Iic.2 (Nat.le_trans (Finset.mem_Iic.1 i.2) (Nat.le_succ n))⟩ := hi
        _ = x i := succAssemble_apply_le (k := k) n (x := (x, b)) (hi := Finset.mem_Iic.1 i.2)
    · have hlast :=
        congrArg (fun f : PrefixState k (n + 1) => f ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) h'
      simpa [nextPairMap] using hlast
  · intro h
    have hfst : frestrictLe (π := fun _ : ℕ => Fin k) n ω = x := by
      exact congrArg Prod.fst h
    have hsnd : ω (n + 1) = b := by
      exact congrArg Prod.snd h
    change frestrictLe (π := fun _ : ℕ => Fin k) (n + 1) ω = succAssemble (k := k) n (x, b)
    funext i
    by_cases hi : i.1 ≤ n
    · have hi' :=
        congrArg (fun f : PrefixState k n => f ⟨i.1, Finset.mem_Iic.2 hi⟩) hfst
      calc
        ω i.1 = x ⟨i.1, Finset.mem_Iic.2 hi⟩ := hi'
        _ = succAssemble (k := k) n (x, b) i :=
          (succAssemble_apply_le (k := k) n (x := (x, b)) (hi := hi)).symm
    · have hi_eq : i = ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
        apply Subtype.ext
        have hi_lt : n < i.1 := Nat.lt_of_not_ge hi
        exact le_antisymm (Finset.mem_Iic.1 i.2) (Nat.succ_le_of_lt hi_lt)
      subst hi_eq
      simpa using hsnd

/-- Recursion step for strict-prefix cylinder probabilities. -/
theorem markovSequenceMeasure_prefix_apply_succAssemble
    (θ : MarkovParam k) (n : ℕ) (x : PrefixState k n) (b : Fin k) :
    markovSequenceMeasure (k := k) θ
        (prefixEvent (k := k) (n + 1) (succAssemble (k := k) n (x, b))) =
      markovSequenceMeasure (k := k) θ (prefixEvent (k := k) n x) *
        stepProb (k := k) θ (lastCoord (k := k) n x) b := by
  let μ := markovSequenceMeasure (k := k) θ
  have htraj :=
    ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => Fin k)
      (μ₀ := ((θ.init : ProbabilityMeasure (Fin k)) : Measure (Fin k)))
      (κ := nextKernel (k := k) θ) (a := n)
  have hmap :
      μ (prefixEvent (k := k) (n + 1) (succAssemble (k := k) n (x, b))) =
        ((μ.map (frestrictLe (π := fun _ : ℕ => Fin k) n)).compProd
          (nextKernel (k := k) θ n)) ({(x, b)} : Set (PrefixState k n × Fin k)) := by
    calc
      μ (prefixEvent (k := k) (n + 1) (succAssemble (k := k) n (x, b)))
          = μ ((fun ω : ℕ → Fin k => (frestrictLe n ω, ω (n + 1))) ⁻¹'
              ({(x, b)} : Set (PrefixState k n × Fin k))) := by
                simp [prefixEvent_succAssemble_eq_pairPreimage]
      _ = (μ.map (fun ω : ℕ → Fin k => (frestrictLe n ω, ω (n + 1))))
            ({(x, b)} : Set (PrefixState k n × Fin k)) := by
              symm
              exact Measure.map_apply
                (by fun_prop)
                (MeasurableSet.singleton (x, b))
      _ = ((μ.map (frestrictLe (π := fun _ : ℕ => Fin k) n)).compProd
            (nextKernel (k := k) θ n)) ({(x, b)} : Set (PrefixState k n × Fin k)) := by
              exact
                congrArg
                  (fun ν : Measure (PrefixState k n × Fin k) =>
                    ν ({(x, b)} : Set (PrefixState k n × Fin k)))
                  htraj.symm
  have hcomp :
      ((μ.map (frestrictLe (π := fun _ : ℕ => Fin k) n)).compProd
          (nextKernel (k := k) θ n)) ({(x, b)} : Set (PrefixState k n × Fin k))
        =
      (μ.map (frestrictLe (π := fun _ : ℕ => Fin k) n)) ({x} : Set (PrefixState k n)) *
        (stepProb (k := k) θ (lastCoord (k := k) n x) b : ℝ≥0∞) := by
    rw [Measure.compProd_apply (MeasurableSet.singleton (x, b))]
    change ∫⁻ z : PrefixState k n,
        nextKernel (k := k) θ n z (Prod.mk z ⁻¹' ({(x, b)} : Set (PrefixState k n × Fin k)))
          ∂(μ.map (frestrictLe (π := fun _ : ℕ => Fin k) n))
      =
      (μ.map (frestrictLe (π := fun _ : ℕ => Fin k) n)) ({x} : Set (PrefixState k n)) *
        (stepProb (k := k) θ (lastCoord (k := k) n x) b : ℝ≥0∞)
    have hpre :
        ∀ z : PrefixState k n,
          Prod.mk z ⁻¹' ({(x, b)} : Set (PrefixState k n × Fin k)) =
            if z = x then ({b} : Set (Fin k)) else ∅ := by
      intro z
      ext y
      by_cases hz : z = x
      · subst hz
        simp
      · simp [hz]
    have hkernel :
        ∀ z : PrefixState k n,
          nextKernel (k := k) θ n z (Prod.mk z ⁻¹' ({(x, b)} : Set (PrefixState k n × Fin k))) =
            if z = x then (stepProb (k := k) θ (lastCoord (k := k) n x) b : ℝ≥0∞) else 0 := by
      intro z
      by_cases hz : z = x
      · rw [hpre z, if_pos hz]
        subst hz
        rw [if_pos rfl]
        change ((nextKernel (k := k) θ n z) (Set.singleton b) : ℝ≥0∞) =
          ↑(stepProb (k := k) θ (lastCoord (k := k) n z) b)
        rw [show nextKernel (k := k) θ n z =
            (((θ.trans (lastCoord (k := k) n z) : ProbabilityMeasure (Fin k)) :
              Measure (Fin k))) by
              rfl]
        simp [stepProb]
      · simp [nextKernel, hpre, hz]
    rw [show
      (fun z : PrefixState k n =>
        nextKernel (k := k) θ n z (Prod.mk z ⁻¹' ({(x, b)} : Set (PrefixState k n × Fin k))))
        = (fun z : PrefixState k n =>
            if z = x then (stepProb (k := k) θ (lastCoord (k := k) n x) b : ℝ≥0∞) else 0) by
              funext z; exact hkernel z]
    have hxmeas : MeasurableSet ({x} : Set (PrefixState k n)) := MeasurableSet.singleton x
    rw [show
      (fun z : PrefixState k n =>
        if z = x then (stepProb (k := k) θ (lastCoord (k := k) n x) b : ℝ≥0∞) else 0)
        = Set.indicator ({x} : Set (PrefixState k n))
            (fun _ : PrefixState k n => (stepProb (k := k) θ (lastCoord (k := k) n x) b : ℝ≥0∞)) by
              funext z; by_cases hz : z = x <;> simp [hz]]
    rw [lintegral_indicator hxmeas]
    simp [lintegral_const, mul_comm]
  have hprev :
      (μ.map (frestrictLe (π := fun _ : ℕ => Fin k) n)) ({x} : Set (PrefixState k n)) =
        μ (prefixEvent (k := k) n x) := by
    exact Measure.map_apply
      (measurable_frestrictLe (X := fun _ : ℕ => Fin k) n)
      (MeasurableSet.singleton x)
  calc
    μ (prefixEvent (k := k) (n + 1) (succAssemble (k := k) n (x, b)))
        =
      ((μ.map (frestrictLe (π := fun _ : ℕ => Fin k) n)).compProd
        (nextKernel (k := k) θ n)) ({(x, b)} : Set (PrefixState k n × Fin k)) := hmap
    _ =
      (μ.map (frestrictLe (π := fun _ : ℕ => Fin k) n)) ({x} : Set (PrefixState k n)) *
        (stepProb (k := k) θ (lastCoord (k := k) n x) b : ℝ≥0∞) := hcomp
    _ = μ (prefixEvent (k := k) n x) * stepProb (k := k) θ (lastCoord (k := k) n x) b := by
          rw [hprev]

/-- Strict-prefix probabilities under the canonical sequence law are exactly
`wordProb`. -/
theorem markovSequenceMeasure_prefix_eq_wordProb
    (θ : MarkovParam k) :
    ∀ n : ℕ, ∀ x : PrefixState k n,
      markovSequenceMeasure (k := k) θ (prefixEvent (k := k) n x) =
        wordProb (k := k) θ (listOfPrefix (k := k) n x)
  | 0, x => markovSequenceMeasure_prefix_apply_zero (k := k) θ x
  | n + 1, x => by
      let xPrev : PrefixState k n :=
        frestrictLe₂ (π := fun _ : ℕ => Fin k) (Nat.le_succ n) x
      let bLast : Fin k := lastCoord (k := k) (n + 1) x
      have hx : succAssemble (k := k) n (xPrev, bLast) = x := by
        simpa [xPrev, bLast, nextPairMap] using
          congrArg (fun f => f x) (succAssemble_nextPairMap (k := k) n)
      calc
        markovSequenceMeasure (k := k) θ (prefixEvent (k := k) (n + 1) x)
            = markovSequenceMeasure (k := k) θ
                (prefixEvent (k := k) (n + 1)
                  (succAssemble (k := k) n (xPrev, bLast))) := by
                    simp [hx]
        _ =
            markovSequenceMeasure (k := k) θ (prefixEvent (k := k) n xPrev) *
              stepProb (k := k) θ (lastCoord (k := k) n xPrev) bLast :=
                markovSequenceMeasure_prefix_apply_succAssemble (k := k) θ n xPrev bLast
        _ =
            wordProb (k := k) θ (listOfPrefix (k := k) n xPrev) *
              stepProb (k := k) θ (lastCoord (k := k) n xPrev) bLast := by
                simp [markovSequenceMeasure_prefix_eq_wordProb (n := n) (x := xPrev)]
        _ =
            wordProb (k := k) θ
              (listOfPrefix (k := k) (n + 1) (succAssemble (k := k) n (xPrev, bLast))) := by
                symm
                exact wordProb_listOfPrefix_succAssemble (k := k) θ n xPrev bLast
        _ = wordProb (k := k) θ (listOfPrefix (k := k) (n + 1) x) := by
              simp [hx]

/-- Prefix-event/cylinder equivalence for lists presented via `List.ofFn`. -/
theorem prefixEvent_prefixOfFin_eq_cylinder_ofFn
    {n : ℕ} (x : Fin (n + 1) → Fin k) :
    prefixEvent (k := k) n (prefixOfFin (k := k) n x) =
      MarkovDeFinettiRecurrence.cylinder (k := k) (List.ofFn x) := by
  ext ω
  constructor
  · intro h
    have h' :
        frestrictLe (π := fun _ : ℕ => Fin k) n ω = prefixOfFin (k := k) n x := by
      simpa [prefixEvent] using h
    refine Set.mem_iInter.mpr ?_
    intro i
    have hi_lt : i.1 < n + 1 := by
      simpa [List.length_ofFn] using i.2
    have hi :=
      congrArg (fun f : PrefixState k n => f ⟨i.1, Finset.mem_Iic.2 (Nat.le_of_lt_succ hi_lt)⟩) h'
    calc
      ω i.1 = prefixOfFin (k := k) n x ⟨i.1, Finset.mem_Iic.2 (Nat.le_of_lt_succ hi_lt)⟩ := hi
      _ = (List.ofFn x).get i := by
        simp only [prefixOfFin]; exact (List.get_ofFn x i).symm
  · intro h
    change frestrictLe (π := fun _ : ℕ => Fin k) n ω = prefixOfFin (k := k) n x
    funext i
    have hi :
        ω i.1 = (List.ofFn x).get
          ⟨i.1, by simpa using Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2)⟩ := by
      exact Set.mem_iInter.mp h ⟨i.1, by simpa using Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2)⟩
    calc
      ω i.1 = (List.ofFn x).get ⟨i.1, by simpa using Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2)⟩ := hi
      _ = prefixOfFin (k := k) n x i := by
        simp only [prefixOfFin]; exact (List.get_ofFn x ⟨i.1, by simpa using Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2)⟩)

/-- The canonical sequence law of `θ` evaluates finite cylinders by `wordProb`. -/
theorem markovSequenceMeasure_cylinder_eq_wordProb
    (θ : MarkovParam k) :
    ∀ xs : List (Fin k),
      markovSequenceMeasure (k := k) θ (cylinder (k := k) xs) =
        wordProb (k := k) θ xs := by
  refine List.ofFnRec ?_
  intro n x
  cases n with
  | zero =>
      have hx : List.ofFn x = ([] : List (Fin k)) := by simp
      rw [hx]
      rw [MarkovDeFinettiRecurrence.cylinder, wordProb, wordProbNN]
      simp
  | succ n =>
      calc
        markovSequenceMeasure (k := k) θ
            (MarkovDeFinettiRecurrence.cylinder (k := k) (List.ofFn x))
            =
          markovSequenceMeasure (k := k) θ
            (prefixEvent (k := k) n (prefixOfFin (k := k) n x)) := by
              simp [prefixEvent_prefixOfFin_eq_cylinder_ofFn]
        _ =
          wordProb (k := k) θ
            (listOfPrefix (k := k) n (prefixOfFin (k := k) n x)) :=
              markovSequenceMeasure_prefix_eq_wordProb (k := k) θ n (prefixOfFin (k := k) n x)
        _ = wordProb (k := k) θ (List.ofFn x) := by
              simp [listOfPrefix_prefixOfFin]

end MarkovDeFinettiSequenceKernel

end Mettapedia.Logic
