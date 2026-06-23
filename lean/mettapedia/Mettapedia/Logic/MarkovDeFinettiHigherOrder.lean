import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.MarkovDeFinettiSequenceKernel

/-!
# Higher-Order Finite Markov Parameters via Context Reduction

This file packages an order-`m` finite-alphabet Markov law as an ordinary
first-order Markov law on length-`m` context states.

The key design choice is to keep the higher-order surface literal:
* the parameter stores an initial law on contexts and a next-symbol kernel,
* `(m+1)`-gram evidence is summarized by context-to-symbol counts,
* all sequence-law theorems are ported by reducing to `MarkovParam` on the
  finite context state space.

We keep the theorem surface honest by reusing the existing first-order sequence
kernel, rather than re-proving trajectory measure facts from scratch.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic

open MeasureTheory
open scoped NNReal ENNReal
open MarkovDeFinettiHard
open MarkovDeFinettiSequenceKernel

namespace MarkovDeFinettiHigherOrder

variable {k m : ℕ}

/-- Context states of length `m`. -/
abbrev Context (k m : ℕ) := Fin m → Fin k

/-- Finite encoded context state used to reuse the ordinary `MarkovParam` API. -/
abbrev EncodedContext (k m : ℕ) := Fin (Fintype.card (Context k m))

/-- Higher-order finite Markov parameter:
initial law on length-`m` contexts, plus a next-symbol kernel. -/
structure HigherOrderMarkovParam (k m : ℕ) where
  init : ProbabilityMeasure (Context k m)
  next : Context k m → ProbabilityMeasure (Fin k)

/-- Turn a context into its list presentation. -/
def contextToList (ctx : Context k m) : List (Fin k) :=
  List.ofFn ctx

@[simp] theorem contextToList_length (ctx : Context k m) :
    (contextToList ctx).length = m := by
  simp [contextToList]

/-- Rebuild a context from an exact-length list. -/
def contextOfList (xs : List (Fin k)) (hxs : xs.length = m) : Context k m :=
  fun i => xs.get ⟨i.1, by
    omega⟩

@[simp] theorem contextOfList_contextToList (ctx : Context k m) :
    contextOfList (k := k) (m := m) (contextToList (k := k) (m := m) ctx)
      (contextToList_length (k := k) (m := m) ctx) = ctx := by
  funext i
  simp [contextOfList, contextToList]

@[simp] theorem contextToList_contextOfList (xs : List (Fin k)) (hxs : xs.length = m) :
    contextToList (k := k) (m := m) (contextOfList (k := k) (m := m) xs hxs) = xs := by
  apply List.ext_get
  · simp [contextToList, hxs]
  · intro i hi1 hi2
    simp [contextToList, contextOfList]

theorem contextToList_injective :
    Function.Injective (contextToList (k := k) (m := m)) := by
  intro ctx₁ ctx₂ h
  simpa [contextToList] using (List.ofFn_injective (n := m) h)

/-- Shift a context by dropping the oldest symbol and appending `a`. -/
def shift (ctx : Context k m) (a : Fin k) : Context k m :=
  fun i =>
    if h : i.1 + 1 < m then ctx ⟨i.1 + 1, h⟩ else a

theorem measurable_encodeContext :
    Measurable (Fintype.equivFin (Context k m) : Context k m → EncodedContext k m) := by
  classical
  simpa using measurable_of_finite (Fintype.equivFin (Context k m))

theorem measurable_decodeContext :
    Measurable ((Fintype.equivFin (Context k m)).symm : EncodedContext k m → Context k m) := by
  classical
  simpa using measurable_of_finite ((Fintype.equivFin (Context k m)).symm)

theorem measurable_shiftEncoded (ctx : EncodedContext k m) :
    Measurable
      (fun a : Fin k =>
        (Fintype.equivFin (Context k m)) (shift (k := k) (m := m)
          ((Fintype.equivFin (Context k m)).symm ctx) a)) := by
  classical
  simpa using measurable_of_finite
    (fun a : Fin k =>
      (Fintype.equivFin (Context k m)) (shift (k := k) (m := m)
        ((Fintype.equivFin (Context k m)).symm ctx) a))

/-- Context-state reduction of a higher-order parameter to an ordinary finite
Markov parameter. -/
noncomputable def toMarkovParam (θ : HigherOrderMarkovParam k m) :
    MarkovParam (Fintype.card (Context k m)) where
  init := θ.init.map measurable_encodeContext.aemeasurable
  trans ctx :=
    (θ.next ((Fintype.equivFin (Context k m)).symm ctx)).map
      (measurable_shiftEncoded (k := k) (m := m) ctx).aemeasurable

/-- Context-word probability is just ordinary `wordProb` on the reduced
context-state chain. -/
def contextWordProb (θ : HigherOrderMarkovParam k m) (ctxs : List (Context k m)) : ℝ≥0∞ :=
  wordProb (k := Fintype.card (Context k m)) (toMarkovParam (k := k) (m := m) θ)
    (ctxs.map (Fintype.equivFin (Context k m)))

/-- The encoded context chain sequence law. -/
noncomputable def encodedContextSequenceMeasure (θ : HigherOrderMarkovParam k m) :
    Measure (ℕ → EncodedContext k m) :=
  markovSequenceMeasure (k := Fintype.card (Context k m))
    (toMarkovParam (k := k) (m := m) θ)

/-- Decode the encoded context trajectory coordinatewise. -/
def decodeContextSeq (ω : ℕ → EncodedContext k m) : ℕ → Context k m :=
  fun n => (Fintype.equivFin (Context k m)).symm (ω n)

theorem measurable_decodeContextSeq :
    Measurable (decodeContextSeq (k := k) (m := m)) := by
  unfold decodeContextSeq
  fun_prop

/-- Sequence law on genuine context trajectories. -/
noncomputable def contextSequenceMeasure (θ : HigherOrderMarkovParam k m) :
    Measure (ℕ → Context k m) :=
  (encodedContextSequenceMeasure (k := k) (m := m) θ).map
    (decodeContextSeq (k := k) (m := m))

/-- Cylinder event on context trajectories. -/
def contextCylinder (ctxs : List (Context k m)) : Set (ℕ → Context k m) :=
  ⋂ i : Fin ctxs.length, {ω | ω i.1 = ctxs[i.1]}

theorem contextCylinder_preimage_decodeContextSeq (ctxs : List (Context k m)) :
    (decodeContextSeq (k := k) (m := m)) ⁻¹' contextCylinder (k := k) (m := m) ctxs =
      MarkovDeFinettiRecurrence.cylinder
        (k := Fintype.card (Context k m))
        (ctxs.map (Fintype.equivFin (Context k m))) := by
  ext ω
  constructor
  · intro h
    refine Set.mem_iInter.mpr ?_
    intro i
    let i' : Fin ctxs.length := ⟨i.1, by simpa using i.2⟩
    have hi : decodeContextSeq (k := k) (m := m) ω i'.1 = ctxs[i'.1] :=
      Set.mem_iInter.mp h i'
    change ω i.1 = (ctxs.map (Fintype.equivFin (Context k m)))[i.1]
    simpa [decodeContextSeq, i'] using
      congrArg (Fintype.equivFin (Context k m)) hi
  · intro h
    refine Set.mem_iInter.mpr ?_
    intro i
    let i' : Fin (ctxs.map (Fintype.equivFin (Context k m))).length := ⟨i.1, by
      convert i.2 using 1
      simp⟩
    have hi : ω i'.1 = (ctxs.map (Fintype.equivFin (Context k m)))[i'.1] :=
      Set.mem_iInter.mp h i'
    change decodeContextSeq (k := k) (m := m) ω i.1 = ctxs[i.1]
    exact (Fintype.equivFin (Context k m)).injective <| by
      simpa [decodeContextSeq, i'] using hi

/-- The context-sequence law evaluates context cylinders by the reduced
context-word probability. -/
theorem contextSequenceMeasure_cylinder_eq_contextWordProb
    (θ : HigherOrderMarkovParam k m) (ctxs : List (Context k m)) :
    contextSequenceMeasure (k := k) (m := m) θ (contextCylinder (k := k) (m := m) ctxs) =
      contextWordProb (k := k) (m := m) θ ctxs := by
  have hmeas : MeasurableSet (contextCylinder (k := k) (m := m) ctxs) := by
    classical
    refine MeasurableSet.iInter ?_
    intro i
    change MeasurableSet
      ((fun ω : ℕ → Context k m => ω i.1) ⁻¹' ({ctxs[i.1]} : Set (Context k m)))
    exact (measurable_pi_apply i.1) (measurableSet_singleton (ctxs[i.1]))
  rw [contextSequenceMeasure, Measure.map_apply
    (measurable_decodeContextSeq (k := k) (m := m)) hmeas]
  rw [contextCylinder_preimage_decodeContextSeq (k := k) (m := m) ctxs]
  simp [contextWordProb, encodedContextSequenceMeasure,
    MarkovDeFinettiSequenceKernel.markovSequenceMeasure_cylinder_eq_wordProb]

/-- `(m+1)`-gram transition counts. -/
@[ext]
structure GramCounts (k m : ℕ) where
  counts : Context k m → Fin k → ℕ
deriving DecidableEq

namespace GramCounts

instance : Zero (GramCounts k m) := ⟨⟨fun _ _ => 0⟩⟩

def bump (c : GramCounts k m) (ctx : Context k m) (a : Fin k) : GramCounts k m :=
  ⟨fun x b => if x = ctx ∧ b = a then c.counts x b + 1 else c.counts x b⟩

@[simp] theorem zero_counts (ctx : Context k m) (a : Fin k) :
    (0 : GramCounts k m).counts ctx a = 0 := rfl

@[simp] theorem bump_self (c : GramCounts k m) (ctx : Context k m) (a : Fin k) :
    (bump c ctx a).counts ctx a = c.counts ctx a + 1 := by
  simp [bump]

@[simp] theorem bump_of_ne (c : GramCounts k m) {ctx x : Context k m} {a b : Fin k}
    (h : ¬(x = ctx ∧ b = a)) :
    (bump c ctx a).counts x b = c.counts x b := by
  simp [bump, h]

end GramCounts

variable [Fact (0 < m)]

/-- The final coordinate of a positive-length context. -/
def lastSymbol (ctx : Context k m) : Fin k :=
  ctx ⟨m - 1, by
    have hm : 0 < m := Fact.out
    omega⟩

theorem measurable_lastSymbol :
    Measurable (lastSymbol (k := k) (m := m)) := by
  unfold lastSymbol
  exact measurable_pi_apply _

@[simp] theorem lastSymbol_shift (ctx : Context k m) (a : Fin k) :
    lastSymbol (k := k) (m := m) (shift (k := k) (m := m) ctx a) = a := by
  unfold lastSymbol shift
  simp
  have hm : 0 < m := Fact.out
  have hnot : ¬((m - 1) + 1 < m) := by
    omega
  simp [hnot]

/-- Consecutive context states extracted from a symbol word. This is only
defined once the word is at least as long as one context. -/
def contextPathOfWord (xs : List (Fin k)) (hxs : m ≤ xs.length) : List (Context k m) :=
  List.ofFn (fun i : Fin (xs.length - m + 1) =>
    fun j : Fin m =>
      xs.get ⟨i.1 + j.1, by
        have hi : i.1 < xs.length - m + 1 := i.2
        have hj : j.1 < m := j.2
        omega⟩)

omit [Fact (0 < m)] in
@[simp] theorem contextPathOfWord_length (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    (contextPathOfWord (k := k) (m := m) xs hxs).length = xs.length - m + 1 := by
  simp [contextPathOfWord]

omit [Fact (0 < m)] in
@[simp] theorem contextPathOfWord_get
    (xs : List (Fin k)) (hxs : m ≤ xs.length)
    (i : Fin (xs.length - m + 1)) (j : Fin m) :
    (contextPathOfWord (k := k) (m := m) xs hxs)[i.1] j =
      xs.get ⟨i.1 + j.1, by
        have hi : i.1 < xs.length - m + 1 := i.2
        have hj : j.1 < m := j.2
        omega⟩ := by
  simp [contextPathOfWord]

omit [Fact (0 < m)] in
@[simp] theorem contextPathOfWord_zero
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    (contextPathOfWord (k := k) (m := m) xs hxs)[0] =
      contextOfList (k := k) (m := m) (xs.take m) (by
        rw [List.length_take]
        omega) := by
  funext j
  simp [contextOfList, contextPathOfWord]

/-- Recover the raw symbol word determined by a nonempty finite context
prefix. -/
def wordOfContextPrefix {n : ℕ} (p : Fin (n + 1) → Context k m) : List (Fin k) :=
  contextToList (k := k) (m := m) (p 0) ++
    List.ofFn (fun i : Fin n => lastSymbol (k := k) (m := m) (p i.succ))

/-- Recover the raw symbol word determined by a finite list of context states. -/
def wordOfContextList : List (Context k m) → List (Fin k)
  | [] => []
  | ctx :: rest => contextToList (k := k) (m := m) ctx ++
      rest.map (lastSymbol (k := k) (m := m))

@[simp] theorem wordOfContextList_nil :
    wordOfContextList (k := k) (m := m) ([] : List (Context k m)) = [] := rfl

@[simp] theorem wordOfContextList_cons (ctx : Context k m) (rest : List (Context k m)) :
    wordOfContextList (k := k) (m := m) (ctx :: rest) =
      contextToList (k := k) (m := m) ctx ++
        rest.map (lastSymbol (k := k) (m := m)) := rfl

@[simp] theorem wordOfContextList_take
    (ctx : Context k m) (rest : List (Context k m)) :
    (wordOfContextList (k := k) (m := m) (ctx :: rest)).take m =
      contextToList (k := k) (m := m) ctx := by
  simp [wordOfContextList, contextToList]

@[simp] theorem wordOfContextList_drop
    (ctx : Context k m) (rest : List (Context k m)) :
    (wordOfContextList (k := k) (m := m) (ctx :: rest)).drop m =
      rest.map (lastSymbol (k := k) (m := m)) := by
  simp [wordOfContextList, contextToList]

@[simp] theorem wordOfContextList_ofFn
    {n : ℕ} (p : Fin (n + 1) → Context k m) :
    wordOfContextList (k := k) (m := m) (List.ofFn p) =
      wordOfContextPrefix (k := k) (m := m) p := by
  have hfun :
      (lastSymbol (k := k) (m := m) ∘ fun i : Fin n => p i.succ) =
        (fun i : Fin n => lastSymbol (k := k) (m := m) (p i.succ)) := by
    funext i
    rfl
  rw [List.ofFn_succ]
  simp [wordOfContextList, wordOfContextPrefix, hfun]

@[simp] theorem wordOfContextPrefix_length {n : ℕ} (p : Fin (n + 1) → Context k m) :
    (wordOfContextPrefix (k := k) (m := m) p).length = m + n := by
  simp [wordOfContextPrefix, contextToList]

@[simp] theorem wordOfContextPrefix_take {n : ℕ} (p : Fin (n + 1) → Context k m) :
    (wordOfContextPrefix (k := k) (m := m) p).take m =
      contextToList (k := k) (m := m) (p 0) := by
  simp [wordOfContextPrefix, contextToList]

@[simp] theorem wordOfContextPrefix_get_initial {n : ℕ} (p : Fin (n + 1) → Context k m)
    {i : ℕ} (hi : i < m) :
    (wordOfContextPrefix (k := k) (m := m) p).get
      ⟨i, by
        have hi' : i < m + n := lt_of_lt_of_le hi (Nat.le_add_right m n)
        simpa [wordOfContextPrefix_length] using hi'⟩ =
      p 0 ⟨i, hi⟩ := by
  simp [wordOfContextPrefix, contextToList, hi]

@[simp] theorem wordOfContextPrefix_drop {n : ℕ} (p : Fin (n + 1) → Context k m) :
    (wordOfContextPrefix (k := k) (m := m) p).drop m =
      List.ofFn (fun i : Fin n => lastSymbol (k := k) (m := m) (p i.succ)) := by
  simp [wordOfContextPrefix, contextToList]

@[simp] theorem wordOfContextPrefix_get_tail {n : ℕ} (p : Fin (n + 1) → Context k m)
    (i : Fin n) :
    (wordOfContextPrefix (k := k) (m := m) p).get
      ⟨m + i.1, by
        rw [wordOfContextPrefix_length]
        exact Nat.add_lt_add_left i.2 m⟩ =
      lastSymbol (k := k) (m := m) (p i.succ) := by
  rw [List.get_eq_getElem, List.getElem_drop' (xs := wordOfContextPrefix (k := k) (m := m) p)
      (i := m) (j := i.1) (by
        rw [wordOfContextPrefix_length]
        exact Nat.add_lt_add_left i.2 m)]
  simp [wordOfContextPrefix_drop]

/-- The first `n` context states of an infinite context trajectory. -/
def contextPrefixMap (n : ℕ) : (ℕ → Context k m) → Fin n → Context k m :=
  fun ω i => ω i.1

omit [Fact (0 < m)] in
theorem measurable_contextPrefixMap (n : ℕ) :
    Measurable (contextPrefixMap (k := k) (m := m) n) := by
  unfold contextPrefixMap
  fun_prop

omit [Fact (0 < m)] in
theorem contextPrefixMap_preimage_singleton_eq_contextCylinder_ofFn
    {n : ℕ} (p : Fin n → Context k m) :
    contextPrefixMap (k := k) (m := m) n ⁻¹' ({p} : Set (Fin n → Context k m)) =
      contextCylinder (k := k) (m := m) (List.ofFn p) := by
  ext ω
  constructor
  · intro h
    refine Set.mem_iInter.mpr ?_
    intro i
    let i' : Fin n := ⟨i.1, by simpa using i.2⟩
    have hi : contextPrefixMap (k := k) (m := m) n ω = p := by simpa using h
    have hcoord := congrArg (fun q : Fin n → Context k m => q i') hi
    simpa [contextPrefixMap] using hcoord
  · intro h
    funext i
    have hi_mem : i.1 < (List.ofFn p).length := by
      simp [List.length_ofFn, i.2]
    have hi' :
        ω i.1 = (List.ofFn p).get ⟨i.1, hi_mem⟩ := by
      exact Set.mem_iInter.mp h ⟨i.1, hi_mem⟩
    change ω i.1 = p i
    have hget : (List.ofFn p).get ⟨i.1, hi_mem⟩ = p i := by
      simp
    exact hi'.trans hget

/-- Project a context trajectory to its raw symbol trajectory: the initial
context gives the first `m` symbols, and each later symbol is the final
coordinate of the next context. -/
def symbolSequenceOfContextTrajectory (ω : ℕ → Context k m) : ℕ → Fin k :=
  fun n =>
    if h : n < m then
      ω 0 ⟨n, h⟩
    else
      lastSymbol (k := k) (m := m) (ω (n - m + 1))

theorem measurable_symbolSequenceOfContextTrajectory :
    Measurable (symbolSequenceOfContextTrajectory (k := k) (m := m)) := by
  rw [measurable_pi_iff]
  intro n
  by_cases h : n < m
  · let idx : Fin m := ⟨n, h⟩
    -- 4.31: the `Measurable.comp` term is `(· ⟨n,h⟩) ∘ (· 0)`, defeq to the eta-reduced goal
    -- `fun x => x 0 ⟨n,⋯⟩`; `simp only [Function.comp_def]` bridges the two normal forms.
    simp only [symbolSequenceOfContextTrajectory, h, idx, ↓reduceDIte]
    exact ((measurable_pi_apply (a := idx) :
      Measurable (fun ctx : Context k m => ctx idx)).comp
        (measurable_pi_apply (a := (0 : ℕ))))
  · simp [symbolSequenceOfContextTrajectory, h]
    exact (measurable_lastSymbol (k := k) (m := m)).comp
      (measurable_pi_apply (a := n - m + 1))

/-- Raw symbol sequence law induced by the reduced context chain. -/
noncomputable def higherOrderSequenceMeasure (θ : HigherOrderMarkovParam k m) :
    Measure (ℕ → Fin k) :=
  (contextSequenceMeasure (k := k) (m := m) θ).map
    (symbolSequenceOfContextTrajectory (k := k) (m := m))

/-- The canonical finite tuple of contexts induced by a long raw word. -/
def contextPathTupleOfWord (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    Fin (xs.length - m + 1) → Context k m :=
  fun i =>
    (contextPathOfWord (k := k) (m := m) xs hxs).get
      ⟨i.1, by
        simpa [contextPathOfWord_length (k := k) (m := m) xs hxs] using i.2⟩

omit [Fact (0 < m)] in
@[simp] theorem contextPathTupleOfWord_ofFn
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    List.ofFn (contextPathTupleOfWord (k := k) (m := m) xs hxs) =
      contextPathOfWord (k := k) (m := m) xs hxs := by
  simpa [contextPathTupleOfWord, contextPathOfWord_length (k := k) (m := m) xs hxs] using
    (List.ofFn_get (contextPathOfWord (k := k) (m := m) xs hxs))

omit [Fact (0 < m)] in
@[simp] theorem contextPathTupleOfWord_zero
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    contextPathTupleOfWord (k := k) (m := m) xs hxs 0 =
      contextOfList (k := k) (m := m) (xs.take m) (by
        rw [List.length_take]
        omega) := by
  rw [contextPathTupleOfWord]
  exact contextPathOfWord_zero (k := k) (m := m) xs hxs

@[simp] theorem lastSymbol_contextPathTupleOfWord_succ
    (xs : List (Fin k)) (hxs : m ≤ xs.length) (i : Fin (xs.length - m)) :
    lastSymbol (k := k) (m := m)
      (contextPathTupleOfWord (k := k) (m := m) xs hxs i.succ) =
      xs.get ⟨m + i.1, by omega⟩ := by
  have hm : 0 < m := Fact.out
  have h :=
    contextPathOfWord_get (k := k) (m := m) xs hxs i.succ
      ⟨m - 1, Nat.sub_lt hm (by decide)⟩
  have hidx : i.1 + 1 + (m - 1) = m + i.1 := by
    omega
  -- 4.31: `contextPathOfWord_get` now produces the `getElem` form while
  -- `contextPathTupleOfWord` is a `List.get`; reduce both with simp, then bridge the
  -- index `Fin.mk` value via `hidx` (the underlying `List.get` is proof-irrelevant).
  simp only [lastSymbol, contextPathTupleOfWord, List.get_eq_getElem, contextPathOfWord_get]
  exact getElem_congr_idx (by simp only [Fin.val_succ]; omega)

omit [Fact (0 < m)] in
theorem contextPathTupleOfWord_succ
    (xs : List (Fin k)) (hxs : m ≤ xs.length) (i : Fin (xs.length - m)) :
    contextPathTupleOfWord (k := k) (m := m) xs hxs i.succ =
      shift (k := k) (m := m)
        (contextPathTupleOfWord (k := k) (m := m) xs hxs ⟨i.1, by omega⟩)
        (xs.get ⟨m + i.1, by omega⟩) := by
  funext j
  by_cases hj : j.1 + 1 < m
  · have hleft :=
      contextPathOfWord_get (k := k) (m := m) xs hxs i.succ j
    have hprev :=
      contextPathOfWord_get (k := k) (m := m) xs hxs
        ⟨i.1, by omega⟩ ⟨j.1 + 1, hj⟩
    calc
      contextPathTupleOfWord (k := k) (m := m) xs hxs i.succ j =
          xs.get ⟨i.1 + (j.1 + 1), by omega⟩ := by
            -- 4.31: `contextPathOfWord_get` is now in `getElem` form; bridge `.get`→`[·]`,
            -- then the residual is a `getElem` index equality.
            simp only [contextPathTupleOfWord, List.get_eq_getElem, contextPathOfWord_get]
            exact getElem_congr_idx (by simp only [Fin.val_succ]; omega)
      _ =
          shift (k := k) (m := m)
            (contextPathTupleOfWord (k := k) (m := m) xs hxs ⟨i.1, by omega⟩)
            (xs.get ⟨m + i.1, by omega⟩) j := by
            symm
            simpa [contextPathTupleOfWord, shift, hj, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              using hprev
  · have hmj : j.1 = m - 1 := by
      omega
    have hleft :=
      contextPathOfWord_get (k := k) (m := m) xs hxs i.succ j
    have hidx : i.1 + 1 + j.1 = m + i.1 := by
      omega
    calc
      contextPathTupleOfWord (k := k) (m := m) xs hxs i.succ j =
          xs.get ⟨i.1 + 1 + j.1, by omega⟩ := by
            -- 4.31: bridge `.get`→`[·]`, fire `contextPathOfWord_get`, then close the
            -- residual `getElem` index equality (`↑i.succ + ↑j = ↑i + 1 + ↑j`).
            simp only [contextPathTupleOfWord, List.get_eq_getElem, contextPathOfWord_get]
            exact getElem_congr_idx (by simp only [Fin.val_succ])
      _ = xs.get ⟨m + i.1, by omega⟩ := by
            simp [hidx]
      _ =
          shift (k := k) (m := m)
            (contextPathTupleOfWord (k := k) (m := m) xs hxs ⟨i.1, by omega⟩)
            (xs.get ⟨m + i.1, by omega⟩) j := by
            simp [shift, hj]

@[simp] theorem wordOfContextPrefix_contextPathTupleOfWord
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    wordOfContextPrefix (k := k) (m := m)
      (contextPathTupleOfWord (k := k) (m := m) xs hxs) = xs := by
  apply List.ext_get
  · simp [wordOfContextPrefix_length]
    omega
  · intro n hnWord hnXs
    by_cases hn : n < m
    · have hinit :
          (wordOfContextPrefix (k := k) (m := m)
            (contextPathTupleOfWord (k := k) (m := m) xs hxs)).get ⟨n, hnWord⟩ =
            contextPathTupleOfWord (k := k) (m := m) xs hxs 0 ⟨n, hn⟩ := by
          simpa using
            (wordOfContextPrefix_get_initial (k := k) (m := m)
              (contextPathTupleOfWord (k := k) (m := m) xs hxs) hn)
      calc
        (wordOfContextPrefix (k := k) (m := m)
          (contextPathTupleOfWord (k := k) (m := m) xs hxs)).get ⟨n, hnWord⟩ =
            contextPathTupleOfWord (k := k) (m := m) xs hxs 0 ⟨n, hn⟩ := hinit
        _ = xs.get ⟨n, hnXs⟩ := by
          rw [contextPathTupleOfWord_zero (k := k) (m := m) xs hxs]
          simp [contextOfList, List.get_eq_getElem, List.getElem_take]
    · let i : Fin (xs.length - m) := ⟨n - m, by omega⟩
      have hnEq : n = m + i.1 := by
        simp [i]
        omega
      have htail :
          (wordOfContextPrefix (k := k) (m := m)
            (contextPathTupleOfWord (k := k) (m := m) xs hxs)).get ⟨n, hnWord⟩ =
            lastSymbol (k := k) (m := m)
              (contextPathTupleOfWord (k := k) (m := m) xs hxs i.succ) := by
          simpa [hnEq] using
            (wordOfContextPrefix_get_tail (k := k) (m := m)
              (contextPathTupleOfWord (k := k) (m := m) xs hxs) i)
      calc
        (wordOfContextPrefix (k := k) (m := m)
          (contextPathTupleOfWord (k := k) (m := m) xs hxs)).get ⟨n, hnWord⟩ =
            lastSymbol (k := k) (m := m)
              (contextPathTupleOfWord (k := k) (m := m) xs hxs i.succ) := htail
        _ = xs.get ⟨m + i.1, by omega⟩ :=
          lastSymbol_contextPathTupleOfWord_succ (k := k) (m := m) xs hxs i
        _ = xs.get ⟨n, hnXs⟩ := by
          simp [hnEq]

/-- `(m+1)`-gram counts read off a consecutive context path. -/
def gramCountsOfPath : List (Context k m) → GramCounts k m
  | [] => 0
  | [_] => 0
  | ctx :: nextCtx :: rest =>
      GramCounts.bump (k := k) (m := m)
        (gramCountsOfPath (nextCtx :: rest)) ctx (lastSymbol (k := k) (m := m) nextCtx)

@[simp] theorem gramCountsOfPath_nil :
    gramCountsOfPath (k := k) (m := m) ([] : List (Context k m)) = 0 := rfl

@[simp] theorem gramCountsOfPath_singleton (ctx : Context k m) :
    gramCountsOfPath (k := k) (m := m) [ctx] = 0 := rfl

@[simp] theorem gramCountsOfPath_cons_cons
    (ctx nextCtx : Context k m) (rest : List (Context k m)) :
    gramCountsOfPath (k := k) (m := m) (ctx :: nextCtx :: rest) =
      GramCounts.bump (k := k) (m := m)
        (gramCountsOfPath (k := k) (m := m) (nextCtx :: rest))
        ctx (lastSymbol (k := k) (m := m) nextCtx) := rfl

/-- Recursively scan future symbols starting from an exposed context, updating
the `(m+1)`-gram counts and final context. -/
def summaryAux (ctx : Context k m) (c : GramCounts k m) : List (Fin k) →
    GramCounts k m × Context k m
  | [] => (c, ctx)
  | a :: rest =>
      summaryAux (shift (k := k) (m := m) ctx a)
        (GramCounts.bump (k := k) (m := m) c ctx a) rest

omit [Fact (0 < m)] in
theorem summaryAux_append_singleton
    (ctx : Context k m) (c : GramCounts k m) (xs : List (Fin k)) (a : Fin k) :
    summaryAux (k := k) (m := m) ctx c (xs ++ [a]) =
      let r := summaryAux (k := k) (m := m) ctx c xs
      (GramCounts.bump (k := k) (m := m) r.1 r.2 a,
        shift (k := k) (m := m) r.2 a) := by
  induction xs generalizing ctx c with
  | nil =>
      simp [summaryAux]
  | cons b xs ih =>
      simp [summaryAux, ih, List.cons_append]

/-- Context-word probability induced by a concrete symbol word of length at
least `m`. -/
def longWordProb (θ : HigherOrderMarkovParam k m) (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    ℝ≥0∞ :=
  contextWordProb (k := k) (m := m) θ (contextPathOfWord (k := k) (m := m) xs hxs)

/-- The short-prefix initial event: the first `xs.length` symbols agree with
`xs` inside the initial context. -/
def initialPrefixSet (xs : List (Fin k)) (hxs : xs.length ≤ m) : Set (Context k m) :=
  {ctx | ∀ i : Fin xs.length, ctx ⟨i.1, by omega⟩ = xs.get i}

/-- Higher-order symbol-word probability:
short words are measured directly against the initial context law, while words
of length at least `m` are measured by the reduced context chain. -/
def wordProb (θ : HigherOrderMarkovParam k m) (xs : List (Fin k)) : ℝ≥0∞ :=
  if hxs : xs.length < m then
    (θ.init : Measure (Context k m)) (initialPrefixSet (k := k) (m := m) xs (Nat.le_of_lt hxs))
  else
    longWordProb (k := k) (m := m) θ xs (Nat.le_of_not_lt hxs)

omit [Fact (0 < m)] in
theorem wordProb_eq_initialPrefix_of_lt
    (θ : HigherOrderMarkovParam k m) (xs : List (Fin k)) (hxs : xs.length < m) :
    wordProb (k := k) (m := m) θ xs =
      (θ.init : Measure (Context k m))
        (initialPrefixSet (k := k) (m := m) xs (Nat.le_of_lt hxs)) := by
  simp [wordProb, hxs]

omit [Fact (0 < m)] in
theorem wordProb_eq_longWordProb_of_le
    (θ : HigherOrderMarkovParam k m) (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    wordProb (k := k) (m := m) θ xs =
      longWordProb (k := k) (m := m) θ xs hxs := by
  simp [wordProb, not_lt_of_ge hxs]

omit [Fact (0 < m)] in
theorem contextSequenceMeasure_contextPath_eq_longWordProb
    (θ : HigherOrderMarkovParam k m) (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    contextSequenceMeasure (k := k) (m := m) θ
        (contextCylinder (k := k) (m := m) (contextPathOfWord (k := k) (m := m) xs hxs)) =
      longWordProb (k := k) (m := m) θ xs hxs := by
  simp [longWordProb, contextSequenceMeasure_cylinder_eq_contextWordProb]

/-- Summary of a word once enough symbols exist to expose one full context:
the `(m+1)`-gram counts together with the final context. -/
def summary (xs : List (Fin k)) : Option (GramCounts k m × Context k m) :=
  if hxs : m ≤ xs.length then
    some <| summaryAux (k := k) (m := m)
      (contextOfList (k := k) (m := m) (xs.take m) (by
        rw [List.length_take]
        omega))
      0
      (xs.drop m)
  else
    none

omit [Fact (0 < m)] in
theorem summary_eq_none_of_lt {xs : List (Fin k)} (hxs : xs.length < m) :
    summary (k := k) (m := m) xs = none := by
  simp [summary, Nat.not_le_of_lt hxs]

omit [Fact (0 < m)] in
theorem summary_eq_some_of_ge {xs : List (Fin k)} (hxs : m ≤ xs.length) :
    summary (k := k) (m := m) xs =
      some
        (summaryAux (k := k) (m := m)
          (contextOfList (k := k) (m := m) (xs.take m) (by
            rw [List.length_take]
            omega))
          0
          (xs.drop m)) := by
  simp [summary, hxs]

omit [Fact (0 < m)] in
theorem summary_eq_some_of_length_eq {xs : List (Fin k)} (hxs : xs.length = m) :
    summary (k := k) (m := m) xs =
      some (0, contextOfList (k := k) (m := m) xs hxs) := by
  rw [summary_eq_some_of_ge (k := k) (m := m) (xs := xs)]
  · have htake : xs.take m = xs := by
      simp [List.take_eq_self_iff, hxs]
    have hdrop : xs.drop m = [] := by
      simp [List.drop_eq_nil_of_le, hxs]
    have hctx :
        contextOfList (k := k) (m := m) (xs.take m) (by
          rw [List.length_take]
          omega) = contextOfList (k := k) (m := m) xs hxs := by
      funext i
      simp [contextOfList, htake]
    simp [summaryAux, hdrop, hctx]
  · omega

omit [Fact (0 < m)] in
theorem summary_append_singleton {xs : List (Fin k)} (a : Fin k) (hxs : m ≤ xs.length) :
    summary (k := k) (m := m) (xs ++ [a]) =
      match summary (k := k) (m := m) xs with
      | none => none
      | some r =>
          some
            (GramCounts.bump (k := k) (m := m) r.1 r.2 a,
              shift (k := k) (m := m) r.2 a) := by
  have hxs' : m ≤ (xs ++ [a]).length := by
    simp
    omega
  rw [summary_eq_some_of_ge (k := k) (m := m) (xs := xs ++ [a]) hxs',
    summary_eq_some_of_ge (k := k) (m := m) (xs := xs) hxs]
  have htake :
      (xs ++ [a]).take m = xs.take m := by
    simpa using List.take_append_of_le_length (l₁ := xs) (l₂ := [a]) (i := m) hxs
  have hdrop :
      (xs ++ [a]).drop m = xs.drop m ++ [a] := by
    simpa using List.drop_append_of_le_length (l₁ := xs) (l₂ := [a]) (i := m) hxs
  have hctx :
      contextOfList (k := k) (m := m) ((xs ++ [a]).take m) (by
        rw [List.length_take]
        omega) =
      contextOfList (k := k) (m := m) (xs.take m) (by
        rw [List.length_take]
        omega) := by
    funext i
    simp [contextOfList, htake]
  simp [hdrop, summaryAux_append_singleton, hctx]

/-- Tail-consistency of context prefixes: every next context is obtained by
shifting the current one and appending the final symbol of the next context. -/
def consistentTail (ctx : Context k m) : List (Context k m) → Prop
  | [] => True
  | nextCtx :: rest =>
      nextCtx = shift (k := k) (m := m) ctx (lastSymbol (k := k) (m := m) nextCtx) ∧
        consistentTail nextCtx rest

/-- Finite context prefixes that can arise from a genuine symbol path. -/
def prefixShiftConsistent : List (Context k m) → Prop
  | [] => True
  | ctx :: rest => consistentTail (k := k) (m := m) ctx rest

theorem prefixShiftConsistent_get_succ :
    ∀ {ctxs : List (Context k m)} {i : ℕ}
      (_hcons : prefixShiftConsistent (k := k) (m := m) ctxs)
      (hi : i + 1 < ctxs.length),
      ctxs.get ⟨i + 1, hi⟩ =
        shift (k := k) (m := m)
          (ctxs.get ⟨i, by omega⟩)
          (lastSymbol (k := k) (m := m) (ctxs.get ⟨i + 1, hi⟩))
  := by
  intro ctxs i
  induction ctxs generalizing i with
  | nil =>
      intro hcons hi
      simp at hi
  | cons ctx rest ih =>
      cases rest with
      | nil =>
          intro hcons hi
          simp at hi
      | cons next rest =>
          intro hcons hi
          rcases hcons with ⟨hstep, htail⟩
          cases i with
          | zero =>
              simpa using hstep
          | succ i =>
              have hi' : i + 1 < (next :: rest).length := by
                simpa using hi
              simpa [List.get, Nat.succ_eq_add_one] using ih htail hi'

theorem contextPrefix_eq_contextPathTupleOfWord_of_prefixShiftConsistent_of_word
    (xs : List (Fin k)) (hxs : m ≤ xs.length)
    {p : Fin (xs.length - m + 1) → Context k m}
    (hword : wordOfContextPrefix (k := k) (m := m) p = xs)
    (hcons : prefixShiftConsistent (k := k) (m := m) (List.ofFn p)) :
    p = contextPathTupleOfWord (k := k) (m := m) xs hxs := by
  funext i
  have hmain :
      ∀ n (hn : n < xs.length - m + 1),
        p ⟨n, hn⟩ =
          contextPathTupleOfWord (k := k) (m := m) xs hxs ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hp0 :
            p 0 =
              contextPathTupleOfWord (k := k) (m := m) xs hxs 0 := by
          apply contextToList_injective (k := k) (m := m)
          calc
            contextToList (k := k) (m := m) (p 0) = xs.take m := by
              simpa using congrArg (List.take m) hword
            _ =
                contextToList (k := k) (m := m)
                  (contextPathTupleOfWord (k := k) (m := m) xs hxs 0) := by
                rw [contextPathTupleOfWord_zero (k := k) (m := m) xs hxs]
                simp
        simpa using hp0
    | succ n ihn =>
        intro hn
        have hnPrev : n < xs.length - m + 1 := by
          omega
        have hnTail : n < xs.length - m := by
          omega
        have hstep :
            p ⟨n + 1, hn⟩ =
              shift (k := k) (m := m)
                (p ⟨n, hnPrev⟩)
                (lastSymbol (k := k) (m := m) (p ⟨n + 1, hn⟩)) := by
          have hstep' :=
            prefixShiftConsistent_get_succ (k := k) (m := m)
              (ctxs := List.ofFn p) (i := n) hcons (by
                simpa using hn)
          have hnOfFn : n < (List.ofFn p).length := by
            simpa [List.length_ofFn] using hnPrev
          have hnCons : n < (p 0 :: List.ofFn (fun i => p i.succ)).length := by
            simpa [List.ofFn_succ] using hnPrev
          have hprevElem :
              (p 0 :: List.ofFn (fun i => p i.succ))[n]'hnCons = p ⟨n, hnPrev⟩ := by
            simpa [List.ofFn_succ] using
              (List.getElem_ofFn (f := p) (i := n) (h := hnOfFn))
          calc
            p ⟨n + 1, hn⟩ =
                shift (k := k) (m := m)
                  ((p 0 :: List.ofFn (fun i => p i.succ))[n]'hnCons)
                  (lastSymbol (k := k) (m := m) (p ⟨n + 1, hn⟩)) := by
                    simpa [List.ofFn_succ, hnCons] using hstep'
            _ =
                shift (k := k) (m := m)
                  (p ⟨n, hnPrev⟩)
                  (lastSymbol (k := k) (m := m) (p ⟨n + 1, hn⟩)) := by
                    rw [hprevElem]
        have hlast :
            lastSymbol (k := k) (m := m) (p ⟨n + 1, hn⟩) =
              xs.get ⟨m + n, by omega⟩ := by
          have htail :=
            wordOfContextPrefix_get_tail (k := k) (m := m) p ⟨n, hnTail⟩
          simpa [hword] using htail.symm
        calc
          p ⟨n + 1, hn⟩ =
              shift (k := k) (m := m)
                (p ⟨n, hnPrev⟩)
                (lastSymbol (k := k) (m := m) (p ⟨n + 1, hn⟩)) := hstep
          _ =
              shift (k := k) (m := m)
                (contextPathTupleOfWord (k := k) (m := m) xs hxs ⟨n, hnPrev⟩)
                (xs.get ⟨m + n, by omega⟩) := by
              rw [ihn hnPrev, hlast]
          _ =
              contextPathTupleOfWord (k := k) (m := m) xs hxs ⟨n + 1, hn⟩ := by
              simpa using
                (contextPathTupleOfWord_succ (k := k) (m := m) xs hxs ⟨n, hnTail⟩).symm
  exact hmain i.1 i.2

open scoped BigOperators

noncomputable def matchingContextPrefixFinset
    (xs : List (Fin k)) :
    Finset (Fin (xs.length - m + 1) → Context k m) :=
  Finset.univ.filter (fun p =>
    wordOfContextPrefix (k := k) (m := m) p = xs)

theorem mem_matchingContextPrefixFinset_iff
    (xs : List (Fin k))
    (p : Fin (xs.length - m + 1) → Context k m) :
    p ∈ matchingContextPrefixFinset (k := k) (m := m) xs ↔
      wordOfContextPrefix (k := k) (m := m) p = xs := by
  classical
  simp [matchingContextPrefixFinset]

theorem contextPathTupleOfWord_mem_matchingContextPrefixFinset
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    contextPathTupleOfWord (k := k) (m := m) xs hxs ∈
      matchingContextPrefixFinset (k := k) (m := m) xs := by
  classical
  simp [matchingContextPrefixFinset, wordOfContextPrefix_contextPathTupleOfWord]

theorem wordOfContextPrefix_contextPrefixMap_eq_symbolPrefix
    (ω : ℕ → Context k m) (n : ℕ) :
    wordOfContextPrefix (k := k) (m := m)
      (contextPrefixMap (k := k) (m := m) (n + 1) ω) =
      List.ofFn (fun i : Fin (m + n) =>
        symbolSequenceOfContextTrajectory (k := k) (m := m) ω i.1) := by
  apply List.ext_get
  · simp [wordOfContextPrefix_length]
  · intro i hiWord hiSeq
    by_cases hi : i < m
    · have hleft :
          (wordOfContextPrefix (k := k) (m := m)
            (contextPrefixMap (k := k) (m := m) (n + 1) ω)).get ⟨i, hiWord⟩ =
              ω 0 ⟨i, hi⟩ := by
        simpa [contextPrefixMap] using
          (wordOfContextPrefix_get_initial (k := k) (m := m)
            (contextPrefixMap (k := k) (m := m) (n + 1) ω) hi)
      calc
        (wordOfContextPrefix (k := k) (m := m)
          (contextPrefixMap (k := k) (m := m) (n + 1) ω)).get ⟨i, hiWord⟩ =
            ω 0 ⟨i, hi⟩ := hleft
        _ =
            (List.ofFn (fun i : Fin (m + n) =>
              symbolSequenceOfContextTrajectory (k := k) (m := m) ω i.1)).get
              ⟨i, hiSeq⟩ := by
            rw [List.get_ofFn]
            simp [symbolSequenceOfContextTrajectory, hi]
    · have hiSeq' : i < m + n := by
        simpa using hiSeq
      let j : Fin n := ⟨i - m, by omega⟩
      have hij : i = m + j.1 := by
        simp [j]
        omega
      have hleft :
          (wordOfContextPrefix (k := k) (m := m)
            (contextPrefixMap (k := k) (m := m) (n + 1) ω)).get ⟨i, hiWord⟩ =
              lastSymbol (k := k) (m := m) (ω (j.1 + 1)) := by
        simpa [contextPrefixMap, hij, Nat.add_assoc] using
          (wordOfContextPrefix_get_tail (k := k) (m := m)
            (contextPrefixMap (k := k) (m := m) (n + 1) ω) j)
      calc
        (wordOfContextPrefix (k := k) (m := m)
          (contextPrefixMap (k := k) (m := m) (n + 1) ω)).get ⟨i, hiWord⟩ =
            lastSymbol (k := k) (m := m) (ω (j.1 + 1)) := hleft
        _ =
            (List.ofFn (fun i : Fin (m + n) =>
              symbolSequenceOfContextTrajectory (k := k) (m := m) ω i.1)).get
              ⟨i, hiSeq⟩ := by
            have hidx : i - m + 1 = j.1 + 1 := by
              simp [j]
            calc
              lastSymbol (k := k) (m := m) (ω (j.1 + 1)) =
                  symbolSequenceOfContextTrajectory (k := k) (m := m) ω i := by
                    simp [symbolSequenceOfContextTrajectory, hi, hidx]
              _ =
                  (List.ofFn (fun i : Fin (m + n) =>
                    symbolSequenceOfContextTrajectory (k := k) (m := m) ω i.1)).get
                    ⟨i, hiSeq⟩ := by
                      rw [List.get_ofFn]
                      simp

theorem mem_cylinder_iff_prefix_eq
    (xs : List (Fin k)) (ω : ℕ → Fin k) :
    ω ∈ MarkovDeFinettiRecurrence.cylinder (k := k) xs ↔
      List.ofFn (fun i : Fin xs.length => ω i.1) = xs := by
  constructor
  · intro h
    apply List.ext_get
    · simp
    · intro i hi1 hi2
      have hi : ω i = xs[i] := Set.mem_iInter.mp h ⟨i, hi2⟩
      simpa [List.get_eq_getElem, List.get_ofFn] using hi
  · intro h
    refine Set.mem_iInter.mpr ?_
    intro i
    have h' : List.ofFn (fun j : Fin xs.length => ω j.1) = List.ofFn xs.get := by
      exact h.trans (List.ofFn_get xs).symm
    have hfun : (fun j : Fin xs.length => ω j.1) = xs.get := List.ofFn_injective h'
    exact congrArg (fun f : Fin xs.length → Fin k => f i) hfun

theorem preimage_cylinder_eq_preimage_matchingContextPrefixFinset
    (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    (symbolSequenceOfContextTrajectory (k := k) (m := m)) ⁻¹'
        (MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
      contextPrefixMap (k := k) (m := m) (xs.length - m + 1) ⁻¹'
        (matchingContextPrefixFinset (k := k) (m := m) xs : Set (Fin (xs.length - m + 1) → Context k m)) := by
  ext ω
  constructor
  · intro hω
    have hprefix :
        List.ofFn (fun i : Fin xs.length =>
          symbolSequenceOfContextTrajectory (k := k) (m := m) ω i.1) = xs :=
      (mem_cylinder_iff_prefix_eq (k := k) xs (symbolSequenceOfContextTrajectory (k := k) (m := m) ω)).mp hω
    have hctx :
        wordOfContextPrefix (k := k) (m := m)
          (contextPrefixMap (k := k) (m := m) (xs.length - m + 1) ω) = xs := by
      calc
        wordOfContextPrefix (k := k) (m := m)
            (contextPrefixMap (k := k) (m := m) (xs.length - m + 1) ω) =
              List.ofFn (fun i : Fin xs.length =>
                symbolSequenceOfContextTrajectory (k := k) (m := m) ω i.1) := by
                  simpa [Nat.add_sub_of_le hxs] using
                    wordOfContextPrefix_contextPrefixMap_eq_symbolPrefix
                      (k := k) (m := m) ω (xs.length - m)
        _ = xs := hprefix
    classical
    simp [matchingContextPrefixFinset, hctx]
  · intro hω
    have hctx :
        wordOfContextPrefix (k := k) (m := m)
          (contextPrefixMap (k := k) (m := m) (xs.length - m + 1) ω) = xs := by
      classical
      simpa [matchingContextPrefixFinset] using hω
    have hprefix :
        List.ofFn (fun i : Fin xs.length =>
          symbolSequenceOfContextTrajectory (k := k) (m := m) ω i.1) = xs := by
      calc
        List.ofFn (fun i : Fin xs.length =>
            symbolSequenceOfContextTrajectory (k := k) (m := m) ω i.1) =
              wordOfContextPrefix (k := k) (m := m)
                (contextPrefixMap (k := k) (m := m) (xs.length - m + 1) ω) := by
                  simpa [Nat.add_sub_of_le hxs] using
                    (wordOfContextPrefix_contextPrefixMap_eq_symbolPrefix
                      (k := k) (m := m) ω (xs.length - m)).symm
        _ = xs := hctx
    exact
      (mem_cylinder_iff_prefix_eq (k := k) xs
        (symbolSequenceOfContextTrajectory (k := k) (m := m) ω)).mpr hprefix

theorem measurableSet_cylinder (xs : List (Fin k)) :
    MeasurableSet (MarkovDeFinettiRecurrence.cylinder (k := k) xs) := by
  refine MeasurableSet.iInter ?_
  intro i
  change MeasurableSet ((fun ω : ℕ → Fin k => ω i.1) ⁻¹' ({xs[i.1]} : Set (Fin k)))
  exact (measurable_pi_apply i.1) (measurableSet_singleton xs[i.1])

def contextWordProbAux
    (θ : HigherOrderMarkovParam k m) (ctx : Context k m) (ctxs : List (Context k m)) :
    ℝ≥0 :=
  wordProbAux (k := Fintype.card (Context k m)) (toMarkovParam (k := k) (m := m) θ)
    ((Fintype.equivFin (Context k m)) ctx)
    (ctxs.map (Fintype.equivFin (Context k m)))

theorem toMarkovParam_stepProb_eq_zero_of_ne_shift
    (θ : HigherOrderMarkovParam k m) (ctx nextCtx : Context k m)
    (hnext : nextCtx ≠ shift (k := k) (m := m) ctx (lastSymbol (k := k) (m := m) nextCtx)) :
    stepProb (k := Fintype.card (Context k m))
      (toMarkovParam (k := k) (m := m) θ)
      ((Fintype.equivFin (Context k m)) ctx)
      ((Fintype.equivFin (Context k m)) nextCtx) = 0 := by
  simp only [MarkovDeFinettiHard.stepProb, toMarkovParam]
  have hmap :
      ((θ.next ((Fintype.equivFin (Context k m)).symm ((Fintype.equivFin (Context k m)) ctx))).map
          (measurable_shiftEncoded (k := k) (m := m)
            ((Fintype.equivFin (Context k m)) ctx)).aemeasurable)
        (Set.singleton ((Fintype.equivFin (Context k m)) nextCtx)) =
        (θ.next ((Fintype.equivFin (Context k m)).symm ((Fintype.equivFin (Context k m)) ctx)))
          ((fun a : Fin k =>
              (Fintype.equivFin (Context k m))
            (shift (k := k) (m := m)
                  ((Fintype.equivFin (Context k m)).symm
                    ((Fintype.equivFin (Context k m)) ctx)) a)) ⁻¹'
            ({(Fintype.equivFin (Context k m)) nextCtx} : Set (EncodedContext k m))) := by
    -- 4.31: `map_apply` yields the `{x}` set-builder form, which is defeq to the
    -- `Set.singleton x` written in `hmap`; `simpa` over-normalizes, so close by `exact`.
    exact
      (MeasureTheory.ProbabilityMeasure.map_apply
        (θ.next ((Fintype.equivFin (Context k m)).symm ((Fintype.equivFin (Context k m)) ctx)))
        (measurable_shiftEncoded (k := k) (m := m)
          ((Fintype.equivFin (Context k m)) ctx)).aemeasurable
        (MeasurableSet.singleton ((Fintype.equivFin (Context k m)) nextCtx)))
  have hpre :
      (fun a : Fin k =>
          (Fintype.equivFin (Context k m))
            (shift (k := k) (m := m) ((Fintype.equivFin (Context k m)).symm
              ((Fintype.equivFin (Context k m)) ctx)) a)) ⁻¹'
          ({(Fintype.equivFin (Context k m)) nextCtx} : Set (EncodedContext k m)) = ∅ := by
    ext a
    constructor
    · intro ha
      have henc :
          (Fintype.equivFin (Context k m))
            (shift (k := k) (m := m) ctx a) =
              (Fintype.equivFin (Context k m)) nextCtx := by
        simpa using ha
      have hshift : shift (k := k) (m := m) ctx a = nextCtx :=
        (Fintype.equivFin (Context k m)).injective henc
      have ha_last : a = lastSymbol (k := k) (m := m) nextCtx := by
        calc
          a = lastSymbol (k := k) (m := m)
                (shift (k := k) (m := m) ctx a) := by
                  symm
                  exact lastSymbol_shift (k := k) (m := m) ctx a
          _ = lastSymbol (k := k) (m := m) nextCtx := by simp [hshift]
      exact False.elim <| hnext <| by
        calc
          nextCtx = shift (k := k) (m := m) ctx a := hshift.symm
          _ = shift (k := k) (m := m) ctx (lastSymbol (k := k) (m := m) nextCtx) := by
              rw [ha_last]
    · intro ha
      simp at ha
  have hzero' :
      (θ.next ((Fintype.equivFin (Context k m)).symm ((Fintype.equivFin (Context k m)) ctx)))
        ((fun a : Fin k =>
            (Fintype.equivFin (Context k m))
              (shift (k := k) (m := m)
                ((Fintype.equivFin (Context k m)).symm
                  ((Fintype.equivFin (Context k m)) ctx)) a)) ⁻¹'
          ({(Fintype.equivFin (Context k m)) nextCtx} : Set (EncodedContext k m))) = 0 := by
    have hpre' :
        (fun a : Fin k =>
            (Fintype.equivFin (Context k m))
              (shift (k := k) (m := m) ctx a)) ⁻¹'
          ({(Fintype.equivFin (Context k m)) nextCtx} : Set (EncodedContext k m)) = ∅ := by
      simpa using hpre
    simp [hpre']
  exact hmap.trans hzero'

theorem contextWordProbAux_eq_zero_of_not_consistentTail
    (θ : HigherOrderMarkovParam k m) (ctx : Context k m) :
    ∀ ctxs : List (Context k m),
      ¬ consistentTail (k := k) (m := m) ctx ctxs →
      contextWordProbAux (k := k) (m := m) θ ctx ctxs = 0
  | [], hbad => False.elim (hbad trivial)
  | nextCtx :: rest, hbad => by
      by_cases hstep :
          nextCtx = shift (k := k) (m := m) ctx
            (lastSymbol (k := k) (m := m) nextCtx)
      · have htail :
            ¬ consistentTail (k := k) (m := m) nextCtx rest := by
          intro hrest
          exact hbad ⟨hstep, hrest⟩
        have hrest0 :
            wordProbAux (k := Fintype.card (Context k m))
              (toMarkovParam (k := k) (m := m) θ)
              ((Fintype.equivFin (Context k m)) nextCtx)
              (rest.map (Fintype.equivFin (Context k m))) = 0 := by
          simpa [contextWordProbAux] using
            contextWordProbAux_eq_zero_of_not_consistentTail
              (θ := θ) (ctx := nextCtx) rest htail
        unfold contextWordProbAux
        simp [wordProbAux, List.map, hrest0]
      · have hzero :
            stepProb (k := Fintype.card (Context k m))
              (toMarkovParam (k := k) (m := m) θ)
              ((Fintype.equivFin (Context k m)) ctx)
              ((Fintype.equivFin (Context k m)) nextCtx) = 0 :=
          toMarkovParam_stepProb_eq_zero_of_ne_shift
            (k := k) (m := m) θ ctx nextCtx hstep
        simp [contextWordProbAux, wordProbAux, hzero]

theorem contextWordProb_eq_zero_of_not_prefixShiftConsistent
    (θ : HigherOrderMarkovParam k m) :
    ∀ ctxs : List (Context k m),
      ¬ prefixShiftConsistent (k := k) (m := m) ctxs →
      contextWordProb (k := k) (m := m) θ ctxs = 0
  | [], hbad => False.elim (hbad trivial)
  | [ctx], hbad => False.elim (hbad trivial)
  | ctx :: nextCtx :: rest, hbad => by
      have htail :
          ¬ consistentTail (k := k) (m := m) ctx (nextCtx :: rest) := hbad
      have haux :
          contextWordProbAux (k := k) (m := m) θ ctx (nextCtx :: rest) = 0 :=
        contextWordProbAux_eq_zero_of_not_consistentTail
          (θ := θ) (ctx := ctx) (nextCtx :: rest) htail
      unfold contextWordProb MarkovDeFinettiHard.wordProb MarkovDeFinettiHard.wordProbNN
      change
        (((initProb (k := Fintype.card (Context k m))
              (toMarkovParam (k := k) (m := m) θ)
              ((Fintype.equivFin (Context k m)) ctx) *
            contextWordProbAux (k := k) (m := m) θ ctx (nextCtx :: rest) : ℝ≥0) : ℝ≥0∞) = 0)
      rw [ENNReal.coe_eq_zero, mul_eq_zero]
      right
      exact haux

theorem higherOrderSequenceMeasure_cylinder_eq_longWordProb
    (θ : HigherOrderMarkovParam k m) (xs : List (Fin k)) (hxs : m ≤ xs.length) :
    higherOrderSequenceMeasure (k := k) (m := m) θ
        (MarkovDeFinettiRecurrence.cylinder (k := k) xs) =
      longWordProb (k := k) (m := m) θ xs hxs := by
  classical
  let s := matchingContextPrefixFinset (k := k) (m := m) xs
  rw [higherOrderSequenceMeasure, Measure.map_apply
    (measurable_symbolSequenceOfContextTrajectory (k := k) (m := m))
    (measurableSet_cylinder (k := k) xs)]
  rw [preimage_cylinder_eq_preimage_matchingContextPrefixFinset (k := k) (m := m) xs hxs]
  rw [← sum_measure_preimage_singleton (μ := contextSequenceMeasure (k := k) (m := m) θ)
    (s := s) (f := contextPrefixMap (k := k) (m := m) (xs.length - m + 1))]
  · trans ∑ p ∈ s, contextWordProb (k := k) (m := m) θ (List.ofFn p)
    · apply Finset.sum_congr rfl
      intro p hp
      rw [contextPrefixMap_preimage_singleton_eq_contextCylinder_ofFn (k := k) (m := m) (p := p)]
      rw [contextSequenceMeasure_cylinder_eq_contextWordProb (k := k) (m := m) θ]
    · have hgoodMem :
          contextPathTupleOfWord (k := k) (m := m) xs hxs ∈ s :=
        contextPathTupleOfWord_mem_matchingContextPrefixFinset (k := k) (m := m) xs hxs
      rw [Finset.sum_eq_single_of_mem (contextPathTupleOfWord (k := k) (m := m) xs hxs) hgoodMem]
      · calc
          contextWordProb (k := k) (m := m) θ
              (List.ofFn (contextPathTupleOfWord (k := k) (m := m) xs hxs)) =
              contextSequenceMeasure (k := k) (m := m) θ
                (contextCylinder (k := k) (m := m)
                  (List.ofFn (contextPathTupleOfWord (k := k) (m := m) xs hxs))) := by
                symm
                rw [contextSequenceMeasure_cylinder_eq_contextWordProb (k := k) (m := m) θ]
          _ = contextSequenceMeasure (k := k) (m := m) θ
                (contextCylinder (k := k) (m := m)
                  (contextPathOfWord (k := k) (m := m) xs hxs)) := by
                rw [contextPathTupleOfWord_ofFn (k := k) (m := m) xs hxs]
          _ = longWordProb (k := k) (m := m) θ xs hxs := by
                exact contextSequenceMeasure_contextPath_eq_longWordProb
                  (k := k) (m := m) θ xs hxs
      · intro p hp hpne
        have hpword :
            wordOfContextPrefix (k := k) (m := m) p = xs :=
          (mem_matchingContextPrefixFinset_iff (k := k) (m := m) xs p).1 hp
        have hbad :
            ¬ prefixShiftConsistent (k := k) (m := m) (List.ofFn p) := by
          intro hcons
          exact hpne <|
            contextPrefix_eq_contextPathTupleOfWord_of_prefixShiftConsistent_of_word
              (k := k) (m := m) xs hxs hpword hcons
        rw [contextWordProb_eq_zero_of_not_prefixShiftConsistent
          (k := k) (m := m) θ (List.ofFn p) hbad]
  · intro p hp
    exact (measurable_contextPrefixMap (k := k) (m := m) (xs.length - m + 1))
      (measurableSet_singleton p)

section OrderTwoExamples

local instance : Fact (0 < 2) := ⟨by decide⟩

theorem orderTwo_cylinder_001_eq_longWordProb
    (θ : HigherOrderMarkovParam 2 2) :
    higherOrderSequenceMeasure (k := 2) (m := 2) θ
        (MarkovDeFinettiRecurrence.cylinder (k := 2)
          ([0, 0, 1] : List (Fin 2))) =
      longWordProb (k := 2) (m := 2) θ ([0, 0, 1] : List (Fin 2)) (by decide) := by
  simpa using
    higherOrderSequenceMeasure_cylinder_eq_longWordProb (k := 2) (m := 2) θ
      ([0, 0, 1] : List (Fin 2)) (by decide)

theorem orderTwo_cylinder_011_eq_longWordProb
    (θ : HigherOrderMarkovParam 2 2) :
    higherOrderSequenceMeasure (k := 2) (m := 2) θ
        (MarkovDeFinettiRecurrence.cylinder (k := 2)
          ([0, 1, 1] : List (Fin 2))) =
      longWordProb (k := 2) (m := 2) θ ([0, 1, 1] : List (Fin 2)) (by decide) := by
  simpa using
    higherOrderSequenceMeasure_cylinder_eq_longWordProb (k := 2) (m := 2) θ
      ([0, 1, 1] : List (Fin 2)) (by decide)

end OrderTwoExamples

end MarkovDeFinettiHigherOrder

end Mettapedia.Logic
