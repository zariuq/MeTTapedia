import Mettapedia.Machines.LevinSearch
import Mettapedia.Computability.KolmogorovComplexity.Prefix
import Mettapedia.Computability.FiniteBitStrings
import Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting
import Mathlib.Logic.Function.Basic

/-!
# Prefix-coded dyadic portfolios with retained worker states

The codeword enumeration is the existing finite bitstring enumeration. Its
prefix-free admission supplies Kraft's bound, rather than assuming a budget
bound separately. The inclusive phase convention admits length at most the
phase. The strict convention printed in IC Algorithm 2 is treated separately.

Allocated slots count worker transitions, including reserved slots after a
worker halts. They do not measure Lean evaluation time or scheduling overhead.
The native learner's eight-turn cost/age policy remains a different scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PrefixPortfolio

open KolmogorovComplexity
open Mettapedia.UniversalAI.TimeBoundedAIXI
open scoped BigOperators

theorem bitstringsOfLength_nodup (length : Nat) : (bitstringsOfLength length).Nodup :=
  FiniteBitStrings.bitstringsOfLength_nodup length

theorem bitstringsUpTo_nodup (phase : Nat) : (bitstringsUpTo phase).Nodup :=
  FiniteBitStrings.bitstringsUpTo_nodup phase

def words (accepts : BinString → Bool) (phase : Nat) : List BinString :=
  (bitstringsUpTo phase).filter accepts

theorem mem_words (accepts : BinString → Bool) (phase : Nat) (word : BinString) :
    word ∈ words accepts phase ↔ accepts word = true ∧ word.length ≤ phase := by
  constructor
  · intro member
    obtain ⟨present, valid⟩ := List.mem_filter.mp member
    exact ⟨valid, length_le_of_mem_bitstringsUpTo present⟩
  · rintro ⟨valid, small⟩
    exact List.mem_filter.mpr ⟨mem_bitstringsUpTo_of_length_le small, valid⟩

theorem words_nodup (accepts : BinString → Bool) (phase : Nat) : (words accepts phase).Nodup :=
  (bitstringsUpTo_nodup phase).filter _

def phaseCost (accepts : BinString → Bool) (phase : Nat) : Nat :=
  ((words accepts phase).map fun word => 2 ^ (phase - word.length)).sum

/-- A finite prefix-free region pays for every slot by the shared Kraft
inequality. No ideal code-length or machine-completeness assumption is used. -/
theorem finite_prefix_budget (codes : Finset BinString) (phase : Nat)
    (free : PrefixFree (codes : Set BinString))
    (bounded : ∀ word ∈ codes, word.length ≤ phase) :
    (∑ word ∈ codes, 2 ^ (phase - word.length)) ≤ 2 ^ phase := by
  have scaled : (∑ word ∈ codes, (2 : ℝ) ^ (phase - word.length)) =
      (2 : ℝ) ^ phase * kraftSum codes := by
    unfold kraftSum Mettapedia.UniversalAI.SolomonoffPrior.kraftSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word present
    rw [zpow_neg, zpow_natCast]
    exact pow_sub₀ 2 (by norm_num) (bounded word present)
  have bound : (∑ word ∈ codes, (2 : ℝ) ^ (phase - word.length)) ≤ (2 : ℝ) ^ phase := by
    rw [scaled]
    exact (mul_le_mul_of_nonneg_left (kraft_inequality codes free) (by positivity)).trans_eq (mul_one _)
  exact_mod_cast bound

theorem phaseCost_le (accepts : BinString → Bool)
    (free : PrefixFree {word | accepts word = true}) (phase : Nat) :
    phaseCost accepts phase ≤ 2 ^ phase := by
  let codes := (words accepts phase).toFinset
  have bounded : ∀ word ∈ codes, word.length ≤ phase := by
    intro word present
    exact ((mem_words accepts phase word).mp (List.mem_toFinset.mp present)).2
  have prefixFree : PrefixFree (codes : Set BinString) := by
    intro first one second two different isPrefix
    exact free first ((mem_words accepts phase first).mp (List.mem_toFinset.mp one)).1
      second ((mem_words accepts phase second).mp (List.mem_toFinset.mp two)).1 different isPrefix
  have bound := finite_prefix_budget codes phase prefixFree bounded
  simpa only [codes, List.sum_toFinset _ (words_nodup accepts phase), phaseCost] using bound

abbrev Codeword (accepts : BinString → Bool) := {word : BinString // accepts word = true}

def members (accepts : BinString → Bool) (phase : Nat) : List (Codeword accepts) :=
  (words accepts phase).attach.map fun word => ⟨word.val, ((mem_words accepts phase word.val).mp word.property).1⟩

theorem mem_members (accepts : BinString → Bool) (phase : Nat) (word : Codeword accepts) :
    word ∈ members accepts phase ↔ word.val.length ≤ phase := by
  constructor
  · intro member
    obtain ⟨candidate, _present, same⟩ := List.mem_map.mp member
    have equal : candidate.val = word.val := congrArg Subtype.val same
    simpa only [← equal] using ((mem_words accepts phase candidate.val).mp candidate.property).2
  · intro small
    have present := (mem_words accepts phase word.val).mpr ⟨word.property, small⟩
    exact List.mem_map.mpr ⟨⟨word.val, present⟩, by simp, Subtype.ext rfl⟩

def family {α : Type*} (accepts : BinString → Bool)
    (free : PrefixFree {word | accepts word = true})
    (searcher : BinString → LevinSearch.Searcher α) : LevinSearch.Family (Codeword accepts) α where
  length word := word.val.length
  searcher word := searcher word.val
  upTo := members accepts
  upTo_exact := mem_members accepts
  kraft phase := by
    have bound := phaseCost_le accepts free phase
    simpa [members, phaseCost, List.map_map, Function.comp_def] using bound

variable {σ α : Type*}

def service (step : BinString → σ → Option σ) (quota : BinString → Nat)
    (state : BinString → σ) (word : BinString) : BinString → σ :=
  Function.update state word (StepCounting.runFor (step word) (quota word) (state word))

def serviceList (step : BinString → σ → Option σ) (quota : BinString → Nat)
    (selected : List BinString) (state : BinString → σ) : BinString → σ :=
  selected.foldl (service step quota) state

theorem serviceList_at (step : BinString → σ → Option σ) (quota : BinString → Nat)
    (selected : List BinString) (unique : selected.Nodup) (state : BinString → σ) (word : BinString) :
    serviceList step quota selected state word =
      if word ∈ selected then StepCounting.runFor (step word) (quota word) (state word) else state word := by
  induction selected generalizing state with
  | nil => simp [serviceList]
  | cons first rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      simp only [serviceList, List.foldl_cons]
      rw [show rest.foldl (service step quota) (service step quota state first) word =
        if word ∈ rest then StepCounting.runFor (step word) (quota word)
          (service step quota state first word) else service step quota state first word from
            ih tailUnique (service step quota state first)]
      by_cases same : word = first
      · subst word
        simp [absent, service]
      · simp [same, service]

def quota (accepts : BinString → Bool) (phase : Nat) (word : BinString) : Nat :=
  if accepts word = true ∧ word.length ≤ phase then 2 ^ (phase - word.length) else 0

def runPhase (accepts : BinString → Bool) (step : BinString → σ → Option σ)
    (phase : Nat) (state : BinString → σ) : BinString → σ :=
  serviceList step (fun word => 2 ^ (phase - word.length)) (words accepts phase) state

theorem runPhase_at (accepts : BinString → Bool) (step : BinString → σ → Option σ)
    (phase : Nat) (state : BinString → σ) (word : BinString) :
    runPhase accepts step phase state word = StepCounting.runFor (step word) (quota accepts phase word) (state word) := by
  rw [runPhase, serviceList_at step _ _ (words_nodup accepts phase)]
  by_cases eligible : accepts word = true ∧ word.length ≤ phase
  · simp [quota, eligible, (mem_words accepts phase word).mpr eligible]
  · have absent : word ∉ words accepts phase := fun member => eligible ((mem_words accepts phase word).mp member)
    simp [quota, eligible, absent]

def runFrom (accepts : BinString → Bool) (step : BinString → σ → Option σ) :
    Nat → Nat → (BinString → σ) → BinString → σ
  | _start, 0, state => state
  | start, count + 1, state => runFrom accepts step (start + 1) count (runPhase accepts step start state)

def workFrom (accepts : BinString → Bool) : Nat → Nat → BinString → Nat
  | _start, 0, _word => 0
  | start, count + 1, word => quota accepts start word + workFrom accepts (start + 1) count word

theorem runFrom_at (accepts : BinString → Bool) (step : BinString → σ → Option σ)
    (count start : Nat) (state : BinString → σ) (word : BinString) :
    runFrom accepts step start count state word =
      StepCounting.runFor (step word) (workFrom accepts start count word) (state word) := by
  induction count generalizing start state with
  | zero => rfl
  | succ count ih =>
      simp only [runFrom, workFrom, ih, runPhase_at]
      exact (StepCounting.runFor_add (step word) _ _ _).symm

theorem runFrom_add (accepts : BinString → Bool) (step : BinString → σ → Option σ)
    (first second start : Nat) (state : BinString → σ) :
    runFrom accepts step start (first + second) state =
      runFrom accepts step (start + first) second (runFrom accepts step start first state) := by
  induction first generalizing start state with
  | zero => simp [runFrom]
  | succ first ih =>
      simpa [Nat.succ_add, runFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (start + 1) (runPhase accepts step start state)

theorem last_quota_le_workFrom (accepts : BinString → Bool) (count start : Nat) (word : BinString) :
    quota accepts (start + count) word ≤ workFrom accepts start (count + 1) word := by
  induction count generalizing start with
  | zero => simp [workFrom]
  | succ count ih =>
      have later := ih (start + 1)
      have bounded := later.trans (Nat.le_add_left (workFrom accepts (start + 1) (count + 1) word)
        (quota accepts start word))
      simpa [workFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bounded

/-- Readout is published only from a stopped worker. Persistence is proved
from retained machine configurations, not assumed for an arbitrary probe. -/
structure Worker (σ α : Type*) where
  initial : BinString → σ
  step : BinString → σ → Option σ
  read : BinString → σ → Option α
  stopped : ∀ word state answer, read word state = some answer → step word state = none

def Worker.searcher (worker : Worker σ α) (word : BinString) : LevinSearch.Searcher α where
  result work := worker.read word (StepCounting.runFor (worker.step word) work (worker.initial word))
  persistent work answer found := by
    have halted := worker.stopped word _ answer found
    change worker.read word (StepCounting.runFor (worker.step word) (work + 1) (worker.initial word)) = some answer
    rw [StepCounting.runFor_add, StepCounting.runFor_of_step_eq_none _ halted]
    exact found

def Worker.filterMap {β : Type*} (worker : Worker σ α) (project : α → Option β) : Worker σ β where
  initial := worker.initial
  step := worker.step
  read word state := (worker.read word state).bind project
  stopped word state answer found := by
    obtain ⟨before, computed, _published⟩ := Option.bind_eq_some_iff.mp found
    exact worker.stopped word state before computed

theorem Worker.filterMap_result {β : Type*} (worker : Worker σ α) (project : α → Option β)
    (word : BinString) (work : Nat) :
    ((worker.filterMap project).searcher word).result work =
      ((worker.searcher word).result work).bind project := rfl

def observations (worker : Worker σ α) (accepts : BinString → Bool)
    (phase : Nat) (state : BinString → σ) : List (BinString × α) :=
  (words accepts phase).filterMap fun word => (worker.read word (state word)).map fun answer => (word, answer)

/-- A real worker answer is reached by the retained portfolio with the
Levin allocation bound, charging the complete prefix codeword length. -/
theorem retained_finds (worker : Worker σ α) (accepts : BinString → Bool)
    (free : PrefixFree {word | accepts word = true}) (word : BinString) (valid : accepts word = true)
    (work : Nat) (answer : α) (found : (worker.searcher word).result work = some answer) :
    let phase := word.length + Nat.clog 2 work
    let rounds := phase + 1
    (word, answer) ∈ observations worker accepts phase (runFrom accepts worker.step 0 rounds worker.initial) ∧
      (family accepts free worker.searcher).cost rounds ≤ 4 * 2 ^ word.length * max work 1 := by
  dsimp only
  let phase := word.length + Nat.clog 2 work
  have eligible : word.length ≤ phase := by dsimp [phase]; omega
  have quotaEnough : work ≤ quota accepts phase word := by
    rw [quota, if_pos ⟨valid, eligible⟩]
    simpa [phase] using Nat.le_pow_clog (by norm_num : 1 < (2 : Nat)) work
  have workEnough := quotaEnough.trans (by simpa using last_quota_le_workFrom accepts phase 0 word)
  have computed := (worker.searcher word).persists workEnough found
  constructor
  · apply List.mem_filterMap.mpr
    refine ⟨word, (mem_words accepts phase word).mpr ⟨valid, eligible⟩, ?_⟩
    rw [runFrom_at]
    change (worker.read word (StepCounting.runFor (worker.step word)
      (workFrom accepts 0 (phase + 1) word) (worker.initial word))).map _ = _
    rw [show worker.read word (StepCounting.runFor (worker.step word)
      (workFrom accepts 0 (phase + 1) word) (worker.initial word)) = some answer from computed]
    rfl
  · exact ((family accepts free worker.searcher).search_finds (member := ⟨word, valid⟩) found).2

def strictWords (accepts : BinString → Bool) : Nat → List BinString
  | 0 => []
  | phase + 1 => words accepts phase

theorem mem_strictWords (accepts : BinString → Bool) (phase : Nat) (word : BinString) :
    word ∈ strictWords accepts phase ↔ accepts word = true ∧ word.length < phase := by
  cases phase with
  | zero => simp [strictWords]
  | succ phase => simpa [strictWords, Nat.lt_succ_iff] using mem_words accepts phase word

def strictPhaseCost (accepts : BinString → Bool) (phase : Nat) : Nat :=
  ((strictWords accepts phase).map fun word => 2 ^ (phase - word.length)).sum

/-- The strict printed convention shifts eligibility by one phase and
doubles each corresponding inclusive allocation. Both conventions are
explicit; their work bounds differ by only the charged constant factor. -/
theorem strictPhaseCost_succ (accepts : BinString → Bool) (phase : Nat) :
    strictPhaseCost accepts (phase + 1) = 2 * phaseCost accepts phase := by
  unfold strictPhaseCost strictWords phaseCost
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro word present
  have small := ((mem_words accepts phase word).mp present).2
  have exponent : phase + 1 - word.length = phase - word.length + 1 := by omega
  simp [exponent, pow_succ, Nat.mul_comm]

theorem strictPhaseCost_le (accepts : BinString → Bool)
    (free : PrefixFree {word | accepts word = true}) (phase : Nat) :
    strictPhaseCost accepts phase ≤ 2 ^ phase := by
  cases phase with
  | zero => simp [strictPhaseCost, strictWords]
  | succ phase =>
      rw [strictPhaseCost_succ]
      have bounded := Nat.mul_le_mul_left 2 (phaseCost_le accepts free phase)
      simpa [pow_succ, Nat.mul_comm] using bounded

#print axioms bitstringsOfLength_nodup
#print axioms bitstringsUpTo_nodup
#print axioms mem_words
#print axioms words_nodup
#print axioms finite_prefix_budget
#print axioms phaseCost_le
#print axioms mem_members
#print axioms serviceList_at
#print axioms runPhase_at
#print axioms runFrom_at
#print axioms runFrom_add
#print axioms last_quota_le_workFrom
#print axioms Worker.filterMap_result
#print axioms retained_finds
#print axioms mem_strictWords
#print axioms strictPhaseCost_succ
#print axioms strictPhaseCost_le

end Mettapedia.Machines.PrefixPortfolio
