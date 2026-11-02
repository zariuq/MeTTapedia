import Mettapedia.Machines.ICSourceClock

/-!
# Retained IC workers in the normalized source clock

The declared region is the existing canonical pair-code language. The lower
prepared-worker interface starts after admission; the entry-worker interface
physically parses the unchanged candidate record before preparing and checking
its original-word task. Every emitted candidate reconstructs and strictly
compresses. Inclusive dyadic allocation uses actual worker transitions. The
entry worker does not call the host parser when constructing its input.
Eligibility enumeration, initial materialization, observation decoding and
variable-cost scheduler administration remain outside this slot clock.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.PreparedICSearch

open Turing StateTransition KolmogorovComplexity
open Mettapedia.Computability
open FeatureTheory.DyadicSearch

def taskInput (original word : BinString) : List (Option Bool) :=
  match parsePair word with
  | some (descriptive, feature) => ICPreparedCheck.input descriptive feature original
  | none => []

theorem taskInput_parsed (original : BinString) {word descriptive feature : BinString}
    (parsed : parsePair word = some (descriptive, feature)) :
    taskInput original word = ICPreparedCheck.input descriptive feature original := by simp [taskInput, parsed]

def project (output : List (Option Bool)) : Option Candidate := (ICPhysicalCheck.readResponse output).join

variable {algorithm : ConditionalAlgorithm}

def worker (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) (original : BinString) :
    PrefixPortfolio.Worker (ICPreparedCheck.machine source).Cfg Candidate :=
  (FiniteStackWorker.worker (ICPreparedCheck.machine source) (taskInput original)).filterMap project

theorem worker_sound (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (original word : BinString) (work : Nat) (candidate : Candidate) (valid : pairCodeTest word = true)
    (found : ((worker source original).searcher word).result work = some candidate) :
    some candidate ∈ autoencoder algorithm word original := by
  change (parsePair word).isSome = true at valid
  obtain ⟨⟨descriptive, feature⟩, parsed⟩ := Option.isSome_iff_exists.mp valid
  rw [worker, PrefixPortfolio.Worker.filterMap_result] at found
  obtain ⟨returned, read, published⟩ := Option.bind_eq_some_iff.mp found
  change (ICPhysicalCheck.readResponse returned).bind id = some candidate at published
  obtain ⟨outcome, decoded, outcomeSame⟩ := Option.bind_eq_some_iff.mp published
  change outcome = some candidate at outcomeSame
  subst outcome
  have clean : ∀ state : (ICPreparedCheck.machine source).Cfg,
      Reaches (ICPreparedCheck.machine source).step
        (initList (ICPreparedCheck.machine source) (taskInput original word)) state → state.l = none →
      ∃ output, state = haltList (ICPreparedCheck.machine source) output := by
    rw [taskInput_parsed original parsed]
    exact ICPreparedCheck.clean_halts_at source descriptive feature original
  obtain ⟨counted⟩ := FiniteStackWorker.sound_at (ICPreparedCheck.machine source) (taskInput original) word
    clean returned work read
  have actual : TM2OutputsInTime (ICPreparedCheck.machine source)
      (ICPreparedCheck.input descriptive feature original) (some returned) work :=
    Eq.mp (congrArg (fun input : List (Option Bool) => TM2OutputsInTime (ICPreparedCheck.machine source)
      input (some returned) work) (taskInput_parsed original parsed)) counted
  obtain ⟨computed, reconstructed, meaning⟩ := ICPreparedCheck.sound source actual
  have same : computed = some candidate := Option.some.inj (reconstructed.symm.trans decoded)
  subst computed
  simpa [autoencoder, parsed] using meaning

theorem complete_from_source_clocks
    (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {original : BinString} (step : CompressionStep algorithm original) (firstTime secondTime : Nat)
    (extract : TM2OutputsInTime (ICSourceClock.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec step.descriptiveProgram original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec step.residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ICSourceClock.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec step.featureProgram step.residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec original)) secondTime) :
    ((worker source original).searcher (pairCode step.descriptiveProgram step.featureProgram)).result
      (ICSourceClock.factor source * (firstTime + secondTime + 1)) = some (step.residual, step.featureProgram) := by
  have run := ICSourceClock.prepared_outputs source extract reconstruct
  have originalRun : TM2OutputsInTime (ICPreparedCheck.machine source)
      (taskInput original (pairCode step.descriptiveProgram step.featureProgram))
      (some (FramedCompressionCheck.response true step.residual step.featureProgram))
      (ICSourceClock.factor source * (firstTime + secondTime + 1)) := by
    simpa [taskInput, parsePair_pairCode, ICPhysicalCheck.result, FramedCompressionCheck.verdict, step.compresses] using run
  have observed := FiniteStackWorker.complete (ICPreparedCheck.machine source) (taskInput original)
    (pairCode step.descriptiveProgram step.featureProgram) _ _ originalRun
  rw [worker, PrefixPortfolio.Worker.filterMap_result, observed]
  simp [project, ICPhysicalCheck.read_response]

/-- Every finite retained observation is sound, not just the branch used by
the allocation witness. Invalid pair codes are outside the declared region. -/
theorem emitted_reconstructs (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (original : BinString) (count phase : Nat) {word residual feature : BinString}
    (emitted : (word, (residual, feature)) ∈ PrefixPortfolio.observations (worker source original)
      pairCodeTest phase (PrefixPortfolio.runFrom pairCodeTest (worker source original).step 0 count
        (worker source original).initial)) :
    ∃ descriptive, parsePair word = some (descriptive, feature) ∧
      residual ∈ algorithm descriptive original ∧ original ∈ algorithm feature residual ∧
      feature.length + residual.length < original.length := by
  obtain ⟨actualWord, eligible, published⟩ := List.mem_filterMap.mp emitted
  obtain ⟨candidate, read, same⟩ := Option.map_eq_some_iff.mp published
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  have valid := ((PrefixPortfolio.mem_words pairCodeTest phase _).mp eligible).1
  rw [PrefixPortfolio.runFrom_at] at read
  exact autoencoder_sound (worker_sound source original _ _ _ valid read)

/-- The actual prepared workers reach each successful candidate under the
inclusive retained policy. The bound charges the complete canonical codeword,
and is a worker-slot bound, not uncharged scheduler wall-clock time. -/
theorem retained_from_source_clocks
    (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {original : BinString} (step : CompressionStep algorithm original) (firstTime secondTime : Nat)
    (extract : TM2OutputsInTime (ICSourceClock.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec step.descriptiveProgram original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec step.residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ICSourceClock.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec step.featureProgram step.residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec original)) secondTime) :
    let time := ICSourceClock.factor source * (firstTime + secondTime + 1)
    let word := pairCode step.descriptiveProgram step.featureProgram
    let phase := word.length + Nat.clog 2 time
    (word, (step.residual, step.featureProgram)) ∈ PrefixPortfolio.observations (worker source original)
      pairCodeTest phase (PrefixPortfolio.runFrom pairCodeTest (worker source original).step 0 (phase + 1)
        (worker source original).initial) ∧
      (PrefixPortfolio.family pairCodeTest pairCodeTest_prefixFree (worker source original).searcher).cost (phase + 1) ≤
        4 * 2 ^ word.length * ICSourceClock.factor source * (firstTime + secondTime + 1) := by
  dsimp only
  have found := complete_from_source_clocks source step firstTime secondTime extract reconstruct
  have allocated := PrefixPortfolio.retained_finds (worker source original) pairCodeTest pairCodeTest_prefixFree
    (pairCode step.descriptiveProgram step.featureProgram) (pairCodeTest_pairCode _ _)
    (ICSourceClock.factor source * (firstTime + secondTime + 1)) _ found
  have positiveFactor : 1 ≤ ICSourceClock.factor source := by simp only [ICSourceClock.factor]; omega
  have positiveTime : 1 ≤ ICSourceClock.factor source * (firstTime + secondTime + 1) := by nlinarith
  simpa only [max_eq_left positiveTime, Nat.mul_assoc] using allocated

/-- A single normalized universal source is fixed before every source word
and valid compression step. This is an allocation theorem after admission;
it does not assign unit cost to parsing or scheduler administration. -/
theorem fixed_universal_one_step :
    ∃ source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec universalConditionalAlgorithm,
      ∀ original (step : CompressionStep universalConditionalAlgorithm original),
        ∃ firstTime secondTime,
          let time := ICSourceClock.factor source * (firstTime + secondTime + 1)
          let word := pairCode step.descriptiveProgram step.featureProgram
          let phase := word.length + Nat.clog 2 time
          (word, (step.residual, step.featureProgram)) ∈ PrefixPortfolio.observations (worker source original)
            pairCodeTest phase (PrefixPortfolio.runFrom pairCodeTest (worker source original).step 0 (phase + 1)
              (worker source original).initial) ∧
            (PrefixPortfolio.family pairCodeTest pairCodeTest_prefixFree (worker source original).searcher).cost (phase + 1) ≤
              4 * 2 ^ word.length * ICSourceClock.factor source * (firstTime + secondTime + 1) := by
  obtain ⟨source⟩ := ConditionalSourceMachine.universal_has_fixed_source NaturalWordEncoding.codec
  refine ⟨source, fun original step => ?_⟩
  obtain ⟨firstTime, ⟨extract⟩⟩ := ICSourceClock.complete source step.extracts
  obtain ⟨secondTime, ⟨reconstruct⟩⟩ := ICSourceClock.complete source step.reconstructs
  exact ⟨firstTime, secondTime, retained_from_source_clocks source step firstTime secondTime extract reconstruct⟩

def entryWorker (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) (original : BinString) :
    PrefixPortfolio.Worker (ICEntryCheck.machine source).Cfg Candidate :=
  (FiniteStackWorker.worker (ICEntryCheck.machine source) (fun word => ICEntryCheck.input word original)).filterMap project

theorem entry_worker_sound (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (original word : BinString) (work : Nat) (candidate : Candidate)
    (found : ((entryWorker source original).searcher word).result work = some candidate) :
    some candidate ∈ autoencoder algorithm word original := by
  rw [entryWorker, PrefixPortfolio.Worker.filterMap_result] at found
  obtain ⟨returned, read, published⟩ := Option.bind_eq_some_iff.mp found
  change (ICPhysicalCheck.readResponse returned).bind id = some candidate at published
  obtain ⟨outcome, decoded, outcomeSame⟩ := Option.bind_eq_some_iff.mp published
  change outcome = some candidate at outcomeSame
  subst outcome
  obtain ⟨counted⟩ := FiniteStackWorker.sound_at (ICEntryCheck.machine source) (fun word => ICEntryCheck.input word original) word
    (ICEntryCheck.clean_halts_at source word original) returned work read
  obtain ⟨computed, reconstructed, meaning⟩ := ICEntryCheck.sound source counted
  have same : computed = some candidate := Option.some.inj (reconstructed.symm.trans decoded)
  simpa only [same] using meaning

theorem entry_complete_from_source_clocks
    (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {original : BinString} (step : CompressionStep algorithm original) (firstTime secondTime : Nat)
    (extract : TM2OutputsInTime (ICSourceClock.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec step.descriptiveProgram original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec step.residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ICSourceClock.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec step.featureProgram step.residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec original)) secondTime) :
    ((entryWorker source original).searcher (pairCode step.descriptiveProgram step.featureProgram)).result
      (ICSourceClock.entryFactor source * (firstTime + secondTime + 1)) = some (step.residual, step.featureProgram) := by
  have run := ICSourceClock.entry_outputs source extract reconstruct
  have originalRun : TM2OutputsInTime (ICEntryCheck.machine source)
      (ICEntryCheck.input (pairCode step.descriptiveProgram step.featureProgram) original)
      (some (FramedCompressionCheck.response true step.residual step.featureProgram))
      (ICSourceClock.entryFactor source * (firstTime + secondTime + 1)) := by
    simpa [ICPhysicalCheck.result, FramedCompressionCheck.verdict, step.compresses] using run
  have observed := FiniteStackWorker.complete (ICEntryCheck.machine source) (fun word => ICEntryCheck.input word original)
    (pairCode step.descriptiveProgram step.featureProgram) _ _ originalRun
  rw [entryWorker, PrefixPortfolio.Worker.filterMap_result, observed]
  simp [project, ICPhysicalCheck.read_response]

theorem entry_emitted_reconstructs (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (original : BinString) (count phase : Nat) {word residual feature : BinString}
    (emitted : (word, (residual, feature)) ∈ PrefixPortfolio.observations (entryWorker source original)
      pairCodeTest phase (PrefixPortfolio.runFrom pairCodeTest (entryWorker source original).step 0 count
        (entryWorker source original).initial)) :
    ∃ descriptive, parsePair word = some (descriptive, feature) ∧
      residual ∈ algorithm descriptive original ∧ original ∈ algorithm feature residual ∧
      feature.length + residual.length < original.length := by
  obtain ⟨actualWord, _eligible, published⟩ := List.mem_filterMap.mp emitted
  obtain ⟨candidate, read, same⟩ := Option.map_eq_some_iff.mp published
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  rw [PrefixPortfolio.runFrom_at] at read
  exact autoencoder_sound (entry_worker_sound source original _ _ _ read)

/-- Physical candidate admission is now within the worker allocation bound.
Eligibility enumeration, initialization and observation/admin costs are still
not assigned free unit cost by this statement. -/
theorem entry_retained_from_source_clocks
    (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {original : BinString} (step : CompressionStep algorithm original) (firstTime secondTime : Nat)
    (extract : TM2OutputsInTime (ICSourceClock.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec step.descriptiveProgram original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec step.residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ICSourceClock.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec step.featureProgram step.residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec original)) secondTime) :
    let time := ICSourceClock.entryFactor source * (firstTime + secondTime + 1)
    let word := pairCode step.descriptiveProgram step.featureProgram
    let phase := word.length + Nat.clog 2 time
    (word, (step.residual, step.featureProgram)) ∈ PrefixPortfolio.observations (entryWorker source original)
      pairCodeTest phase (PrefixPortfolio.runFrom pairCodeTest (entryWorker source original).step 0 (phase + 1)
        (entryWorker source original).initial) ∧
      (PrefixPortfolio.family pairCodeTest pairCodeTest_prefixFree (entryWorker source original).searcher).cost (phase + 1) ≤
        4 * 2 ^ word.length * ICSourceClock.entryFactor source * (firstTime + secondTime + 1) := by
  dsimp only
  have found := entry_complete_from_source_clocks source step firstTime secondTime extract reconstruct
  have allocated := PrefixPortfolio.retained_finds (entryWorker source original) pairCodeTest pairCodeTest_prefixFree
    (pairCode step.descriptiveProgram step.featureProgram) (pairCodeTest_pairCode _ _)
    (ICSourceClock.entryFactor source * (firstTime + secondTime + 1)) _ found
  have positiveFactor : 1 ≤ ICSourceClock.entryFactor source := by
    simp only [ICSourceClock.entryFactor, ICSourceClock.factor]
    omega
  have positiveTime : 1 ≤ ICSourceClock.entryFactor source * (firstTime + secondTime + 1) := by nlinarith
  simpa only [max_eq_left positiveTime, Nat.mul_assoc] using allocated

theorem fixed_universal_entry_one_step :
    ∃ source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec universalConditionalAlgorithm,
      ∀ original (step : CompressionStep universalConditionalAlgorithm original),
        ∃ firstTime secondTime,
          let time := ICSourceClock.entryFactor source * (firstTime + secondTime + 1)
          let word := pairCode step.descriptiveProgram step.featureProgram
          let phase := word.length + Nat.clog 2 time
          (word, (step.residual, step.featureProgram)) ∈ PrefixPortfolio.observations (entryWorker source original)
            pairCodeTest phase (PrefixPortfolio.runFrom pairCodeTest (entryWorker source original).step 0 (phase + 1)
              (entryWorker source original).initial) ∧
            (PrefixPortfolio.family pairCodeTest pairCodeTest_prefixFree (entryWorker source original).searcher).cost (phase + 1) ≤
              4 * 2 ^ word.length * ICSourceClock.entryFactor source * (firstTime + secondTime + 1) := by
  obtain ⟨source⟩ := ConditionalSourceMachine.universal_has_fixed_source NaturalWordEncoding.codec
  refine ⟨source, fun original step => ?_⟩
  obtain ⟨firstTime, ⟨extract⟩⟩ := ICSourceClock.complete source step.extracts
  obtain ⟨secondTime, ⟨reconstruct⟩⟩ := ICSourceClock.complete source step.reconstructs
  exact ⟨firstTime, secondTime, entry_retained_from_source_clocks source step firstTime secondTime extract reconstruct⟩

end Mettapedia.Machines.PreparedICSearch
