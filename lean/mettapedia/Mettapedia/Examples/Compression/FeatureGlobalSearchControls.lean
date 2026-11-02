import Mettapedia.Computability.KolmogorovComplexity.FeatureGlobalSearch

/-!
# Effective competing-search controls

A finite partial-recursive machine has both a real one-bit compression and a
divergent descriptive trial. The actual global scheduler eventually publishes
the compression and the actual greedy scheduler eventually commits. Finite
budgets, including those on an empty source with no feature, never certify
exhaustion of the unbounded program enumeration.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureGlobalSearchControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open KolmogorovComplexity.FeatureTheory.GlobalSearch
open scoped Classical

theorem finite_machine_effective : Partrec₂ finiteCompressionAlgorithm := by
  unfold Partrec₂
  have first : Computable fun input : BinString × BinString => decide (input = ([false], [])) :=
    (Primrec.eq.comp Primrec.id (Primrec.const ([false], []))).decide.to_comp
  have second : Computable fun input : BinString × BinString => decide (input = ([true], fourTrue)) :=
    (Primrec.eq.comp Primrec.id (Primrec.const ([true], fourTrue))).decide.to_comp
  refine (Partrec.cond first (Partrec.const' (Part.some fourTrue))
    (Partrec.cond second (Partrec.const' (Part.some [])) Partrec.none)).of_eq ?_
  rintro ⟨program, condition⟩
  by_cases one : program = [false] ∧ condition = [] <;>
    by_cases two : program = [true] ∧ condition = fourTrue <;>
      simp [finiteCompressionAlgorithm, one, two, Prod.mk.injEq]

theorem finite_chain : BChain finiteCompressionAlgorithm 2 fourTrue [[false]] [] := by
  exact .cons finiteCompressionStep.extracts finiteCompressionStep.reconstructs
    finiteCompressionStep.compresses (by norm_num [finiteCompressionStep, fourTrue]) (.nil [])

theorem coded_global_and_greedy_progress :
    ∃ code : Nat.Partrec.Code,
      Nat.Partrec.Code.eval code = encodedConditionalAlgorithm finiteCompressionAlgorithm ∧
      (∃ fuel, (⟨[], [[false]]⟩ : Frame) ∈ observedFrames code fuel (initial fourTrue)) ∧
      (∃ fuel, 0 < fuel ∧ (greedyRun code fuel (greedyInitial fourTrue)).current.features ≠ []) := by
  obtain ⟨code, codeSpec⟩ := exists_conditional_algorithm_code finite_machine_effective
  exact ⟨code, codeSpec, bChain_eventually_observed codeSpec finite_chain (by decide),
    greedy_eventually_commits codeSpec finite_chain (by decide)⟩

theorem divergent_trial_is_reachable (code : Nat.Partrec.Code) :
    Reaches code (.enumerate (.root fourTrue) 0) (.extract (.root fourTrue) [] [false] 0) :=
  enumerate_reaches_pair code (.root fourTrue) [] [false]

theorem divergent_trial_keeps_waiting {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm finiteCompressionAlgorithm)
    (stage : Nat) : successors code (.extract (.root fourTrue) [] [false] stage) =
      [.extract (.root fourTrue) [] [false] (stage + 1)] := by
  have missing : evaluate code [] fourTrue stage = none := by
    cases evaluated : evaluate code [] fourTrue stage with
    | none => rfl
    | some result =>
        have impossible := evaluate_sound codeSpec evaluated
        simp [finiteCompressionAlgorithm] at impossible
  simp [successors, Frame.root, missing]

theorem empty_source_has_no_compression (U : ConditionalAlgorithm) :
    ¬ Nonempty (CompressionStep U []) := by
  rintro ⟨step⟩
  have impossible := step.compresses
  simp at impossible

theorem featureless_source_does_not_certify_exhaustion (code : Nat.Partrec.Code) (fuel : Nat) :
    (Mettapedia.Algorithms.Compression.FairQueue.run priority (successors code) fuel (initial [])).2.pending ≠ [] :=
  global_search_never_exhausted code fuel []

theorem zero_budget_has_no_observation (code : Nat.Partrec.Code) (source : BinString) :
    observedFrames code 0 (initial source) = [] := rfl

theorem zero_budget_does_not_commit (code : Nat.Partrec.Code) (source : BinString) :
    (greedyRun code 0 (greedyInitial source)).current.features = [] := rfl

theorem greedy_featureless_source_does_not_certify_exhaustion (code : Nat.Partrec.Code) (fuel : Nat) :
    (greedyRun code fuel (greedyInitial [])).queue.pending ≠ [] :=
  greedy_search_never_exhausted code fuel []

#print axioms finite_machine_effective
#print axioms finite_chain
#print axioms coded_global_and_greedy_progress
#print axioms divergent_trial_is_reachable
#print axioms divergent_trial_keeps_waiting
#print axioms empty_source_has_no_compression
#print axioms featureless_source_does_not_certify_exhaustion
#print axioms zero_budget_has_no_observation
#print axioms zero_budget_does_not_commit
#print axioms greedy_featureless_source_does_not_certify_exhaustion

end Mettapedia.Examples.Compression.FeatureGlobalSearchControls
