import Mettapedia.Computability.KolmogorovComplexity.FeatureDyadicSearch
import Mettapedia.Computability.KolmogorovComplexity.FeatureGlobalSearch
import Mettapedia.Machines.HierarchicalPrefixCost

/-!
# Hierarchical incremental search with retained compiled workers

The recursive hierarchy runs the same compiled checked autoencoder used by
the one-step dyadic search. Successful workers become live child searches;
siblings are retained. A source-length depth bound loses no strict finite
compression chain. Every observed path reconstructs the original source.

The charged nested bound expands into a sum with cumulative complete
codeword lengths. Its local work is actual four-stack checked-worker time,
not a claimed linear bound in the original interpreter's two evaluations.
The variable-cost administration and interpreter-cost join remain separate.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory.HierarchicalSearch

open Mettapedia.Machines
open DyadicSearch

abbrev Frame := GlobalSearch.Frame
abbrev Entry := HierarchicalPrefixSearch.TimedEntry Candidate

def workers (code : Turing.ToPartrec.Code) (frame : Frame) := checkedWorker code frame.residual

def nextFrame (frame : Frame) (candidate : Candidate) : Frame := frame.extend candidate.2 candidate.1

def followFrame : Frame → List (BinString × Candidate) → Frame
  | frame, [] => frame
  | frame, (_word, candidate) :: rest => followFrame (nextFrame frame candidate) rest

def search (code : Turing.ToPartrec.Code) (source : BinString) (budget : Nat) :=
  ResumablePrefixClock.run
    (HierarchicalPrefixSearch.tick (workers code) pairCodeTest nextFrame source.length) budget
    (HierarchicalPrefixSearch.initial (workers code) source.length (.root source))

theorem pathRuns_valid {U : ConditionalAlgorithm} {code : Turing.ToPartrec.Code}
    (codeSpec : ∀ word source, code.eval [Encodable.encode (word, source)] =
      (autoencoder U word source).map fun candidate => [Encodable.encode candidate])
    {frame : Frame} {path : List (BinString × Candidate)} {source : BinString}
    (runs : HierarchicalPrefixSearch.PathRuns (workers code) nextFrame frame path)
    (valid : frame.Valid U source) : (followFrame frame path).Valid U source := by
  induction runs with
  | nil frame => exact valid
  | @cons frame word candidate rest found later ih =>
      obtain ⟨residual, feature⟩ := candidate
      obtain ⟨work, read⟩ := found
      have computes := checkedWorker_sound codeSpec frame.residual word work (residual, feature) read
      obtain ⟨_descriptive, _parsed, _extracted, rebuilt, smaller⟩ := autoencoder_sound computes
      exact ih (GlobalSearch.extend_valid valid rebuilt smaller)

theorem every_observed_path_valid {U : ConditionalAlgorithm} {code : Turing.ToPartrec.Code}
    (codeSpec : ∀ word source, code.eval [Encodable.encode (word, source)] =
      (autoencoder U word source).map fun candidate => [Encodable.encode candidate])
    (source : BinString) (budget : Nat) (path : List (BinString × Candidate))
    (seen : HierarchicalPrefixSearch.Follows source.length path (search code source budget)) :
    (followFrame (.root source) path).Valid U source :=
  pathRuns_valid codeSpec
    (HierarchicalPrefixSearch.every_observed_path_runs (workers code) pairCodeTest nextFrame
      source.length budget (.root source) path seen)
    (GlobalSearch.root_valid U source)

theorem every_observed_description_reconstructs {U : ConditionalAlgorithm} {code : Turing.ToPartrec.Code}
    (codeSpec : ∀ word source, code.eval [Encodable.encode (word, source)] =
      (autoencoder U word source).map fun candidate => [Encodable.encode candidate])
    (source : BinString) (budget : Nat) (path : List (BinString × Candidate))
    (seen : HierarchicalPrefixSearch.Follows source.length path (search code source budget)) :
    source ∈ schemeInterpreter U (followFrame (.root source) path).description [] :=
  GlobalSearch.valid_description (every_observed_path_valid codeSpec source budget path seen)

theorem bChain_has_timed_path {U : ConditionalAlgorithm} {code : Turing.ToPartrec.Code}
    (codeSpec : ∀ word source, code.eval [Encodable.encode (word, source)] =
      (autoencoder U word source).map fun candidate => [Encodable.encode candidate])
    {factor : ℝ} {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (accumulated : List BinString) :
    ∃ entries : List Entry,
      HierarchicalPrefixSearch.TimedPath (workers code) nextFrame ⟨source, accumulated⟩ entries ∧
      (∀ entry ∈ entries, pairCodeTest entry.1.1 = true) ∧
      entries.length = features.length ∧
      followFrame ⟨source, accumulated⟩ (entries.map Prod.fst) = ⟨final, accumulated ++ features⟩ := by
  induction chain generalizing accumulated with
  | nil source =>
      exact ⟨[], .nil _, by simp, rfl, by simp [followFrame]⟩
  | @cons source residual final feature descriptive features extracts reconstructs smaller _ratio later ih =>
      let step : CompressionStep U source := ⟨feature, descriptive, residual, extracts, reconstructs, smaller⟩
      obtain ⟨work, read⟩ := checkedWorker_complete codeSpec step
      obtain ⟨entries, timed, admitted, count, finished⟩ := ih (accumulated ++ [feature])
      refine ⟨((pairCode descriptive feature, (residual, feature)), work) :: entries,
        .cons read timed, ?_, ?_, ?_⟩
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact pairCodeTest_pairCode _ _
        · exact admitted entry member
      · simpa only [List.length_cons] using congrArg (· + 1) count
      · simpa [followFrame, nextFrame, GlobalSearch.Frame.extend, List.append_assoc] using finished

theorem bChain_observed_by_bound {U : ConditionalAlgorithm} {code : Turing.ToPartrec.Code}
    (codeSpec : ∀ word source, code.eval [Encodable.encode (word, source)] =
      (autoencoder U word source).map fun candidate => [Encodable.encode candidate])
    {factor : ℝ} {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) :
    ∃ entries : List Entry,
      HierarchicalPrefixSearch.TimedPath (workers code) nextFrame (.root source) entries ∧
      entries.length = features.length ∧
      HierarchicalPrefixSearch.Follows source.length (entries.map Prod.fst)
        (search code source (HierarchicalPrefixSearch.nestedBound entries)) ∧
      followFrame (.root source) (entries.map Prod.fst) = ⟨final, features⟩ ∧
      HierarchicalPrefixSearch.nestedBound entries = (HierarchicalPrefixSearch.weightedTerms 0 entries).sum := by
  obtain ⟨entries, timed, admitted, count, finished⟩ := bChain_has_timed_path codeSpec chain []
  have bounded : entries.length ≤ source.length := by
    rw [count]
    have bound := chain.length_bound
    omega
  exact ⟨entries, timed, count,
    HierarchicalPrefixSearch.path_by_bound (workers code) pairCodeTest pairCodeTest_prefixFree
      nextFrame timed admitted source.length bounded,
    by simpa only [GlobalSearch.Frame.root, List.nil_append] using finished,
    HierarchicalPrefixSearch.nestedBound_eq_weighted_sum entries⟩

/-- One compiled checked machine is fixed before all sources, factors and
finite compression chains. The operational search retains every competitor;
the bound is a cumulative-codeword weighted sum in hierarchical turns. -/
theorem exists_bounded_hierarchical_search {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    ∃ code : Turing.ToPartrec.Code,
      (∀ word source, code.eval [Encodable.encode (word, source)] =
        (autoencoder U word source).map fun candidate => [Encodable.encode candidate]) ∧
      ∀ factor source final features, BChain U factor source features final →
        ∃ entries : List Entry,
          entries.length = features.length ∧
          HierarchicalPrefixSearch.Follows source.length (entries.map Prod.fst)
            (search code source (HierarchicalPrefixSearch.nestedBound entries)) ∧
          followFrame (.root source) (entries.map Prod.fst) = ⟨final, features⟩ ∧
          HierarchicalPrefixSearch.nestedBound entries = (HierarchicalPrefixSearch.weightedTerms 0 entries).sum := by
  obtain ⟨code, codeSpec⟩ := exists_compiled_autoencoder effective
  refine ⟨code, codeSpec, fun _factor _source _final _features chain => ?_⟩
  obtain ⟨entries, _timed, count, seen, finished, bound⟩ := bChain_observed_by_bound codeSpec chain
  exact ⟨entries, count, seen, finished, bound⟩

theorem bounded_search_debits (code : Turing.ToPartrec.Code) (source : BinString) (budget : Nat) :
    let debit := HierarchicalPrefixSearch.runDebit (workers code) pairCodeTest nextFrame source.length budget
      (HierarchicalPrefixSearch.initial (workers code) source.length (.root source))
    debit.localTransitions ≤ budget ∧ debit.administrativeSelectors ≤ source.length * budget :=
  HierarchicalPrefixSearch.runDebit_bounds (workers code) pairCodeTest nextFrame source.length budget _

theorem search_resumes (code : Turing.ToPartrec.Code) (source : BinString) (first second : Nat) :
    search code source (first + second) =
      ResumablePrefixClock.run
        (HierarchicalPrefixSearch.tick (workers code) pairCodeTest nextFrame source.length) second
        (search code source first) :=
  ResumablePrefixClock.run_add _ first second _

end KolmogorovComplexity.FeatureTheory.HierarchicalSearch
