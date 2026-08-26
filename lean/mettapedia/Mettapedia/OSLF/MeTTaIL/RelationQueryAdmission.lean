import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# Constructive admission for external relation-query rows

`Engine.premiseStepWithEnv_relationQuery_mem` eliminates a successful query
result into a binding merge.  Compiler and hosting proofs also need the
constructive direction: an explicitly declared environment row, an exact
argument match, and an exact binding merge produce a successful query result.

These lemmas expose that boundary without unfolding the complete query engine
inside every downstream language proof.  They grant no authority to an
external relation beyond the row and matching evidence supplied by the caller.
-/

namespace Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine

/-! ## Small matching constructors -/

/-- A bound query variable matches its already-bound value without extending
the binding map. -/
theorem matchRelationArgument_bound_self
    {bindings : Bindings} {name : String} {value : Pattern}
    (found : bindings.lookup name = some value) :
    [] ∈ matchRelationArgument bindings (.fvar name) value := by
  simp [matchRelationArgument, found]

/-- An unbound top-level query variable acquires exactly the supplied value. -/
theorem matchRelationArgument_unbound
    {bindings : Bindings} {name : String} {value : Pattern}
    (missing : bindings.lookup name = none) :
    [(name, value)] ∈
      matchRelationArgument bindings (.fvar name) value := by
  simp [matchRelationArgument, missing]

/-- Empty argument and tuple lists match with the empty extension. -/
theorem matchRelationArgs_nil (bindings : Bindings) :
    [] ∈ matchRelationArgs bindings [] [] := by
  simp [matchRelationArgs]

/-- Compose one exact argument match with an exact tail match.  Keeping both
merges explicit retains the proof-relevant binding order used by the engine. -/
theorem matchRelationArgs_cons
    {seed headExtension extended tailExtension combined : Bindings}
    {argument value : Pattern} {arguments values : List Pattern}
    (head : headExtension ∈
      matchRelationArgument seed argument value)
    (extend : mergeBindings seed headExtension = some extended)
    (tail : tailExtension ∈
      matchRelationArgs extended arguments values)
    (combine : mergeBindings headExtension tailExtension = some combined) :
    combined ∈ matchRelationArgs seed
      (argument :: arguments) (value :: values) := by
  simp only [matchRelationArgs, List.mem_flatMap]
  refine ⟨headExtension, head, ?_⟩
  rw [extend]
  simp only [List.mem_filterMap]
  exact ⟨tailExtension, tail, combine⟩

/-- Prepending an already-bound variable retains the exact extension produced
by the remaining arguments. -/
theorem matchRelationArgs_bound_cons
    {seed tailExtension combined : Bindings}
    {name : String} {value : Pattern}
    {arguments values : List Pattern}
    (found : seed.lookup name = some value)
    (tail : tailExtension ∈ matchRelationArgs seed arguments values)
    (combine : mergeBindings [] tailExtension = some combined) :
    combined ∈ matchRelationArgs seed
      (.fvar name :: arguments) (value :: values) := by
  exact matchRelationArgs_cons
    (matchRelationArgument_bound_self found)
    (by simp [mergeBindings]) tail
    combine

/-- A final argument with an exact matcher fibre contributes exactly that
fibre to the query result. -/
theorem matchRelationArgs_single
    {seed extension extended : Bindings} {argument value : Pattern}
    (matched : extension ∈ matchRelationArgument seed argument value)
    (merged : mergeBindings seed extension = some extended) :
    extension ∈ matchRelationArgs seed [argument] [value] := by
  exact matchRelationArgs_cons matched merged
    (matchRelationArgs_nil _) (by simp [mergeBindings])

/-- A row explicitly supplied by `RelationEnv`, together with its exact
argument match and binding merge, is admitted by `relationQueryStep`.

The environment is queried at the already-substituted argument list, exactly
as the engine does.  Builtin rows remain a separate disjunct and are not used
by this constructor. -/
theorem relationQueryStep_of_env_tuple
    {relEnv : RelationEnv} {language : LanguageDef}
    {bindings extension result : Bindings}
    {relation : String} {arguments tuple : List Pattern}
    (row : tuple ∈ relEnv.tuples relation
      (arguments.map (applyBindings bindings)))
    (matched : extension ∈ matchRelationArgs bindings arguments tuple)
    (merged : mergeBindings bindings extension = some result) :
    result ∈ relationQueryStep relEnv language bindings relation arguments := by
  unfold relationQueryStep
  rw [List.mem_flatMap]
  refine ⟨tuple, ?_, ?_⟩
  · exact List.mem_append.mpr (Or.inr row)
  · rw [List.mem_filterMap]
    exact ⟨extension, matched, merged⟩

/-- Constructive introduction rule for a `relationQuery` premise. -/
theorem premiseStepWithEnv_relationQuery_of_env_tuple
    {relEnv : RelationEnv} {language : LanguageDef}
    {bindings extension result : Bindings}
    {relation : String} {arguments tuple : List Pattern}
    (row : tuple ∈ relEnv.tuples relation
      (arguments.map (applyBindings bindings)))
    (matched : extension ∈ matchRelationArgs bindings arguments tuple)
    (merged : mergeBindings bindings extension = some result) :
    result ∈ premiseStepWithEnv relEnv language bindings
      (.relationQuery relation arguments) := by
  exact relationQueryStep_of_env_tuple row matched merged

/-- The introduction rule and the engine's existing elimination rule retain
the same merge witness.  This small round-trip is useful when a language proof
must preserve exact binding fibres rather than only query success. -/
theorem admitted_relationQuery_has_merge_witness
    {relEnv : RelationEnv} {language : LanguageDef}
    {bindings extension result : Bindings}
    {relation : String} {arguments tuple : List Pattern}
    (row : tuple ∈ relEnv.tuples relation
      (arguments.map (applyBindings bindings)))
    (matched : extension ∈ matchRelationArgs bindings arguments tuple)
    (merged : mergeBindings bindings extension = some result) :
    ∃ recovered : Bindings,
      mergeBindings bindings recovered = some result := by
  exact premiseStepWithEnv_relationQuery_mem
    (lang := language)
    (premiseStepWithEnv_relationQuery_of_env_tuple
      (language := language) row matched merged)

/-! ## Failure composition -/

/-- If one premise has no binding continuation, no suffix can revive the
premise list.  This is the elimination counterpart of the constructive query
admission lemmas above and does not assume that other relation queries are
functional. -/
theorem applyPremisesWithEnv_eq_nil_of_head_eq_nil
    {relEnv : RelationEnv} {language : LanguageDef}
    {bindings : Bindings} {premise : Premise} {remaining : List Premise}
    (headEmpty :
      premiseStepWithEnv relEnv language bindings premise = []) :
    applyPremisesWithEnv relEnv language (premise :: remaining) bindings =
      [] := by
  unfold applyPremisesWithEnv
  rw [List.foldl_cons]
  simp only [List.flatMap_singleton, headEmpty]
  induction remaining with
  | nil => rfl
  | cons next rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatMap_nil]
      exact inductionHypothesis

end Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
