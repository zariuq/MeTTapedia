import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StratifiedCensusCollection
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommutativeMatching

/-! # Actual collection preserves duplicates, order and its stratified cut -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StratifiedCensusCollection.Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Sources Sources.Commutative
open Mettapedia.Machines
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Collection

abbrev Value := Tm Nat
abbrev Pattern := Pat Nat Nat
def noComm (_ : Nat) : Bool := false
abbrev layer : TermLayer Nat Value Pattern := termLayer noComm
abbrev matcher : Matcher Nat Value Pattern := cmatch noComm
def queryVar : Pattern := .var 0
def label (occurrence : Nat) : Value := if occurrence < 2 then .leaf 1 else .leaf 2
def contents : List Nat := [0, 1, 2]
def collected (state : Store Nat Value) := observe layer matcher label contents queryVar queryVar state
def allData (state : Store Nat Value) := packet layer matcher label contents queryVar queryVar state
def constrain : Steps Nat Value := [(0, .leaf 2)]

theorem the_census_is_complete (state : Store Nat Value) :
    (census matcher label contents queryVar state).Holds label contents.toFinset :=
  census_holds matcher label contents (by decide) queryVar state

theorem measured_order_effect_with_duplicates :
    (collectFirst collected Store.empty constrain).map (fun result => result.1.answer) = some [.leaf 1, .leaf 1, .leaf 2] ∧
      (constrainFirst collected Store.empty constrain).map (fun result => result.1.answer) = some [.leaf 2] := by
  decide +kernel

theorem region_reads_the_shared_name (value : Value) :
    ReadsOnly [0] (fun state => Matcher.region matcher state queryVar value) := by
  intro first second agrees
  have here := agrees 0 (List.mem_singleton_self _)
  cases initial : first 0 with
  | none =>
      have final : second 0 = none := here.symm.trans initial
      simp [Matcher.region, matcher, cmatch, rawMatch, queryVar, initial, final, List.pwFilter]
  | some bound =>
      have final : second 0 = some bound := here.symm.trans initial
      simp [Matcher.region, matcher, cmatch, rawMatch, queryVar, initial, final]
      split_ifs <;> simp [List.pwFilter]

theorem values_read_the_shared_name (value : Value) :
    ReadsOnly [0] (fun state => emitted layer matcher queryVar queryVar state value) := by
  intro first second agrees
  have here := agrees 0 (List.mem_singleton_self _)
  cases initial : first 0 with
  | none =>
      have final : second 0 = none := here.symm.trans initial
      simp [emitted, matcher, cmatch, rawMatch, queryVar, initial, final, layer, termLayer, Pat.inst, List.pwFilter]
  | some bound =>
      have final : second 0 = some bound := here.symm.trans initial
      simp [emitted, matcher, cmatch, rawMatch, queryVar, initial, final, layer, termLayer, Pat.inst]
      split_ifs <;> simp [List.pwFilter, initial, final]

/-- The whole result is stable, including its actual ordered transcript and
census, while an unrelated name acquires information. -/
theorem determined_collection_survives_unrelated_refinement
    {first second : Store Nat Value} (known : Determined [0] first) (grows : first ⊑ second) :
    allData second = allData first :=
  stable_after_determination layer matcher label contents queryVar queryVar [0]
    region_reads_the_shared_name values_read_the_shared_name known grows

theorem the_actual_query_has_stratified_meaning
    {constraints reordered : Steps Nat Value} (permuted : constraints.Perm reordered) :
    constrainFirst allData Store.empty reordered =
      (solveConj constraints).map fun state => (allData state, state) :=
  stratified_census_meaning layer matcher label contents queryVar queryVar permuted

/-- Two compatible bindings in different orders produce the same collection
of the actual stored rows and the same complete-read metadata. -/
theorem concrete_constraint_orders_agree :
    (constrainFirst collected Store.empty [(0, .leaf 2), (1, .leaf 7)]).map (fun result => result.1.answer) = some [.leaf 2] ∧
      (constrainFirst collected Store.empty [(1, .leaf 7), (0, .leaf 2)]).map (fun result => result.1.answer) = some [.leaf 2] := by
  decide +kernel

/-- Equal predicate censuses do not certify answer order. The existing
ordered transcript detects this reversed scanner reply. -/
theorem an_ordered_collection_needs_its_transcript :
    census matcher label contents queryVar Store.empty = census matcher label contents.reverse queryVar Store.empty ∧
      (observe layer matcher label contents queryVar queryVar Store.empty).answer = [.leaf 1, .leaf 1, .leaf 2] ∧
      (observe layer matcher label contents.reverse queryVar queryVar Store.empty).answer = [.leaf 2, .leaf 1, .leaf 1] ∧
      ReadOnlyQuery.checkReads (Query.scanList label contents.reverse)
        (collected Store.empty).reads = false := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  apply congrArg (fun seen => (⟨Matcher.region matcher Store.empty queryVar, seen⟩ : PredicateQuery Nat Value))
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StratifiedCensusCollection.Controls
