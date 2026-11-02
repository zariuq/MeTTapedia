import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeReadoutSource
import Mettapedia.Algorithms.CountedKeySort

/-!
# Integer sorting through the actual PeTTa evaluator

The registered `msort` primitive now evaluates its operand with the existing
machine and sorts only the admitted closed integer-list fragment. The
source theorem preserves the operand's resulting world; sorting itself does
not change it. A counted merge worker refines the independent primitive's
ordered result, including repeated values and arbitrary-precision integers.

The mode composition uses this actual sorting path before the previously
certified captured fold/readout. General nested fold dispatch, mixed-value
term ordering and native machine-word costs remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.IntegerSortSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Algorithms
open Eval SpaceSemantics

def source (operand : Atom) : Atom := .expression [.symbol "msort", operand]

theorem returns (program : Program) (caller : Subst) (before after : Effects.State)
    (operand : Atom) (values : List Int)
    (evaluated : PureReturns program caller before operand after (.expression (StdLib.integerAtoms values))) :
    PureReturns program caller before (source operand) after
      (.expression (StdLib.integerAtoms (values.mergeSort (· ≤ ·)))) := by
  apply native_unary_call_returns program caller before after after "msort" operand
    (.expression (StdLib.integerAtoms values)) _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) evaluated
    (StdLib.integer_msort after values) (by decide)

theorem worker_exact (values : List Int) :
    (CountedKeySort.run id values).rows = values.mergeSort (· ≤ ·) := by
  have checked := CountedKeySort.run_spec (id : Int → Int) values
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    checked.2.1 (List.pairwise_mergeSort' (· ≤ ·) values)
  exact checked.1.trans (List.mergeSort_perm values (· ≤ ·)).symm

theorem worker_source_return (program : Program) (caller : Subst) (before after : Effects.State)
    (operand : Atom) (values : List Int)
    (evaluated : PureReturns program caller before operand after (.expression (StdLib.integerAtoms values))) :
    PureReturns program caller before (source operand) after
      (.expression (StdLib.integerAtoms (CountedKeySort.run id values).rows)) := by
  rw [worker_exact]
  exact returns program caller before after operand values evaluated

theorem worker_comparisons (values : List Int) :
    (CountedKeySort.run id values).comparisons ≤ values.length * CountedKeySort.depth values.length :=
  (CountedKeySort.run_spec id values).2.2

theorem nat_sort_embedding (values : List Nat) :
    (values.map Int.ofNat).mergeSort (· ≤ ·) = (values.mergeSort (· ≤ ·)).map Int.ofNat := by
  symm
  apply List.map_mergeSort
  intro left leftMember right rightMember
  simp

theorem natural_atoms (values : List Nat) :
    StdLib.integerAtoms (values.map Int.ofNat) = values.map MeTTaIL.WireKit.number := by
  simp only [StdLib.integerAtoms, List.map_map, Function.comp_def]
  rfl

theorem natural_returns (program : Program) (caller : Subst) (before after : Effects.State)
    (operand : Atom) (values : List Nat)
    (evaluated : PureReturns program caller before operand after
      (.expression (values.map MeTTaIL.WireKit.number))) :
    PureReturns program caller before (source operand) after
      (.expression ((values.mergeSort (· ≤ ·)).map MeTTaIL.WireKit.number)) := by
  have input := evaluated
  rw [← natural_atoms] at input
  have result := returns program caller before after operand (values.map Int.ofNat) input
  rw [nat_sort_embedding, natural_atoms] at result
  exact result

theorem sorted_return_unique (program : Program) (caller : Subst) (before after : Effects.State)
    (operand : Atom) (values : List Nat)
    (evaluated : PureReturns program caller before operand after
      (.expression (values.map MeTTaIL.WireKit.number)))
    (observedWorld : Effects.State) (observed : Atom)
    (returned : PureReturns program caller before (source operand) observedWorld observed) :
    observedWorld = after ∧ observed = .expression ((values.mergeSort (· ≤ ·)).map MeTTaIL.WireKit.number) := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program caller before observedWorld _ _ returned
  have unique := (pure_returns_completed_iff program caller before after _ _
    (natural_returns program caller before after operand values evaluated) observedWorld [observed] [] []).mp ⟨fuel, completed⟩
  exact ⟨unique.1, (List.cons.inj unique.2.1).1⟩

/-- Source sorting followed by the captured fold and its actual let/readout.
The two stages are explicit; this does not rename the composition as a proof
of general host-fold dispatch inside the evaluator. -/
def ModeCompletes (program : Program) (caller : Subst) (operand : Atom)
    (head : String) (names : ModeFoldSource.Names) (readout : Atom)
    (before after : Effects.State) (answer : Atom) : Prop :=
  ∃ labels : List Nat,
    PureReturns program caller before (source operand) after (.expression (labels.map MeTTaIL.WireKit.number)) ∧
    ModeReadoutSource.Completes program head names readout after labels answer

theorem sorted_mode_is_histogram {program : Program} {caller : Subst} {operand : Atom}
    {head : String} (step : ModeFoldSource.Certified program head)
    {readout : Atom} (finish : ModeReadoutSource.Certified program step.names readout)
    (before after : Effects.State) (values : List Nat)
    (evaluated : PureReturns program caller before operand after
      (.expression (values.map MeTTaIL.WireKit.number))) (answer : Atom) :
    ModeCompletes program caller operand head step.names readout before after answer ↔
      answer = ModeFoldSource.labelAtom (Mettapedia.Machines.ModeAggregation.sparseReadout
        (Mettapedia.Machines.ModeAggregation.sparseHistogram values)) := by
  constructor
  · rintro ⟨labels, sorted, folded⟩
    have same := (sorted_return_unique program caller before after operand values evaluated after _ sorted).2
    have labelsEqual : labels = values.mergeSort (· ≤ ·) := by
      have mapped := Atom.expression.inj same
      have injective : Function.Injective MeTTaIL.WireKit.number := by
        intro first second equal
        change (Atom.grounded (.int first)) = .grounded (.int second) at equal
        exact Int.ofNat_inj.mp (Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue.int.inj (Atom.grounded.inj equal))
      exact injective.list_map mapped
    subst labels
    exact (ModeReadoutSource.permuted_then_sorted_source step finish after values answer).mp folded
  · intro same
    refine ⟨values.mergeSort (· ≤ ·), natural_returns program caller before after operand values evaluated, ?_⟩
    exact (ModeReadoutSource.permuted_then_sorted_source step finish after values answer).mpr same

namespace Controls

def program : Program := {equations := [], declarations := []}
def world : Effects.State := {core := []}

def literal (values : List Int) : Atom := .expression [.symbol "quote", .expression (StdLib.integerAtoms values)]

theorem example_sort_returns :
    PureReturns program [] world (source (literal [3, -2, 3, 1])) world
      (.expression (StdLib.integerAtoms [-2, 1, 3, 3])) := by
  apply native_unary_call_returns program [] world world world "msort" _ _ _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (show PureReturns program [] world (literal [3, -2, 3, 1]) world
      (.expression (StdLib.integerAtoms [3, -2, 3, 1])) from
      by simpa only [literal, ProcessCalculi.MORK.applySubst_nil] using
        (quote_returns program [] world (.expression (StdLib.integerAtoms [3, -2, 3, 1]))))
    (StdLib.integer_sort_keeps_duplicate_values world) (by decide)

theorem nested_size_observes_duplicates :
    PureReturns program [] world
      (.expression [.symbol "size-atom", source (literal [3, -2, 3, 1])]) world
      (.grounded (.int 4)) := by
  exact native_unary_call_returns program [] world world world "size-atom" _ _ _ (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) example_sort_returns rfl (by decide)

theorem nested_index_observes_order :
    PureReturns program [] world
      (.expression [.symbol "index-atom", source (literal [3, -2, 3, 1]), .grounded (.int 0)]) world
      (.grounded (.int (-2))) := by
  exact native_binary_call_returns program [] world world world world "index-atom" _ _ _ _ _
    (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    example_sort_returns (grounded_returns program [] world (.int 0)) rfl (by decide)

theorem boolean_encoding_not_admitted : StdLib.integers [Effects.boolean true] = none := by decide +kernel

theorem wrong_scalar_msort_is_not_sort_atom :
    StdLib.apply world "msort" [.grounded (.int 3)] = .error (.invalidArguments "msort") ∧
      StdLib.apply world "sort-atom" [.grounded (.int 3)] = .ok (world, [.expression []]) := ⟨rfl, rfl⟩

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.IntegerSortSource
