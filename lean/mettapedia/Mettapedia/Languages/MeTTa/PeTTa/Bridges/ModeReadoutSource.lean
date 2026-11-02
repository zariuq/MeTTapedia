import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeFoldSource

/-!
# The source readout after a captured mode fold

The tuple result is bound by the actual PeTTa matcher, and its readout runs in
the existing evaluator. Quotation is the explicit injection of the already
captured fold value into that continuation, not reevaluation of the value.
The final-result observer then licenses histogram readout; the tuple trace
and source-machine page count are deliberately not identified with it.

Input sortedness is explicit. The downstream IntegerSortSource bridge connects
source integer msort to this adapter. General fold dispatch and the enclosing
label-generation effects remain outside this captured-input adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeReadoutSource

open ModeFoldSource
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)
open Mettapedia.Machines.TypedScalar
open Mettapedia.Machines.ModeAggregation
open Eval SpaceSemantics MeTTaIL.WireKit

def environment (names : Names) : ScalarSource.Environment Slot := fun name =>
  if name = names.current then some .current else
  if name = names.count then some .count else
  if name = names.best then some .best else
  if name = names.bestCount then some .bestCount else none

def callee (names : Names) (state : RunState) : Subst :=
  [(names.bestCount, number state.best.count), (names.best, labelAtom state.best.label),
    (names.count, number state.runCount), (names.current, labelAtom state.current)]

theorem captured (names : Names) (distinct : names.all.Nodup) (state : RunState) :
    ScalarSource.Captured (environment names) (callee names state) (locals state 0) := by
  simp only [Names.all, Names.fields, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  intro name slot found
  unfold environment at found
  split_ifs at found <;> cases found
  all_goals subst name
  all_goals simp_all [callee, Subst.lookup, locals, labelAtom, number, encoded,
    MeTTaIL.CettaWireAtom.encode, ScalarSource.encode, ne_comm]

def ir : ScalarBody.Body Slot :=
  .branch (.binary .gt (.read .count) (.read .bestCount))
    (.scalar (ModeFoldSource.read .current)) (.scalar (ModeFoldSource.read .best))

theorem ir_uniform (program : Program) (state : RunState) :
    ir.eval program (locals state 0) = some (labelAtom (SortedRun.finish state).label) := by
  by_cases larger : state.best.count < state.runCount <;>
    simp [ir, ScalarBody.Body.eval, ScalarBody.evalField, ModeFoldSource.read,
      Expr.eval, Binary.eval, locals, SortedRun.finish, larger, labelAtom]

abbrev Certified (program : Program) (names : Names) (source : Atom) :=
  ScalarBody.Recognized program (environment names) source ir

def infer (program : Program) (names : Names) (source : Atom) : Option (Certified program names source) :=
  ScalarBody.recognize program (environment names) source ir

theorem Certified.returns {program : Program} {names : Names} {source : Atom}
    (certificate : Certified program names source) (distinct : names.all.Nodup)
    (world : Effects.State) (state : RunState) :
    PureReturns program (callee names state) world source world (labelAtom (SortedRun.finish state).label) := by
  apply certificate.compiled.returns _ world (locals state 0) (captured names distinct state)
  rw [ScalarBody.canonical_equal_eval certificate.body ir certificate.normalized, ir_uniform]

def pattern (names : Names) : Atom := .expression (names.fields.map Atom.var)

theorem match_result (names : Names) (distinct : names.all.Nodup) (state : RunState) :
    matchBinding [] (pattern names) (encode state) = some (callee names state) := by
  simp only [Names.all, Names.fields, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  simp_all [pattern, Names.fields, encode, matchBinding, matchValue, matchValue.matchValues,
    matchAtom, Subst.lookup, callee]

def continuation (names : Names) (body accumulator : Atom) : Atom :=
  apply "let" [pattern names, apply "quote" [accumulator], body]

theorem Certified.continuation_returns {program : Program} {names : Names} {source : Atom}
    (certificate : Certified program names source) (distinct : names.all.Nodup)
    (world : Effects.State) (state : RunState) :
    PureReturns program [] world (continuation names source (encode state)) world
      (labelAtom (SortedRun.finish state).label) := by
  apply let_returns program [] (callee names state) world world world _ _ _ (encode state) _
    (by simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using
      quote_returns program [] world (encode state)) (match_result names distinct state)
    (certificate.returns distinct world state)

/-- The source's captured fold followed by its ordinary let/readout
continuation. No optimized histogram occurs in this reference judgment. -/
def Completes (program : Program) (head : String) (names : Names) (body : Atom)
    (world : Effects.State) (labels : List Nat) (answer : Atom) : Prop :=
  ∃ accumulator,
    FoldSource.Evaluates program (wrappedCallback head) world (labels.map number)
      (encode SortedRun.initial) accumulator ∧
    PureReturns program [] world (continuation names body accumulator) world answer

theorem source_complete {program : Program} {head : String} (step : ModeFoldSource.Certified program head)
    {body : Atom} (finish : Certified program step.names body) (world : Effects.State) (labels : List Nat) :
    Completes program head step.names body world labels (labelAtom (SortedRun.sourceMode labels)) :=
  ⟨_, step.wrapped_fold world labels SortedRun.initial,
    finish.continuation_returns step.distinct world (labels.foldl SortedRun.step SortedRun.initial)⟩

theorem source_complete_iff {program : Program} {head : String} (step : ModeFoldSource.Certified program head)
    {body : Atom} (finish : Certified program step.names body) (world : Effects.State)
    (labels : List Nat) (answer : Atom) :
    Completes program head step.names body world labels answer ↔ answer = labelAtom (SortedRun.sourceMode labels) := by
  constructor
  · rintro ⟨accumulator, folded, returned⟩
    have same := FoldSource.evaluates_unique folded (step.wrapped_fold world labels SortedRun.initial)
    subst accumulator
    obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program [] world world _ answer returned
    have unique := (pure_returns_completed_iff program [] world world _ _
      (finish.continuation_returns step.distinct world (labels.foldl SortedRun.step SortedRun.initial))
      world [answer] [] []).mp ⟨fuel, completed⟩
    exact (List.cons.inj unique.2.1).1
  · rintro rfl
    exact source_complete step finish world labels

theorem sorted_source_is_histogram {program : Program} {head : String} (step : ModeFoldSource.Certified program head)
    {body : Atom} (finish : Certified program step.names body) (world : Effects.State)
    (labels : List Nat) (sorted : labels.Pairwise (· ≤ ·)) (answer : Atom) :
    Completes program head step.names body world labels answer ↔
      answer = labelAtom (sparseReadout (sparseHistogram labels)) := by
  rw [source_complete_iff step finish, SortedRun.source_equals_mode labels sorted, sparse_readout_exact]

theorem permuted_then_sorted_source {program : Program} {head : String} (step : ModeFoldSource.Certified program head)
    {body : Atom} (finish : Certified program step.names body) (world : Effects.State)
    (labels : List Nat) (answer : Atom) :
    Completes program head step.names body world (labels.mergeSort (· ≤ ·)) answer ↔
      answer = labelAtom (sparseReadout (sparseHistogram labels)) := by
  rw [source_complete_iff step finish, SortedRun.sorted_source_is_histogram_readout]

theorem grouped_source_readout {Key : Type} [DecidableEq Key]
    {program : Program} {head : String} (step : ModeFoldSource.Certified program head)
    {body : Atom} (finish : Certified program step.names body) (world : Effects.State)
    (bound : Nat) (rows : List (Key × Nat)) (key : Key)
    (bounded : ∀ row ∈ rows, row.2 < bound) (answer : Atom) :
    Completes program head step.names body world ((Grouped.votes rows key).mergeSort (· ≤ ·)) answer ↔
      answer = labelAtom (Grouped.finiteReadout bound (Multiplicative.toAdd (Grouped.groupedCounts bound rows key))) := by
  rw [source_complete_iff step finish, Grouped.grouped_mode_exact bound rows key bounded]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeReadoutSource
