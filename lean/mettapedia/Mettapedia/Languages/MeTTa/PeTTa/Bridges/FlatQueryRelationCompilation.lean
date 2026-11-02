import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryPatternExtraction
import Mettapedia.GSLT.Dynamics.PreparedFactorIndex

/-!
# Source-row compilation without answer enumeration

The compiler scans the supplied source snapshot once. A supported row keeps
its original ordinal even when earlier rows were proved irrelevant. An
unsupported row refuses the whole compilation; it is never discarded as a
failed match. Distinct occurrences remain distinct entries.

The exactness theorem holds for every represented incoming binding state,
not merely the state observed during compilation. The source side is the
actual PeTTa row matcher, and erasing ordinals recovers `queryBodies`.
Ordinals are snapshot-local occurrences, not native global object identities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryRelationCompilation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics.ConjunctiveRowMatching
open Mettapedia.GSLT.Dynamics.ConjunctiveRegionProvenance
open SpaceSemantics FlatQueryRowCodec FlatQueryPatternExtraction

variable {Value : Type} [DecidableEq Value]

structure Entry {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) where
  ordinal : Nat
  values : List Value
  arity : values.length = compiled.cells.length

def Entry.vector {codec : Codec Value} {names : Inventory String} {source : Atom}
    {compiled : Compiled codec names source} (entry : Entry compiled) : Fin compiled.cells.length → Value :=
  fun column => entry.values.get (Fin.cast entry.arity.symm column)

omit [DecidableEq Value] in
theorem Entry.vector_exact {codec : Codec Value} {names : Inventory String} {source : Atom}
    {compiled : Compiled codec names source} (entry : Entry compiled) : List.ofFn entry.vector = entry.values := by
  apply List.ext_getElem
  · simp [entry.arity]
  · intro index left right
    rw [List.getElem_ofFn]
    rfl

def nativeScan {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) (environment : DenseEnvironment names Value)
    (rows : List (Entry compiled)) : List (Nat × DenseEnvironment names Value) :=
  rows.flatMap fun entry => ((bindValues environment compiled.cells entry.values).map (entry.ordinal, ·)).toList

def sourceScan (bindings : Subst) (pattern : Atom) : Nat → List Atom → List (Nat × Subst)
  | _, [] => []
  | start, row :: rows => ((matchValue bindings pattern row).map (start, ·)).toList ++ sourceScan bindings pattern (start + 1) rows

def project (codec : Codec Value) (names : Inventory String) (answer : Nat × Subst) : Nat × DenseEnvironment names Value :=
  (answer.1, readback codec names answer.2)

omit [DecidableEq Value] in
theorem project_occurrence (codec : Codec Value) (names : Inventory String) (ordinal : Nat) (choice : Option Subst) :
    (((choice.map (ordinal, ·)).toList).map (project codec names)) =
      ((choice.map (readback codec names)).map (ordinal, ·)).toList := by cases choice <;> rfl

theorem sourceScan_is_queryBodies (bindings : Subst) (pattern body : Atom) (start : Nat) (rows : List Atom) :
    (sourceScan bindings pattern start rows).map (fun answer => Eval.Control.evaluate answer.2 body) =
      Eval.queryBodies bindings rows pattern body := by
  change (sourceScan bindings pattern start rows).map (fun answer => Eval.Control.evaluate answer.2 body) =
    rows.filterMap (fun row => (matchValue bindings pattern row).map (fun bound => Eval.Control.evaluate bound body))
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
      cases matched : matchValue bindings pattern row <;>
        simp [sourceScan, matched, ih]

theorem known_row_exact {codec : Codec Value} {names : Inventory String} {source atom : Atom}
    (compiled : Compiled codec names source) (known : KnownRow compiled atom)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings) :
    (matchValue bindings source atom).map (readback codec names) = bindValues environment compiled.cells known.values := by
  simpa only [compiled.exact, known.exact] using
    row_readback_exact codec names environment bindings represented compiled.head compiled.ordinary compiled.cells known.values

theorem known_row_preserves {codec : Codec Value} {names : Inventory String} {source atom : Atom}
    (compiled : Compiled codec names source) (known : KnownRow compiled atom)
    (environment : DenseEnvironment names Value) (bindings after : Subst)
    (represented : Represents codec names environment bindings)
    (matched : matchValue bindings source atom = some after) :
    Represents codec names (readback codec names after) after := by
  have related := match_row codec names environment bindings represented compiled.head compiled.ordinary compiled.cells known.values
  simp only [compiled.exact, known.exact, matched] at related
  cases result : bindValues environment compiled.cells known.values with
  | none => rw [result] at related; cases related
  | some output =>
      rw [result] at related
      have agrees := Option.rel_some_some.mp related
      rw [readback_exact codec names output after agrees]
      exact agrees

structure Relation {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) (start : Nat) (rows : List Atom) where
  entries : List (Entry compiled)
  lower : ∀ entry ∈ entries, start ≤ entry.ordinal
  upper : ∀ entry ∈ entries, entry.ordinal < start + rows.length
  increasing : entries.Pairwise (fun first second => first.ordinal < second.ordinal)
  exact : ∀ environment bindings, Represents codec names environment bindings →
    nativeScan compiled environment entries = (sourceScan bindings source start rows).map (project codec names)
  preserves : ∀ environment bindings, Represents codec names environment bindings →
    ∀ answer ∈ sourceScan bindings source start rows,
      Represents codec names (readback codec names answer.2) answer.2

def Relation.nil {codec : Codec Value} {names : Inventory String} {source : Atom}
    (compiled : Compiled codec names source) (start : Nat) : Relation compiled start [] where
  entries := []
  lower _ member := False.elim (List.not_mem_nil member)
  upper _ member := False.elim (List.not_mem_nil member)
  increasing := .nil
  exact _ _ _ := rfl
  preserves _ _ _ _ member := False.elim (List.not_mem_nil member)

def Relation.skip {codec : Codec Value} {names : Inventory String} {source row : Atom}
    {compiled : Compiled codec names source} {start : Nat} {rows : List Atom}
    (irrelevant : ∀ bindings, matchValue bindings source row = none)
    (later : Relation compiled (start + 1) rows) : Relation compiled start (row :: rows) where
  entries := later.entries
  lower entry member := (Nat.le_succ start).trans (later.lower entry member)
  upper entry member := by have bound := later.upper entry member; simp only [List.length_cons]; omega
  increasing := later.increasing
  exact environment bindings represented := by
    simpa [sourceScan, irrelevant bindings] using later.exact environment bindings represented
  preserves environment bindings represented answer member := by
    apply later.preserves environment bindings represented answer
    simpa [sourceScan, irrelevant bindings] using member

def Relation.cons {codec : Codec Value} {names : Inventory String} {source row : Atom}
    {compiled : Compiled codec names source} {start : Nat} {rows : List Atom}
    (known : KnownRow compiled row) (later : Relation compiled (start + 1) rows) :
    Relation compiled start (row :: rows) where
  entries := ⟨start, known.values, known.arity⟩ :: later.entries
  lower entry member := by
    rcases List.mem_cons.mp member with same | old
    · subst entry; exact Nat.le_refl _
    · exact (Nat.le_succ start).trans (later.lower entry old)
  upper entry member := by
    rcases List.mem_cons.mp member with same | old
    · subst entry; simp
    · have bound := later.upper entry old; simp only [List.length_cons]; omega
  increasing := List.pairwise_cons.mpr ⟨fun entry member => later.lower entry member, later.increasing⟩
  exact environment bindings represented := by
    simp only [nativeScan, List.flatMap_cons, sourceScan, List.map_append]
    rw [project_occurrence, known_row_exact compiled known environment bindings represented]
    exact congrArg (fun tail => ((bindValues environment compiled.cells known.values).map (start, ·)).toList ++ tail)
      (later.exact environment bindings represented)
  preserves environment bindings represented answer member := by
    rcases List.mem_append.mp member with first | rest
    · have selected := Option.mem_toList.mp first
      obtain ⟨after, matched, same⟩ := Option.map_eq_some_iff.mp selected
      cases same
      exact known_row_preserves compiled known environment bindings after represented matched
    · exact later.preserves environment bindings represented answer rest

def compile {codec : Codec Value} {names : Inventory String} {source : Atom}
    (pattern : Compiled codec names source) : (start : Nat) → (rows : List Atom) → Option (Relation pattern start rows)
  | start, [] => some (Relation.nil pattern start)
  | start, row :: rows => do
      let disposition ← classifyRow pattern row
      let later ← compile pattern (start + 1) rows
      match disposition with
      | .irrelevant proof => return Relation.skip proof later
      | .known known => return Relation.cons known later

theorem rejected_row_refuses_relation {codec : Codec Value} {names : Inventory String} {source row : Atom}
    (pattern : Compiled codec names source) (start : Nat) (rows : List Atom)
    (unsupported : classifyRow pattern row = none) : compile pattern start (row :: rows) = none := by
  simp [compile, unsupported]

theorem unique_occurrence_ids {codec : Codec Value} {names : Inventory String} {source : Atom}
    {compiled : Compiled codec names source} {start : Nat} {rows : List Atom}
    (relation : Relation compiled start rows) : (relation.entries.map Entry.ordinal).Nodup :=
  (List.pairwise_map.mpr relation.increasing).imp (fun less => Nat.ne_of_lt less)

/-- The artifact is the existing conjunctive-query Factor, not a parallel
relational language. Original source ordinals are its occurrence tokens. -/
def Relation.factor {codec : Codec Value} {names : Inventory String} {source : Atom}
    {compiled : Compiled codec names source} {start : Nat} {rows : List Atom}
    (relation : Relation compiled start rows) : Factor names.Slot Value Nat where
  arity := compiled.cells.length
  pattern := compiled.cells.get
  rows := relation.entries.map (fun entry => (entry.ordinal, entry.vector))

theorem factorScan_source_exact {codec : Codec Value} {names : Inventory String} {source : Atom}
    {compiled : Compiled codec names source} {start : Nat} {rows : List Atom}
    (relation : Relation compiled start rows) (environment : DenseEnvironment names Value) (bindings : Subst)
    (represented : Represents codec names environment bindings) :
    (relation.factor.rows.flatMap fun row => ((bindFactor environment relation.factor row).map (row.1, ·)).toList) =
      (sourceScan bindings source start rows).map (project codec names) := by
  rw [← relation.exact environment bindings represented]
  simp only [Relation.factor, List.flatMap_map, bindFactor,
    List.ofFn_get, Entry.vector_exact, nativeScan]

theorem factor_occurrences_exact {codec : Codec Value} {names : Inventory String} {source : Atom}
    {compiled : Compiled codec names source} {start : Nat} {rows : List Atom}
    (relation : Relation compiled start rows) (assignment : names.Slot → Value) (bindings : Subst)
    (represented : Represents codec names (fun name => some (assignment name)) bindings) :
    relation.factor.occurrences assignment = (sourceScan bindings source start rows).map Prod.fst := by
  have exact := congrArg (List.map Prod.fst)
    (factorScan_source_exact relation (fun name => some (assignment name)) bindings represented)
  simp only [List.map_flatMap, List.map_map, Function.comp_def, project, bindFactor_full] at exact
  have collect (entries : List (Nat × (Fin relation.factor.arity → Value))) :
      (entries.flatMap fun row =>
        ((if relation.factor.acceptsRow assignment row then some (fun name => some (assignment name)) else none).map
          (row.1, ·)).toList.map Prod.fst) =
      (entries.filter (relation.factor.acceptsRow assignment)).map Prod.fst := by
    induction entries with
    | nil => rfl
    | cons row entries ih =>
        cases accepted : relation.factor.acceptsRow assignment row with
        | false => simpa [accepted] using ih
        | true => simpa [accepted] using congrArg (row.1 :: ·) ih
  rw [collect] at exact
  exact exact

theorem indexed_occurrences_source {OrderedValue : Type} [LinearOrder OrderedValue]
    {codec : Codec OrderedValue} {names : Inventory String} {source : Atom}
    {compiled : Compiled codec names source} {start : Nat} {rows : List Atom}
    (relation : Relation compiled start rows) (assignment : names.Slot → OrderedValue) (bindings : Subst)
    (represented : Represents codec names (fun name => some (assignment name)) bindings) (outside : OrderedValue) :
    (Mettapedia.GSLT.Dynamics.PreparedFactorIndex.occurrences
      (Mettapedia.GSLT.Dynamics.PreparedFactorIndex.prepare relation.factor) assignment outside).Perm
      ((sourceScan bindings source start rows).map Prod.fst) := by
  rw [← factor_occurrences_exact relation assignment bindings represented]
  exact Mettapedia.GSLT.Dynamics.PreparedFactorIndex.occurrences_exact
    (Mettapedia.GSLT.Dynamics.PreparedFactorIndex.prepare relation.factor) assignment outside

theorem indexed_count_source {OrderedValue : Type} [LinearOrder OrderedValue]
    {codec : Codec OrderedValue} {names : Inventory String} {source : Atom}
    {compiled : Compiled codec names source} {start : Nat} {rows : List Atom}
    (relation : Relation compiled start rows) (assignment : names.Slot → OrderedValue) (bindings : Subst)
    (represented : Represents codec names (fun name => some (assignment name)) bindings) (outside : OrderedValue) :
    Mettapedia.GSLT.Dynamics.PreparedFactorIndex.weight
      (Mettapedia.GSLT.Dynamics.PreparedFactorIndex.prepare relation.factor) (fun _ => (1 : Nat)) assignment outside =
      (sourceScan bindings source start rows).length := by
  rw [Mettapedia.GSLT.Dynamics.PreparedFactorIndex.weight_exact,
    factor_occurrences_exact relation assignment bindings represented]
  simp [Function.comp_def]

namespace Controls

open FlatQueryPatternExtraction.Controls FlatQueryRowCodec.Controls

def rows : List Atom := [.expression [.symbol "unrelated"],
  .expression [.symbol "r", .grounded (.int 7), .grounded (.int 7)],
  .expression [.symbol "r", .grounded (.int 7), .grounded (.int 7)]]

def relation : Relation compiled 10 rows := (compile compiled 10 rows).get (by decide +kernel)

theorem skipped_rows_do_not_renumber_occurrences : relation.entries.map Entry.ordinal = [11, 12] := by decide +kernel

theorem duplicate_values_still_yield_two_bindings :
    (nativeScan compiled (fun _ => none) relation.entries).map (fun answer => (answer.1, answer.2 only)) =
      [(11, some 7), (12, some 7)] := by decide +kernel

theorem inconsistent_captured_value_yields_no_row :
    nativeScan compiled (fun _ => some 8) relation.entries = [] := by decide +kernel

theorem open_row_is_not_silently_filtered_out :
    (compile compiled 0 (.expression [.symbol "r", .var "stored", .grounded (.int 7)] :: rows)).isNone = true := by decide +kernel

theorem prepared_index_keeps_two_source_occurrences :
    Mettapedia.GSLT.Dynamics.PreparedFactorIndex.weight
      (Mettapedia.GSLT.Dynamics.PreparedFactorIndex.prepare relation.factor) (fun _ => (1 : Nat)) (fun _ => 7) 0 = 2 := by
  rw [indexed_count_source relation (fun _ => 7) [("x", .grounded (.int 7))]
    (by intro slot; fin_cases slot; rfl) 0]
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryRelationCompilation
