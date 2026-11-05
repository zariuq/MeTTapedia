import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedQueryAdmission

/-!
# Completion of domain-safe nested insertion phases

Static slot coverage, complete current reads and a live destination establish
completion of a single phase. Output construction introduces no unbound slot
or program equation/declaration. This is logical evaluator completion; native
allocation and work admission remain separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryCompletion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance ConjunctiveRowMatching
open FlatQueryRowCodec FlatQueryPatternExtraction FlatQueryRelationCompilation FlatQueryDomainInvariant
open FiniteNestedQuerySource
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

variable {Value : Type} [DecidableEq Value]

def Covered {codec : Codec Value} {names : Inventory String} (queries : List (Query codec names)) (bindings : Subst) : Prop :=
  ∀ slot, (readback codec names bindings slot).isSome ∨ ∃ query ∈ queries, Cell.variable slot ∈ query.pattern.cells

def coveredCheck {codec : Codec Value} {names : Inventory String} (queries : List (Query codec names)) (bindings : Subst) : Bool :=
  (List.finRange names.keys.length).all fun slot => (readback codec names bindings slot).isSome ||
    queries.any (fun query => decide (Cell.variable slot ∈ query.pattern.cells))

theorem coveredCheck_iff {codec : Codec Value} {names : Inventory String}
    (queries : List (Query codec names)) (bindings : Subst) : coveredCheck queries bindings = true ↔ Covered queries bindings := by
  simp [coveredCheck, Covered]

theorem matching_binds_cells {codec : Codec Value} {names : Inventory String} {source : Atom}
    (pattern : Compiled codec names source) (domain : Finset Value) (atom : Atom) (bindings after : Subst)
    (ready : rowReady pattern domain atom = true) (bound : BindingsInDomain codec names domain bindings)
    (matched : matchValue bindings source atom = some after) (slot : names.Slot)
    (used : Cell.variable slot ∈ pattern.cells) : (readback codec names after slot).isSome = true := by
  cases classified : classifyRow pattern atom with
  | none => simp [rowReady, classified] at ready
  | some result =>
      cases result with
      | irrelevant absent => rw [absent bindings] at matched; cases matched
      | known known =>
          have projected := known_row_exact pattern known (readback codec names bindings) bindings bound.1
          rw [matched] at projected
          have pairs := (bindValues_sound projected.symm).2
          obtain ⟨index, inside, atCell⟩ := List.mem_iff_getElem.mp used
          have valueInside : index < known.values.length := by rw [← pairs.length_eq]; exact inside
          have held := pairs.get inside valueInside
          simp only [List.get_eq_getElem, atCell] at held
          exact Option.isSome_iff_exists.mpr ⟨known.values[index], held⟩

omit [DecidableEq Value] in
theorem readback_extends {codec : Codec Value} {names : Inventory String} {before after : Subst}
    (extended : after.lookupExtends before) : GenericJoinRegions.Extends (readback codec names before) (readback codec names after) := by
  intro slot value found
  obtain ⟨atom, lookup, decoded⟩ := Option.bind_eq_some_iff.mp found
  simp only [readback, extended (names.reify slot) atom lookup, Option.bind_some, decoded]

theorem covered_tail {codec : Codec Value} {names : Inventory String}
    (query : Query codec names) (queries : List (Query codec names)) (domain : Finset Value)
    (rows : List Atom) (bindings after : Subst)
    (ready : rows.all (rowReady query.pattern domain) = true) (bound : BindingsInDomain codec names domain bindings)
    (covered : Covered (query :: queries) bindings) (chosen : after ∈ choices bindings query.source rows) : Covered queries after := by
  obtain ⟨atom, present, matched⟩ := (choices_member bindings query.source rows after).mp chosen
  have extension := readback_extends (codec := codec) (names := names) (matchValue_lookup_extends matched)
  intro slot
  rcases covered slot with old | ⟨selected, member, used⟩
  · obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp old
    exact Or.inl (Option.isSome_iff_exists.mpr ⟨value, extension slot value found⟩)
  · rcases List.mem_cons.mp member with same | member
    · subst selected
      exact Or.inl (matching_binds_cells query.pattern domain atom bindings after
        (List.all_eq_true.mp ready atom present) bound matched slot used)
    · exact Or.inr ⟨selected, member, used⟩

def DataHead {codec : Codec Value} {names : Inventory String} (head : FlatQueryOutputDomain.Head codec names) : Prop :=
  head.2.head ≠ "=" ∧ head.2.head ≠ ":"

omit [DecidableEq Value] in
theorem encoded_data {codec : Codec Value} {names : Inventory String} (head : FlatQueryOutputDomain.Head codec names)
    (data : DataHead head) (values : List Value) : GuardedInsertionSource.dataRow (row codec head.2.head values) = true := by
  have ground : isGroundAtom.isGroundList (values.map codec.encode) = true := by
    induction values with
    | nil => rfl
    | cons value values ih => simp [isGroundAtom.isGroundList, ClosedQueryAdmission.literal_ground (codec.literal value), ih]
  simp [GuardedInsertionSource.dataRow, row, data.1, data.2, isGroundAtom, isGroundAtom.isGroundList, ground]

omit [DecidableEq Value] in
theorem emit_complete {codec : Codec Value} {names : Inventory String} (head : FlatQueryOutputDomain.Head codec names)
    (data : DataHead head) (target : Handle) (bindings : Subst) (before : Effects.State) (rows : List Atom)
    (total : ∀ slot, ∃ value, readback codec names bindings slot = some value)
    (snapshot : before.read target = some rows) : ∃ after answers, emit head target bindings before = some (after, answers) := by
  obtain ⟨values, rendered⟩ := ConjunctiveOutputDomain.instantiate_total _ total head.2.cells
  obtain ⟨after, changed, inserted⟩ := FreshInsertionSource.update_exists snapshot (row codec head.2.head values)
  exact ⟨after, FreshInsertionSource.answers changed, by simp [emit, rendered, encoded_data head data values, inserted]⟩

theorem completed_access {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (footprint queries : List (Query codec names)) (within : ∀ query ∈ queries, query ∈ footprint)
    (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before after : Effects.State) (rows answers : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain footprint before)
    (snapshot : before.read target = some rows)
    (completed : run queries head target bindings before = some (after, answers)) : ∃ result, after.read target = some result := by
  have reference := run_refines domain footprint queries within head constants target bindings before after answers bound valid completed
  obtain ⟨result, reading, _⟩ := FreshNestedQuerySource.run_growth target head.1 (queries.map Query.leg)
    bindings before after answers rows snapshot reference
  exact ⟨result, reading⟩

private theorem traverse_complete (body : Body) (invariant : Effects.State → Prop) (captured : List Subst)
    (law : ∀ bindings ∈ captured, ∀ before, invariant before →
      ∃ after answers, body bindings before = some (after, answers) ∧ invariant after)
    (before : Effects.State) (collected : List Atom) (valid : invariant before) :
    ∃ after answers, traverse body captured (before, collected) = some (after, answers) := by
  induction captured generalizing before collected with
  | nil => exact ⟨before, collected, rfl⟩
  | cons bindings rest ih =>
      obtain ⟨next, firstAnswers, first, nextValid⟩ := law bindings List.mem_cons_self before valid
      obtain ⟨after, answers, later⟩ := ih (fun bound member => law bound (List.mem_cons_of_mem _ member))
        next (collected ++ firstAnswers) nextValid
      exact ⟨after, answers, by simpa only [EffectfulQuerySource.traverse, first, Option.bind_some] using later⟩

theorem run_complete {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (footprint queries : List (Query codec names)) (within : ∀ query ∈ queries, query ∈ footprint)
    (head : FlatQueryOutputDomain.Head codec names) (data : DataHead head)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before : Effects.State) (targetRows : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain footprint before)
    (covered : Covered queries bindings) (targetRead : before.read target = some targetRows) :
    ∃ after answers, run queries head target bindings before = some (after, answers) := by
  induction queries generalizing bindings before targetRows with
  | nil =>
      apply emit_complete head data target bindings before targetRows _ targetRead
      intro slot
      rcases covered slot with present | ⟨query, impossible, _⟩
      · exact Option.isSome_iff_exists.mp present
      · cases impossible
  | cons query queries ih =>
      obtain ⟨rows, snapshot, ready⟩ := valid query (within query List.mem_cons_self)
      have remaining : ∀ item ∈ queries, item ∈ footprint := fun item member => within item (List.mem_cons_of_mem _ member)
      let invariant := fun state => ViewsInDomain domain footprint state ∧ ∃ rows, state.read target = some rows
      obtain ⟨after, answers, computed⟩ := traverse_complete (run queries head target) invariant
        (choices bindings query.source rows) (fun selected member current currentValid => by
          have nextBound := choices_preserve query.pattern domain rows bindings selected ready bound member
          have nextCovered := covered_tail query queries domain rows bindings selected ready bound covered member
          obtain ⟨currentRows, currentRead⟩ := currentValid.2
          obtain ⟨next, values, returned⟩ := ih remaining selected current currentRows nextBound currentValid.1 nextCovered currentRead
          exact ⟨next, values, returned,
            run_preserves domain footprint queries remaining head constants target selected current next values nextBound currentValid.1 returned,
            completed_access domain footprint queries remaining head constants target selected current next currentRows values
              nextBound currentValid.1 currentRead returned⟩)
        before [] ⟨valid, targetRows, targetRead⟩
      exact ⟨after, answers, by simpa only [FiniteNestedQuerySource.run, List.map_cons, Query.leg, NestedQuerySource.run,
        snapshot, bind, Option.bind] using computed⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryCompletion
