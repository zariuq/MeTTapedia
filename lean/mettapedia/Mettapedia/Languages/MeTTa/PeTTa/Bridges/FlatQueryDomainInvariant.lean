import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryOutputDomain
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NestedQuerySource

/-!
# Fixed value domains across mutable query reads

Each current read is checked with the existing row classifier. A new row may
change query answers while preserving their value domain. No old query view
is reused merely because this invariant survives a write.

The row classifier refuses relevant open or unsupported values. This is the
plain directional-query profile, not a replacement for stored-ID unification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryDomainInvariant

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveBindingDomain ConjunctiveRowMatching
open FlatQueryRowCodec FlatQueryPatternExtraction FlatQueryRelationCompilation
open NamedSpaces SpaceSemantics EffectfulQuerySource

variable {Value : Type} [DecidableEq Value]

def rowReady {codec : Codec Value} {names : Inventory String} {source : Atom}
    (pattern : Compiled codec names source) (domain : Finset Value) (atom : Atom) : Bool :=
  match classifyRow pattern atom with
  | none => false
  | some (.irrelevant _) => true
  | some (.known known) => known.values.all fun value => decide (value ∈ domain)

theorem encoded_row_ready {codec : Codec Value} {names : Inventory String} {source : Atom}
    (pattern : Compiled codec names source) (domain : Finset Value) (head : String) (values : List Value)
    (inside : ∀ value ∈ values, value ∈ domain) : rowReady pattern domain (row codec head values) = true := by
  have all : values.all (fun value => decide (value ∈ domain)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using inside
  by_cases same : head = pattern.head
  · subst head
    by_cases arity : values.length = pattern.cells.length
    · let known : KnownRow pattern (row codec pattern.head values) := ⟨values, arity, rfl⟩
      have classified : classifyRow pattern (row codec pattern.head values) = some (.known known) := by
        simp only [row, classifyRow]
        split_ifs with headEq arityEq
        · split
          next missing =>
            have decoded := FlatQueryOutputDomain.decodeValues_roundtrip codec values
            rw [missing] at decoded
            cases decoded
          next actual decoded =>
            have same : actual = values := Option.some.inj (decoded.symm.trans (FlatQueryOutputDomain.decodeValues_roundtrip codec values))
            subst actual
            rfl
        · exact False.elim (arityEq (by simpa only [List.length_map] using arity))
        all_goals exact False.elim (headEq True.intro)
      simpa only [rowReady, classified] using all
    · simp [rowReady, row, classifyRow, arity]
  · simp [rowReady, row, classifyRow, same]

theorem catalogue_row_ready {codec : Codec Value} {names : Inventory String} {source : Atom}
    (pattern : Compiled codec names source) (domain : Finset Value) (shapes : Finset (String × Nat))
    (atom : Atom) (inside : atom ∈ FlatQueryOutputDomain.catalogue codec domain shapes) :
    rowReady pattern domain atom = true := by
  obtain ⟨⟨head, values⟩, member, rfl⟩ := Finset.mem_image.mp inside
  exact encoded_row_ready pattern domain head values
    ((ConjunctiveOutputDomain.mem_catalogue domain shapes head values).mp member).2

def BindingsInDomain (codec : Codec Value) (names : Inventory String) (domain : Finset Value) (bindings : Subst) : Prop :=
  Represents codec names (readback codec names bindings) bindings ∧ InDomain domain (readback codec names bindings)

def validateBindings (codec : Codec Value) (names : Inventory String) (domain : Finset Value) (bindings : Subst) : Bool :=
  decide (Represents codec names (readback codec names bindings) bindings) &&
    (List.finRange names.keys.length).all (fun slot => (readback codec names bindings slot).all (fun value => decide (value ∈ domain)))

theorem validateBindings_iff (codec : Codec Value) (names : Inventory String) (domain : Finset Value) (bindings : Subst) :
    validateBindings codec names domain bindings = true ↔ BindingsInDomain codec names domain bindings := by
  simp only [validateBindings, Bool.and_eq_true, decide_eq_true_eq, BindingsInDomain,
    List.all_eq_true, List.mem_finRange, true_implies]
  apply and_congr_right
  intro _
  constructor
  · intro checked slot value found
    simpa [found] using checked slot
  · intro bounded slot
    cases found : readback codec names bindings slot with
    | none => simp
    | some value => simp [bounded slot value found]

theorem matching_preserves {codec : Codec Value} {names : Inventory String} {source : Atom}
    (pattern : Compiled codec names source) (domain : Finset Value) (atom : Atom)
    (bindings after : Subst) (ready : rowReady pattern domain atom = true)
    (initial : BindingsInDomain codec names domain bindings)
    (matched : matchValue bindings source atom = some after) : BindingsInDomain codec names domain after := by
  cases classified : classifyRow pattern atom with
  | none => simp [rowReady, classified] at ready
  | some result =>
      cases result with
      | irrelevant absent => rw [absent bindings] at matched; cases matched
      | known known =>
          have all : ∀ value ∈ known.values, value ∈ domain := by
            simpa [rowReady, classified] using ready
          have projected := known_row_exact pattern known (readback codec names bindings) bindings initial.1
          rw [matched] at projected
          refine ⟨known_row_preserves pattern known _ bindings after initial.1 matched, ?_⟩
          exact bindValues_domain domain initial.2 all projected.symm

theorem choices_preserve {codec : Codec Value} {names : Inventory String} {source : Atom}
    (pattern : Compiled codec names source) (domain : Finset Value) (rows : List Atom)
    (bindings after : Subst) (ready : rows.all (rowReady pattern domain) = true)
    (initial : BindingsInDomain codec names domain bindings)
    (chosen : after ∈ choices bindings source rows) : BindingsInDomain codec names domain after := by
  obtain ⟨atom, present, matched⟩ := (choices_member bindings source rows after).mp chosen
  exact matching_preserves pattern domain atom bindings after (List.all_eq_true.mp ready atom present) initial matched

structure Query (codec : Codec Value) (names : Inventory String) where
  handle : Handle
  source : Atom
  pattern : Compiled codec names source
  notConjunction : pattern.head ≠ ","

def Query.leg {codec : Codec Value} {names : Inventory String} (query : Query codec names) : NestedQuerySource.Leg :=
  (query.handle, query.source)

def compileQuery (codec : Codec Value) (names : Inventory String) (handle : Handle) (source : Atom) :
    Option (Query codec names) := do
  let pattern ← compilePattern codec names source
  if active : pattern.head = "," then none else some ⟨handle, source, pattern, active⟩

def ViewsInDomain {codec : Codec Value} {names : Inventory String}
    (domain : Finset Value) (queries : List (Query codec names)) (state : Effects.State) : Prop :=
  ∀ query ∈ queries, ∃ rows, state.read query.handle = some rows ∧ rows.all (rowReady query.pattern domain) = true

def validateViews {codec : Codec Value} {names : Inventory String}
    (domain : Finset Value) (queries : List (Query codec names)) (state : Effects.State) : Bool :=
  queries.all fun query => match state.read query.handle with
    | none => false
    | some rows => rows.all (rowReady query.pattern domain)

theorem validateViews_iff {codec : Codec Value} {names : Inventory String}
    (domain : Finset Value) (queries : List (Query codec names)) (state : Effects.State) :
    validateViews domain queries state = true ↔ ViewsInDomain domain queries state := by
  simp only [validateViews, List.all_eq_true, ViewsInDomain]
  apply forall_congr'
  intro query
  apply imp_congr_right
  intro _
  cases state.read query.handle <;> simp

theorem insert_preserves {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (shapes : Finset (String × Nat))
    (before after : Effects.State) (target : Handle) (atom : Atom)
    (valid : ViewsInDomain domain queries before) (inside : atom ∈ FlatQueryOutputDomain.catalogue codec domain shapes)
    (inserted : Effects.insert before target atom = some after) : ViewsInDomain domain queries after := by
  intro query present
  obtain ⟨rows, reading, ready⟩ := valid query present
  by_cases same : query.handle = target
  · obtain ⟨old, beforeRead, afterRead⟩ := Effects.insert_reads_back inserted
    have equalRows : old = rows := Option.some.inj (beforeRead.symm.trans (by simpa [same] using reading))
    subst old
    refine ⟨rows ++ [atom], by simpa [same] using afterRead, ?_⟩
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, ready,
      catalogue_row_ready query.pattern domain shapes atom inside]
  · exact ⟨rows, (Effects.insert_read_other inserted same).trans reading, ready⟩

theorem fresh_preserves {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (shapes : Finset (String × Nat))
    (before after : Effects.State) (target : Handle) (atom : Atom) (changed : Bool)
    (valid : ViewsInDomain domain queries before) (inside : atom ∈ FlatQueryOutputDomain.catalogue codec domain shapes)
    (updated : FreshInsertionSource.update before target atom = some (after, changed)) : ViewsInDomain domain queries after := by
  rcases GuardedInsertionSource.update_cases (FreshInsertionSource.unchanged_update updated) with same | inserted
  · subst after; exact valid
  · exact insert_preserves domain queries shapes before after target atom valid inside inserted

private theorem traverse_preserves (body : Body) (invariant : Effects.State → Prop) (captured : List Subst)
    (law : ∀ bindings ∈ captured, ∀ before after answers, invariant before →
      body bindings before = some (after, answers) → invariant after)
    (before after : Effects.State) (collected answers : List Atom) (valid : invariant before)
    (completed : traverse body captured (before, collected) = some (after, answers)) : invariant after := by
  induction captured generalizing before collected with
  | nil =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj completed)
      exact valid
  | cons bindings rest ih =>
      obtain ⟨next, first, later⟩ := Option.bind_eq_some_iff.mp completed
      exact ih (fun bound member => law bound (List.mem_cons_of_mem _ member)) next.1 (collected ++ next.2)
        (law bindings List.mem_cons_self before next.1 next.2 valid first) later

/-- Actual current-state reads preserve binding domains. The body may grow
those same spaces provided it preserves their row-domain invariant. -/
theorem nested_preserves {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (footprint : List (Query codec names)) (body : Body)
    (leaf : ∀ bindings before after answers, BindingsInDomain codec names domain bindings →
      ViewsInDomain domain footprint before → body bindings before = some (after, answers) →
      ViewsInDomain domain footprint after)
    (queries : List (Query codec names)) (within : ∀ query ∈ queries, query ∈ footprint)
    (bindings : Subst) (before after : Effects.State) (answers : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain footprint before)
    (completed : NestedQuerySource.run body (queries.map Query.leg) bindings before = some (after, answers)) :
    ViewsInDomain domain footprint after := by
  induction queries generalizing bindings before after answers with
  | nil => exact leaf bindings before after answers bound valid completed
  | cons query queries ih =>
      obtain ⟨rows, snapshot, traversed⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨old, oldRead, ready⟩ := valid query (within query List.mem_cons_self)
      have equalRows : old = rows := Option.some.inj (oldRead.symm.trans snapshot)
      subst old
      apply traverse_preserves _ (ViewsInDomain domain footprint) (choices bindings query.source rows) _
        before after [] answers valid traversed
      intro selected member current next values currentValid returned
      exact ih (fun item present => within item (List.mem_cons_of_mem _ present)) selected current next values
        (choices_preserve query.pattern domain rows bindings selected ready bound member) currentValid returned

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryDomainInvariant
