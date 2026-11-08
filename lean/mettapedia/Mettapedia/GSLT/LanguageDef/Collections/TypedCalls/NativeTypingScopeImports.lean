import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeEdits

/-!
# Selective typing publication through ordered module dependencies

Physical source rows remain editable occurrence lists. The existing ordered
dependency store owns their typing projections, dependency ordering, reverse
notification index and lifetime generations. A data-only edit changes its
physical source without notifying typing readers; an edit whose old or new
row may affect typing publishes the new projection through that owner.

The invariant connecting physical rows to published projections is proved
through edits, import/link/unlink and retirement. It is not assumed at every
step. Existing validated-query and source-segment laws then transport to the
actual annotation/subtype observations. Dependency identities remain ordered;
equal payloads are not deduplicated.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeImports

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypingScopeCapture TypeScopeClosure

structure State (size : Nat) where
  sources : Fin size → NativeTypingScopeEdits.State
  publication : OrderedDependencyStore.Store Atom size

def Valid {size : Nat} (state : State size) : Prop :=
  ∀ source, (state.publication.members source).own = capture (state.sources source).view.entries

def initialState {size : Nat} (identity : Nat) (sources : Fin size → NativeTypingScopeEdits.State) : State size :=
  ⟨sources, OrderedDependencyStore.initial identity (fun source => capture (sources source).view.entries)⟩

theorem initialize_valid {size : Nat} (identity : Nat) (sources : Fin size → NativeTypingScopeEdits.State) :
    Valid (initialState identity sources) := fun _ => rfl

theorem initialize_observers {size : Nat} (identity : Nat)
    (sources : Fin size → NativeTypingScopeEdits.State) :
    OrderedDependencyStore.ObserverInvariant (initialState identity sources).publication :=
  OrderedDependencyStore.initial_observers identity _

inductive Action (size : Nat) where
  | edit (source : Fin size) (edit : NativeTypingScopeEdits.Edit)
  | link (reader source : Fin size)
  | unlink (reader source : Fin size)
  | importModule (reader source : Fin size)
  | retire (source : Fin size)

def nextSources {size : Nat} (state : State size) : Action size → Fin size → NativeTypingScopeEdits.State
  | .edit source edit => Function.update state.sources source (NativeTypingScopeEdits.step (state.sources source) edit)
  | .retire source => Function.update state.sources source (NativeTypingScopeEdits.publish (state.sources source) [] true true)
  | _ => state.sources

def commands {size : Nat} (state : State size) : Action size → List (OrderedDependencyStore.Action Atom size)
  | .edit source edit =>
      let after := NativeTypingScopeEdits.step (state.sources source) edit
      if after.typingRevision = (state.sources source).typingRevision then []
      else [.replace source (capture after.view.entries)]
  | .link reader source => [.link reader source]
  | .unlink reader source => [.unlink reader source]
  | .importModule reader source => [.importModule reader source]
  | .retire source => [.retire source]

def step {size : Nat} (state : State size) (action : Action size) : State size :=
  ⟨nextSources state action, OrderedDependencyStore.execute state.publication (commands state action)⟩

theorem topology_owns_unchanged {size : Nat} (store : OrderedDependencyStore.Store Atom size)
    (reader source member : Fin size) :
    ((OrderedDependencyStore.link store reader source).members member).own = (store.members member).own := by
  unfold OrderedDependencyStore.link
  split
  · rfl
  · exact OrderedDependencyStore.setDependencies_own store reader member _

theorem step_valid {size : Nat} (state : State size) (valid : Valid state) (action : Action size) :
    Valid (step state action) := by
  intro member
  cases action with
  | edit source edit =>
      simp only [step, commands]
      split
      next same =>
        simp only [OrderedDependencyStore.execute, nextSources]
        by_cases isSource : member = source
        · subst member
          simp only [Function.update_self]
          exact (valid source).trans (NativeTypingScopeEdits.step_same_typing_capture (state.sources source) edit same).symm
        · simpa [Function.update_of_ne isSource] using valid member
      next changed =>
        simp only [OrderedDependencyStore.execute, OrderedDependencyStore.step, OrderedDependencyStore.replaceOwn, nextSources]
        by_cases isSource : member = source
        · subst member
          simp [OrderedDependencyStore.contentUpdate]
        · simpa [OrderedDependencyStore.contentUpdate, Function.update_of_ne isSource, isSource] using valid member
  | link reader source =>
      simpa [step, commands, nextSources, OrderedDependencyStore.execute, OrderedDependencyStore.step,
        topology_owns_unchanged] using valid member
  | unlink reader source =>
      simpa [step, commands, nextSources, OrderedDependencyStore.execute, OrderedDependencyStore.step, OrderedDependencyStore.unlink,
        OrderedDependencyStore.setDependencies_own] using valid member
  | importModule reader source =>
      simpa [step, commands, nextSources, OrderedDependencyStore.execute, OrderedDependencyStore.step, OrderedDependencyStore.importModule,
        OrderedDependencyStore.setDependencies_own] using valid member
  | retire source =>
      by_cases isSource : member = source
      · subst member
        simp [step, commands, nextSources, OrderedDependencyStore.execute, OrderedDependencyStore.step, OrderedDependencyStore.retire,
          NativeTypingScopeEdits.publish, RevisionedStoreView.replaceRevision, capture]
      · simpa [step, commands, nextSources, OrderedDependencyStore.execute, OrderedDependencyStore.step, OrderedDependencyStore.retire,
          Function.update_of_ne isSource, isSource] using valid member

theorem step_observers {size : Nat} (state : State size)
    (observers : OrderedDependencyStore.ObserverInvariant state.publication) (action : Action size) :
    OrderedDependencyStore.ObserverInvariant (step state action).publication :=
  OrderedDependencyStore.execute_observers state.publication observers (commands state action)

def execute {size : Nat} (state : State size) : List (Action size) → State size
  | [] => state
  | action :: rest => execute (step state action) rest

def trace {size : Nat} (state : State size) : List (Action size) → List (OrderedDependencyStore.Action Atom size)
  | [] => []
  | action :: rest => commands state action ++ trace (step state action) rest

theorem owner_execute_append {size : Nat} (store : OrderedDependencyStore.Store Atom size)
    (first second : List (OrderedDependencyStore.Action Atom size)) :
    OrderedDependencyStore.execute store (first ++ second) = OrderedDependencyStore.execute (OrderedDependencyStore.execute store first) second := by
  induction first generalizing store with
  | nil => rfl
  | cons action rest ih => exact ih _

theorem execute_publication {size : Nat} (state : State size) (actions : List (Action size)) :
    (execute state actions).publication = OrderedDependencyStore.execute state.publication (trace state actions) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      simpa [execute, trace, owner_execute_append, step] using ih (step state action)

theorem execute_valid {size : Nat} (state : State size) (valid : Valid state)
    (actions : List (Action size)) : Valid (execute state actions) := by
  induction actions generalizing state with
  | nil => exact valid
  | cons action rest ih => exact ih _ (step_valid state valid action)

theorem execute_observers {size : Nat} (state : State size)
    (observers : OrderedDependencyStore.ObserverInvariant state.publication) (actions : List (Action size)) :
    OrderedDependencyStore.ObserverInvariant (execute state actions).publication := by
  rw [execute_publication]
  exact OrderedDependencyStore.execute_observers state.publication observers _

/-- Independent source collection: root rows, then imported members' own
rows in the recorded import order. No recursive double composition occurs. -/
def sourceRows {size : Nat} (state : State size) (reader : Fin size) : List Atom :=
  (state.sources reader).view.entries ++
    (state.publication.members reader).deps.flatMap fun source => (state.sources source).view.entries

theorem capture_flatMap {Id : Type} (rows : Id → List Atom) (ids : List Id) :
    capture (ids.flatMap rows) = ids.flatMap fun id => capture (rows id) := by
  induction ids with
  | nil => rfl
  | cons id ids ih => simp [capture, List.filter_append, List.flatMap_cons] at ih ⊢; rw [ih]

theorem query_eq_source_packet {size : Nat} (state : State size) (valid : Valid state)
    (reader : Fin size) : OrderedDependencyStore.query state.publication reader = capture (sourceRows state reader) := by
  rw [OrderedDependencyStore.query_eq_view]
  simp only [OrderedDependencyStore.view, sourceRows, capture, List.filter_append]
  rw [valid reader]
  congr 1
  change _ = capture ((state.publication.members reader).deps.flatMap fun source =>
    (state.sources source).view.entries)
  rw [capture_flatMap]
  apply List.flatMap_congr
  intro source _
  exact valid source

/-- Validated selective publication gives exact ordered dependency packets
through arbitrary removal, replacement, import and retirement histories. -/
theorem validated_packet {size : Nat} (state : State size) (valid : Valid state)
    (observers : OrderedDependencyStore.ObserverInvariant state.publication) (actions : List (Action size))
    (reader : Fin size)
    (accepted : OrderedDependencyStore.checkRead (execute state actions).publication
      (OrderedDependencyStore.readStamp state.publication reader) = true) :
    capture (sourceRows (execute state actions) reader) = capture (sourceRows state reader) := by
  rw [← query_eq_source_packet _ (execute_valid state valid actions), ← query_eq_source_packet state valid]
  rw [execute_publication] at accepted ⊢
  exact OrderedDependencyStore.validated_query state.publication observers (trace state actions) reader accepted

theorem validated_queries {size : Nat} (state : State size) (valid : Valid state)
    (observers : OrderedDependencyStore.ObserverInvariant state.publication) (actions : List (Action size))
    (reader : Fin size)
    (accepted : OrderedDependencyStore.checkRead (execute state actions).publication
      (OrderedDependencyStore.readStamp state.publication reader) = true)
    (subject input : Atom) (fresh : String) :
    getAnnotatedTypes ⟨sourceRows (execute state actions) reader⟩ subject =
      getAnnotatedTypes ⟨sourceRows state reader⟩ subject ∧
    subtypeQuery rawWorld input fresh (sourceRows (execute state actions) reader) =
      subtypeQuery rawWorld input fresh (sourceRows state reader) := by
  have packet := validated_packet state valid observers actions reader accepted
  constructor
  · rw [← annotations_capture, packet, annotations_capture]
  · rw [← subtypeQuery_capture, packet, subtypeQuery_capture]

/-- Source-local coordinates remain separate from importer notifications.
An importer's own row counter need not advance when an imported source edits. -/
theorem step_source_laws {size : Nat} (state : State size) (action : Action size)
    (source : Fin size) :
    let before := state.sources source
    let after := (step state action).sources source
    before.typingRevision ≤ after.typingRevision ∧
    before.prefixEpoch ≤ after.prefixEpoch ∧
    (after.typingRevision = before.typingRevision → capture after.view.entries = capture before.view.entries) ∧
    (after.prefixEpoch = before.prefixEpoch → before.view.entries <+: after.view.entries) := by
  have untouched (localState : NativeTypingScopeEdits.State) :
      localState.typingRevision ≤ localState.typingRevision ∧
      localState.prefixEpoch ≤ localState.prefixEpoch ∧
      (localState.typingRevision = localState.typingRevision →
        capture localState.view.entries = capture localState.view.entries) ∧
      (localState.prefixEpoch = localState.prefixEpoch → localState.view.entries <+: localState.view.entries) :=
    ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl, fun _ => List.prefix_refl _⟩
  cases action with
  | edit writer edit =>
      by_cases same : source = writer
      · subst source
        simpa [step, nextSources] using
          And.intro (NativeTypingScopeEdits.typingRevision_mono (state.sources writer) edit)
            (And.intro (NativeTypingScopeEdits.prefixEpoch_mono (state.sources writer) edit)
              (And.intro (NativeTypingScopeEdits.step_same_typing_capture (state.sources writer) edit)
                (NativeTypingScopeEdits.step_same_prefix_epoch (state.sources writer) edit)))
      · simp [step, nextSources, Function.update_of_ne same]
  | retire writer =>
      by_cases same : source = writer
      · subst source
        simp [step, nextSources, NativeTypingScopeEdits.publish]
      · simp [step, nextSources, Function.update_of_ne same]
  | link _ _ => exact untouched _
  | unlink _ _ => exact untouched _
  | importModule _ _ => exact untouched _

theorem execute_source_laws {size : Nat} (state : State size) (actions : List (Action size))
    (source : Fin size) :
    let before := state.sources source
    let after := (execute state actions).sources source
    before.typingRevision ≤ after.typingRevision ∧
    before.prefixEpoch ≤ after.prefixEpoch ∧
    (after.typingRevision = before.typingRevision → capture after.view.entries = capture before.view.entries) ∧
    (after.prefixEpoch = before.prefixEpoch → before.view.entries <+: after.view.entries) := by
  induction actions generalizing state with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl, fun _ => List.prefix_refl _⟩
  | cons action rest ih =>
      have first := step_source_laws state action source
      have later := ih (step state action)
      refine ⟨first.1.trans later.1, first.2.1.trans later.2.1, ?_, ?_⟩
      · intro same
        have firstEq : ((step state action).sources source).typingRevision =
            (state.sources source).typingRevision := by dsimp only [execute] at same; omega
        have laterEq : ((execute (step state action) rest).sources source).typingRevision =
            ((step state action).sources source).typingRevision := by simpa [execute, firstEq] using same
        exact (later.2.2.1 laterEq).trans (first.2.2.1 firstEq)
      · intro same
        have firstEq : ((step state action).sources source).prefixEpoch =
            (state.sources source).prefixEpoch := by dsimp only [execute] at same; omega
        have laterEq : ((execute (step state action) rest).sources source).prefixEpoch =
            ((step state action).sources source).prefixEpoch := by simpa [execute, firstEq] using same
        exact (first.2.2.2 firstEq).trans (later.2.2.2 laterEq)

def dependencyStamp {size : Nat} (state : State size) (reader : Fin size) : List (Fin size × Nat) :=
  (state.publication.members reader).deps.map fun source => (source, (state.sources source).typingRevision)

def dependencyRows {size : Nat} (state : State size) (reader : Fin size) : List Atom :=
  (state.publication.members reader).deps.flatMap fun source => (state.sources source).view.entries

/-- The ordered dependency stamp permits source-local appends beyond an
overlay ceiling without treating those appends as changes to imported rows. -/
theorem dependency_stamp_packet {size : Nat} (state : State size) (actions : List (Action size))
    (reader : Fin size) (same : dependencyStamp (execute state actions) reader = dependencyStamp state reader) :
    capture (dependencyRows (execute state actions) reader) = capture (dependencyRows state reader) := by
  have ids : ((execute state actions).publication.members reader).deps =
      (state.publication.members reader).deps := by
    simpa [dependencyStamp, List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) same
  have revisions := same
  simp only [dependencyStamp, ids] at revisions
  have each := List.map_inj_left.mp revisions
  simp only [dependencyRows]
  rw [ids, capture_flatMap, capture_flatMap]
  apply List.flatMap_congr
  intro source member
  have sameRevision := congrArg Prod.snd (each source member)
  exact (execute_source_laws state actions source).2.2.1 sameRevision

namespace Controls

def row : Atom := NativeTypingScopeEdits.Controls.row
def note : Atom := NativeTypingScopeEdits.Controls.note
def locals : Fin 3 → NativeTypingScopeEdits.State := fun id =>
  ⟨⟨id.val, 0, if id = 2 then [row, row] else []⟩, 0, 0⟩

def initial : State 3 :=
  ⟨locals, OrderedDependencyStore.initial 19 (fun source => capture (locals source).view.entries)⟩

theorem initial_valid : Valid initial := fun _ => rfl

def imported : State 3 := step initial (.importModule 0 2)

theorem duplicate_import_rows_preserved : sourceRows imported 0 = [row, row] := by decide

theorem removing_one_imported_duplicate_expires_stamp :
    sourceRows (step imported (.edit 2 (.erase 0))) 0 = [row] ∧
    OrderedDependencyStore.checkRead (step imported (.edit 2 (.erase 0))).publication
      (OrderedDependencyStore.readStamp imported.publication 0) = false := by decide

theorem data_only_import_edit_keeps_stamp :
    OrderedDependencyStore.checkRead (step imported (.edit 2 (.append note))).publication
      (OrderedDependencyStore.readStamp imported.publication 0) = true ∧
    capture (sourceRows (step imported (.edit 2 (.append note))) 0) = capture (sourceRows imported 0) := by decide

theorem unlink_and_relink_does_not_revive_stamp :
    let after := execute imported [.unlink 0 2, .link 0 2]
    sourceRows after 0 = sourceRows imported 0 ∧
    OrderedDependencyStore.checkRead after.publication
      (OrderedDependencyStore.readStamp imported.publication 0) = false := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeImports
