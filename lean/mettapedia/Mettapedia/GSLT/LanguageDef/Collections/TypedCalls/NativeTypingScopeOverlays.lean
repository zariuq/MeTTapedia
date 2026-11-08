import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeImports

/-!
# Typing packets through nested overlay and import histories

An overlay transforms the root's own occurrence sequence, then appends the
ordered imported source segments once. A raw prefix-rewrite coordinate protects
inherited positions; a typing coordinate protects an unlayered own segment.
Imported segments retain their ordered source identities and typing revisions.
Layer publication has a separate monotone coordinate, preventing ABA reuse.

The theorem follows the actual mixed source-edit/import and layer-publication
algorithms. It admits an append beyond an inherited ceiling without invalidating
that prefix, while rejecting a data-only deletion that shifts masked positions.
The token is an explicit semantic dependency certificate. Mapping the native
compressed owner/import epochs to this certificate remains a representation
obligation; identity and counter rollover cannot be omitted from that mapping.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeOverlays

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypingScopeCapture TypeScopeClosure

abbrev Layer := OrderedDependencyOverlay.Layer Atom

def ownClock (layers : List Layer) (source : NativeTypingScopeEdits.State) : Nat :=
  if layers.isEmpty then source.typingRevision else source.prefixEpoch

def layeredRows {size : Nat} (source : NativeTypingScopeImports.State size)
    (reader : Fin size) (layers : List Layer) : List Atom :=
  layers.foldl (fun rows layer => layer.view rows) (source.sources reader).view.entries ++
    NativeTypingScopeImports.dependencyRows source reader

def CeilingValid {size : Nat} (source : NativeTypingScopeImports.State size)
    (reader : Fin size) : List Layer → Prop
  | [] => True
  | first :: _ => first.ceiling ≤ (source.sources reader).view.entries.length

theorem source_history_packet {size : Nat} (source : NativeTypingScopeImports.State size)
    (actions : List (NativeTypingScopeImports.Action size)) (reader : Fin size) (layers : List Layer)
    (bounded : CeilingValid source reader layers)
    (sameOwn : ownClock layers ((NativeTypingScopeImports.execute source actions).sources reader) =
      ownClock layers (source.sources reader))
    (sameImports : NativeTypingScopeImports.dependencyStamp (NativeTypingScopeImports.execute source actions) reader =
      NativeTypingScopeImports.dependencyStamp source reader) :
    capture (layeredRows (NativeTypingScopeImports.execute source actions) reader layers) =
      capture (layeredRows source reader layers) := by
  have imports := NativeTypingScopeImports.dependency_stamp_packet source actions reader sameImports
  have localLaws := NativeTypingScopeImports.execute_source_laws source actions reader
  simp only [layeredRows, capture, List.filter_append]
  change _ ++ capture (NativeTypingScopeImports.dependencyRows _ reader) =
    _ ++ capture (NativeTypingScopeImports.dependencyRows _ reader)
  rw [imports]
  congr 1
  cases layers with
  | nil => exact localLaws.2.2.1 (by simpa [ownClock] using sameOwn)
  | cons first rest =>
      have prefixEq : ((NativeTypingScopeImports.execute source actions).sources reader).prefixEpoch =
          (source.sources reader).prefixEpoch := by simpa [ownClock] using sameOwn
      have firstSame := NativeTypingScopeEdits.layer_view_of_prefix first
        (source.sources reader).view.entries
        ((NativeTypingScopeImports.execute source actions).sources reader).view.entries
        (localLaws.2.2.2 prefixEq) bounded
      simp only [List.foldl_cons, firstSame]

structure State (size : Nat) where
  source : NativeTypingScopeImports.State size
  reader : Fin size
  layers : List Layer
  identity : Nat
  generation : Nat
  publication : Nat

inductive Action (size : Nat) where
  | source (action : NativeTypingScopeImports.Action size)
  | publish (layers : List Layer)
  | retire

def step {size : Nat} (state : State size) : Action size → State size
  | .source action => { state with source := NativeTypingScopeImports.step state.source action }
  | .publish layers => { state with layers := layers, publication := state.publication + 1 }
  | .retire => { state with layers := [], generation := state.generation + 1, publication := state.publication + 1 }

def execute {size : Nat} (state : State size) : List (Action size) → State size
  | [] => state
  | action :: rest => execute (step state action) rest

def sourceActions {size : Nat} (actions : List (Action size)) : List (NativeTypingScopeImports.Action size) :=
  actions.filterMap fun action => match action with | .source inner => some inner | _ => none

theorem execute_source {size : Nat} (state : State size) (actions : List (Action size)) :
    (execute state actions).source = NativeTypingScopeImports.execute state.source (sourceActions actions) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      have later := ih (step state action)
      cases action <;> simpa [execute, step, sourceActions,
        List.filterMap_cons, NativeTypingScopeImports.execute] using later

theorem execute_reader {size : Nat} (state : State size) (actions : List (Action size)) :
    (execute state actions).reader = state.reader := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      have later := ih (step state action)
      cases action <;> simpa [execute, step] using later

theorem step_publication_mono {size : Nat} (state : State size) (action : Action size) :
    state.publication ≤ (step state action).publication := by cases action <;> simp [step]

theorem execute_publication_mono {size : Nat} (state : State size) (actions : List (Action size)) :
    state.publication ≤ (execute state actions).publication := by
  induction actions generalizing state with
  | nil => exact Nat.le_refl _
  | cons action rest ih => exact (step_publication_mono state action).trans (ih _)

theorem execute_same_publication_layers {size : Nat} (state : State size) (actions : List (Action size))
    (same : (execute state actions).publication = state.publication) :
    (execute state actions).layers = state.layers := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      have first := step_publication_mono state action
      have later := execute_publication_mono (step state action) rest
      have firstEq : (step state action).publication = state.publication := by
        simp only [execute] at same
        omega
      cases action with
      | source inner => exact ih _ (by simpa [execute, step] using same)
      | publish layers => simp [step] at firstEq
      | retire => simp [step] at firstEq

structure Token (size : Nat) where
  identity : Nat
  generation : Nat
  reader : Fin size
  publication : Nat
  own : Nat
  imports : List (Fin size × Nat)
  deriving DecidableEq

def token {size : Nat} (state : State size) : Token size :=
  ⟨state.identity, state.generation, state.reader, state.publication,
    ownClock state.layers (state.source.sources state.reader),
    NativeTypingScopeImports.dependencyStamp state.source state.reader⟩

def check {size : Nat} (state : State size) (saved : Token size) : Bool := decide (token state = saved)

def packet {size : Nat} (state : State size) : List Atom :=
  capture (layeredRows state.source state.reader state.layers)

theorem validated_packet {size : Nat} (state : State size) (actions : List (Action size))
    (bounded : CeilingValid state.source state.reader state.layers)
    (accepted : check (execute state actions) (token state) = true) :
    packet (execute state actions) = packet state := by
  have equal : token (execute state actions) = token state := of_decide_eq_true accepted
  have publicationEq := congrArg Token.publication equal
  have layersEq := execute_same_publication_layers state actions publicationEq
  have ownEq := congrArg Token.own equal
  have importsEq := congrArg Token.imports equal
  simp only [token, layersEq, execute_source, execute_reader] at ownEq importsEq
  simp only [packet, execute_source, execute_reader, layersEq]
  exact source_history_packet state.source (sourceActions actions) state.reader state.layers bounded ownEq importsEq

theorem validated_queries {size : Nat} (state : State size) (actions : List (Action size))
    (bounded : CeilingValid state.source state.reader state.layers)
    (accepted : check (execute state actions) (token state) = true)
    (subject input : Atom) (fresh : String) :
    getAnnotatedTypes ⟨layeredRows (execute state actions).source (execute state actions).reader
        (execute state actions).layers⟩ subject =
      getAnnotatedTypes ⟨layeredRows state.source state.reader state.layers⟩ subject ∧
    subtypeQuery rawWorld input fresh (layeredRows (execute state actions).source
        (execute state actions).reader (execute state actions).layers) =
      subtypeQuery rawWorld input fresh (layeredRows state.source state.reader state.layers) := by
  have same := validated_packet state actions bounded accepted
  constructor
  · rw [← annotations_capture subject (layeredRows (execute state actions).source
        (execute state actions).reader (execute state actions).layers),
      ← annotations_capture subject (layeredRows state.source state.reader state.layers)]
    exact congrArg (fun rows => getAnnotatedTypes ⟨rows⟩ subject) same
  · rw [← subtypeQuery_capture input fresh (layeredRows (execute state actions).source
        (execute state actions).reader (execute state actions).layers),
      ← subtypeQuery_capture input fresh (layeredRows state.source state.reader state.layers)]
    exact congrArg (subtypeQuery rawWorld input fresh) same

namespace Controls

def row : Atom := NativeTypingScopeEdits.Controls.row
def note : Atom := NativeTypingScopeEdits.Controls.note
def locals : Fin 3 → NativeTypingScopeEdits.State := fun id =>
  ⟨⟨id.val, 0, if id = 0 then [note, row] else if id = 2 then [row, row] else []⟩, 0, 0⟩

def base : NativeTypingScopeImports.State 3 :=
  NativeTypingScopeImports.step
    ⟨locals, OrderedDependencyStore.initial 19 (fun source => capture (locals source).view.entries)⟩
    (.importModule 0 2)

def nested : State 3 := ⟨base, 0, [⟨2, {0}, [row]⟩, ⟨2, ∅, [row]⟩], 41, 0, 0⟩

theorem nested_duplicates_and_imports : packet nested = [row, row, row, row, row] := by decide

theorem inherited_typed_append_keeps_token :
    let after := step nested (.source (.edit 0 (.append row)))
    check after (token nested) = true ∧ packet after = packet nested := by decide

theorem data_only_deletion_invalidates_overlay :
    let after := step nested (.source (.edit 0 (.erase 0)))
    (after.source.sources 0).typingRevision = (nested.source.sources 0).typingRevision ∧
    check after (token nested) = false ∧ packet after ≠ packet nested := by decide

theorem imported_removal_invalidates_overlay :
    check (step nested (.source (.edit 2 (.erase 0)))) (token nested) = false := by decide

theorem restored_layers_do_not_revalidate :
    let after := execute nested [.publish [], .publish nested.layers]
    packet after = packet nested ∧ check after (token nested) = false := by decide

theorem unbounded_initial_ceiling_is_not_certified :
    let bad := { nested with layers := [⟨3, ∅, []⟩] }
    let after := step bad (.source (.edit 0 (.append row)))
    ¬ CeilingValid bad.source bad.reader bad.layers ∧
    check after (token bad) = true ∧ packet after ≠ packet bad := by
  dsimp only
  unfold CeilingValid
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeOverlays
