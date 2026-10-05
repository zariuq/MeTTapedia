import Mettapedia.GSLT.Distinction.HistoryCoverage

/-!
# One context category for the history grammar

`HistoryCoverage` proves that parallel contexts and renamings of nodes commute
with the history grammar, each as its own `SpanTransport.Congruent` instance,
and `HistoryContextualReadout` reads the grammar over contexts whose arrows are
event paths.  This module builds one structure that carries all three.

* **Firing by splitting** (`Splits`, `Moves`, `splitGSLT`).  An event fires on
  a configuration that is what the event consumes, what it reads, and a rest;
  the result replaces the consumed nodes by the produced ones.  A two-sided
  entry reads an event forward or backward.  This presentation uses only
  multiset addition and renaming, and no erasure or subtraction.
* **History contexts** (`Context`, `Context.apply`, `Context.andThen`).  A
  context renames the nodes of a configuration by a renaming that commutes with
  the grammar, then places an authored frame beside it.  Contexts compose, with
  identity and associativity (`Context.one_andThen`, `Context.andThen_one`,
  `Context.andThen_assoc`), and act on configurations, events, entries and
  scripts (`Context.apply_andThen`, `Context.event_andThen`,
  `Context.script_andThen`).  Renaming commutes with parallel addition
  (`Context.frame_andThen_rename`, `Context.apply_frame_rename`), and every
  context is a renaming followed by a frame (`Context.normal_form`).
* **Substitution commutes with steps** (`splits_apply`, `moves_apply`,
  `path_apply`).
* **The whole reduction span** (`eventSpan`, `contextSpan`,
  `contextSpan_one`, `contextSpan_andThen`).  Contexts act on the labelled
  reduction span by span maps, and the action is functorial as an equality of
  span maps: every labelled step keeps its event, renamed, and both endpoints.
  The span is covered by its own events (`eventShadow_sourceOccurrenceLifts`,
  `eventShadow_targetOccurrenceLifts`).  The same holds for the two-sided span
  of forward and backward entries (`entrySpan`, `contextEntrySpan_one`,
  `contextEntrySpan_andThen`), and contexts commute with reading a step forward
  (`forwardEntry_context`).
* **The context category** (`World`, `Arrow`, `category`).  An arrow is a
  two-sided event script together with a history context, and composition is
  the semidirect product: a later context renames the earlier script.  Pure
  scripts are the event-path contexts (`scriptArrow_comp`), pure contexts embed
  functorially (`contextArrow_andThen`), a context slides past a script by
  renaming it (`interchange`), and every arrow is a context followed by a script
  (`arrow_normal_form`).
* **The four lifting laws of a context** (`context_four_laws`,
  `context_four_occurrence_laws`).  The two forth laws always hold.  The source
  back law holds exactly when the frame is empty, the target back law exactly
  when the frame is empty and the renaming is onto, for endpoint lifting and
  for occurrence lifting alike.  Without a listing, a renaming with a left
  inverse and no frame still lifts every source occurrence
  (`sourceOccurrenceLifts_of_leftInverse`), whether or not it is onto.  So the
  future diamond commutes with a context
  exactly when its frame is empty (`diamond_natural_iff`), and the predecessor
  box exactly when it is moreover a bijection (`box_natural_iff`).

**Choice.**  Every declaration of this module is free of `Classical.choice`:
it uses multiset addition, renaming and cardinality, list operations, and a
partial inverse of a renaming searched along a listing of the nodes.  The
equivalence of `Splits` with the firing relation of `HistoryGrammar`, which
uses multiset erasure and subtraction, is the host profile
`HistoryContextHostProfile`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryContextCategory

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner (Direction)
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver (Listing)
open Mettapedia.GSLT.Distinction.HistoryObserverControls (relabel)
open Mettapedia.GSLT.Distinction.HistoryCoverage (Renaming)
open Mettapedia.GSLT.Distinction.HistoryIndependence (consumed read produced)
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## Multiset lemmas without choice -/

section Multisets

variable {α β : Type}

theorem add_left_cancel_free {prefix_ left right : Multiset α}
    (same : prefix_ + left = prefix_ + right) : left = right := by
  induction prefix_ using Multiset.induction_on with
  | empty => rwa [Multiset.zero_add, Multiset.zero_add] at same
  | cons x rest inductionHypothesis =>
      rw [Multiset.cons_add, Multiset.cons_add] at same
      exact inductionHypothesis ((Multiset.cons_inj_right x).mp same)

theorem add_right_cancel_free {suffix left right : Multiset α}
    (same : left + suffix = right + suffix) : left = right := by
  rw [Multiset.add_comm left, Multiset.add_comm right] at same
  exact add_left_cancel_free same

theorem coe_cons_eq (x : α) (rest : List α) : ((x :: rest : List α) : Multiset α) = {x} + ↑rest := by
  rw [Multiset.singleton_add]
  rfl

end Multisets

variable {V : Type} (G : Grammar V)

/-! ## Firing by splitting -/

/-- **An event fires by splitting**: the configuration is what the event
consumes, what it reads and a rest, and the result is what it produces, what it
read and the same rest. -/
def Splits (event : Event V) (source target : Multiset V) : Prop :=
  ∃ rest, source = consumed event + read event + rest ∧ target = produced G event + read event + rest

/-- A two-sided entry: an event read forward or backward. -/
abbrev Entry (V : Type) := Direction × Event V

/-- **A two-sided move**: a forward entry fires its event, a backward entry
undoes it. -/
def Moves : Entry V → Multiset V → Multiset V → Prop
  | (.forward, event), source, target => Splits G event source target
  | (.backward, event), source, target => Splits G event target source

/-- Every event consumes or reads a node. -/
theorem need_pos (event : Event V) : 0 < Multiset.card (consumed event + read event) := by
  cases event with
  | evolve x =>
      rw [Multiset.card_add]
      change 0 < Multiset.card (x ::ₘ 0) + Multiset.card (0 : Multiset V)
      rw [Multiset.card_cons]
      omega
  | fork x =>
      rw [Multiset.card_add]
      change 0 < Multiset.card (0 : Multiset V) + Multiset.card (x ::ₘ 0)
      rw [Multiset.card_cons]
      omega
  | merge x y =>
      rw [Multiset.card_add]
      change 0 < Multiset.card (x ::ₘ y ::ₘ 0) + Multiset.card (0 : Multiset V)
      rw [Multiset.card_cons]
      omega
  | erase x =>
      rw [Multiset.card_add]
      change 0 < Multiset.card (x ::ₘ 0) + Multiset.card (0 : Multiset V)
      rw [Multiset.card_cons]
      omega

/-- **Nothing fires on the empty configuration.** -/
theorem not_splits_zero {event : Event V} {target : Multiset V} : ¬ Splits G event 0 target := by
  rintro ⟨rest, sourceEq, -⟩
  have sizes := congrArg Multiset.card sourceEq
  rw [Multiset.card_zero, Multiset.card_add] at sizes
  have positive := need_pos event
  omega

/-- **The history grammar by splitting, as a GSLT.** -/
abbrev splitGSLT : GSLT.{0} where
  Term := Multiset V
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := ∃ event, Splits G event source target
  rewrites_resp_left := by
    intro _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    exact equal ▸ step

/-! ## Renaming events -/

section Relabel

theorem relabel_id (event : Event V) : relabel (fun x => x) event = event := by
  cases event <;> rfl

theorem relabel_relabel (first second : V → V) (event : Event V) :
    relabel second (relabel first event) = relabel (fun x => second (first x)) event := by
  cases event <;> rfl

theorem relabel_congr {first second : V → V} (same : ∀ x, first x = second x) (event : Event V) :
    relabel first event = relabel second event := by
  cases event <;> simp only [relabel, same]

theorem consumed_relabel (f : V → V) (event : Event V) :
    consumed (relabel f event) = (consumed event).map f := by
  cases event with
  | evolve x => rfl
  | fork x => rfl
  | merge x y => rfl
  | erase x => rfl

theorem read_relabel (f : V → V) (event : Event V) : read (relabel f event) = (read event).map f := by
  cases event with
  | evolve x => rfl
  | fork x => rfl
  | merge x y => rfl
  | erase x => rfl

variable {G}

/-- A map of nodes commuting with evolution and merge, injective or not. -/
structure Equivariant (G : Grammar V) (f : V → V) : Prop where
  evolve_comm : ∀ x, f (G.evolve x) = G.evolve (f x)
  merge_comm : ∀ x y, f (G.merge x y) = G.merge (f x) (f y)

theorem renaming_equivariant (rename : Renaming G) : Equivariant G rename.map :=
  ⟨rename.evolve_comm, rename.merge_comm⟩

theorem produced_relabel {f : V → V} (equivariant : Equivariant G f) (event : Event V) :
    produced G (relabel f event) = (produced G event).map f := by
  cases event with
  | evolve x =>
      change (G.evolve (f x) ::ₘ 0 : Multiset V) = (G.evolve x ::ₘ 0).map f
      rw [Multiset.map_cons, Multiset.map_zero, equivariant.evolve_comm]
  | fork x => rfl
  | merge x y =>
      change (G.merge (f x) (f y) ::ₘ 0 : Multiset V) = (G.merge x y ::ₘ 0).map f
      rw [Multiset.map_cons, Multiset.map_zero, equivariant.merge_comm]
  | erase x => rfl

/-- **Splitting is equivariant** under every map commuting with the grammar. -/
theorem splits_map {f : V → V} (equivariant : Equivariant G f) {event : Event V}
    {source target : Multiset V} (splits : Splits G event source target) :
    Splits G (relabel f event) (source.map f) (target.map f) := by
  obtain ⟨rest, rfl, rfl⟩ := splits
  refine ⟨rest.map f, ?_, ?_⟩
  · rw [consumed_relabel, read_relabel, Multiset.map_add, Multiset.map_add]
  · rw [produced_relabel equivariant, read_relabel, Multiset.map_add, Multiset.map_add]

/-- **Splitting is a congruence for parallel composition.** -/
theorem splits_add (frame : Multiset V) {event : Event V} {source target : Multiset V}
    (splits : Splits G event source target) :
    Splits G event (source + frame) (target + frame) := by
  obtain ⟨rest, rfl, rfl⟩ := splits
  exact ⟨rest + frame, by rw [Multiset.add_assoc], by rw [Multiset.add_assoc]⟩

end Relabel

/-! ## History contexts -/

/-- **A history context**: a renaming of nodes that commutes with the grammar,
then an authored frame placed in parallel.  The frame is authored as a list; it
acts through the multiset it denotes. -/
structure Context (G : Grammar V) where
  rename : Renaming G
  frame : List V

namespace Context

variable {G}

theorem ext {first second : Context G} (rename : first.rename.map = second.rename.map)
    (frame : first.frame = second.frame) : first = second := by
  obtain ⟨firstRename, firstFrame⟩ := first
  obtain ⟨secondRename, secondFrame⟩ := second
  have renamings : firstRename = secondRename := Renaming.ext rename
  cases renamings
  cases frame
  rfl

/-- **A context acts on a configuration**: rename it, then place the frame
beside it. -/
def apply (context : Context G) (live : Multiset V) : Multiset V :=
  live.map context.rename.map + (context.frame : Multiset V)

/-- A context renames an event. -/
def event (context : Context G) (event : Event V) : Event V := relabel context.rename.map event

/-- A context renames an entry and keeps its direction. -/
def entry (context : Context G) (entry : Entry V) : Entry V := (entry.1, context.event entry.2)

/-- A context renames a script entry by entry. -/
def script (context : Context G) (script : List (Entry V)) : List (Entry V) := script.map context.entry

/-- The identity context: no renaming and an empty frame. -/
protected def one (G : Grammar V) : Context G := ⟨Renaming.id G, []⟩

/-- **One context after another**: the later renaming also renames the earlier
frame. -/
def andThen (earlier later : Context G) : Context G :=
  ⟨earlier.rename.comp later.rename, earlier.frame.map later.rename.map ++ later.frame⟩

/-- A renaming as a context with an empty frame. -/
def ofRenaming (rename : Renaming G) : Context G := ⟨rename, []⟩

/-- A frame as a context without renaming. -/
def ofFrame (G : Grammar V) (frame : List V) : Context G := ⟨Renaming.id G, frame⟩

@[simp] theorem andThen_rename_map (earlier later : Context G) (x : V) :
    (earlier.andThen later).rename.map x = later.rename.map (earlier.rename.map x) := rfl

@[simp] theorem one_rename_map (x : V) : (Context.one G).rename.map x = x := rfl

theorem one_andThen (context : Context G) : (Context.one G).andThen context = context :=
  ext rfl rfl

theorem andThen_one (context : Context G) : context.andThen (Context.one G) = context :=
  ext rfl (by
    change context.frame.map (fun x => x) ++ [] = context.frame
    rw [List.map_id', List.append_nil])

theorem andThen_assoc (first second third : Context G) :
    (first.andThen second).andThen third = first.andThen (second.andThen third) :=
  ext rfl (by
    change (first.frame.map second.rename.map ++ second.frame).map third.rename.map ++ third.frame =
      first.frame.map (fun x => third.rename.map (second.rename.map x)) ++
        (second.frame.map third.rename.map ++ third.frame)
    rw [List.map_append, List.map_map, List.append_assoc]
    rfl)

theorem apply_one (live : Multiset V) : (Context.one G).apply live = live := by
  change live.map (fun x => x) + ((([] : List V)) : Multiset V) = live
  rw [Multiset.coe_nil, Multiset.add_zero, Multiset.map_id']

theorem apply_andThen (earlier later : Context G) (live : Multiset V) :
    (earlier.andThen later).apply live = later.apply (earlier.apply live) := by
  change live.map (fun x => later.rename.map (earlier.rename.map x)) +
      ((earlier.frame.map later.rename.map ++ later.frame : List V) : Multiset V) =
    (live.map earlier.rename.map + (earlier.frame : Multiset V)).map later.rename.map +
      (later.frame : Multiset V)
  rw [← Multiset.coe_add, ← Multiset.map_coe, Multiset.map_add, Multiset.map_map,
    Multiset.add_assoc]
  rfl

theorem event_one (event : Event V) : (Context.one G).event event = event := relabel_id event

theorem event_andThen (earlier later : Context G) (event : Event V) :
    (earlier.andThen later).event event = later.event (earlier.event event) :=
  (relabel_relabel earlier.rename.map later.rename.map event).symm

theorem entry_one (entry : Entry V) : (Context.one G).entry entry = entry := by
  obtain ⟨direction, event⟩ := entry
  change (direction, (Context.one G).event event) = (direction, event)
  rw [event_one]

theorem entry_andThen (earlier later : Context G) (entry : Entry V) :
    (earlier.andThen later).entry entry = later.entry (earlier.entry entry) := by
  obtain ⟨direction, event⟩ := entry
  change (direction, (earlier.andThen later).event event) = (direction, later.event (earlier.event event))
  rw [event_andThen]

theorem script_one (script : List (Entry V)) : (Context.one G).script script = script := by
  unfold Context.script
  conv_rhs => rw [← List.map_id script]
  exact List.map_congr_left fun entry _ => entry_one entry

theorem script_andThen (earlier later : Context G) (script : List (Entry V)) :
    (earlier.andThen later).script script = later.script (earlier.script script) := by
  unfold Context.script
  rw [List.map_map]
  exact List.map_congr_left fun entry _ => entry_andThen earlier later entry

theorem script_nil (context : Context G) : context.script [] = [] := rfl

theorem script_cons (context : Context G) (entry : Entry V) (rest : List (Entry V)) :
    context.script (entry :: rest) = context.entry entry :: context.script rest := rfl

theorem script_append (context : Context G) (first second : List (Entry V)) :
    context.script (first ++ second) = context.script first ++ context.script second :=
  List.map_append

theorem script_length (context : Context G) (script : List (Entry V)) :
    (context.script script).length = script.length :=
  List.length_map _

/-- **Every context is a renaming followed by a frame.** -/
theorem normal_form (context : Context G) :
    context = (ofRenaming context.rename).andThen (ofFrame G context.frame) :=
  ext rfl rfl

/-- **Renaming commutes with parallel addition**: placing a frame and then
renaming is renaming and then placing the renamed frame. -/
theorem frame_andThen_rename (frame : List V) (rename : Renaming G) :
    (ofFrame G frame).andThen (ofRenaming rename) = (ofRenaming rename).andThen (ofFrame G (frame.map rename.map)) :=
  ext rfl (by
    change frame.map rename.map ++ [] = [].map (fun x => x) ++ frame.map rename.map
    rw [List.append_nil]
    rfl)

/-- The same law on configurations. -/
theorem apply_frame_rename (frame : List V) (rename : Renaming G) (live : Multiset V) :
    (ofRenaming rename).apply ((ofFrame G frame).apply live) =
      (ofFrame G (frame.map rename.map)).apply ((ofRenaming rename).apply live) := by
  rw [← apply_andThen, ← apply_andThen, frame_andThen_rename]

theorem apply_ofRenaming (rename : Renaming G) (live : Multiset V) :
    (ofRenaming rename).apply live = live.map rename.map := by
  change live.map rename.map + ((([] : List V)) : Multiset V) = _
  rw [Multiset.coe_nil, Multiset.add_zero]

theorem apply_ofFrame (frame : List V) (live : Multiset V) :
    (ofFrame G frame).apply live = live + (frame : Multiset V) := by
  change live.map (fun x => x) + _ = _
  rw [Multiset.map_id']
  rfl

theorem apply_of_frame_nil (context : Context G) (empty : context.frame = []) (live : Multiset V) :
    context.apply live = live.map context.rename.map := by
  unfold Context.apply
  rw [empty, Multiset.coe_nil, Multiset.add_zero]

theorem apply_zero (context : Context G) : context.apply 0 = (context.frame : Multiset V) := by
  unfold Context.apply
  rw [Multiset.map_zero, Multiset.zero_add]

end Context

/-! ## Substitution commutes with steps -/

/-- **A context carries every split**, with its event renamed. -/
theorem splits_apply (context : Context G) {event : Event V} {source target : Multiset V}
    (splits : Splits G event source target) :
    Splits G (context.event event) (context.apply source) (context.apply target) :=
  splits_add (context.frame : Multiset V) (splits_map (renaming_equivariant context.rename) splits)

/-- **A context carries every two-sided move.** -/
theorem moves_apply (context : Context G) {entry : Entry V} {source target : Multiset V}
    (moves : Moves G entry source target) :
    Moves G (context.entry entry) (context.apply source) (context.apply target) := by
  obtain ⟨direction, event⟩ := entry
  cases direction with
  | forward => exact splits_apply G context moves
  | backward => exact splits_apply G context moves

/-- Two-sided labelled paths. -/
inductive Path : Multiset V → List (Entry V) → Multiset V → Prop where
  | nil (live : Multiset V) : Path live [] live
  | cons {live middle result : Multiset V} {entry : Entry V} {rest : List (Entry V)} :
      Moves G entry live middle → Path middle rest result → Path live (entry :: rest) result

/-- **A context carries every path**, with its script renamed. -/
theorem path_apply (context : Context G) {source target : Multiset V} {script : List (Entry V)}
    (path : Path G source script target) :
    Path G (context.apply source) (context.script script) (context.apply target) := by
  induction path with
  | nil live => exact .nil _
  | cons moves _ inductionHypothesis => exact .cons (moves_apply G context moves) inductionHypothesis

theorem path_append {first second : List (Entry V)} :
    ∀ {source target : Multiset V}, Path G source (first ++ second) target ↔
      ∃ middle, Path G source first middle ∧ Path G middle second target := by
  induction first with
  | nil =>
      intro source target
      exact ⟨fun path => ⟨source, .nil _, path⟩, fun ⟨middle, start, path⟩ => by cases start; exact path⟩
  | cons entry rest inductionHypothesis =>
      intro source target
      constructor
      · intro path
        cases path with
        | cons moves path' =>
            obtain ⟨middle, start, finish⟩ := inductionHypothesis.mp path'
            exact ⟨middle, .cons moves start, finish⟩
      · rintro ⟨middle, start, finish⟩
        cases start with
        | cons moves start' => exact .cons moves (inductionHypothesis.mpr ⟨middle, start', finish⟩)

/-! ## The labelled reduction span and its contexts -/

/-- A labelled step: an event and its endpoints, with the split that fires
it. -/
structure EventStep (G : Grammar V) where
  event : Event V
  source : Multiset V
  target : Multiset V
  splits : Splits G event source target

theorem EventStep.ext' {G : Grammar V} {first second : EventStep G} (event : first.event = second.event)
    (source : first.source = second.source) (target : first.target = second.target) :
    first = second := by
  obtain ⟨_, _, _, _⟩ := first
  obtain ⟨_, _, _, _⟩ := second
  cases event
  cases source
  cases target
  rfl

/-- **The labelled reduction span** of the history grammar. -/
def eventSpan : ReductionSpan (Multiset V) where
  Edge := EventStep G
  source := EventStep.source
  target := EventStep.target

/-- **A context acts on the whole labelled span**: every step keeps its event,
renamed, and both endpoints, acted on. -/
def contextSpan (context : Context G) : SpanMap (eventSpan G) (eventSpan G) where
  states := context.apply
  events step := ⟨context.event step.event, context.apply step.source, context.apply step.target,
    splits_apply G context step.splits⟩
  source_comm _ := rfl
  target_comm _ := rfl

theorem spanMap_ext {X Y : Type} {A : ReductionSpan X} {B : ReductionSpan Y} {first second : SpanMap A B}
    (states : first.states = second.states) (events : first.events = second.events) : first = second := by
  obtain ⟨_, _, _, _⟩ := first
  obtain ⟨_, _, _, _⟩ := second
  cases states
  cases events
  rfl

/-- **The identity context is the identity of the labelled span.** -/
theorem contextSpan_one : contextSpan G (Context.one G) = SpanMap.identity (eventSpan G) :=
  spanMap_ext (funext Context.apply_one) (funext fun step =>
    EventStep.ext' (Context.event_one step.event) (Context.apply_one step.source)
      (Context.apply_one step.target))

/-- **Composition of contexts is composition of span maps**, on events and on
both endpoints. -/
theorem contextSpan_andThen (earlier later : Context G) :
    contextSpan G (earlier.andThen later) = (contextSpan G later).comp (contextSpan G earlier) :=
  spanMap_ext (funext (Context.apply_andThen earlier later)) (funext fun step =>
    EventStep.ext' (Context.event_andThen earlier later step.event)
      (Context.apply_andThen earlier later step.source) (Context.apply_andThen earlier later step.target))

/-- A two-sided labelled step: an entry and its endpoints, with the move. -/
structure EntryStep (G : Grammar V) where
  entry : Entry V
  source : Multiset V
  target : Multiset V
  moves : Moves G entry source target

theorem EntryStep.ext' {G : Grammar V} {first second : EntryStep G} (entry : first.entry = second.entry)
    (source : first.source = second.source) (target : first.target = second.target) :
    first = second := by
  obtain ⟨_, _, _, _⟩ := first
  obtain ⟨_, _, _, _⟩ := second
  cases entry
  cases source
  cases target
  rfl

/-- **The two-sided labelled span**: forward entries fire events, backward
entries undo them. -/
def entrySpan : ReductionSpan (Multiset V) where
  Edge := EntryStep G
  source := EntryStep.source
  target := EntryStep.target

/-- **A context acts on the two-sided span**, keeping every entry's direction
and renaming its event. -/
def contextEntrySpan (context : Context G) : SpanMap (entrySpan G) (entrySpan G) where
  states := context.apply
  events step := ⟨context.entry step.entry, context.apply step.source, context.apply step.target,
    moves_apply G context step.moves⟩
  source_comm _ := rfl
  target_comm _ := rfl

theorem contextEntrySpan_one : contextEntrySpan G (Context.one G) = SpanMap.identity (entrySpan G) :=
  spanMap_ext (funext Context.apply_one) (funext fun step =>
    EntryStep.ext' (Context.entry_one step.entry) (Context.apply_one step.source)
      (Context.apply_one step.target))

theorem contextEntrySpan_andThen (earlier later : Context G) :
    contextEntrySpan G (earlier.andThen later) = (contextEntrySpan G later).comp (contextEntrySpan G earlier) :=
  spanMap_ext (funext (Context.apply_andThen earlier later)) (funext fun step =>
    EntryStep.ext' (Context.entry_andThen earlier later step.entry)
      (Context.apply_andThen earlier later step.source) (Context.apply_andThen earlier later step.target))

/-- The forward reading of a labelled step. -/
def forwardEntry : SpanMap (eventSpan G) (entrySpan G) where
  states := id
  events step := ⟨(.forward, step.event), step.source, step.target, step.splits⟩
  source_comm _ := rfl
  target_comm _ := rfl

/-- **Contexts commute with the forward reading.** -/
theorem forwardEntry_context (context : Context G) :
    (forwardEntry G).comp (contextSpan G context) = (contextEntrySpan G context).comp (forwardEntry G) :=
  spanMap_ext rfl rfl

/-- The event shadow: a labelled step forgets its event and is an edge of the
GSLT's reduction span. -/
def eventShadow : SpanMap (eventSpan G) (gsltSpan (splitGSLT G)) where
  states := id
  events step := ⟨step.source, step.target, ⟨step.event, step.splits⟩⟩
  source_comm _ := rfl
  target_comm _ := rfl

/-- Every edge of the GSLT's reduction span leaving a configuration is the
shadow of a labelled step leaving it. -/
theorem eventShadow_sourceOccurrenceLifts : (eventShadow G).SourceOccurrenceLifts := by
  rintro state ⟨source, target, event, splits⟩ sourceEq
  exact ⟨⟨event, source, target, splits⟩, sourceEq, rfl⟩

/-- Every edge reaching a configuration is the shadow of a labelled step
reaching it. -/
theorem eventShadow_targetOccurrenceLifts : (eventShadow G).TargetOccurrenceLifts := by
  rintro state ⟨source, target, event, splits⟩ targetEq
  exact ⟨⟨event, source, target, splits⟩, targetEq, rfl⟩

/-- Contexts act on the GSLT's steps. -/
theorem step_congruent_context (context : Context G) :
    SpanTransport.Congruent (splitGSLT G).Step context.apply context.apply :=
  fun _ _ step => let ⟨event, splits⟩ := step; ⟨context.event event, splits_apply G context splits⟩

/-! ## The context category: event scripts and history contexts -/

/-- A world of the context category: the length of the script travelled. -/
structure World (G : Grammar V) where
  length : ℕ

/-- **An arrow of the context category**: a two-sided event script together
with a history context. -/
structure Arrow {G : Grammar V} (first second : World G) where
  script : List (Entry V)
  context : Context G
  length_eq : first.length + script.length = second.length

variable {G}

theorem Arrow.ext' {first second : World G} {earlier later : Arrow first second}
    (script : earlier.script = later.script) (context : earlier.context = later.context) :
    earlier = later := by
  obtain ⟨_, _, _⟩ := earlier
  obtain ⟨_, _, _⟩ := later
  cases script
  cases context
  rfl

/-- The identity arrow. -/
def Arrow.id (world : World G) : Arrow world world := ⟨[], Context.one G, Nat.add_zero _⟩

/-- **Composition is the semidirect product**: the later context renames the
earlier script, and the contexts compose. -/
def Arrow.comp {first second third : World G} (earlier : Arrow first second) (later : Arrow second third) :
    Arrow first third :=
  ⟨later.context.script earlier.script ++ later.script, earlier.context.andThen later.context, by
    rw [List.length_append, Context.script_length, ← Nat.add_assoc, earlier.length_eq, later.length_eq]⟩

/-- **The context category of the history grammar.** -/
instance category : Category.{0} (World G) where
  Hom := Arrow
  id := Arrow.id
  comp := Arrow.comp
  id_comp arrow := Arrow.ext' (by
      change (Arrow.context arrow).script [] ++ Arrow.script arrow = Arrow.script arrow
      rfl) (Context.one_andThen (Arrow.context arrow))
  comp_id arrow := Arrow.ext' (by
      change (Context.one G).script (Arrow.script arrow) ++ [] = Arrow.script arrow
      rw [Context.script_one, List.append_nil]) (Context.andThen_one (Arrow.context arrow))
  assoc first second third := Arrow.ext' (by
      change (Arrow.context third).script ((Arrow.context second).script (Arrow.script first) ++
          Arrow.script second) ++ Arrow.script third =
        ((Arrow.context second).andThen (Arrow.context third)).script (Arrow.script first) ++
          ((Arrow.context third).script (Arrow.script second) ++ Arrow.script third)
      rw [Context.script_append, Context.script_andThen, List.append_assoc])
    (Context.andThen_assoc (Arrow.context first) (Arrow.context second) (Arrow.context third))

theorem comp_script {first second third : World G} (earlier : first ⟶ second) (later : second ⟶ third) :
    Arrow.script (earlier ≫ later) = (Arrow.context later).script (Arrow.script earlier) ++ Arrow.script later :=
  rfl

theorem comp_context {first second third : World G} (earlier : first ⟶ second) (later : second ⟶ third) :
    Arrow.context (earlier ≫ later) = (Arrow.context earlier).andThen (Arrow.context later) := rfl

theorem id_script (world : World G) : Arrow.script (𝟙 world : world ⟶ world) = [] := rfl

theorem id_context (world : World G) : Arrow.context (𝟙 world : world ⟶ world) = Context.one G := rfl

/-- A pure context at a world. -/
def contextArrow (world : World G) (context : Context G) : world ⟶ world :=
  ⟨[], context, Nat.add_zero _⟩

/-- A pure event script: an event-path context. -/
def scriptArrow {first second : World G} (script : List (Entry V))
    (length_eq : first.length + script.length = second.length) : first ⟶ second :=
  ⟨script, Context.one G, length_eq⟩

/-- **Pure contexts compose as contexts.** -/
theorem contextArrow_andThen (world : World G) (earlier later : Context G) :
    contextArrow world (earlier.andThen later) = contextArrow world earlier ≫ contextArrow world later :=
  Arrow.ext' rfl rfl

theorem contextArrow_one (world : World G) : contextArrow world (Context.one G) = 𝟙 world := rfl

/-- **Pure scripts compose by concatenation**, as event paths do. -/
theorem scriptArrow_comp {first second third : World G} (earlier later : List (Entry V))
    (earlierLength : first.length + earlier.length = second.length)
    (laterLength : second.length + later.length = third.length)
    (length_eq : first.length + (earlier ++ later).length = third.length) :
    scriptArrow earlier earlierLength ≫ scriptArrow later laterLength = scriptArrow (earlier ++ later) length_eq :=
  Arrow.ext' (by
      change (Context.one G).script earlier ++ later = earlier ++ later
      rw [Context.script_one])
    (Context.andThen_one _)

/-- **A context slides past a script by renaming it.** -/
theorem interchange {first second : World G} (script : List (Entry V))
    (length_eq : first.length + script.length = second.length) (context : Context G) :
    scriptArrow script length_eq ≫ contextArrow second context =
      contextArrow first context ≫
        scriptArrow (context.script script) (by rw [Context.script_length]; exact length_eq) :=
  Arrow.ext' (by
      change context.script script ++ [] = (Context.one G).script [] ++ context.script script
      rw [List.append_nil]
      rfl)
    ((Context.one_andThen context).trans (Context.andThen_one context).symm)

/-- **Every arrow is a context followed by a script.** -/
theorem arrow_normal_form {first second : World G} (arrow : first ⟶ second) :
    arrow = contextArrow first (Arrow.context arrow) ≫ scriptArrow (Arrow.script arrow) (Arrow.length_eq arrow) :=
  Arrow.ext' rfl (Context.andThen_one (Arrow.context arrow)).symm

/-! ## The four lifting laws of a context -/

section Lifts

variable [DecidableEq V] (L : Listing V)

/-- A partial inverse of a renaming, searched along a listing of the nodes. -/
def inverseOn (rename : Renaming G) (y : V) : V :=
  match L.nodes.find? (fun x => decide (rename.map x = y)) with
  | some x => x
  | none => y

theorem inverseOn_map (rename : Renaming G) (x : V) : inverseOn L rename (rename.map x) = x := by
  unfold inverseOn
  split
  · next candidate found =>
      have matched : decide (rename.map candidate = rename.map x) = true :=
        List.find?_some (p := fun other => decide (rename.map other = rename.map x)) found
      exact rename.injective (of_decide_eq_true matched)
  · next found => exact absurd (decide_eq_true rfl) (List.find?_eq_none.mp found x (L.complete x))

theorem map_inverseOn (rename : Renaming G) {y : V} (inRange : ∃ x, rename.map x = y) :
    rename.map (inverseOn L rename y) = y := by
  obtain ⟨x, rfl⟩ := inRange
  rw [inverseOn_map]

theorem multiset_inverseOn_map (rename : Renaming G) (live : Multiset V) :
    (live.map rename.map).map (inverseOn L rename) = live := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id' live]
  exact Multiset.map_congr rfl fun x _ => inverseOn_map L rename x

theorem multiset_map_inverseOn (rename : Renaming G) {live : Multiset V}
    (inRange : ∀ y ∈ live, ∃ x, rename.map x = y) :
    (live.map (inverseOn L rename)).map rename.map = live := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id' live]
  exact Multiset.map_congr rfl fun y member => map_inverseOn L rename (inRange y member)

omit [DecidableEq V] in
theorem mem_range_of_mem_map {rename : V → V} {live : Multiset V} {y : V}
    (member : y ∈ live.map rename) : ∃ x, rename x = y := by
  obtain ⟨x, _, same⟩ := Multiset.mem_map.mp member
  exact ⟨x, same⟩

omit [DecidableEq V] in
/-- The nodes an event names are those it consumes or reads. -/
theorem relabel_inverse_of_needs {rename inverse : V → V} {event : Event V}
    (needs : ∀ y ∈ consumed event + read event, rename (inverse y) = y) :
    relabel rename (relabel inverse event) = event := by
  cases event with
  | evolve x =>
      have := needs x (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self x 0)))
      change Event.evolve (rename (inverse x)) = _
      rw [this]
  | fork x =>
      have := needs x (Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons_self x 0)))
      change Event.fork (rename (inverse x)) = _
      rw [this]
  | merge x y =>
      have first := needs x (Multiset.mem_add.mpr (Or.inl (by
        change x ∈ x ::ₘ y ::ₘ 0
        exact Multiset.mem_cons_self x _)))
      have second := needs y (Multiset.mem_add.mpr (Or.inl (by
        change y ∈ x ::ₘ y ::ₘ 0
        exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self y 0))))
      change Event.merge (rename (inverse x)) (rename (inverse y)) = _
      rw [first, second]
  | erase x =>
      have := needs x (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self x 0)))
      change Event.erase (rename (inverse x)) = _
      rw [this]

omit [DecidableEq V] in
/-- The erasure of a node of the frame, from the frame placed beside the empty
configuration. -/
theorem splits_erase_frame (x : V) (rest : List V) :
    Splits G (.erase x) ((x :: rest : List V) : Multiset V) (rest : Multiset V) := by
  refine ⟨rest, ?_, ?_⟩
  · change _ = (x ::ₘ 0) + 0 + _
    rw [Multiset.add_zero, coe_cons_eq]
    rfl
  · change _ = 0 + 0 + _
    rw [Multiset.zero_add, Multiset.zero_add]

omit [DecidableEq V] in
/-- **A renaming with a left inverse and no frame lifts every source
occurrence**, whether or not the renaming is onto. -/
theorem sourceOccurrenceLifts_of_leftInverse (context : Context G) (empty : context.frame = [])
    (inverse : V → V) (leftInverse : ∀ x, inverse (context.rename.map x) = x) :
    (contextSpan G context).SourceOccurrenceLifts := by
  intro state step sourceEq
  obtain ⟨event, source, target, rest, sourceSplit, targetSplit⟩ := step
  change source = context.apply state at sourceEq
  rw [Context.apply_of_frame_nil context empty] at sourceEq
  subst sourceEq
  have back : ∀ y, (∃ x, context.rename.map x = y) → context.rename.map (inverse y) = y := by
    rintro y ⟨x, rfl⟩
    rw [leftInverse]
  have inRange : ∀ y ∈ consumed event + read event + rest, ∃ x, context.rename.map x = y := by
    intro y member
    rw [← sourceSplit] at member
    exact mem_range_of_mem_map member
  have needs : ∀ y ∈ consumed event + read event, context.rename.map (inverse y) = y := fun y member =>
    back y (inRange y (Multiset.mem_add.mpr (Or.inl member)))
  have restBack : (rest.map inverse).map context.rename.map = rest := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id' rest]
    exact Multiset.map_congr rfl fun y member => back y (inRange y (Multiset.mem_add.mpr (Or.inr member)))
  have stateBack : (state.map context.rename.map).map inverse = state := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id' state]
    exact Multiset.map_congr rfl fun x _ => leftInverse x
  refine ⟨⟨relabel inverse event, state,
    produced G (relabel inverse event) + read (relabel inverse event) + rest.map inverse,
    ⟨rest.map inverse, ?_, rfl⟩⟩, rfl, ?_⟩
  · rw [consumed_relabel, read_relabel, ← Multiset.map_add, ← Multiset.map_add, ← sourceSplit, stateBack]
  · apply EventStep.ext'
    · exact relabel_inverse_of_needs needs
    · exact Context.apply_of_frame_nil context empty state
    · change context.apply (produced G (relabel inverse event) + read (relabel inverse event) +
        rest.map inverse) = target
      rw [Context.apply_of_frame_nil context empty, Multiset.map_add, Multiset.map_add,
        ← produced_relabel (renaming_equivariant context.rename), ← read_relabel,
        relabel_inverse_of_needs needs, restBack, targetSplit]

include L in
/-- **Source occurrence lifting holds exactly when the frame is empty.** -/
theorem contextSpan_sourceOccurrenceLifts_iff (context : Context G) :
    (contextSpan G context).SourceOccurrenceLifts ↔ context.frame = [] := by
  constructor
  · intro lifts
    cases frame : context.frame with
    | nil => rfl
    | cons x rest =>
        exfalso
        have splits : Splits G (.erase x) (context.apply 0) (rest : Multiset V) := by
          rw [Context.apply_zero, frame]
          exact splits_erase_frame x rest
        obtain ⟨lift, sourceEq, _⟩ := lifts 0 ⟨.erase x, context.apply 0, rest, splits⟩ rfl
        have lifted := lift.splits
        change lift.source = 0 at sourceEq
        rw [sourceEq] at lifted
        exact not_splits_zero G lifted
  · intro empty
    exact sourceOccurrenceLifts_of_leftInverse context empty (inverseOn L context.rename)
      (inverseOn_map L context.rename)

include L in
/-- **Source endpoint lifting holds exactly when the frame is empty.** -/
theorem contextSpan_sourceLifts_iff (context : Context G) :
    (contextSpan G context).SourceLifts ↔ context.frame = [] := by
  constructor
  · intro lifts
    cases frame : context.frame with
    | nil => rfl
    | cons x rest =>
        exfalso
        have splits : Splits G (.erase x) (context.apply 0) (rest : Multiset V) := by
          rw [Context.apply_zero, frame]
          exact splits_erase_frame x rest
        obtain ⟨lift, sourceEq, _⟩ := lifts 0 ⟨.erase x, context.apply 0, rest, splits⟩ rfl
        have lifted := lift.splits
        change lift.source = 0 at sourceEq
        rw [sourceEq] at lifted
        exact not_splits_zero G lifted
  · intro empty
    exact (contextSpan G context).sourceLifts_of_occurrence
      ((contextSpan_sourceOccurrenceLifts_iff L context).mpr empty)

include L in
/-- A bijective renaming has an inverse renaming. -/
def inverseRenaming (rename : Renaming G) (onto : Function.Surjective rename.map) : Renaming G where
  map := inverseOn L rename
  injective first second same := by
    rw [← map_inverseOn L rename (onto first), ← map_inverseOn L rename (onto second), same]
  evolve_comm x := by
    apply rename.injective
    rw [map_inverseOn L rename (onto _), rename.evolve_comm, map_inverseOn L rename (onto x)]
  merge_comm x y := by
    apply rename.injective
    rw [map_inverseOn L rename (onto _), rename.merge_comm, map_inverseOn L rename (onto x),
      map_inverseOn L rename (onto y)]

theorem inverseRenaming_map (rename : Renaming G) (onto : Function.Surjective rename.map) (y : V) :
    rename.map ((inverseRenaming L rename onto).map y) = y :=
  map_inverseOn L rename (onto y)

omit [DecidableEq V] in
/-- The undoing of an erasure, reaching any configuration. -/
theorem splits_erase_into (y : V) (live : Multiset V) : Splits G (.erase y) ({y} + live) live := by
  refine ⟨live, ?_, ?_⟩
  · change _ = (y ::ₘ 0) + 0 + live
    rw [Multiset.add_zero]
    rfl
  · change _ = 0 + 0 + live
    rw [Multiset.zero_add, Multiset.zero_add]

omit [DecidableEq V] in
/-- The copy of a node, reaching two copies of it beside a rest. -/
theorem splits_fork_into (x : V) (rest : Multiset V) :
    Splits G (.fork x) ({x} + rest) ({x} + ({x} + rest)) := by
  refine ⟨rest, ?_, ?_⟩
  · change _ = 0 + (x ::ₘ 0) + rest
    rw [Multiset.zero_add]
    rfl
  · change _ = (x ::ₘ 0) + (x ::ₘ 0) + rest
    rw [Multiset.add_assoc]
    rfl

omit [DecidableEq V] in
/-- Target endpoint lifting of a context forces its renaming onto. -/
theorem onto_of_targetLifts {context : Context G} (lifts : (contextSpan G context).TargetLifts) :
    Function.Surjective context.rename.map := by
  intro y
  obtain ⟨lift, targetEq, sourceEq⟩ :=
    lifts 0 ⟨.erase y, {y} + context.apply 0, context.apply 0, splits_erase_into y _⟩ rfl
  change context.apply lift.source = {y} + context.apply 0 at sourceEq
  unfold Context.apply at sourceEq
  rw [Multiset.map_zero, Multiset.zero_add] at sourceEq
  have renamed := add_right_cancel_free sourceEq
  exact mem_range_of_mem_map (renamed ▸ Multiset.mem_singleton_self y)

omit [DecidableEq V] in
/-- Target endpoint lifting of a context forces its frame empty. -/
theorem frame_nil_of_targetLifts {context : Context G} (lifts : (contextSpan G context).TargetLifts) :
    context.frame = [] := by
  cases frame : context.frame with
  | nil => rfl
  | cons x rest =>
      exfalso
      obtain ⟨node, renamed⟩ := onto_of_targetLifts lifts x
      have target : context.apply {node} = {x} + ({x} + (rest : Multiset V)) := by
        unfold Context.apply
        rw [Multiset.map_singleton, renamed, frame, coe_cons_eq]
      obtain ⟨lift, targetEq, sourceEq⟩ := lifts {node}
        ⟨.fork x, {x} + rest, context.apply {node}, target ▸ splits_fork_into x _⟩ rfl
      change context.apply lift.source = {x} + rest at sourceEq
      unfold Context.apply at sourceEq
      rw [frame, coe_cons_eq] at sourceEq
      have empty : lift.source.map context.rename.map = 0 :=
        add_right_cancel_free (sourceEq.trans (Multiset.zero_add _).symm)
      have lifted := lift.splits
      rw [Multiset.map_eq_zero.mp empty] at lifted
      exact not_splits_zero G lifted

include L in
/-- **Target occurrence lifting holds exactly when the frame is empty and the
renaming is onto.** -/
theorem contextSpan_targetOccurrenceLifts_iff (context : Context G) :
    (contextSpan G context).TargetOccurrenceLifts ↔
      context.frame = [] ∧ Function.Surjective context.rename.map := by
  constructor
  · intro lifts
    have endpoint := (contextSpan G context).targetLifts_of_occurrence lifts
    exact ⟨frame_nil_of_targetLifts endpoint, onto_of_targetLifts endpoint⟩
  · rintro ⟨empty, onto⟩ state step targetEq
    obtain ⟨event, source, target, rest, sourceSplit, targetSplit⟩ := step
    change target = context.apply state at targetEq
    rw [Context.apply_of_frame_nil context empty] at targetEq
    subst targetEq
    have back : ∀ y, context.rename.map ((inverseRenaming L context.rename onto).map y) = y :=
      inverseRenaming_map L context.rename onto
    refine ⟨⟨relabel (inverseRenaming L context.rename onto).map event,
      consumed (relabel (inverseRenaming L context.rename onto).map event) +
        read (relabel (inverseRenaming L context.rename onto).map event) +
          rest.map (inverseRenaming L context.rename onto).map, state,
      ⟨rest.map (inverseRenaming L context.rename onto).map, rfl, ?_⟩⟩, rfl, ?_⟩
    · rw [produced_relabel (renaming_equivariant _), read_relabel, ← Multiset.map_add, ← Multiset.map_add,
        ← targetSplit]
      exact (multiset_inverseOn_map L context.rename state).symm
    · apply EventStep.ext'
      · exact relabel_inverse_of_needs (rename := context.rename.map) fun y _ => back y
      · change context.apply (consumed (relabel (inverseRenaming L context.rename onto).map event) +
          read (relabel (inverseRenaming L context.rename onto).map event) +
            rest.map (inverseRenaming L context.rename onto).map) = source
        rw [Context.apply_of_frame_nil context empty, Multiset.map_add, Multiset.map_add,
          ← consumed_relabel, ← read_relabel,
          relabel_inverse_of_needs (rename := context.rename.map) fun y _ => back y,
          Multiset.map_map, sourceSplit]
        congr 1
        conv_rhs => rw [← Multiset.map_id' rest]
        exact Multiset.map_congr rfl fun y _ => back y
      · exact Context.apply_of_frame_nil context empty state

include L in
/-- **Target endpoint lifting holds exactly when the frame is empty and the
renaming is onto.** -/
theorem contextSpan_targetLifts_iff (context : Context G) :
    (contextSpan G context).TargetLifts ↔ context.frame = [] ∧ Function.Surjective context.rename.map :=
  ⟨fun lifts => ⟨frame_nil_of_targetLifts lifts, onto_of_targetLifts lifts⟩,
    fun conditions => (contextSpan G context).targetLifts_of_occurrence
      ((contextSpan_targetOccurrenceLifts_iff L context).mpr conditions)⟩

include L in
/-- **The four lifting laws of a context**, for its graph as a state relation:
both forth laws hold, the source back law holds exactly when the frame is
empty, and the target back law exactly when moreover the renaming is onto. -/
theorem context_four_laws (context : Context G) :
    SpanTransport.SourceForth (eventSpan G) (eventSpan G) (SpanTransport.graph (contextSpan G context)) ∧
      SpanTransport.TargetForth (eventSpan G) (eventSpan G) (SpanTransport.graph (contextSpan G context)) ∧
      (SpanTransport.SourceBack (eventSpan G) (eventSpan G) (SpanTransport.graph (contextSpan G context)) ↔
        context.frame = []) ∧
      (SpanTransport.TargetBack (eventSpan G) (eventSpan G) (SpanTransport.graph (contextSpan G context)) ↔
        context.frame = [] ∧ Function.Surjective context.rename.map) :=
  ⟨SpanTransport.spanMap_sourceForth _, SpanTransport.spanMap_targetForth _,
    (SpanTransport.spanMap_sourceBack_iff _).trans (contextSpan_sourceLifts_iff L context),
    (SpanTransport.spanMap_targetBack_iff _).trans (contextSpan_targetLifts_iff L context)⟩

include L in
/-- **The four occurrence laws of a context**: as an event relation the context
keeps every event, renamed; both forth laws hold, and the back laws hold
exactly under the same conditions as the endpoint laws. -/
theorem context_four_occurrence_laws (context : Context G) :
    (SpanTransport.SpanRelation.ofSpanMap (contextSpan G context)).Keeps
        (fun step : EventStep G => context.event step.event) EventStep.event ∧
      (SpanTransport.SpanRelation.ofSpanMap (contextSpan G context)).SourceForthOcc ∧
      (SpanTransport.SpanRelation.ofSpanMap (contextSpan G context)).TargetForthOcc ∧
      ((SpanTransport.SpanRelation.ofSpanMap (contextSpan G context)).SourceBackOcc ↔ context.frame = []) ∧
      ((SpanTransport.SpanRelation.ofSpanMap (contextSpan G context)).TargetBackOcc ↔
        context.frame = [] ∧ Function.Surjective context.rename.map) := by
  refine ⟨?_, SpanTransport.SpanRelation.ofSpanMap_sourceForthOcc _,
    SpanTransport.SpanRelation.ofSpanMap_targetForthOcc _,
    (SpanTransport.SpanRelation.ofSpanMap_sourceBackOcc_iff _).trans
      (contextSpan_sourceOccurrenceLifts_iff L context),
    (SpanTransport.SpanRelation.ofSpanMap_targetBackOcc_iff _).trans
      (contextSpan_targetOccurrenceLifts_iff L context)⟩
  rintro step _ rfl
  rfl

include L in
/-- **The future diamond commutes with a context exactly when its frame is
empty.** -/
theorem diamond_natural_iff (context : Context G) :
    (∀ (predicate : Multiset V → Prop) (live : Multiset V),
      derivedDiamond (eventSpan G) predicate (context.apply live) ↔
        derivedDiamond (eventSpan G) (predicate ∘ context.apply) live) ↔ context.frame = [] :=
  ((contextSpan G context).sourceLifts_iff_diamond).symm.trans (contextSpan_sourceLifts_iff L context)

include L in
/-- **The predecessor box commutes with a context exactly when its frame is
empty and its renaming is a bijection.** -/
theorem box_natural_iff (context : Context G) :
    (∀ (predicate : Multiset V → Prop) (live : Multiset V),
      derivedBox (eventSpan G) predicate (context.apply live) ↔
        derivedBox (eventSpan G) (predicate ∘ context.apply) live) ↔
      context.frame = [] ∧ Function.Surjective context.rename.map :=
  ((contextSpan G context).targetLifts_iff_box).symm.trans (contextSpan_targetLifts_iff L context)

end Lifts

end Mettapedia.GSLT.Distinction.HistoryContextCategory
