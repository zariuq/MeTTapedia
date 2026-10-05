import Mettapedia.GSLT.Distinction.HistoryContextCategory
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebra
import Mettapedia.GSLT.Logic.DiscreteReadingCodings

/-!
# The common contextual two-sided history model

`HistoryContextCategory` builds one context category for the history grammar:
an arrow is a two-sided event script together with a history context (a
renaming and a parallel frame).  This module places the grammar over that
category as a small contextual coalgebra with declared readings, and reads it
through the observed material readout of `ContextualObservedCoalgebra`.

* **Placed configurations** (`Placed`, `transport`, `placed`, `fresh`).  A
  state at a world is a configuration, its origin, and the script still to be
  run.  Transport along an arrow applies the context to the configuration,
  renames the pending script, and appends the arrow's script.
* **Profiles** (`Profile`, `exact`, `directions`, `futureOnly`).  A profile says
  which actual two-sided moves a written entry admits: exactly itself, any move
  in its direction, or, for a future-only observer, any forward move and no
  backward one.  Profiles commute with every context.
* **The two-sided coalgebra** (`Advances`, `Emits`, `coalgebra`, `receipts`).
  Along an arrow, a placed configuration emits the result of a move admitted
  by the next entry of its transported script, placed one entry later.  Forward
  entries fire events and backward entries undo them.  The authored receipts
  retain the written entry, the actual move, the result and the rest of the
  script.
* **Declared readings and the exact kernel** (`observes`, `ObservedBisimilar`,
  `value`, `value_eq_iff`, `reading_row_iff`).  The result, fault and cost
  readings of the configuration are declared atoms.  Material equality is one
  stable bisimulation that preserves every declared atom at every context
  (`readings_eq_in_context`); it is not ordinary bisimilarity intersected with
  agreement of the present readings (`HistoryContextControls`).
* **Faithfulness of the exact profile** (`fresh_bisimilar_iff_eq`,
  `fresh_observed_iff_eq`).  Configurations placed fresh at one world are
  bisimilar, already without readings, exactly when they are equal: erasures
  count every node.
* **Descent** (`box_descends_iff_pastMatching`,
  `diamond_descends_iff_futureMatching`, `reading_descends`,
  `exact_box_descends`).  For any observation of configurations, the
  predecessor box of every descending predicate descends exactly when the
  incoming steps match modulo the observation's kernel, and the future diamond
  exactly when the outgoing ones do.  Declared readings descend in every
  profile; with the exact profile every predicate and its predecessor box
  descend.  The future-only profile is the control
  (`HistoryContextControls.futureOnly_box_not_descends`).
* **Authored dictionaries** (`worldCoding`, `arrowCoding`, `atomCoding`).
  Faithful material labels for worlds and arrows, from a node coding and a
  listing of the nodes; the arrow label keeps the script, the renaming and the
  authored frame.

**Choice.**  The construction, the kernel theorems, faithfulness of the exact
profile and the descent criteria are free of `Classical.choice`; the
dictionaries are built from material pairs and finite chains.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryContextTwoSided

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner (Direction)
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver (Listing Reading NodeReadings reading)
open Mettapedia.GSLT.Distinction.HistoryCoverage (Renaming)
open Mettapedia.GSLT.Distinction.HistoryContextCategory
open Mettapedia.GSLT.Distinction.HistoryIndependence (consumed read produced)
open Mettapedia.GSLT.Distinction.Constructive (Scale)
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.TypeTheory.ContextualWitnessCover (NaturalHom)
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.OSLF.Framework.DerivedModalities

variable {V : Type} (G : Grammar V)

/-! ## Placed configurations -/

/-- **A placed configuration**: a configuration, the world it was placed at,
and the script still to be run since then. -/
structure Placed {G : Grammar V} (point : World G) where
  live : Multiset V
  origin : ℕ
  script : List (Entry V)
  length_eq : origin + script.length = point.length

variable {G}

theorem Placed.ext' {point : World G} {first second : Placed point} (live : first.live = second.live)
    (origin : first.origin = second.origin) (script : first.script = second.script) : first = second := by
  obtain ⟨_, _, _, _⟩ := first
  obtain ⟨_, _, _, _⟩ := second
  cases live
  cases origin
  cases script
  rfl

/-- **Transport along an arrow**: the context acts on the configuration and
renames the pending script, and the arrow's own script is appended. -/
def transport {first second : World G} (arrow : first ⟶ second) (state : Placed first) : Placed second :=
  ⟨(Arrow.context arrow).apply state.live, state.origin,
    (Arrow.context arrow).script state.script ++ Arrow.script arrow, by
      rw [List.length_append, Context.script_length, ← Nat.add_assoc, state.length_eq,
        Arrow.length_eq arrow]⟩

theorem transport_live {first second : World G} (arrow : first ⟶ second) (state : Placed first) :
    (transport arrow state).live = (Arrow.context arrow).apply state.live := rfl

theorem transport_origin {first second : World G} (arrow : first ⟶ second) (state : Placed first) :
    (transport arrow state).origin = state.origin := rfl

theorem transport_script {first second : World G} (arrow : first ⟶ second) (state : Placed first) :
    (transport arrow state).script = (Arrow.context arrow).script state.script ++ Arrow.script arrow := rfl

theorem transport_id {point : World G} (state : Placed point) : transport (𝟙 point) state = state :=
  Placed.ext' (Context.apply_one state.live) rfl (by
    change (Context.one G).script state.script ++ [] = state.script
    rw [Context.script_one, List.append_nil])

theorem transport_comp {first second third : World G} (earlier : first ⟶ second) (later : second ⟶ third)
    (state : Placed first) : transport (earlier ≫ later) state = transport later (transport earlier state) :=
  Placed.ext' (Context.apply_andThen _ _ state.live) rfl (by
    change ((Arrow.context earlier).andThen (Arrow.context later)).script state.script ++
        ((Arrow.context later).script (Arrow.script earlier) ++ Arrow.script later) =
      (Arrow.context later).script ((Arrow.context earlier).script state.script ++ Arrow.script earlier) ++
        Arrow.script later
    rw [Context.script_andThen, Context.script_append, List.append_assoc])

variable (G)

/-- **Placed configurations as a functor on the context category.** -/
def placed : World G ⥤ Type where
  obj point := Placed point
  map arrow := TypeCat.ofHom (transport arrow)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro state
    exact transport_id state
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro state
    exact transport_comp earlier later state

variable {G}

theorem placed_map {first second : World G} (arrow : first ⟶ second) (state : Placed first) :
    (placed G).map arrow state = transport arrow state := rfl

/-- A configuration placed fresh at a world, with nothing pending. -/
def fresh (point : World G) (live : Multiset V) : Placed point := ⟨live, point.length, [], Nat.add_zero _⟩

/-- The next world. -/
def next (point : World G) : World G := ⟨point.length + 1⟩

/-- The arrow of one script entry, without context. -/
def entryArrow (point : World G) (entry : Entry V) : point ⟶ next point :=
  scriptArrow [entry] rfl

/-- The arrow of a context, at one world. -/
abbrev inContext (point : World G) (context : Context G) : point ⟶ point := contextArrow point context

theorem transport_entryArrow_fresh (point : World G) (entry : Entry V) (live : Multiset V) :
    transport (entryArrow point entry) (fresh point live) =
      ⟨(Context.one G).apply live, point.length, [entry], rfl⟩ := rfl

theorem transport_inContext (point : World G) (context : Context G) (state : Placed point) :
    transport (inContext point context) state =
      ⟨context.apply state.live, state.origin, context.script state.script, by
        rw [Context.script_length]; exact state.length_eq⟩ :=
  Placed.ext' rfl rfl (List.append_nil _)

/-! ## Profiles -/

variable (G)

/-- **A profile of script reading**: which actual two-sided moves a written
entry admits, preserved by every context. -/
structure Profile where
  admits : Entry V → Entry V → Prop
  admits_context : ∀ (context : Context G) {written actual : Entry V}, admits written actual →
    admits (context.entry written) (context.entry actual)

/-- **The exact profile**: a written entry admits exactly itself. -/
def exact : Profile G where
  admits written actual := actual = written
  admits_context _ _ _ same := by rw [same]

/-- **The direction profile**: a written entry admits every move in its
direction. -/
def directions : Profile G where
  admits written actual := actual.1 = written.1
  admits_context _ _ _ same := same

/-- **The future-only profile**: a forward entry admits every forward move, and
a backward entry admits none. -/
def futureOnly : Profile G where
  admits written actual := written.1 = .forward ∧ actual.1 = .forward
  admits_context _ _ _ both := both

/-! ## The two-sided contextual coalgebra -/

variable {G} (profile : Profile G)

/-- **A placed configuration advances**: the next entry of its script admits a
move from its configuration, and the child is the result, one entry later,
with the rest of the script. -/
def Advances {point : World G} (state child : Placed point) : Prop :=
  ∃ written actual rest, state.script = written :: rest ∧ profile.admits written actual ∧
    Moves G actual state.live child.live ∧ child.origin = state.origin + 1 ∧ child.script = rest

/-- **Advancing commutes with transport.** -/
theorem advances_transport {first second : World G} (arrow : first ⟶ second) {state child : Placed first}
    (advances : Advances profile state child) :
    Advances profile (transport arrow state) (transport arrow child) := by
  obtain ⟨written, actual, rest, scriptEq, admitted, moves, originEq, childScript⟩ := advances
  refine ⟨(Arrow.context arrow).entry written, (Arrow.context arrow).entry actual,
    (Arrow.context arrow).script rest ++ Arrow.script arrow, ?_,
    profile.admits_context _ admitted, moves_apply G _ moves, originEq, ?_⟩
  · rw [transport_script, scriptEq]
    rfl
  · rw [transport_script, childScript]

/-- **A placed configuration emits a child along an arrow** when its transport
along the arrow advances to it. -/
def Emits {point target : World G} (state : Placed point) (arrow : point ⟶ target) (child : Placed target) :
    Prop :=
  Advances profile (transport arrow state) child

/-- The children of a placed configuration at every future. -/
def children (point : World G) (state : Placed point) :
    CoveredFuturePowerFamilies.Predicate (placed G) point where
  holds argument := Emits profile state argument.1.2 argument.2
  closed {first second} move available := by
    obtain ⟨⟨step, triangle⟩, moved⟩ := move
    have advanced := advances_transport profile step available
    rw [← transport_comp] at advanced
    have childEq : transport step first.2 = second.2 := moved
    change Advances profile (transport second.1.2 state) second.2
    rw [← triangle, ← childEq]
    exact advanced

/-- **The retained receipts**: for each future, the written entry, the actual
move, the result and the rest of the script. -/
def receipts (point : World G) (state : Placed point) :
    CoveredFuturePowerFamilies.Enumeration (children profile point state) where
  Carrier future := {receipt : Entry V × Entry V × Multiset V × List (Entry V) //
    (transport future.2 state).script = receipt.1 :: receipt.2.2.2 ∧ profile.admits receipt.1 receipt.2.1 ∧
      Moves G receipt.2.1 (transport future.2 state).live receipt.2.2.1}
  value future receipt := ⟨receipt.1.2.2.1, state.origin + 1, receipt.1.2.2.2, by
    have lengths := (transport future.2 state).length_eq
    rw [receipt.2.1, List.length_cons, transport_origin] at lengths
    omega⟩
  covered future argument := by
    constructor
    · rintro ⟨written, actual, rest, scriptEq, admitted, moves, originEq, childScript⟩
      refine ⟨⟨(written, actual, argument.live, rest), scriptEq, admitted, moves⟩, ?_⟩
      exact Placed.ext' rfl originEq.symm childScript.symm
    · rintro ⟨⟨⟨written, actual, result, rest⟩, scriptEq, admitted, moves⟩, rfl⟩
      exact ⟨written, actual, rest, scriptEq, admitted, moves, rfl, rfl⟩

/-- **The history as a small two-sided contextual coalgebra** over the context
category. -/
def coalgebra : NaturalHom (placed G) (CoveredFuturePowerFamilies.family (placed G)) where
  app point state := ⟨children profile point state, ⟨receipts profile point state⟩⟩
  naturality {first second} step state := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro argument
    obtain ⟨⟨target, arrow⟩, child⟩ := argument
    change Emits profile state (step ≫ arrow) child ↔ Emits profile (transport step state) arrow child
    exact Iff.of_eq (congrArg (fun moved => Advances profile moved child) (transport_comp step arrow state))

theorem coalgebra_holds {point target : World G} (state : Placed point) (arrow : point ⟶ target)
    (child : Placed target) :
    ((coalgebra profile).app point state).val.holds ⟨⟨target, arrow⟩, child⟩ ↔ Emits profile state arrow child :=
  Iff.rfl

/-- **Along one entry, a fresh configuration emits exactly the results of the
admitted moves.** -/
theorem emits_entry_fresh_iff (point : World G) (entry : Entry V) (live result : Multiset V) :
    Emits profile (fresh point live) (entryArrow point entry) (fresh (next point) result) ↔
      ∃ actual, profile.admits entry actual ∧ Moves G actual live result := by
  constructor
  · rintro ⟨written, actual, rest, scriptEq, admitted, moves, _, _⟩
    have writtenEq : written = entry := (List.cons.inj scriptEq).1.symm
    rw [writtenEq] at admitted
    change Moves G actual ((Context.one G).apply live) result at moves
    rw [Context.apply_one] at moves
    exact ⟨actual, admitted, moves⟩
  · rintro ⟨actual, admitted, moves⟩
    refine ⟨entry, actual, [], rfl, admitted, ?_, rfl, rfl⟩
    change Moves G actual ((Context.one G).apply live) result
    rw [Context.apply_one]
    exact moves

/-! ## Declared readings and the exact kernel -/

section Readings

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)
  (R : NodeReadings K V)

/-- **The declared readings**: an atom names a reading and its value, observed
at the configuration of a placed state. -/
def observes (atom : Reading × W) (state : ContextualCoalgebraLabelledGraph.State (placed G)) : Prop :=
  atom.2 = reading K R atom.1 state.2.live

/-- **The observed kernel**: one stable bisimulation that preserves every
declared reading. -/
abbrev ObservedBisimilar (point : World G) (left right : Placed point) : Prop :=
  ContextualObservedCoalgebra.ObservedBisimilar (coalgebra profile) (observes K R) point left right

theorem readings_eq_of_observed {point : World G} {left right : Placed point}
    (related : ObservedBisimilar profile K R point left right) (observation : Reading) :
    reading K R observation left.live = reading K R observation right.live :=
  (ContextualObservedCoalgebra.observed_bisimilar_atoms (coalgebra profile) (observes K R) related
    (observation, reading K R observation left.live)).mp rfl

/-- **The exact kernel keeps every reading at every context**: related states
have equal readings after every arrow. -/
theorem readings_eq_in_context {point target : World G} {left right : Placed point}
    (related : ObservedBisimilar profile K R point left right) (arrow : point ⟶ target)
    (observation : Reading) :
    reading K R observation (transport arrow left).live = reading K R observation (transport arrow right).live := by
  obtain ⟨relation, bisimulation, relatedStates⟩ := related
  exact readings_eq_of_observed profile K R
    ⟨relation, bisimulation, bisimulation.underlying.stable arrow relatedStates⟩ observation

/-- The exact kernel forgets to ordinary contextual bisimilarity. -/
theorem bisimilar_of_observed {point : World G} {left right : Placed point}
    (related : ObservedBisimilar profile K R point left right) :
    ContextualCoalgebraBisimulation.Bisimilar (coalgebra profile) point left right :=
  ContextualObservedCoalgebra.observed_bisimilar_forgets_atoms (coalgebra profile) (observes K R) related

/-- **The exact kernel, as one relation**: a stable bisimulation preserving the
declared readings at every related pair. -/
theorem observed_iff {point : World G} (left right : Placed point) :
    ObservedBisimilar profile K R point left right ↔
      ∃ relation : ∀ point, Placed point → Placed point → Prop,
        ContextualCoalgebraBisimulation.IsBisimulation (coalgebra profile) relation ∧
        (∀ {point : World G} {first second : Placed point}, relation point first second →
          ∀ observation, reading K R observation first.live = reading K R observation second.live) ∧
        relation point left right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    refine ⟨relation, bisimulation.underlying, fun {point first second} relatedStates observation => ?_, related⟩
    exact (bisimulation.atoms relatedStates (observation, reading K R observation first.live)).mp rfl
  · rintro ⟨relation, bisimulation, preserves, related⟩
    refine ⟨relation, ⟨bisimulation, fun {point first second} relatedStates atom => ?_⟩, related⟩
    change atom.2 = reading K R atom.1 first.live ↔ atom.2 = reading K R atom.1 second.live
    rw [preserves relatedStates atom.1]

end Readings

/-! ## Faithfulness of the exact profile -/

section Faithful

variable (G)

theorem splits_erase_split (x : V) (rest : Multiset V) : Splits G (.erase x) ({x} + rest) rest :=
  ⟨rest, by
    change _ = (x ::ₘ 0) + 0 + rest
    rw [Multiset.add_zero]
    rfl, by
    change _ = 0 + 0 + rest
    rw [Multiset.zero_add, Multiset.zero_add]⟩

theorem splits_erase_iff (x : V) (source target : Multiset V) :
    Splits G (.erase x) source target ↔ source = {x} + target := by
  constructor
  · rintro ⟨rest, sourceEq, targetEq⟩
    change source = (x ::ₘ 0) + 0 + rest at sourceEq
    change target = 0 + 0 + rest at targetEq
    rw [Multiset.zero_add, Multiset.zero_add] at targetEq
    rw [sourceEq, targetEq, Multiset.add_zero]
    rfl
  · rintro rfl
    exact splits_erase_split G x target

variable {G}

/-- **An erasure is matched by the same erasure.**  Fresh configurations
bisimilar under the exact profile erase the same node, to fresh results that
are bisimilar one world later. -/
theorem erase_matched {point : World G} {first second : Multiset V}
    (bisimilar : ContextualCoalgebraBisimulation.Bisimilar (coalgebra (exact G)) point (fresh point first)
      (fresh point second)) (x : V) (rest : Multiset V) (split : first = {x} + rest) :
    ∃ rest', second = {x} + rest' ∧
      ContextualCoalgebraBisimulation.Bisimilar (coalgebra (exact G)) (next point) (fresh (next point) rest)
        (fresh (next point) rest') := by
  have emitted : Emits (exact G) (fresh point first) (entryArrow point (.forward, .erase x))
      (fresh (next point) rest) := by
    refine ⟨(.forward, .erase x), (.forward, .erase x), [], rfl, rfl, ?_, rfl, rfl⟩
    change Splits G (.erase x) ((Context.one G).apply first) rest
    rw [Context.apply_one, split]
    exact splits_erase_split G x rest
  obtain ⟨matching, available, related⟩ :=
    (ContextualCoalgebraBisimulation.bisimilar_isBisimulation (coalgebra (exact G))).forth bisimilar
      ⟨next point, entryArrow point (.forward, .erase x)⟩ emitted
  obtain ⟨written, actual, restScript, scriptEq, admitted, moves, originEq, childScript⟩ := available
  have writtenEq : written = (.forward, .erase x) := (List.cons.inj scriptEq).1.symm
  change actual = written at admitted
  rw [admitted, writtenEq] at moves
  change Splits G (.erase x) ((Context.one G).apply second) matching.live at moves
  rw [Context.apply_one, splits_erase_iff] at moves
  have restNil : restScript = [] := (List.cons.inj scriptEq).2.symm
  have freshMatching : matching = fresh (next point) matching.live :=
    Placed.ext' rfl originEq (childScript.trans restNil)
  rw [freshMatching] at related
  exact ⟨matching.live, moves, related⟩

theorem card_zero_of_bisimilar {point : World G} {second : Multiset V}
    (bisimilar : ContextualCoalgebraBisimulation.Bisimilar (coalgebra (exact G)) point (fresh point 0)
      (fresh point second)) : second = 0 := by
  induction second using Quot.inductionOn with
  | h list =>
      cases list with
      | nil => rfl
      | cons y rest =>
          exfalso
          obtain ⟨rest', split, _⟩ := erase_matched
            (ContextualCoalgebraBisimulation.bisimilar_symm (coalgebra (exact G)) bisimilar) y rest
            (coe_cons_eq y rest)
          have sizes := congrArg Multiset.card split
          rw [Multiset.card_zero, Multiset.card_add] at sizes
          change 0 = Multiset.card (y ::ₘ 0) + _ at sizes
          rw [Multiset.card_cons] at sizes
          omega

theorem eq_of_fresh_bisimilar_list : ∀ (list : List V) (point : World G) (second : Multiset V),
    ContextualCoalgebraBisimulation.Bisimilar (coalgebra (exact G)) point (fresh point (list : Multiset V))
      (fresh point second) → (list : Multiset V) = second
  | [], _, _, bisimilar => (card_zero_of_bisimilar bisimilar).symm
  | x :: rest, point, second, bisimilar => by
      obtain ⟨rest', split, related⟩ := erase_matched bisimilar x rest (coe_cons_eq x rest)
      rw [split, coe_cons_eq, eq_of_fresh_bisimilar_list rest (next point) rest' related]

/-- **With the exact profile, fresh configurations are bisimilar exactly when
they are equal**, already without readings. -/
theorem fresh_bisimilar_iff_eq (point : World G) (first second : Multiset V) :
    ContextualCoalgebraBisimulation.Bisimilar (coalgebra (exact G)) point (fresh point first)
        (fresh point second) ↔ first = second := by
  constructor
  · exact Quot.inductionOn first (fun list => eq_of_fresh_bisimilar_list list point second)
  · rintro rfl
    exact ContextualCoalgebraBisimulation.bisimilar_refl (coalgebra (exact G)) point _

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)
  (R : NodeReadings K V)

/-- **With the exact profile the observed kernel of fresh configurations is
equality.** -/
theorem fresh_observed_iff_eq (point : World G) (first second : Multiset V) :
    ObservedBisimilar (exact G) K R point (fresh point first) (fresh point second) ↔ first = second := by
  constructor
  · intro related
    exact (fresh_bisimilar_iff_eq point first second).mp (bisimilar_of_observed (exact G) K R related)
  · rintro rfl
    exact ⟨fun _ => Eq, ⟨ContextualCoalgebraBisimulation.equality_isBisimulation (coalgebra (exact G)),
      fun {_ _ _} same _ => by rw [same]⟩, rfl⟩

end Faithful

/-! ## Descent along an observation -/

section Descent

universe u e

variable {X : Type u}

/-- **The predecessor box descends exactly under past matching**: for a setoid
of states, the predecessor box of every invariant predicate is invariant
exactly when incoming steps match modulo the setoid. -/
theorem box_descends_iff_pastMatching (A : ReductionSpan.{u, e} X) (equations : Setoid X) :
    (∀ predicate : X → Prop, (∀ ⦃left right⦄, equations.r left right → (predicate left ↔ predicate right)) →
      ∀ ⦃left right⦄, equations.r left right →
        (derivedBox A predicate left ↔ derivedBox A predicate right)) ↔
      PastMatching A equations := by
  constructor
  · intro descends left right related event targetEq
    let incoming : X → Prop := fun state =>
      ∃ matched : A.Edge, A.target matched = right ∧ equations.r state (A.source matched)
    have invariant : ∀ ⦃first second⦄, equations.r first second → (incoming first ↔ incoming second) := by
      intro first second same
      constructor
      · rintro ⟨matched, matchedTarget, sourceRelated⟩
        exact ⟨matched, matchedTarget, equations.iseqv.trans (equations.iseqv.symm same) sourceRelated⟩
      · rintro ⟨matched, matchedTarget, sourceRelated⟩
        exact ⟨matched, matchedTarget, equations.iseqv.trans same sourceRelated⟩
    have atRight : derivedBox A incoming right := fun matched matchedTarget =>
      ⟨matched, matchedTarget, equations.iseqv.refl _⟩
    exact ((descends incoming invariant related).mpr atRight) event targetEq
  · intro matching predicate invariant left right related
    constructor
    · intro holds event targetEq
      obtain ⟨matched, matchedTarget, sourceRelated⟩ :=
        matching (equations.iseqv.symm related) event targetEq
      exact (invariant sourceRelated).mpr (holds matched matchedTarget)
    · intro holds event targetEq
      obtain ⟨matched, matchedTarget, sourceRelated⟩ := matching related event targetEq
      exact (invariant sourceRelated).mpr (holds matched matchedTarget)

/-- **The future diamond descends exactly under future matching.** -/
theorem diamond_descends_iff_futureMatching (A : ReductionSpan.{u, e} X) (equations : Setoid X) :
    (∀ predicate : X → Prop, (∀ ⦃left right⦄, equations.r left right → (predicate left ↔ predicate right)) →
      ∀ ⦃left right⦄, equations.r left right →
        (derivedDiamond A predicate left ↔ derivedDiamond A predicate right)) ↔
      FutureMatching A equations := by
  constructor
  · intro descends left right related event sourceEq
    let near : X → Prop := fun state => equations.r state (A.target event)
    have invariant : ∀ ⦃first second⦄, equations.r first second → (near first ↔ near second) :=
      fun _ _ same => ⟨fun close => equations.iseqv.trans (equations.iseqv.symm same) close,
        fun close => equations.iseqv.trans same close⟩
    obtain ⟨matched, matchedSource, holds⟩ :=
      (descends near invariant related).mp ⟨event, sourceEq, equations.iseqv.refl _⟩
    exact ⟨matched, matchedSource, equations.iseqv.symm holds⟩
  · intro matching predicate invariant left right related
    constructor
    · rintro ⟨event, sourceEq, holds⟩
      obtain ⟨matched, matchedSource, targetRelated⟩ := matching related event sourceEq
      exact ⟨matched, matchedSource, (invariant targetRelated).mp holds⟩
    · rintro ⟨event, sourceEq, holds⟩
      obtain ⟨matched, matchedSource, targetRelated⟩ := matching (equations.iseqv.symm related) event sourceEq
      exact ⟨matched, matchedSource, (invariant targetRelated).mp holds⟩

end Descent

/-! ## Authored dictionaries and material values -/

section Codings

/-- A natural number as a finite chain. -/
def natCoding : ArgumentCoding ℕ where
  graph := OutcomeLabels.chainGraph
  injective := by
    intro first second same
    change HSet.mk (OutcomeLabels.chainGraph first) = HSet.mk (OutcomeLabels.chainGraph second) at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact OutcomeLabels.chainValue_injective same

/-- Pairs as material pairs. -/
def pairCoding {A B : Type} (first : ArgumentCoding A) (second : ArgumentCoding B) :
    ArgumentCoding (A × B) where
  graph value := AccessiblePointedGraph.kpairGraph (first.graph value.1) (second.graph value.2)
  injective := by
    rintro ⟨a, b⟩ ⟨c, d⟩ same
    change HSet.mk (AccessiblePointedGraph.kpairGraph (first.graph a) (second.graph b)) =
      HSet.mk (AccessiblePointedGraph.kpairGraph (first.graph c) (second.graph d)) at same
    rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
    obtain ⟨left, right⟩ := HSet.kpair_inj.mp same
    rw [first.injective left, second.injective right]

/-- A coding along an injective map. -/
def comapCoding {A B : Type} (coding : ArgumentCoding B) (f : A → B) (injective : Function.Injective f) :
    ArgumentCoding A where
  graph value := coding.graph (f value)
  injective _ _ same := injective (coding.injective same)

/-- The index of a direction. -/
def directionIndex : Direction → ℕ
  | .forward => 0
  | .backward => 1

theorem directionIndex_injective : Function.Injective directionIndex := by
  intro first second same
  cases first <;> cases second <;> first | rfl | exact absurd same (by decide)

/-- An event as its kind and the list of its nodes. -/
def eventView : Event V → ℕ × List V
  | .evolve x => (0, [x])
  | .fork x => (1, [x])
  | .merge x y => (2, [x, y])
  | .erase x => (3, [x])

theorem eventView_injective : Function.Injective (eventView (V := V)) := by
  intro first second same
  have tags := congrArg Prod.fst same
  have nodes := congrArg Prod.snd same
  cases first <;> cases second <;> simp only [eventView] at tags nodes <;> (try (exfalso; omega))
  all_goals simp only [List.cons.injEq, and_true] at nodes
  all_goals first
    | (subst nodes; rfl)
    | (obtain ⟨firstNode, secondNode⟩ := nodes; subst firstNode; subst secondNode; rfl)

/-- A two-sided entry as its direction and its event. -/
def entryCoding (nodes : ArgumentCoding V) : ArgumentCoding (Entry V) :=
  comapCoding (pairCoding natCoding (pairCoding natCoding (ArgumentCoding.lists nodes)))
    (fun entry => (directionIndex entry.1, eventView entry.2)) (by
      intro first second same
      obtain ⟨directions, events⟩ := Prod.mk.inj same
      exact Prod.ext (directionIndex_injective directions) (eventView_injective events))

/-- **A context as its renaming along the listing and its authored frame.** -/
def contextCoding (nodes : ArgumentCoding V) (L : Listing V) : ArgumentCoding (Context G) :=
  comapCoding (pairCoding (ArgumentCoding.lists nodes) (ArgumentCoding.lists nodes))
    (fun context => (L.nodes.map context.rename.map, context.frame)) (by
      intro first second same
      obtain ⟨renamings, frames⟩ := Prod.mk.inj same
      have pointwise := List.map_inj_left.mp renamings
      exact Context.ext (funext fun x => pointwise x (L.complete x)) frames)

variable (G)

/-- A world as its length. -/
def worldCoding : ArgumentCoding (World G) :=
  comapCoding natCoding World.length (by
    rintro ⟨first⟩ ⟨second⟩ same
    cases same
    rfl)

variable {G}

/-- **An arrow as its script and its context.** -/
def arrowCoding (nodes : ArgumentCoding V) (L : Listing V) (first second : World G) :
    ArgumentCoding (first ⟶ second) :=
  comapCoding (pairCoding (ArgumentCoding.lists (entryCoding nodes)) (contextCoding nodes L))
    (fun arrow => (Arrow.script arrow, Arrow.context arrow)) (by
      intro earlier later same
      obtain ⟨scripts, contexts⟩ := Prod.mk.inj same
      exact Arrow.ext' scripts contexts)

/-- The index of a reading. -/
def readingIndex : Reading → ℕ
  | .result => 0
  | .fault => 1
  | .cost => 2

theorem readingIndex_injective : Function.Injective readingIndex := by
  intro first second same
  cases first <;> cases second <;> first | rfl | exact absurd same (by decide)

/-- A declared reading as its name and its value. -/
def atomCoding {W : Type} (values : ArgumentCoding W) : ArgumentCoding (Reading × W) :=
  pairCoding (comapCoding natCoding readingIndex readingIndex_injective) values

end Codings

section Material

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)
  (R : NodeReadings K V) (nodes : ArgumentCoding V) (L : Listing V) (values : ArgumentCoding W)

/-- **The material value of a placed configuration**, with its declared
readings. -/
abbrev value (state : ContextualCoalgebraLabelledGraph.State (placed G)) : HSet.{0} :=
  ContextualObservedCoalgebra.value (coalgebra profile) (observes K R) (worldCoding G) (arrowCoding nodes L)
    (atomCoding values) state

/-- **The kernel theorem**: material equality at one world is the observed
kernel, one stable bisimulation that preserves every declared reading. -/
theorem value_eq_iff (point : World G) (left right : Placed point) :
    value profile K R nodes L values ⟨point, left⟩ = value profile K R nodes L values ⟨point, right⟩ ↔
      ObservedBisimilar profile K R point left right :=
  ContextualObservedCoalgebra.value_eq_iff (coalgebra profile) (observes K R) (worldCoding G)
    (arrowCoding nodes L) (atomCoding values) point left right

/-- **Every declared reading is a material row.** -/
theorem reading_row_iff (state : ContextualCoalgebraLabelledGraph.State (placed G)) (observation : Reading)
    (number : W) :
    HSet.kpair ((ContextualObservedCoalgebra.readings (coalgebra profile) (observes K R) (worldCoding G)
        (arrowCoding nodes L) (atomCoding values)).taggedReading (.inl (observation, number))) ∅ ∈
      value profile K R nodes L values state ↔ number = reading K R observation state.2.live :=
  ContextualObservedCoalgebra.observation_row_iff (coalgebra profile) (observes K R) (worldCoding G)
    (arrowCoding nodes L) (atomCoding values) state (observation, number)

/-- The material observation of configurations placed fresh at one world. -/
def freshValue (point : World G) (live : Multiset V) : HSet.{0} :=
  value profile K R nodes L values ⟨point, fresh point live⟩

/-- The kernel of the fresh observation, as a setoid. -/
def freshKernel (point : World G) : Setoid (Multiset V) where
  r first second := freshValue profile K R nodes L values point first =
    freshValue profile K R nodes L values point second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- **Declared readings descend in every profile.** -/
theorem reading_descends (point : World G) (observation : Reading) (number : W) :
    PredicateDescends (freshValue profile K R nodes L values point)
      (fun live => reading K R observation live = number) := by
  refine ⟨fun observed => ∃ live, freshValue profile K R nodes L values point live = observed ∧
    reading K R observation live = number, fun live => ⟨?_, fun holds => ⟨live, rfl, holds⟩⟩⟩
  rintro ⟨other, same, holds⟩
  have related := (value_eq_iff profile K R nodes L values point _ _).mp same
  exact (readings_eq_of_observed profile K R related observation).symm.trans holds

/-- **A native predicate of configurations descends along the fresh observation
exactly when it is invariant under the exact kernel.** -/
theorem native_descends_iff (point : World G) (predicate : Multiset V → Prop) :
    PredicateDescends (freshValue profile K R nodes L values point) predicate ↔
      ∀ first second, ObservedBisimilar profile K R point (fresh point first) (fresh point second) →
        (predicate first ↔ predicate second) := by
  constructor
  · rintro ⟨observed, reflects⟩ first second related
    have same : freshValue profile K R nodes L values point first =
        freshValue profile K R nodes L values point second :=
      (value_eq_iff profile K R nodes L values point _ _).mpr related
    have atSecond := reflects second
    rw [← same] at atSecond
    exact (reflects first).symm.trans atSecond
  · intro invariant
    refine ⟨fun observed => ∃ live, freshValue profile K R nodes L values point live = observed ∧ predicate live,
      fun live => ⟨?_, fun holds => ⟨live, rfl, holds⟩⟩⟩
    rintro ⟨other, same, holds⟩
    exact (invariant other live ((value_eq_iff profile K R nodes L values point _ _).mp same)).mp holds

/-- **The predecessor box descends along the fresh observation exactly when
incoming steps match modulo its kernel.** -/
theorem fresh_box_descends_iff (point : World G) :
    (∀ predicate : Multiset V → Prop,
      (∀ ⦃left right⦄, (freshKernel profile K R nodes L values point).r left right →
        (predicate left ↔ predicate right)) →
      ∀ ⦃left right⦄, (freshKernel profile K R nodes L values point).r left right →
        (derivedBox (eventSpan G) predicate left ↔ derivedBox (eventSpan G) predicate right)) ↔
      PastMatching (eventSpan G) (freshKernel profile K R nodes L values point) :=
  box_descends_iff_pastMatching (eventSpan G) _

/-- **With the exact profile the fresh observation is injective**, so every
predicate of configurations descends. -/
theorem exact_freshValue_injective (point : World G) :
    Function.Injective (freshValue (exact G) K R nodes L values point) := fun first second same =>
  (fresh_observed_iff_eq K R point first second).mp
    ((value_eq_iff (exact G) K R nodes L values point _ _).mp same)

theorem exact_predicate_descends (point : World G) (predicate : Multiset V → Prop) :
    PredicateDescends (freshValue (exact G) K R nodes L values point) predicate :=
  ⟨fun observed => ∃ live, freshValue (exact G) K R nodes L values point live = observed ∧ predicate live,
    fun live => ⟨fun ⟨_, same, holds⟩ =>
      (exact_freshValue_injective K R nodes L values point same) ▸ holds, fun holds => ⟨live, rfl, holds⟩⟩⟩

/-- **With the exact profile the predecessor box descends**: incoming steps
match modulo the kernel of the fresh observation. -/
theorem exact_pastMatching (point : World G) :
    PastMatching (eventSpan G) (freshKernel (exact G) K R nodes L values point) := by
  intro left right related event targetEq
  have same := exact_freshValue_injective K R nodes L values point related
  exact ⟨event, targetEq.trans same, rfl⟩

end Material

/-! ## The future-only profile on configurations of one size -/

section FutureOnly

variable (G)

/-- A forward step of every kind from every configuration of the same size, to
a result of the same size. -/
theorem splits_same_size {event : Event V} {source target : Multiset V}
    (splits : Splits G event source target) :
    ∀ (list : List V), Multiset.card (list : Multiset V) = Multiset.card source →
      ∃ event' target', Splits G event' (list : Multiset V) target' ∧
        Multiset.card target = Multiset.card target' := by
  obtain ⟨rest, rfl, rfl⟩ := splits
  intro list sizes
  rw [Multiset.coe_card, Multiset.card_add, Multiset.card_add] at sizes
  cases event with
  | evolve x =>
      change list.length = Multiset.card (x ::ₘ 0) + Multiset.card (0 : Multiset V) + _ at sizes
      rw [Multiset.card_cons, Multiset.card_zero] at sizes
      obtain ⟨y, others, rfl⟩ : ∃ y others, list = y :: others := by
        cases list with
        | nil => rw [List.length_nil] at sizes; exfalso; omega
        | cons y others => exact ⟨y, others, rfl⟩
      refine ⟨.evolve y, {G.evolve y} + ↑others, ⟨others, ?_, ?_⟩, ?_⟩
      · change _ = (y ::ₘ 0) + 0 + _
        rw [Multiset.add_zero, coe_cons_eq]
        rfl
      · change _ = (G.evolve y ::ₘ 0) + 0 + _
        rw [Multiset.add_zero]
        rfl
      · change Multiset.card ((G.evolve x ::ₘ 0) + 0 + rest) =
          Multiset.card ((G.evolve y ::ₘ 0) + ((others : List V) : Multiset V))
        simp only [Multiset.add_zero, Multiset.card_add, Multiset.card_cons, Multiset.card_zero,
          Multiset.coe_card]
        simp only [List.length_cons] at sizes
        omega
  | fork x =>
      change list.length = Multiset.card (0 : Multiset V) + Multiset.card (x ::ₘ 0) + _ at sizes
      rw [Multiset.card_cons, Multiset.card_zero] at sizes
      obtain ⟨y, others, rfl⟩ : ∃ y others, list = y :: others := by
        cases list with
        | nil => rw [List.length_nil] at sizes; exfalso; omega
        | cons y others => exact ⟨y, others, rfl⟩
      refine ⟨.fork y, {y} + ({y} + ↑others), ⟨others, ?_, ?_⟩, ?_⟩
      · change _ = 0 + (y ::ₘ 0) + _
        rw [Multiset.zero_add, coe_cons_eq]
        rfl
      · change _ = (y ::ₘ 0) + (y ::ₘ 0) + _
        rw [Multiset.add_assoc]
        rfl
      · change Multiset.card ((x ::ₘ 0) + (x ::ₘ 0) + rest) =
          Multiset.card ((y ::ₘ 0) + ((y ::ₘ 0) + ((others : List V) : Multiset V)))
        simp only [Multiset.card_add, Multiset.card_cons, Multiset.card_zero, Multiset.coe_card]
        simp only [List.length_cons] at sizes
        omega
  | merge x y =>
      change list.length = Multiset.card (x ::ₘ y ::ₘ 0) + Multiset.card (0 : Multiset V) + _ at sizes
      rw [Multiset.card_cons, Multiset.card_cons, Multiset.card_zero] at sizes
      obtain ⟨u, w, others, rfl⟩ : ∃ u w others, list = u :: w :: others := by
        cases list with
        | nil => rw [List.length_nil] at sizes; exfalso; omega
        | cons u tail =>
            cases tail with
            | nil => rw [List.length_cons, List.length_nil] at sizes; exfalso; omega
            | cons w others => exact ⟨u, w, others, rfl⟩
      refine ⟨.merge u w, {G.merge u w} + ↑others, ⟨others, ?_, ?_⟩, ?_⟩
      · change _ = (u ::ₘ w ::ₘ 0) + 0 + _
        rw [Multiset.add_zero]
        rfl
      · change _ = (G.merge u w ::ₘ 0) + 0 + _
        rw [Multiset.add_zero]
        rfl
      · change Multiset.card ((G.merge x y ::ₘ 0) + 0 + rest) =
          Multiset.card ((G.merge u w ::ₘ 0) + ((others : List V) : Multiset V))
        simp only [Multiset.add_zero, Multiset.card_add, Multiset.card_cons, Multiset.card_zero,
          Multiset.coe_card]
        simp only [List.length_cons] at sizes
        omega
  | erase x =>
      change list.length = Multiset.card (x ::ₘ 0) + Multiset.card (0 : Multiset V) + _ at sizes
      rw [Multiset.card_cons, Multiset.card_zero] at sizes
      obtain ⟨y, others, rfl⟩ : ∃ y others, list = y :: others := by
        cases list with
        | nil => rw [List.length_nil] at sizes; exfalso; omega
        | cons y others => exact ⟨y, others, rfl⟩
      refine ⟨.erase y, ↑others, splits_erase_split G y others |> fun splits => by
        rw [coe_cons_eq]
        exact splits, ?_⟩
      change Multiset.card (0 + 0 + rest) = Multiset.card ((others : List V) : Multiset V)
      simp only [Multiset.zero_add, Multiset.coe_card]
      simp only [List.length_cons] at sizes
      omega

variable {G}

/-- Placed configurations of one shape: the same origin, scripts with the same
directions, and configurations of the same size. -/
def SameShape (point : World G) (left right : Placed point) : Prop :=
  left.origin = right.origin ∧ left.script.map Prod.fst = right.script.map Prod.fst ∧
    Multiset.card left.live = Multiset.card right.live

theorem script_directions (context : Context G) (script : List (Entry V)) :
    (context.script script).map Prod.fst = script.map Prod.fst := by
  unfold Context.script
  rw [List.map_map]
  rfl

theorem card_apply (context : Context G) (live : Multiset V) :
    Multiset.card (context.apply live) = Multiset.card live + (context.frame).length := by
  unfold Context.apply
  rw [Multiset.card_add, Multiset.card_map, Multiset.coe_card]

theorem sameShape_transport {first second : World G} (arrow : first ⟶ second) {left right : Placed first}
    (shape : SameShape first left right) : SameShape second (transport arrow left) (transport arrow right) := by
  obtain ⟨origins, directions, sizes⟩ := shape
  refine ⟨origins, ?_, ?_⟩
  · rw [transport_script, transport_script, List.map_append, List.map_append, script_directions,
      script_directions, directions]
  · rw [transport_live, transport_live, card_apply, card_apply, sizes]

theorem sameShape_symm {point : World G} {left right : Placed point} (shape : SameShape point left right) :
    SameShape point right left :=
  ⟨shape.1.symm, shape.2.1.symm, shape.2.2.symm⟩

theorem sameShape_advances {point : World G} {left right child : Placed point}
    (shape : SameShape point left right) (advances : Advances (futureOnly G) left child) :
    ∃ matching, Advances (futureOnly G) right matching ∧ SameShape point child matching := by
  obtain ⟨written, actual, rest, scriptEq, ⟨writtenForward, actualForward⟩, moves, originEq, childScript⟩ :=
    advances
  obtain ⟨origins, directions, sizes⟩ := shape
  obtain ⟨direction, event⟩ := actual
  change direction = .forward at actualForward
  subst actualForward
  obtain ⟨written', rest', rightScript⟩ : ∃ written' rest', right.script = written' :: rest' := by
    cases rightScript : right.script with
    | nil =>
        rw [scriptEq, rightScript] at directions
        cases directions
    | cons written' rest' => exact ⟨written', rest', rfl⟩
  rw [scriptEq, rightScript, List.map_cons, List.map_cons] at directions
  obtain ⟨heads, tails⟩ := List.cons.inj directions
  obtain ⟨event', result', moved, resultSize⟩ := Quot.inductionOn right.live
    (motive := fun live => Multiset.card live = Multiset.card left.live →
      ∃ event' target', Splits G event' live target' ∧ Multiset.card child.live = Multiset.card target')
    (fun list same => splits_same_size G moves list same) sizes.symm
  have lengths := right.length_eq
  rw [rightScript, List.length_cons] at lengths
  refine ⟨⟨result', right.origin + 1, rest', by omega⟩, ⟨written', (.forward, event'), rest', rightScript,
    ⟨heads ▸ writtenForward, rfl⟩, moved, rfl, rfl⟩, ?_⟩
  refine ⟨by rw [originEq, origins], by rw [childScript]; exact tails, resultSize⟩

/-- **In the future-only profile, one shape is a contextual bisimulation.** -/
theorem sameShape_isBisimulation :
    ContextualCoalgebraBisimulation.IsBisimulation (coalgebra (futureOnly G)) (SameShape (G := G)) where
  stable step _ _ shape := sameShape_transport step shape
  forth {_ _ _} shape future {_} available := sameShape_advances (sameShape_transport future.2 shape) available
  back {_ _ _} shape future {_} available := by
    obtain ⟨matching, matched, matchedShape⟩ :=
      sameShape_advances (sameShape_transport future.2 (sameShape_symm shape)) available
    exact ⟨matching, matched, sameShape_symm matchedShape⟩

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)
  (R : NodeReadings K V)

/-- **In the future-only profile, with readings that depend only on size,
configurations of one size placed fresh at one world are observed alike.** -/
theorem futureOnly_fresh_observed (sizeReadings : ∀ observation (first second : Multiset V),
      Multiset.card first = Multiset.card second →
        reading K R observation first = reading K R observation second)
    (point : World G) {first second : Multiset V} (sizes : Multiset.card first = Multiset.card second) :
    ObservedBisimilar (futureOnly G) K R point (fresh point first) (fresh point second) := by
  refine ⟨SameShape (G := G), ⟨sameShape_isBisimulation, ?_⟩, rfl, rfl, sizes⟩
  intro _ left right shape atom
  change atom.2 = reading K R atom.1 left.live ↔ atom.2 = reading K R atom.1 right.live
  rw [sizeReadings atom.1 left.live right.live shape.2.2]

end FutureOnly

end Mettapedia.GSLT.Distinction.HistoryContextTwoSided
