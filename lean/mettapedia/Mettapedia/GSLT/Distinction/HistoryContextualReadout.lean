import Mettapedia.GSLT.Distinction.HistoryObserver
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadout
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraMaterialReadout

/-!
# The history grammar through the contextual coalgebra readouts

The contextual readouts (`ContextualEnumeratedCoalgebraReadout`,
`ContextualCoalgebraMaterialReadout`) read small contextual coalgebras over a
context category.  Their labelled-path contexts (`LabelledContextPaths.World`)
have lists of labels as arrows.  This module places the history grammar there,
with the code of each event as its label.

* **Placed configurations** (`Placed`, `states`).  A state at a world is a
  configuration together with the world it was placed at and the labelled path
  travelled since.  Transport along an arrow extends the path.
* **The history coalgebra** (`Emits`, `coalgebra`).  A placed configuration
  has a child along a future arrow when the path from its origin, followed by
  that arrow, starts with the code of an event that fires; the child is the
  result, placed one step after the origin, with the rest of the path.  The
  child predicate is closed under further arrows and natural in the context.
* **Retained receipts** (`receipts`).  The branch enumeration lists, for each
  future, the event that fired, its result and the rest of the path.  The
  constructed readout does not depend on it
  (`readout_receipts_independent`).
* **The two readouts** (`readout_eq_iff`, `material_eq_iff`,
  `material_contexts_eq`, `material_eq_iff_readout_eq`).  Both have exactly the
  contextual bisimilarity at one context as their kernel; material equality also
  fixes the context.
* **Events are kept** (`fresh_bisimilar_iff`, `material_fresh_eq_iff`,
  `fresh_child_row_iff`).  With an injective code, configurations placed fresh
  at one world have equal readings exactly when they are equal; the material
  value of a fresh configuration has the child row labelled by the one-event
  arrow of an event exactly when that event fires, with the value of its
  result.  Different events label different rows (`event_rows_distinct`).
* **An injective code** (`eventCode`, `eventCode_injective`): the kind and the
  nodes of an event, paired, from any injective index of nodes.
* **Without event labels only the size is kept** (`unlabelled_fresh_bisimilar_iff`).
  With one label for every event, fresh configurations are bisimilar exactly
  when they have the same number of nodes, and two receipts with one child are
  read alike (`unlabelled_receipts_one_child`).

**Where choice enters.**  The firing relation uses Mathlib's multiset erase and
subtraction, which carry `Classical.choice` (see `HistoryObserver`), and so does
every statement about the history coalgebra.  The readouts, the label and arrow
dictionaries and the bisimulation kernels they supply are choice-free.
`eventCode_injective` uses Mathlib's `Nat.pair_eq_pair`, which carries
`Classical.choice` through its square-root lemmas.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryContextualReadout

open _root_.CategoryTheory
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.TypeTheory.ContextualWitnessCover (NaturalHom)
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.LabelledContextPaths

/-! ## Placed configurations -/

section Placed

variable (V : Type)

/-- A configuration placed at an origin world, with the labelled path travelled
since. -/
structure Placed (point : World) where
  live : Multiset V
  origin : World
  path : origin ⟶ point

/-- Placed configurations as a functor on worlds: transport extends the path. -/
def states : World ⥤ Type where
  obj point := Placed V point
  map step := TypeCat.ofHom fun placed => ⟨placed.live, placed.origin, placed.path ≫ step⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro placed
    change (⟨placed.live, placed.origin, placed.path ≫ 𝟙 point⟩ : Placed V point) = placed
    rw [Category.comp_id]
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro placed
    change (⟨placed.live, placed.origin, placed.path ≫ (first ≫ second)⟩ : Placed V _) =
      ⟨placed.live, placed.origin, (placed.path ≫ first) ≫ second⟩
    rw [Category.assoc]

variable {V}

theorem states_map {first second : World} (step : first ⟶ second) (placed : Placed V first) :
    (states V).map step placed = ⟨placed.live, placed.origin, placed.path ≫ step⟩ := rfl

/-- A configuration placed fresh at a world. -/
def fresh (point : World) (live : Multiset V) : Placed V point := ⟨live, point, 𝟙 point⟩

end Placed

/-- The world one label later. -/
def next (point : World) : World := ⟨point.length + 1⟩

/-- The arrow of one label. -/
def oneStep (point : World) (label : ℕ) : point ⟶ next point := ⟨[label], rfl⟩

theorem path_comp_val {first second third : World} (earlier : first ⟶ second)
    (later : second ⟶ third) : (earlier ≫ later).val = earlier.val ++ later.val := rfl

/-! ## The history coalgebra -/

variable {V : Type} [DecidableEq V] (G : Grammar V) (code : Event V → ℕ)

/-- **A placed configuration emits a child along an arrow**: its path, then the
arrow, starts with the code of an event that fires; the child is the result,
placed one step after the origin with the rest of the path. -/
def Emits {point target : World} (state : Placed V point) (arrow : point ⟶ target)
    (child : Placed V target) : Prop :=
  ∃ event rest, (state.path ≫ arrow).val = code event :: rest ∧
    Fires G event state.live child.live ∧
    child.origin.length = state.origin.length + 1 ∧ child.path.val = rest

/-- The children of a placed configuration at every future. -/
def children (point : World) (state : Placed V point) :
    CoveredFuturePowerFamilies.Predicate (states V) point where
  holds argument := Emits G code state argument.1.2 argument.2
  closed {first second} move available := by
    obtain ⟨⟨step, triangle⟩, moved⟩ := move
    obtain ⟨event, rest, pathEq, fires, originEq, childPath⟩ := available
    refine ⟨event, rest ++ step.val, ?_, ?_, ?_, ?_⟩
    · rw [← triangle, ← Category.assoc, path_comp_val, pathEq]
      rfl
    · rw [← moved]
      exact fires
    · rw [← moved]
      exact originEq
    · rw [← moved]
      change (first.2.path ≫ step).val = rest ++ step.val
      rw [path_comp_val, childPath]

/-- **The retained event receipts**: for each future, the event that fired, its
result and the rest of the path. -/
def receipts (point : World) (state : Placed V point) :
    CoveredFuturePowerFamilies.Enumeration (children G code point state) where
  Carrier future := {receipt : Event V × Multiset V × List ℕ //
    (state.path ≫ future.2).val = code receipt.1 :: receipt.2.2 ∧
      Fires G receipt.1 state.live receipt.2.1}
  value future receipt := ⟨receipt.1.2.1, ⟨state.origin.length + 1⟩, ⟨receipt.1.2.2, by
    have lengths := (state.path ≫ future.2).property
    rw [receipt.2.1, List.length_cons] at lengths
    change state.origin.length + 1 + receipt.1.2.2.length = future.1.length
    omega⟩⟩
  covered future argument := by
    constructor
    · rintro ⟨event, rest, pathEq, fires, originEq, childPath⟩
      refine ⟨⟨(event, argument.live, rest), pathEq, fires⟩, ?_⟩
      obtain ⟨live, ⟨originLength⟩, path⟩ := argument
      change originLength = state.origin.length + 1 at originEq
      subst originEq
      change (⟨live, ⟨state.origin.length + 1⟩, ⟨rest, _⟩⟩ : Placed V future.1) = ⟨live, _, path⟩
      congr 1
      exact Subtype.ext childPath.symm
    · rintro ⟨⟨⟨event, live, rest⟩, pathEq, fires⟩, rfl⟩
      exact ⟨event, rest, pathEq, fires, rfl, rfl⟩

/-- **The history as a small contextual coalgebra.** -/
def coalgebra : NaturalHom (states V) (CoveredFuturePowerFamilies.family (states V)) where
  app point state := ⟨children G code point state, ⟨receipts G code point state⟩⟩
  naturality {first second} step state := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro argument
    change Emits G code state (step ≫ argument.1.2) argument.2 ↔
      Emits G code ⟨state.live, state.origin, state.path ≫ step⟩ argument.1.2 argument.2
    unfold Emits
    rw [Category.assoc]

theorem coalgebra_holds {point target : World} (state : Placed V point) (arrow : point ⟶ target)
    (child : Placed V target) :
    ((coalgebra G code).app point state).val.holds ⟨⟨target, arrow⟩, child⟩ ↔
      Emits G code state arrow child :=
  Iff.rfl

/-! ## The two readouts -/

/-- The constructed readout of the history coalgebra, from its event receipts. -/
abbrev readout : NaturalHom (states V) (ContextualSmallCoalgebraGenerators.quotient (D := World)) :=
  ContextualEnumeratedCoalgebraReadout.readout (states V) (coalgebra G code) (receipts G code)

/-- **The readout's kernel is contextual bisimilarity.** -/
theorem readout_eq_iff (point : World) (left right : Placed V point) :
    (readout G code).app point left = (readout G code).app point right ↔
      ContextualCoalgebraBisimulation.Bisimilar (coalgebra G code) point left right :=
  ContextualEnumeratedCoalgebraReadout.value_eq_iff (states V) (coalgebra G code) (receipts G code)
    point left right

/-- The readout is a coalgebra map into the separated recipient. -/
theorem readout_square :
    (coalgebra G code).comp (CoveredFuturePowerFunctor.imageHom (readout G code)) =
      (readout G code).comp ContextualSmallCoalgebraGenerators.quotientCoalgebra :=
  ContextualEnumeratedCoalgebraReadout.readout_square (states V) (coalgebra G code) (receipts G code)

/-- **The readout does not depend on the receipts**: the truth-subtype
enumeration gives the same readout. -/
theorem readout_receipts_independent :
    readout G code = ContextualEnumeratedCoalgebraReadout.readout (states V) (coalgebra G code)
      (fun point state => CoveredFuturePowerFamilies.smallEnumeration (children G code point state)) :=
  ContextualEnumeratedCoalgebraReadout.readout_enumeration_independent (states V) (coalgebra G code)
    (receipts G code) _

/-- The material reading of a placed configuration, with the labelled-path
dictionaries for worlds and arrows. -/
abbrev material (state : ContextualCoalgebraLabelledGraph.State (states V)) : HSet.{0} :=
  ContextualCoalgebraMaterialReadout.value (coalgebra G code) worlds arrows state

/-- **Material equality at one context is contextual bisimilarity.** -/
theorem material_eq_iff (point : World) (left right : Placed V point) :
    material G code ⟨point, left⟩ = material G code ⟨point, right⟩ ↔
      ContextualCoalgebraBisimulation.Bisimilar (coalgebra G code) point left right :=
  ContextualCoalgebraMaterialReadout.value_eq_iff (coalgebra G code) worlds arrows point left right

/-- **Material equality fixes the context.** -/
theorem material_contexts_eq {first second : ContextualCoalgebraLabelledGraph.State (states V)}
    (same : material G code first = material G code second) : first.1 = second.1 :=
  ContextualCoalgebraMaterialReadout.value_contexts_eq (coalgebra G code) worlds arrows same

/-- The two readouts identify the same placed configurations. -/
theorem material_eq_iff_readout_eq (point : World) (left right : Placed V point) :
    material G code ⟨point, left⟩ = material G code ⟨point, right⟩ ↔
      (readout G code).app point left = (readout G code).app point right :=
  (material_eq_iff G code point left right).trans (readout_eq_iff G code point left right).symm

/-! ## Fresh configurations -/

/-- A child emitted along one label by a fresh configuration is fresh. -/
theorem emitted_fresh {point : World} {live : Multiset V} {label : ℕ} {child : Placed V (next point)}
    (emitted : Emits G code (fresh point live) (oneStep point label) child) :
    child = fresh (next point) child.live := by
  obtain ⟨event, rest, pathEq, _, originEq, childPath⟩ := emitted
  change [label] = code event :: rest at pathEq
  have restNil : rest = [] := (List.cons.inj pathEq).2.symm
  obtain ⟨childLive, ⟨originLength⟩, path⟩ := child
  change originLength = point.length + 1 at originEq
  subst originEq
  subst restNil
  change (⟨childLive, ⟨point.length + 1⟩, path⟩ : Placed V (next point)) = ⟨childLive, next point, 𝟙 _⟩
  congr 1
  exact Subtype.ext childPath

/-- A fresh configuration emits the fresh result of every event that fires,
along the arrow of its code. -/
theorem emits_fresh {point : World} {live result : Multiset V} {event : Event V}
    (fires : Fires G event live result) :
    Emits G code (fresh point live) (oneStep point (code event)) (fresh (next point) result) :=
  ⟨event, [], rfl, fires, rfl, rfl⟩

/-- With an injective code, a fresh configuration emits along the arrow of an
event exactly the results of that event. -/
theorem emits_fresh_iff (injective : Function.Injective code) {point : World}
    {live result : Multiset V} {event : Event V} :
    Emits G code (fresh point live) (oneStep point (code event)) (fresh (next point) result) ↔
      Fires G event live result := by
  constructor
  · rintro ⟨event', rest, pathEq, fires, _, _⟩
    change [code event] = code event' :: rest at pathEq
    rw [injective (List.cons.inj pathEq).1]
    exact fires
  · exact emits_fresh G code

/-- No event fires on the empty configuration. -/
theorem not_fires_zero {event : Event V} {result : Multiset V} : ¬ Fires G event 0 result := by
  intro fires
  cases fires with
  | evolve member => exact Multiset.notMem_zero _ member
  | fork member => exact Multiset.notMem_zero _ member
  | @merge x y _ enabled =>
      exact Multiset.notMem_zero x (Multiset.mem_of_le enabled (by simp [pair] : x ∈ pair x y))
  | erase member => exact Multiset.notMem_zero _ member

/-- The configurations whose fresh placements are bisimilar somewhere. -/
def FreshBisimilar (left right : Multiset V) : Prop :=
  ∃ point, ContextualCoalgebraBisimulation.Bisimilar (coalgebra G code) point (fresh point left)
    (fresh point right)

theorem freshBisimilar_matchesErasures (injective : Function.Injective code) :
    MatchesErasures (G := G) (FreshBisimilar G code) := by
  rintro left right ⟨point, bisimilar⟩ x member
  have fires : Fires G (.erase x) left (left.erase x) := .erase member
  obtain ⟨matching, available, related⟩ :=
    (ContextualCoalgebraBisimulation.bisimilar_isBisimulation (coalgebra G code)).forth bisimilar
      ⟨next point, oneStep point (code (.erase x))⟩ (emits_fresh G code fires)
  obtain ⟨live', origin', path'⟩ := matching
  have freshMatching : (⟨live', origin', path'⟩ : Placed V (next point)) = fresh (next point) live' :=
    emitted_fresh G code available
  rw [freshMatching] at available related
  exact ⟨live', (emits_fresh_iff G code injective).mp available, next point, related⟩

/-- **With an injective code, fresh configurations are bisimilar exactly when
they are equal**: erasures count every node. -/
theorem fresh_bisimilar_iff (injective : Function.Injective code) (point : World)
    (left right : Multiset V) :
    ContextualCoalgebraBisimulation.Bisimilar (coalgebra G code) point (fresh point left)
        (fresh point right) ↔ left = right := by
  constructor
  · intro bisimilar
    refine eq_of_matchesErasures (G := G) (relation := FreshBisimilar G code)
      (freshBisimilar_matchesErasures G code injective) ?_ ⟨point, bisimilar⟩
    intro first second related x member
    obtain ⟨point', related⟩ := related
    obtain ⟨second', fires, related'⟩ := freshBisimilar_matchesErasures G code injective
      ⟨point', ContextualCoalgebraBisimulation.bisimilar_symm (coalgebra G code) related⟩ x member
    obtain ⟨point'', related''⟩ := related'
    exact ⟨second', fires, point'', ContextualCoalgebraBisimulation.bisimilar_symm (coalgebra G code)
      related''⟩
  · rintro rfl
    exact ContextualCoalgebraBisimulation.bisimilar_refl (coalgebra G code) point _

/-- **The material readout of fresh configurations is injective.** -/
theorem material_fresh_eq_iff (injective : Function.Injective code) (point : World)
    (left right : Multiset V) :
    material G code ⟨point, fresh point left⟩ = material G code ⟨point, fresh point right⟩ ↔
      left = right :=
  (material_eq_iff G code point _ _).trans (fresh_bisimilar_iff G code injective point left right)

/-- **The material value keeps the event of every child row**: the value of a
fresh configuration has the child row along the arrow of an event, with the
value of a fresh result, exactly when that event fires to that result. -/
theorem fresh_child_row_iff (injective : Function.Injective code) (point : World)
    (live result : Multiset V) (event : Event V) :
    HSet.kpair ((ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
        (.child point (next point) (oneStep point (code event))))
        (material G code ⟨next point, fresh (next point) result⟩) ∈
      material G code ⟨point, fresh point live⟩ ↔ Fires G event live result := by
  refine (ContextualCoalgebraMaterialReadout.child_row_iff (coalgebra G code) worlds arrows
    (oneStep point (code event)) (fresh point live) (fresh (next point) result)).trans ?_
  constructor
  · rintro ⟨matching, available, related⟩
    obtain ⟨live', origin', path'⟩ := matching
    have freshMatching : (⟨live', origin', path'⟩ : Placed V (next point)) = fresh (next point) live' :=
      emitted_fresh G code available
    rw [freshMatching] at available related
    rw [(fresh_bisimilar_iff G code injective _ result live').mp related]
    exact (emits_fresh_iff G code injective).mp available
  · intro fires
    exact ⟨fresh (next point) result, emits_fresh G code fires,
      ContextualCoalgebraBisimulation.bisimilar_refl (coalgebra G code) _ _⟩

omit [DecidableEq V] in
/-- **Different events label different rows.** -/
theorem event_rows_distinct (injective : Function.Injective code) (point : World)
    {first second : Event V} (different : first ≠ second) :
    (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
        (.child point (next point) (oneStep point (code first))) ≠
      (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
        (.child point (next point) (oneStep point (code second))) := by
  intro same
  have labelsEq := (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective same
  have arrowsEq : oneStep point (code first) = oneStep point (code second) := by
    injection labelsEq
  exact different (injective (List.cons.inj (congrArg Subtype.val arrowsEq)).1)

/-! ## An injective code of events -/

omit [DecidableEq V] in
/-- The code of an event from an injective index of nodes: its kind and its
nodes, paired. -/
def eventCode (index : V → ℕ) : Event V → ℕ
  | .evolve x => Nat.pair 0 (index x)
  | .fork x => Nat.pair 1 (index x)
  | .merge x y => Nat.pair 2 (Nat.pair (index x) (index y))
  | .erase x => Nat.pair 3 (index x)

omit [DecidableEq V] in
/-- **An injective index of nodes gives an injective code of events.** -/
theorem eventCode_injective {index : V → ℕ} (injective : Function.Injective index) :
    Function.Injective (eventCode index) := by
  intro first second same
  cases first <;> cases second <;> simp only [eventCode, Nat.pair_eq_pair] at same <;>
    first
      | omega
      | (obtain ⟨_, same⟩ := same; rw [injective same])
      | (obtain ⟨_, same⟩ := same
         obtain ⟨left, right⟩ := same
         rw [injective left, injective right])

/-! ## Without event labels -/

/-- One label for every event. -/
def unlabelled : Event V → ℕ := fun _ => 0

omit [DecidableEq V] in
theorem card_erase_add_one [DecidableEq V] {x : V} {live : Multiset V} (member : x ∈ live) :
    Multiset.card (live.erase x) + 1 = Multiset.card live := by
  rw [Multiset.card_erase_of_mem member]
  exact Nat.succ_pred_eq_of_pos (Multiset.card_pos_iff_exists_mem.mpr ⟨x, member⟩)

omit [DecidableEq V] in
theorem card_sub_pair_add_two [DecidableEq V] {x y : V} {live : Multiset V} (enabled : pair x y ≤ live) :
    Multiset.card (live - pair x y) + 2 = Multiset.card live := by
  have two := Multiset.card_le_card enabled
  rw [Multiset.card_sub enabled]
  simp only [pair, Multiset.card_cons, Multiset.card_zero] at two ⊢
  omega

theorem card_le_of_fires {event : Event V} {source target : Multiset V}
    (fires : Fires G event source target) : Multiset.card source ≤ Multiset.card target + 1 := by
  cases fires with
  | evolve member =>
      have := card_erase_add_one member
      rw [Multiset.card_cons]
      omega
  | fork member =>
      rw [Multiset.card_cons]
      omega
  | merge enabled =>
      have := card_sub_pair_add_two enabled
      rw [Multiset.card_cons]
      omega
  | erase member =>
      have := card_erase_add_one member
      omega

/-- **A step of one size is matched by a step of the same size from any
configuration of the same size.** -/
theorem fires_same_size {event : Event V} {left result : Multiset V}
    (fires : Fires G event left result) {right : Multiset V}
    (sameSize : Multiset.card left = Multiset.card right) :
    ∃ event' result', Fires G event' right result' ∧
      Multiset.card result = Multiset.card result' := by
  have someNode : ∀ {x : V}, x ∈ left → ∃ y, y ∈ right := by
    intro x member
    have positive := Multiset.card_pos_iff_exists_mem.mpr ⟨x, member⟩
    rw [sameSize] at positive
    exact Multiset.card_pos_iff_exists_mem.mp positive
  cases fires with
  | @evolve x _ member =>
      obtain ⟨y, memberRight⟩ := someNode member
      refine ⟨.evolve y, _, .evolve memberRight, ?_⟩
      have leftSize := card_erase_add_one member
      have rightSize := card_erase_add_one memberRight
      rw [Multiset.card_cons, Multiset.card_cons]
      omega
  | @fork x _ member =>
      obtain ⟨y, memberRight⟩ := someNode member
      refine ⟨.fork y, _, .fork memberRight, ?_⟩
      rw [Multiset.card_cons, Multiset.card_cons, sameSize]
  | @merge x y _ enabled =>
      obtain ⟨z, memberRight⟩ := someNode (Multiset.mem_of_le enabled (by simp [pair] : x ∈ pair x y))
      refine ⟨.erase z, _, .erase memberRight, ?_⟩
      have leftSize := card_sub_pair_add_two enabled
      have rightSize := card_erase_add_one memberRight
      rw [Multiset.card_cons]
      omega
  | @erase x _ member =>
      obtain ⟨z, memberRight⟩ := someNode member
      refine ⟨.erase z, _, .erase memberRight, ?_⟩
      have leftSize := card_erase_add_one member
      have rightSize := card_erase_add_one memberRight
      omega

/-- Placed configurations with one placement and the same size. -/
def SameShape (point : World) (left right : Placed V point) : Prop :=
  ∃ (origin : World) (path : origin ⟶ point) (first second : Multiset V),
    left = ⟨first, origin, path⟩ ∧ right = ⟨second, origin, path⟩ ∧
      Multiset.card first = Multiset.card second

theorem sameShape_forth {point : World} {left right : Placed V point}
    (related : SameShape point left right) (future : PowerClassPresheafBaseChange.Future.Objects point)
    {child : Placed V future.1}
    (available : Emits G unlabelled left future.2 child) :
    ∃ matching, Emits G unlabelled right future.2 matching ∧ SameShape future.1 child matching := by
  obtain ⟨origin, path, first, second, rfl, rfl, sameSize⟩ := related
  obtain ⟨event, rest, pathEq, fires, originEq, childPath⟩ := available
  obtain ⟨event', result', fires', resultSize⟩ := fires_same_size G fires sameSize
  refine ⟨⟨result', child.origin, child.path⟩, ⟨event', rest, pathEq, fires', originEq, childPath⟩,
    child.origin, child.path, child.live, result', rfl, rfl, resultSize⟩

/-- **Without event labels, sizes form a contextual bisimulation.** -/
theorem sameShape_isBisimulation :
    ContextualCoalgebraBisimulation.IsBisimulation (coalgebra G unlabelled) (SameShape (V := V)) where
  stable {_ _} step {_ _} related := by
    obtain ⟨origin, path, first, second, rfl, rfl, sameSize⟩ := related
    exact ⟨origin, path ≫ step, first, second, rfl, rfl, sameSize⟩
  forth {_ _ _} related future {_} available := sameShape_forth G related future available
  back {point left right} related future {child} available := by
    have symmetric : SameShape point right left := by
      obtain ⟨origin, path, first, second, rfl, rfl, sameSize⟩ := related
      exact ⟨origin, path, second, first, rfl, rfl, sameSize.symm⟩
    obtain ⟨matching, matched, shape⟩ := sameShape_forth G symmetric future available
    refine ⟨matching, matched, ?_⟩
    obtain ⟨origin, path, first, second, rfl, rfl, sameSize⟩ := shape
    exact ⟨origin, path, second, first, rfl, rfl, sameSize.symm⟩

theorem card_le_of_unlabelled_bisimilar : ∀ (size : ℕ) {point : World} {left right : Multiset V},
    Multiset.card left = size →
      ContextualCoalgebraBisimulation.Bisimilar (coalgebra G unlabelled) point (fresh point left)
        (fresh point right) → Multiset.card right ≤ size
  | 0, point, left, right, leftSize, bisimilar => by
      have empty : left = 0 := Multiset.card_eq_zero.mp leftSize
      subst empty
      by_contra positive
      have positive' : 0 < Multiset.card right := by omega
      obtain ⟨z, member⟩ := Multiset.card_pos_iff_exists_mem.mp positive'
      obtain ⟨matching, available, _⟩ :=
        (ContextualCoalgebraBisimulation.bisimilar_isBisimulation (coalgebra G unlabelled)).back
          bisimilar ⟨next point, oneStep point 0⟩
          (emits_fresh G unlabelled (Fires.erase (G := G) member))
      obtain ⟨event, _, _, fires, _, _⟩ := available
      exact not_fires_zero G fires
  | size + 1, point, left, right, leftSize, bisimilar => by
      obtain ⟨x, member⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card left)
      obtain ⟨matching, available, related⟩ :=
        (ContextualCoalgebraBisimulation.bisimilar_isBisimulation (coalgebra G unlabelled)).forth
          bisimilar ⟨next point, oneStep point 0⟩
          (emits_fresh G unlabelled (Fires.erase (G := G) member))
      obtain ⟨live', origin', path'⟩ := matching
      have freshMatching : (⟨live', origin', path'⟩ : Placed V (next point)) = fresh (next point) live' :=
        emitted_fresh G unlabelled available
      rw [freshMatching] at available related
      have erasedSize := card_erase_add_one member
      have smaller := card_le_of_unlabelled_bisimilar size (by omega) related
      obtain ⟨event, _, _, fires, _, _⟩ := available
      have step : Multiset.card right ≤ Multiset.card live' + 1 := card_le_of_fires G fires
      omega

/-- **Without event labels, fresh configurations are bisimilar exactly when they
have the same size.** -/
theorem unlabelled_fresh_bisimilar_iff (point : World) (left right : Multiset V) :
    ContextualCoalgebraBisimulation.Bisimilar (coalgebra G unlabelled) point (fresh point left)
        (fresh point right) ↔ Multiset.card left = Multiset.card right := by
  constructor
  · intro bisimilar
    exact le_antisymm
      (card_le_of_unlabelled_bisimilar G _ rfl
        (ContextualCoalgebraBisimulation.bisimilar_symm (coalgebra G unlabelled) bisimilar))
      (card_le_of_unlabelled_bisimilar G _ rfl bisimilar)
  · intro sameSize
    exact ContextualCoalgebraBisimulation.greatest (coalgebra G unlabelled)
      (sameShape_isBisimulation G) ⟨point, 𝟙 point, left, right, rfl, rfl, sameSize⟩

/-- **Two receipts, one child**: without event labels, erasing one of two copies
and merging them, when the merge is idempotent, are two retained receipts with
the same child. -/
theorem unlabelled_receipts_one_child (x : V) (idempotent : G.merge x x = x) (point : World) :
    ∃ first second : (receipts G unlabelled point (fresh point (pair x x))).Carrier
        ⟨next point, oneStep point 0⟩,
      first ≠ second ∧
        (receipts G unlabelled point (fresh point (pair x x))).value _ first =
          (receipts G unlabelled point (fresh point (pair x x))).value _ second := by
  have erased : Fires G (.erase x) (pair x x) (x ::ₘ 0) := by
    have fires := Fires.erase (G := G) (x := x) (live := pair x x) (by simp [pair])
    simpa [pair] using fires
  have merged : Fires G (.merge x x) (pair x x) (x ::ₘ 0) := by
    have fires := Fires.merge (G := G) (x := x) (y := x) (live := pair x x) le_rfl
    rwa [pair_sub_pair, idempotent] at fires
  refine ⟨⟨(.erase x, x ::ₘ 0, []), rfl, erased⟩, ⟨(.merge x x, x ::ₘ 0, []), rfl, merged⟩, ?_, rfl⟩
  intro same
  have events := congrArg (fun receipt => receipt.1.1) same
  cases events

end Mettapedia.GSLT.Distinction.HistoryContextualReadout
