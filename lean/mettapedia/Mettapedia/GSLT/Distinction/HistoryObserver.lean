import Mettapedia.GSLT.Distinction.HistoryIndependence
import Mettapedia.GSLT.Distinction.SpanTransport
import Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent

/-!
# The history grammar as an exact-value graded observer

`HistoryGrammar` presents the event grammar of the distinction calculus as a
GSLT of configurations, with the events labelling the steps (`eventSystem`).
This module presents that labelled system to the constructive graded layer
(`Constructive.PresentedSystem`) and to the exact-value observer of
`GradedValueObserver`.

* **Pasts are authored** (`unstep`, `unstep_eq_some_iff`, `unrun_eq_some_iff`).
  An event records the nodes it consumes, so the configuration it fired from
  is a function of the event and the configuration it reached, and a whole
  history is undone from its end.  Successor and predecessor lists
  (`successors`, `predecessors`) have at most one entry, and membership in
  either is exactly the firing relation (`mem_successors`, `mem_predecessors`).
* **Action coverage** (`stepAgreement`, `mem_allSuccessors`,
  `mem_allPredecessors`).  The steps of the history GSLT are exactly the
  authored actions; over a listed node set, one finite list holds exactly the
  successors and one exactly the predecessors of a configuration.
* **Readings** (`NodeReadings`, `reading`, `presented`).  Three readings in a
  constructive scale: the best `result` value among live nodes, the `fault`
  flag (whether a faulty node is live), and the `cost` meter, the extensive
  potential clamped to `[0, one]`.  The exact-value atoms of
  `GradedValueObserver` test them.
* **The observer separates configurations** (`gradedBisimilar_iff_eq`,
  `eventSystem_bisimilar_iff_eq`).  Erasures alone count every node, so graded
  bisimilarity, and plain bisimilarity of the event system, is equality.
* **Every finite-depth readout class retains the readings**
  (`value_eq_of_stateOf_eq`, `atom_stage_iff_at_depth`), for any presented
  system and without a stabilization certificate.
* **Histories are read exactly** (`val_chain`, `history_faults_iff`,
  `history_result`, `history_cost`).  The formula that follows a history's
  events reads `0` exactly when the history faults, and otherwise the
  discounted reading of its result.  An event cost that is the change of the
  node potential (assumed, `PotentialLaws`) sums along every history to the
  change of the cost meter between configurations within budget.
* **Branching profiles** (classical; `eventSystem_imageFiniteModulo`,
  `eventSystem_predecessorFiniteModulo`, `kindSystem`).  The event-labelled
  system branches finitely in both directions for every node type, so the
  two-sided Hennessy–Milner theorem applies (`twoSided_logicallyEquivalent_iff_eq`).
  A label that records only the kind of event loses the consumed nodes: its
  successors stay finite (`kindSystem_imageFiniteModulo`), but its pasts are
  finitely branching exactly when the node type is finite
  (`kindSystem_predecessorFiniteModulo_iff`).
* **Causal occurrences** (`CausalOccurrence`, `forgetCopies`).  An occurrence
  that also names which copy of its principal node it uses.  Every labelled
  step lifts to one (`forgetCopies_sourceOccurrenceLifts`), but labelled steps
  and the occurrences of the shared trace core (`enabled_eq_of_site_eq`) do not
  determine the copy; see `HistoryObserverControls`.

**Scope of costs.**  The local Livšic theorem
(`HistoryGrammar.exact_iff_locallyClosed`) characterizes exact *real* event
costs, with free fork and erasure.  `history_cost` assumes the potential laws
in the scale's group; it does not derive them, and says nothing about
nonnegative accounts (`LevelAccounts`: a nonnegative exact cost is zero).

**Where choice enters.**  `Multiset.erase`, multiset subtraction and the
decidable order and equality of multisets carry `Classical.choice` through
the list permutation lemmas that make them well defined
(`List.perm_cons_erase`, `List.Perm.erase`).  The firing relation `Fires`, the
history GSLT and every declaration over it therefore list `Classical.choice`.
The generic statements of this module (`value_eq_of_readout_eq`,
`value_eq_of_stateOf_eq`, `atom_stage_iff_at_depth`, `best` and its laws) do
not.  The finiteness profiles use `Set.Finite` and are classical.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryObserver

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.GradedValueObserver
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent

/-! ## Finite-depth readout classes retain the readings -/

section Retained

universe uS uAtom uLabel uObs uV

variable {W : Type uV} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
variable {S : GSLT.{uS}} {K : Scale W} (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)

/-- Equal readouts at any depth have equal readings: the atom of an observation
has depth zero. -/
theorem value_eq_of_readout_eq {depth : Nat} {left right : S.Term}
    (same : ObservedGradedFamilyDescent.readout Q depth left =
      ObservedGradedFamilyDescent.readout Q depth right) (observation : Q.Obs) :
    Q.value observation left = Q.value observation right :=
  congrFun same ⟨.atom observation, Nat.zero_le depth⟩

/-- **Every finite-depth readout class retains every reading**, without a
stabilization certificate. -/
theorem value_eq_of_stateOf_eq {depth : Nat} {left right : S.Term}
    (same : stateOf Q depth left = stateOf Q depth right) (observation : Q.Obs) :
    Q.value observation left = Q.value observation right :=
  value_eq_of_readout_eq Q
    ((classOf_eq_iff (ObservedGradedFamilyDescent.readout Q depth) left right).mp same) observation

/-- The exact-value atoms descend to the readout classes at every depth. -/
theorem atom_stage_iff_at_depth (depth : Nat) (atom : (valueSystem Q).Atom) (source : S.Term) :
    (stageSystem Q depth).observes atom (stateOf Q depth source) ↔
      (valueSystem Q).observes atom source := by
  constructor
  · rintro ⟨other, same, holds⟩
    change Q.value atom.1 other = atom.2 at holds
    change Q.value atom.1 source = atom.2
    exact (value_eq_of_stateOf_eq Q same atom.1).symm.trans holds
  · intro holds
    exact ⟨source, rfl, holds⟩

end Retained

/-! ## The largest reading among live nodes -/

section Best

universe uA uV

variable {α : Type uA} {W : Type uV} [Zero W] [LinearOrder W]

/-- One step of the maximum of readings. -/
def maxStep (f : α → W) : α → W → W := fun x acc => max (f x) acc

instance maxStep_leftCommutative (f : α → W) : LeftCommutative (maxStep f) :=
  ⟨fun _ _ _ => max_left_comm _ _ _⟩

/-- The largest reading of a live node, `0` on the empty configuration. -/
def best (f : α → W) (live : Multiset α) : W := Multiset.foldr (maxStep f) 0 live

@[simp] theorem best_zero (f : α → W) : best f 0 = 0 := Multiset.foldr_zero _ _

@[simp] theorem best_cons (f : α → W) (x : α) (live : Multiset α) :
    best f (x ::ₘ live) = max (f x) (best f live) :=
  Multiset.foldr_cons _ _ _ _

theorem best_nonneg (f : α → W) (live : Multiset α) : 0 ≤ best f live := by
  induction live using Multiset.induction_on with
  | empty => exact le_of_eq (best_zero f).symm
  | cons x rest inductionHypothesis =>
      rw [best_cons]
      exact inductionHypothesis.trans (le_max_right _ _)

theorem best_le (f : α → W) {bound : W} (nonneg : 0 ≤ bound) (each : ∀ x, f x ≤ bound)
    (live : Multiset α) : best f live ≤ bound := by
  induction live using Multiset.induction_on with
  | empty => rw [best_zero]; exact nonneg
  | cons x rest inductionHypothesis =>
      rw [best_cons]
      exact max_le (each x) inductionHypothesis

theorem le_best (f : α → W) {x : α} {live : Multiset α} (member : x ∈ live) : f x ≤ best f live := by
  induction live using Multiset.induction_on with
  | empty => exact absurd member (Multiset.notMem_zero x)
  | cons y rest inductionHypothesis =>
      rw [best_cons]
      rcases Multiset.mem_cons.mp member with same | member
      · rw [same]; exact le_max_left _ _
      · exact (inductionHypothesis member).trans (le_max_right _ _)

/-- With nonnegative readings, the largest reading is zero exactly when every
live reading is. -/
theorem best_eq_zero_iff (f : α → W) (nonneg : ∀ x, 0 ≤ f x) (live : Multiset α) :
    best f live = 0 ↔ ∀ x ∈ live, f x = 0 := by
  induction live using Multiset.induction_on with
  | empty => exact ⟨fun _ x member => absurd member (Multiset.notMem_zero x), fun _ => best_zero f⟩
  | cons y rest inductionHypothesis =>
      rw [best_cons]
      constructor
      · intro zero x member
        have restZero : best f rest = 0 :=
          le_antisymm ((le_max_right _ _).trans_eq zero) (best_nonneg f rest)
        rcases Multiset.mem_cons.mp member with same | member
        · rw [same]; exact le_antisymm ((le_max_left _ _).trans_eq zero) (nonneg y)
        · exact inductionHypothesis.mp restZero x member
      · intro all
        rw [all y (Multiset.mem_cons_self y rest),
          inductionHypothesis.mpr fun x member => all x (Multiset.mem_cons_of_mem member), max_self]

/-- With readings at most `bound`, the largest reading is `bound` exactly when
some live reading is. -/
theorem best_eq_iff_of_le (f : α → W) {bound : W} (positive : 0 < bound) (each : ∀ x, f x ≤ bound)
    (live : Multiset α) : best f live = bound ↔ ∃ x ∈ live, f x = bound := by
  induction live using Multiset.induction_on with
  | empty =>
      rw [best_zero]
      exact ⟨fun zero => absurd zero (ne_of_lt positive), fun ⟨x, member, _⟩ =>
        absurd member (Multiset.notMem_zero x)⟩
  | cons y rest inductionHypothesis =>
      rw [best_cons]
      constructor
      · intro attained
        rcases le_total (f y) (best f rest) with le | le
        · rw [max_eq_right le] at attained
          obtain ⟨x, member, holds⟩ := inductionHypothesis.mp attained
          exact ⟨x, Multiset.mem_cons_of_mem member, holds⟩
        · rw [max_eq_left le] at attained
          exact ⟨y, Multiset.mem_cons_self y rest, attained⟩
      · rintro ⟨x, member, holds⟩
        have below : best f rest ≤ bound := best_le f (le_of_lt positive) each rest
        rcases Multiset.mem_cons.mp member with same | member
        · rw [← same, holds]; exact max_eq_left below
        · rw [inductionHypothesis.mpr ⟨x, member, holds⟩]; exact max_eq_right (each y)

theorem best_replicate_succ (f : α → W) (x : α) (nonneg : 0 ≤ f x) :
    ∀ count : Nat, best f (Multiset.replicate (count + 1) x) = f x
  | 0 => by
      rw [Multiset.replicate_succ, best_cons, Multiset.replicate_zero, best_zero]
      exact max_eq_left nonneg
  | count + 1 => by
      rw [Multiset.replicate_succ, best_cons, best_replicate_succ f x nonneg count, max_self]

end Best

/-! ## Backward steps -/

variable {V : Type} [DecidableEq V] (G : Grammar V)

/-- **Undo one event** at a configuration: the configuration it fired from.  An
event names the nodes it consumes, so there is at most one. -/
def unstep : Event V → Multiset V → Option (Multiset V)
  | .evolve x, live =>
      if G.evolve x ∈ live then some (x ::ₘ live.erase (G.evolve x)) else none
  | .fork x, live => if x ∈ live.erase x then some (live.erase x) else none
  | .merge x y, live =>
      if G.merge x y ∈ live then some (pair x y + live.erase (G.merge x y)) else none
  | .erase x, live => some (x ::ₘ live)

/-- **Pasts are exact**: undoing an event gives exactly the configurations it
fires from. -/
theorem unstep_eq_some_iff (event : Event V) (source target : Multiset V) :
    unstep G event target = some source ↔ Fires G event source target := by
  cases event with
  | evolve x =>
      constructor
      · intro undone
        simp only [unstep] at undone
        split_ifs at undone with present
        cases undone
        have fires := Fires.evolve (G := G) (Multiset.mem_cons_self x (target.erase (G.evolve x)))
        rwa [Multiset.erase_cons_head, Multiset.cons_erase present] at fires
      · intro fires
        cases fires with
        | evolve member =>
            simp only [unstep, if_pos (Multiset.mem_cons_self _ _), Multiset.erase_cons_head,
              Multiset.cons_erase member]
  | fork x =>
      constructor
      · intro undone
        simp only [unstep] at undone
        split_ifs at undone with present
        cases undone
        have fires := Fires.fork (G := G) present
        rwa [Multiset.cons_erase (Multiset.mem_of_mem_erase present)] at fires
      · intro fires
        cases fires with
        | fork member =>
            simp only [unstep, Multiset.erase_cons_head, if_pos member]
  | merge x y =>
      constructor
      · intro undone
        simp only [unstep] at undone
        split_ifs at undone with present
        cases undone
        have fires := Fires.merge (G := G)
          (Multiset.le_add_right (pair x y) (target.erase (G.merge x y)))
        rwa [add_tsub_cancel_left, Multiset.cons_erase present] at fires
      · intro fires
        cases fires with
        | merge enabled =>
            simp only [unstep, if_pos (Multiset.mem_cons_self _ _), Multiset.erase_cons_head,
              add_tsub_cancel_of_le enabled]
  | erase x =>
      constructor
      · intro undone
        simp only [unstep] at undone
        cases undone
        have fires := Fires.erase (G := G) (Multiset.mem_cons_self x target)
        rwa [Multiset.erase_cons_head] at fires
      · intro fires
        cases fires with
        | erase member => simp only [unstep, Multiset.cons_erase member]

/-- An event fires to at most one configuration. -/
theorem fires_target_unique {event : Event V} {source target target' : Multiset V}
    (first : Fires G event source target) (second : Fires G event source target') :
    target = target' :=
  Option.some.inj (((step_eq_some_iff G event source target).mpr first).symm.trans
    ((step_eq_some_iff G event source target').mpr second))

/-- An event fires from at most one configuration. -/
theorem fires_source_unique {event : Event V} {source source' target : Multiset V}
    (first : Fires G event source target) (second : Fires G event source' target) :
    source = source' :=
  Option.some.inj (((unstep_eq_some_iff G event source target).mpr first).symm.trans
    ((unstep_eq_some_iff G event source' target).mpr second))

/-- Undo a history from its end, last event first. -/
def unrun : List (Event V) → Multiset V → Option (Multiset V)
  | [], live => some live
  | event :: rest, live => (unstep G event live).bind (unrun rest)

theorem labelledPath_append {first second : List (Event V)} :
    ∀ {source target : Multiset V}, LabelledPath G source (first ++ second) target ↔
      ∃ middle, LabelledPath G source first middle ∧ LabelledPath G middle second target := by
  induction first with
  | nil =>
      intro source target
      constructor
      · intro path
        exact ⟨source, .nil _, path⟩
      · rintro ⟨middle, start, path⟩
        cases start
        exact path
  | cons event rest inductionHypothesis =>
      intro source target
      constructor
      · intro path
        cases path with
        | cons fires path' =>
            obtain ⟨middle, start, finish⟩ := inductionHypothesis.mp path'
            exact ⟨middle, .cons fires start, finish⟩
      · rintro ⟨middle, start, finish⟩
        cases start with
        | cons fires start' => exact .cons fires (inductionHypothesis.mpr ⟨middle, start', finish⟩)

theorem labelledPath_singleton {event : Event V} {source target : Multiset V} :
    LabelledPath G source [event] target ↔ Fires G event source target := by
  constructor
  · intro path
    cases path with
    | cons fires rest =>
        cases rest
        exact fires
  · intro fires
    exact .cons fires (.nil _)

/-- **Histories are recovered from their end**: undoing a history's events,
last first, gives exactly the configuration that runs it into the given one. -/
theorem unrun_eq_some_iff : ∀ (history : List (Event V)) (source target : Multiset V),
    unrun G history target = some source ↔ LabelledPath G source history.reverse target
  | [], source, target => by
      constructor
      · intro undone
        cases undone
        exact .nil _
      · intro path
        cases path
        rfl
  | event :: rest, source, target => by
      rw [List.reverse_cons, labelledPath_append]
      simp only [unrun]
      constructor
      · intro undone
        cases undoneStep : unstep G event target with
        | none =>
            rw [undoneStep] at undone
            cases undone
        | some middle =>
            rw [undoneStep, Option.bind_some] at undone
            exact ⟨middle, (unrun_eq_some_iff rest source middle).mp undone,
              (labelledPath_singleton G).mpr ((unstep_eq_some_iff G event middle target).mp undoneStep)⟩
      · rintro ⟨middle, path, last⟩
        rw [(unstep_eq_some_iff G event middle target).mpr ((labelledPath_singleton G).mp last),
          Option.bind_some]
        exact (unrun_eq_some_iff rest source middle).mpr path

/-! ## Authored lists and action coverage -/

theorem mem_toList_iff {α : Type} {option : Option α} {value : α} :
    value ∈ option.toList ↔ option = some value := by
  cases option with
  | none => simp
  | some held => simp [eq_comm]

/-- The authored successor list of an event: at most one configuration. -/
def successors (event : Event V) (source : Multiset V) : List (Multiset V) :=
  (step G event source).toList

/-- The authored predecessor list of an event: at most one configuration. -/
def predecessors (event : Event V) (target : Multiset V) : List (Multiset V) :=
  (unstep G event target).toList

theorem mem_successors {event : Event V} {source target : Multiset V} :
    target ∈ successors G event source ↔ Fires G event source target :=
  mem_toList_iff.trans (step_eq_some_iff G event source target)

theorem mem_predecessors {event : Event V} {source target : Multiset V} :
    source ∈ predecessors G event target ↔ Fires G event source target :=
  mem_toList_iff.trans (unstep_eq_some_iff G event source target)

theorem successors_length_le (event : Event V) (source : Multiset V) :
    (successors G event source).length ≤ 1 := by
  unfold successors
  cases step G event source <;> simp

theorem predecessors_length_le (event : Event V) (target : Multiset V) :
    (predecessors G event target).length ≤ 1 := by
  unfold predecessors
  cases unstep G event target <;> simp

/-- **Action coverage**: the steps of the history GSLT are exactly the authored
labelled actions. -/
theorem stepAgreement : SpanTransport.StepAgreement (eventSystem G) := fun _ _ => Iff.rfl

/-- A finite list of every node. -/
structure Listing (Node : Type) where
  nodes : List Node
  complete : ∀ node, node ∈ nodes

namespace Listing

variable {G}

/-- Every event over a listed node set. -/
def events (L : Listing V) : List (Event V) :=
  L.nodes.map Event.evolve ++ L.nodes.map Event.fork ++
    L.nodes.flatMap (fun x => L.nodes.map (Event.merge x)) ++ L.nodes.map Event.erase

omit [DecidableEq V] in
theorem mem_events (L : Listing V) (event : Event V) : event ∈ L.events := by
  cases event with
  | evolve x => simp [events, L.complete]
  | fork x => simp [events, L.complete]
  | merge x y => simp [events, L.complete]
  | erase x => simp [events, L.complete]

end Listing

/-- Every successor of a configuration, over a listed node set. -/
def allSuccessors (L : Listing V) (source : Multiset V) : List (Multiset V) :=
  L.events.flatMap fun event => successors G event source

/-- Every predecessor of a configuration, over a listed node set. -/
def allPredecessors (L : Listing V) (target : Multiset V) : List (Multiset V) :=
  L.events.flatMap fun event => predecessors G event target

/-- **The successor list holds exactly the steps.** -/
theorem mem_allSuccessors (L : Listing V) {source target : Multiset V} :
    target ∈ allSuccessors G L source ↔ (historyGSLT G).Step source target := by
  change _ ↔ ∃ event, Fires G event source target
  simp only [allSuccessors, List.mem_flatMap, mem_successors]
  exact ⟨fun ⟨event, _, fires⟩ => ⟨event, fires⟩, fun ⟨event, fires⟩ => ⟨event, L.mem_events event, fires⟩⟩

/-- **The predecessor list holds exactly the reversed steps.** -/
theorem mem_allPredecessors (L : Listing V) {source target : Multiset V} :
    source ∈ allPredecessors G L target ↔ (historyGSLT G).Step source target := by
  change _ ↔ ∃ event, Fires G event source target
  simp only [allPredecessors, List.mem_flatMap, mem_predecessors]
  exact ⟨fun ⟨event, _, fires⟩ => ⟨event, fires⟩, fun ⟨event, fires⟩ => ⟨event, L.mem_events event, fires⟩⟩

/-! ## Readings and the presented system -/

/-- The three readings of a configuration. -/
inductive Reading where
  | result
  | fault
  | cost
  deriving DecidableEq, Repr

theorem Reading.mem_all (observation : Reading) :
    observation ∈ [Reading.result, Reading.fault, Reading.cost] := by
  cases observation <;> simp

section Readings

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-- Readings of single nodes: a result value in `[0, one]`, a fault flag and a
potential. -/
structure NodeReadings (Node : Type) where
  result : Node → W
  result_nonneg : ∀ node, 0 ≤ result node
  result_le_one : ∀ node, result node ≤ K.one
  faulty : Node → Bool
  potential : Node → W

/-- The extensive potential of a configuration: the sum over its nodes. -/
def potentialSum (potential : V → W) (live : Multiset V) : W := (live.map potential).sum

/-- The fault indicator of a node. -/
def faultIndicator (R : NodeReadings K V) (x : V) : W := if R.faulty x then K.one else 0

/-- **The readings of a configuration**: the best live result, whether a faulty
node is live, and the clamped potential. -/
def reading (R : NodeReadings K V) : Reading → Multiset V → W
  | .result, live => best R.result live
  | .fault, live => best (faultIndicator K R) live
  | .cost, live => K.clamp (potentialSum R.potential live)

variable {K}

omit [DecidableEq V] in
theorem faultIndicator_nonneg (R : NodeReadings K V) (x : V) : 0 ≤ faultIndicator K R x := by
  unfold faultIndicator
  split
  · exact K.zero_le_one
  · exact le_rfl

omit [DecidableEq V] in
theorem faultIndicator_le_one (R : NodeReadings K V) (x : V) : faultIndicator K R x ≤ K.one := by
  unfold faultIndicator
  split
  · exact le_rfl
  · exact K.zero_le_one

omit [DecidableEq V] in
theorem reading_nonneg (R : NodeReadings K V) (observation : Reading) (live : Multiset V) :
    0 ≤ reading K R observation live := by
  cases observation with
  | result => exact best_nonneg _ _
  | fault => exact best_nonneg _ _
  | cost => exact K.clamp_nonneg _

omit [DecidableEq V] in
theorem reading_le_one (R : NodeReadings K V) (observation : Reading) (live : Multiset V) :
    reading K R observation live ≤ K.one := by
  cases observation with
  | result => exact best_le _ K.zero_le_one R.result_le_one _
  | fault => exact best_le _ K.zero_le_one (faultIndicator_le_one R) _
  | cost => exact K.clamp_le_one _

omit [DecidableEq V] in
/-- **The fault reading is `one` exactly when a faulty node is live.** -/
theorem fault_reading_eq_one_iff (R : NodeReadings K V) (live : Multiset V) :
    reading K R .fault live = K.one ↔ ∃ x ∈ live, R.faulty x = true := by
  change best (faultIndicator K R) live = K.one ↔ _
  rw [best_eq_iff_of_le _ K.one_pos (faultIndicator_le_one R)]
  refine exists_congr fun x => and_congr Iff.rfl ?_
  unfold faultIndicator
  cases faulty : R.faulty x
  · simp only [Bool.false_eq_true, if_false, iff_false]
    exact ne_of_lt K.one_pos
  · simp only [if_true]

omit [DecidableEq V] in
/-- **The fault reading is `0` exactly when no faulty node is live.** -/
theorem fault_reading_eq_zero_iff (R : NodeReadings K V) (live : Multiset V) :
    reading K R .fault live = 0 ↔ ∀ x ∈ live, R.faulty x = false := by
  change best (faultIndicator K R) live = 0 ↔ _
  rw [best_eq_zero_iff _ (faultIndicator_nonneg R)]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  unfold faultIndicator
  cases faulty : R.faulty x
  · simp only [Bool.false_eq_true, if_false]
  · simp only [if_true, Bool.true_eq_false, iff_false]
    exact ne_of_gt K.one_pos

omit [DecidableEq V] in
/-- **Within budget the cost reading is the potential.** -/
theorem cost_reading_of_mem (R : NodeReadings K V) {live : Multiset V}
    (nonneg : 0 ≤ potentialSum R.potential live) (le_one : potentialSum R.potential live ≤ K.one) :
    reading K R .cost live = potentialSum R.potential live :=
  K.clamp_of_mem nonneg le_one

variable (K)

/-- **The history grammar as a presented system**: the event-labelled steps,
the three readings, and the authored successor lists. -/
def presented (R : NodeReadings K V) : PresentedSystem (historyGSLT G) K where
  dynamics := eventSystem G
  Obs := Reading
  value := reading K R
  value_nonneg := reading_nonneg R
  value_le_one := reading_le_one R
  value_resp _ _ _ same := by cases same; rfl
  successors := successors G
  successors_act member := (mem_successors G).mp member
  successors_cover action := ⟨_, (mem_successors G).mpr action, rfl⟩

/-- Over a listed node set the vocabulary is finite. -/
def vocabulary (R : NodeReadings K V) (L : Listing V) : (presented G K R).Vocabulary where
  observations := [.result, .fault, .cost]
  observations_complete := Reading.mem_all
  labels := L.events
  labels_complete := L.mem_events

/-! ## The observer separates configurations -/

variable {G}

/-- A relation of configurations that matches every erasure forward. -/
def MatchesErasures (relation : Multiset V → Multiset V → Prop) : Prop :=
  ∀ ⦃left right⦄, relation left right → ∀ x ∈ left,
    ∃ right', Fires G (.erase x) right right' ∧ relation (left.erase x) right'

theorem count_le_of_matchesErasures {relation : Multiset V → Multiset V → Prop}
    (matched : MatchesErasures (G := G) relation) (x : V) :
    ∀ (bound : Nat) ⦃left right : Multiset V⦄, relation left right →
      bound ≤ left.count x → bound ≤ right.count x
  | 0, _, _, _, _ => Nat.zero_le _
  | bound + 1, left, right, related, le => by
      have member : x ∈ left := Multiset.count_pos.mp (by omega)
      obtain ⟨right', fires, related'⟩ := matched related x member
      cases fires with
      | erase memberRight =>
          have lower := count_le_of_matchesErasures matched x bound related'
            (by rw [Multiset.count_erase_self]; omega)
          rw [Multiset.count_erase_self] at lower
          have positive := Multiset.count_pos.mpr memberRight
          omega

/-- **Erasures count every node**: a relation matching erasures in both
directions relates only equal configurations. -/
theorem eq_of_matchesErasures {relation : Multiset V → Multiset V → Prop}
    (forth : MatchesErasures (G := G) relation)
    (back : MatchesErasures (G := G) (fun left right => relation right left))
    {left right : Multiset V} (related : relation left right) : left = right :=
  Multiset.ext.mpr fun x =>
    le_antisymm (count_le_of_matchesErasures forth x _ related le_rfl)
      (count_le_of_matchesErasures back x _ related le_rfl)

variable (G)

/-- **The event system separates configurations**: bisimilarity is equality. -/
theorem eventSystem_bisimilar_iff_eq (left right : Multiset V) :
    (eventSystem G).Bisimilar left right ↔ left = right := by
  constructor
  · rintro ⟨relation, ⟨forth, back, _⟩, related⟩
    exact eq_of_matchesErasures (relation := relation)
      (fun _ _ related x member => forth related (.erase x) (Fires.erase (G := G) member))
      (fun _ _ related x member => back related (.erase x) (Fires.erase (G := G) member)) related
  · rintro rfl
    exact (eventSystem G).bisimilar_refl left

/-- **Graded bisimilarity of the history observer is equality**, whatever the
readings. -/
theorem gradedBisimilar_iff_eq (R : NodeReadings K V) (left right : Multiset V) :
    (presented G K R).GradedBisimilar left right ↔ left = right := by
  constructor
  · rintro ⟨relation, ⟨forth, back, _⟩, related⟩
    exact eq_of_matchesErasures (relation := relation)
      (fun _ _ related x member => forth related (.erase x) (Fires.erase (G := G) member))
      (fun _ _ related x member => back related (.erase x) (Fires.erase (G := G) member)) related
  · rintro rfl
    exact ⟨_, (presented G K R).isGradedBisimulation_equiv, rfl⟩

/-- The exact-value observer's bisimilarity is equality. -/
theorem valueSystem_bisimilar_iff_eq (R : NodeReadings K V) (left right : Multiset V) :
    (valueSystem (presented G K R)).Bisimilar left right ↔ left = right :=
  (bisimilar_iff_graded (presented G K R) left right).trans (gradedBisimilar_iff_eq G K R left right)

/-! ## Histories read exactly -/

/-- The formula that follows a history's events and then tests `inner`. -/
def chain (R : NodeReadings K V) :
    List (Event V) → (presented G K R).Formula → (presented G K R).Formula
  | [], inner => inner
  | event :: rest, inner => .dia event (chain R rest inner)

/-- **The value of a history's formula**: `0` when the history faults, and the
discounted value of `inner` at its result otherwise. -/
theorem val_chain (R : NodeReadings K V) :
    ∀ (history : List (Event V)) (inner : (presented G K R).Formula) (source : Multiset V),
      (presented G K R).val (chain G K R history inner) source =
        (run G history source).elim 0
          (fun result => K.discount^[history.length] ((presented G K R).val inner result))
  | [], inner, source => rfl
  | event :: rest, inner, source => by
      change K.discount (listSup ((presented G K R).val (chain G K R rest inner))
        (successors G event source)) = _
      cases fired : step G event source with
      | none =>
          simp only [successors, fired, Option.toList_none, listSup_nil, K.discount_zero, run,
            Option.bind_none, Option.elim_none]
      | some middle =>
          simp only [successors, fired, Option.toList_some, listSup_cons, listSup_nil, run,
            Option.bind_some]
          rw [max_eq_left ((presented G K R).val_nonneg _ middle), val_chain R rest inner middle]
          cases ran : run G rest middle with
          | none => simp only [Option.elim_none, K.discount_zero]
          | some result =>
              simp only [Option.elim_some, List.length_cons, Function.iterate_succ_apply']

theorem iterate_discount_pos (positive : K.Positive) : ∀ count : Nat, 0 < K.discount^[count] K.one
  | 0 => K.one_pos
  | count + 1 => by
      rw [Function.iterate_succ_apply']
      exact positive (iterate_discount_pos positive count)

/-- **The observer reads every fault of a history**: with a positive discount,
the formula of a history is `0` exactly when the history faults. -/
theorem history_faults_iff (R : NodeReadings K V) (positive : K.Positive)
    (history : List (Event V)) (source : Multiset V) :
    (presented G K R).val (chain G K R history .top) source = 0 ↔ run G history source = none := by
  rw [val_chain]
  cases run G history source with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some result =>
      simp only [Option.elim_some, PresentedSystem.val_top, reduceCtorEq, iff_false]
      exact ne_of_gt (iterate_discount_pos K positive _)

/-- **The observer reads the result of a history**: each reading of the result,
discounted once per event. -/
theorem history_result (R : NodeReadings K V) {history : List (Event V)}
    {source result : Multiset V} (ran : run G history source = some result) (observation : Reading) :
    (presented G K R).val (chain G K R history (.atom observation)) source =
      K.discount^[history.length] (reading K R observation result) := by
  rw [val_chain, ran]
  rfl

/-! ## Costs: the potential laws -/

/-- An event cost that is the change of a node potential.  This is the
hypothesis of `HistoryGrammar.labelledPath_cost`, read in the scale's group;
here it is assumed, never derived from loops. -/
def PotentialLaws (cost : Event V → W) (potential : V → W) : Prop :=
  ∀ x y : V,
    cost (.evolve x) = potential (G.evolve x) - potential x ∧
      cost (.fork x) = potential x ∧
      cost (.erase x) = -potential x ∧
      cost (.merge x y) = potential (G.merge x y) - potential x - potential y

omit [DecidableEq V] [LinearOrder W] [IsOrderedAddMonoid W] in
theorem potentialSum_cons (potential : V → W) (x : V) (live : Multiset V) :
    potentialSum potential (x ::ₘ live) = potential x + potentialSum potential live := by
  simp [potentialSum]

omit [LinearOrder W] [IsOrderedAddMonoid W] in
theorem potentialSum_erase (potential : V → W) {x : V} {live : Multiset V} (member : x ∈ live) :
    potentialSum potential live = potential x + potentialSum potential (live.erase x) := by
  conv_lhs => rw [← Multiset.cons_erase member]
  exact potentialSum_cons potential x _

omit [LinearOrder W] [IsOrderedAddMonoid W] in
theorem potentialSum_sub (potential : V → W) {part live : Multiset V} (le : part ≤ live) :
    potentialSum potential live =
      potentialSum potential (live - part) + potentialSum potential part := by
  conv_lhs => rw [← Multiset.sub_add_cancel le]
  simp [potentialSum]

omit [LinearOrder W] [IsOrderedAddMonoid W] in
/-- **Along a labelled path a cost with the potential laws sums to the change of
the extensive potential.** -/
theorem labelledPath_potentialSum {cost : Event V → W} {potential : V → W}
    (laws : PotentialLaws G cost potential) {source target : Multiset V} {history : List (Event V)}
    (path : LabelledPath G source history target) :
    (history.map cost).sum = potentialSum potential target - potentialSum potential source := by
  induction path with
  | nil live => simp
  | cons fires _ inductionHypothesis =>
      rw [List.map_cons, List.sum_cons, inductionHypothesis]
      cases fires with
      | @evolve x live enabled =>
          rw [(laws x x).1, potentialSum_erase potential enabled, potentialSum_cons]
          abel
      | @fork x live enabled =>
          rw [(laws x x).2.1, potentialSum_cons]
          abel
      | @merge x y live enabled =>
          rw [(laws x y).2.2.2, potentialSum_sub potential enabled, potentialSum_cons]
          simp only [pair, potentialSum_cons]
          simp only [potentialSum, Multiset.map_zero, Multiset.sum_zero]
          abel
      | @erase x live enabled =>
          rw [(laws x x).2.2.1, potentialSum_erase potential enabled]
          abel

/-- **The observer's cost readings price every history within budget**: when
the event cost has the potential laws of the node potential and both ends lie
within `[0, one]`, the cost of a history is the change of the cost reading. -/
theorem history_cost (R : NodeReadings K V) {cost : Event V → W}
    (laws : PotentialLaws G cost R.potential) {history : List (Event V)}
    {source result : Multiset V} (ran : run G history source = some result)
    (sourceBudget : 0 ≤ potentialSum R.potential source ∧ potentialSum R.potential source ≤ K.one)
    (resultBudget : 0 ≤ potentialSum R.potential result ∧ potentialSum R.potential result ≤ K.one) :
    (history.map cost).sum = reading K R .cost result - reading K R .cost source := by
  rw [cost_reading_of_mem R resultBudget.1 resultBudget.2,
    cost_reading_of_mem R sourceBudget.1 sourceBudget.2]
  exact labelledPath_potentialSum G laws ((run_eq_some_iff G history source result).mp ran)

end Readings

/-- On an integer scale the discount is the identity, so the formula of a
history reads the result's values undiscounted. -/
theorem history_result_integers (unit : ℤ) (positive : 0 < unit)
    (R : NodeReadings (Scale.integers unit positive) V) {history : List (Event V)}
    {source result : Multiset V} (ran : run G history source = some result) (observation : Reading) :
    (presented G (Scale.integers unit positive) R).val
        (chain G (Scale.integers unit positive) R history (.atom observation)) source =
      reading (Scale.integers unit positive) R observation result := by
  rw [history_result G (Scale.integers unit positive) R ran observation]
  change id^[history.length] _ = _
  rw [Function.iterate_id]
  rfl

/-- **The integer observer reads the exact cost of a history within budget**:
the difference of the cost formula after the history and the cost atom
before it. -/
theorem history_cost_integers (unit : ℤ) (positive : 0 < unit)
    (R : NodeReadings (Scale.integers unit positive) V) {cost : Event V → ℤ}
    (laws : PotentialLaws G cost R.potential) {history : List (Event V)}
    {source result : Multiset V} (ran : run G history source = some result)
    (sourceBudget : 0 ≤ potentialSum R.potential source ∧ potentialSum R.potential source ≤ unit)
    (resultBudget : 0 ≤ potentialSum R.potential result ∧ potentialSum R.potential result ≤ unit) :
    (history.map cost).sum =
      (presented G (Scale.integers unit positive) R).val
          (chain G (Scale.integers unit positive) R history (.atom .cost)) source -
        (presented G (Scale.integers unit positive) R).val (.atom .cost) source := by
  rw [history_result_integers G unit positive R ran]
  exact history_cost G (Scale.integers unit positive) R laws ran sourceBudget resultBudget

/-! ## Branching profiles -/

/-- The event-labelled system branches finitely forward. -/
theorem eventSystem_imageFiniteModulo : (eventSystem G).ImageFiniteModulo := by
  intro event source
  refine ⟨{target | target ∈ successors G event source}, List.finite_toSet _, ?_⟩
  intro target fires
  exact ⟨target, (mem_successors G).mpr fires, rfl⟩

/-- **The event-labelled system branches finitely backward**, for every node
type: the event names what it consumed. -/
theorem eventSystem_predecessorFiniteModulo :
    SpanTransport.PredecessorFiniteModulo (eventSystem G) := by
  intro event target
  refine ⟨{source | source ∈ predecessors G event target}, List.finite_toSet _, ?_⟩
  intro source fires
  exact ⟨source, (mem_predecessors G).mpr fires, rfl⟩

/-- **Two-sided Hennessy–Milner for the history grammar** (classical): logical
equivalence of futures and pasts is two-sided bisimilarity. -/
theorem twoSided_logicallyEquivalent_iff_bisimilar (left right : Multiset V) :
    (SpanTransport.twoSided (eventSystem G)).LogicallyEquivalent left right ↔
      (SpanTransport.twoSided (eventSystem G)).Bisimilar left right :=
  SpanTransport.twoSided_logicallyEquivalent_iff_bisimilar (eventSystem G)
    (eventSystem_imageFiniteModulo G) (eventSystem_predecessorFiniteModulo G) left right

/-- **Two-sided formulas separate every two configurations** (classical). -/
theorem twoSided_logicallyEquivalent_iff_eq (left right : Multiset V) :
    (SpanTransport.twoSided (eventSystem G)).LogicallyEquivalent left right ↔ left = right := by
  rw [twoSided_logicallyEquivalent_iff_bisimilar]
  constructor
  · intro bisimilar
    exact (eventSystem_bisimilar_iff_eq G left right).mp
      (SpanTransport.bisimilar_of_twoSided (eventSystem G) bisimilar)
  · rintro rfl
    exact (SpanTransport.twoSided (eventSystem G)).bisimilar_refl left

/-- A two-sided bisimulation gives both target laws on the history GSLT's
reduction span. -/
theorem twoSided_targetLaws {relation : Multiset V → Multiset V → Prop}
    (bisimulation : (SpanTransport.twoSided (eventSystem G)).IsBisimulation relation) :
    SpanTransport.TargetForth (gsltSpan (historyGSLT G)) (gsltSpan (historyGSLT G)) relation ∧
      SpanTransport.TargetBack (gsltSpan (historyGSLT G)) (gsltSpan (historyGSLT G)) relation :=
  SpanTransport.targetLaws_of_twoSided (stepAgreement G) bisimulation

/-- The kind of an event, forgetting its nodes. -/
inductive EventKind where
  | evolve
  | fork
  | merge
  | erase
  deriving DecidableEq, Repr

/-- The kind of an event. -/
def kindOf : Event V → EventKind
  | .evolve _ => .evolve
  | .fork _ => .fork
  | .merge _ _ => .merge
  | .erase _ => .erase

/-- **The kind-labelled system**: a step is labelled by its kind of event
only, as an observer that does not see the consumed nodes labels it. -/
def kindSystem : System.{0, 0} (historyGSLT G) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := EventKind
  act kind source target := ∃ event, kindOf event = kind ∧ Fires G event source target
  act_resp_left := by
    intro _ _ _ target same action
    cases same
    exact ⟨target, action, rfl⟩
  act_resp_right := by
    intro _ _ _ _ action same
    cases same
    exact action

/-- The candidate successors of a configuration: one per kind and per pair of
live nodes. -/
def kindSuccessorCandidates (source : Multiset V) : Finset (Multiset V) :=
  (source.toFinset ×ˢ source.toFinset).biUnion fun nodes =>
    {G.evolve nodes.1 ::ₘ source.erase nodes.1, nodes.1 ::ₘ source,
      G.merge nodes.1 nodes.2 ::ₘ (source - pair nodes.1 nodes.2), source.erase nodes.1}

theorem mem_kindSuccessorCandidates {event : Event V} {source target : Multiset V}
    (fires : Fires G event source target) : target ∈ kindSuccessorCandidates G source := by
  unfold kindSuccessorCandidates
  rw [Finset.mem_biUnion]
  cases fires with
  | @evolve x _ member =>
      exact ⟨(x, x), Finset.mem_product.mpr ⟨Multiset.mem_toFinset.mpr member,
        Multiset.mem_toFinset.mpr member⟩, by simp⟩
  | @fork x _ member =>
      exact ⟨(x, x), Finset.mem_product.mpr ⟨Multiset.mem_toFinset.mpr member,
        Multiset.mem_toFinset.mpr member⟩, by simp⟩
  | @merge x y _ enabled =>
      have memberX : x ∈ source := Multiset.mem_of_le enabled (by simp [pair])
      have memberY : y ∈ source := Multiset.mem_of_le enabled (by simp [pair])
      exact ⟨(x, y), Finset.mem_product.mpr ⟨Multiset.mem_toFinset.mpr memberX,
        Multiset.mem_toFinset.mpr memberY⟩, by simp⟩
  | @erase x _ member =>
      exact ⟨(x, x), Finset.mem_product.mpr ⟨Multiset.mem_toFinset.mpr member,
        Multiset.mem_toFinset.mpr member⟩, by simp⟩

/-- **Kind-labelled successors branch finitely for every node type**: a step
can only use live nodes. -/
theorem kindSystem_imageFiniteModulo : (kindSystem G).ImageFiniteModulo := by
  intro kind source
  refine ⟨↑(kindSuccessorCandidates G source), Finset.finite_toSet _, ?_⟩
  rintro target ⟨event, _, fires⟩
  exact ⟨target, mem_kindSuccessorCandidates G fires, rfl⟩

/-- Over a listed node set the kind-labelled pasts branch finitely. -/
theorem kindSystem_predecessorFiniteModulo (L : Listing V) :
    SpanTransport.PredecessorFiniteModulo (kindSystem G) := by
  intro kind target
  refine ⟨{source | source ∈ allPredecessors G L target}, List.finite_toSet _, ?_⟩
  rintro source ⟨event, _, fires⟩
  exact ⟨source, (mem_allPredecessors G L).mpr ⟨event, fires⟩, rfl⟩

/-- **Kind-labelled pasts branch finitely exactly when the node type is finite**
(classical).  Erasing any node from `{x}` reaches the empty configuration, so
the erase pasts of `0` are in bijection with the nodes. -/
theorem kindSystem_predecessorFiniteModulo_iff :
    SpanTransport.PredecessorFiniteModulo (kindSystem G) ↔ (Set.univ : Set V).Finite := by
  constructor
  · intro finite
    obtain ⟨representatives, finiteRepresentatives, cover⟩ := finite .erase 0
    have injective : Set.InjOn (fun x : V => ({x} : Multiset V))
        ((fun x : V => ({x} : Multiset V)) ⁻¹' representatives) :=
      fun x _ y _ same => Multiset.singleton_inj.mp same
    refine (finiteRepresentatives.preimage injective).subset fun x _ => ?_
    obtain ⟨representative, member, same⟩ :=
      cover (source := {x}) ⟨.erase x, rfl, by
        have fires := Fires.erase (G := G) (Multiset.mem_singleton_self x)
        rwa [Multiset.erase_singleton] at fires⟩
    change ({x} : Multiset V) = representative at same
    change ({x} : Multiset V) ∈ representatives
    rw [same]
    exact member
  · intro finite
    obtain ⟨nodes, complete⟩ : ∃ nodes : List V, ∀ x, x ∈ nodes :=
      ⟨finite.toFinset.toList, fun x => by simp⟩
    exact kindSystem_predecessorFiniteModulo G ⟨nodes, complete⟩

/-! ## Causal occurrences -/

/-- The principal node of an event: the node evolved, copied, erased, or the
left node merged. -/
def principal : Event V → V
  | .evolve x => x
  | .fork x => x
  | .merge x _ => x
  | .erase x => x

theorem principal_mem {event : Event V} {source target : Multiset V}
    (fires : Fires G event source target) : principal event ∈ source := by
  cases fires with
  | evolve member => exact member
  | fork member => exact member
  | merge enabled => exact Multiset.mem_of_le enabled (by simp [pair, principal])
  | erase member => exact member

/-- **A causal occurrence**: a labelled step together with the copy of its
principal node that it uses. -/
structure CausalOccurrence where
  event : Event V
  source : Multiset V
  target : Multiset V
  fires : Fires G event source target
  copy : Fin (source.count (principal event))

/-- The labelled step of a causal occurrence: its event and endpoints. -/
def CausalOccurrence.step {G : Grammar V} (occurrence : CausalOccurrence G) : LabelledStep G :=
  ⟨(occurrence.event, occurrence.source, occurrence.target), occurrence.fires⟩

/-- The reduction span of labelled steps. -/
def labelledSpan : ReductionSpan (Multiset V) where
  Edge := LabelledStep G
  source step := step.1.2.1
  target step := step.1.2.2

/-- The reduction span of causal occurrences. -/
def causalSpan : ReductionSpan (Multiset V) where
  Edge := CausalOccurrence G
  source := CausalOccurrence.source
  target := CausalOccurrence.target

/-- **Forgetting the copy**: the span map from causal occurrences to labelled
steps. -/
def forgetCopies : ObservationSpans.SpanMap (causalSpan G) (labelledSpan G) where
  states := id
  events := CausalOccurrence.step
  source_comm _ := rfl
  target_comm _ := rfl

/-- The first copy of the principal node. -/
def firstCopy (step : LabelledStep G) : CausalOccurrence G :=
  ⟨step.1.1, step.1.2.1, step.1.2.2, step.2,
    ⟨0, Multiset.count_pos.mpr (principal_mem G step.2)⟩⟩

theorem firstCopy_step (step : LabelledStep G) : (firstCopy G step).step = step := rfl

/-- **Exact occurrence lifting holds**: every labelled step at a configuration
is the image of a causal occurrence there. -/
theorem forgetCopies_sourceOccurrenceLifts : (forgetCopies G).SourceOccurrenceLifts :=
  fun _ step sourceEq => ⟨firstCopy G step, sourceEq, rfl⟩

theorem forgetCopies_targetOccurrenceLifts : (forgetCopies G).TargetOccurrenceLifts :=
  fun _ step targetEq => ⟨firstCopy G step, targetEq, rfl⟩

/-- **The trace core's occurrences are labelled steps**: at a configuration an
enabled occurrence of `HistoryIndependence.presentation` is determined by its
event. -/
theorem enabled_eq_of_site_eq {live : Multiset V}
    (first second : (HistoryIndependence.presentation G).Enabled live)
    (same : first.site = second.site) : first = second := by
  obtain ⟨site, target, ⟨fires⟩⟩ := first
  obtain ⟨site', target', ⟨fires'⟩⟩ := second
  change site = site' at same
  subst same
  have targets := fires_target_unique G fires fires'
  subst targets
  rfl

end Mettapedia.GSLT.Distinction.HistoryObserver
