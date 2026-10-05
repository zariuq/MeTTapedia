import Mettapedia.GSLT.Distinction.HistoryContextCost
import Mettapedia.GSLT.Distinction.HistoryCoverageProfiles
import Mettapedia.GSLT.Logic.ContextualObservedMaterialFamily
import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers

/-!
# Controls for the contextual two-sided history model

The model of `HistoryContextTwoSided` keeps three distinctions of the observed
material readout, and its descent and lifting criteria have failing cases.

* **The exact kernel is stronger than agreement of behaviour**
  (`kernel_stronger_than_behaviour`).  On the authored instance with signed
  potentials, a result and a failure placed fresh are ordinarily bisimilar in
  the future-only profile and agree on every present reading; still no profile
  relates them in the exact kernel, because beside a pending task their cost
  readings differ.
* **Provenance has no factor through the material observation**
  (`fixed_evolution_observed`, `provenance_no_material_factor`).  Evolving a
  node that evolution fixes, forward or backward, gives one material value; the
  pending script, which records the direction, is a natural reading of the
  placed configurations with no factor through the observation.
* **Products that agree now and differ at a future argument**
  (`same_all_present_applications`, `full_future_products_differ`).  Over the
  material members of the authored instance, the family of numbers bounded by
  the result reading plus the world's length grows along a script arrow.  The
  dependent products of the constant `true` and of the test `= 0` agree at
  every present argument and differ at the newly admitted one.
* **The future-only profile: the predecessor box does not descend**
  (`futureOnly_fresh_observed_iff`, `futureOnly_box_not_descends`).  In the
  future-only profile with readings that depend on size only, the fresh kernel
  is equality of size.  Having no single node among one's predecessors is
  invariant under it, yet its predecessor box holds at a pending task and fails
  at a result: incoming steps do not match modulo the kernel.
* **Endpoint lifts do not recover an erased occurrence**
  (`endpoint_lifts_not_recovery`).  Forgetting which copy an occurrence uses has
  both occurrence lifts, hence both endpoint lifts, and no choice of occurrence
  from its labelled step returns the two copies erased from `{x, x}`.
* **A pending task in context** (`pending_frame_not_natural`): the future
  diamond and the predecessor box do not commute with it.
* **Renamings** (`shift_source_not_target`, `swap_all_laws`).  The successor
  renaming of the natural numbers lifts every source occurrence and no target
  endpoint; the node swap of a two-node grammar, a bijection that is not the
  identity, satisfies all four occurrence laws and commutes with the
  predecessor box.
* **The authored instance** (`renaming_trivial`): its only renaming is the
  identity.

**Choice.**  Every declaration of this module is free of `Classical.choice`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryContextControls

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner (Direction)
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver (Listing Reading NodeReadings reading best best_cons best_zero
  potentialSum faultIndicator principal)
open Mettapedia.GSLT.Distinction.HistoryCoverage (Renaming best_add)
open Mettapedia.GSLT.Distinction.HistoryObserverControls (relabel)
open Mettapedia.GSLT.Distinction.HistoryContextCategory
open Mettapedia.GSLT.Distinction.HistoryContextTwoSided
open Mettapedia.GSLT.Distinction.HistoryContextCost
open Mettapedia.GSLT.Distinction.HistoryCoverageProfiles
open Mettapedia.GSLT.Distinction.HistoryIndependence (consumed read produced)
open Mettapedia.GSLT.Distinction.Constructive (Scale)
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.TypeTheory.ContextualWitnessCover (NaturalHom)
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.OSLF.Framework.DerivedModalities
open HistoryCoverageControls (Node grammar listing scale readings unit_pos)

/-! ## The authored instance in the model -/

/-- The nodes of the authored instance by their index. -/
def nodeCoding : ArgumentCoding Node :=
  comapCoding natCoding Node.index Node.index_injective

/-- Integer values as material tags. -/
abbrev integerCoding : ArgumentCoding ℤ := Mettapedia.GSLT.DiscreteReadingCodings.integers

/-- **The authored instance has only the identity renaming.** -/
theorem renaming_trivial (rename : Renaming grammar) (x : Node) : rename.map x = x := by
  have evolveTask : rename.map .done = grammar.evolve (rename.map .task) := rename.evolve_comm .task
  have mergeDone : rename.map .task = grammar.merge (rename.map .done) (rename.map .task) :=
    rename.merge_comm .done .task
  have injective := rename.injective
  cases task : rename.map .task with
  | failed =>
      exfalso
      rw [task] at evolveTask
      exact Node.noConfusion (injective (evolveTask.trans task.symm))
  | done =>
      exfalso
      rw [task] at mergeDone
      cases done : rename.map .done with
      | task => rw [done] at mergeDone; exact Node.noConfusion mergeDone
      | done => exact Node.noConfusion (injective (done.trans task.symm))
      | failed => rw [done] at mergeDone; exact Node.noConfusion mergeDone
  | task =>
      rw [task] at evolveTask
      have doneFixed : rename.map .done = .done := evolveTask
      cases x with
      | task => exact task
      | done => exact doneFixed
      | failed =>
          cases failed : rename.map .failed with
          | task => exact absurd (injective (failed.trans task.symm)) Node.noConfusion
          | done => exact absurd (injective (failed.trans doneFixed.symm)) Node.noConfusion
          | failed => rfl

theorem apply_eq_add (context : Context grammar) (live : Multiset Node) :
    context.apply live = live + (context.frame : Multiset Node) := by
  unfold Context.apply
  congr 1
  conv_rhs => rw [← Multiset.map_id' live]
  exact Multiset.map_congr rfl fun x _ => renaming_trivial context.rename x

/-! ## The exact kernel is stronger than agreement of behaviour -/

section Kernel

theorem signed_result (live : Multiset Node) : reading scale signedReadings .result live = 0 := by
  induction live using Multiset.induction_on with
  | empty => rfl
  | cons x rest inductionHypothesis =>
      change best signedReadings.result (x ::ₘ rest) = 0
      rw [best_cons]
      change max 0 (best signedReadings.result rest) = 0
      change max 0 (reading scale signedReadings .result rest) = 0
      rw [inductionHypothesis]
      rfl

theorem signed_fault (live : Multiset Node) : reading scale signedReadings .fault live = 0 := by
  induction live using Multiset.induction_on with
  | empty => rfl
  | cons x rest inductionHypothesis =>
      change best (faultIndicator scale signedReadings) (x ::ₘ rest) = 0
      rw [best_cons]
      change max 0 (best (faultIndicator scale signedReadings) rest) = 0
      change max 0 (reading scale signedReadings .fault rest) = 0
      rw [inductionHypothesis]
      rfl

theorem signed_cost_done : reading scale signedReadings .cost (.done ::ₘ 0) = 0 := by
  change clampedCost (.done ::ₘ 0) = 0
  rw [clampedCost_eq, potentialSum_singleton]
  rfl

theorem signed_cost_failed : reading scale signedReadings .cost (.failed ::ₘ 0) = 0 := by
  change clampedCost (.failed ::ₘ 0) = 0
  rw [clampedCost_eq, potentialSum_singleton]
  rfl

theorem signed_cost_done_framed : reading scale signedReadings .cost (pendingFrame.apply (.done ::ₘ 0)) = 1 := by
  change clampedCost (pendingFrame.apply (.done ::ₘ 0)) = 1
  rw [clampedCost_eq, pendingFrame_apply, potentialSum_add', potentialSum_singleton, potentialSum_singleton]
  rfl

theorem signed_cost_failed_framed :
    reading scale signedReadings .cost (pendingFrame.apply (.failed ::ₘ 0)) = 0 := by
  change clampedCost (pendingFrame.apply (.failed ::ₘ 0)) = 0
  rw [clampedCost_eq, pendingFrame_apply, potentialSum_add', potentialSum_singleton, potentialSum_singleton]
  rfl

/-- **The exact kernel is stronger than agreement of behaviour.**  A result and a
failure placed fresh are ordinarily bisimilar in the future-only profile and
agree on every present reading; still in every profile the exact kernel
separates them, because beside a pending task their cost readings are `1` and
`0`. -/
theorem kernel_stronger_than_behaviour (point : World grammar) :
    ContextualCoalgebraBisimulation.Bisimilar (coalgebra (futureOnly grammar)) point
        (fresh point (.done ::ₘ 0)) (fresh point (.failed ::ₘ 0)) ∧
      (∀ observation, reading scale signedReadings observation (.done ::ₘ 0) =
        reading scale signedReadings observation (.failed ::ₘ 0)) ∧
      ∀ profile : Profile grammar,
        ¬ ObservedBisimilar profile scale signedReadings point (fresh point (.done ::ₘ 0))
          (fresh point (.failed ::ₘ 0)) := by
  refine ⟨ContextualCoalgebraBisimulation.greatest (coalgebra (futureOnly grammar)) sameShape_isBisimulation
    ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro observation
    cases observation with
    | result => rw [signed_result, signed_result]
    | fault => rw [signed_fault, signed_fault]
    | cost => rw [signed_cost_done, signed_cost_failed]
  · intro profile related
    have framed := readings_eq_in_context profile scale signedReadings related
      (inContext point pendingFrame) .cost
    rw [transport_live, transport_live] at framed
    change reading scale signedReadings .cost (pendingFrame.apply (.done ::ₘ 0)) =
      reading scale signedReadings .cost (pendingFrame.apply (.failed ::ₘ 0)) at framed
    rw [signed_cost_done_framed, signed_cost_failed_framed] at framed
    exact absurd framed (by decide)

end Kernel

/-! ## Provenance has no factor through the material observation -/

section Provenance

variable {V : Type} (G : Grammar V)

/-- A pending script with its origin. -/
structure Pending (point : World G) where
  origin : ℕ
  script : List (Entry V)
  length_eq : origin + script.length = point.length

theorem Pending.ext' {point : World G} {first second : Pending G point} (origin : first.origin = second.origin)
    (script : first.script = second.script) : first = second := by
  obtain ⟨_, _, _⟩ := first
  obtain ⟨_, _, _⟩ := second
  cases origin
  cases script
  rfl

/-- Transport of a pending script. -/
def Pending.transport {first second : World G} (arrow : first ⟶ second) (pending : Pending G first) :
    Pending G second :=
  ⟨pending.origin, (Arrow.context arrow).script pending.script ++ Arrow.script arrow, by
    rw [List.length_append, Context.script_length, ← Nat.add_assoc, pending.length_eq, Arrow.length_eq arrow]⟩

/-- **The pending scripts**, as a functor on the context category. -/
def pendingScripts : World G ⥤ Type where
  obj point := Pending G point
  map arrow := TypeCat.ofHom (Pending.transport G arrow)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro pending
    exact Pending.ext' G rfl (by
      change (Context.one G).script pending.script ++ [] = pending.script
      rw [Context.script_one, List.append_nil])
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro pending
    exact Pending.ext' G rfl (by
      change ((Arrow.context earlier).andThen (Arrow.context later)).script pending.script ++
          ((Arrow.context later).script (Arrow.script earlier) ++ Arrow.script later) =
        (Arrow.context later).script ((Arrow.context earlier).script pending.script ++ Arrow.script earlier) ++
          Arrow.script later
      rw [Context.script_andThen, Context.script_append, List.append_assoc])

/-- **Provenance**: the pending script of a placed configuration, a natural
reading. -/
def provenance : NaturalHom (placed G) (pendingScripts G) where
  app _ state := ⟨state.origin, state.script, state.length_eq⟩
  naturality _ _ := rfl

/-- A forward or backward evolution of a node that evolution fixes, pending in
one configuration. -/
def FixedPair (point : World G) (left right : Placed point) : Prop :=
  left = right ∨ (left.live = right.live ∧ left.origin = right.origin ∧
    ∃ y rest, G.evolve y = y ∧ left.script = (.forward, .evolve y) :: rest ∧
      right.script = (.backward, .evolve y) :: rest)

variable {G}

theorem fixedPair_transport {first second : World G} (arrow : first ⟶ second) {left right : Placed first}
    (pair : FixedPair G first left right) :
    FixedPair G second (transport arrow left) (transport arrow right) := by
  rcases pair with same | ⟨lives, origins, y, rest, fixed, leftScript, rightScript⟩
  · exact Or.inl (congrArg (transport arrow) same)
  · refine Or.inr ⟨by rw [transport_live, transport_live, lives], origins,
      (Arrow.context arrow).rename.map y, (Arrow.context arrow).script rest ++ Arrow.script arrow, ?_, ?_, ?_⟩
    · rw [← (Arrow.context arrow).rename.evolve_comm, fixed]
    · rw [transport_script, leftScript]
      rfl
    · rw [transport_script, rightScript]
      rfl

theorem fixed_moves_same {y : V} (fixed : G.evolve y = y) {source target : Multiset V}
    (splits : Splits G (.evolve y) source target) : target = source := by
  obtain ⟨rest, sourceEq, targetEq⟩ := splits
  rw [sourceEq, targetEq]
  change (G.evolve y ::ₘ 0) + 0 + rest = (y ::ₘ 0) + 0 + rest
  rw [fixed]

theorem fixed_splits_self {y : V} (fixed : G.evolve y = y) {source target : Multiset V}
    (splits : Splits G (.evolve y) source target) : Splits G (.evolve y) target source := by
  have same := fixed_moves_same fixed splits
  rw [same]
  rw [same] at splits
  exact splits

theorem fixedPair_forth {point : World G} {left right child : Placed point} (pair : FixedPair G point left right)
    (advances : Advances (exact G) left child) :
    ∃ matching, Advances (exact G) right matching ∧ FixedPair G point child matching := by
  rcases pair with same | ⟨lives, origins, y, rest, fixed, leftScript, rightScript⟩
  · exact ⟨child, same ▸ advances, Or.inl rfl⟩
  · obtain ⟨written, actual, rest', scriptEq, admitted, moves, originEq, childScript⟩ := advances
    rw [leftScript] at scriptEq
    obtain ⟨writtenEq, restEq⟩ := List.cons.inj scriptEq
    change actual = written at admitted
    rw [admitted, ← writtenEq] at moves
    refine ⟨child, ⟨(.backward, .evolve y), (.backward, .evolve y), rest, rightScript, rfl, ?_,
      by rw [originEq, origins], by rw [childScript, restEq]⟩, Or.inl rfl⟩
    change Splits G (.evolve y) child.live right.live
    rw [← lives]
    exact fixed_splits_self fixed moves

theorem fixedPair_back {point : World G} {left right child : Placed point} (pair : FixedPair G point left right)
    (advances : Advances (exact G) right child) :
    ∃ matching, Advances (exact G) left matching ∧ FixedPair G point matching child := by
  rcases pair with same | ⟨lives, origins, y, rest, fixed, leftScript, rightScript⟩
  · exact ⟨child, same ▸ advances, Or.inl rfl⟩
  · obtain ⟨written, actual, rest', scriptEq, admitted, moves, originEq, childScript⟩ := advances
    rw [rightScript] at scriptEq
    obtain ⟨writtenEq, restEq⟩ := List.cons.inj scriptEq
    change actual = written at admitted
    rw [admitted, ← writtenEq] at moves
    refine ⟨child, ⟨(.forward, .evolve y), (.forward, .evolve y), rest, leftScript, rfl, ?_,
      by rw [originEq, origins], by rw [childScript, restEq]⟩, Or.inl rfl⟩
    change Splits G (.evolve y) left.live child.live
    rw [lives]
    exact fixed_splits_self fixed moves

/-- **Fixed evolution, run forward or undone, is observed alike.** -/
theorem fixedPair_isObservedBisimulation {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    (K : Scale W) (R : NodeReadings K V) :
    ContextualObservedCoalgebra.IsObservedBisimulation (coalgebra (exact G)) (observes K R) (FixedPair G) where
  underlying := {
    stable := fun step _ _ pair => fixedPair_transport step pair
    forth := fun {_ _ _} pair future {_} available =>
      fixedPair_forth (fixedPair_transport future.2 pair) available
    back := fun {_ _ _} pair future {_} available =>
      fixedPair_back (fixedPair_transport future.2 pair) available }
  atoms {_ left right} pair atom := by
    rcases pair with same | ⟨lives, _, _⟩
    · rw [same]
    · change atom.2 = reading K R atom.1 left.live ↔ atom.2 = reading K R atom.1 right.live
      rw [lives]

variable (G)

/-- The configuration `{x}` at the world of length one, with the evolution of
`x` pending forward or backward. -/
def pendingEvolution (x : V) (direction : Direction) : Placed (⟨1⟩ : World G) :=
  ⟨x ::ₘ 0, 0, [(direction, .evolve x)], rfl⟩

theorem fixed_evolution_observed {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    (K : Scale W) (R : NodeReadings K V) {x : V} (fixed : G.evolve x = x) :
    ObservedBisimilar (exact G) K R ⟨1⟩ (pendingEvolution G x .forward) (pendingEvolution G x .backward) :=
  ⟨FixedPair G, fixedPair_isObservedBisimulation K R, Or.inr ⟨rfl, rfl, x, [], fixed, rfl, rfl⟩⟩

/-- **Provenance has no factor through the material observation**: whenever a
node is fixed by evolution, no natural reading of material members returns the
pending script. -/
theorem provenance_no_material_factor {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    (K : Scale W) (R : NodeReadings K V) (nodes : ArgumentCoding V) (L : Listing V) (values : ArgumentCoding W)
    {x : V} (fixed : G.evolve x = x) :
    ¬ ∃ consumer : NaturalHom
        (ContextualObservedMaterialFamily.members (coalgebra (exact G)) (observes K R) (worldCoding G)
          (arrowCoding nodes L) (atomCoding values)) (pendingScripts G),
      (ContextualObservedMaterialFamily.observation (coalgebra (exact G)) (observes K R) (worldCoding G)
          (arrowCoding nodes L) (atomCoding values)).comp consumer = provenance G := by
  rintro ⟨consumer, factors⟩
  have aliases := (ContextualObservedMaterialFamily.observation_eq_iff (coalgebra (exact G)) (observes K R)
    (worldCoding G) (arrowCoding nodes L) (atomCoding values) ⟨1⟩ (pendingEvolution G x .forward)
    (pendingEvolution G x .backward)).mpr (fixed_evolution_observed G K R fixed)
  have first := congrArg (fun map : NaturalHom (placed G) (pendingScripts G) =>
    map.app ⟨1⟩ (pendingEvolution G x .forward)) factors
  have second := congrArg (fun map : NaturalHom (placed G) (pendingScripts G) =>
    map.app ⟨1⟩ (pendingEvolution G x .backward)) factors
  have scripts := congrArg Pending.script
    (first.symm.trans ((congrArg (consumer.app ⟨1⟩) aliases).trans second))
  change [((.forward : Direction), Event.evolve x)] = [((.backward : Direction), Event.evolve x)] at scripts
  cases scripts

end Provenance

/-! ## Products that agree now and differ at a future argument -/

section Products

/-- The material members of the authored instance in the exact profile. -/
abbrev material :=
  ContextualObservedMaterialFamily.members (coalgebra (exact grammar)) (observes scale readings)
    (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding)

/-- The material observation of placed configurations. -/
abbrev observation :=
  ContextualObservedMaterialFamily.observation (coalgebra (exact grammar)) (observes scale readings)
    (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding)

theorem observation_related {point : World grammar} {left right : Placed point}
    (same : observation.app point left = observation.app point right) :
    ObservedBisimilar (exact grammar) scale readings point left right :=
  (ContextualObservedMaterialFamily.observation_eq_iff (coalgebra (exact grammar)) (observes scale readings)
    (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding) point left right).mp same

/-- The result reading as a number. -/
def resultNumber (live : Multiset Node) : ℕ := (reading scale readings .result live).toNat

theorem result_monotone (context : Context grammar) (live : Multiset Node) :
    resultNumber live ≤ resultNumber (context.apply live) := by
  unfold resultNumber
  rw [apply_eq_add]
  change (best readings.result live).toNat ≤ (best readings.result (live + _)).toNat
  rw [best_add]
  exact Int.toNat_le_toNat (le_max_left _ _)

/-- The numbers bounded by the result reading of every representative plus the
length of the world. -/
def resultBounds (point : material.Elements) (number : ℕ) : Prop :=
  ∀ argument : Placed point.1, observation.app point.1 argument = point.2 →
    number ≤ resultNumber argument.live + point.1.length

theorem bound_follows {first second : material.Elements} (step : first ⟶ second) {number : ℕ}
    (bound : resultBounds first number) : resultBounds second number := by
  intro next representsNext
  obtain ⟨argument, represents⟩ := ContextualObservedMaterialFamily.observation_cover
    (coalgebra (exact grammar)) (observes scale readings) (worldCoding grammar) (arrowCoding nodeCoding listing)
    (atomCoding integerCoding) first.1 first.2
  have observedNext : observation.app second.1 (transport step.1 argument) = second.2 :=
    (observation.naturality step.1 argument).symm.trans ((congrArg (material.map step.1) represents).trans step.2)
  have related := observation_related (observedNext.trans representsNext.symm)
  have resultEq := readings_eq_of_observed (exact grammar) scale readings related .result
  have monotone := result_monotone (Arrow.context step.1) argument.live
  have lengths : first.1.length ≤ second.1.length := by
    have := Arrow.length_eq step.1
    omega
  have before := bound argument represents
  change resultNumber next.live + second.1.length ≥ number
  have nextEq : resultNumber next.live = resultNumber ((Arrow.context step.1).apply argument.live) := by
    unfold resultNumber
    rw [← resultEq]
    rfl
  omega

/-- **A growing family of numbers over the material members.** -/
def results : material.Elements ⥤ Type where
  obj point := {number : ℕ // resultBounds point number}
  map step := TypeCat.ofHom fun number => ⟨number.val, bound_follows step number.property⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro number
    exact Subtype.ext rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro number
    exact Subtype.ext rfl

/-- The first world. -/
abbrev origin : World grammar := ⟨0⟩

/-- The entry run along the growing arrow. -/
abbrev growingEntry : Entry Node := (.forward, .evolve .task)

/-- A pending task, placed fresh at the first world. -/
def taskPoint : material.Elements := ⟨origin, observation.app origin (fresh origin (.task ::ₘ 0))⟩

/-- The same member one script entry later. -/
def laterPoint : material.Elements :=
  ⟨next origin, observation.app (next origin) (transport (entryArrow origin growingEntry) (fresh origin (.task ::ₘ 0)))⟩

/-- The growing arrow between the two members. -/
def advance : taskPoint ⟶ laterPoint :=
  CategoryOfElements.homMk _ _ (entryArrow origin growingEntry)
    (observation.naturality (entryArrow origin growingEntry) (fresh origin (.task ::ₘ 0)))

theorem task_result_zero : resultNumber (.task ::ₘ 0) = 0 := by
  unfold resultNumber
  change (best readings.result (.task ::ₘ 0)).toNat = 0
  rw [best_cons, best_zero]
  rfl

theorem resultBounds_task (number : ℕ) : resultBounds taskPoint number ↔ number ≤ 0 := by
  constructor
  · intro bound
    have := bound (fresh origin (.task ::ₘ 0)) rfl
    change number ≤ resultNumber (Node.task ::ₘ 0) + 0 at this
    rw [task_result_zero] at this
    exact this
  · intro bound argument represents
    have related := observation_related represents
    have resultEq := readings_eq_of_observed (exact grammar) scale readings related .result
    have argumentZero : resultNumber argument.live = 0 := by
      unfold resultNumber
      rw [resultEq]
      exact task_result_zero
    change number ≤ resultNumber argument.live + 0
    omega

theorem resultBounds_later (number : ℕ) : resultBounds laterPoint number ↔ number ≤ 1 := by
  have transportedLive : (transport (entryArrow origin growingEntry) (fresh origin (.task ::ₘ 0))).live =
      .task ::ₘ 0 := Context.apply_one _
  constructor
  · intro bound
    have := bound (transport (entryArrow origin growingEntry) (fresh origin (.task ::ₘ 0))) rfl
    change number ≤ resultNumber (transport (entryArrow origin growingEntry) (fresh origin (.task ::ₘ 0))).live + 1
      at this
    rw [transportedLive, task_result_zero] at this
    exact this
  · intro bound argument represents
    have related := observation_related represents
    have resultEq := readings_eq_of_observed (exact grammar) scale readings related .result
    have argumentZero : resultNumber argument.live = 0 := by
      unfold resultNumber
      rw [resultEq, transportedLive]
      exact task_result_zero
    change number ≤ resultNumber argument.live + 1
    omega

/-- The number newly admitted one entry later. -/
def newlyAdmitted : results.obj laterPoint := ⟨1, (resultBounds_later 1).mpr le_rfl⟩

/-- **No earlier number reaches the newly admitted one.** -/
theorem new_member_admitted : ¬ ∃ earlier : results.obj taskPoint, results.map advance earlier = newlyAdmitted := by
  rintro ⟨earlier, same⟩
  have numbers := congrArg Subtype.val same
  change earlier.val = 1 at numbers
  have bound := (resultBounds_task earlier.val).mp earlier.property
  omega

abbrev parameters : material.Elements ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev booleanBody : results.Elements ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The constant `true`. -/
def alwaysTrue : NatTrans
    (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.overArguments results parameters) booleanBody where
  app _ := TypeCat.ofHom fun _ => true
  naturality _ _ _ := rfl

/-- The test `= 0`. -/
def onlyZero : NatTrans
    (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.overArguments results parameters) booleanBody where
  app argument := TypeCat.ofHom fun _ => decide (argument.2.val = 0)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro _
    have numbers := congrArg Subtype.val step.2
    change first.2.val = second.2.val at numbers
    exact congrArg (fun number => decide (number = 0)) numbers.symm

abbrev trueProduct := Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.piCurry results booleanBody alwaysTrue
abbrev zeroProduct := Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.piCurry results booleanBody onlyZero

theorem trueProduct_beta (point : material.Elements) (argument : results.obj point) :
    Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody point
      (trueProduct.app point PUnit.unit) argument = true :=
  congrArg (fun operation : NatTrans
    (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.overArguments results parameters) booleanBody =>
      operation.app ⟨point, argument⟩ PUnit.unit)
        (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.pi_uncurry_curry results booleanBody alwaysTrue)

theorem zeroProduct_beta (point : material.Elements) (argument : results.obj point) :
    Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody point
      (zeroProduct.app point PUnit.unit) argument = decide (argument.val = 0) :=
  congrArg (fun operation : NatTrans
    (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.overArguments results parameters) booleanBody =>
      operation.app ⟨point, argument⟩ PUnit.unit)
        (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.pi_uncurry_curry results booleanBody onlyZero)

/-- **The two products agree at every present argument.** -/
theorem same_all_present_applications (argument : results.obj taskPoint) :
    Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody taskPoint
      (trueProduct.app taskPoint PUnit.unit) argument =
    Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody taskPoint
      (zeroProduct.app taskPoint PUnit.unit) argument := by
  have zero := Nat.eq_zero_of_le_zero ((resultBounds_task argument.val).mp argument.property)
  rw [trueProduct_beta, zeroProduct_beta, zero]
  rfl

/-- **The two products differ**, at the argument newly admitted one entry
later. -/
theorem full_future_products_differ : trueProduct.app taskPoint PUnit.unit ≠ zeroProduct.app taskPoint PUnit.unit := by
  intro same
  have atFuture := congrArg
    (fun term => Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.pi results booleanBody |>.map
      advance term) same
  have first := congrArg (fun map => map PUnit.unit) (trueProduct.naturality advance)
  have second := congrArg (fun map => map PUnit.unit) (zeroProduct.naturality advance)
  have equality := first.trans (atFuture.trans second.symm)
  change trueProduct.app laterPoint PUnit.unit = zeroProduct.app laterPoint PUnit.unit at equality
  have applications := congrArg
    (fun term => Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody
      laterPoint term newlyAdmitted) equality
  rw [trueProduct_beta, zeroProduct_beta] at applications
  change true = false at applications
  exact Bool.noConfusion applications

end Products

/-! ## The future-only profile: the predecessor box does not descend -/

section FutureOnly

variable {V : Type} {G : Grammar V}

theorem card_le_of_splits {event : Event V} {source target : Multiset V} (splits : Splits G event source target) :
    Multiset.card source ≤ Multiset.card target + 1 := by
  obtain ⟨rest, rfl, rfl⟩ := splits
  simp only [Multiset.card_add]
  cases event with
  | evolve x =>
      change Multiset.card (x ::ₘ 0) + Multiset.card (0 : Multiset V) + _ ≤
        Multiset.card (G.evolve x ::ₘ 0) + Multiset.card (0 : Multiset V) + _ + 1
      simp only [Multiset.card_cons, Multiset.card_zero]
      omega
  | fork x =>
      change Multiset.card (0 : Multiset V) + Multiset.card (x ::ₘ 0) + _ ≤
        Multiset.card (x ::ₘ 0) + Multiset.card (x ::ₘ 0) + _ + 1
      simp only [Multiset.card_cons, Multiset.card_zero]
      omega
  | merge x y =>
      change Multiset.card (x ::ₘ y ::ₘ 0) + Multiset.card (0 : Multiset V) + _ ≤
        Multiset.card (G.merge x y ::ₘ 0) + Multiset.card (0 : Multiset V) + _ + 1
      simp only [Multiset.card_cons, Multiset.card_zero]
      omega
  | erase x =>
      change Multiset.card (x ::ₘ 0) + Multiset.card (0 : Multiset V) + _ ≤
        Multiset.card (0 : Multiset V) + Multiset.card (0 : Multiset V) + _ + 1
      simp only [Multiset.card_cons, Multiset.card_zero]
      omega

/-- The child of a fresh configuration along one forward entry is fresh. -/
theorem advanced_fresh {point : World G} {live : Multiset V} {entry : Entry V} {child : Placed (next point)}
    (advances : Advances (futureOnly G) (transport (entryArrow point entry) (fresh point live)) child) :
    child = fresh (next point) child.live := by
  obtain ⟨_, _, rest, scriptEq, _, _, originEq, childScript⟩ := advances
  have restNil : rest = [] := (List.cons.inj scriptEq).2.symm
  exact Placed.ext' rfl originEq (childScript.trans restNil)

theorem futureOnly_card_le : ∀ (size : ℕ) {point : World G} {left right : Multiset V},
    Multiset.card left = size →
      ContextualCoalgebraBisimulation.Bisimilar (coalgebra (futureOnly G)) point (fresh point left)
        (fresh point right) → Multiset.card right ≤ size
  | 0, point, left, right, leftSize, bisimilar => by
      have empty : left = 0 := Multiset.card_eq_zero.mp leftSize
      subst empty
      induction right using Quot.inductionOn with
      | h list =>
          cases list with
          | nil => exact Nat.le_refl _
          | cons z rest =>
              exfalso
              have emitted : Emits (futureOnly G) (fresh point ((z :: rest : List V) : Multiset V))
                  (entryArrow point (.forward, .erase z)) (fresh (next point) (rest : Multiset V)) := by
                refine ⟨(.forward, .erase z), (.forward, .erase z), [], rfl, ⟨rfl, rfl⟩, ?_, rfl, rfl⟩
                change Splits G (.erase z) ((Context.one G).apply ((z :: rest : List V) : Multiset V)) rest
                rw [Context.apply_one, coe_cons_eq]
                exact splits_erase_split G z rest
              obtain ⟨matching, available, _⟩ :=
                (ContextualCoalgebraBisimulation.bisimilar_isBisimulation (coalgebra (futureOnly G))).back
                  bisimilar ⟨next point, entryArrow point (.forward, .erase z)⟩ emitted
              obtain ⟨_, ⟨direction, event⟩, _, _, ⟨_, forward⟩, moves, _, _⟩ := available
              change direction = .forward at forward
              subst forward
              change Splits G event ((Context.one G).apply 0) matching.live at moves
              rw [Context.apply_one] at moves
              exact not_splits_zero G moves
  | size + 1, point, left, right, leftSize, bisimilar => by
      induction left using Quot.inductionOn with
      | h list =>
          cases list with
          | nil =>
              exfalso
              have leftLength : ([] : List V).length = size + 1 := leftSize
              rw [List.length_nil] at leftLength
              omega
          | cons x rest =>
              have emitted : Emits (futureOnly G) (fresh point ((x :: rest : List V) : Multiset V))
                  (entryArrow point (.forward, .erase x)) (fresh (next point) (rest : Multiset V)) := by
                refine ⟨(.forward, .erase x), (.forward, .erase x), [], rfl, ⟨rfl, rfl⟩, ?_, rfl, rfl⟩
                change Splits G (.erase x) ((Context.one G).apply ((x :: rest : List V) : Multiset V)) rest
                rw [Context.apply_one, coe_cons_eq]
                exact splits_erase_split G x rest
              obtain ⟨matching, available, related⟩ :=
                (ContextualCoalgebraBisimulation.bisimilar_isBisimulation (coalgebra (futureOnly G))).forth
                  bisimilar ⟨next point, entryArrow point (.forward, .erase x)⟩ emitted
              have related' : ContextualCoalgebraBisimulation.Bisimilar (coalgebra (futureOnly G)) (next point)
                  (fresh (next point) (rest : Multiset V))
                  (fresh (next point) (matching : Placed (next point)).live) := by
                rw [← advanced_fresh available]
                exact related
              obtain ⟨_, ⟨direction, event⟩, _, _, ⟨_, forward⟩, moves, _, _⟩ := available
              change direction = .forward at forward
              subst forward
              change Splits G event ((Context.one G).apply right) matching.live at moves
              rw [Context.apply_one] at moves
              have restSize : Multiset.card ((rest : List V) : Multiset V) = size := by
                have leftLength : (x :: rest).length = size + 1 := leftSize
                rw [Multiset.coe_card]
                rw [List.length_cons] at leftLength
                omega
              have smaller := futureOnly_card_le size restSize related'
              have step := card_le_of_splits moves
              omega

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W) (R : NodeReadings K V)

/-- **In the future-only profile, with readings that depend on size only, the
fresh kernel is equality of size.** -/
theorem futureOnly_fresh_observed_iff (sizeReadings : ∀ observation (first second : Multiset V),
      Multiset.card first = Multiset.card second → reading K R observation first = reading K R observation second)
    (point : World G) (first second : Multiset V) :
    ObservedBisimilar (futureOnly G) K R point (fresh point first) (fresh point second) ↔
      Multiset.card first = Multiset.card second := by
  constructor
  · intro related
    have bisimilar := bisimilar_of_observed (futureOnly G) K R related
    exact le_antisymm
      (futureOnly_card_le _ rfl (ContextualCoalgebraBisimulation.bisimilar_symm _ bisimilar))
      (futureOnly_card_le _ rfl bisimilar)
  · exact futureOnly_fresh_observed K R sizeReadings point

/-- Readings that are `0` everywhere. -/
def zeroReadings : NodeReadings scale Node where
  result _ := 0
  result_nonneg _ := Int.le_refl 0
  result_le_one _ := by decide
  faulty _ := false
  potential _ := 0

theorem zero_reading (observation : Reading) (live : Multiset Node) :
    reading scale zeroReadings observation live = 0 := by
  cases observation with
  | result =>
      induction live using Multiset.induction_on with
      | empty => rfl
      | cons x rest inductionHypothesis =>
          change best zeroReadings.result (x ::ₘ rest) = 0
          rw [best_cons]
          change max 0 (reading scale zeroReadings .result rest) = 0
          rw [inductionHypothesis]
          rfl
  | fault =>
      induction live using Multiset.induction_on with
      | empty => rfl
      | cons x rest inductionHypothesis =>
          change best (faultIndicator scale zeroReadings) (x ::ₘ rest) = 0
          rw [best_cons]
          change max 0 (reading scale zeroReadings .fault rest) = 0
          rw [inductionHypothesis]
          rfl
  | cost =>
      change scale.clamp (potentialSum zeroReadings.potential live) = 0
      have sumZero : potentialSum zeroReadings.potential live = 0 := by
        induction live using Multiset.induction_on with
        | empty => exact potentialSum_zero _
        | cons x rest inductionHypothesis =>
            rw [show (x ::ₘ rest) = (x ::ₘ 0) + rest from (Multiset.singleton_add x rest).symm, potentialSum_add',
              potentialSum_singleton, inductionHypothesis]
            rfl
      rw [sumZero]
      rfl

/-- Having more or fewer than one node. -/
def notSingle (live : Multiset Node) : Prop := Multiset.card live ≠ 1

theorem singleton_eq_add {a b : Node} {rest : Multiset Node} (same : (b ::ₘ 0) = (a ::ₘ 0) + rest) :
    rest = 0 ∧ a = b := by
  have sizes := congrArg Multiset.card same
  rw [Multiset.card_add, Multiset.card_cons, Multiset.card_cons, Multiset.card_zero] at sizes
  have restZero : rest = 0 := Multiset.card_eq_zero.mp (by omega)
  subst restZero
  rw [Multiset.add_zero] at same
  exact ⟨rfl, (Multiset.singleton_inj.mp same).symm⟩

/-- **Every step into a pending task starts from two nodes.** -/
theorem box_task : derivedBox (eventSpan grammar) notSingle (.task ::ₘ 0) := by
  rintro ⟨event, source, target, rest, sourceEq, targetEq⟩ reached
  change target = .task ::ₘ 0 at reached
  change Multiset.card source ≠ 1
  rw [reached] at targetEq
  rw [sourceEq]
  cases event with
  | evolve x =>
      exfalso
      change (.task ::ₘ 0) = (grammar.evolve x ::ₘ 0) + 0 + rest at targetEq
      rw [Multiset.add_zero] at targetEq
      obtain ⟨_, evolved⟩ := singleton_eq_add targetEq
      cases x <;> exact Node.noConfusion evolved
  | fork x =>
      exfalso
      have sizes := congrArg Multiset.card targetEq
      change Multiset.card (Node.task ::ₘ 0) = Multiset.card ((x ::ₘ 0) + (x ::ₘ 0) + rest) at sizes
      simp only [Multiset.card_add, Multiset.card_cons, Multiset.card_zero] at sizes
      omega
  | merge x y =>
      change (.task ::ₘ 0) = (grammar.merge x y ::ₘ 0) + 0 + rest at targetEq
      rw [Multiset.add_zero] at targetEq
      obtain ⟨restZero, _⟩ := singleton_eq_add targetEq
      subst restZero
      change Multiset.card ((x ::ₘ y ::ₘ 0) + 0 + 0) ≠ 1
      simp only [Multiset.card_add, Multiset.card_cons, Multiset.card_zero]
      omega
  | erase x =>
      change (.task ::ₘ 0) = 0 + 0 + rest at targetEq
      rw [Multiset.zero_add, Multiset.zero_add] at targetEq
      subst targetEq
      change Multiset.card ((x ::ₘ 0) + 0 + (.task ::ₘ 0)) ≠ 1
      simp only [Multiset.card_add, Multiset.card_cons, Multiset.card_zero]
      omega

/-- **A single pending task steps into a result.** -/
theorem not_box_done : ¬ derivedBox (eventSpan grammar) notSingle (.done ::ₘ 0) := by
  intro box
  exact box ⟨.evolve .task, .task ::ₘ 0, .done ::ₘ 0, 0, rfl, rfl⟩ rfl rfl

/-- **The future-only profile: the predecessor box does not descend.**  A
pending task and a result have one fresh material value; having a number of
nodes other than one is invariant under the kernel; its predecessor box holds
at the task and fails at the result; so incoming steps do not match modulo the
kernel. -/
theorem futureOnly_box_not_descends (point : World grammar) :
    (freshKernel (futureOnly grammar) scale zeroReadings nodeCoding listing integerCoding point).r
        (.task ::ₘ 0) (.done ::ₘ 0) ∧
      (∀ ⦃left right⦄, (freshKernel (futureOnly grammar) scale zeroReadings nodeCoding listing integerCoding
        point).r left right → (notSingle left ↔ notSingle right)) ∧
      derivedBox (eventSpan grammar) notSingle (.task ::ₘ 0) ∧
      ¬ derivedBox (eventSpan grammar) notSingle (.done ::ₘ 0) ∧
      ¬ PastMatching (eventSpan grammar)
        (freshKernel (futureOnly grammar) scale zeroReadings nodeCoding listing integerCoding point) := by
  have sizeReadings : ∀ observation (first second : Multiset Node),
      Multiset.card first = Multiset.card second →
        reading scale zeroReadings observation first = reading scale zeroReadings observation second :=
    fun observation first second _ => (zero_reading observation first).trans (zero_reading observation second).symm
  have kernel : ∀ first second,
      (freshKernel (futureOnly grammar) scale zeroReadings nodeCoding listing integerCoding point).r first second ↔
        Multiset.card first = Multiset.card second := fun first second =>
    (value_eq_iff (futureOnly grammar) scale zeroReadings nodeCoding listing integerCoding point _ _).trans
      (futureOnly_fresh_observed_iff scale zeroReadings sizeReadings point first second)
  have related := (kernel (.task ::ₘ 0) (.done ::ₘ 0)).mpr rfl
  have invariant : ∀ ⦃left right⦄, (freshKernel (futureOnly grammar) scale zeroReadings nodeCoding listing
      integerCoding point).r left right → (notSingle left ↔ notSingle right) := by
    intro left right same
    unfold notSingle
    rw [(kernel left right).mp same]
  refine ⟨related, invariant, box_task, not_box_done, fun matching => ?_⟩
  exact not_box_done (((fresh_box_descends_iff (futureOnly grammar) scale zeroReadings nodeCoding listing
    integerCoding point).mpr matching notSingle invariant related).mp box_task)

end FutureOnly

/-! ## Endpoint lifts do not recover an erased occurrence -/

section Copies

variable {V : Type} [DecidableEq V] (G : Grammar V)

omit [DecidableEq V] in
theorem principal_mem {event : Event V} {source target : Multiset V} (splits : Splits G event source target) :
    principal event ∈ source := by
  obtain ⟨rest, rfl, -⟩ := splits
  refine Multiset.mem_add.mpr (Or.inl ?_)
  cases event with
  | evolve x => exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self x 0))
  | fork x => exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons_self x 0))
  | merge x y =>
      refine Multiset.mem_add.mpr (Or.inl ?_)
      change x ∈ x ::ₘ y ::ₘ 0
      exact Multiset.mem_cons_self x _
  | erase x => exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self x 0))

/-- A labelled step and the copy of its principal node that it uses. -/
structure CopyStep where
  step : EventStep G
  copy : Fin (step.source.count (principal step.event))

/-- The span of copy-carrying steps. -/
def copySpan : ReductionSpan (Multiset V) where
  Edge := CopyStep G
  source occurrence := occurrence.step.source
  target occurrence := occurrence.step.target

/-- **Forgetting the copy.** -/
def forgetCopy : SpanMap (copySpan G) (eventSpan G) where
  states := id
  events occurrence := occurrence.step
  source_comm _ := rfl
  target_comm _ := rfl

/-- The first copy of the principal node. -/
def firstCopy (step : EventStep G) : CopyStep G :=
  ⟨step, ⟨0, Multiset.count_pos.mpr (principal_mem G step.splits)⟩⟩

/-- **Endpoint lifts do not recover an erased occurrence.**  Forgetting the
copy has both occurrence lifts, hence both endpoint lifts, and no choice of a
copy-carrying step from its labelled step returns both copies erased from
`{x, x}`. -/
theorem endpoint_lifts_not_recovery (x : V) :
    (forgetCopy G).SourceOccurrenceLifts ∧ (forgetCopy G).TargetOccurrenceLifts ∧
      (forgetCopy G).SourceLifts ∧ (forgetCopy G).TargetLifts ∧
      ¬ ∃ pick : EventStep G → CopyStep G, ∀ occurrence, pick ((forgetCopy G).events occurrence) = occurrence := by
  have sourceLifts : (forgetCopy G).SourceOccurrenceLifts :=
    fun _ step sourceEq => ⟨firstCopy G step, sourceEq, rfl⟩
  have targetLifts : (forgetCopy G).TargetOccurrenceLifts :=
    fun _ step targetEq => ⟨firstCopy G step, targetEq, rfl⟩
  refine ⟨sourceLifts, targetLifts, (forgetCopy G).sourceLifts_of_occurrence sourceLifts,
    (forgetCopy G).targetLifts_of_occurrence targetLifts, ?_⟩
  rintro ⟨pick, recovers⟩
  let erased : EventStep G := ⟨.erase x, x ::ₘ x ::ₘ 0, x ::ₘ 0, splits_erase_double G x⟩
  have twice : (x ::ₘ x ::ₘ 0 : Multiset V).count (principal (Event.erase x)) = 2 := by
    change (x ::ₘ x ::ₘ 0 : Multiset V).count x = 2
    rw [Multiset.count_cons_self, Multiset.count_cons_self, Multiset.count_zero]
  have firstPicked := recovers ⟨erased, ⟨0, by rw [twice]; omega⟩⟩
  have secondPicked := recovers ⟨erased, ⟨1, by rw [twice]; omega⟩⟩
  have same := firstPicked.symm.trans secondPicked
  have copies := congrArg (fun occurrence : CopyStep G => (occurrence.copy : ℕ)) same
  change 0 = 1 at copies
  omega

end Copies

/-! ## Renamings: source and target back laws -/

section Renamings

/-- Evolution fixes every number and merge keeps its left node. -/
def shiftGrammar : Grammar ℕ := ⟨fun x => x, fun x _ => x⟩

/-- **The successor renaming**: injective, commuting with the grammar, not
onto. -/
def shiftRenaming : Renaming shiftGrammar where
  map := Nat.succ
  injective _ _ same := Nat.succ.inj same
  evolve_comm _ := rfl
  merge_comm _ _ := rfl

/-- **The source back law without the target back law**: the successor
renaming lifts every source occurrence and does not lift target endpoints,
since nothing renames to `0`. -/
theorem shift_source_not_target :
    (contextSpan shiftGrammar (Context.ofRenaming shiftRenaming)).SourceOccurrenceLifts ∧
      (contextSpan shiftGrammar (Context.ofRenaming shiftRenaming)).SourceLifts ∧
      ¬ (contextSpan shiftGrammar (Context.ofRenaming shiftRenaming)).TargetLifts := by
  have lifts := sourceOccurrenceLifts_of_leftInverse (Context.ofRenaming shiftRenaming) rfl Nat.pred
    (fun _ => rfl)
  refine ⟨lifts, (contextSpan _ _).sourceLifts_of_occurrence lifts, fun target => ?_⟩
  obtain ⟨x, renamed⟩ := onto_of_targetLifts target 0
  exact Nat.succ_ne_zero x renamed

open HistoryObserverControls (swapGrammar)

/-- **The node swap**: a bijective renaming of the swap grammar. -/
def swapRenaming : Renaming swapGrammar where
  map := not
  injective first second same := by
    cases first <;> cases second <;> first | rfl | exact Bool.noConfusion same
  evolve_comm _ := rfl
  merge_comm _ _ := rfl

/-- **All four occurrence laws hold for a bijective renaming that is not the
identity**, so the future diamond and the predecessor box commute with it. -/
theorem swap_all_laws :
    swapRenaming.map ≠ id ∧
      (contextSpan swapGrammar (Context.ofRenaming swapRenaming)).SourceOccurrenceLifts ∧
      (contextSpan swapGrammar (Context.ofRenaming swapRenaming)).TargetOccurrenceLifts ∧
      ∀ (predicate : Multiset Bool → Prop) (live : Multiset Bool),
        derivedBox (eventSpan swapGrammar) predicate ((Context.ofRenaming swapRenaming).apply live) ↔
          derivedBox (eventSpan swapGrammar) (predicate ∘ (Context.ofRenaming swapRenaming).apply) live := by
  have onto : Function.Surjective swapRenaming.map := fun y => ⟨!y, Bool.not_not y⟩
  refine ⟨fun same => Bool.noConfusion (congrFun same true), ?_, ?_, ?_⟩
  · exact (contextSpan_sourceOccurrenceLifts_iff HistoryCoverageControls.boolListing _).mpr rfl
  · exact (contextSpan_targetOccurrenceLifts_iff HistoryCoverageControls.boolListing _).mpr ⟨rfl, onto⟩
  · exact (box_natural_iff HistoryCoverageControls.boolListing _).mpr ⟨rfl, onto⟩

end Renamings

/-! ## A pending task in context -/

/-- **The future diamond and the predecessor box do not commute with a pending
task placed in context.** -/
theorem pending_frame_not_natural :
    (¬ ∀ (predicate : Multiset Node → Prop) (live : Multiset Node),
      derivedDiamond (eventSpan grammar) predicate (pendingFrame.apply live) ↔
        derivedDiamond (eventSpan grammar) (predicate ∘ pendingFrame.apply) live) ∧
    ¬ ∀ (predicate : Multiset Node → Prop) (live : Multiset Node),
      derivedBox (eventSpan grammar) predicate (pendingFrame.apply live) ↔
        derivedBox (eventSpan grammar) (predicate ∘ pendingFrame.apply) live :=
  ⟨fun natural => List.cons_ne_nil _ _ ((diamond_natural_iff listing pendingFrame).mp natural),
    fun natural => List.cons_ne_nil _ _ ((box_natural_iff listing pendingFrame).mp natural).1⟩

end Mettapedia.GSLT.Distinction.HistoryContextControls
