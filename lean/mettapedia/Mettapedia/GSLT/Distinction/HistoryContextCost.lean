import Mettapedia.GSLT.Distinction.HistoryContextTwoSided
import Mettapedia.GSLT.Distinction.HistoryCoverageControls

/-!
# Costs in context: the counterexample and two repairs

The cost reading of `HistoryObserver` clamps the extensive potential of a
configuration to `[0, one]`.  A clamped reading is not congruent under all
context additions: two configurations read alike, and the same frame placed
beside them makes them read differently.  This module states that as a
theorem and gives two repairs, each as one transport theorem whose replay
criterion is one of its own clauses.

* **Runs in context** (`splitPresentation`, `transportRun`, `onPath_transportRun`).
  Runs are occurrence paths of the history GSLT by splitting; a context
  transports every run, renaming its events.
* **One transport theorem with its replay criterion** (`ContextTransport`).  For
  an observation of configurations, a reading of it, a budget and a class of
  admissible contexts: the class contains the identity and is closed under
  composition; after an admissible context the observation is a function of the
  observation before it; and every run between endpoints within the budget,
  transported by an admissible context, costs the change of the read
  observation between the transported endpoints.  Replay of any run by any
  other with the same endpoints is then qualified in every admissible context
  (`ContextTransport.qualified_replay`).
* **The counterexample** (`clamped_not_congruent`, `clamped_frame_congruent_iff`).
  On the authored instance with signed potentials, a failure and the empty
  configuration both read cost `0`, and with a pending task beside them they
  read `1` and `0`.  For a frame, the clamped reading is congruent exactly when
  the frame's potential is `0`.
* **Repair (a): an observer that retains the potential** (`retained_transport`).
  The exact extensive potential is congruent under every context whose renaming
  preserves the node potential, and it reads every run in every such context;
  the clamped cost after any such context is a function of it
  (`clamped_of_retained`).
* **Repair (b): an admissible class** (`neutral_transport`).  For contexts whose
  renaming preserves the node potential and whose frame has potential `0`, the
  clamped reading itself is congruent, and it reads every run between endpoints
  within budget.  These contexts form a wide subcategory (`Neutral.one`,
  `Neutral.andThen`).
* **State potentials are not path work** (`work_transport`, `levels_in_context`).
  A context keeps the unit work of every run, and still the replay of a copy and
  its erasure by the empty run is qualified for a readable cost and not for the
  work, in every context.

**Choice.**  Every declaration of this module is free of `Classical.choice`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryContextCost

open Mettapedia.GSLT
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver (Reading NodeReadings reading potentialSum PotentialLaws)
open Mettapedia.GSLT.Distinction.HistoryContextCategory
open Mettapedia.GSLT.Distinction.HistoryObserverControls (relabel)
open Mettapedia.GSLT.Distinction.HistoryIndependence (consumed read produced)
open Mettapedia.GSLT.Distinction.Constructive (Scale)
open Mettapedia.GSLT.Distinction.LevelAccounts (QualifiedReplay LevelReadings)
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.TraceCostValuation (pathAccount)
open Mettapedia.Effects
open Mettapedia.Cybernetics.DistinctionCalculus.History

variable {V : Type} (G : Grammar V)

/-! ## Runs in context -/

/-- The history GSLT by splitting, presented with events as sites. -/
abbrev splitPresentation : InteractionPresentation (splitGSLT G) where
  Site := Event V
  Event event live result := PLift (Splits G event live result)
  sound evidence := ⟨_, evidence.down⟩

/-- An event cost as an occurrence valuation. -/
def costValuation {A : Type} [AddMonoid A] (cost : Event V → A) : OccurrenceValuation (splitPresentation G) A where
  grade occurrence := cost occurrence.site

/-- **A context transports every run**, renaming its events. -/
def transportRun (context : Context G) : ∀ {source target : Multiset V},
    OccurrencePath (splitPresentation G) source target →
      OccurrencePath (splitPresentation G) (context.apply source) (context.apply target)
  | _, _, .refl live => OccurrencePath.refl (P := splitPresentation G) (context.apply live)
  | _, _, .cons occurrence rest =>
      .cons ⟨context.event occurrence.site, ⟨splits_apply G context occurrence.evidence.down⟩⟩
        (transportRun context rest)

/-- The cost of a transported run is the renamed cost of the run. -/
theorem onPath_transportRun {A : Type} [AddMonoid A] (cost : Event V → A) (context : Context G) :
    ∀ {source target : Multiset V} (run : OccurrencePath (splitPresentation G) source target),
      (costValuation G cost).onPath (transportRun G context run) =
        (costValuation G (fun event => cost (context.event event))).onPath run
  | _, _, .refl _ => rfl
  | _, _, .cons occurrence rest => by
      change cost (context.event occurrence.site) + (costValuation G cost).onPath (transportRun G context rest) =
        cost (context.event occurrence.site) + _
      rw [onPath_transportRun cost context rest]

/-! ## Potentials -/

section Potentials

variable {W : Type} [AddCommGroup W]

theorem potentialSum_add' (potential : V → W) (first second : Multiset V) :
    potentialSum potential (first + second) = potentialSum potential first + potentialSum potential second := by
  unfold potentialSum
  rw [Multiset.map_add, Multiset.sum_add]

theorem potentialSum_singleton (potential : V → W) (x : V) :
    potentialSum potential (x ::ₘ 0) = potential x := by
  unfold potentialSum
  rw [Multiset.map_cons, Multiset.map_zero, Multiset.sum_cons, Multiset.sum_zero, add_zero]

theorem potentialSum_zero (potential : V → W) : potentialSum potential (0 : Multiset V) = 0 := by
  unfold potentialSum
  rw [Multiset.map_zero, Multiset.sum_zero]

/-- With the potential laws an event costs what it produces less what it
consumes. -/
theorem cost_eq_of_laws {cost : Event V → W} {potential : V → W} (laws : PotentialLaws G cost potential)
    (event : Event V) :
    cost event = potentialSum potential (produced G event) - potentialSum potential (consumed event) := by
  cases event with
  | evolve x =>
      change cost (.evolve x) = potentialSum potential (G.evolve x ::ₘ 0) - potentialSum potential (x ::ₘ 0)
      rw [potentialSum_singleton, potentialSum_singleton]
      exact (laws x x).1
  | fork x =>
      change cost (.fork x) = potentialSum potential (x ::ₘ 0) - potentialSum potential 0
      rw [potentialSum_singleton, potentialSum_zero, sub_zero]
      exact (laws x x).2.1
  | merge x y =>
      change cost (.merge x y) = potentialSum potential (G.merge x y ::ₘ 0) -
        potentialSum potential (x ::ₘ y ::ₘ 0)
      have pair : potentialSum potential (x ::ₘ y ::ₘ 0) = potential x + potential y := by
        unfold potentialSum
        rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_zero, Multiset.sum_cons, Multiset.sum_cons,
          Multiset.sum_zero, add_zero]
      rw [potentialSum_singleton, pair, (laws x y).2.2.2, sub_sub]
  | erase x =>
      change cost (.erase x) = potentialSum potential 0 - potentialSum potential (x ::ₘ 0)
      rw [potentialSum_singleton, potentialSum_zero, zero_sub]
      exact (laws x x).2.2.1

/-- **A split changes the potential by the cost of its event.** -/
theorem splits_potential {cost : Event V → W} {potential : V → W} (laws : PotentialLaws G cost potential)
    {event : Event V} {source target : Multiset V} (splits : Splits G event source target) :
    potentialSum potential target - potentialSum potential source = cost event := by
  obtain ⟨rest, rfl, rfl⟩ := splits
  rw [cost_eq_of_laws G laws, potentialSum_add', potentialSum_add', potentialSum_add', potentialSum_add']
  abel

/-- **A cost with the potential laws is read by the potential on every run.** -/
theorem onPath_potential {cost : Event V → W} {potential : V → W} (laws : PotentialLaws G cost potential) :
    ∀ {source target : Multiset V} (run : OccurrencePath (splitPresentation G) source target),
      (costValuation G cost).onPath run = potentialSum potential target - potentialSum potential source
  | _, _, .refl _ => (sub_self _).symm
  | _, _, .cons occurrence rest => by
      change cost occurrence.site + (costValuation G cost).onPath rest = _
      rw [onPath_potential laws rest, ← splits_potential G laws occurrence.evidence.down]
      abel

variable {G}

/-- A context whose renaming preserves the node potential. -/
def PotentialPreserving (potential : V → W) (context : Context G) : Prop :=
  ∀ x, potential (context.rename.map x) = potential x

omit [AddCommGroup W] in
theorem PotentialPreserving.one (potential : V → W) : PotentialPreserving potential (Context.one G) :=
  fun _ => rfl

omit [AddCommGroup W] in
theorem PotentialPreserving.andThen {potential : V → W} {earlier later : Context G}
    (first : PotentialPreserving potential earlier) (second : PotentialPreserving potential later) :
    PotentialPreserving potential (earlier.andThen later) := fun x => by
  change potential (later.rename.map (earlier.rename.map x)) = potential x
  rw [second, first]

theorem potentialSum_map_preserving {potential : V → W} {context : Context G}
    (preserving : PotentialPreserving potential context) (live : Multiset V) :
    potentialSum potential (live.map context.rename.map) = potentialSum potential live := by
  unfold potentialSum
  rw [Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun x _ => preserving x)

/-- **The potential in context**: the potential before the context plus the
potential of the frame. -/
theorem potentialSum_apply {potential : V → W} {context : Context G}
    (preserving : PotentialPreserving potential context) (live : Multiset V) :
    potentialSum potential (context.apply live) =
      potentialSum potential live + potentialSum potential (context.frame : Multiset V) := by
  unfold Context.apply
  rw [potentialSum_add', potentialSum_map_preserving preserving]

/-- A potential-preserving context keeps every cost with the potential laws. -/
theorem cost_context {cost : Event V → W} {potential : V → W} (laws : PotentialLaws G cost potential)
    {context : Context G} (preserving : PotentialPreserving potential context) (event : Event V) :
    cost (context.event event) = cost event := by
  have produced_eq : potentialSum potential (produced G (context.event event)) =
      potentialSum potential (produced G event) := by
    change potentialSum potential (produced G (relabel context.rename.map event)) = _
    rw [produced_relabel (renaming_equivariant context.rename), potentialSum_map_preserving preserving]
  have consumed_eq : potentialSum potential (consumed (context.event event)) =
      potentialSum potential (consumed event) := by
    change potentialSum potential (consumed (relabel context.rename.map event)) = _
    rw [consumed_relabel, potentialSum_map_preserving preserving]
  rw [cost_eq_of_laws G laws, cost_eq_of_laws G laws, produced_eq, consumed_eq]

/-- A context whose renaming preserves the potential and whose frame has
potential `0`. -/
def Neutral (potential : V → W) (context : Context G) : Prop :=
  PotentialPreserving potential context ∧ potentialSum potential (context.frame : Multiset V) = 0

theorem Neutral.one (potential : V → W) : Neutral potential (Context.one G) :=
  ⟨PotentialPreserving.one potential, potentialSum_zero potential⟩

/-- **Neutral contexts compose**: with the identity they form a wide
subcategory of the context category. -/
theorem Neutral.andThen {potential : V → W} {earlier later : Context G} (first : Neutral potential earlier)
    (second : Neutral potential later) : Neutral potential (earlier.andThen later) := by
  refine ⟨first.1.andThen second.1, ?_⟩
  change potentialSum potential ((earlier.frame.map later.rename.map ++ later.frame : List V) : Multiset V) = 0
  rw [← Multiset.coe_add, potentialSum_add', ← Multiset.map_coe, potentialSum_map_preserving second.1,
    first.2, second.2, add_zero]

end Potentials

/-! ## One transport theorem with its replay criterion -/

section Transport

variable {W : Type} [AddCommGroup W]

variable {G}

/-- **Context transport of an observation, with its replay criterion.**  The
admissible contexts contain the identity and compose; after an admissible
context the observation is a function of the observation before it; and every
run between endpoints within the budget, transported by an admissible context,
costs the change of the read observation between the transported endpoints. -/
structure ContextTransport {O : Type} (observe : Multiset V → O) (readValue : O → W)
    (budget : Multiset V → Prop) (admissible : Context G → Prop) (cost : Event V → W) : Prop where
  admissible_one : admissible (Context.one G)
  admissible_andThen : ∀ {earlier later : Context G}, admissible earlier → admissible later →
    admissible (earlier.andThen later)
  congruent : ∀ {context : Context G}, admissible context →
    ∃ act : O → O, ∀ live, observe (context.apply live) = act (observe live)
  replay : ∀ {context : Context G}, admissible context →
    ∀ {source target : Multiset V} (run : OccurrencePath (splitPresentation G) source target),
      budget source → budget target →
        (costValuation G cost).onPath (transportRun G context run) =
          readValue (observe (context.apply target)) - readValue (observe (context.apply source))

/-- **Replay is qualified in every admissible context**: two runs between the
same endpoints within budget, transported by an admissible context, have one
account. -/
theorem ContextTransport.qualified_replay {O : Type} {observe : Multiset V → O} {readValue : O → W}
    {budget : Multiset V → Prop} {admissible : Context G → Prop} {cost : Event V → W}
    (transport : ContextTransport observe readValue budget admissible cost) {context : Context G}
    (admitted : admissible context) {source target : Multiset V}
    (first second : OccurrencePath (splitPresentation G) source target) (sourceBudget : budget source)
    (targetBudget : budget target) :
    QualifiedReplay (pathAccount (costValuation G cost)) (transportRun G context first)
      (transportRun G context second) := by
  change Multiplicative.ofAdd ((costValuation G cost).onPath (transportRun G context first)) =
    Multiplicative.ofAdd ((costValuation G cost).onPath (transportRun G context second))
  rw [transport.replay admitted first sourceBudget targetBudget,
    transport.replay admitted second sourceBudget targetBudget]

/-- **Repair (a): an observer that retains the potential.**  The exact
extensive potential is transported by every context whose renaming preserves
the node potential, and it reads every transported run. -/
theorem retained_transport {cost : Event V → W} {potential : V → W} (laws : PotentialLaws G cost potential) :
    ContextTransport (G := G) (potentialSum potential) id (fun _ => True) (PotentialPreserving potential) cost where
  admissible_one := PotentialPreserving.one potential
  admissible_andThen first second := first.andThen second
  congruent {context} preserving :=
    ⟨fun value => value + potentialSum potential (context.frame : Multiset V), potentialSum_apply preserving⟩
  replay {_} _ _ _ _ _ _ := onPath_potential G laws _

variable [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-- **The clamped cost after a context is read off the retained potential.** -/
theorem clamped_of_retained (R : NodeReadings K V) {context : Context G}
    (preserving : PotentialPreserving R.potential context) (live : Multiset V) :
    reading K R .cost (context.apply live) =
      K.clamp (potentialSum R.potential live + potentialSum R.potential (context.frame : Multiset V)) := by
  change K.clamp (potentialSum R.potential (context.apply live)) = _
  rw [potentialSum_apply preserving]

/-- Configurations whose potential lies within `[0, one]`. -/
def WithinBudget (R : NodeReadings K V) (live : Multiset V) : Prop :=
  0 ≤ potentialSum R.potential live ∧ potentialSum R.potential live ≤ K.one

/-- **Repair (b): a restricted admissible class.**  For neutral contexts the
clamped cost reading itself is transported unchanged, and it reads every
transported run between endpoints within budget. -/
theorem neutral_transport (R : NodeReadings K V) {cost : Event V → W}
    (laws : PotentialLaws G cost R.potential) :
    ContextTransport (G := G) (reading K R .cost) id (WithinBudget K R) (Neutral R.potential) cost where
  admissible_one := Neutral.one R.potential
  admissible_andThen first second := first.andThen second
  congruent {context} neutral := ⟨id, fun live => by
    rw [clamped_of_retained K R neutral.1, neutral.2, add_zero]
    rfl⟩
  replay {context} neutral source target run sourceBudget targetBudget := by
    have inBudget : ∀ live, WithinBudget K R live →
        reading K R .cost (context.apply live) = potentialSum R.potential (context.apply live) := by
      intro live within
      rw [clamped_of_retained K R neutral.1, neutral.2, add_zero, potentialSum_apply neutral.1, neutral.2,
        add_zero]
      exact K.clamp_of_mem within.1 within.2
    change _ = reading K R .cost (context.apply target) - reading K R .cost (context.apply source)
    rw [inBudget target targetBudget, inBudget source sourceBudget]
    exact onPath_potential G laws _

/-- **The clamped reading fails to be congruent for a context** as soon as two
configurations read alike and the context separates them. -/
theorem clamped_not_congruent_of (R : NodeReadings K V) (context : Context G) {first second : Multiset V}
    (alike : reading K R .cost first = reading K R .cost second)
    (separated : reading K R .cost (context.apply first) ≠ reading K R .cost (context.apply second)) :
    ¬ ∃ act : W → W, ∀ live, reading K R .cost (context.apply live) = act (reading K R .cost live) := by
  rintro ⟨act, congruent⟩
  exact separated ((congruent first).trans ((congrArg act alike).trans (congruent second).symm))

end Transport

/-! ## State potentials and path work -/

section Work

/-- One unit of work per event. -/
def unitWork : Event V → ℤ := fun _ => 1

/-- **A context keeps the work of every run.** -/
theorem work_transport (context : Context G) {source target : Multiset V}
    (run : OccurrencePath (splitPresentation G) source target) :
    (costValuation G unitWork).onPath (transportRun G context run) = (costValuation G unitWork).onPath run :=
  onPath_transportRun G unitWork context run

theorem splits_fork_single (x : V) : Splits G (.fork x) (x ::ₘ 0) (x ::ₘ x ::ₘ 0) :=
  ⟨0, by
    change _ = 0 + (x ::ₘ 0) + 0
    rw [Multiset.zero_add, Multiset.add_zero], rfl⟩

theorem splits_erase_double (x : V) : Splits G (.erase x) (x ::ₘ x ::ₘ 0) (x ::ₘ 0) :=
  ⟨x ::ₘ 0, rfl, by
    change _ = 0 + 0 + (x ::ₘ 0)
    rw [Multiset.zero_add, Multiset.zero_add]⟩

/-- The loop that copies a node and erases the copy. -/
def forkEraseLoop (x : V) : OccurrencePath (splitPresentation G) (x ::ₘ 0) (x ::ₘ 0) :=
  .cons ⟨.fork x, ⟨splits_fork_single G x⟩⟩ (.cons ⟨.erase x, ⟨splits_erase_double G x⟩⟩
    (OccurrencePath.refl (P := splitPresentation G) _))

/-- The levels of a run: a reference cost, the unit work and no overhead. -/
def levels {W : Type} [AddCommGroup W] (reference : Event V → W) :
    LevelReadings (OccurrenceCat (splitPresentation G)) (Multiplicative W) (Multiplicative ℤ)
      (Multiplicative ℤ) where
  reference := pathAccount (costValuation G reference)
  work := pathAccount (costValuation G unitWork)
  overhead := RunAccount.trivial _ _

/-- **In every context, replaying the copy-and-erase loop by the empty run is
qualified for a readable reference cost, and not for the work or the three
levels together.**  A state potential reads the reference; no state reading
reads the work. -/
theorem levels_in_context {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    {reference : Event V → W} {potential : V → W} (laws : PotentialLaws G reference potential)
    (context : Context G) (x : V) :
    QualifiedReplay (levels G reference).reference (transportRun G context (forkEraseLoop G x))
        (transportRun G context (OccurrencePath.refl (P := splitPresentation G) (x ::ₘ 0))) ∧
      ¬ QualifiedReplay (levels G reference).work (transportRun G context (forkEraseLoop G x))
        (transportRun G context (OccurrencePath.refl (P := splitPresentation G) (x ::ₘ 0))) ∧
      ¬ QualifiedReplay (levels G reference).total (transportRun G context (forkEraseLoop G x))
        (transportRun G context (OccurrencePath.refl (P := splitPresentation G) (x ::ₘ 0))) := by
  have referenceQualified : QualifiedReplay (levels G reference).reference
      (transportRun G context (forkEraseLoop G x)) (transportRun G context (OccurrencePath.refl (P := splitPresentation G) (x ::ₘ 0))) := by
    change Multiplicative.ofAdd ((costValuation G reference).onPath (transportRun G context (forkEraseLoop G x))) =
      Multiplicative.ofAdd ((costValuation G reference).onPath (transportRun G context (OccurrencePath.refl (P := splitPresentation G) (x ::ₘ 0))))
    rw [onPath_potential G laws, onPath_potential G laws]
  have workNot : ¬ QualifiedReplay (levels G reference).work (transportRun G context (forkEraseLoop G x))
      (transportRun G context (OccurrencePath.refl (P := splitPresentation G) (x ::ₘ 0))) := by
    intro qualified
    have costs := Multiplicative.ofAdd.injective qualified
    change (costValuation G unitWork).onPath (transportRun G context (forkEraseLoop G x)) =
      (costValuation G unitWork).onPath (transportRun G context (OccurrencePath.refl (P := splitPresentation G) (x ::ₘ 0))) at costs
    rw [work_transport, work_transport] at costs
    change (1 : ℤ) + (1 + 0) = 0 at costs
    omega
  refine ⟨referenceQualified, workNot, fun total => ?_⟩
  exact workNot (((LevelReadings.total_iff (levels G reference) _ _).mp total).2.1)

end Work

/-! ## The counterexample on the authored instance -/

section Instance

open HistoryCoverageControls (Node grammar scale)
open HistoryCoverageControls.Node

/-- **Signed readings**: no result, no fault, a pending task carries one unit
of potential and a failure minus one. -/
def signedReadings : NodeReadings scale Node where
  result _ := 0
  result_nonneg _ := Int.le_refl 0
  result_le_one _ := by decide
  faulty _ := false
  potential
    | .task => 1
    | .failed => -1
    | .done => 0

/-- The clamped cost of the signed readings. -/
abbrev clampedCost (live : Multiset Node) : ℤ := reading scale signedReadings .cost live

theorem clampedCost_eq (live : Multiset Node) :
    clampedCost live = max 0 (min 1 (potentialSum signedReadings.potential live)) := rfl

theorem signed_replicate (node : Node) : ∀ count : ℕ,
    potentialSum signedReadings.potential (Multiset.replicate count node) =
      count * signedReadings.potential node
  | 0 => by
      rw [Multiset.replicate_zero, potentialSum_zero, Nat.cast_zero, zero_mul]
  | count + 1 => by
      rw [Multiset.replicate_succ, show (node ::ₘ Multiset.replicate count node) =
          (node ::ₘ 0) + Multiset.replicate count node from (Multiset.singleton_add _ _).symm,
        potentialSum_add', potentialSum_singleton, signed_replicate node count]
      push_cast
      ring

/-- A pending task as a frame. -/
def pendingFrame : Context grammar := Context.ofFrame grammar [.task]

theorem pendingFrame_apply (live : Multiset Node) : pendingFrame.apply live = live + (.task ::ₘ 0) :=
  Context.apply_ofFrame (G := grammar) [Node.task] live

/-- **The counterexample**: the empty configuration and a failure both read
cost `0`; with a pending task beside them they read `1` and `0`.  So the clamped
cost reading is not congruent for this context. -/
theorem clamped_not_congruent :
    clampedCost 0 = clampedCost (.failed ::ₘ 0) ∧
      clampedCost (pendingFrame.apply 0) = 1 ∧ clampedCost (pendingFrame.apply (.failed ::ₘ 0)) = 0 ∧
      ¬ ∃ act : ℤ → ℤ, ∀ live, clampedCost (pendingFrame.apply live) = act (clampedCost live) := by
  have empty : clampedCost 0 = 0 := by
    rw [clampedCost_eq, potentialSum_zero]
    rfl
  have failure : clampedCost (.failed ::ₘ 0) = 0 := by
    rw [clampedCost_eq, potentialSum_singleton]
    rfl
  have emptyFramed : clampedCost (pendingFrame.apply 0) = 1 := by
    rw [clampedCost_eq, pendingFrame_apply, Multiset.zero_add, potentialSum_singleton]
    rfl
  have failureFramed : clampedCost (pendingFrame.apply (.failed ::ₘ 0)) = 0 := by
    rw [clampedCost_eq, pendingFrame_apply, potentialSum_add', potentialSum_singleton, potentialSum_singleton]
    rfl
  refine ⟨empty.trans failure.symm, emptyFramed, failureFramed, ?_⟩
  exact clamped_not_congruent_of scale signedReadings pendingFrame (empty.trans failure.symm)
    (fun same => absurd (emptyFramed.symm.trans (same.trans failureFramed)) (by decide))

/-- **For a frame, the clamped cost is congruent exactly when the frame has
potential `0`.** -/
theorem clamped_frame_congruent_iff (frame : List Node) :
    (∃ act : ℤ → ℤ, ∀ live, clampedCost ((Context.ofFrame grammar frame).apply live) = act (clampedCost live)) ↔
      potentialSum signedReadings.potential (frame : Multiset Node) = 0 := by
  have framed : ∀ live, clampedCost ((Context.ofFrame grammar frame).apply live) =
      max 0 (min 1 (potentialSum signedReadings.potential live +
        potentialSum signedReadings.potential (frame : Multiset Node))) := by
    intro live
    rw [clampedCost_eq, Context.apply_ofFrame, potentialSum_add']
  constructor
  · rintro ⟨act, congruent⟩
    rcases Int.lt_trichotomy (potentialSum signedReadings.potential (frame : Multiset Node)) 0 with
      negative | zero | positive
    · exfalso
      obtain ⟨count, hcount⟩ : ∃ count : ℕ,
          potentialSum signedReadings.potential (frame : Multiset Node) = -((count : ℤ) + 1) :=
        ⟨(-(potentialSum signedReadings.potential (frame : Multiset Node)) - 1).toNat, by omega⟩
      have first := congruent (Multiset.replicate (count + 1) .task)
      have second := congruent (Multiset.replicate (count + 2) .task)
      rw [framed, clampedCost_eq, signed_replicate] at first second
      change max 0 (min 1 (((count + 1 : ℕ) : ℤ) * 1 + _)) = act (max 0 (min 1 (((count + 1 : ℕ) : ℤ) * 1)))
        at first
      change max 0 (min 1 (((count + 2 : ℕ) : ℤ) * 1 + _)) = act (max 0 (min 1 (((count + 2 : ℕ) : ℤ) * 1)))
        at second
      rw [hcount] at first second
      have low : max (0 : ℤ) (min 1 (((count + 1 : ℕ) : ℤ) * 1)) = 1 := by push_cast; omega
      have high : max (0 : ℤ) (min 1 (((count + 2 : ℕ) : ℤ) * 1)) = 1 := by push_cast; omega
      have lowFramed : max (0 : ℤ) (min 1 (((count + 1 : ℕ) : ℤ) * 1 + -((count : ℤ) + 1))) = 0 := by
        push_cast; omega
      have highFramed : max (0 : ℤ) (min 1 (((count + 2 : ℕ) : ℤ) * 1 + -((count : ℤ) + 1))) = 1 := by
        push_cast; omega
      rw [low, lowFramed] at first
      rw [high, highFramed] at second
      have contradiction := first.trans second.symm
      omega
    · exact zero
    · exfalso
      obtain ⟨count, hcount⟩ : ∃ count : ℕ,
          potentialSum signedReadings.potential (frame : Multiset Node) = (count : ℤ) + 1 :=
        ⟨(potentialSum signedReadings.potential (frame : Multiset Node) - 1).toNat, by omega⟩
      have first := congruent (Multiset.replicate count .failed)
      have second := congruent (Multiset.replicate (count + 1) .failed)
      rw [framed, clampedCost_eq, signed_replicate] at first second
      change max 0 (min 1 (((count : ℕ) : ℤ) * (-1) + _)) = act (max 0 (min 1 (((count : ℕ) : ℤ) * (-1))))
        at first
      change max 0 (min 1 (((count + 1 : ℕ) : ℤ) * (-1) + _)) =
        act (max 0 (min 1 (((count + 1 : ℕ) : ℤ) * (-1)))) at second
      rw [hcount] at first second
      have low : max (0 : ℤ) (min 1 (((count : ℕ) : ℤ) * (-1))) = 0 := by omega
      have high : max (0 : ℤ) (min 1 (((count + 1 : ℕ) : ℤ) * (-1))) = 0 := by push_cast; omega
      have lowFramed : max (0 : ℤ) (min 1 (((count : ℕ) : ℤ) * (-1) + ((count : ℤ) + 1))) = 1 := by omega
      have highFramed : max (0 : ℤ) (min 1 (((count + 1 : ℕ) : ℤ) * (-1) + ((count : ℤ) + 1))) = 0 := by
        push_cast; omega
      rw [low, lowFramed] at first
      rw [high, highFramed] at second
      have contradiction := first.trans second.symm
      omega
  · intro zero
    refine ⟨id, fun live => ?_⟩
    rw [framed, zero, add_zero]
    rfl

/-- The event cost of the signed potential. -/
def signedCost : Event Node → ℤ
  | .evolve x => signedReadings.potential (grammar.evolve x) - signedReadings.potential x
  | .fork x => signedReadings.potential x
  | .merge x y => signedReadings.potential (grammar.merge x y) - signedReadings.potential x -
      signedReadings.potential y
  | .erase x => -signedReadings.potential x

theorem signedCost_laws : PotentialLaws grammar signedCost signedReadings.potential :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- **The counterexample and the two repairs, side by side**, on the authored
instance with signed potentials.  The clamped cost is not congruent for a
pending task in context.  Repair (a): the retained potential is transported,
with its replay criterion, by every context that preserves the node potential,
the pending task among them.  Repair (b): the clamped cost is transported, with
its replay criterion within budget, by the neutral contexts, and the pending
task is not neutral. -/
theorem repairs_side_by_side :
    (¬ ∃ act : ℤ → ℤ, ∀ live, clampedCost (pendingFrame.apply live) = act (clampedCost live)) ∧
      ContextTransport (G := grammar) (potentialSum signedReadings.potential) id (fun _ => True)
        (PotentialPreserving signedReadings.potential) signedCost ∧
      PotentialPreserving signedReadings.potential pendingFrame ∧
      ContextTransport (G := grammar) (reading scale signedReadings .cost) id (WithinBudget scale signedReadings)
        (Neutral signedReadings.potential) signedCost ∧
      ¬ Neutral signedReadings.potential pendingFrame := by
  refine ⟨clamped_not_congruent.2.2.2, retained_transport signedCost_laws, fun _ => rfl,
    neutral_transport scale signedReadings signedCost_laws, fun neutral => ?_⟩
  have framePotential := neutral.2
  change potentialSum signedReadings.potential (Node.task ::ₘ 0) = 0 at framePotential
  rw [potentialSum_singleton] at framePotential
  exact absurd framePotential (by decide)

end Instance

end Mettapedia.GSLT.Distinction.HistoryContextCost
