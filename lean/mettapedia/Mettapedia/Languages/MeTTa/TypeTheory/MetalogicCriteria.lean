import Mettapedia.TypeTheory.ScopedIdentity
import Mettapedia.Computability.CompassionateTrinityPressure
import Mettapedia.GSLT.Core.ObservationIndexedPruning
import Mettapedia.Languages.MeTTa.TypeTheory.StagedReflective.SuperpositionOccurrencePressure

/-!
# Defeasible criteria for a MeTTa metalogic

These criteria are theorem-level pressures, not axioms and not a production
Prime specification.  Each criterion is paired with a positive witness or a
negative countermodel.  The collection should be revised or removed when
future semantics, implementations, or wellbeing evidence refutes it.

The current evidence supports a narrow commitment:

* exact Boolean checking is required only at a named kernel boundary;
* proof-relevant routes remain available outside scoped proof-irrelevant
  regions;
* a coarse support or result-type view cannot replace route or occurrence
  information when clients observe it;
* exhaustion is not closed absence;
* optimization authority is relative to an explicit observer; and
* structural transport does not erase material presentation identity.

Nothing here chooses global K, global non-K, univalence, a final collection
type, or a complete ethics of artificial minds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.MetalogicCriteria

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.GSLT.Core.OpenTotalityObservation

universe uJudgment

/-! ## Exact checking is a local boundary -/

/-- A proposed executable checker, separated from the proposition it is meant
to decide. -/
structure CheckerCandidate (Judgment : Type uJudgment) where
  check : Judgment -> Bool

/-- Exactness of one checker for one named authorization judgment.  This does
not require every proposition or every identity type to be decidable. -/
def CheckerCandidate.ExactFor {Judgment : Type uJudgment}
    (candidate : CheckerCandidate Judgment)
    (Authorized : Judgment -> Prop) : Prop :=
  forall judgment, candidate.check judgment = true <-> Authorized judgment

namespace CheckerCanary

def Authorized (judgment : Bool) : Prop := judgment = true

def exact : CheckerCandidate Bool where
  check := fun judgment => judgment

def rejectAll : CheckerCandidate Bool where
  check := fun _ => false

theorem exact_is_exact : exact.ExactFor Authorized := by
  intro judgment
  cases judgment <;> simp [exact, Authorized]

/-- Merely terminating is insufficient: a checker which rejects everything
is not exact for a nonempty authorization judgment. -/
theorem rejectAll_not_exact : Not (rejectAll.ExactFor Authorized) := by
  intro alleged
  have trueCase := alleged true
  simp [rejectAll, Authorized] at trueCase

end CheckerCanary

/-! ## Scoped identity and route retention -/

/-- The route-plural layer and its checked proof-irrelevant region coexist in
one concrete model.  Thus scoped UIP does not force global route collapse. -/
theorem route_plurality_and_checked_bubble_compatible :
    HasDistinctRoutes BubbleCanary.layer /\
      ScopedRouteUIP BubbleCanary.layer BubbleCanary.checkedOnly /\
      Not (RouteUIP BubbleCanary.layer) := by
  exact ⟨BubbleCanary.layer_hasDistinctRoutes,
    BubbleCanary.checkedOnly_scopedUIP,
    BubbleCanary.layer_not_routeUIP⟩

/-- The retained conversion label is not recoverable from proposition-valued
support.  A support-level proof may certify convertibility without replacing
the epistemic or operational route. -/
theorem support_cannot_reconstruct_conversion_route :
    Not (exists summarize : ConversionCanary.Support -> Option Bool,
      forall conversion : ConversionCanary.Route,
        summarize conversion.toSupport =
          ConversionCanary.routeLabel conversion) :=
  ConversionCanary.routeLabel_does_not_factor_through_support

namespace RouteObservationCanary

open Mettapedia.TypeTheory.ScopedIdentity.ConversionCanary

abbrev SupportView := PLift Support

abbrev firstRoute : Route :=
  Mettapedia.TypeTheory.JudgmentalEquality.ReceiptCanary.first

abbrev secondRoute : Route :=
  Mettapedia.TypeTheory.JudgmentalEquality.ReceiptCanary.second

/-- The coarse observer retains only proposition-valued convertibility
support and erases which primitive conversion route was used. -/
def supportObserver : Observer Route SupportView where
  observe := fun route => ⟨route.toSupport⟩

/-- A route-sensitive goal which selects one primitive conversion label. -/
def firstLabelProblem : ProblemSpace Route where
  preferredRegion := {route | routeLabel route = some false}

/-- Retaining the conversion route makes its primitive label observable. -/
theorem firstLabel_visible_at_route :
    firstLabelProblem.GoalVisibleAt (Observer.identity Route) := by
  refine ⟨{route | routeLabel route = some false}, ?_⟩
  intro route
  rfl

/-- Proposition-valued support merges two routes on which the selected goal
differs, so this route-sensitive client cannot authorize the erasure. -/
theorem firstLabel_not_visible_at_support :
    Not (firstLabelProblem.GoalVisibleAt supportObserver) := by
  intro visible
  have invariant :=
    (firstLabelProblem.goalVisibleAt_iff_invariantOnFibres
      supportObserver).mp visible
  have sameSupport :
      supportObserver.observe firstRoute =
        supportObserver.observe secondRoute :=
    Subsingleton.elim _ _
  have contradiction := invariant firstRoute secondRoute sameSupport
  simp [firstLabelProblem, firstRoute, secondRoute] at contradiction

end RouteObservationCanary

/-- Explicit structural transport and material inspection are compatible,
rather than competing global identity doctrines. -/
theorem structural_transport_retains_material_distinction :
    ConstructionCanary.booleanFiniteTwoEquivalence.source ≠
        ConstructionCanary.booleanFiniteTwoEquivalence.target /\
      forall value :
          ConstructionCanary.Carrier
            ConstructionCanary.booleanFiniteTwoEquivalence.source,
        ConstructionCanary.booleanFiniteTwoEquivalence.structurallyEquivalent.symm
            (ConstructionCanary.booleanFiniteTwoEquivalence.structurallyEquivalent
              value) = value :=
  ConstructionCanary.transportable_and_inspectable

/-! ## Wellbeing-sensitive observation remains fine enough -/

open Mettapedia.Computability.CompassionateTrinityPressure

/-- Ordered observation can express the finite propagation-shaped signal. -/
theorem valence_signal_visible_at_history :
    adjacencyProblem.GoalVisibleAt
      (Observer.identity (List ValenceObservation)) :=
  adjacency_visible_to_stream

/-- The same signal cannot be reconstructed from the occurrence bag alone. -/
theorem valence_signal_not_recoverable_from_bag :
    Not (adjacencyProblem.GoalVisibleAt bagObserver) :=
  adjacency_not_visible_to_bag

/-- A resource bound ending in silence remains distinct from proved closed
absence. -/
theorem exhausted_silence_is_not_closed_absence :
    Not (Observation.EstablishesClosedAbsence exhaustedSilence) :=
  exhausted_silence_does_not_establish_closed_absence

/-! ## Current superposition typing is too coarse for occurrence clients -/

open Mettapedia.Languages.MeTTa.StagedReflective.SuperpositionOccurrencePressure

/-- The current result-type observer cannot express duplicated occurrence. -/
theorem current_type_is_not_occurrence_adequate :
    Not (duplicationProblem.GoalVisibleAt typeObserver) :=
  duplication_not_visible_to_current_type

/-- A richer occurrence observer demonstrates that the requirement itself is
satisfiable without selecting its final surface representation. -/
theorem occurrence_requirement_is_satisfiable :
    duplicationProblem.GoalVisibleAt occurrenceObserver :=
  duplication_visible_to_occurrence_count

/-! ## Optimization is indexed by observation -/

open Mettapedia.GSLT.Core.ObservationIndexedPruning

/-- Duplicate removal is valid at the extensional set readout. -/
theorem duplicate_pruning_has_a_lawful_scope :
    LawfulAt Canary.setObserver Canary.removeDuplicate.toChange :=
  Canary.duplicate_prune_lawful_at_set

/-- The same transformation is invalid at the occurrence-bag readout. -/
theorem duplicate_pruning_has_a_forbidden_scope :
    Not (LawfulAt Canary.bagObserver Canary.removeDuplicate.toChange) :=
  Canary.duplicate_prune_not_lawful_at_bag

/-- A sound occurrence-bag guard therefore cannot silently acquire the
coarser set observer's pruning authority. -/
theorem bag_guard_cannot_inherit_set_pruning
    (guard : Guard Canary.bagObserver Unit) :
    Not (guard.accepts Canary.removeDuplicate.toChange) :=
  Canary.every_sound_bag_guard_rejects_duplicate guard

/-! ## Joint nondegenerate witness -/

/-- The presently selected pressures are jointly witnessed by the concrete
positive and negative models above.  This is a compatibility theorem for the
criteria, not a construction of the final MeTTa metalogic. -/
theorem criteria_jointly_witnessed :
    CheckerCanary.exact.ExactFor CheckerCanary.Authorized /\
      HasDistinctRoutes BubbleCanary.layer /\
      ScopedRouteUIP BubbleCanary.layer BubbleCanary.checkedOnly /\
      Not (RouteUIP BubbleCanary.layer) /\
      Not (RouteObservationCanary.firstLabelProblem.GoalVisibleAt
        RouteObservationCanary.supportObserver) /\
      Not (adjacencyProblem.GoalVisibleAt bagObserver) /\
      Not (Observation.EstablishesClosedAbsence exhaustedSilence) /\
      Not (duplicationProblem.GoalVisibleAt typeObserver) /\
      duplicationProblem.GoalVisibleAt occurrenceObserver /\
      LawfulAt Canary.setObserver Canary.removeDuplicate.toChange /\
      Not (LawfulAt Canary.bagObserver Canary.removeDuplicate.toChange) := by
  exact ⟨CheckerCanary.exact_is_exact,
    BubbleCanary.layer_hasDistinctRoutes,
    BubbleCanary.checkedOnly_scopedUIP,
    BubbleCanary.layer_not_routeUIP,
    RouteObservationCanary.firstLabel_not_visible_at_support,
    valence_signal_not_recoverable_from_bag,
    exhausted_silence_is_not_closed_absence,
    current_type_is_not_occurrence_adequate,
    occurrence_requirement_is_satisfiable,
    duplicate_pruning_has_a_lawful_scope,
    duplicate_pruning_has_a_forbidden_scope⟩

/-! ## Axiom audit -/

#print axioms CheckerCanary.exact_is_exact
#print axioms CheckerCanary.rejectAll_not_exact
#print axioms route_plurality_and_checked_bubble_compatible
#print axioms support_cannot_reconstruct_conversion_route
#print axioms RouteObservationCanary.firstLabel_visible_at_route
#print axioms RouteObservationCanary.firstLabel_not_visible_at_support
#print axioms structural_transport_retains_material_distinction
#print axioms valence_signal_not_recoverable_from_bag
#print axioms exhausted_silence_is_not_closed_absence
#print axioms current_type_is_not_occurrence_adequate
#print axioms bag_guard_cannot_inherit_set_pruning
#print axioms criteria_jointly_witnessed

end Mettapedia.Languages.MeTTa.TypeTheory.MetalogicCriteria
