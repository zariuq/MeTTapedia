import Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
import Mathlib.Data.List.FinRange

/-!
# Finite occurrence families in the Prime interaction fibration

The pairwise separation certificate extends to a finite, nonempty list of
exact Cost-rho event occurrences.  One retained frame exhibits a common source
decomposition for the entire list.  Event identity is positional: two equal
event values at different indices remain two occurrences.

The certificate compiles into the existing `ParallelCostSchedule`; it does
not introduce a second scheduler hierarchy.  Every permutation of the listed
occurrences serializes to the same target, while the licensed concurrent
schedule places the whole family in one wave.  Failure to construct this
certificate merely withholds that one-wave license and says nothing about the
existence of a chronological schedule.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration

open Mettapedia.Algebra
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- A nonempty finite family with one exact occurrence/resource decomposition
in a common source. -/
structure FamilySeparation (Ground : Type u)
    (events : List (CostedEvent Ground)) (source : CostConfig Ground) :
    Type u where
  frame : CostConfig Ground
  source_eq : source = costWaveSource events frame
  nonempty : events ≠ []

namespace FamilySeparation

variable {Ground : Type u} {events : List (CostedEvent Ground)}
variable {source : CostConfig Ground}

/-- Positional identities of all licensed event occurrences. -/
def occurrenceIndices
    (_separation : FamilySeparation Ground events source) :
    List (Fin events.length) :=
  List.finRange events.length

/-- Every licensed occurrence index appears exactly once.  This remains true
when distinct indices carry structurally equal events. -/
theorem occurrence_index_count_eq_one
    (separation : FamilySeparation Ground events source)
    (index : Fin events.length) :
    separation.occurrenceIndices.count index = 1 := by
  exact List.count_finRange index

/-- The matching already used by the Cost-rho execution semantics. -/
def toMatching (separation : FamilySeparation Ground events source) :
    CostMatching Ground where
  source := source
  events := events
  frame := separation.frame
  source_eq := separation.source_eq

def target (separation : FamilySeparation Ground events source) :
    CostConfig Ground :=
  separation.toMatching.target

def receipt (separation : FamilySeparation Ground events source) :
    Multiset (SpendEvent Ground (CostName Ground)) :=
  separation.toMatching.receipt

@[simp] theorem receipt_card
    (separation : FamilySeparation Ground events source) :
    separation.receipt.card = events.length := by
  simp [receipt, toMatching, CostMatching.receipt, costWaveReceipt]

/-- The common decomposition is an authorized nonempty concurrent step. -/
theorem parallelStep (separation : FamilySeparation Ground events source) :
    ParallelCostStep source separation.receipt separation.target := by
  exact ⟨separation.toMatching, rfl, separation.nonempty, rfl, rfl⟩

/-- Compile the whole separated family as one wave in the existing scheduler
artifact. -/
def schedule (separation : FamilySeparation Ground events source) :
    ParallelCostSchedule source separation.receipt separation.target
      events.length 1 := by
  simpa [receipt, target, toMatching, CostMatching.receipt,
    CostMatching.target, costWaveReceipt] using
    (ParallelCostSchedule.cons separation.parallelStep
      (ParallelCostSchedule.nil separation.target))

/-- Erasure is an ordinary authorized parallel trace with the same exact
source, receipt, target, and occurrence count. -/
theorem schedule_erases
    (separation : FamilySeparation Ground events source) :
    ParallelCostTrace source separation.receipt separation.target
      events.length :=
  separation.schedule.toTrace

/-- Every permutation of the exact occurrence list is a chronological path
from the same source to the same target. -/
theorem permutation_reaches_common_target
    (separation : FamilySeparation Ground events source)
    {schedule : List (CostedEvent Ground)}
    (permutation : schedule.Perm events) :
    CostTrace source (costWaveTrace schedule) separation.target :=
  separation.toMatching.permutation_serializes permutation

/-- Any two occurrence permutations commute in the semantic sense required by
the scheduler: both are authorized chronological paths from the exact common
source to the exact common target.  Event identities are retained in the two
trace labels rather than quotienting the paths themselves. -/
theorem permutations_commute
    (separation : FamilySeparation Ground events source)
    {leftSchedule rightSchedule : List (CostedEvent Ground)}
    (leftPermutation : leftSchedule.Perm events)
    (rightPermutation : rightSchedule.Perm events) :
    CostTrace source (costWaveTrace leftSchedule) separation.target ∧
      CostTrace source (costWaveTrace rightSchedule) separation.target :=
  ⟨separation.permutation_reaches_common_target leftPermutation,
    separation.permutation_reaches_common_target rightPermutation⟩

/-- Work is exactly the number of listed occurrences. -/
theorem schedule_work_eq_length
    (separation : FamilySeparation Ground events source) :
    separation.schedule.workSpan.work = events.length :=
  separation.schedule.workSpan_work_eq_count

/-- A nonempty fully separated family has span one. -/
theorem schedule_span_eq_one
    (separation : FamilySeparation Ground events source) :
    separation.schedule.workSpan.span = 1 :=
  separation.schedule.workSpan_span_eq_waves

theorem schedule_workSpan
    (separation : FamilySeparation Ground events source) :
    separation.schedule.workSpan = ⟨events.length, 1⟩ := by
  apply WorkSpan.ext
  · exact separation.schedule_work_eq_length
  · exact separation.schedule_span_eq_one

/-- A two-element family specializes to the established pair certificate. -/
def toPair {left right : CostedEvent Ground}
    (separation : FamilySeparation Ground [left, right] source) :
    CostEffectSeparation Ground source left right :=
  ⟨separation.frame, separation.source_eq⟩

end FamilySeparation

/-! ## Scheduler-policy colour classes -/

/-- A valid colouring is a chronological list of nonempty colour classes.
Each class carries the exact family-separation evidence needed at the state
where that wave runs.  This is policy input compiled into
`ParallelCostSchedule`, not a second execution semantics. -/
inductive ValidWaveColoring (Ground : Type u) :
    CostConfig Ground → List (List (CostedEvent Ground)) →
      CostConfig Ground → Type u where
  | nil (config : CostConfig Ground) :
      ValidWaveColoring Ground config [] config
  | cons {source target : CostConfig Ground}
      {wave : List (CostedEvent Ground)}
      {waves : List (List (CostedEvent Ground))}
      (head : FamilySeparation Ground wave source)
      (tail : ValidWaveColoring Ground head.target waves target) :
      ValidWaveColoring Ground source (wave :: waves) target

namespace ValidWaveColoring

variable {Ground : Type u} {source target : CostConfig Ground}
variable {waves : List (List (CostedEvent Ground))}

def receipt :
    ∀ {source target : CostConfig Ground}
      {waves : List (List (CostedEvent Ground))},
      ValidWaveColoring Ground source waves target →
        Multiset (SpendEvent Ground (CostName Ground))
  | _, _, _, .nil _ => 0
  | _, _, _, .cons head tail => head.receipt + receipt tail

/-- Compile any operationally valid colouring into the established scheduler
schedule.  No optimality of the colouring is assumed. -/
def toSchedule :
    ∀ {source target : CostConfig Ground}
      {waves : List (List (CostedEvent Ground))}
      (coloring : ValidWaveColoring Ground source waves target),
      ParallelCostSchedule source coloring.receipt target
        waves.flatten.length waves.length
  | _, _, _, .nil config => by
      simpa [receipt] using ParallelCostSchedule.nil config
  | _, _, _, .cons head tail => by
      simpa [receipt, List.flatten, head.receipt_card, Nat.add_comm] using
        (ParallelCostSchedule.cons head.parallelStep (toSchedule tail))

/-- Any valid colouring yields an authorized ordinary trace. -/
def toTrace (coloring : ValidWaveColoring Ground source waves target) :
    ParallelCostTrace source coloring.receipt target waves.flatten.length :=
  coloring.toSchedule.toTrace

theorem work_eq_occurrence_count
    (coloring : ValidWaveColoring Ground source waves target) :
    coloring.toSchedule.workSpan.work = waves.flatten.length :=
  coloring.toSchedule.workSpan_work_eq_count

theorem span_eq_colour_count
    (coloring : ValidWaveColoring Ground source waves target) :
    coloring.toSchedule.workSpan.span = waves.length :=
  coloring.toSchedule.workSpan_span_eq_waves

/-- Span is monotone under any certified policy refinement that does not add
colour classes.  This promises no minimum-colouring result. -/
theorem span_mono_of_colour_count_le
    (strong : ValidWaveColoring Ground source strongWaves strongTarget)
    (weak : ValidWaveColoring Ground weakSource weakWaves weakTarget)
    (noMoreColours : strongWaves.length ≤ weakWaves.length) :
    strong.toSchedule.workSpan.span ≤ weak.toSchedule.workSpan.span := by
  simpa [strong.span_eq_colour_count, weak.span_eq_colour_count] using
    noMoreColours

end ValidWaveColoring

/-! ## Occurrence-indexed conflict graphs -/

/-- A conflict graph is indexed by event *occurrences*, not event values.
Equal event values at different positions therefore remain distinct vertices. -/
structure OccurrenceConflictGraph (n : Nat) where
  conflict : Fin n → Fin n → Prop
  symmetric : ∀ {left right}, conflict left right → conflict right left
  irreflexive : ∀ occurrence, ¬ conflict occurrence occurrence

namespace OccurrenceConflictGraph

/-- No two vertices placed in one colour class are connected by the graph. -/
def ConflictFree (graph : OccurrenceConflictGraph n)
    (wave : List (Fin n)) : Prop :=
  ∀ left ∈ wave, ∀ right ∈ wave, ¬ graph.conflict left right

/-- `stronger` licenses at least the separations licensed by `weaker`: every
conflict retained by the stronger analysis was already a conflict before.
Equivalently, strengthening separation may remove conflict edges, never add
them. -/
def SeparationRefines (stronger weaker : OccurrenceConflictGraph n) : Prop :=
  ∀ left right, stronger.conflict left right → weaker.conflict left right

theorem conflictFree_of_separationRefines
    {stronger weaker : OccurrenceConflictGraph n}
    (refines : stronger.SeparationRefines weaker)
    {wave : List (Fin n)} (free : weaker.ConflictFree wave) :
    stronger.ConflictFree wave := by
  intro left leftMem right rightMem conflict
  exact free left leftMem right rightMem (refines left right conflict)

end OccurrenceConflictGraph

/-- Recover the event values named by positional colour classes. -/
def eventWaves (events : List (CostedEvent Ground))
    (indexWaves : List (List (Fin events.length))) :
    List (List (CostedEvent Ground)) :=
  indexWaves.map fun wave => wave.map events.get

@[simp] theorem eventWaves_length
    (events : List (CostedEvent Ground))
    (indexWaves : List (List (Fin events.length))) :
    (eventWaves events indexWaves).length = indexWaves.length := by
  simp [eventWaves]

@[simp] theorem eventWaves_flatten_length
    (events : List (CostedEvent Ground))
    (indexWaves : List (List (Fin events.length))) :
    (eventWaves events indexWaves).flatten.length =
      indexWaves.flatten.length := by
  simp [eventWaves, Function.comp_def]

/-- A graph colouring becomes an execution certificate only when:

* its index classes partition the exact occurrence indices;
* every class is graph-conflict-free; and
* every class carries the operational `FamilySeparation` evidence required
  at its chronological source.

The last field is essential: pairwise graph compatibility alone cannot prove
that a whole class fits a resource configuration with finite multiplicities. -/
structure ValidConflictColoring (Ground : Type u)
    (events : List (CostedEvent Ground))
    (source target : CostConfig Ground) : Type u where
  graph : OccurrenceConflictGraph events.length
  indexWaves : List (List (Fin events.length))
  covers : indexWaves.flatten.Perm (List.finRange events.length)
  conflictFree : ∀ wave ∈ indexWaves, graph.ConflictFree wave
  operational :
    ValidWaveColoring Ground source (eventWaves events indexWaves) target

namespace ValidConflictColoring

variable {Ground : Type u} {events : List (CostedEvent Ground)}
variable {source target : CostConfig Ground}

/-- Every exact event-occurrence vertex appears in precisely one colour
class, even when two vertices contain equal event values. -/
theorem occurrence_index_count_eq_one
    (coloring : ValidConflictColoring Ground events source target)
    (index : Fin events.length) :
    coloring.indexWaves.flatten.count index = 1 := by
  simpa using coloring.covers.count index

/-- The graph layer compiles to the same established schedule artifact as a
direct operational colouring. -/
def toSchedule
    (coloring : ValidConflictColoring Ground events source target) :=
  coloring.operational.toSchedule

/-- Every valid conflict colouring yields an authorized Cost-rho trace. -/
def toTrace
    (coloring : ValidConflictColoring Ground events source target) :=
  coloring.operational.toTrace

/-- Work counts original occurrences, independently of how they are
partitioned into colour classes. -/
theorem work_eq_event_count
    (coloring : ValidConflictColoring Ground events source target) :
    coloring.toSchedule.workSpan.work = events.length := by
  calc
    coloring.toSchedule.workSpan.work =
        (eventWaves events coloring.indexWaves).flatten.length :=
      coloring.operational.work_eq_occurrence_count
    _ = coloring.indexWaves.flatten.length :=
      eventWaves_flatten_length events coloring.indexWaves
    _ = (List.finRange events.length).length := coloring.covers.length_eq
    _ = events.length := by simp

/-- Span is the number of supplied colour classes.  No minimum-colouring
claim is made. -/
theorem span_eq_colour_count
    (coloring : ValidConflictColoring Ground events source target) :
    coloring.toSchedule.workSpan.span = coloring.indexWaves.length := by
  calc
    coloring.toSchedule.workSpan.span =
        (eventWaves events coloring.indexWaves).length :=
      coloring.operational.span_eq_colour_count
    _ = coloring.indexWaves.length :=
      eventWaves_length events coloring.indexWaves

/-- Any two certified policies compare monotonically whenever the stronger
separation analysis produces no more colour classes.  This is deliberately
not an optimal-colouring theorem. -/
theorem span_mono_of_no_more_colours
    (strong : ValidConflictColoring Ground strongEvents strongSource
      strongTarget)
    (weak : ValidConflictColoring Ground weakEvents weakSource weakTarget)
    (noMoreColours : strong.indexWaves.length ≤ weak.indexWaves.length) :
    strong.toSchedule.workSpan.span ≤ weak.toSchedule.workSpan.span := by
  rw [strong.span_eq_colour_count, weak.span_eq_colour_count]
  exact noMoreColours

/-- Strengthening the separation analysis preserves every previously valid
colouring, with exactly the same operational schedule and span.  A policy may
then choose a coarser colouring, but no minimum-colouring claim is needed. -/
def ofSeparationRefines
    (coloring : ValidConflictColoring Ground events source target)
    (stronger : OccurrenceConflictGraph events.length)
    (refines : stronger.SeparationRefines coloring.graph) :
    ValidConflictColoring Ground events source target where
  graph := stronger
  indexWaves := coloring.indexWaves
  covers := coloring.covers
  conflictFree := by
    intro wave membership
    exact OccurrenceConflictGraph.conflictFree_of_separationRefines refines
      (coloring.conflictFree wave membership)
  operational := coloring.operational

theorem span_ofSeparationRefines
    (coloring : ValidConflictColoring Ground events source target)
    (stronger : OccurrenceConflictGraph events.length)
    (refines : stronger.SeparationRefines coloring.graph) :
    (coloring.ofSeparationRefines stronger refines).toSchedule.workSpan.span =
      coloring.toSchedule.workSpan.span := by
  rw [(coloring.ofSeparationRefines stronger refines).span_eq_colour_count,
    coloring.span_eq_colour_count]
  rfl

end ValidConflictColoring

/-! ## Three-occurrence control, including equal event values -/

namespace Examples

open NativeInteractionFibration.Examples

def repeatedSource : CostConfig Ground :=
  costWaveSource [leftEvent, rightEvent, leftEvent] 0

/-- The first and third values are equal but remain distinct funded
occurrences in the common decomposition. -/
def repeatedFamily :
    FamilySeparation Ground [leftEvent, rightEvent, leftEvent] repeatedSource :=
  ⟨0, rfl, by simp⟩

theorem repeated_family_occurrence_two_once :
    repeatedFamily.occurrenceIndices.count (2 : Fin 3) = 1 :=
  repeatedFamily.occurrence_index_count_eq_one 2

theorem repeated_family_workSpan :
    repeatedFamily.schedule.workSpan = ⟨3, 1⟩ :=
  repeatedFamily.schedule_workSpan

/-- The same two occurrences may also be scheduled as two singleton colour
classes. -/
def leftSingleton : FamilySeparation Ground [leftEvent] source where
  frame := rightEvent.consumed
  source_eq := by
    simp [source, costWaveSource]
  nonempty := by simp

def rightAfterLeft :
    FamilySeparation Ground [rightEvent] leftSingleton.target where
  frame := leftEvent.produced
  source_eq := by
    simp [FamilySeparation.target, FamilySeparation.toMatching,
      CostMatching.target, costWaveTarget, costWaveSource, leftSingleton]
    ac_rfl
  nonempty := by simp

def twoColouring :
    ValidWaveColoring Ground source [[leftEvent], [rightEvent]]
      rightAfterLeft.target :=
  .cons leftSingleton
    (.cons rightAfterLeft (.nil rightAfterLeft.target))

def oneColourFamily :
    FamilySeparation Ground [leftEvent, rightEvent] source :=
  ⟨sameChannelSeparation.frame, sameChannelSeparation.source_eq, by simp⟩

theorem two_colouring_workSpan :
    twoColouring.toSchedule.workSpan = ⟨2, 2⟩ := by
  apply WorkSpan.ext
  · exact twoColouring.work_eq_occurrence_count
  · exact twoColouring.span_eq_colour_count

/-- More certified separation permits merging the same occurrences into one
wave, strictly reducing span while preserving work.  This is a comparison of
two valid policies, not a claim that either colouring is minimal. -/
theorem one_colour_strictly_improves_span :
    oneColourFamily.schedule.workSpan.work =
        twoColouring.toSchedule.workSpan.work ∧
      oneColourFamily.schedule.workSpan.span <
        twoColouring.toSchedule.workSpan.span := by
  rw [oneColourFamily.schedule_workSpan, two_colouring_workSpan]
  decide

/-! A conservative graph may separate occurrences that the richer operational
analysis can in fact run together.  This is permitted: valid colourings owe
soundness, not optimality. -/

def pairConflictGraph : OccurrenceConflictGraph 2 where
  conflict := (· ≠ ·)
  symmetric := fun conflict => conflict.symm
  irreflexive := fun _ contradiction => contradiction rfl

theorem pairConflictGraph_singleton_free (index : Fin 2) :
    pairConflictGraph.ConflictFree [index] := by
  intro left leftMem right rightMem conflict
  simp only [List.mem_singleton] at leftMem rightMem
  subst left
  subst right
  exact conflict rfl

def pairConflictColoring :
    ValidConflictColoring Ground [leftEvent, rightEvent] source
      rightAfterLeft.target where
  graph := pairConflictGraph
  indexWaves := [[0], [1]]
  covers := by decide
  conflictFree := by
    intro wave membership
    simp only [List.mem_cons] at membership
    rcases membership with rfl | membership
    · exact pairConflictGraph_singleton_free 0
    · rcases membership with rfl | impossible
      · exact pairConflictGraph_singleton_free 1
      · cases impossible
  operational := by
    simpa [eventWaves] using twoColouring

theorem pair_conflict_colouring_workSpan :
    pairConflictColoring.toSchedule.workSpan = ⟨2, 2⟩ := by
  apply WorkSpan.ext
  · exact pairConflictColoring.work_eq_event_count
  · exact pairConflictColoring.span_eq_colour_count

/-- The graph-positive control: putting the conflicting occurrences in one
class does not satisfy the graph side of the certificate. -/
theorem pairConflictGraph_rejects_one_colour :
    ¬ pairConflictGraph.ConflictFree [(0 : Fin 2), 1] := by
  intro conflictFree
  apply conflictFree 0 (by simp) 1 (by simp)
  show (0 : Fin 2) ≠ 1
  decide

theorem repeated_family_nontrivial_permutation_reaches_same_target :
    CostTrace repeatedSource
      (costWaveTrace [leftEvent, leftEvent, rightEvent])
      repeatedFamily.target := by
  exact repeatedFamily.permutation_reaches_common_target
    (List.Perm.cons leftEvent (List.Perm.swap rightEvent leftEvent []))

/-- The contested single-purse source has no two-occurrence family license.
No conclusion about a chronological execution is derived. -/
theorem contested_has_no_family_separation :
    FamilySeparation Ground [leftEvent, leftCompetitor] contestedSource →
      False := by
  intro separation
  exact contested_has_no_parallel_separation separation.toPair

end Examples

#print axioms FamilySeparation.occurrence_index_count_eq_one
#print axioms FamilySeparation.schedule_erases
#print axioms FamilySeparation.permutation_reaches_common_target
#print axioms FamilySeparation.permutations_commute
#print axioms FamilySeparation.schedule_workSpan
#print axioms Examples.repeated_family_workSpan
#print axioms Examples.two_colouring_workSpan
#print axioms Examples.one_colour_strictly_improves_span
#print axioms ValidConflictColoring.work_eq_event_count
#print axioms ValidConflictColoring.span_eq_colour_count
#print axioms ValidConflictColoring.span_ofSeparationRefines
#print axioms Examples.pair_conflict_colouring_workSpan
#print axioms Examples.pairConflictGraph_rejects_one_colour
#print axioms Examples.contested_has_no_family_separation

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
