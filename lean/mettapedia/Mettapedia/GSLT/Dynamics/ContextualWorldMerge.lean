import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

/-!
# Occurrence-preserving contextual world merge

Alternative worlds may share physical storage without becoming jointly true.
This module retains two layers:

* a list of contextual occurrences preserves multiplicity and authored
  occurrence identity;
* `worldsFor` summarizes the worlds in which a fact is available.

The support projection forgets duplicate occurrences and the bag projection
forgets world conditions.  Both are useful views, but neither is the source of
truth.  The negative control shows why: naked support contains both `heads`
and `tails`, while their contextual intersection is empty.
-/

namespace Mettapedia.GSLT.Dynamics.ContextualWorldMerge

set_option autoImplicit false

universe uFact uWorld uState uAnswer uIntent

/-- One fact occurrence together with the finite set of worlds supporting it. -/
structure ContextualOccurrence (Fact : Type uFact) (World : Type uWorld) where
  fact : Fact
  worlds : Finset World

/-- The information-preserving carrier retains every occurrence. -/
abbrev Carrier (Fact : Type uFact) (World : Type uWorld) :=
  List (ContextualOccurrence Fact World)

/-- Alternative branch families compose by occurrence-preserving append. -/
def merge {Fact : Type uFact} {World : Type uWorld}
    (left right : Carrier Fact World) : Carrier Fact World :=
  left ++ right

/-- Worlds supporting a structural fact.  Repeated occurrences contribute by
union while remaining distinct in the underlying carrier. -/
def worldsFor {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] [DecidableEq World]
    (fact : Fact) : Carrier Fact World -> Finset World
  | [] => {}
  | occurrence :: rest =>
      if occurrence.fact = fact then
        occurrence.worlds ∪ worldsFor fact rest
      else
        worldsFor fact rest

/-- The occurrence-bag view forgets branch conditions but retains duplicate
fact occurrences. -/
def bagProjection {Fact : Type uFact} {World : Type uWorld}
    (occurrences : Carrier Fact World) : Multiset Fact :=
  occurrences.map ContextualOccurrence.fact

/-- The set view forgets both branch conditions and duplicate occurrences. -/
def supportProjection {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] (occurrences : Carrier Fact World) : Finset Fact :=
  (occurrences.map ContextualOccurrence.fact).toFinset

/-- A fact is possible when at least one retained world supports it. -/
def Possible {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] [DecidableEq World]
    (occurrences : Carrier Fact World) (fact : Fact) : Prop :=
  (worldsFor fact occurrences).Nonempty

/-- Two facts are jointly possible precisely when some one retained world
supports both. -/
def JointlyPossible {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] [DecidableEq World]
    (occurrences : Carrier Fact World)
    (left right : Fact) : Prop :=
  (worldsFor left occurrences ∩ worldsFor right occurrences).Nonempty

@[simp] theorem worldsFor_nil {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] [DecidableEq World] (fact : Fact) :
    worldsFor fact ([] : Carrier Fact World) = {} :=
  rfl

@[simp] theorem worldsFor_cons_same {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] [DecidableEq World]
    (fact : Fact) (worlds : Finset World)
    (rest : Carrier Fact World) :
    worldsFor fact ({ fact := fact, worlds := worlds } :: rest) =
      worlds ∪ worldsFor fact rest := by
  simp [worldsFor]

@[simp] theorem worldsFor_cons_other {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] [DecidableEq World]
    {other fact : Fact} (different : other ≠ fact)
    (worlds : Finset World) (rest : Carrier Fact World) :
    worldsFor fact ({ fact := other, worlds := worlds } :: rest) =
      worldsFor fact rest := by
  simp [worldsFor, different]

/-- Context summary is a homomorphism from occurrence merge to world union. -/
theorem worldsFor_merge {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] [DecidableEq World] (fact : Fact)
    (left right : Carrier Fact World) :
    worldsFor fact (merge left right) =
      worldsFor fact left ∪ worldsFor fact right := by
  induction left with
  | nil => simp [merge]
  | cons occurrence rest inductionHypothesis =>
      unfold merge at inductionHypothesis ⊢
      by_cases same : occurrence.fact = fact
      · simp only [List.cons_append, worldsFor, same, if_pos]
        rw [inductionHypothesis]
        exact (Finset.union_assoc _ _ _).symm
      · simp only [List.cons_append, worldsFor, same]
        exact inductionHypothesis

/-- The bag projection is likewise a merge homomorphism, but to multiset
addition rather than idempotent union. -/
theorem bagProjection_merge {Fact : Type uFact} {World : Type uWorld}
    (left right : Carrier Fact World) :
    bagProjection (merge left right) =
      bagProjection left + bagProjection right := by
  simp [bagProjection, merge]

/-- The set projection is the coarser idempotent merge homomorphism. -/
theorem supportProjection_merge {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] (left right : Carrier Fact World) :
    supportProjection (merge left right) =
      supportProjection left ∪ supportProjection right := by
  simp [supportProjection, merge]

/-- Joint possibility is symmetric. -/
theorem jointlyPossible_comm {Fact : Type uFact} {World : Type uWorld}
    [DecidableEq Fact] [DecidableEq World]
    (occurrences : Carrier Fact World)
    (left right : Fact) :
    JointlyPossible occurrences left right <->
      JointlyPossible occurrences right left := by
  simp [JointlyPossible, Finset.inter_comm]

/-! ## Bridge from isolated execution worlds -/

/-- Give each isolated result occurrence its singleton branch context. -/
def ofWorldResults {State : Type uState} {Answer : Type uAnswer}
    {Intent : Type uIntent} {Fact : Type uFact}
    (toFact : Answer -> Fact)
    (results : List
      (ContextualEffectHandlers.WorldResult State Answer Intent)) :
    Carrier Fact ContextualEffectHandlers.BranchTrace :=
  results.map fun result =>
    { fact := toFact result.answer, worlds := {result.branch} }

/-- Contextualization neither creates nor drops occurrences. -/
@[simp] theorem length_ofWorldResults {State : Type uState}
    {Answer : Type uAnswer} {Intent : Type uIntent} {Fact : Type uFact}
    (toFact : Answer -> Fact)
    (results : List
      (ContextualEffectHandlers.WorldResult State Answer Intent)) :
    (ofWorldResults toFact results).length = results.length := by
  simp [ofWorldResults]

/-- Forgetting contexts after contextualization returns the exact answer bag
mapped through the requested fact view. -/
theorem bagProjection_ofWorldResults {State : Type uState}
    {Answer : Type uAnswer} {Intent : Type uIntent} {Fact : Type uFact}
    (toFact : Answer -> Fact)
    (results : List
      (ContextualEffectHandlers.WorldResult State Answer Intent)) :
    bagProjection (ofWorldResults toFact results) =
      (results.map (fun result => toFact result.answer) : Multiset Fact) := by
  have listEquality :
      (ofWorldResults toFact results).map ContextualOccurrence.fact =
        results.map (fun result => toFact result.answer) := by
    simp [ofWorldResults, List.map_map, Function.comp_def]
  exact congrArg (fun facts : List Fact => (facts : Multiset Fact)) listEquality

/-! ## Positive and negative controls -/

namespace Canary

inductive Fact where
  | heads
  | tails
  | wet
deriving DecidableEq, Repr

/-- `false` and `true` are two mutually exclusive retained worlds. -/
def occurrences : Carrier Fact Bool :=
  [{ fact := .heads, worlds := {false} },
   { fact := .tails, worlds := {true} },
   { fact := .wet, worlds := {false} },
   { fact := .wet, worlds := {true} }]

/-- One structural fact may be supported by both alternatives. -/
theorem wet_has_both_worlds :
    worldsFor .wet occurrences = {false, true} := by
  ext world
  cases world <;> simp [worldsFor, occurrences]

/-- The occurrence view remembers the two independent derivations of `wet`. -/
theorem wet_has_two_occurrences :
    (bagProjection occurrences).count .wet = 2 := by
  decide

/-- The set projection contains both exclusive facts and therefore cannot by
itself answer whether they may be used together. -/
theorem naked_support_forgets_exclusivity :
    .heads ∈ supportProjection occurrences /\
      .tails ∈ supportProjection occurrences := by
  decide

/-- Context intersection rejects the impossible cross-world conjunction. -/
theorem heads_and_tails_not_jointly_possible :
    Not (JointlyPossible occurrences .heads .tails) := by
  simp [JointlyPossible, worldsFor, occurrences]

/-- A fact supported in both worlds composes with either branch-local fact. -/
theorem wet_is_compatible_with_each_alternative :
    JointlyPossible occurrences .wet .heads /\
      JointlyPossible occurrences .wet .tails := by
  simp [JointlyPossible, worldsFor, occurrences]

/-- Deduplication is a genuine quotient: support has three structural facts
while the information-preserving carrier has four occurrences. -/
theorem support_is_strictly_coarser :
    (supportProjection occurrences).card = 3 /\ occurrences.length = 4 := by
  decide

end Canary

/-! ## Axiom audit -/

#print axioms worldsFor_merge
#print axioms bagProjection_merge
#print axioms supportProjection_merge
#print axioms Canary.heads_and_tails_not_jointly_possible
#print axioms Canary.support_is_strictly_coarser

end Mettapedia.GSLT.Dynamics.ContextualWorldMerge
