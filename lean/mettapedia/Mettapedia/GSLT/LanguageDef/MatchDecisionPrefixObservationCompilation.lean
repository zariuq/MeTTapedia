import Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
import Mettapedia.GSLT.LanguageDef.MatchDecisionContract

/-!
# Prefix-sharing compilation for match-decision observations

A match decision may demand several coordinates of one dynamic query.  Walking
every coordinate independently repeats their common prefixes.  This module
separates the semantic and cost claims of compiling those coordinates into a
parent-linked observation trie.

`PrefixEntry` is the generated physical invariant: a root entry contains the
query root and a child entry applies exactly one authored child observation to
its parent.  Its value is proved equal to an independent direct path fold.
Consequently any consumer of the complete observation vector sees exactly the
same value, including candidate order and multiplicity.

The observation vector may be demanded lazily.  Selecting entries by index
preserves both request order and repeated requests, while unrequested entries
need not be evaluated.  This matters when selector coordinates are always
observed but repeated-variable equality coordinates are observed only for
surviving candidates.

The unit-edge cost theorem is deliberately representation-specific.  The
compiled trie stores the union of nonempty demanded prefixes and therefore
never stores more prefix edges than independent walks inspect.  It is minimal
among prefix-edge representations that cover those demands.  Sharing can make
the bound strict, while disjoint one-edge paths provide a negative canary where
it is an equality.  Constant metadata cost remains explicit in `selectedCost`;
the cost-aware selector declines the trie whenever that cost erases the saving.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MatchDecisionPrefixObservationCompilation

universe uState uObservation uResult

abbrev Path := List Nat

/-- Independent direct observation of one query coordinate.  The state may
encode present, absent, or unknown; the theorem does not collapse those cases. -/
def observe {State : Type uState}
    (step : State → Nat → State) (root : State) (path : Path) : State :=
  path.foldl step root

/-- A generated trie entry is obtained only from the query root or by one
child step from an already generated parent entry. -/
inductive PrefixEntry (State : Type uState)
    (root : State) (step : State → Nat → State) where
  | root
  | child (parent : PrefixEntry State root step) (edge : Nat)

namespace PrefixEntry

variable {State : Type uState} {root : State}
  {step : State → Nat → State}

/-- The authored coordinate denoted by a generated entry. -/
def path : PrefixEntry State root step → Path
  | .root => []
  | .child parent edge => path parent ++ [edge]

/-- Evaluate the parent-linked representation, one edge at a time. -/
def value : PrefixEntry State root step → State
  | .root => root
  | .child parent edge => step (value parent) edge

theorem observe_snoc (pathPrefix : Path) (edge : Nat) :
    observe step root (pathPrefix ++ [edge]) =
      step (observe step root pathPrefix) edge := by
  simp [observe, List.foldl_append]

/-- A query-observation state is absorbing when every deeper child request
returns that same state.  Match decisions use this for unknown coordinates
below a query variable and absent coordinates below a missing child. -/
def IsAbsorbing (state : State) : Prop :=
  ∀ edge, step state edge = state

/-- Once an observation reaches an absorbing state, no suffix edge can add
information.  A physical observer may therefore skip the complete suffix. -/
theorem observe_eq_of_absorbing (state : State) (path : Path)
    (absorbing : IsAbsorbing (step := step) state) :
    observe step state path = state := by
  induction path with
  | nil => rfl
  | cons edge rest inductionHypothesis =>
      simp only [observe, List.foldl_cons]
      rw [absorbing edge]
      exact inductionHypothesis

/-- The suffix-skipping form used by a prefix cache: after the independently
observed prefix becomes absorbing, walking or omitting the remaining authored
coordinate has exactly the same result. -/
theorem observe_append_eq_of_absorbing
    (pathPrefix pathSuffix : Path)
    (absorbing : IsAbsorbing (step := step)
      (observe step root pathPrefix)) :
    observe step root (pathPrefix ++ pathSuffix) =
      observe step root pathPrefix := by
  calc
    observe step root (pathPrefix ++ pathSuffix) =
        observe step (observe step root pathPrefix) pathSuffix := by
          simp [observe, List.foldl_append]
    _ = observe step root pathPrefix :=
      observe_eq_of_absorbing
        (step := step) (observe step root pathPrefix) pathSuffix absorbing

/-- Every generated entry agrees with the independent direct path observer. -/
theorem value_eq_observe (entry : PrefixEntry State root step) :
    value entry = observe step root (path entry) := by
  induction entry with
  | root => rfl
  | child parent edge inductionHypothesis =>
      simp only [value, path, observe_snoc]
      rw [inductionHypothesis]

/-- Values read through the compiled parent links. -/
def cachedValues (entries : List (PrefixEntry State root step)) : List State :=
  entries.map value

/-- Values read by independently walking each authored coordinate. -/
def directValues (entries : List (PrefixEntry State root step)) : List State :=
  entries.map fun entry => observe step root (path entry)

/-- The compiled and direct observation vectors are exactly equal. -/
theorem cachedValues_eq_directValues
    (entries : List (PrefixEntry State root step)) :
    cachedValues entries = directValues entries := by
  simp [cachedValues, directValues, value_eq_observe]

/-- Any downstream observer receives the same result.  In particular, a
candidate filter cannot change source order, multiplicity, or refutation by
switching between these two representations. -/
theorem consumer_exact {Result : Type uResult}
    (consume : List State → Result)
    (entries : List (PrefixEntry State root step)) :
    consume (cachedValues entries) = consume (directValues entries) := by
  rw [cachedValues_eq_directValues]

/-- A lazy consumer may request any subfamily of generated terminals.  The
`filterMap` presentation intentionally preserves request order and duplicate
requests while omitting invalid physical indices on both sides. -/
def cachedAt (entries : List (PrefixEntry State root step))
    (requests : List Nat) : List State :=
  requests.filterMap fun index => (entries[index]?).map value

/-- Independent walking for exactly the same requested occurrence family. -/
def directAt (entries : List (PrefixEntry State root step))
    (requests : List Nat) : List State :=
  requests.filterMap fun index =>
    (entries[index]?).map fun entry => observe step root (path entry)

/-- Demand-driven cache filling is exact for every requested occurrence
family, including reordered and repeated requests. -/
theorem cachedAt_eq_directAt
    (entries : List (PrefixEntry State root step))
    (requests : List Nat) :
    cachedAt entries requests = directAt entries requests := by
  induction requests with
  | nil => rfl
  | cons index requests inductionHypothesis =>
      simp only [cachedAt, directAt] at inductionHypothesis ⊢
      cases selected : entries[index]? with
      | none => simp [selected, inductionHypothesis]
      | some entry =>
          simp [selected, value_eq_observe, inductionHypothesis]

/-- Every downstream consumer of a lazily requested observation vector sees
the independent result. -/
theorem demandedConsumer_exact {Result : Type uResult}
    (consume : List State → Result)
    (entries : List (PrefixEntry State root step))
    (requests : List Nat) :
    consume (cachedAt entries requests) =
      consume (directAt entries requests) := by
  rw [cachedAt_eq_directAt]

end PrefixEntry

/-! ## Absorbing query-state canaries -/

/-- A small independent model of the runtime observation trichotomy. -/
inductive QueryObservation where
  | unknown
  | absent
  | value (payload : Nat)
  deriving DecidableEq, Repr

/-- Unknown and absent observations stay unknown and absent below every
further edge.  A present value may reveal more structure. -/
def queryObservationStep : QueryObservation → Nat → QueryObservation
  | .unknown, _ => .unknown
  | .absent, _ => .absent
  | .value payload, edge => .value (payload + edge + 1)

theorem unknown_isAbsorbing :
    PrefixEntry.IsAbsorbing (step := queryObservationStep)
      .unknown := by
  intro edge
  rfl

theorem absent_isAbsorbing :
    PrefixEntry.IsAbsorbing (step := queryObservationStep)
      .absent := by
  intro edge
  rfl

/-- Positive transfer canary: a long suffix under a variable contributes no
observation, so skipping it is exact. -/
theorem unknown_suffix_skip_canary :
    observe queryObservationStep .unknown [7, 11, 13, 17] =
      .unknown := by
  exact PrefixEntry.observe_eq_of_absorbing
    (step := queryObservationStep) .unknown [7, 11, 13, 17]
    unknown_isAbsorbing

/-- Positive transfer canary: absence is equally stable under every deeper
coordinate. -/
theorem absent_suffix_skip_canary :
    observe queryObservationStep .absent [2, 3, 5] = .absent := by
  exact PrefixEntry.observe_eq_of_absorbing
    (step := queryObservationStep) .absent [2, 3, 5]
    absent_isAbsorbing

/-- Negative canary: an observed value is not generally absorbing.  Skipping
its suffix without an independent absorption proof would change meaning. -/
theorem value_suffix_is_not_generally_skippable :
    observe queryObservationStep (.value 10) [4] ≠ .value 10 := by
  decide

namespace Cost

open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra

/-- Unit work of independently walking every demanded path. -/
def directCost (paths : List Path) : Nat :=
  (paths.map List.length).sum

/-- Unit storage/work floor of one shared-prefix trie. -/
def trieCost (paths : List Path) : Nat :=
  frontierPrefixCost paths

/-- Selector coordinates and repeated-variable equality endpoints are merely
two occurrence-preserving sources of demands on the same observer. -/
def equalityPaths (equalities : List (Path × Path)) : List Path :=
  equalities.flatMap fun equality => [equality.1, equality.2]

/-- The physical graph compiler receives one ordered occurrence family.  No
consumer kind gains semantic authority from being included here. -/
def allConsumerPaths (selectorPaths : List Path)
    (equalities : List (Path × Path)) : List Path :=
  selectorPaths ++ equalityPaths equalities

/-- Prefix sharing never increases the number of distinct query edges that
must be represented.  This is a structural lower bound, not a claim that a
trie edge and a direct loop iteration have identical machine cost. -/
theorem trieCost_le_directCost (paths : List Path) :
    trieCost paths ≤ directCost paths := by
  induction paths with
  | nil => simp [trieCost, directCost, frontierPrefixCost, frontierPrefixes]
  | cons path paths inductionHypothesis =>
      have union :
          frontierPrefixes (path :: paths) =
            nonemptyPrefixes path ∪ frontierPrefixes paths := by
        ext pathPrefix
        simp [frontierPrefixes, nonemptyPrefixes]
      rw [trieCost, directCost, frontierPrefixCost, union]
      simp only [List.map_cons, List.sum_cons]
      calc
        (nonemptyPrefixes path ∪ frontierPrefixes paths).card ≤
            (nonemptyPrefixes path).card +
              (frontierPrefixes paths).card := Finset.card_union_le _ _
        _ = path.length + trieCost paths := by
          rw [nonemptyPrefixes_card]
          rfl
        _ ≤ path.length + directCost paths :=
          Nat.add_le_add_left inductionHypothesis path.length

/-- In the one-child-step representation model, any physical prefix set that
covers every demanded coordinate contains the canonical trie's prefix set.
Thus the union-of-prefixes realization has minimum edge cardinality in this
model; this is not a claim about arbitrary machine encodings or cache costs. -/
theorem trieCost_minimal_of_covers
    (paths : List Path) (representation : Finset Path)
    (covers : frontierPrefixes paths ⊆ representation) :
    trieCost paths ≤ representation.card := by
  exact Finset.card_le_card covers

/-- Cost of the better of direct walking and a trie carrying an explicit
metadata charge. -/
def selectedCost (metadata : Nat) (paths : List Path) : Nat :=
  min (directCost paths) (metadata + trieCost paths)

/-- Cost-aware admission is never worse than retaining the direct walker. -/
theorem selectedCost_le_directCost (metadata : Nat) (paths : List Path) :
    selectedCost metadata paths ≤ directCost paths := by
  exact min_le_left _ _

/-- The current compact runtime realization charges one extra unit per trie
edge plus one plan-level unit for cache metadata.  This is intentionally more
conservative than the structural lower bound: admission requires a strict
two-for-one edge reduction before machine constants are measured. -/
def chargedTrieCost (paths : List Path) : Nat :=
  1 + 2 * trieCost paths

/-- Runtime admission is a representation choice, not a semantic rule. -/
def runtimeAdmitted (paths : List Path) : Bool :=
  decide (chargedTrieCost paths < directCost paths)

theorem runtimeAdmitted_iff (paths : List Path) :
    runtimeAdmitted paths = true ↔
      chargedTrieCost paths < directCost paths := by
  simp [runtimeAdmitted]

/-- Every admitted graph has a strictly smaller charged structural cost than
independent walking. -/
theorem runtimeAdmitted_strict
    (paths : List Path) (admitted : runtimeAdmitted paths = true) :
    chargedTrieCost paths < directCost paths := by
  exact (runtimeAdmitted_iff paths).mp admitted

/-- A shared first edge makes the structural prefix bound strict. -/
example : trieCost [[0, 1], [0, 2]] = 3 := by decide

example : directCost [[0, 1], [0, 2]] = 4 := by decide

/-- Disjoint one-edge paths are the negative canary: no prefix work is saved. -/
example : trieCost [[0], [1]] = directCost [[0], [1]] := by decide

/-- Enough metadata overhead lawfully makes the selector retain direct
walking even on the small shared-prefix example. -/
example : selectedCost 2 [[0, 1], [0, 2]] = 4 := by decide

/-- Four paths with a long common prefix pass the conservative runtime
admission boundary. -/
example :
    runtimeAdmitted
      [[0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 5], [0, 1, 2, 6]] = true := by
  decide

/-- Disjoint one-edge coordinates fail the same admission test. -/
example : runtimeAdmitted [[0], [1]] = false := by decide

/-- Equality endpoints participate as ordinary demanded occurrences.  The
two copies of `[0, 1]` retain their direct-walk multiplicity while the trie
stores that prefix once. -/
example :
    directCost
      (allConsumerPaths [[0, 1, 2]] [([0, 1], [0, 1, 3])]) = 8 := by
  decide

example :
    trieCost
      (allConsumerPaths [[0, 1, 2]] [([0, 1], [0, 1, 3])]) = 4 := by
  decide

/-- Negative transfer canary: shallow disjoint selector and equality
coordinates still provide no prefix saving and therefore remain direct. -/
example :
    runtimeAdmitted (allConsumerPaths [[0]] [([1], [2])]) = false := by
  decide

end Cost

#print axioms PrefixEntry.value_eq_observe
#print axioms PrefixEntry.cachedValues_eq_directValues
#print axioms PrefixEntry.consumer_exact
#print axioms PrefixEntry.cachedAt_eq_directAt
#print axioms PrefixEntry.demandedConsumer_exact
#print axioms PrefixEntry.observe_eq_of_absorbing
#print axioms PrefixEntry.observe_append_eq_of_absorbing
#print axioms unknown_suffix_skip_canary
#print axioms absent_suffix_skip_canary
#print axioms value_suffix_is_not_generally_skippable
#print axioms Cost.trieCost_le_directCost
#print axioms Cost.trieCost_minimal_of_covers
#print axioms Cost.selectedCost_le_directCost
#print axioms Cost.runtimeAdmitted_iff
#print axioms Cost.runtimeAdmitted_strict

end Mettapedia.GSLT.LanguageDef.MatchDecisionPrefixObservationCompilation
