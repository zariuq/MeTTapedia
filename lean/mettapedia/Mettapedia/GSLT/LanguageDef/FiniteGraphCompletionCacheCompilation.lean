import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Completed structural observations on finite graphs

Two independent executable traversals inspect a finite graph, including graphs
with cycles.  The reference uses active-path rejection.  The second retains a
bounded list of completed successful node observations.  It records a node only
in its exit continuation, after every child has completed successfully.  A
possibly inaccurate eligibility hint controls retention, never acceptance.

The closed theorem starts with an empty cache.  Both traversals accept exactly
the same roots at a proved finite-graph depth bound.  The bound counts remaining
active-path depth, not instructions or total work.  Cached execution can spend
less work, and equality at arbitrary insufficient budgets is not claimed.

Nodes represent structural comparison states, not raw runtime addresses.  Their
local verdict and child comparisons come from a fixed interpreted graph.  A
runtime still owes this interpretation, source/origin identity, absence of
mutation within an observation, and correspondence of its EXIT stack to the
recursive exit continuation here.  This is not a refinement proof for a C
matcher, grounded equality, variable binding, or physical allocation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation

universe uKey uEntry

variable {Key : Type uKey}

/-- One independently inspected comparison state.  The local verdict may be
false even when a caller would like to treat the state as reflexive. -/
structure Node (Key : Type uKey) where
  localAccept : Bool
  children : List Key := []
  eligible : Bool := true
  deriving Repr

abbrev Graph (Key : Type uKey) := Key → Node Key

/-- A finite successful observation tree.  This independent inductive
specification has no cache, active-path parameter, or fuel. -/
inductive Accepted (graph : Graph Key) : Key → Prop
  | exit (key : Key) (localOk : (graph key).localAccept = true)
      (children : ∀ child ∈ (graph key).children, Accepted graph child) :
      Accepted graph key

def ChildOf (graph : Graph Key) (child parent : Key) : Prop :=
  child ∈ (graph parent).children

theorem Accepted.localOk {graph : Graph Key} {key : Key}
    (accepted : Accepted graph key) : (graph key).localAccept = true := by
  cases accepted with
  | exit _ localOk _ => exact localOk

theorem Accepted.child {graph : Graph Key} {key child : Key}
    (accepted : Accepted graph key) (member : child ∈ (graph key).children) :
    Accepted graph child := by
  cases accepted with
  | exit _ _ children => exact children child member

theorem Accepted.accessible {graph : Graph Key} {key : Key}
    (accepted : Accepted graph key) : Acc (ChildOf graph) key := by
  induction accepted with
  | exit key _ _ inductionHypothesis =>
      exact Acc.intro key (fun child member => inductionHypothesis child member)

private theorem accessible_not_self {α : Sort uKey} {relation : α → α → Prop}
    {key : α} (accessible : Acc relation key) : ¬ relation key key := by
  induction accessible with
  | intro key _ inductionHypothesis =>
      intro loop
      exact inductionHypothesis key loop loop

/-- A finite successful observation cannot contain a reachable structural
cycle, even when every node's eligibility hint says it may be cached. -/
theorem Accepted.no_cycle {graph : Graph Key} {key : Key}
    (accepted : Accepted graph key) :
    ¬ Relation.TransGen (ChildOf graph) key key :=
  accessible_not_self accepted.accessible.transGen

def ActiveAncestors (graph : Graph Key) (path : List Key) (key : Key) : Prop :=
  ∀ ancestor ∈ path, Relation.TransGen (ChildOf graph) key ancestor

theorem activeAncestors_child {graph : Graph Key} {path : List Key}
    {key child : Key} (ancestors : ActiveAncestors graph path key)
    (member : child ∈ (graph key).children) :
    ActiveAncestors graph (key :: path) child := by
  intro ancestor present
  rcases List.mem_cons.mp present with same | older
  · subst ancestor
    exact Relation.TransGen.single member
  · exact Relation.TransGen.head member (ancestors ancestor older)

theorem Accepted.not_active {graph : Graph Key} {path : List Key} {key : Key}
    (accepted : Accepted graph key)
    (ancestors : ActiveAncestors graph path key) : key ∉ path := by
  intro present
  exact accepted.no_cycle (ancestors key present)

/-! ## Independent ordinary active-path traversal -/

/-- Sequence successful child observations and count their actual expansions. -/
def visitChildren (visit : Key → Option Nat) : List Key → Option Nat
  | [] => some 0
  | child :: children => do
      let count ← visit child
      let rest ← visitChildren visit children
      pure (count + rest)

variable [DecidableEq Key]

def ordinary (graph : Graph Key) : Nat → List Key → Key → Option Nat
  | 0, _, _ => none
  | fuel + 1, path, key =>
      if key ∈ path then none
      else if (graph key).localAccept then do
        let count ← visitChildren (ordinary graph fuel (key :: path))
          (graph key).children
        pure (count + 1)
      else none

omit [DecidableEq Key] in
theorem visitChildren_sound {visit : Key → Option Nat} {children : List Key}
    {count : Nat} (executed : visitChildren visit children = some count) :
    ∀ child ∈ children, ∃ childCount, visit child = some childCount := by
  induction children generalizing count with
  | nil => simp
  | cons child children inductionHypothesis =>
      cases first : visit child with
      | none => simp [visitChildren, first] at executed
      | some firstCount =>
          cases rest : visitChildren visit children with
          | none => simp [visitChildren, first, rest] at executed
          | some restCount =>
              intro selected member
              rcases List.mem_cons.mp member with same | later
              · subst selected
                exact ⟨firstCount, first⟩
              · exact inductionHypothesis rest selected later

omit [DecidableEq Key] in
theorem visitChildren_complete {visit : Key → Option Nat} {children : List Key}
    (complete : ∀ child ∈ children, ∃ count, visit child = some count) :
    ∃ count, visitChildren visit children = some count := by
  induction children with
  | nil => exact ⟨0, rfl⟩
  | cons child children inductionHypothesis =>
      obtain ⟨firstCount, first⟩ := complete child (by simp)
      obtain ⟨restCount, rest⟩ := inductionHypothesis
        (fun selected member => complete selected (by simp [member]))
      exact ⟨firstCount + restCount, by simp [visitChildren, first, rest]⟩

theorem ordinary_sound {graph : Graph Key} {fuel : Nat} {path : List Key}
    {key : Key} {count : Nat} (executed : ordinary graph fuel path key = some count) :
    Accepted graph key := by
  induction fuel generalizing path key count with
  | zero => simp [ordinary] at executed
  | succ fuel inductionHypothesis =>
      by_cases active : key ∈ path
      · simp [ordinary, active] at executed
      by_cases localOk : (graph key).localAccept = true
      · cases children : visitChildren (ordinary graph fuel (key :: path))
            (graph key).children with
        | none => simp [ordinary, active, localOk, children] at executed
        | some childCount =>
            exact Accepted.exit key localOk (fun child member => by
              obtain ⟨count, observed⟩ := visitChildren_sound children child member
              exact inductionHypothesis observed)
      · simp [ordinary, active, localOk] at executed

/-- Cardinality bounds active-path depth.  Repeated DAG occurrences do not
consume this bound across sibling branches. -/
theorem ordinary_complete [Fintype Key] {graph : Graph Key} {fuel : Nat}
    {path : List Key} {key : Key}
    (accepted : Accepted graph key) (unique : path.Nodup)
    (ancestors : ActiveAncestors graph path key)
    (adequate : Fintype.card Key < path.length + fuel) :
    ∃ count, ordinary graph fuel path key = some count := by
  induction fuel generalizing path key with
  | zero =>
      have bounded := unique.length_le_card
      omega
  | succ fuel inductionHypothesis =>
      have inactive := accepted.not_active ancestors
      have nextUnique : (key :: path).Nodup := List.nodup_cons.mpr ⟨inactive, unique⟩
      have nextAdequate : Fintype.card Key < (key :: path).length + fuel := by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using adequate
      obtain ⟨count, children⟩ := visitChildren_complete
        (visit := ordinary graph fuel (key :: path))
        (children := (graph key).children) (fun child member =>
          inductionHypothesis (accepted.child member) nextUnique
            (activeAncestors_child ancestors member) nextAdequate)
      exact ⟨count + 1, by simp [ordinary, inactive, accepted.localOk, children]⟩

def depthBound (Key : Type uKey) [Fintype Key] : Nat := Fintype.card Key + 1

theorem ordinary_closed_iff [Fintype Key] (graph : Graph Key) (key : Key) :
    (∃ count, ordinary graph (depthBound Key) [] key = some count) ↔ Accepted graph key := by
  constructor
  · rintro ⟨count, executed⟩
    exact ordinary_sound executed
  · intro accepted
    exact ordinary_complete accepted (by simp)
      (by simp [ActiveAncestors]) (by simp [depthBound])

/-! ## Bounded completed-success traversal -/

abbrev Cache (Key : Type uKey) := List Key

structure Stats where
  expansions : Nat := 0
  hits : Nat := 0
  deriving DecidableEq, Repr

def Stats.add (left right : Stats) : Stats :=
  ⟨left.expansions + right.expansions, left.hits + right.hits⟩

abbrev CachedResult (Key : Type uKey) := Cache Key × Stats

/-- Replacement can discard any older receipt.  This concrete policy retains
the newest bounded prefix; it does not assume an unbounded memo table. -/
def remember (capacity : Nat) (key : Key) (cache : Cache Key) : Cache Key :=
  (key :: cache).take capacity

/-- The invariant records finite observation receipts, not assumed equality
with the cached algorithm.  Empty initialization and actual exits establish it. -/
def CacheValid (graph : Graph Key) (capacity : Nat) (cache : Cache Key) : Prop :=
  cache.length ≤ capacity ∧ ∀ key ∈ cache, Accepted graph key

omit [DecidableEq Key] in
theorem empty_valid (graph : Graph Key) (capacity : Nat) :
    CacheValid graph capacity [] := by
  simp [CacheValid]

omit [DecidableEq Key] in
theorem remember_valid {graph : Graph Key} {capacity : Nat} {cache : Cache Key}
    {key : Key} (valid : CacheValid graph capacity cache)
    (receipt : Accepted graph key) :
    CacheValid graph capacity (remember capacity key cache) := by
  constructor
  · simp [remember, List.length_take]
  · intro selected member
    have source : selected ∈ key :: cache := List.mem_of_mem_take member
    rcases List.mem_cons.mp source with same | older
    · subst selected
      exact receipt
    · exact valid.2 selected older

def visitCachedChildren
    (visit : Key → Cache Key → Option (CachedResult Key)) :
    List Key → Cache Key → Option (CachedResult Key)
  | [], cache => some (cache, {})
  | child :: children, cache => do
      let (next, firstStats) ← visit child cache
      let (final, restStats) ← visitCachedChildren visit children next
      pure (final, firstStats.add restStats)

/-- The recursive return after `visitCachedChildren` is the checked EXIT.
Publication is deliberately after that return, never on initial entry.  Hits
precede active-path lookup, as in a completed-comparison optimization. -/
def cached (graph : Graph Key) (capacity : Nat) :
    Nat → List Key → Key → Cache Key → Option (CachedResult Key)
  | 0, _, _, _ => none
  | fuel + 1, path, key, cache =>
      if (graph key).eligible && decide (key ∈ cache) then
        some (cache, { hits := 1 })
      else if key ∈ path then none
      else if (graph key).localAccept then do
        let (next, stats) ← visitCachedChildren
          (cached graph capacity fuel (key :: path)) (graph key).children cache
        let completed := if (graph key).eligible then remember capacity key next else next
        pure (completed, { stats with expansions := stats.expansions + 1 })
      else none

omit [DecidableEq Key] in
theorem visitCachedChildren_sound {graph : Graph Key} {capacity : Nat}
    {visit : Key → Cache Key → Option (CachedResult Key)}
    (visitSound : ∀ key cache result, CacheValid graph capacity cache →
      visit key cache = some result →
      Accepted graph key ∧ CacheValid graph capacity result.1)
    {children : List Key} {cache : Cache Key} {result : CachedResult Key}
    (valid : CacheValid graph capacity cache)
    (executed : visitCachedChildren visit children cache = some result) :
    (∀ child ∈ children, Accepted graph child) ∧
      CacheValid graph capacity result.1 := by
  induction children generalizing cache result with
  | nil =>
      simp [visitCachedChildren] at executed
      subst result
      exact ⟨by simp, valid⟩
  | cons child children inductionHypothesis =>
      cases first : visit child cache with
      | none => simp [visitCachedChildren, first] at executed
      | some firstResult =>
          have firstSound := visitSound child cache firstResult valid first
          cases rest : visitCachedChildren visit children firstResult.1 with
          | none => simp [visitCachedChildren, first, rest] at executed
          | some restResult =>
              have restSound := inductionHypothesis firstSound.2 rest
              simp [visitCachedChildren, first, rest] at executed
              subst result
              exact ⟨fun selected member => by
                rcases List.mem_cons.mp member with same | later
                · subst selected
                  exact firstSound.1
                · exact restSound.1 selected later, restSound.2⟩

/-- Every retained receipt is derived from completed children.  This proves
validity even when the graph is cyclic and every eligibility hint is true. -/
theorem cached_sound {graph : Graph Key} {capacity fuel : Nat}
    {path : List Key} {key : Key} {cache : Cache Key} {result : CachedResult Key}
    (valid : CacheValid graph capacity cache)
    (executed : cached graph capacity fuel path key cache = some result) :
    Accepted graph key ∧ CacheValid graph capacity result.1 := by
  induction fuel generalizing path key cache result with
  | zero => simp [cached] at executed
  | succ fuel inductionHypothesis =>
      by_cases hit : (graph key).eligible = true ∧ key ∈ cache
      · have present : key ∈ cache := hit.2
        simp [cached, hit] at executed
        subst result
        exact ⟨valid.2 key present, valid⟩
      · by_cases active : key ∈ path
        · simp [cached, hit, active] at executed
        by_cases localOk : (graph key).localAccept = true
        · cases children : visitCachedChildren
              (cached graph capacity fuel (key :: path)) (graph key).children cache with
          | none => simp [cached, hit, active, localOk, children] at executed
          | some childResult =>
              have childSound := visitCachedChildren_sound
                (fun child before after admitted observed => inductionHypothesis admitted observed)
                valid children
              have receipt : Accepted graph key := Accepted.exit key localOk childSound.1
              simp [cached, hit, active, localOk, children] at executed
              subst result
              constructor
              · exact receipt
              · split
                · exact remember_valid childSound.2 receipt
                · exact childSound.2
        · simp [cached, hit, active, localOk] at executed

omit [DecidableEq Key] in
theorem visitCachedChildren_complete
    {visit : Key → Cache Key → Option (CachedResult Key)} {children : List Key}
    (complete : ∀ child ∈ children, ∀ cache, ∃ result, visit child cache = some result)
    (cache : Cache Key) :
    ∃ result, visitCachedChildren visit children cache = some result := by
  induction children generalizing cache with
  | nil => exact ⟨(cache, {}), rfl⟩
  | cons child children inductionHypothesis =>
      obtain ⟨first, observed⟩ := complete child (by simp) cache
      obtain ⟨rest, continued⟩ := inductionHypothesis
        (fun selected member => complete selected (by simp [member])) first.1
      exact ⟨(rest.1, first.2.add rest.2), by
        simp [visitCachedChildren, observed, continued]⟩

/-- A cache cannot turn an ordinary successful traversal into failure, even
before using cache validity.  This compares the actual independent recursions. -/
theorem cached_complete_of_ordinary {graph : Graph Key} {capacity fuel : Nat}
    {path : List Key} {key : Key} {count : Nat}
    (executed : ordinary graph fuel path key = some count) :
    ∀ cache, ∃ result, cached graph capacity fuel path key cache = some result := by
  induction fuel generalizing path key count with
  | zero => simp [ordinary] at executed
  | succ fuel inductionHypothesis =>
      intro cache
      by_cases hit : (graph key).eligible = true ∧ key ∈ cache
      · exact ⟨(cache, { hits := 1 }), by simp [cached, hit]⟩
      by_cases active : key ∈ path
      · simp [ordinary, active] at executed
      by_cases localOk : (graph key).localAccept = true
      · cases children : visitChildren (ordinary graph fuel (key :: path))
            (graph key).children with
        | none => simp [ordinary, active, localOk, children] at executed
        | some childCount =>
            obtain ⟨childResult, continued⟩ := visitCachedChildren_complete
              (visit := cached graph capacity fuel (key :: path))
              (children := (graph key).children) (fun child member before => by
                obtain ⟨observedCount, observed⟩ := visitChildren_sound children child member
                exact inductionHypothesis observed before) cache
            refine ⟨((if (graph key).eligible then remember capacity key childResult.1
                else childResult.1),
              { childResult.2 with expansions := childResult.2.expansions + 1 }), ?_⟩
            simp [cached, hit, active, localOk, continued]
      · simp [ordinary, active, localOk] at executed

theorem cached_closed_iff [Fintype Key] (graph : Graph Key) (capacity : Nat)
    (key : Key) (cache : Cache Key) (valid : CacheValid graph capacity cache) :
    (∃ result, cached graph capacity (depthBound Key) [] key cache = some result) ↔
      Accepted graph key := by
  constructor
  · rintro ⟨result, executed⟩
    exact (cached_sound valid executed).1
  · intro accepted
    obtain ⟨count, executed⟩ := (ordinary_closed_iff graph key).2 accepted
    exact cached_complete_of_ordinary executed cache

/-- Closed initial-empty-cache preservation and reflection.  The quantifiers
include all finite graphs, all eligibility hints, and capacity zero. -/
theorem initial_empty_acceptance_iff [Fintype Key]
    (graph : Graph Key) (capacity : Nat) (key : Key) :
    (∃ result, cached graph capacity (depthBound Key) [] key [] = some result) ↔
      ∃ count, ordinary graph (depthBound Key) [] key = some count := by
  rw [cached_closed_iff graph capacity key [] (empty_valid graph capacity),
    ordinary_closed_iff]

private theorem option_isSome_iff {α : Type*} (value : Option α) :
    value.isSome = true ↔ ∃ result, value = some result := by
  cases value <;> simp

/-- Executable Boolean acceptance equality at the justified depth bound. -/
theorem initial_empty_acceptance_exact [Fintype Key]
    (graph : Graph Key) (capacity : Nat) (key : Key) :
    (cached graph capacity (depthBound Key) [] key []).isSome =
      (ordinary graph (depthBound Key) [] key).isSome := by
  have same := initial_empty_acceptance_iff graph capacity key
  rw [← option_isSome_iff, ← option_isSome_iff] at same
  exact Bool.eq_iff_iff.mpr same

/-! ## Authoritative append stages and receipt invalidation -/

variable {Entry : Type uEntry}

/-- Length identifies an immutable prefix only along an actual append path. -/
theorem append_prefix_eq_of_length_eq {before after : List Entry}
    (extension : before <+: after) (sameLength : before.length = after.length) :
    before = after := by
  obtain ⟨tail, rfl⟩ := extension
  have empty : tail = [] := by
    have zero : tail.length = 0 := by simpa using sameLength.symm
    exact List.length_eq_zero_iff.mp zero
  simp [empty]

/-- A different authoritative length declines all earlier receipts. -/
def reuseAfterAppend (before after : List Entry) (cache : Cache Key) : Cache Key :=
  if before.length = after.length then cache else []

omit [DecidableEq Key] in
theorem reuseAfterAppend_valid (interpret : List Entry → Graph Key)
    {before after : List Entry} {capacity : Nat} {cache : Cache Key}
    (extension : before <+: after) (valid : CacheValid (interpret before) capacity cache) :
    CacheValid (interpret after) capacity (reuseAfterAppend before after cache) := by
  by_cases sameLength : before.length = after.length
  · have same := append_prefix_eq_of_length_eq extension sameLength
    subst after
    simpa [reuseAfterAppend] using valid
  · simpa [reuseAfterAppend, sameLength] using empty_valid (interpret after) capacity

/-- Receipts are obtained from an actual empty-cache run, then either retained
under an equal authoritative prefix or discarded after growth.  No cache
correctness or graph-equality premise is assumed at the public boundary. -/
theorem completed_then_append_acceptance_iff [Fintype Key]
    (interpret : List Entry → Graph Key) {before after : List Entry}
    (extension : before <+: after) (capacity : Nat) (first next : Key)
    {completed : CachedResult Key}
    (observed : cached (interpret before) capacity (depthBound Key) [] first [] = some completed) :
    (∃ result, cached (interpret after) capacity (depthBound Key) [] next
        (reuseAfterAppend before after completed.1) = some result) ↔
      ∃ count, ordinary (interpret after) (depthBound Key) [] next = some count := by
  have receipt := (cached_sound (empty_valid (interpret before) capacity) observed).2
  rw [cached_closed_iff (interpret after) capacity next _
      (reuseAfterAppend_valid interpret extension receipt), ordinary_closed_iff]

/-! ## Executable positive and negative controls -/

namespace Canaries

private def shared : Graph (Fin 4)
  | 0 => ⟨true, [1, 1], true⟩
  | 1 => ⟨true, [2, 3], true⟩
  | _ => ⟨true, [], true⟩

/-- A repeated DAG is traversed seven times ordinarily and expanded four
times with one completed-subgraph hit.  These are model counts, not timings. -/
example : ordinary shared 5 [] 0 = some 7 ∧
    cached shared 8 5 [] 0 [] = some ([0, 1, 3, 2], ⟨4, 1⟩) := by
  decide

/-- Capacity zero remains correct and performs every expansion. -/
example : cached shared 0 5 [] 0 [] = some ([], ⟨7, 0⟩) := by
  decide

private def selfCycle : Graph (Fin 1) := fun _ => ⟨true, [0], true⟩

example : ordinary selfCycle 2 [] 0 = none ∧ cached selfCycle 8 2 [] 0 [] = none := by
  decide

/-- Deliberately incorrect control: caching at ENTER accepts a recurrence
before any completed observation can justify it. -/
private def enterCached (graph : Graph Key) (capacity : Nat) :
    Nat → List Key → Key → Cache Key → Bool
  | 0, _, _, _ => false
  | fuel + 1, path, key, cache =>
      if key ∈ cache then true
      else if key ∈ path then false
      else (graph key).localAccept && (graph key).children.all
        (fun child => enterCached graph capacity fuel (key :: path) child
          (remember capacity key cache))

example : enterCached selfCycle 8 2 [] 0 [] = true ∧
    cached selfCycle 8 2 [] 0 [] = none := by
  decide

private def failedLeaf : Graph (Fin 2)
  | 0 => ⟨true, [1], true⟩
  | _ => ⟨false, [], true⟩

example : ordinary failedLeaf 3 [] 0 = none ∧ cached failedLeaf 8 3 [] 0 [] = none := by
  decide

/-- Origin is part of the interpreted comparison key.  A successful live
observation does not justify a distinct source-origin observation. -/
private def originGraph : Graph (Fin 1 × Bool) := fun key => ⟨!key.2, [], true⟩

example : cached originGraph 8 3 [] (0, false) [] =
      some ([(0, false)], ⟨1, 0⟩) ∧
    cached originGraph 8 3 [] (0, true) [(0, false)] = none := by
  decide

/-- The same hinted comparison is terminal when its hidden variable is
unbound, and cyclic after a new binding.  The hint itself never changes. -/
private def hiddenVariableGraph (bindings : List Bool) : Graph (Fin 1) :=
  fun _ => ⟨true, if bindings.headD false then [0] else [], true⟩

example : cached (hiddenVariableGraph []) 8 2 [] 0 [] = some ([0], ⟨1, 0⟩) ∧
    cached (hiddenVariableGraph [true]) 8 2 [] 0
      (reuseAfterAppend ([] : List Bool) [true] [0]) = none ∧
    cached (hiddenVariableGraph [true]) 8 2 [] 0 [0] = some ([0], ⟨0, 1⟩) := by
  decide

/-- Equal lengths without append authority do not validate old receipts. -/
example : reuseAfterAppend [false] [true] ([0] : Cache (Fin 1)) = [0] ∧
    ¬ ([false] <+: [true]) := by
  decide

/-- An already justified receipt can succeed at an insufficient depth budget
where ordinary traversal exhausts.  The closed theorem uses `depthBound`. -/
example : ordinary shared 1 [] 0 = none ∧
    cached shared 8 1 [] 0 [0] = some ([0], ⟨0, 1⟩) := by
  decide

end Canaries

#print axioms ordinary_sound
#print axioms ordinary_complete
#print axioms cached_sound
#print axioms initial_empty_acceptance_exact
#print axioms append_prefix_eq_of_length_eq
#print axioms completed_then_append_acceptance_iff

end Mettapedia.GSLT.LanguageDef.FiniteGraphCompletionCacheCompilation
