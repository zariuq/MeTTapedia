import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Ordered graph search with global visited positions

This model retains a pending alternative stack and a global set of visited
node/position pairs. It distinguishes exhausted work bounds from an absent
match. A decreasing measure gives a sufficient bound for every finite graph,
including nullable cycles. Reachability is specified independently as the
reflexive transitive closure of graph transitions.

Examples distinguish selected prefixes from whole-language membership and
nullable repetition from a weaker, single-choice loop. The model corresponds
to symbolic graph operations; it does not verify a source parser, Thompson
construction, native allocator or compiled C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.OrderedGraphSearch

universe u v w z

abbrev Point (State : Type u) (length : Nat) := State × Fin (length + 1)

inductive Node (State : Type u) (Class : Type v) (Assertion : Type w) (Tag : Type z) where
  | accept (tag : Tag)
  | dead
  | jump (next : State)
  | choice (first second : State)
  | consume (class_ : Class) (next : State)
  | assertion (assertion_ : Assertion) (next : State)

structure Probe (Class : Type v) (Assertion : Type w) (length : Nat) where
  contains : Class → Fin (length + 1) → Bool
  holds : Assertion → Fin (length + 1) → Bool

structure Configuration (State : Type u) (length : Nat) where
  pending : List (Point State length)
  visited : Finset (Point State length)

inductive StepResult (State : Type u) (Tag : Type z) (length : Nat) where
  | halt (selected : Option (Point State length × Tag))
  | advance (configuration : Configuration State length)

inductive RunResult (State : Type u) (Tag : Type z) (length : Nat) where
  | exhausted
  | halt (selected : Option (Point State length × Tag))
  deriving DecidableEq

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

def successor (position : Fin (length + 1)) : Option (Fin (length + 1)) :=
  if h : position.val < length then some ⟨position.val + 1, by omega⟩ else none

theorem successor_advances {position after : Fin (length + 1)}
    (advanced : successor position = some after) :
    after.val = position.val + 1 ∧ after.val ≤ length := by
  simp only [successor] at advanced
  split at advanced
  · cases advanced
    simp
    omega
  · simp at advanced

def acceptedTag : Node State Class Assertion Tag → Option Tag
  | .accept tag => some tag
  | _ => none

def expand (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (point : Point State length) : List (Point State length) :=
  match graph point.1 with
  | .accept _ | .dead => []
  | .jump next => [(next, point.2)]
  | .choice first second => [(first, point.2), (second, point.2)]
  | .consume class_ next =>
      if probe.contains class_ point.2 then
        match successor point.2 with
        | some after => [(next, after)]
        | none => []
      else []
  | .assertion assertion_ next =>
      if probe.holds assertion_ point.2 then [(next, point.2)] else []

theorem expand_length (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (point : Point State length) :
    (expand graph probe point).length ≤ 2 := by
  cases node : graph point.1 with
  | accept tag => simp [expand, node]
  | dead => simp [expand, node]
  | jump next => simp [expand, node]
  | choice first second => simp [expand, node]
  | consume class_ next =>
      simp only [expand, node]
      split
      · cases advanced : successor point.2 <;> simp_all
      · simp
  | assertion assertion_ next =>
      simp only [expand, node]
      split <;> simp

def step [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (configuration : Configuration State length) :
    StepResult State Tag length :=
  match configuration.pending with
  | [] => .halt none
  | point :: rest =>
      if point ∈ configuration.visited then .advance ⟨rest, configuration.visited⟩
      else match acceptedTag (graph point.1) with
        | some tag => .halt (some (point, tag))
        | none => .advance ⟨expand graph probe point ++ rest, insert point configuration.visited⟩

def rank [Fintype State] (configuration : Configuration State length) : Nat :=
  2 * (Fintype.card (Point State length) - configuration.visited.card) + configuration.pending.length

theorem step_decreases [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (configuration next : Configuration State length)
    (transition : step graph probe configuration = .advance next) :
    rank next < rank configuration := by
  rcases configuration with ⟨pending, visited⟩
  cases pending with
  | nil => simp [step] at transition
  | cons point rest =>
      by_cases seen : point ∈ visited
      · simp only [step, seen, if_pos, StepResult.advance.injEq] at transition
        subst next
        simp only [rank, List.length_cons]
        omega
      · cases accept : acceptedTag (graph point.1) with
        | some tag => simp [step, seen, accept] at transition
        | none =>
            simp [step, seen, accept] at transition
            subst next
            have size := expand_length graph probe point
            have card := Finset.card_le_univ (insert point visited)
            rw [Finset.card_insert_of_notMem seen] at card
            simp only [rank, List.length_append, List.length_cons,
              Finset.card_insert_of_notMem seen]
            omega

def run [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) : Nat → Configuration State length → RunResult State Tag length
  | 0, _ => .exhausted
  | fuel + 1, configuration =>
      match step graph probe configuration with
      | .halt selected => .halt selected
      | .advance next => run graph probe fuel next

/-- Work exhaustion cannot masquerade as a negative match. -/
theorem run_sufficient [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (fuel : Nat) : ∀ configuration, rank configuration < fuel →
      run graph probe fuel configuration ≠ .exhausted := by
  induction fuel with
  | zero => intro configuration sufficient; omega
  | succ fuel ih =>
      intro configuration sufficient
      cases transition : step graph probe configuration with
      | halt selected => simp [run, transition]
      | advance next =>
          have smaller := step_decreases graph probe configuration next transition
          have enough : rank next < fuel := by omega
          simpa only [run, transition] using ih next enough

def initial (state : State) : Configuration State length := ⟨[(state, 0)], ∅⟩

/-- Nullable cycles and pending duplicates fit a graph/input-size bound. -/
theorem initial_work_bound [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (state : State) :
    run graph probe (2 * (Fintype.card State * (length + 1)) + 2) (initial state) ≠ .exhausted := by
  apply run_sufficient
  simp [rank, initial, Point, Fintype.card_prod]

theorem run_more [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (fuel extra : Nat) : ∀ configuration,
      run graph probe fuel configuration ≠ .exhausted →
      run graph probe (fuel + extra) configuration = run graph probe fuel configuration := by
  induction fuel with
  | zero => simp [run]
  | succ fuel ih =>
      intro configuration finished
      cases transition : step graph probe configuration with
      | halt selected => simp [run, transition, Nat.succ_add]
      | advance next =>
          simp only [run, transition] at finished
          simpa only [run, transition, Nat.succ_add] using ih next finished

def reachable (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (start point : Point State length) : Prop :=
  Relation.ReflTransGen (fun first second => second ∈ expand graph probe first) start point

def reachableConfiguration (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (start : Point State length)
    (configuration : Configuration State length) : Prop :=
  (∀ point ∈ configuration.pending, reachable graph probe start point) ∧
  (∀ point ∈ configuration.visited, reachable graph probe start point)

theorem step_preserves_reachability [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (start : Point State length) (configuration next : Configuration State length)
    (sound : reachableConfiguration graph probe start configuration)
    (transition : step graph probe configuration = .advance next) :
    reachableConfiguration graph probe start next := by
  rcases configuration with ⟨pending, visited⟩
  cases pending with
  | nil => simp [step] at transition
  | cons point rest =>
      have reached := sound.1 point (by simp)
      by_cases seen : point ∈ visited
      · simp only [step, seen, if_pos, StepResult.advance.injEq] at transition
        subst next
        exact ⟨fun next member => sound.1 next (by simp [member]), sound.2⟩
      · cases accept : acceptedTag (graph point.1) with
        | some tag => simp [step, seen, accept] at transition
        | none =>
            simp [step, seen, accept] at transition
            subst next
            constructor
            · intro next member
              rcases List.mem_append.mp member with expanded | pending
              · exact reached.tail expanded
              · exact sound.1 next (by simp [pending])
            · intro next member
              rcases Finset.mem_insert.mp member with same | earlier
              · subst next; exact reached
              · exact sound.2 next earlier

theorem step_match_sound [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (start : Point State length) (configuration : Configuration State length)
    (sound : reachableConfiguration graph probe start configuration)
    (point : Point State length) (tag : Tag)
    (transition : step graph probe configuration = .halt (some (point, tag))) :
    reachable graph probe start point ∧ acceptedTag (graph point.1) = some tag := by
  rcases configuration with ⟨pending, visited⟩
  cases pending with
  | nil => simp [step] at transition
  | cons first rest =>
      by_cases seen : first ∈ visited
      · simp [step, seen] at transition
      · cases accept : acceptedTag (graph first.1) with
        | none => simp [step, seen, accept] at transition
        | some found =>
            simp [step, seen, accept] at transition
            obtain ⟨rfl, rfl⟩ := transition
            exact ⟨sound.1 first (by simp), accept⟩

/-- The selected result follows actual class/assertion transitions from start. -/
theorem run_match_sound [DecidableEq State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (start : Point State length) (fuel : Nat) :
    ∀ configuration, reachableConfiguration graph probe start configuration →
      ∀ point tag, run graph probe fuel configuration = .halt (some (point, tag)) →
        reachable graph probe start point ∧ acceptedTag (graph point.1) = some tag := by
  induction fuel with
  | zero => simp [run]
  | succ fuel ih =>
      intro configuration sound point tag selected
      cases transition : step graph probe configuration with
      | halt found =>
          simp only [run, transition, RunResult.halt.injEq] at selected
          subst found
          exact step_match_sound graph probe start configuration sound point tag transition
      | advance next =>
          simp only [run, transition] at selected
          exact ih next (step_preserves_reachability graph probe start configuration next sound transition)
            point tag selected

theorem initial_reachable (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (state : State) :
    reachableConfiguration graph probe (state, 0) (initial state) := by
  constructor
  · intro point member
    simp only [initial, List.mem_singleton] at member
    subst point
    exact Relation.ReflTransGen.refl
  · simp [initial]

def fullToken : RunResult State Tag length → Bool
  | .halt (some ((_, position), _)) => position.val == length
  | _ => false

/-- Relabel classes/assertions without changing node identities or priorities. -/
def mapNode {Class' : Type v} {Assertion' : Type w}
    (classMap : Class → Class') (assertionMap : Assertion → Assertion') :
    Node State Class Assertion Tag → Node State Class' Assertion' Tag
  | .accept tag => .accept tag
  | .dead => .dead
  | .jump next => .jump next
  | .choice first second => .choice first second
  | .consume class_ next => .consume (classMap class_) next
  | .assertion assertion_ next => .assertion (assertionMap assertion_) next

theorem acceptedTag_map {Class' : Type v} {Assertion' : Type w}
    (classMap : Class → Class') (assertionMap : Assertion → Assertion')
    (node : Node State Class Assertion Tag) :
    acceptedTag (mapNode classMap assertionMap node) = acceptedTag node := by
  cases node <;> rfl

theorem expand_map {Class' : Type v} {Assertion' : Type w}
    (classMap : Class → Class') (assertionMap : Assertion → Assertion')
    (graph : State → Node State Class Assertion Tag)
    (source : Probe Class Assertion length) (target : Probe Class' Assertion' length)
    (classes : ∀ class_ position, target.contains (classMap class_) position = source.contains class_ position)
    (assertions : ∀ assertion_ position, target.holds (assertionMap assertion_) position =
      source.holds assertion_ position)
    (point : Point State length) :
    expand (fun state => mapNode classMap assertionMap (graph state)) target point =
      expand graph source point := by
  cases node : graph point.1 <;> simp [expand, node, mapNode, classes, assertions]

theorem step_map [DecidableEq State] {Class' : Type v} {Assertion' : Type w}
    (classMap : Class → Class') (assertionMap : Assertion → Assertion')
    (graph : State → Node State Class Assertion Tag)
    (source : Probe Class Assertion length) (target : Probe Class' Assertion' length)
    (classes : ∀ class_ position, target.contains (classMap class_) position = source.contains class_ position)
    (assertions : ∀ assertion_ position, target.holds (assertionMap assertion_) position =
      source.holds assertion_ position)
    (configuration : Configuration State length) :
    step (fun state => mapNode classMap assertionMap (graph state)) target configuration =
      step graph source configuration := by
  rcases configuration with ⟨pending, visited⟩
  cases pending with
  | nil => rfl
  | cons point rest =>
      simp only [step, acceptedTag_map,
        expand_map classMap assertionMap graph source target classes assertions]

/-- A class quotient with independently equal probes preserves selected spans,
tags, pending alternatives, visited history and exhaustion, not only membership. -/
theorem run_map [DecidableEq State] {Class' : Type v} {Assertion' : Type w}
    (classMap : Class → Class') (assertionMap : Assertion → Assertion')
    (graph : State → Node State Class Assertion Tag)
    (source : Probe Class Assertion length) (target : Probe Class' Assertion' length)
    (classes : ∀ class_ position, target.contains (classMap class_) position = source.contains class_ position)
    (assertions : ∀ assertion_ position, target.holds (assertionMap assertion_) position =
      source.holds assertion_ position)
    (fuel : Nat) : ∀ configuration,
    run (fun state => mapNode classMap assertionMap (graph state)) target fuel configuration =
      run graph source fuel configuration := by
  induction fuel with
  | zero => intro configuration; rfl
  | succ fuel ih =>
      intro configuration
      simp only [run, step_map classMap assertionMap graph source target classes assertions]
      cases step graph source configuration with
      | halt selected => rfl
      | advance next => exact ih next

private def asciiProbe (length : Nat) : Probe Unit Unit length :=
  ⟨fun _ position => position.val < length, fun _ _ => false⟩

private def preferredPrefix (reverse : Bool) : Fin 5 → Node (Fin 5) Unit Unit Unit :=
  fun state => match state.val with
    | 0 => if reverse then .choice 3 1 else .choice 1 3
    | 1 => .consume () 2
    | 2 => .accept ()
    | 3 => .consume () 4
    | _ => .consume () 2

theorem selected_prefix_is_not_whole_language_membership :
    run (preferredPrefix false) (asciiProbe 2) 22 (initial 0) =
      .halt (some ((2, 1), ())) ∧
    fullToken (run (preferredPrefix false) (asciiProbe 2) 22 (initial 0)) = false ∧
    fullToken (run (preferredPrefix true) (asciiProbe 2) 22 (initial 0)) = true := by decide

private def nullableRepetition : Fin 6 → Node (Fin 6) Unit Unit Unit :=
  fun state => match state.val with
    | 0 => .choice 1 5
    | 1 => .choice 2 3
    | 2 => .jump 4
    | 3 => .consume () 4
    | 4 => .choice 1 5
    | _ => .accept ()

private def weakNullableLoop : Fin 5 → Node (Fin 5) Unit Unit Unit :=
  fun state => match state.val with
    | 0 => .choice 1 4
    | 1 => .choice 2 3
    | 2 => .jump 0
    | 3 => .consume () 0
    | _ => .accept ()

theorem separate_nullable_choice_preserves_empty_priority :
    run nullableRepetition (asciiProbe 1) 26 (initial 0) = .halt (some ((5, 0), ())) ∧
    run weakNullableLoop (asciiProbe 1) 22 (initial 0) = .halt (some ((4, 1), ())) := by decide

theorem nullable_cycle_finishes_without_match :
    run (fun (_ : Fin 1) => (Node.jump 0 : Node (Fin 1) Unit Unit Unit))
      (asciiProbe 0) 4 (initial 0) = .halt none := by decide

theorem exhaustion_is_not_absence :
    (RunResult.exhausted : RunResult (Fin 1) Unit 0) ≠ .halt none := by decide

theorem dropping_assertion_agreement_changes_selection :
    let graph : Fin 2 → Node (Fin 2) Unit Unit Unit :=
      fun state => if state.val = 0 then .assertion () 1 else .accept ()
    run graph (Probe.mk (fun _ _ => false) (fun _ _ => false) : Probe Unit Unit 0)
      6 (initial 0) = .halt none ∧
    run graph (Probe.mk (fun _ _ => false) (fun _ _ => true) : Probe Unit Unit 0)
      6 (initial 0) = .halt (some ((1, 0), ())) := by decide

#print axioms successor_advances
#print axioms expand_length
#print axioms step_decreases
#print axioms run_sufficient
#print axioms initial_work_bound
#print axioms run_more
#print axioms step_preserves_reachability
#print axioms step_match_sound
#print axioms run_match_sound
#print axioms initial_reachable
#print axioms acceptedTag_map
#print axioms expand_map
#print axioms step_map
#print axioms run_map
#print axioms selected_prefix_is_not_whole_language_membership
#print axioms separate_nullable_choice_preserves_empty_priority
#print axioms nullable_cycle_finishes_without_match
#print axioms exhaustion_is_not_absence
#print axioms dropping_assertion_agreement_changes_selection

end Mettapedia.Computability.RegularLanguages.OrderedGraphSearch
