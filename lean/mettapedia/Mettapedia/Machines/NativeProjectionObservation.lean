import Mettapedia.Machines.DemandSummary

/-!
# Shared support observation before native projection

The reference asks whether a labelled node is reachable. The implementation
folds the graph with the existing memoized metadata owner. Nested folds select
pattern variables absent from every effect. This is read-only metadata: it
neither merges branch bindings nor changes answer multiplicity or effects.

The final owner also distinguishes a complete observation from refusal. An
unavailable read does not establish a negative program fact. Native pruning
flags, predicate allowances, allocation and pointer correspondence remain
separate C obligations; the bounds below count metadata combinations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeProjectionObservation

open DemandSummary

universe u
variable {Label : Type u}

def combine (predicate : Label → Bool) (label : Label) (children : List Bool) : Bool :=
  predicate label || children.any id

def source (graph : Graph Label) (predicate : Label → Bool) (root : Nat) : Prop :=
  ∃ node ∈ reachable graph root, predicate (graph.label node) = true

def inspect (graph : Graph Label) (predicate : Label → Bool) (root : Nat) : Bool :=
  (demand graph (combine predicate) root (fun _ => none)).value

theorem eager_source (graph : Graph Label) (predicate : Label → Bool) (root : Nat) :
    eager graph (combine predicate) root = true ↔ source graph predicate root := by
  induction root using Nat.strong_induction_on with
  | h root ih =>
    rw [eager, combine]
    constructor
    · intro found
      rcases Bool.or_eq_true_iff.mp found with here | later
      · refine ⟨root, ?_, here⟩
        rw [reachable]
        exact Finset.mem_insert_self _ _
      · obtain ⟨answer, member, yes⟩ := List.any_eq_true.mp later
        obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
        obtain ⟨node, reachableChild, observed⟩ :=
          (ih child.val child.isLt).mp yes
        refine ⟨node, ?_, observed⟩
        rw [reachable]
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨child, List.mem_toFinset.mpr childMember, reachableChild⟩)
    · rintro ⟨node, member, observed⟩
      rw [reachable] at member
      rcases Finset.mem_insert.mp member with same | childMember
      · exact Bool.or_eq_true_iff.mpr (Or.inl (same ▸ observed))
      · obtain ⟨child, present, underChild⟩ := Finset.mem_biUnion.mp childMember
        apply Bool.or_eq_true_iff.mpr
        right
        apply List.any_eq_true.mpr
        exact ⟨eager graph (combine predicate) child.val,
          List.mem_map.mpr ⟨child, List.mem_toFinset.mp present, rfl⟩,
          (ih child.val child.isLt).mpr ⟨node, underChild, observed⟩⟩

theorem inspect_source (graph : Graph Label) (predicate : Label → Bool) (root : Nat) :
    inspect graph predicate root = true ↔ source graph predicate root := by
  rw [inspect, demand_exact graph (combine predicate) root _
    (empty_sound graph (combine predicate))]
  exact eager_source graph predicate root

theorem combinations_bounded (graph : Graph Label) (predicate : Label → Bool) (root : Nat) :
    (demand graph (combine predicate) root (fun _ => none)).computed.length ≤
      (reachable graph root).card := by
  simpa using demand_combinations_le_uncached_reachable graph (combine predicate)
    root (fun _ => none) (empty_sound graph (combine predicate))

variable {Variable : Type u} [DecidableEq Variable]

def variablePresent (key : Variable) (label : Option Variable) : Bool :=
  decide (label = some key)

def unread (graph : Graph (Option Variable)) (effects : List Nat) : Option Variable → Bool
  | none => false
  | some key => effects.all fun root => !(inspect graph (variablePresent key) root)

def projects (graph : Graph (Option Variable)) (patterns effects : List Nat) : Bool :=
  patterns.any fun root => inspect graph (unread graph effects) root

def sourceProjects (graph : Graph (Option Variable)) (patterns effects : List Nat) : Prop :=
  ∃ root ∈ patterns, ∃ node ∈ reachable graph root, ∃ key,
    graph.label node = some key ∧
      ∀ effect ∈ effects, ¬source graph (variablePresent key) effect

theorem projection_refines (graph : Graph (Option Variable)) (patterns effects : List Nat) :
    projects graph patterns effects = true ↔ sourceProjects graph patterns effects := by
  simp only [projects, List.any_eq_true, inspect_source, source, sourceProjects]
  constructor
  · rintro ⟨root, present, node, member, unused⟩
    cases label : graph.label node with
    | none => simp [unread, label] at unused
    | some key =>
      refine ⟨root, present, node, member, key, label, ?_⟩
      simp only [label, unread, List.all_eq_true] at unused
      intro effect included observed
      have notFound := unused effect included
      have found := (inspect_source graph (variablePresent key) effect).mpr observed
      simp [found] at notFound
  · rintro ⟨root, present, node, member, key, label, unused⟩
    refine ⟨root, present, node, member, ?_⟩
    simp only [label, unread, List.all_eq_true]
    intro effect included
    have notFound : inspect graph (variablePresent key) effect = false := by
      cases found : inspect graph (variablePresent key) effect with
      | false => rfl
      | true => exact False.elim (unused effect included
          ((inspect_source graph (variablePresent key) effect).mp found))
    simp [notFound]

/-- Stop at the first incomplete observation, rather than using its false
payload as evidence of absence. A complete positive prefix needs no suffix. -/
def accept : List (Option Bool) → Bool
  | [] => false
  | none :: _ => false
  | some true :: _ => true
  | some false :: later => accept later

theorem complete_observations (answers : List Bool) :
    accept (answers.map some) = answers.any id := by
  induction answers with
  | nil => rfl
  | cons first later ih => cases first <;> simp [accept, ih]

theorem incomplete_prefix_refuses (later : List (Option Bool)) :
    accept (none :: later) = false := rfl

theorem completed_positive_needs_no_suffix (later : List (Option Bool)) :
    accept (some true :: later) = true := rfl

namespace Controls

def shared : Graph (Option Nat) where
  label := fun n => if n = 0 then some 7 else none
  children := fun n => match n with
    | 0 => []
    | n + 1 => [⟨n, Nat.lt_succ_self n⟩, ⟨n, Nat.lt_succ_self n⟩]

theorem sharing_preserves_presence : inspect shared (variablePresent 7) 40 = true := by
  decide +kernel

theorem sharing_does_not_invent_variables : inspect shared (variablePresent 8) 40 = false := by
  decide +kernel

def disjoint : Graph (Option Nat) where
  label := fun n => if n = 0 then some 7 else none
  children := fun _ => []

theorem refusal_is_not_a_negative_program_fact :
    projects disjoint [0] [1] = true ∧ accept [none] = false ∧ accept [some true] = true := by
  decide +kernel

end Controls

end Mettapedia.Machines.NativeProjectionObservation

#print axioms Mettapedia.Machines.NativeProjectionObservation.eager_source
#print axioms Mettapedia.Machines.NativeProjectionObservation.inspect_source
#print axioms Mettapedia.Machines.NativeProjectionObservation.combinations_bounded
#print axioms Mettapedia.Machines.NativeProjectionObservation.projection_refines
#print axioms Mettapedia.Machines.NativeProjectionObservation.complete_observations
#print axioms Mettapedia.Machines.NativeProjectionObservation.incomplete_prefix_refuses
#print axioms Mettapedia.Machines.NativeProjectionObservation.completed_positive_needs_no_suffix
#print axioms Mettapedia.Machines.NativeProjectionObservation.Controls.sharing_preserves_presence
#print axioms Mettapedia.Machines.NativeProjectionObservation.Controls.sharing_does_not_invent_variables
#print axioms Mettapedia.Machines.NativeProjectionObservation.Controls.refusal_is_not_a_negative_program_fact
