import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Presentations

/-!
# Decorations of locally presented coalgebras

The state carrier may live in an arbitrarily larger universe than its
branch carriers. All finite branch paths from a state form an explicitly
constructed small graph. Its picture supplies a material behaviour without
choosing a small presentation of the large state carrier.

The branch family and successor operation are the authored coalgebra data.
No representatives, enclosing carrier, or decoration are inputs to the
construction. The theorem does not replace this data by an existential
smallness assertion whose witnesses would have to be selected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.LocallyPresentedCoalgebras

open AccessiblePointedGraph

universe u v w

/-- A coalgebra specifies its small positions and their actual successors. -/
structure Coalgebra (State : Type v) where
  Branch : State → Type u
  next : (state : State) → Branch state → State

variable {State : Type v} (system : Coalgebra.{u, v} State)

/-- Each layer stores small path codes and computes their possibly large
terminal states. No state is stored as part of the small path code. -/
def layer (root : State) : Nat → Σ Codes : Type u, Codes → State
  | 0 => ⟨PUnit, fun _ => root⟩
  | length + 1 =>
    let previous := layer root length
    ⟨Σ code : previous.1, system.Branch (previous.2 code),
      fun extension => system.next (previous.2 extension.1) extension.2⟩

abbrev Path (root : State) (length : Nat) : Type u := (layer system root length).1

abbrev Node (root : State) : Type u := Σ length, Path system root length

def endpoint {root : State} (node : Node system root) : State :=
  (layer system root node.1).2 node.2

def rootNode (root : State) : Node system root := ⟨0, PUnit.unit⟩

def append {root : State} (node : Node system root)
    (branch : system.Branch (endpoint system node)) : Node system root :=
  ⟨node.1 + 1, ⟨node.2, branch⟩⟩

def edge {root : State} (source target : Node system root) : Prop :=
  ∃ branch : system.Branch (endpoint system source), append system source branch = target

@[simp] theorem endpoint_root (root : State) :
    endpoint system (rootNode system root) = root := rfl

@[simp] theorem endpoint_append {root : State} (node : Node system root)
    (branch : system.Branch (endpoint system node)) :
    endpoint system (append system node branch) = system.next (endpoint system node) branch := rfl

theorem path_reachable (root : State) (length : Nat) (path : Path system root length) :
    Relation.ReflTransGen (edge system) (rootNode system root) ⟨length, path⟩ := by
  induction length with
  | zero => cases path; exact .refl
  | succ length earlier =>
    rcases path with ⟨earlierCode, branch⟩
    exact (earlier earlierCode).tail ⟨branch, rfl⟩

/-- All finite paths form a genuine accessible graph in the branch universe. -/
def graph (root : State) : AccessiblePointedGraph.{u} where
  Node := Node system root
  edge := edge system
  point := rootNode system root
  reachable node := path_reachable system root node.1 node.2

/-- The material carrier has the branch bound, independently of state size. -/
def behaviour (state : State) : HSet.{u} := HSet.mk (graph system state)

private theorem occurrence_length (state : State) (occurrence : Occurrence (graph system state)) :
    occurrence.val.1 = 1 := by
  obtain ⟨branch, same⟩ := occurrence.property
  exact (congrArg Sigma.fst same).symm

/-- A root occurrence retains its actual position even when two successors
have the same material value. The position is extracted from the stored
path code, not from a propositional choice of an edge witness. -/
def occurrenceBranch (state : State) (occurrence : Occurrence (graph system state)) :
    system.Branch state :=
  ((occurrence_length system state occurrence) ▸ occurrence.val.2).2

def branchOccurrence (state : State) (branch : system.Branch state) :
    Occurrence (graph system state) :=
  ⟨append system (rootNode system state) branch, ⟨branch, rfl⟩⟩

theorem branchOccurrence_occurrenceBranch (state : State)
    (occurrence : Occurrence (graph system state)) :
    branchOccurrence system state (occurrenceBranch system state occurrence) = occurrence := by
  rcases occurrence with ⟨⟨length, path⟩, available⟩
  have sameLength := occurrence_length system state ⟨⟨length, path⟩, available⟩
  cases sameLength
  rcases path with ⟨earlierCode, branch⟩
  cases earlierCode
  rfl

theorem occurrenceBranch_branchOccurrence (state : State) (branch : system.Branch state) :
    occurrenceBranch system state (branchOccurrence system state branch) = branch := rfl

def occurrenceEquiv (state : State) : Occurrence (graph system state) ≃ system.Branch state where
  toFun := occurrenceBranch system state
  invFun := branchOccurrence system state
  left_inv := branchOccurrence_occurrenceBranch system state
  right_inv := occurrenceBranch_branchOccurrence system state

/-- The relational view forgets repeated positions with the same successor. -/
def transition (source target : State) : Prop :=
  ∃ branch : system.Branch source, system.next source branch = target

/-- Path evaluation preserves and lifts exactly the authored successors. -/
theorem endpoint_bounded (root : State) :
    IsBoundedMorphism (graph system root).edge (transition system) (endpoint system) where
  map source target step := by
    obtain ⟨branch, rfl⟩ := step
    exact ⟨branch, rfl⟩
  lift source target step := by
    obtain ⟨branch, rfl⟩ := step
    exact ⟨append system source branch, ⟨branch, rfl⟩, rfl⟩

/-- The small graph at any path has the same behaviour as a fresh graph at
its terminal state. -/
theorem decorate_endpoint (root : State) (node : (graph system root).Node) :
    HSet.decorate (graph system root).edge node = behaviour system (endpoint system node) := by
  rw [behaviour, HSet.mk_eq_decorate]
  apply HSet.decorate_eq_of_bisimilar
  exact (endpoint_bounded system root).bisimilar_of_eq
    (endpoint_bounded system (endpoint system node)) rfl

theorem mem_behaviour (state : State) (value : HSet.{u}) :
    value ∈ behaviour system state ↔
      ∃ branch : system.Branch state, behaviour system (system.next state branch) = value := by
  rw [behaviour, HSet.mk_eq_decorate]
  constructor
  · intro member
    obtain ⟨child, ⟨branch, rfl⟩, same⟩ := HSet.mem_decorate.mp member
    exact ⟨branch, (decorate_endpoint system state _).symm.trans same⟩
  · rintro ⟨branch, same⟩
    exact HSet.mem_decorate.mpr
      ⟨append system (rootNode system state) branch, ⟨branch, rfl⟩,
        (decorate_endpoint system state _).trans same⟩

/-- The usual decoration equation, allowing a larger state universe. -/
def IsDecoration (decoration : State → HSet.{u}) : Prop :=
  ∀ state value, value ∈ decoration state ↔
    ∃ branch : system.Branch state, decoration (system.next state branch) = value

theorem behaviour_isDecoration : IsDecoration system (behaviour system) :=
  mem_behaviour system

/-- Uniqueness uses strong material extensionality, not selection from a
propositional existence statement. -/
theorem IsDecoration.eq_behaviour {decoration : State → HSet.{u}}
    (lawful : IsDecoration system decoration) : decoration = behaviour system := by
  funext state
  refine HSet.eq_of_isBisimulation
    (R := fun first second => ∃ state, decoration state = first ∧ behaviour system state = second)
    ?_ ⟨state, rfl, rfl⟩
  rintro first second ⟨state, rfl, rfl⟩
  constructor
  · intro child member
    obtain ⟨branch, rfl⟩ := (lawful state child).mp member
    exact ⟨behaviour system (system.next state branch),
      (mem_behaviour system state _).mpr ⟨branch, rfl⟩,
      system.next state branch, rfl, rfl⟩
  · intro child member
    obtain ⟨branch, rfl⟩ := (mem_behaviour system state child).mp member
    exact ⟨decoration (system.next state branch),
      (lawful state _).mpr ⟨branch, rfl⟩, system.next state branch, rfl, rfl⟩

theorem existsUnique_decoration :
    ∃! decoration : State → HSet.{u}, IsDecoration system decoration :=
  ⟨behaviour system, behaviour_isDecoration system, fun _ lawful => lawful.eq_behaviour⟩

theorem behaviour_bounded :
    IsBoundedMorphism (transition system) HSet.membershipGraph (behaviour system) where
  map state target step := by
    obtain ⟨branch, rfl⟩ := step
    exact (mem_behaviour system state _).mpr ⟨branch, rfl⟩
  lift state value member := by
    obtain ⟨branch, same⟩ := (mem_behaviour system state value).mp member
    exact ⟨system.next state branch, ⟨branch, rfl⟩, same⟩

/-- The constructed readout identifies exactly ordinary relational
bisimilarity, regardless of the relative state and branch universes. -/
theorem behaviour_eq_iff {Other : Type w} (other : Coalgebra.{u, w} Other)
    (first : State) (second : Other) :
    behaviour system first = behaviour other second ↔
      Bisimilar (transition system) (transition other) first second := by
  constructor
  · intro same
    exact (behaviour_bounded system).bisimilar_of_eq (behaviour_bounded other) same
  · intro related
    rw [behaviour, behaviour, HSet.mk_eq_decorate, HSet.mk_eq_decorate]
    apply HSet.decorate_eq_of_bisimilar
    exact ((endpoint_bounded system first).bisimilar (graph system first).point).trans
      (related.trans ((endpoint_bounded other second).bisimilar (graph other second).point).symm)

/-- A bounded change of operational presentation preserves its value. -/
theorem behaviour_natural {Other : Type w} (other : Coalgebra.{u, w} Other)
    (map : State → Other)
    (lawful : IsBoundedMorphism (transition system) (transition other) map) (state : State) :
    behaviour other (map state) = behaviour system state :=
  ((behaviour_eq_iff system other state (map state)).mpr (lawful.bisimilar state)).symm

section MembershipModel

/-- Bare material values supply their actual member positions at the raised
bound. No presentation of each value or member needs to be selected. -/
def membershipSystem : Coalgebra.{u + 1, u + 1} HSet.{u} where
  Branch value := {member : HSet.{u} // member ∈ value}
  next _ member := member.val

theorem lift_isDecoration : IsDecoration membershipSystem.{u} HSet.lift := by
  intro state value
  exact HSet.mem_lift_iff.trans
    ⟨fun ⟨member, available, same⟩ => ⟨⟨member, available⟩, same⟩,
      fun ⟨member, same⟩ => ⟨member.val, member.property, same⟩⟩

/-- Reconstructing the membership coalgebra produces the proved cumulative
embedding, not a same-level selector for graph presentations. -/
theorem membership_behaviour : behaviour membershipSystem.{u} = HSet.lift :=
  lift_isDecoration.eq_behaviour.symm

theorem membership_behaviour_injective :
    Function.Injective (behaviour membershipSystem.{u}) := by
  rw [membership_behaviour]
  exact HSet.lift_injective

theorem membership_quine_survives :
    behaviour membershipSystem HSet.quineAtom.{u} = HSet.quineAtom.{u + 1} := by
  rw [membership_behaviour, HSet.lift_quineAtom]

end MembershipModel

section Controls

/-- All small types, a larger state carrier, supply arbitrarily large
branching families. Every branch returns to its own state. -/
def typeLoopSystem : Coalgebra.{u, u + 1} (Type u) where
  Branch carrier := carrier
  next carrier _ := carrier

theorem typeLoop_empty :
    behaviour typeLoopSystem (ULift.{u, 0} Empty) = (∅ : HSet.{u}) := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  obtain ⟨branch, _⟩ := (mem_behaviour typeLoopSystem _ value).mp member
  exact branch.down.elim

theorem typeLoop_quine (carrier : Type u) (inhabited : Nonempty carrier) :
    behaviour typeLoopSystem carrier = HSet.quineAtom.{u} := by
  apply HSet.eq_quineAtom_of_eq_singleton
  apply HSet.ext
  intro value
  rw [mem_behaviour, HSet.mem_singleton]
  constructor
  · rintro ⟨_, same⟩
    exact same.symm
  · intro same
    obtain ⟨branch⟩ := inhabited
    exact ⟨branch, same.symm⟩

theorem duplicate_occurrences_retained :
    ¬ Subsingleton (Occurrence (graph typeLoopSystem (ULift.{u, 0} Bool))) := by
  intro collapsed
  have same : (ULift.up true : ULift.{u, 0} Bool) = ULift.up false :=
    (occurrenceEquiv typeLoopSystem _).symm.injective (collapsed.allEq _ _)
  exact Bool.noConfusion (congrArg ULift.down same)

theorem duplicate_values_identified :
    behaviour typeLoopSystem (ULift.{u, 0} Bool) =
      behaviour typeLoopSystem (ULift.{u, 0} PUnit) :=
  (typeLoop_quine _ ⟨ULift.up true⟩).trans (typeLoop_quine _ ⟨ULift.up PUnit.unit⟩).symm

def infinite_positions_retained :
    Occurrence (graph typeLoopSystem (ULift.{u, 0} Nat)) ≃ ULift.{u, 0} Nat :=
  occurrenceEquiv typeLoopSystem _

theorem empty_and_infinite_distinguished :
    behaviour typeLoopSystem (ULift.{u, 0} Empty) ≠
      behaviour typeLoopSystem (ULift.{u, 0} Nat) := by
  rw [typeLoop_empty, typeLoop_quine _ ⟨ULift.up 0⟩]
  exact HSet.empty_ne_quineAtom

end Controls

#print axioms graph
#print axioms behaviour
#print axioms mem_behaviour
#print axioms existsUnique_decoration
#print axioms behaviour_eq_iff
#print axioms membership_behaviour
#print axioms occurrenceEquiv
#print axioms duplicate_values_identified
#print axioms infinite_positions_retained

end Mettapedia.TypeTheory.MaterialSets.Hypersets.LocallyPresentedCoalgebras
