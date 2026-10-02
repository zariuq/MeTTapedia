import Mettapedia.GSLT.Parsing.ClassAwarePackedForest
import Mettapedia.Algorithms.SharedKBest
import Mathlib.Data.List.Forall2

/-!
# Shared k-best evaluation of class-aware packed storage

A checked topological enumeration turns the existing forest's physical
families into the shared k-best network. Node references become earlier
cache references; terminal references remain constants in the original
family metadata. The source relation below unfolds the finite store directly.
It does not replace parser replay: a storage derivation is a parse only when
the existing `Replays` certificate supplies that additional qualification.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwarePackedForestKBest

open ClassAwarePackedForest
open Mettapedia.Algorithms

def nodeChildren (children : List ChildRef) : List NodeKey :=
  children.filterMap fun child => match child with
    | .node key => some key
    | .terminal _ _ _ => none

/-- Repeated node references remain repeated; terminal information remains
in `Family.children` and is not itself a nondeterministic child cache. -/
def childRanks (keys : List NodeKey) (family : Family) : List Nat :=
  (nodeChildren family.children).map (fun key => keys.idxOf key)

/-- This finite check rules out missing references, cyclic dependencies and
duplicate physical stored families. It does not check parser validity. -/
def ValidTopology (forest : Forest) (keys : List NodeKey) : Prop :=
  keys.Nodup ∧ forest.families.Nodup ∧
    (∀ root ∈ forest.roots, root ∈ keys) ∧
    (∀ family ∈ forest.families, family.parent ∈ keys ∧
      ∀ child ∈ nodeChildren family.children, keys.idxOf child < keys.idxOf family.parent)

instance (forest : Forest) (keys : List NodeKey) : Decidable (ValidTopology forest keys) :=
  inferInstanceAs (Decidable (keys.Nodup ∧ forest.families.Nodup ∧
    (∀ root ∈ forest.roots, root ∈ keys) ∧
    (∀ family ∈ forest.families, family.parent ∈ keys ∧
      ∀ child ∈ nodeChildren family.children, keys.idxOf child < keys.idxOf family.parent)))

def validate (forest : Forest) (keys : List NodeKey) : Bool := decide (ValidTopology forest keys)

theorem validate_iff (forest : Forest) (keys : List NodeKey) :
    validate forest keys = true ↔ ValidTopology forest keys := by simp [validate]

theorem no_self_child (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (family : Family) (present : family ∈ forest.families) :
    family.parent ∉ nodeChildren family.children := by
  intro self
  exact Nat.lt_irrefl _ ((valid.2.2.2 family present).2 family.parent self)

theorem no_two_cycle (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (first second : Family)
    (firstPresent : first ∈ forest.families) (secondPresent : second ∈ forest.families)
    (forward : second.parent ∈ nodeChildren first.children) :
    first.parent ∉ nodeChildren second.children := by
  intro backward
  have firstBound := (valid.2.2.2 first firstPresent).2 second.parent forward
  have secondBound := (valid.2.2.2 second secondPresent).2 first.parent backward
  omega

def familiesAt (forest : Forest) (key : NodeKey) : List Family :=
  forest.families.filter (fun family => family.parent == key)

theorem family_at_iff (forest : Forest) (key : NodeKey) (family : Family) :
    family ∈ familiesAt forest key ↔ family ∈ forest.families ∧ family.parent = key := by
  simp [familiesAt]

def physicalFamily (forest : Forest) (keys : List NodeKey) (owner : Fin keys.length)
    (row : Fin (familiesAt forest keys[owner]).length) : Family :=
  (familiesAt forest keys[owner])[row]

theorem physical_family_present (forest : Forest) (keys : List NodeKey)
    (owner : Fin keys.length) (row : Fin (familiesAt forest keys[owner]).length) :
    physicalFamily forest keys owner row ∈ forest.families ∧
      (physicalFamily forest keys owner row).parent = keys[owner] :=
  (family_at_iff forest keys[owner] _).mp (List.getElem_mem _)

theorem child_before (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (owner : Fin keys.length)
    (row : Fin (familiesAt forest keys[owner]).length) (child : NodeKey)
    (member : child ∈ nodeChildren (physicalFamily forest keys owner row).children) :
    keys.idxOf child < owner.val := by
  obtain ⟨present, parent⟩ := physical_family_present forest keys owner row
  have earlier := (valid.2.2.2 _ present).2 child member
  have rank : keys.idxOf keys[owner] = owner.val := valid.1.idxOf_getElem owner.val owner.isLt
  rw [parent, rank] at earlier
  exact earlier

def compileFamily (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat)
    (owner : Fin keys.length) (row : Fin (familiesAt forest keys[owner]).length) :
    SharedKBest.Family owner.val where
  charge := charge (physicalFamily forest keys owner row)
  children := (nodeChildren (physicalFamily forest keys owner row).children).attach.map
    (fun child => ⟨keys.idxOf child.val, child_before forest keys valid owner row child.val child.property⟩)

theorem compile_child_ranks (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat)
    (owner : Fin keys.length) (row : Fin (familiesAt forest keys[owner]).length) :
    (compileFamily forest keys valid charge owner row).children.map Fin.val =
      childRanks keys (physicalFamily forest keys owner row) := by
  simp [compileFamily, childRanks, List.map_map, Function.comp_def]

def compiledFamilies (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat) (owner : Fin keys.length) :
    List (SharedKBest.Family owner.val) :=
  List.ofFn (compileFamily forest keys valid charge owner)

def compilePrefix (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat) :
    (count : Nat) → count ≤ keys.length → SharedKBest.Network count
  | 0, _ => .empty
  | count + 1, bound =>
      .append (compilePrefix forest keys valid charge count (by omega))
        (compiledFamilies forest keys valid charge ⟨count, by omega⟩)

def compile (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat) :
    SharedKBest.Network keys.length :=
  compilePrefix forest keys valid charge keys.length le_rfl

/-- Independent finite storage unfolding. A physical parent-family choice
requires ordered child unfoldings at exactly its stored node references.
Terminal constants and physical ProductionRef remain recoverable from that
same family; no network successor or solver premise appears here. -/
inductive Unfolding (forest : Forest) (keys : List NodeKey) (charge : Family → Nat) :
    Nat → SharedKBest.Derivation → Prop where
  | family (owner : Fin keys.length)
      (row : Fin (familiesAt forest keys[owner]).length) (children : List SharedKBest.Derivation)
      (childProofs : List.Forall₂ (Unfolding forest keys charge)
        (childRanks keys (physicalFamily forest keys owner row)) children) :
      Unfolding forest keys charge owner.val
        (.node owner.val row.val (charge (physicalFamily forest keys owner row)) children)

private theorem alternatives_index {previous : Nat}
    (childSource : Fin previous → SharedKBest.Derivation → Prop)
    (owner start : Nat) (families : List (SharedKBest.Family previous))
    (derivation : SharedKBest.Derivation) :
    SharedKBest.AlternativesAllow childSource owner start families derivation ↔
      ∃ row : Fin families.length,
        SharedKBest.FamilyAllows childSource owner (start + row.val) families[row] derivation := by
  induction families generalizing start with
  | nil =>
      constructor
      · intro impossible; exact False.elim impossible
      · rintro ⟨row, _⟩; exact Fin.elim0 row
  | cons first rest ih =>
      constructor
      · intro allowed
        rcases allowed with head | tail
        · exact ⟨⟨0, by simp⟩, by simpa using head⟩
        · obtain ⟨row, proof⟩ := (ih (start + 1)).mp tail
          exact ⟨⟨row.val + 1, by simp⟩, by simpa [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using proof⟩
      · rintro ⟨row, allowed⟩
        cases value : row.val with
        | zero => exact Or.inl (by simpa [value] using allowed)
        | succ index =>
            right
            apply (ih (start + 1)).mpr
            refine ⟨⟨index, by have := row.isLt; simp only [List.length_cons] at this; omega⟩, ?_⟩
            simpa [value, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using allowed

private theorem alternatives_ofFn {previous count : Nat}
    (childSource : Fin previous → SharedKBest.Derivation → Prop)
    (owner : Nat) (family : Fin count → SharedKBest.Family previous)
    (derivation : SharedKBest.Derivation) :
    SharedKBest.AlternativesAllow childSource owner 0 (List.ofFn family) derivation ↔
      ∃ row : Fin count, SharedKBest.FamilyAllows childSource owner row.val (family row) derivation := by
  rw [alternatives_index]
  constructor
  · rintro ⟨row, allowed⟩
    refine ⟨⟨row.val, by simpa using row.isLt⟩, ?_⟩
    simpa only [Fin.getElem_fin, List.getElem_ofFn, Nat.zero_add] using allowed
  · rintro ⟨row, allowed⟩
    refine ⟨⟨row.val, by simp⟩, ?_⟩
    simpa only [Fin.getElem_fin, List.getElem_ofFn, Nat.zero_add] using allowed

private theorem unfolding_cases (forest : Forest) (keys : List NodeKey) (charge : Family → Nat)
    {owner : Nat} {derivation : SharedKBest.Derivation}
    (unfolded : Unfolding forest keys charge owner derivation) :
    ∃ bound : owner < keys.length,
      ∃ row : Fin (familiesAt forest keys[owner]).length,
        ∃ children, List.Forall₂ (Unfolding forest keys charge)
          (childRanks keys (physicalFamily forest keys ⟨owner, bound⟩ row)) children ∧
          derivation = .node owner row.val
            (charge (physicalFamily forest keys ⟨owner, bound⟩ row)) children := by
  cases unfolded with
  | family actual row children childProofs =>
      exact ⟨actual.isLt, row, children, childProofs, rfl⟩

theorem unfolding_iff (forest : Forest) (keys : List NodeKey) (charge : Family → Nat)
    (owner : Fin keys.length) (derivation : SharedKBest.Derivation) :
    Unfolding forest keys charge owner.val derivation ↔
      ∃ row : Fin (familiesAt forest keys[owner]).length,
        ∃ children, List.Forall₂ (Unfolding forest keys charge)
          (childRanks keys (physicalFamily forest keys owner row)) children ∧
          derivation = .node owner.val row.val
            (charge (physicalFamily forest keys owner row)) children := by
  constructor
  · intro unfolded
    obtain ⟨bound, row, children, proofs, same⟩ := unfolding_cases forest keys charge unfolded
    exact ⟨row, children, proofs, same⟩
  · rintro ⟨row, children, childProofs, rfl⟩
    exact .family owner row children childProofs

private theorem children_correspond (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat)
    (owner : Fin keys.length) (row : Fin (familiesAt forest keys[owner]).length)
    (source : Fin owner.val → SharedKBest.Derivation → Prop)
    (correspondence : ∀ index derivation,
      source index derivation ↔ Unfolding forest keys charge index.val derivation)
    (children : List SharedKBest.Derivation) :
    List.Forall₂ source (compileFamily forest keys valid charge owner row).children children ↔
      List.Forall₂ (Unfolding forest keys charge)
        (childRanks keys (physicalFamily forest keys owner row)) children := by
  rw [← compile_child_ranks forest keys valid charge owner row, List.forall₂_map_left_iff]
  constructor
  · exact List.Forall₂.imp (fun index derivation proof =>
      (correspondence index derivation).mp proof)
  · exact List.Forall₂.imp (fun index derivation proof =>
      (correspondence index derivation).mpr proof)

/-- Forward and backward correspondence with independently defined finite
store unfoldings, including physical family position and ordered children. -/
theorem prefix_source_iff (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat)
    (count : Nat) (bound : count ≤ keys.length) (index : Fin count)
    (derivation : SharedKBest.Derivation) :
    SharedKBest.Source (compilePrefix forest keys valid charge count bound) index derivation ↔
      Unfolding forest keys charge index.val derivation := by
  induction count generalizing derivation with
  | zero => exact Fin.elim0 index
  | succ previous ih =>
      simp only [compilePrefix, SharedKBest.Source]
      split
      next earlier => exact ih (by omega) ⟨index.val, earlier⟩ derivation
      next later =>
        have last : index.val = previous := by omega
        rw [last]
        unfold compiledFamilies
        rw [alternatives_ofFn]
        simp only [SharedKBest.FamilyAllows]
        rw [unfolding_iff forest keys charge ⟨previous, by omega⟩]
        apply exists_congr
        intro row
        apply exists_congr
        intro children
        rw [children_correspond forest keys valid charge ⟨previous, by omega⟩ row
          (SharedKBest.Source (compilePrefix forest keys valid charge previous (by omega)))
          (fun child proof => ih (by omega) child proof)]
        rfl

theorem source_iff (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat)
    (index : Fin keys.length) (derivation : SharedKBest.Derivation) :
    SharedKBest.Source (compile forest keys valid charge) index derivation ↔
      Unfolding forest keys charge index.val derivation :=
  prefix_source_iff forest keys valid charge keys.length le_rfl index derivation

def solve (forest : Forest) (keys : List NodeKey) (valid : ValidTopology forest keys)
    (charge : Family → Nat) (requested : Nat) (index : Fin keys.length) :
    SharedKBest.Certified requested SharedKBest.Derivation SharedKBest.cost
      (Unfolding forest keys charge index.val) :=
  (SharedKBest.solve (compile forest keys valid charge) requested index).relabel
    (source_iff forest keys valid charge index)

theorem solve_correct (forest : Forest) (keys : List NodeKey) (valid : ValidTopology forest keys)
    (charge : Family → Nat) (requested : Nat) (index : Fin keys.length) :
    DerivationPrefix.Correct requested SharedKBest.cost (Unfolding forest keys charge index.val)
      (solve forest keys valid charge requested index).cache.values :=
  (solve forest keys valid charge requested index).correct

/-- A returned prefix shorter than the requested demand exhausts exactly
the finite storage source. Equal costs do not change this statement. -/
theorem shortage_complete (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat) (requested : Nat)
    (index : Fin keys.length)
    (short : (solve forest keys valid charge requested index).cache.values.length < requested)
    (derivation : SharedKBest.Derivation) :
    derivation ∈ (solve forest keys valid charge requested index).cache.values ↔
      Unfolding forest keys charge index.val derivation := by
  have correct := solve_correct forest keys valid charge requested index
  constructor
  · exact correct.sound derivation
  · intro unfolded
    rcases DerivationPrefix.member_or_full requested SharedKBest.cost _ _ correct unfolded with
      present | full
    · exact present
    · omega

/-- The cache identity carries the original owner and physical family row. -/
def ownerOf : SharedKBest.Derivation → Nat
  | .node owner _ _ _ => owner

def metadata (forest : Forest) (keys : List NodeKey) :
    SharedKBest.Derivation → Option Family
  | .node owner row _ _ => do
      let key ← keys[owner]?
      (familiesAt forest key)[row]?

theorem unfolding_owner (forest : Forest) (keys : List NodeKey) (charge : Family → Nat)
    {owner : Nat} {derivation : SharedKBest.Derivation}
    (unfolded : Unfolding forest keys charge owner derivation) :
    ownerOf derivation = owner := by cases unfolded; rfl

theorem physical_family_injective (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (owner : Fin keys.length) :
    Function.Injective (physicalFamily forest keys owner) := by
  intro first second same
  have distinct : (familiesAt forest keys[owner]).Nodup := valid.2.1.filter _
  exact distinct.get_inj_iff.mp same

theorem metadata_family (forest : Forest) (keys : List NodeKey) (charge : Family → Nat)
    (owner : Fin keys.length) (row : Fin (familiesAt forest keys[owner]).length)
    (children : List SharedKBest.Derivation) :
    metadata forest keys (.node owner.val row.val
      (charge (physicalFamily forest keys owner row)) children) =
      some (physicalFamily forest keys owner row) := by
  simp [metadata, physicalFamily, owner.isLt]

theorem unfolding_metadata (forest : Forest) (keys : List NodeKey) (charge : Family → Nat)
    {owner : Nat} {derivation : SharedKBest.Derivation}
    (unfolded : Unfolding forest keys charge owner derivation) :
    ∃ family ∈ forest.families, metadata forest keys derivation = some family := by
  cases unfolded with
  | family owner row children _ =>
      exact ⟨physicalFamily forest keys owner row,
        (physical_family_present forest keys owner row).1,
        metadata_family forest keys charge owner row children⟩

/-- Read terminal constants in place and reconstruct each nonterminal key
from the selected child derivation. Order and repeated child references
survive; any missing or extra child makes reconstruction fail. -/
def restoreChildren (keys : List NodeKey) :
    List ChildRef → List SharedKBest.Derivation → Option (List ChildRef)
  | [], [] => some []
  | .terminal matcher start stop :: rest, children =>
      (.terminal matcher start stop :: ·) <$> restoreChildren keys rest children
  | .node _ :: rest, child :: children => do
      let key ← keys[ownerOf child]?
      let tail ← restoreChildren keys rest children
      pure (.node key :: tail)
  | _, _ => none

theorem restore_children (forest : Forest) (keys : List NodeKey) (charge : Family → Nat)
    (refs : List ChildRef) (children : List SharedKBest.Derivation)
    (present : ∀ key ∈ nodeChildren refs, key ∈ keys)
    (unfolded : List.Forall₂ (Unfolding forest keys charge)
      ((nodeChildren refs).map (fun key => keys.idxOf key)) children) :
    restoreChildren keys refs children = some refs := by
  induction refs generalizing children with
  | nil => cases unfolded; rfl
  | cons first rest ih =>
      cases first with
      | terminal matcher start stop =>
          have tail := ih children (by simpa [nodeChildren] using present) unfolded
          simpa [restoreChildren] using congrArg (Option.map (.terminal matcher start stop :: ·)) tail
      | node key =>
          cases unfolded with
          | cons headProof tailProof =>
              have member := present key (by simp [nodeChildren])
              have tail := ih _ (by
                intro child inside
                apply present child
                change child ∈ key :: nodeChildren rest
                exact List.mem_cons_of_mem _ inside) tailProof
              simp [restoreChildren, unfolding_owner forest keys charge headProof,
                List.getElem?_idxOf member, tail]

theorem metadata_and_children (forest : Forest) (keys : List NodeKey)
    (valid : ValidTopology forest keys) (charge : Family → Nat)
    (owner : Fin keys.length) (row : Fin (familiesAt forest keys[owner]).length)
    (children : List SharedKBest.Derivation)
    (unfolded : List.Forall₂ (Unfolding forest keys charge)
      (childRanks keys (physicalFamily forest keys owner row)) children) :
    metadata forest keys (.node owner.val row.val
      (charge (physicalFamily forest keys owner row)) children) =
        some (physicalFamily forest keys owner row) ∧
      restoreChildren keys (physicalFamily forest keys owner row).children children =
        some (physicalFamily forest keys owner row).children := by
  refine ⟨metadata_family forest keys charge owner row children, ?_⟩
  apply restore_children forest keys charge _ children _ unfolded
  intro key member
  exact List.idxOf_lt_length_iff.mp
    (lt_trans (child_before forest keys valid owner row key member) owner.isLt)

end Mettapedia.GSLT.Parsing.ClassAwarePackedForestKBest
