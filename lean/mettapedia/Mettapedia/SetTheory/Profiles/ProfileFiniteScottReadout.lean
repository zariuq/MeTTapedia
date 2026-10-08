import Mettapedia.TypeTheory.MaterialSets.Hypersets.UnfoldingIdentityComparison
import Mettapedia.SetTheory.AntiFoundation.Graphs
import Mettapedia.SetTheory.AntiFoundation.Core
import Mettapedia.SetTheory.AntiFoundation.Denotations
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutPresentations
import Mettapedia.SetTheory.Profiles.ProfileConstructiveFiniteFunctions

/-!
# Finite raw unfolding observations and conditional Scott comparisons

An adjacency successor is one target vertex satisfying the edge relation.
Local bijections therefore count distinct successors, including successors
with equal material values. Repeated entries naming the same target in an
authored row are separate provenance positions, not extra adjacency edges.

The comparison concerns full rooted unfolding trees of raw adjacency graphs.
It gives Scott root equality on Scott-extensional graphs. An arbitrary raw
graph may have duplicate vertices which extensional material equality must
identify; its raw unfolding readout is then a different observation. This
module does not construct a Scott anti-foundation universe or provide native
Scott material equality.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileFiniteScottReadout

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open UnfoldingIdentityComparison ConstructiveFinite

universe u

abbrev Child {α : Type u} (edge : α → α → Prop) (source : α) :=
  {target : α // edge source target}

section Local

variable {α β : Type u} {left : α → α → Prop} {right : β → β → Prop}
variable {relation : α → β → Prop}

/-- The witness is a bijection of actual successor types, together with
the matching of their endpoints. -/
structure ChildMatching (first : α) (second : β) where
  children : Child left first ≃ Child right second
  related : ∀ child, relation child.val (children child).val

theorem ChildMatching.related_back {first : α} {second : β}
    (matching : ChildMatching (left := left) (right := right) (relation := relation) first second)
    (child : Child right second) :
    relation (matching.children.symm child).val child.val := by
  simpa only [Equiv.apply_symm_apply] using
    matching.related (matching.children.symm child)

abbrev Strategy := ∀ {first second}, relation first second →
  ChildMatching (left := left) (right := right) (relation := relation) first second

def forwardExtend
    (strategy : Strategy (left := left) (right := right) (relation := relation))
    {source target : α} {second : β}
    (before : {node : PathNode right second // relation source node.1})
    (step : left source target) :
    {node : PathNode right second // relation target node.1} :=
  let matching := strategy before.property
  let reply := matching.children ⟨target, step⟩
  ⟨⟨reply.val, .snoc before.val.2 reply.property⟩, matching.related ⟨target, step⟩⟩

def backwardExtend
    (strategy : Strategy (left := left) (right := right) (relation := relation))
    {source target : β} {first : α}
    (before : {node : PathNode left first // relation node.1 source})
    (step : right source target) :
    {node : PathNode left first // relation node.1 target} :=
  let matching := strategy before.property
  let reply := matching.children.symm ⟨target, step⟩
  ⟨⟨reply.val, .snoc before.val.2 reply.property⟩,
    matching.related_back ⟨target, step⟩⟩

def forwardTrace (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second) :
    {target : α} → Path left first target →
      {node : PathNode right second // relation target node.1}
  | _, .nil => ⟨⟨second, .nil⟩, related⟩
  | _, .snoc path step => forwardExtend strategy (forwardTrace strategy related path) step

def backwardTrace (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second) :
    {target : β} → Path right second target →
      {node : PathNode left first // relation node.1 target}
  | _, .nil => ⟨⟨first, .nil⟩, related⟩
  | _, .snoc path step => backwardExtend strategy (backwardTrace strategy related path) step

def forwardNode (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second)
    (node : PathNode left first) : PathNode right second :=
  (forwardTrace strategy related node.2).val

def backwardNode (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second)
    (node : PathNode right second) : PathNode left first :=
  (backwardTrace strategy related node.2).val

theorem backward_forward_trace
    (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second)
    {target : α} (path : Path left first target) :
    backwardTrace strategy related (forwardTrace strategy related path).val.2 =
      ⟨⟨target, path⟩, (forwardTrace strategy related path).property⟩ := by
  induction path with
  | nil => rfl
  | @snoc source target path step previous =>
    change backwardExtend strategy
      (backwardTrace strategy related (forwardTrace strategy related path).val.2)
      ((strategy (forwardTrace strategy related path).property).children
        ⟨target, step⟩).property = _
    rw [previous]
    apply Subtype.ext
    exact congrArg (fun child : Child left source =>
      (⟨child.val, Path.snoc path child.property⟩ : PathNode left first))
      ((strategy (forwardTrace strategy related path).property).children.symm_apply_apply
        ⟨target, step⟩)


theorem backward_forward
    (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second)
    {target : α} (path : Path left first target) :
    backwardNode strategy related (forwardNode strategy related ⟨target, path⟩) =
      ⟨target, path⟩ :=
  congrArg Subtype.val (backward_forward_trace strategy related path)

theorem forward_backward_trace
    (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second)
    {target : β} (path : Path right second target) :
    forwardTrace strategy related (backwardTrace strategy related path).val.2 =
      ⟨⟨target, path⟩, (backwardTrace strategy related path).property⟩ := by
  induction path with
  | nil => rfl
  | @snoc source target path step previous =>
    change forwardExtend strategy
      (forwardTrace strategy related (backwardTrace strategy related path).val.2)
      ((strategy (backwardTrace strategy related path).property).children.symm
        ⟨target, step⟩).property = _
    rw [previous]
    apply Subtype.ext
    exact congrArg (fun child : Child right source =>
      (⟨child.val, Path.snoc path child.property⟩ : PathNode right second))
      ((strategy (backwardTrace strategy related path).property).children.apply_symm_apply
        ⟨target, step⟩)

theorem forward_backward
    (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second)
    {target : β} (path : Path right second target) :
    forwardNode strategy related (backwardNode strategy related ⟨target, path⟩) =
      ⟨target, path⟩ :=
  congrArg Subtype.val (forward_backward_trace strategy related path)

theorem forward_edge
    (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second)
    {source target : PathNode left first} (step : PathEdge left first source target) :
    PathEdge right second (forwardNode strategy related source)
      (forwardNode strategy related target) := by
  cases step with
  | extend path step =>
    exact .extend (forwardTrace strategy related path).val.2
      ((strategy (forwardTrace strategy related path).property).children ⟨_, step⟩).property

theorem backward_edge
    (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second)
    {source target : PathNode right second} (step : PathEdge right second source target) :
    PathEdge left first (backwardNode strategy related source)
      (backwardNode strategy related target) := by
  cases step with
  | extend path step =>
    exact .extend (backwardTrace strategy related path).val.2
      ((strategy (backwardTrace strategy related path).property).children.symm ⟨_, step⟩).property

/-- A specified local bijection at every matched pair transports every
finite path, with a constructed inverse and both edge directions. -/
def unfoldingIso
    (strategy : Strategy (left := left) (right := right) (relation := relation))
    {first : α} {second : β} (related : relation first second) :
    PresentationIso (unfold left first) (unfold right second) where
  nodes := {
    toFun := forwardNode strategy related
    invFun := backwardNode strategy related
    left_inv := fun node => backward_forward strategy related node.2
    right_inv := fun node => forward_backward strategy related node.2 }
  edge_iff source target := by
    constructor
    · exact forward_edge strategy related
    · intro step
      change PathEdge right second (forwardNode strategy related source)
        (forwardNode strategy related target) at step
      have reflected := backward_edge strategy related step
      rcases source with ⟨source, sourcePath⟩
      rcases target with ⟨target, targetPath⟩
      change PathEdge left first ⟨source, sourcePath⟩ ⟨target, targetPath⟩
      simpa only [backward_forward] using reflected
  point := rfl

theorem pathChild_iff {γ : Type u} {edge : γ → γ → Prop} {root : γ}
    (node child : PathNode edge root) :
    PathEdge edge root node child ↔
      ∃ step : edge node.1 child.1, child.2 = Path.snoc node.2 step := by
  constructor
  · intro step
    cases step with
    | extend path available => exact ⟨available, rfl⟩
  · rintro ⟨step, same⟩
    rcases child with ⟨target, path⟩
    change path = Path.snoc node.2 step at same
    rw [same]
    exact .extend node.2 step

/-- Successors at an arbitrary unfolding occurrence, not only its root,
are exactly the adjacency successors of its endpoint. -/
def pathChildEquiv {γ : Type u} (edge : γ → γ → Prop) (root : γ)
    (node : PathNode edge root) :
    Child (PathEdge edge root) node ≃ Child edge node.1 where
  toFun child := ⟨child.val.1, by
    obtain ⟨step, _⟩ := (pathChild_iff node child.val).mp child.property
    exact step⟩
  invFun child := ⟨⟨child.val, .snoc node.2 child.property⟩, .extend node.2 child.property⟩
  left_inv child := by
    apply Subtype.ext
    obtain ⟨step, same⟩ := (pathChild_iff node child.val).mp child.property
    exact Sigma.ext rfl (heq_of_eq same.symm)
  right_inv child := Subtype.ext rfl

def isoChildEquiv {G H : AccessiblePointedGraph.{u}} (iso : PresentationIso G H)
    (node : G.Node) : Child G.edge node ≃ Child H.edge (iso.nodes node) where
  toFun child := ⟨iso.nodes child.val, (iso.edge_iff node child.val).mp child.property⟩
  invFun child := ⟨iso.nodes.symm child.val,
    (iso.edge_iff node _).mpr (by simpa only [Equiv.apply_symm_apply] using child.property)⟩
  left_inv child := Subtype.ext (iso.nodes.symm_apply_apply child.val)
  right_inv child := Subtype.ext (iso.nodes.apply_symm_apply child.val)

def isoRelation {first : α} {second : β}
    (iso : PresentationIso (unfold left first) (unfold right second))
    (source : α) (target : β) : Prop :=
  ∃ node : PathNode left first, node.1 = source ∧ (iso.nodes node).1 = target

theorem isoRelation_root {first : α} {second : β}
    (iso : PresentationIso (unfold left first) (unfold right second)) :
    isoRelation iso first second :=
  ⟨⟨first, .nil⟩, rfl, congrArg Sigma.fst iso.point⟩

/-- A full tree isomorphism supplies a local bijection at every pair of
endpoints it relates. No representative path is chosen globally. -/
theorem isoRelation_matching {first : α} {second : β}
    (iso : PresentationIso (unfold left first) (unfold right second))
    {source : α} {target : β} (related : isoRelation iso source target) :
    Nonempty (ChildMatching (left := left) (right := right)
      (relation := isoRelation iso) source target) := by
  obtain ⟨node, rfl, rfl⟩ := related
  let matching := (pathChildEquiv left first node).symm.trans
    ((isoChildEquiv iso node).trans (pathChildEquiv right second (iso.nodes node)))
  exact ⟨{
    children := matching
    related := fun child => ⟨⟨child.val, .snoc node.2 child.property⟩, rfl, rfl⟩ }⟩

def ChildMatching.selectedChildrenEquiv {first : α} {second : β}
    (matching : ChildMatching (left := left) (right := right) (relation := relation) first second)
    (selectedLeft : α → Prop) (selectedRight : β → Prop)
    (compatible : ∀ {a b}, relation a b → (selectedLeft a ↔ selectedRight b)) :
    {child : Child left first // selectedLeft child.val} ≃
      {child : Child right second // selectedRight child.val} :=
  matching.children.subtypeEquiv (fun child => compatible (matching.related child))


end Local

section Finite

variable {α β : Type u}
variable [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]
variable (left : α → α → Prop) (right : β → β → Prop)
variable [DecidableRel left] [DecidableRel right]

abbrev ChildMaps (first : α) (second : β) :=
  (Child left first → Child right second) × (Child right second → Child left first)

def ValidMaps (table : List (α × β)) (first : α) (second : β)
    (maps : ChildMaps left right first second) : Prop :=
  (∀ child, maps.2 (maps.1 child) = child) ∧
  (∀ child, maps.1 (maps.2 child) = child) ∧
  ∀ child, (child.val, (maps.1 child).val) ∈ table

instance validMapsDecidable (table : List (α × β)) (first : α) (second : β)
    (maps : ChildMaps left right first second) :
    Decidable (ValidMaps left right table first second maps) := by
  unfold ValidMaps
  infer_instance

/-- Both maps and their inverse laws are enumerated over finite successor
types. The Boolean algorithm needs no choice of an inverse function. -/
def Matches (table : List (α × β)) (first : α) (second : β) : Prop :=
  ∃ maps : ChildMaps left right first second, ValidMaps left right table first second maps

instance matchesDecidable (table : List (α × β)) (first : α) (second : β) :
    Decidable (Matches left right table first second) := by
  unfold Matches
  exact inverseExistsDecidable (ValidMaps left right table first second)

omit [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]
  [DecidableRel left] [DecidableRel right] in
theorem matches_of_matching (table : List (α × β)) {first : α} {second : β}
    (matching : ChildMatching (left := left) (right := right)
      (relation := fun a b => (a, b) ∈ table) first second) :
    Matches left right table first second :=
  ⟨⟨matching.children, matching.children.symm⟩,
    matching.children.symm_apply_apply, matching.children.apply_symm_apply, matching.related⟩

omit [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]
  [DecidableRel left] [DecidableRel right] in
theorem matching_of_matches (table : List (α × β)) {first : α} {second : β}
    (available : Matches left right table first second) :
    Nonempty (ChildMatching (left := left) (right := right)
      (relation := fun a b => (a, b) ∈ table) first second) := by
  obtain ⟨maps, leftInverse, rightInverse, matched⟩ := available
  exact ⟨{ children := ⟨maps.1, maps.2, leftInverse, rightInverse⟩, related := matched }⟩

omit [Enumeration α] [Enumeration β] [DecidableEq α] [DecidableEq β]
  [DecidableRel left] [DecidableRel right] in
theorem matches_mono {firstTable secondTable : List (α × β)}
    (subset : firstTable ⊆ secondTable) {first : α} {second : β}
    (available : Matches left right firstTable first second) :
    Matches left right secondTable first second := by
  obtain ⟨maps, leftInverse, rightInverse, matched⟩ := available
  exact ⟨maps, leftInverse, rightInverse, fun child => subset (matched child)⟩

def refine (table : List (α × β)) : List (α × β) :=
  table.filter (fun pair => decide (Matches left right table pair.1 pair.2))

theorem mem_refine (table : List (α × β)) (first : α) (second : β) :
    (first, second) ∈ refine left right table ↔
      (first, second) ∈ table ∧ Matches left right table first second :=
  by simp only [refine, List.mem_filter, decide_eq_true_eq]

theorem refine_sublist (table : List (α × β)) : List.Sublist (refine left right table) table :=
  List.filter_sublist

theorem refine_subset (table : List (α × β)) : refine left right table ⊆ table :=
  (refine_sublist left right table).subset

def rounds : Nat → List (α × β)
  | 0 => pairElements
  | count + 1 => refine left right (rounds count)

theorem rounds_succ_subset (count : Nat) :
    rounds left right (count + 1) ⊆ rounds left right count :=
  refine_subset left right _

theorem unequal_rounds_card (count : Nat)
    (changes : rounds left right (count + 1) ≠ rounds left right count) :
    (rounds left right (count + 1)).length < (rounds left right count).length := by
  exact length_lt_of_sublist_ne (refine_sublist left right _) changes

theorem strict_rounds_card_bound (count : Nat)
    (changes : rounds left right (count + 1) ≠ rounds left right count) :
    (rounds left right (count + 1)).length + (count + 1) ≤ size (α := α) * size (α := β) := by
  induction count with
  | zero =>
    have decreases := unequal_rounds_card left right 0 changes
    simpa only [rounds, pair_length, Nat.succ_eq_add_one] using Nat.succ_le_of_lt decreases
  | succ count previous =>
    have earlier : rounds left right (count + 1) ≠ rounds left right count := by
      intro same
      apply changes
      exact congrArg (refine left right) same
    have bound := previous earlier
    have decreases := unequal_rounds_card left right (count + 1) changes
    omega

/-- A bound for comparisons across two carriers. It counts candidate
pairs, and makes no optimal per-graph depth claim. -/
theorem rounds_stabilize :
    rounds left right (size (α := α) * size (α := β) + 1) =
      rounds left right (size (α := α) * size (α := β)) := by
  by_cases same : rounds left right (size (α := α) * size (α := β) + 1) =
      rounds left right (size (α := α) * size (α := β))
  · exact same
  · have impossible := strict_rounds_card_bound left right (size (α := α) * size (α := β)) same
    omega

def stable : List (α × β) := rounds left right (size (α := α) * size (α := β))

theorem stable_fixed : refine left right (stable left right) = stable left right :=
  rounds_stabilize left right

theorem matching_in_rounds {relation : α → β → Prop}
    (matching : ∀ {first second}, relation first second →
      Nonempty (ChildMatching (left := left) (right := right) (relation := relation) first second))
    (count : Nat) {first : α} {second : β} (related : relation first second) :
    (first, second) ∈ rounds left right count := by
  induction count generalizing first second with
  | zero => exact pair_complete first second
  | succ count previous =>
    apply (mem_refine left right _ _ _).mpr
    obtain ⟨children, paired⟩ := matching related
    exact ⟨previous related,
      matches_of_matching left right _ ⟨children, fun child => previous (paired child)⟩⟩

theorem stable_matches {first : α} {second : β}
    (related : (first, second) ∈ stable left right) :
    Matches left right (stable left right) first second := by
  have retained : (first, second) ∈ refine left right (stable left right) :=
    (stable_fixed left right).symm ▸ related
  exact ((mem_refine left right _ first second).mp retained).2

/-- The explicit candidate list supplies actual mutually inverse maps. -/
def stableStrategy :
    Strategy (left := left) (right := right)
      (relation := fun first second => (first, second) ∈ stable left right) := by
  intro first second related
  let selected := inverseWitness (ValidMaps left right (stable left right) first second)
    (stable_matches left right related)
  exact {
    children := {
      toFun := selected.val.1
      invFun := selected.val.2
      left_inv := selected.property.1
      right_inv := selected.property.2.1 }
    related := selected.property.2.2 }

theorem stable_kernel (first : α) (second : β) :
    (first, second) ∈ stable left right ↔
      Nonempty (PresentationIso (unfold left first) (unfold right second)) := by
  constructor
  · intro related
    exact ⟨unfoldingIso (stableStrategy left right) related⟩
  · rintro ⟨iso⟩
    exact matching_in_rounds left right (isoRelation_matching iso) _ (isoRelation_root iso)

def rawUnfoldingEquivalent (first : α) (second : β) : Bool :=
  decide ((first, second) ∈ stable left right)

theorem rawUnfoldingEquivalent_eq_true (first : α) (second : β) :
    rawUnfoldingEquivalent left right first second = true ↔
      Nonempty (PresentationIso (unfold left first) (unfold right second)) := by
  simp only [rawUnfoldingEquivalent, decide_eq_true_eq, stable_kernel]

/-- Counts of any compatible child predicate are preserved, not only
the total number of children. -/
theorem stable_selected_count (first : α) (second : β)
    (related : (first, second) ∈ stable left right)
    (selectedLeft : α → Prop) (selectedRight : β → Prop)
    [DecidablePred selectedLeft] [DecidablePred selectedRight]
    (compatible : ∀ {a b}, (a, b) ∈ stable left right →
      (selectedLeft a ↔ selectedRight b)) :
    size (α := {child : Child left first // selectedLeft child.val}) =
      size (α := {child : Child right second // selectedRight child.val}) := by
  obtain ⟨matching⟩ := matching_of_matches left right _ (stable_matches left right related)
  exact size_eq_of_equiv (matching.selectedChildrenEquiv selectedLeft selectedRight compatible)

theorem stable_child_count (first : α) (second : β)
    (related : (first, second) ∈ stable left right) :
    size (α := Child left first) = size (α := Child right second) := by
  obtain ⟨matching⟩ := matching_of_matches left right _ (stable_matches left right related)
  exact size_eq_of_equiv matching.children

theorem rawUnfoldingEquivalent_preserves_bisimulation (first : α) (second : β)
    (same : rawUnfoldingEquivalent left right first second = true) :
    Bisimilar left right first second := by
  obtain ⟨iso⟩ := (rawUnfoldingEquivalent_eq_true left right first second).mp same
  let related := isoRelation iso
  have matching : ∀ {a b}, related a b →
      Nonempty (ChildMatching (left := left) (right := right) (relation := related) a b) :=
    isoRelation_matching iso
  apply IsBisimulation.bisimilar (R := related) (a := first) (b := second)
  · intro a b paired
    obtain ⟨children, matched⟩ := matching paired
    constructor
    · intro child available
      exact ⟨(children ⟨child, available⟩).val,
        (children ⟨child, available⟩).property, matched ⟨child, available⟩⟩
    · intro child available
      let reply := children.symm ⟨child, available⟩
      refine ⟨reply.val, reply.property, ?_⟩
      have paired := matched reply
      simpa only [reply, Equiv.apply_symm_apply] using paired
  · exact isoRelation_root iso

theorem rawUnfoldingEquivalent_reflexive (first : α) : rawUnfoldingEquivalent left left first first = true :=
  (rawUnfoldingEquivalent_eq_true left left first first).mpr ⟨PresentationIso.refl _⟩

theorem rawUnfoldingEquivalent_symm (first : α) (second : β) :
    rawUnfoldingEquivalent left right first second = rawUnfoldingEquivalent right left second first := by
  apply Bool.eq_iff_iff.mpr
  simp only [rawUnfoldingEquivalent_eq_true]
  exact ⟨fun ⟨iso⟩ => ⟨iso.symm⟩, fun ⟨iso⟩ => ⟨iso.symm⟩⟩

theorem rawUnfoldingEquivalent_trans {γ : Type u} [Enumeration γ] [DecidableEq γ]
    (third : γ → γ → Prop) [DecidableRel third]
    (first : α) (second : β) (target : γ)
    (firstSame : rawUnfoldingEquivalent left right first second = true)
    (secondSame : rawUnfoldingEquivalent right third second target = true) :
    rawUnfoldingEquivalent left third first target = true := by
  obtain ⟨firstIso⟩ := (rawUnfoldingEquivalent_eq_true left right first second).mp firstSame
  obtain ⟨secondIso⟩ := (rawUnfoldingEquivalent_eq_true right third second target).mp secondSame
  exact (rawUnfoldingEquivalent_eq_true left third first target).mpr ⟨firstIso.trans secondIso⟩

omit [Enumeration β] [DecidableEq β] [DecidableRel right] in
/-- Scott extensionality is an admissibility condition on a graph. Only
under that condition does its raw unfolding kernel reduce to root identity. -/
theorem raw_kernel_on_scott_extensional (extensional : ScottExtensional left)
    (first second : α) :
    rawUnfoldingEquivalent left left first second = true ↔ first = second :=
  (rawUnfoldingEquivalent_eq_true left left first second).trans (extensional first second)

end Finite

section ExtensionalityBoundary

open Mettapedia.SetTheory.AntiFoundation

variable {α V : Type u} {edge : Edge α} {membership : MemRel V}

/-- Material extensionality forces vertices with identical child sets to
have equal decorations, independently of anti-foundation. -/
theorem decoration_eq_of_same_children (extensional : WeaklyExtensional (memChild membership))
    {decoration : α → V} (lawful : IsDecoration edge membership decoration)
    {first second : α} (same : ∀ child, edge first child ↔ edge second child) :
    decoration first = decoration second := by
  apply extensional
  intro value
  change membership value (decoration first) ↔ membership value (decoration second)
  rw [lawful first value, lawful second value]
  constructor
  · rintro ⟨child, available, equal⟩
    exact ⟨child, (same child).mp available, equal⟩
  · rintro ⟨child, available, equal⟩
    exact ⟨child, (same child).mpr available, equal⟩

theorem same_children_obstruct_injective_decoration
    (extensional : WeaklyExtensional (memChild membership))
    {first second : α} (different : first ≠ second)
    (same : ∀ child, edge first child ↔ edge second child) :
    ¬ ∃ decoration : α → V, IsDecoration edge membership decoration ∧
      Function.Injective decoration := by
  rintro ⟨decoration, lawful, injective⟩
  exact different (injective (decoration_eq_of_same_children extensional lawful same))

end ExtensionalityBoundary

namespace Presentations

open ProfileGraphReadout.Presentations

/-- The executable raw-unfolding reading of a validated authored graph.
It uses adjacency support while the source retains all row positions. -/
def rawUnfoldingEqual (first second : Checked) : Bool :=
  rawUnfoldingEquivalent (edge first) (edge second) (root first) (root second)

theorem rawUnfoldingEqual_kernel (first second : Checked) :
    rawUnfoldingEqual first second = true ↔
      Nonempty (PresentationIso (unfold (edge first) (root first))
        (unfold (edge second) (root second))) :=
  rawUnfoldingEquivalent_eq_true _ _ _ _

end Presentations

namespace Controls

open Mettapedia.SetTheory.AntiFoundation

instance scottEnumeration : Enumeration Scott where
  elements := [.s0, .s1]
  nodup := by decide
  complete node := by cases node <;> simp

instance scottDecidable : DecidableRel scottEdge := by
  intro source target
  cases source <;> cases target <;> unfold scottEdge <;> infer_instance

theorem scott_degrees :
    size (α := Child scottEdge Scott.s0) = 1 ∧
      size (α := Child scottEdge Scott.s1) = 2 := by
  decide +kernel

theorem scott_raw_unfoldings_differ :
    rawUnfoldingEquivalent scottEdge scottEdge Scott.s0 Scott.s1 = false := by
  decide +kernel

theorem scott_unfoldings_separated :
    ¬ Nonempty (PresentationIso (unfold scottEdge Scott.s0) (unfold scottEdge Scott.s1)) := by
  intro same
  have accepted := (rawUnfoldingEquivalent_eq_true scottEdge scottEdge Scott.s0 Scott.s1).mpr same
  rw [scott_raw_unfoldings_differ] at accepted
  exact Bool.noConfusion accepted

/-- The existing Scott graph witnesses a genuine distinction between
ordinary bisimulation and full unfolding identity. -/
theorem scott_pair_bisimulation_and_raw_unfolding_control :
    Bisimilar scottEdge scottEdge Scott.s0 Scott.s1 ∧
      rawUnfoldingEquivalent scottEdge scottEdge Scott.s0 Scott.s1 = false ∧
      ¬ Nonempty (PresentationIso (unfold scottEdge Scott.s0) (unfold scottEdge Scott.s1)) :=
  ⟨scott_s0_bisim_s1, scott_raw_unfoldings_differ, scott_unfoldings_separated⟩

theorem scott_pair_scott_extensional : ScottExtensional scottEdge := by
  intro first second
  constructor
  · rintro ⟨iso⟩
    cases first with
    | s0 =>
      cases second with
      | s0 => rfl
      | s1 => exact (scott_unfoldings_separated ⟨iso⟩).elim
    | s1 =>
      cases second with
      | s0 => exact (scott_unfoldings_separated ⟨iso.symm⟩).elim
      | s1 => rfl
  · intro same
    cases same
    exact ⟨PresentationIso.refl _⟩

/-- Agreement with the existing canonical Scott control, not with every
ordinary decoration of this graph. -/
theorem scott_canonical_control_kernel (first second : Scott) :
    rawUnfoldingEquivalent scottEdge scottEdge first second = true ↔
      scottSafa first = scottSafa second := by
  rw [raw_kernel_on_scott_extensional scottEdge scott_pair_scott_extensional]
  cases first <;> cases second <;> simp [scottSafa]

theorem scott_ordinary_decoration_not_unique :
    ∃ first second : Scott → SSet,
      IsDecoration scottEdge sMem first ∧ IsDecoration scottEdge sMem second ∧
        first .s1 ≠ second .s1 :=
  scott_two_solutions

def unaryEdge (_source _target : Fin 1) : Prop := True
def cycleEdgeFin (source target : Fin 2) : Prop := source ≠ target

instance unaryDecidable : DecidableRel unaryEdge := fun _ _ => isTrue trivial
instance cycleDecidable : DecidableRel cycleEdgeFin := by
  intro source target
  unfold cycleEdgeFin
  infer_instance

theorem loop_two_cycle_raw_unfoldings_agree :
    rawUnfoldingEquivalent unaryEdge cycleEdgeFin 0 0 = true := by
  decide +kernel

theorem loop_two_cycle_unfolding_iso :
    Nonempty (PresentationIso (unfold unaryEdge 0) (unfold cycleEdgeFin 0)) :=
  (rawUnfoldingEquivalent_eq_true unaryEdge cycleEdgeFin 0 0).mp loop_two_cycle_raw_unfoldings_agree

/-- Whole presentation identity remains finer: one and two vertices
cannot be related by an original-graph node bijection. -/
theorem loop_two_cycle_no_original_bijection : ¬ Nonempty (Fin 1 ≃ Fin 2) := by
  rintro ⟨nodes⟩
  have impossible := size_eq_of_equiv nodes
  simp only [size_fin] at impossible
  omega

def allBinaryEdge (_source _target : Fin 2) : Prop := True
instance allBinaryDecidable : DecidableRel allBinaryEdge := fun _ _ => isTrue trivial

theorem all_binary_roots_raw_equal :
    rawUnfoldingEquivalent allBinaryEdge allBinaryEdge 0 1 = true := by
  decide +kernel

theorem all_binary_not_scott_extensional : ¬ ScottExtensional allBinaryEdge := by
  intro extensional
  have same := (raw_kernel_on_scott_extensional allBinaryEdge extensional 0 1).mp
    all_binary_roots_raw_equal
  exact (by decide : (0 : Fin 2) ≠ 1) same

theorem all_binary_vs_unary_raw_different :
    rawUnfoldingEquivalent allBinaryEdge unaryEdge 0 0 = false := by
  decide +kernel

theorem all_binary_vs_unary_bisimilar : Bisimilar allBinaryEdge unaryEdge 0 0 := by
  apply IsBisimulation.bisimilar (R := fun _ _ => True)
  · intro first second _
    constructor
    · intro child _
      exact ⟨0, trivial, trivial⟩
    · intro child _
      exact ⟨0, trivial, trivial⟩
  · trivial

theorem all_binary_vs_unary_material_equal :
    HSet.decorate allBinaryEdge 0 = HSet.decorate unaryEdge 0 :=
  HSet.decorate_eq_of_bisimilar all_binary_vs_unary_bisimilar

/-- The two binary vertices cannot be injected into any extensional
material carrier; their child sets are already identical. -/
theorem all_binary_no_injective_decoration {V : Type}
    (membership : MemRel V) (extensional : WeaklyExtensional (memChild membership)) :
    ¬ ∃ decoration : Fin 2 → V, IsDecoration allBinaryEdge membership decoration ∧
      Function.Injective decoration :=
  same_children_obstruct_injective_decoration extensional (by decide : (0 : Fin 2) ≠ 1)
    (fun _ => Iff.rfl)

def twoEmptyEdge (source target : Fin 3) : Prop := source = 0 ∧ target ≠ 0
def oneEmptyEdge (source target : Fin 2) : Prop := source = 0 ∧ target = 1

instance twoEmptyDecidable : DecidableRel twoEmptyEdge := by
  intro source target
  unfold twoEmptyEdge
  infer_instance

instance oneEmptyDecidable : DecidableRel oneEmptyEdge := by
  intro source target
  unfold oneEmptyEdge
  infer_instance

theorem two_empty_vs_one_empty_raw_different :
    rawUnfoldingEquivalent twoEmptyEdge oneEmptyEdge 0 0 = false := by
  decide +kernel

theorem two_empty_roots_identified :
    rawUnfoldingEquivalent twoEmptyEdge twoEmptyEdge 1 2 = true := by
  decide +kernel

theorem two_empty_not_scott_extensional : ¬ ScottExtensional twoEmptyEdge := by
  intro extensional
  have same := (raw_kernel_on_scott_extensional twoEmptyEdge extensional 1 2).mp
    two_empty_roots_identified
  exact (by decide : (1 : Fin 3) ≠ 2) same

theorem two_empty_vs_one_empty_bisimilar : Bisimilar twoEmptyEdge oneEmptyEdge 0 0 := by
  let relation : Fin 3 → Fin 2 → Prop := fun first second =>
    (first = 0 ∧ second = 0) ∨ (first ≠ 0 ∧ second = 1)
  have matched : IsBisimulation twoEmptyEdge oneEmptyEdge relation := by
    intro first second paired
    rcases paired with ⟨rfl, rfl⟩ | ⟨nonzero, rfl⟩
    · constructor
      · intro child available
        exact ⟨1, ⟨rfl, rfl⟩, Or.inr ⟨available.2, rfl⟩⟩
      · intro child available
        exact ⟨1, ⟨rfl, by decide⟩, Or.inr ⟨by decide, available.2⟩⟩
    · constructor
      · intro child available
        exact (nonzero available.1).elim
      · intro child available
        exact ((by decide : (1 : Fin 2) ≠ 0) available.1).elim
  exact matched.bisimilar (Or.inl ⟨rfl, rfl⟩)

theorem two_empty_vs_one_empty_material_equal :
    HSet.decorate twoEmptyEdge 0 = HSet.decorate oneEmptyEdge 0 :=
  HSet.decorate_eq_of_bisimilar two_empty_vs_one_empty_bisimilar

theorem empty_duplicate_no_injective_decoration {V : Type}
    (membership : MemRel V) (extensional : WeaklyExtensional (memChild membership)) :
    ¬ ∃ decoration : Fin 3 → V, IsDecoration twoEmptyEdge membership decoration ∧
      Function.Injective decoration := by
  apply same_children_obstruct_injective_decoration extensional
    (by decide : (1 : Fin 3) ≠ 2)
  intro child
  unfold twoEmptyEdge
  simp

open ProfileGraphReadout.Presentations in
theorem authored_repeated_slots_raw_equal :
    Presentations.rawUnfoldingEqual Controls.duplicate Controls.chain = true := by
  decide +kernel

open ProfileGraphReadout.Presentations in
theorem authored_distinct_empty_nodes_raw_different :
    Presentations.rawUnfoldingEqual Controls.twoEmptyTargets Controls.chain = false := by
  decide +kernel

open ProfileGraphReadout.Presentations in
theorem authored_occurrences_two_adjacency_child_one :
    size (α := Occurrence Controls.duplicate (root Controls.duplicate)) = 2 ∧
      size (α := Child (edge Controls.duplicate) (root Controls.duplicate)) = 1 := by
  decide +kernel

end Controls

end Mettapedia.SetTheory.Profiles.ProfileFiniteScottReadout
