import Mettapedia.SetTheory.Profiles.ProfileFiniteScottReadout

/-!
# Constructed finite quotient and recount

A raw adjacency graph is quotiented by its full-unfolding kernel. Edges in
that quotient are images of adjacency support; several old targets in the
same class give one new target. Recounting therefore uses the new graph,
rather than the old graph's child multiplicities.

Every nontrivial quotient removes a vertex. Iterating that construction
terminates with a Scott-extensional finite graph. This is a canonical finite
graph reading, not an anti-foundation universe. A material interpretation
must preserve its canonical kernel; an ordinary decoration is insufficient.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileFiniteScottCollapse

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open UnfoldingIdentityComparison
open ProfileFiniteScottReadout ConstructiveFinite
open Mettapedia.SetTheory.AntiFoundation

universe u

section FiniteQuotient

variable {α : Type u} [Enumeration α]
variable (relation : α → α → Prop) [DecidableRel relation]
variable (equivalence : Equivalence relation)

omit [Enumeration α] in
/-- Equivalent rows have the same first matching candidate. -/
theorem witnessFromList_congr (pool : List α) (first second : α → Prop)
    [DecidablePred first] [DecidablePred second]
    (firstAvailable : ∃ value ∈ pool, first value)
    (secondAvailable : ∃ value ∈ pool, second value)
    (same : ∀ value, first value ↔ second value) :
    (witnessFromList pool first firstAvailable).val =
      (witnessFromList pool second secondAvailable).val := by
  induction pool with
  | nil => exact False.elim (by simp at firstAvailable)
  | cons head tail previous =>
    by_cases goodFirst : first head
    · have goodSecond := (same head).mp goodFirst
      simp only [witnessFromList, goodFirst, goodSecond, dif_pos]
    · have goodSecond : ¬ second head := fun proof => goodFirst ((same head).mpr proof)
      simp only [witnessFromList, goodFirst, goodSecond]
      exact previous _ _

def representative (value : α) : α :=
  (witness (relation value) ⟨value, equivalence.refl value⟩).val

theorem related_representative (value : α) :
    relation value (representative relation equivalence value) :=
  (witness (relation value) ⟨value, equivalence.refl value⟩).property

theorem representatives_equal {first second : α} (same : relation first second) :
    representative relation equivalence first = representative relation equivalence second := by
  apply witnessFromList_congr
  intro value
  exact ⟨fun available => equivalence.trans (equivalence.symm same) available,
    fun available => equivalence.trans same available⟩

theorem representative_kernel (first second : α) :
    representative relation equivalence first = representative relation equivalence second ↔
      relation first second := by
  constructor
  · intro same
    have firstRelated := related_representative relation equivalence first
    have secondRelated := related_representative relation equivalence second
    rw [same] at firstRelated
    exact equivalence.trans firstRelated (equivalence.symm secondRelated)
  · exact representatives_equal relation equivalence

theorem representative_idempotent (value : α) :
    representative relation equivalence (representative relation equivalence value) =
      representative relation equivalence value :=
  (representatives_equal relation equivalence (related_representative relation equivalence value)).symm

abbrev Representative := {value : α // representative relation equivalence value = value}

def project (value : α) : Representative relation equivalence :=
  ⟨representative relation equivalence value, representative_idempotent relation equivalence value⟩

theorem project_kernel (first second : α) :
    project relation equivalence first = project relation equivalence second ↔ relation first second :=
  Subtype.ext_iff.trans (representative_kernel relation equivalence first second)

theorem project_representative (value : Representative relation equivalence) :
    project relation equivalence value.val = value := Subtype.ext value.property

theorem project_surjective : Function.Surjective (project relation equivalence) :=
  fun value => ⟨value.val, project_representative relation equivalence value⟩

variable (edge : α → α → Prop) [DecidableRel edge]

/-- Adjacency in the quotient is support of the projected old targets. -/
def quotientEdge (source target : Representative relation equivalence) : Prop :=
  ∃ child, edge source.val child ∧ project relation equivalence child = target

instance quotientEdgeDecidable [DecidableEq α] : DecidableRel (quotientEdge relation equivalence edge) := by
  intro source target
  unfold quotientEdge
  infer_instance

omit [DecidableRel edge] in
/-- The image law holds at every original source, including nonrepresentatives. -/
theorem quotientEdge_project (regular : IsBisimulation edge edge relation) (source : α) (target : Representative relation equivalence) :
    quotientEdge relation equivalence edge (project relation equivalence source) target ↔
      ∃ child, edge source child ∧ project relation equivalence child = target := by
  constructor
  · rintro ⟨child, available, same⟩
    obtain ⟨reply, replyAvailable, paired⟩ :=
      (regular (related_representative relation equivalence source)).2 child available
    exact ⟨reply, replyAvailable,
      ((project_kernel relation equivalence reply child).mpr paired).trans same⟩
  · rintro ⟨child, available, same⟩
    obtain ⟨reply, replyAvailable, paired⟩ :=
      (regular (related_representative relation equivalence source)).1 child available
    exact ⟨reply, replyAvailable,
      ((project_kernel relation equivalence child reply).mpr paired).symm.trans same⟩

omit [DecidableRel edge] in
theorem quotient_projection_bisimulation (regular : IsBisimulation edge edge relation) :
    IsBisimulation edge (quotientEdge relation equivalence edge)
      (fun source target => project relation equivalence source = target) := by
  intro source target same
  subst target
  constructor
  · intro child available
    exact ⟨project relation equivalence child,
      (quotientEdge_project relation equivalence edge regular source _).mpr
        ⟨child, available, rfl⟩, rfl⟩
  · intro child available
    obtain ⟨reply, replyAvailable, paired⟩ :=
      (quotientEdge_project relation equivalence edge regular source child).mp available
    exact ⟨reply, replyAvailable, paired⟩

def NoMerge : Prop := ∀ value, representative relation equivalence value = value

instance noMergeDecidable [DecidableEq α] : Decidable (NoMerge relation equivalence) := by
  unfold NoMerge
  infer_instance

theorem noMerge_iff_kernel_identity :
    NoMerge relation equivalence ↔ ∀ first second, relation first second ↔ first = second := by
  constructor
  · intro unchanged first second
    rw [← representative_kernel relation equivalence, unchanged first, unchanged second]
  · intro literal value
    exact ((literal value _).mp (related_representative relation equivalence value)).symm

theorem quotient_size_le [DecidableEq α] :
    size (α := Representative relation equivalence) ≤ size (α := α) := by
  rw [subtype_size]
  exact List.length_filter_le _ _

theorem quotient_size_lt [DecidableEq α] (changes : ¬ NoMerge relation equivalence) :
    size (α := Representative relation equivalence) < size (α := α) := by
  rw [subtype_size]
  apply length_lt_of_sublist_ne List.filter_sublist
  intro same
  apply changes
  intro value
  have located : value ∈ (elements (α := α)).filter
      (fun value => decide (representative relation equivalence value = value)) :=
    same.symm ▸ complete value
  exact of_decide_eq_true (List.mem_filter.mp located).2

end FiniteQuotient

/-- A finite carrier together with its actual enumeration and adjacency. -/
structure FiniteGraph where
  Node : Type u
  enumeration : Enumeration Node
  equality : DecidableEq Node
  edge : Node → Node → Prop
  decideEdge : DecidableRel edge

attribute [instance] FiniteGraph.enumeration FiniteGraph.equality FiniteGraph.decideEdge

namespace FiniteGraph

@[instance_reducible] def tableRelationDecidable {α : Type u} [DecidableEq α] (table : List (α × α)) :
    DecidableRel (fun first second => (first, second) ∈ table) :=
  fun first second => inferInstanceAs (Decidable ((first, second) ∈ table))

@[instance_reducible] def relationDecisionFromTable {α : Type u} [DecidableEq α]
    (relation : α → α → Prop) (table : List (α × α))
    (correct : ∀ first second, (first, second) ∈ table ↔ relation first second) :
    DecidableRel relation :=
  fun first second => decidable_of_iff ((first, second) ∈ table) (correct first second)

/-- A complete finite adjacency table is computed once before queries.
Its decision closure recognizes exactly the original edge relation. -/
@[instance_reducible] def cachedRelationDecidable {α : Type u} [Enumeration α] [DecidableEq α]
    (relation : α → α → Prop) [DecidableRel relation] : DecidableRel relation :=
  relationDecisionFromTable relation
    (pairElements.filter (fun pair => decide (relation pair.1 pair.2))) (by
      intro first second
      simp only [List.mem_filter, decide_eq_true_eq]
      exact and_iff_right (pair_complete first second))

def rawRelation (graph : FiniteGraph.{u}) (first second : graph.Node) : Prop :=
  (first, second) ∈ stable graph.edge graph.edge

instance rawRelationDecidable (graph : FiniteGraph.{u}) : DecidableRel graph.rawRelation :=
  tableRelationDecidable (stable graph.edge graph.edge)

theorem rawRelation_equivalence (graph : FiniteGraph.{u}) : Equivalence graph.rawRelation := by
  refine ⟨?_, ?_, ?_⟩
  · intro node
    exact (stable_kernel graph.edge graph.edge node node).mpr ⟨PresentationIso.refl _⟩
  · intro first second same
    obtain ⟨isomorphism⟩ := (stable_kernel graph.edge graph.edge first second).mp same
    exact (stable_kernel graph.edge graph.edge second first).mpr ⟨isomorphism.symm⟩
  · intro first middle last before after
    obtain ⟨firstIso⟩ := (stable_kernel graph.edge graph.edge first middle).mp before
    obtain ⟨secondIso⟩ := (stable_kernel graph.edge graph.edge middle last).mp after
    exact (stable_kernel graph.edge graph.edge first last).mpr ⟨firstIso.trans secondIso⟩

theorem rawRelation_regular (graph : FiniteGraph.{u}) :
    IsBisimulation graph.edge graph.edge graph.rawRelation := by
  intro first second same
  let matching := stableStrategy graph.edge graph.edge same
  constructor
  · intro child available
    exact ⟨(matching.children ⟨child, available⟩).val,
      (matching.children ⟨child, available⟩).property, matching.related ⟨child, available⟩⟩
  · intro child available
    exact ⟨(matching.children.symm ⟨child, available⟩).val,
      (matching.children.symm ⟨child, available⟩).property, matching.related_back ⟨child, available⟩⟩

def regularIdentification (graph : FiniteGraph.{u}) : RegularIdentification graph.edge where
  ident := graph.rawRelation
  equiv := graph.rawRelation_equivalence
  bisim := graph.rawRelation_regular

def quotient (graph : FiniteGraph.{u}) : FiniteGraph.{u} where
  Node := Representative graph.rawRelation graph.rawRelation_equivalence
  enumeration := inferInstance
  equality := inferInstance
  edge := quotientEdge graph.rawRelation graph.rawRelation_equivalence graph.edge
  decideEdge := cachedRelationDecidable (quotientEdge graph.rawRelation graph.rawRelation_equivalence graph.edge)

def projection (graph : FiniteGraph.{u}) : graph.Node → graph.quotient.Node :=
  project graph.rawRelation graph.rawRelation_equivalence

theorem projection_kernel (graph : FiniteGraph.{u}) (first second : graph.Node) :
    graph.projection first = graph.projection second ↔ graph.rawRelation first second :=
  project_kernel graph.rawRelation graph.rawRelation_equivalence first second

theorem projection_surjective (graph : FiniteGraph.{u}) : Function.Surjective graph.projection :=
  project_surjective graph.rawRelation graph.rawRelation_equivalence

theorem projection_edge (graph : FiniteGraph.{u})
    (source : graph.Node) (target : graph.quotient.Node) :
    graph.quotient.edge (graph.projection source) target ↔
      ∃ child, graph.edge source child ∧ graph.projection child = target :=
  quotientEdge_project graph.rawRelation graph.rawRelation_equivalence graph.edge
    graph.rawRelation_regular source target

def stopped (graph : FiniteGraph.{u}) : Prop :=
  NoMerge graph.rawRelation graph.rawRelation_equivalence

instance stoppedDecidable (graph : FiniteGraph.{u}) : Decidable graph.stopped :=
  noMergeDecidable graph.rawRelation graph.rawRelation_equivalence

theorem stopped_iff_scottExtensional (graph : FiniteGraph.{u}) :
    graph.stopped ↔ ScottExtensional graph.edge := by
  rw [stopped, noMerge_iff_kernel_identity]
  constructor
  · intro literal first second
    exact (stable_kernel graph.edge graph.edge first second).symm.trans (literal first second)
  · intro extensional first second
    exact (stable_kernel graph.edge graph.edge first second).trans (extensional first second)

theorem quotient_size_le (graph : FiniteGraph.{u}) :
    size (α := graph.quotient.Node) ≤ size (α := graph.Node) :=
  ProfileFiniteScottCollapse.quotient_size_le graph.rawRelation graph.rawRelation_equivalence

theorem quotient_size_lt (graph : FiniteGraph.{u}) (changes : ¬ graph.stopped) :
    size (α := graph.quotient.Node) < size (α := graph.Node) :=
  ProfileFiniteScottCollapse.quotient_size_lt graph.rawRelation graph.rawRelation_equivalence changes

def quotientEquiv (graph : FiniteGraph.{u}) (unchanged : graph.stopped) :
    graph.Node ≃ graph.quotient.Node where
  toFun := graph.projection
  invFun value := value.val
  left_inv value := unchanged value
  right_inv value := project_representative graph.rawRelation graph.rawRelation_equivalence value

theorem quotientEquiv_edge (graph : FiniteGraph.{u}) (unchanged : graph.stopped)
    (source target : graph.Node) :
    graph.edge source target ↔
      graph.quotient.edge (graph.quotientEquiv unchanged source) (graph.quotientEquiv unchanged target) := by
  change graph.edge source target ↔
    graph.quotient.edge (graph.projection source) (graph.projection target)
  rw [projection_edge]
  exact ⟨fun available => ⟨target, available, rfl⟩,
    fun ⟨child, available, same⟩ => (graph.quotientEquiv unchanged).injective same ▸ available⟩

/-- Original graph isomorphism transports every unfolding occurrence. -/
def unfoldingEquivIso {α β : Type u} (left : α → α → Prop) (right : β → β → Prop)
    (nodes : α ≃ β) (edges : ∀ first second, left first second ↔ right (nodes first) (nodes second))
    (first : α) : PresentationIso (unfold left first) (unfold right (nodes first)) := by
  let strategy : Strategy (left := left) (right := right)
      (relation := fun a b => nodes a = b) := by
    intro source target paired
    subst target
    exact ⟨nodes.subtypeEquiv (fun child => edges source child), fun _ => rfl⟩
  exact unfoldingIso strategy rfl

theorem scottExtensional_of_equiv {α β : Type u} (left : α → α → Prop) (right : β → β → Prop)
    (nodes : α ≃ β) (edges : ∀ first second, left first second ↔ right (nodes first) (nodes second))
    (extensional : ScottExtensional left) : ScottExtensional right := by
  intro first second
  constructor
  · rintro ⟨isomorphism⟩
    have firstIso : PresentationIso (unfold left (nodes.symm first)) (unfold right first) := by
      simpa only [Equiv.apply_symm_apply] using unfoldingEquivIso left right nodes edges (nodes.symm first)
    have secondIso : PresentationIso (unfold left (nodes.symm second)) (unfold right second) := by
      simpa only [Equiv.apply_symm_apply] using unfoldingEquivIso left right nodes edges (nodes.symm second)
    have same := (extensional _ _).mp ⟨firstIso.trans (isomorphism.trans secondIso.symm)⟩
    simpa only [Equiv.apply_symm_apply] using congrArg nodes same
  · intro same
    subst second
    exact ⟨PresentationIso.refl _⟩

theorem stopped_quotient (graph : FiniteGraph.{u}) (unchanged : graph.stopped) :
    graph.quotient.stopped :=
  (stopped_iff_scottExtensional _).mpr
    (scottExtensional_of_equiv graph.edge graph.quotient.edge (graph.quotientEquiv unchanged)
      (graph.quotientEquiv_edge unchanged) ((stopped_iff_scottExtensional _).mp unchanged))

def iterate (graph : FiniteGraph.{u}) : Nat → FiniteGraph.{u}
  | 0 => graph
  | count + 1 => (iterate graph count).quotient

def iterateProjection (graph : FiniteGraph.{u}) :
    (count : Nat) → graph.Node → (graph.iterate count).Node
  | 0 => fun value => value
  | count + 1 => fun value =>
      (graph.iterate count).projection (iterateProjection graph count value)

theorem iterateProjection_surjective (graph : FiniteGraph.{u}) (count : Nat) :
    Function.Surjective (graph.iterateProjection count) := by
  induction count with
  | zero => exact fun value => ⟨value, rfl⟩
  | succ count previous =>
    exact (graph.iterate count).projection_surjective.comp previous

theorem iterateProjection_edge (graph : FiniteGraph.{u}) (count : Nat)
    (source : graph.Node) (target : (graph.iterate count).Node) :
    (graph.iterate count).edge (graph.iterateProjection count source) target ↔
      ∃ child, graph.edge source child ∧ graph.iterateProjection count child = target := by
  induction count with
  | zero =>
    exact ⟨fun available => ⟨target, available, rfl⟩,
      fun ⟨child, available, same⟩ => same ▸ available⟩
  | succ count previous =>
    change (graph.iterate count).quotient.edge
      ((graph.iterate count).projection (graph.iterateProjection count source)) target ↔
        ∃ child, graph.edge source child ∧
          (graph.iterate count).projection (graph.iterateProjection count child) = target
    rw [(graph.iterate count).projection_edge (graph.iterateProjection count source) target]
    constructor
    · rintro ⟨middle, available, same⟩
      obtain ⟨child, childAvailable, paired⟩ := (previous middle).mp available
      exact ⟨child, childAvailable, (congrArg (graph.iterate count).projection paired).trans same⟩
    · rintro ⟨child, available, same⟩
      exact ⟨graph.iterateProjection count child,
        (previous _).mpr ⟨child, available, rfl⟩, same⟩

theorem iterateProjection_equal_persists (graph : FiniteGraph.{u}) (count later : Nat)
    (first second : graph.Node)
    (same : graph.iterateProjection count first = graph.iterateProjection count second) :
    graph.iterateProjection (count + later) first = graph.iterateProjection (count + later) second := by
  induction later with
  | zero => exact same
  | succ later previous =>
    change (graph.iterate (count + later)).projection
      (graph.iterateProjection (count + later) first) =
        (graph.iterate (count + later)).projection (graph.iterateProjection (count + later) second)
    exact congrArg (graph.iterate (count + later)).projection previous

theorem stopped_predecessor (graph : FiniteGraph.{u}) (count : Nat)
    (notStopped : ¬ (graph.iterate (count + 1)).stopped) :
    ¬ (graph.iterate count).stopped := fun earlier =>
  notStopped (stopped_quotient _ earlier)

theorem strict_iteration_bound (graph : FiniteGraph.{u}) (count : Nat)
    (notStopped : ¬ (graph.iterate count).stopped) :
    size (α := (graph.iterate (count + 1)).Node) + (count + 1) ≤ size (α := graph.Node) := by
  induction count with
  | zero =>
    exact Nat.succ_le_of_lt (quotient_size_lt graph notStopped)
  | succ count previous =>
    have earlier := stopped_predecessor graph count notStopped
    have bound := previous earlier
    have decreases := quotient_size_lt (graph.iterate (count + 1)) notStopped
    change size (α := (graph.iterate (count + 2)).Node) <
      size (α := (graph.iterate (count + 1)).Node) at decreases
    omega

/-- The input size bounds actual quotient rounds; no final quotient is supplied. -/
theorem iterate_stops (graph : FiniteGraph.{u}) :
    (graph.iterate (size (α := graph.Node))).stopped := by
  by_cases unchanged : (graph.iterate (size (α := graph.Node))).stopped
  · exact unchanged
  · have impossible := strict_iteration_bound graph (size (α := graph.Node)) unchanged
    omega

def canonicalGraph (graph : FiniteGraph.{u}) : FiniteGraph.{u} :=
  graph.iterate (size (α := graph.Node))

def canonicalProjection (graph : FiniteGraph.{u}) : graph.Node → graph.canonicalGraph.Node :=
  graph.iterateProjection (size (α := graph.Node))

theorem canonicalGraph_scottExtensional (graph : FiniteGraph.{u}) :
    ScottExtensional graph.canonicalGraph.edge :=
  (stopped_iff_scottExtensional _).mp (iterate_stops graph)

theorem canonicalProjection_surjective (graph : FiniteGraph.{u}) :
    Function.Surjective graph.canonicalProjection :=
  iterateProjection_surjective graph _

theorem canonicalProjection_edge (graph : FiniteGraph.{u})
    (source : graph.Node) (target : graph.canonicalGraph.Node) :
    graph.canonicalGraph.edge (graph.canonicalProjection source) target ↔
      ∃ child, graph.edge source child ∧ graph.canonicalProjection child = target :=
  iterateProjection_edge graph _ source target

theorem stopped_iterate (graph : FiniteGraph.{u}) (unchanged : graph.stopped) (count : Nat) :
    (graph.iterate count).stopped := by
  induction count with
  | zero => exact unchanged
  | succ count previous => exact stopped_quotient _ previous

theorem iterateProjection_injective_of_stopped (graph : FiniteGraph.{u})
    (unchanged : graph.stopped) (count : Nat) : Function.Injective (graph.iterateProjection count) := by
  induction count with
  | zero => exact fun _ _ same => same
  | succ count previous =>
    exact ((graph.iterate count).quotientEquiv (stopped_iterate graph unchanged count)).injective.comp previous

def iterateOrigin (graph : FiniteGraph.{u}) :
    (count : Nat) → (graph.iterate count).Node → graph.Node
  | 0 => fun value => value
  | count + 1 => fun value => iterateOrigin graph count value.val

theorem iterateProjection_origin (graph : FiniteGraph.{u}) (count : Nat)
    (value : (graph.iterate count).Node) :
    graph.iterateProjection count (graph.iterateOrigin count value) = value := by
  induction count with
  | zero => rfl
  | succ count previous =>
    change (graph.iterate count).projection
      (graph.iterateProjection count (graph.iterateOrigin count value.val)) = value
    rw [previous]
    exact project_representative _ _ value

def canonicalOrigin (graph : FiniteGraph.{u}) : graph.canonicalGraph.Node → graph.Node :=
  graph.iterateOrigin (size (α := graph.Node))

theorem canonicalProjection_origin (graph : FiniteGraph.{u}) (value : graph.canonicalGraph.Node) :
    graph.canonicalProjection (graph.canonicalOrigin value) = value :=
  iterateProjection_origin graph _ value

/-- Identical adjacency sets give isomorphic full unfolding trees. -/
theorem unfoldings_of_same_children (graph : FiniteGraph.{u}) (first second : graph.Node)
    (same : ∀ child, graph.edge first child ↔ graph.edge second child) :
    Nonempty (PresentationIso (unfold graph.edge first) (unfold graph.edge second)) := by
  let relation : graph.Node → graph.Node → Prop := fun a b => a = b ∨ a = first ∧ b = second
  have matching : ∀ {a b}, relation a b →
      Nonempty (ChildMatching (left := graph.edge) (right := graph.edge) (relation := relation) a b) := by
    intro a b paired
    rcases paired with rfl | ⟨rfl, rfl⟩
    · exact ⟨⟨Equiv.refl _, fun _ => Or.inl rfl⟩⟩
    · exact ⟨⟨(Equiv.refl graph.Node).subtypeEquiv same, fun _ => Or.inl rfl⟩⟩
  exact (stable_kernel graph.edge graph.edge first second).mp
    (matching_in_rounds graph.edge graph.edge matching _ (Or.inr ⟨rfl, rfl⟩))

/-- The canonical quotient's actual membership relation. -/
def canonicalMember (graph : FiniteGraph.{u})
    (member set : graph.canonicalGraph.Node) : Prop := graph.canonicalGraph.edge set member

instance canonicalMemberDecidable (graph : FiniteGraph.{u}) : DecidableRel graph.canonicalMember :=
  fun member set => graph.canonicalGraph.decideEdge set member

theorem canonicalMember_extensional (graph : FiniteGraph.{u}) :
    WeaklyExtensional (memChild graph.canonicalMember) := by
  intro first second same
  apply (canonicalGraph_scottExtensional graph first second).mp
  exact unfoldings_of_same_children graph.canonicalGraph first second same

def canonicalEquivalent (graph : FiniteGraph.{u}) (first second : graph.Node) : Bool :=
  decide (graph.canonicalProjection first = graph.canonicalProjection second)

theorem canonicalEquivalent_kernel (graph : FiniteGraph.{u}) (first second : graph.Node) :
    graph.canonicalEquivalent first second = true ↔
      graph.canonicalProjection first = graph.canonicalProjection second := by
  simp only [canonicalEquivalent, decide_eq_true_eq]

/-- The canonical kernel compares the final, recounted unfoldings. -/
theorem canonicalEquivalent_unfolding_kernel (graph : FiniteGraph.{u}) (first second : graph.Node) :
    graph.canonicalEquivalent first second = true ↔
      Nonempty (PresentationIso
        (unfold graph.canonicalGraph.edge (graph.canonicalProjection first))
        (unfold graph.canonicalGraph.edge (graph.canonicalProjection second))) :=
  (canonicalEquivalent_kernel graph first second).trans
    (canonicalGraph_scottExtensional graph _ _).symm

theorem canonicalEquivalent_of_stopped (graph : FiniteGraph.{u})
    (unchanged : graph.stopped) (first second : graph.Node) :
    graph.canonicalEquivalent first second = true ↔ first = second :=
  (canonicalEquivalent_kernel graph first second).trans
    (iterateProjection_injective_of_stopped graph unchanged _).eq_iff

/-- Every first-round merge remains merged in the constructed final reading. -/
theorem canonicalEquivalent_of_raw (graph : FiniteGraph.{u}) (first second : graph.Node)
    (same : graph.rawRelation first second) : graph.canonicalEquivalent first second = true := by
  have initial : graph.iterateProjection 1 first = graph.iterateProjection 1 second :=
    (projection_kernel graph first second).mpr same
  have positive : 0 < size (α := graph.Node) := List.length_pos_iff.mpr (List.ne_nil_of_mem (complete first))
  have final := iterateProjection_equal_persists graph 1 (size (α := graph.Node) - 1) first second initial
  have steps : 1 + (size (α := graph.Node) - 1) = size (α := graph.Node) := by omega
  apply (canonicalEquivalent_kernel graph first second).mpr
  change graph.iterateProjection (size (α := graph.Node)) first = graph.iterateProjection (size (α := graph.Node)) second
  rw [steps] at final
  exact final

/-- This finite material interpretation is constructed from the input graph. -/
theorem canonicalDecoration (graph : FiniteGraph.{u}) :
    CanonicalDecoration graph.edge
      (fun first second => graph.canonicalEquivalent first second = true)
      graph.canonicalMember graph.canonicalProjection where
  decoration source value := by
    change graph.canonicalGraph.edge (graph.canonicalProjection source) value ↔ _
    rw [canonicalProjection_edge]
    exact ⟨fun ⟨child, available, same⟩ => ⟨child, available, same.symm⟩,
      fun ⟨child, available, same⟩ => ⟨child, available, same.symm⟩⟩
  respects _ _ same := (canonicalEquivalent_kernel graph _ _).mp same
  reflects _ _ same := (canonicalEquivalent_kernel graph _ _).mpr same

def canonicalIdentification (graph : FiniteGraph.{u}) : RegularIdentification graph.edge := by
  refine ⟨fun first second => graph.canonicalEquivalent first second = true, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro node
      exact (canonicalEquivalent_kernel graph node node).mpr rfl
    · intro first second same
      exact (canonicalEquivalent_kernel graph second first).mpr
        ((canonicalEquivalent_kernel graph first second).mp same).symm
    · intro first middle last before after
      exact (canonicalEquivalent_kernel graph first last).mpr
        (((canonicalEquivalent_kernel graph first middle).mp before).trans
          ((canonicalEquivalent_kernel graph middle last).mp after))
  · intro first second same
    have paired := (canonicalEquivalent_kernel graph first second).mp same
    constructor
    · intro child available
      have projected := (graph.canonicalProjection_edge first _).mpr ⟨child, available, rfl⟩
      rw [paired] at projected
      obtain ⟨reply, replyAvailable, matched⟩ := (graph.canonicalProjection_edge second _).mp projected
      exact ⟨reply, replyAvailable, (canonicalEquivalent_kernel graph child reply).mpr matched.symm⟩
    · intro child available
      have projected := (graph.canonicalProjection_edge second _).mpr ⟨child, available, rfl⟩
      rw [← paired] at projected
      obtain ⟨reply, replyAvailable, matched⟩ := (graph.canonicalProjection_edge first _).mp projected
      exact ⟨reply, replyAvailable, (canonicalEquivalent_kernel graph reply child).mpr matched⟩

/-- Canonical material readout preserves the ordinary Aczel denotation. -/
theorem canonicalEquivalent_preserves_material (graph : FiniteGraph.{u})
    (first second : graph.Node) (same : graph.canonicalEquivalent first second = true) :
    HSet.decorate graph.edge first = HSet.decorate graph.edge second :=
  HSet.decorate_eq_of_bisimilar ((canonicalIdentification graph).bisim.bisimilar same)

/-- A target interpretation of the final graph is required to retain its
canonical identity. Ordinary decorations need not be injective. -/
theorem transport_canonicalDecoration (graph : FiniteGraph.{u}) {V : Type u}
    (membership : MemRel V) (decoration : graph.canonicalGraph.Node → V)
    (canonical : CanonicalDecoration graph.canonicalGraph.edge Eq membership decoration) :
    CanonicalDecoration graph.edge
      (fun first second => graph.canonicalEquivalent first second = true)
      membership (fun value => decoration (graph.canonicalProjection value)) where
  decoration source value := by
    rw [canonical.decoration]
    constructor
    · rintro ⟨middle, available, same⟩
      obtain ⟨child, childAvailable, projected⟩ := (graph.canonicalProjection_edge source middle).mp available
      exact ⟨child, childAvailable, same.trans (congrArg decoration projected.symm)⟩
    · rintro ⟨child, available, same⟩
      exact ⟨graph.canonicalProjection child,
        (graph.canonicalProjection_edge source _).mpr ⟨child, available, rfl⟩, same⟩
  respects first second same := congrArg decoration ((canonicalEquivalent_kernel graph first second).mp same)
  reflects first second same := (canonicalEquivalent_kernel graph first second).mpr (canonical.reflects _ _ same)

theorem transported_kernel (graph : FiniteGraph.{u}) {V : Type u}
    (membership : MemRel V) (decoration : graph.canonicalGraph.Node → V)
    (canonical : CanonicalDecoration graph.canonicalGraph.edge Eq membership decoration)
    (first second : graph.Node) :
    graph.canonicalEquivalent first second = true ↔
      decoration (graph.canonicalProjection first) = decoration (graph.canonicalProjection second) :=
  ⟨(transport_canonicalDecoration graph membership decoration canonical).respects first second,
    (transport_canonicalDecoration graph membership decoration canonical).reflects first second⟩

/-- The final quotient has complete dependent membership fibres; its child
receipts can still carry several original occurrences of the same member. -/
def childReadout (graph : FiniteGraph.{u}) (source : graph.Node)
    (child : Child graph.edge source) :
    Child graph.canonicalGraph.edge (graph.canonicalProjection source) :=
  ⟨graph.canonicalProjection child.val,
    (graph.canonicalProjection_edge source _).mpr ⟨child.val, child.property, rfl⟩⟩

theorem childReadout_surjective (graph : FiniteGraph.{u}) (source : graph.Node) :
    Function.Surjective (graph.childReadout source) := by
  intro child
  obtain ⟨reply, available, paired⟩ := (graph.canonicalProjection_edge source child.val).mp child.property
  exact ⟨⟨reply, available⟩, Subtype.ext paired⟩

theorem childReadout_kernel (graph : FiniteGraph.{u}) (source : graph.Node)
    (first second : Child graph.edge source) :
    graph.childReadout source first = graph.childReadout source second ↔
      graph.canonicalEquivalent first.val second.val = true :=
  Subtype.ext_iff.trans (canonicalEquivalent_kernel graph first.val second.val).symm

/-- The final graph's support enumerates each member class once. -/
def members (graph : FiniteGraph.{u}) (source : graph.Node) : List graph.canonicalGraph.Node :=
  elements.filter (fun target => decide (graph.canonicalGraph.edge (graph.canonicalProjection source) target))

theorem mem_members (graph : FiniteGraph.{u}) (source : graph.Node)
    (target : graph.canonicalGraph.Node) :
    target ∈ graph.members source ↔ graph.canonicalMember target (graph.canonicalProjection source) := by
  simp only [members, List.mem_filter, decide_eq_true_eq]
  exact and_iff_right (complete target)

theorem members_nodup (graph : FiniteGraph.{u}) (source : graph.Node) : (graph.members source).Nodup :=
  (nodup (α := graph.canonicalGraph.Node)).filter _

/-- Material membership fibres can be lifted back to retained source vertices. -/
def memberOrigins (graph : FiniteGraph.{u}) (source : graph.Node) : List graph.Node :=
  (graph.members source).map graph.canonicalOrigin

theorem mem_memberOrigins (graph : FiniteGraph.{u}) (source target : graph.Node) :
    target ∈ graph.memberOrigins source ↔
      ∃ value ∈ graph.members source, graph.canonicalOrigin value = target := List.mem_map

end FiniteGraph

section DisjointUnion

variable {α β : Type u} [Enumeration α] [Enumeration β]

instance sumEnumeration : Enumeration (Sum α β) where
  elements := (elements (α := α)).map Sum.inl ++ (elements (α := β)).map Sum.inr
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨(nodup (α := α)).map Sum.inl_injective,
      (nodup (α := β)).map Sum.inr_injective, ?_⟩
    intro first before second after same
    obtain ⟨left, _, sameFirst⟩ := List.mem_map.mp before
    obtain ⟨right, _, sameSecond⟩ := List.mem_map.mp after
    have impossible : (Sum.inl left : Sum α β) = Sum.inr right :=
      sameFirst.trans (same.trans sameSecond.symm)
    cases impossible
  complete value := by
    cases value with
    | inl value => exact List.mem_append_left _ (List.mem_map.mpr ⟨value, complete value, rfl⟩)
    | inr value => exact List.mem_append_right _ (List.mem_map.mpr ⟨value, complete value, rfl⟩)

end DisjointUnion

namespace FiniteGraph

abbrev ofEdges {α : Type u} [Enumeration α] [DecidableEq α]
    (edge : α → α → Prop) [DecidableRel edge] : FiniteGraph.{u} where
  Node := α
  enumeration := inferInstance
  equality := inferInstance
  edge := edge
  decideEdge := inferInstance

def disjointEdge (left right : FiniteGraph.{u}) : Sum left.Node right.Node → Sum left.Node right.Node → Prop
  | .inl source, .inl target => left.edge source target
  | .inr source, .inr target => right.edge source target
  | _, _ => False

instance disjointEdgeDecidable (left right : FiniteGraph.{u}) :
    DecidableRel (disjointEdge left right) := by
  intro source target
  cases source <;> cases target <;> unfold disjointEdge <;> infer_instance

abbrev disjointUnion (left right : FiniteGraph.{u}) : FiniteGraph.{u} :=
  ofEdges (disjointEdge left right)

def normalizedEqual (left right : FiniteGraph.{u}) (first : left.Node) (second : right.Node) : Bool :=
  (disjointUnion left right).canonicalEquivalent (.inl first) (.inr second)

def normalizedMember (left right : FiniteGraph.{u}) (member : left.Node) (set : right.Node) : Bool :=
  let joint := disjointUnion left right
  decide (joint.canonicalMember (joint.canonicalProjection (.inl member))
    (joint.canonicalProjection (.inr set)))

theorem normalizedEqual_kernel (left right : FiniteGraph.{u}) (first : left.Node) (second : right.Node) :
    normalizedEqual left right first second = true ↔
      (disjointUnion left right).canonicalProjection (.inl first) =
        (disjointUnion left right).canonicalProjection (.inr second) :=
  canonicalEquivalent_kernel _ _ _

theorem normalizedMember_eq_true (left right : FiniteGraph.{u}) (member : left.Node) (set : right.Node) :
    normalizedMember left right member set = true ↔
      ∃ child, right.edge set child ∧
        (disjointUnion left right).canonicalEquivalent (.inl member) (.inr child) = true := by
  simp only [normalizedMember, decide_eq_true_eq]
  change (disjointUnion left right).canonicalGraph.edge
    ((disjointUnion left right).canonicalProjection (.inr set))
    ((disjointUnion left right).canonicalProjection (.inl member)) ↔ _
  refine (canonicalProjection_edge (disjointUnion left right) (.inr set)
    ((disjointUnion left right).canonicalProjection (.inl member))).trans ?_
  constructor
  · rintro ⟨child, available, same⟩
    cases child with
    | inl child => exact False.elim available
    | inr child => exact ⟨child, available, (canonicalEquivalent_kernel _ _ _).mpr same.symm⟩
  · rintro ⟨child, available, same⟩
    exact ⟨.inr child, available, ((canonicalEquivalent_kernel _ _ _).mp same).symm⟩

end FiniteGraph

section RetainedRepresentatives

variable {α β : Type u} [DecidableEq β]

/-- Retain the first source entry of each unread class, in source order. -/
def selectFresh (key : α → β) (seen : List β) : List α → List α
  | [] => []
  | head :: tail => if key head ∈ seen then selectFresh key seen tail
      else head :: selectFresh key (key head :: seen) tail

theorem selectFresh_sublist (key : α → β) (seen : List β) (entries : List α) :
    (selectFresh key seen entries).Sublist entries := by
  induction entries generalizing seen with
  | nil => exact List.Sublist.refl []
  | cons head tail previous =>
    by_cases present : key head ∈ seen
    · simpa only [selectFresh, if_pos present] using (previous seen).cons head
    · simpa only [selectFresh, if_neg present] using (previous (key head :: seen)).cons_cons head

theorem selectFresh_support (key : α → β) (seen : List β) (entries : List α) (value : β) :
    value ∈ (selectFresh key seen entries).map key ↔
      value ∈ entries.map key ∧ value ∉ seen := by
  induction entries generalizing seen with
  | nil => simp only [selectFresh, List.map_nil, List.not_mem_nil, false_and]
  | cons head tail previous =>
    by_cases present : key head ∈ seen
    · simp only [selectFresh, if_pos present, previous, List.map_cons, List.mem_cons]
      constructor
      · rintro ⟨listed, unread⟩
        exact ⟨Or.inr listed, unread⟩
      · rintro ⟨same | listed, unread⟩
        · exact False.elim (unread (same ▸ present))
        · exact ⟨listed, unread⟩
    · simp only [selectFresh, if_neg present, List.map_cons, List.mem_cons, previous]
      constructor
      · rintro (same | ⟨listed, unread⟩)
        · exact ⟨Or.inl same, same ▸ present⟩
        · exact ⟨Or.inr listed, fun found => unread (Or.inr found)⟩
      · rintro ⟨same | listed, unread⟩
        · exact Or.inl same
        · by_cases same : value = key head
          · exact Or.inl same
          · exact Or.inr ⟨listed, fun found => found.elim same unread⟩

theorem selectFresh_nodup (key : α → β) (seen : List β) (entries : List α) :
    ((selectFresh key seen entries).map key).Nodup := by
  induction entries generalizing seen with
  | nil => exact List.nodup_nil
  | cons head tail previous =>
    by_cases present : key head ∈ seen
    · simpa only [selectFresh, if_pos present] using previous seen
    · simp only [selectFresh, if_neg present, List.map_cons, List.nodup_cons]
      refine ⟨?_, previous (key head :: seen)⟩
      intro listed
      exact ((selectFresh_support key (key head :: seen) tail (key head)).mp listed).2
        (List.mem_cons_self)

theorem selectFresh_first (key : α → β) (seen : List β) (entries : List α) (value : α)
    (selected : value ∈ selectFresh key seen entries) :
    ∃ before after, entries = before ++ value :: after ∧
      key value ∉ seen ∧ key value ∉ before.map key := by
  induction entries generalizing seen with
  | nil => simp only [selectFresh, List.not_mem_nil] at selected
  | cons head tail previous =>
    by_cases present : key head ∈ seen
    · simp only [selectFresh, if_pos present] at selected
      obtain ⟨before, after, split, unread, first⟩ := previous seen selected
      refine ⟨head :: before, after, congrArg (head :: ·) split, unread, ?_⟩
      simp only [List.map_cons, List.mem_cons]
      rintro (same | earlier)
      · exact unread (same ▸ present)
      · exact first earlier
    · simp only [selectFresh, if_neg present, List.mem_cons] at selected
      rcases selected with same | selected
      · subst value
        exact ⟨[], tail, rfl, present, List.not_mem_nil⟩
      · obtain ⟨before, after, split, unread, first⟩ := previous (key head :: seen) selected
        refine ⟨head :: before, after, congrArg (head :: ·) split,
          fun earlier => unread (List.mem_cons_of_mem (key head) earlier), ?_⟩
        simp only [List.map_cons, List.mem_cons]
        rintro (same | earlier)
        · exact unread (List.mem_cons.mpr (Or.inl same))
        · exact first earlier

end RetainedRepresentatives

namespace Presentations

open ProfileGraphReadout.Presentations

abbrev graph (presentation : Checked) : FiniteGraph := FiniteGraph.ofEdges (edge presentation)

def equal (first second : Checked) : Bool :=
  FiniteGraph.normalizedEqual (graph first) (graph second) (root first) (root second)

def member (element set : Checked) : Bool :=
  FiniteGraph.normalizedMember (graph element) (graph set) (root element) (root set)

/-- Authored child occurrences retain their endpoint and row order. -/
def sourceChildren (presentation : Checked) : List (Node presentation) :=
  (elements (α := Occurrence presentation (root presentation))).map
    (occurrenceTarget presentation (root presentation))

theorem mem_sourceChildren (presentation : Checked) (child : Node presentation) :
    child ∈ sourceChildren presentation ↔ edge presentation (root presentation) child := by
  simp only [sourceChildren, List.mem_map]
  constructor
  · rintro ⟨occurrence, _, rfl⟩
    exact occurrence_edge presentation (root presentation) occurrence
  · intro available
    obtain ⟨occurrence, same⟩ := (edge_iff_occurrence presentation (root presentation) child).mp available
    exact ⟨occurrence, complete occurrence, same⟩

theorem sourceChildren_values (presentation : Checked) :
    (sourceChildren presentation).map Fin.val = row presentation (root presentation) := by
  change ((List.finRange _).map (occurrenceTarget presentation (root presentation))).map Fin.val = _
  rw [List.map_map, ← List.ofFn_eq_map]
  exact List.ofFn_getElem

/-- Choose source witnesses for canonical member classes; an unrelated
global representative never replaces a retained child receipt. -/
def selectedChildren (presentation : Checked) : List (Node presentation) :=
  selectFresh (graph presentation).canonicalProjection [] (sourceChildren presentation)

def members (presentation : Checked) : List Nat :=
  (selectedChildren presentation).map Fin.val

theorem selectedChildren_sublist (presentation : Checked) :
    (selectedChildren presentation).Sublist (sourceChildren presentation) :=
  selectFresh_sublist _ _ _

theorem selectedChildren_edge (presentation : Checked) (child : Node presentation)
    (selected : child ∈ selectedChildren presentation) :
    edge presentation (root presentation) child :=
  (mem_sourceChildren presentation child).mp ((selectedChildren_sublist presentation).subset selected)

theorem selectedChildren_support (presentation : Checked) (child : Node presentation) :
    (graph presentation).canonicalProjection child ∈
      (selectedChildren presentation).map (graph presentation).canonicalProjection ↔
      (graph presentation).canonicalMember ((graph presentation).canonicalProjection child)
        ((graph presentation).canonicalProjection (root presentation)) := by
  constructor
  · intro selected
    obtain ⟨listed, _⟩ := (selectFresh_support (graph presentation).canonicalProjection []
      (sourceChildren presentation) ((graph presentation).canonicalProjection child)).mp selected
    obtain ⟨source, present, same⟩ := List.mem_map.mp listed
    exact ((graph presentation).canonicalProjection_edge (root presentation) _).mpr
      ⟨source, (mem_sourceChildren presentation source).mp present, same⟩
  · intro member
    obtain ⟨source, available, same⟩ :=
      ((graph presentation).canonicalProjection_edge (root presentation) _).mp member
    exact (selectFresh_support (graph presentation).canonicalProjection [] (sourceChildren presentation)
      ((graph presentation).canonicalProjection child)).mpr
        ⟨List.mem_map.mpr ⟨source, (mem_sourceChildren presentation source).mpr available, same⟩,
          List.not_mem_nil⟩

theorem selectedChildren_classes_nodup (presentation : Checked) :
    ((selectedChildren presentation).map (graph presentation).canonicalProjection).Nodup :=
  selectFresh_nodup _ _ _

theorem selectedChildren_first (presentation : Checked) (child : Node presentation)
    (selected : child ∈ selectedChildren presentation) :
    ∃ before after, sourceChildren presentation = before ++ child :: after ∧
      ∀ earlier ∈ before, (graph presentation).canonicalProjection earlier ≠
        (graph presentation).canonicalProjection child := by
  obtain ⟨before, after, split, _, first⟩ := selectFresh_first
    (graph presentation).canonicalProjection [] (sourceChildren presentation) child selected
  refine ⟨before, after, split, ?_⟩
  intro earlier listed same
  exact first (List.mem_map.mpr ⟨earlier, listed, same⟩)

theorem equal_kernel (first second : Checked) :
    equal first second = true ↔
      (FiniteGraph.disjointUnion (graph first) (graph second)).canonicalProjection (.inl (root first)) =
        (FiniteGraph.disjointUnion (graph first) (graph second)).canonicalProjection (.inr (root second)) :=
  FiniteGraph.normalizedEqual_kernel _ _ _ _

theorem member_eq_true (element set : Checked) :
    member element set = true ↔ ∃ child,
      edge set (root set) child ∧
        (FiniteGraph.disjointUnion (graph element) (graph set)).canonicalEquivalent
          (.inl (root element)) (.inr child) = true :=
  FiniteGraph.normalizedMember_eq_true _ _ _ _

theorem members_complete (presentation : Checked) (target : Nat) :
    target ∈ members presentation ↔
      ∃ child ∈ selectedChildren presentation, child.val = target := List.mem_map

theorem members_sublist (presentation : Checked) :
    (members presentation).Sublist (row presentation (root presentation)) := by
  rw [members, ← sourceChildren_values]
  exact (selectedChildren_sublist presentation).map Fin.val

theorem members_source_receipt (presentation : Checked) (target : Nat)
    (listed : target ∈ members presentation) :
    ∃ occurrence : Occurrence presentation (root presentation),
      (occurrenceTarget presentation (root presentation) occurrence).val = target := by
  obtain ⟨child, selected, same⟩ := (members_complete presentation target).mp listed
  obtain ⟨occurrence, paired⟩ := (edge_iff_occurrence presentation (root presentation) child).mp
    (selectedChildren_edge presentation child selected)
  exact ⟨occurrence, (congrArg Fin.val paired).trans same⟩

end Presentations

namespace Controls

open Mettapedia.SetTheory.AntiFoundation
open FiniteGraph

abbrev binary : FiniteGraph := ofEdges ProfileFiniteScottReadout.Controls.allBinaryEdge
abbrev loop : FiniteGraph := ofEdges ProfileFiniteScottReadout.Controls.unaryEdge

theorem binary_vertices_identified : binary.canonicalEquivalent 0 1 = true :=
  canonicalEquivalent_of_raw _ _ _ (by decide +kernel)

def recountEdge (source target : Fin 5) : Prop :=
  (source = 0 ∧ (target = 1 ∨ target = 2)) ∨ (source = 3 ∧ target = 4)

instance recountDecidable : DecidableRel recountEdge := by
  intro source target
  unfold recountEdge
  infer_instance

abbrev recount : FiniteGraph := ofEdges recountEdge

theorem recount_initial_raw_different :
    rawUnfoldingEquivalent recountEdge recountEdge 0 3 = false := by decide +kernel

theorem recount_one_pass_distinct : recount.projection 0 ≠ recount.projection 3 := by
  intro same
  have retained := (projection_kernel recount 0 3).mp same
  have accepted : rawUnfoldingEquivalent recountEdge recountEdge 0 3 = true :=
    decide_eq_true retained
  rw [recount_initial_raw_different] at accepted
  exact Bool.noConfusion accepted

theorem recount_second_pass_identifies :
    recount.quotient.projection (recount.projection 0) =
      recount.quotient.projection (recount.projection 3) := by decide +kernel

theorem recount_final_identifies : recount.canonicalEquivalent 0 3 = true := by
  apply (canonicalEquivalent_kernel recount 0 3).mpr
  change recount.iterateProjection 5 0 = recount.iterateProjection 5 3
  exact iterateProjection_equal_persists recount 2 3 0 3 recount_second_pass_identifies

/-- The first support quotient alone misses this equality. -/
theorem second_recount_is_necessary :
    recount.projection 0 ≠ recount.projection 3 ∧ recount.canonicalEquivalent 0 3 = true :=
  ⟨recount_one_pass_distinct, recount_final_identifies⟩

abbrev scott : FiniteGraph := ofEdges scottEdge

theorem scott_stopped : scott.stopped :=
  (stopped_iff_scottExtensional _).mpr ProfileFiniteScottReadout.Controls.scott_pair_scott_extensional

theorem scott_canonical_kernel (first second : Scott) :
    scott.canonicalEquivalent first second = true ↔ scottSafa first = scottSafa second := by
  apply (canonicalEquivalent_of_stopped scott scott_stopped first second).trans
  cases first <;> cases second <;> simp [scottSafa]

abbrev copiedScott : FiniteGraph := disjointUnion scott scott

def ordinaryCopied : copiedScott.Node → SSet
  | .inl value => scottSafa value
  | .inr _value => .omega

theorem ordinaryCopied_decoration : IsDecoration copiedScott.edge sMem ordinaryCopied := by
  intro source value
  cases source with
  | inl source =>
    constructor
    · intro member
      obtain ⟨child, available, same⟩ := (scottSafa_decoration source value).mp member
      exact ⟨.inl child, available, same⟩
    · rintro ⟨child, available, same⟩
      cases child with
      | inl child => exact (scottSafa_decoration source value).mpr ⟨child, available, same⟩
      | inr child => exact False.elim available
  | inr source =>
    constructor
    · intro member
      obtain ⟨child, available, same⟩ := (scott_collapse_safa source value).mp member
      exact ⟨.inr child, available, same⟩
    · rintro ⟨child, available, same⟩
      cases child with
      | inl child => exact False.elim available
      | inr child => exact (scott_collapse_safa source value).mpr ⟨child, available, same⟩

theorem copied_raw_identifies : copiedScott.rawRelation (.inl .s1) (.inr .s1) := by decide +kernel

theorem copied_canonical_identifies :
    copiedScott.canonicalEquivalent (.inl .s1) (.inr .s1) = true :=
  canonicalEquivalent_of_raw _ _ _ copied_raw_identifies

theorem copied_ordinary_separates : ordinaryCopied (.inl .s1) ≠ ordinaryCopied (.inr .s1) := by
  decide +kernel

/-- Ordinary solutions of set equations do not license canonical merges. -/
theorem ordinary_decoration_does_not_justify_canonical_merges :
    ¬ ∀ decoration : copiedScott.Node → SSet,
      IsDecoration copiedScott.edge sMem decoration →
      ∀ first second, copiedScott.canonicalEquivalent first second = true → decoration first = decoration second := by
  intro purported
  exact copied_ordinary_separates
    (purported ordinaryCopied ordinaryCopied_decoration _ _ copied_canonical_identifies)

open ProfileGraphReadout.Presentations

def binarySource : Checked := ⟨⟨0, [[0, 1], [0, 1]]⟩, by decide⟩
def scottSource0 : Checked := ⟨⟨0, [[0], [0, 1]]⟩, by decide⟩
def scottSource1 : Checked := ⟨⟨1, [[0], [0, 1]]⟩, by decide⟩
def recountSource0 : Checked := ⟨⟨0, [[1, 2], [], [], [4], []]⟩, by decide⟩
def recountSource3 : Checked := ⟨⟨3, [[1, 2], [], [], [4], []]⟩, by decide⟩
def unrelatedEmpty : Checked := ⟨⟨2, [[], [], [1]]⟩, by decide⟩
def authoredOrder : Checked := ⟨⟨2, [[], [0], [1, 0]]⟩, by decide⟩
def firstEmptyOccurrence : Checked := ⟨⟨2, [[], [], [1, 0]]⟩, by decide⟩

theorem authored_member_origin_retained : Presentations.members unrelatedEmpty = [1] := by decide +kernel

theorem authored_member_order_retained : Presentations.members authoredOrder = [1, 0] := by decide +kernel

theorem first_authored_representative_retained : Presentations.members firstEmptyOccurrence = [1] := by
  decide +kernel

theorem global_origin_is_a_different_readout :
    ((Presentations.graph unrelatedEmpty).memberOrigins (root unrelatedEmpty)).map Fin.val = [0] := by
  decide +kernel

end Controls

end Mettapedia.SetTheory.Profiles.ProfileFiniteScottCollapse
