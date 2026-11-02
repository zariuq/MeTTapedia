import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedSequentialization

/-!
# Finite guard-cut graphs ordered by the existing Kahn scheduler

Vertices are rule-use occurrences. Resource edges retain shared reads;
guard edges select the exact predecessor set at a guarded event. Different
choices of cut yield different graphs rather than one asserted process order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutOrders

open Mettapedia.Algorithms.WellFoundedServices
open LinearConnectionLayout

universe uT uO
variable {T : Type uT} {O : Type uO} [DecidableEq O] {n : Nat}

def ResourceEdge (events : Fin n → Event T O) (first second : Fin n) : Prop :=
  (∃ o ∈ (events first).2.made, o ∈ (events second).2.taken ∨ o ∈ (events second).2.read) ∨
    (first ≠ second ∧ ∃ o ∈ (events first).2.read, o ∈ (events second).2.taken)

def GuardEdge (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    (first second : Fin n) : Prop :=
  ((events second).1.checks ≠ [] ∧ first ∈ cuts second) ∨
    ((events first).1.checks ≠ [] ∧ second ≠ first ∧ second ∉ cuts first)

def Edge (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    (first second : Fin n) : Prop := ResourceEdge events first second ∨ GuardEdge events cuts first second

instance edgeDecidable (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n)) :
    DecidableRel (Edge events cuts) := by
  intro first second
  unfold Edge ResourceEdge GuardEdge
  infer_instance

def catalogue (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n)) : Catalogue (Fin n) where
  items := List.finRange n
  deps second := (List.finRange n).filter fun first => decide (Edge events cuts first second)

@[simp] theorem mem_deps (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    (first second : Fin n) :
    first ∈ (catalogue events cuts).deps second ↔ Edge events cuts first second := by
  simp [catalogue]

def Acyclic (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n)) : Prop :=
  ∀ event, ¬ Relation.TransGen (Edge events cuts) event event

def order? (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n)) : Option (List (Fin n)) :=
  (catalogue events cuts).acyclic?.map fun certificate => certificate.order

theorem order?_isSome_iff (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n)) :
    (order? events cuts).isSome ↔ Acyclic events cuts := by
  have uses : (catalogue events cuts).Uses = Function.swap (Edge events cuts) := by
    funext second first
    exact propext (by simp [Catalogue.Uses, catalogue])
  simp only [order?, Option.isSome_map, Catalogue.acyclic?_isSome_iff, uses,
    Relation.transGen_swap, Acyclic]

theorem order?_spec (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    {order : List (Fin n)} (computed : order? events cuts = some order) :
    (catalogue events cuts).Respects order ∧ ∀ event, event ∈ order := by
  obtain ⟨certificate, _, same⟩ := Option.map_eq_some_iff.mp computed
  subst order
  exact ⟨certificate.respects, fun event => certificate.covers event (List.mem_finRange _)⟩

theorem enumeration_perm (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    {order : List (Fin n)} (respects : (catalogue events cuts).Respects order)
    (covers : ∀ event, event ∈ order) : order.Perm (List.finRange n) := by
  apply (List.perm_ext_iff_of_nodup respects.nodup (List.nodup_finRange n)).mpr
  intro event
  exact ⟨fun _ => List.mem_finRange _, fun _ => covers event⟩

theorem supplier_in_prefix (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    {order earlier : List (Fin n)} {current supplier : Fin n} {later : List (Fin n)}
    (respects : (catalogue events cuts).Respects order) (covers : ∀ event, event ∈ order)
    (decomposition : order = earlier ++ current :: later) (edge : Edge events cuts supplier current) :
    supplier ∈ earlier := by
  have dependency : supplier ∈ (catalogue events cuts).deps current := (mem_deps ..).mpr edge
  have member := covers supplier
  rw [decomposition, List.mem_append, List.mem_cons] at member
  rcases member with inEarlier | same | inLater
  · exact inEarlier
  · subst supplier
    exact False.elim (respects.irrefl current (covers current) dependency)
  · have pairwise := respects.pairwise
    rw [decomposition] at pairwise
    have suffix := (List.pairwise_append.mp pairwise).2.1
    exact False.elim ((List.pairwise_cons.mp suffix).1 supplier inLater dependency)

def RealizesCuts (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    (order : List (Fin n)) : Prop :=
  ∀ earlier current later, order = earlier ++ current :: later →
    (events current).1.checks ≠ [] → earlier.toFinset = cuts current

theorem realizes_cuts (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    {order : List (Fin n)} (respects : (catalogue events cuts).Respects order)
    (covers : ∀ event, event ∈ order) : RealizesCuts events cuts order := by
  intro earlier current later decomposition guarded
  have split := respects.nodup
  rw [decomposition] at split
  have notEarlier : current ∉ earlier := fun member =>
    (List.nodup_append.mp split).2.2 current member current List.mem_cons_self rfl
  apply Finset.ext
  intro event
  constructor
  · intro member
    have inEarlier := List.mem_toFinset.mp member
    by_contra notCut
    have different : event ≠ current := by intro same; subst event; exact notEarlier inEarlier
    have edge : Edge events cuts current event := Or.inr (Or.inr ⟨guarded, different, notCut⟩)
    have pairwise := respects.pairwise
    rw [decomposition] at pairwise
    exact (List.pairwise_append.mp pairwise).2.2 event inEarlier current List.mem_cons_self
      ((mem_deps ..).mpr edge)
  · intro member
    exact List.mem_toFinset.mpr (supplier_in_prefix events cuts respects covers decomposition
      (Or.inr (Or.inl ⟨guarded, member⟩)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutOrders
