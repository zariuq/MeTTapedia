import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionCompleteness
import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis
import Mathlib.Data.List.FinRange

/-!
# Unordered occurrence connections and the existing checked Kahn service

Vertices are event occurrence indices, not rule values. An edge goes from
an event producing a physical identity to an event consuming that identity.
Acyclicity means absence of a nonempty graph path from a vertex to itself.
It is defined independently of source execution or a supplied total order.

The existing catalogue's computable, measured Kahn wave scheduler supplies
an enumeration exactly when this independent graph has no cycle. Catalogue
dependencies run opposite to producer/use edges; that correspondence is
proved explicitly. Equal raw rules remain different indexed occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedOccurrenceConnections

open Mettapedia.Algorithms.WellFoundedServices
open LinearConnectionLayout

universe uT uO
variable {T : Type uT} {O : Type uO} [DecidableEq O] {n : Nat}

def roster (events : Fin n → Event T O) : List (Event T O) := (List.finRange n).map events

def Edge (events : Fin n → Event T O) (producer consumer : Fin n) : Prop :=
  ∃ occurrence ∈ (events producer).2.made, occurrence ∈ (events consumer).2.taken

instance edgeDecidable (events : Fin n → Event T O) : DecidableRel (Edge events) := by
  intro producer consumer
  unfold Edge
  infer_instance

/-- A nonempty closed producer/use path is forbidden, independently of any
enumeration. In particular this excludes a self-supplying event. -/
def Acyclic (events : Fin n → Event T O) : Prop := ∀ event, ¬ Relation.TransGen (Edge events) event event

def catalogue (events : Fin n → Event T O) : Catalogue (Fin n) where
  items := List.finRange n
  deps consumer := (List.finRange n).filter fun producer => decide (Edge events producer consumer)

theorem catalogue_uses (events : Fin n → Event T O) (consumer producer : Fin n) :
    (catalogue events).Uses consumer producer ↔ Edge events producer consumer := by
  simp [Catalogue.Uses, catalogue]

theorem uses_eq_swap (events : Fin n → Event T O) :
    (catalogue events).Uses = Function.swap (Edge events) := by
  funext consumer producer
  exact propext (catalogue_uses events consumer producer)

theorem acyclic_iff_no_dependency_cycles (events : Fin n → Event T O) :
    Acyclic events ↔ ∀ event, ¬ Relation.TransGen (catalogue events).Uses event event := by
  rw [uses_eq_swap]
  simp only [Acyclic, Relation.transGen_swap]

/-- This calls the existing measured Kahn scheduler and returns its checked
flattened wave order. It does not enumerate permutations. -/
def order? (events : Fin n → Event T O) : Option (List (Fin n)) :=
  (catalogue events).acyclic?.map fun certificate => certificate.order

theorem order?_isSome_iff (events : Fin n → Event T O) : (order? events).isSome ↔ Acyclic events := by
  simp only [order?, Option.isSome_map, Catalogue.acyclic?_isSome_iff]
  exact (acyclic_iff_no_dependency_cycles events).symm

theorem order?_spec (events : Fin n → Event T O) {order : List (Fin n)}
    (computed : order? events = some order) :
    (catalogue events).Respects order ∧ ∀ event, event ∈ order := by
  obtain ⟨certificate, _, same⟩ := Option.map_eq_some_iff.mp computed
  subst order
  exact ⟨certificate.respects, fun event => certificate.covers event (List.mem_finRange _)⟩

theorem enumeration_perm (events : Fin n → Event T O) {order : List (Fin n)}
    (respects : (catalogue events).Respects order) (covers : ∀ event, event ∈ order) :
    order.Perm (List.finRange n) := by
  apply (List.perm_ext_iff_of_nodup respects.nodup (List.nodup_finRange n)).mpr
  intro event
  exact ⟨fun _ => List.mem_finRange _, fun _ => covers event⟩

theorem order?_perm (events : Fin n → Event T O) {order : List (Fin n)}
    (computed : order? events = some order) : order.Perm (List.finRange n) :=
  enumeration_perm events (order?_spec events computed).1 (order?_spec events computed).2

theorem edge_precedes (events : Fin n → Event T O) {order : List (Fin n)}
    (respects : (catalogue events).Respects order) (covers : ∀ event, event ∈ order)
    {producer consumer : Fin n} (edge : Edge events producer consumer) :
    order.idxOf producer < order.idxOf consumer :=
  respects.idxOf_lt (covers consumer) (covers producer) (by simpa [catalogue] using edge)

theorem acyclic_of_enumeration (events : Fin n → Event T O) {order : List (Fin n)}
    (respects : (catalogue events).Respects order) (covers : ∀ event, event ∈ order) : Acyclic events :=
  (acyclic_iff_no_dependency_cycles events).mpr
    (respects.acyclic (fun event _ => covers event))

theorem exists_computed_order (events : Fin n → Event T O) (acyclic : Acyclic events) :
    ∃ order, order? events = some order :=
  Option.isSome_iff_exists.mp ((order?_isSome_iff events).mpr acyclic)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedOccurrenceConnections
