import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassMembers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedMemberGraphs

/-!
# Small actual material witnesses of discrete identity

An equality predicate separates the singleton empty hyperset. Its actual
graph has a small occurrence-class member carrier. Explicit encode/decode
maps and inverse laws represent endpoint equality without selecting a graph
occurrence or increasing the bound of a displayed presheaf fibre.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafIdentityWitness

open AccessiblePointedGraph

universe u
variable {T : Type u}

def graph (left right : T) : AccessiblePointedGraph.{u} :=
  separationGraph (singletonGraph empty) (fun _ => left = right)

theorem mk_graph (left right : T) :
    HSet.mk (graph left right) = HSet.sep (fun _ => left = right) {∅} := by
  rw [graph, mk_separationGraph, mk_singletonGraph, HSet.mk_empty]

abbrev Witness (left right : T) := PowerMemberClass (graph left right)

theorem member_condition {left right : T} (witness : Witness left right) :
    (classMember (graph left right) witness).1 = ∅ ∧ left = right := by
  have belongs : classValue (graph left right) witness.1 ∈ picture (graph left right) :=
    (classMember (graph left right) witness).2
  rw [picture_eq_mk, mk_graph, HSet.mem_sep, HSet.mem_singleton] at belongs
  exact belongs

theorem decode {left right : T} (witness : Witness left right) : left = right := (member_condition witness).2

def encode {left right : T} (same : left = right) : Witness left right :=
  (powerMemberEquiv (graph left right)).symm ⟨∅, by
    rw [picture_eq_mk, mk_graph, HSet.mem_sep, HSet.mem_singleton]
    exact ⟨rfl, same⟩⟩

theorem encode_decode {left right : T} (witness : Witness left right) : encode (decode witness) = witness := by
  apply (powerMemberEquiv (graph left right)).injective
  change powerMemberEquiv (graph left right) ((powerMemberEquiv (graph left right)).symm _) = _
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext (member_condition witness).1.symm

def witnessEquiv (left right : T) : Witness left right ≃ ULift.{u, 0} (PLift (left = right)) where
  toFun witness := ⟨⟨decode witness⟩⟩
  invFun same := encode same.down.down
  left_inv := encode_decode
  right_inv _ := rfl

instance {left right : T} : Subsingleton (Witness left right) :=
  ⟨fun first second => (witnessEquiv left right).injective
    (Subsingleton.elim (witnessEquiv left right first) (witnessEquiv left right second))⟩

theorem classValue_encode {left right : T} (same : left = right) :
    classValue (graph left right) (encode same).1 = ∅ :=
  (member_condition (encode same)).1

theorem graph_empty_of_distinct {left right : T} (different : left ≠ right) : HSet.mk (graph left right) = ∅ := by
  rw [mk_graph]
  apply HSet.eq_empty_iff.mpr
  intro value belongs
  exact different (HSet.mem_sep.mp belongs).2

theorem witness_empty_of_distinct {left right : T} (different : left ≠ right) : ¬ Nonempty (Witness left right) :=
  fun ⟨witness⟩ => different (decode witness)

theorem graph_reflexive (term : T) : HSet.mk (graph term term) = {∅} := by
  rw [mk_graph]
  apply HSet.ext
  intro value
  rw [HSet.mem_sep]
  exact and_iff_left rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafIdentityWitness
