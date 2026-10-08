import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceMaterial
import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceDependence

/-!
# Material controls for actual reachability receipts and their consumers

The atom dictionary covers arbitrary natural vertices. Full material receipt
readings distinguish the direct and indirect authored derivations, whereas
material fact sets merge their common conclusion. The computed finite-batch
recovery supports a destination-indexed whole section. Route selection does
not descend, even though its constant family does.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence.Controls

attribute [local instance] Finite.membership

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilySectionDescent

private def atomParts : Atom → Nat × Nat × Nat
  | .selected start finish => (0, start, finish)
  | .edge start finish => (1, start, finish)
  | .reaches start finish => (2, start, finish)

private theorem atomParts_injective : Function.Injective atomParts := by
  intro first second same
  cases first <;> cases second <;> simp_all [atomParts]

def atomCoding : ArgumentCoding Atom where
  graph atom := AccessiblePointedGraph.kpairGraph
    ((ArgumentCoding.ofEncodable Nat).graph (atomParts atom).1)
    (AccessiblePointedGraph.kpairGraph
      ((ArgumentCoding.ofEncodable Nat).graph (atomParts atom).2.1)
      ((ArgumentCoding.ofEncodable Nat).graph (atomParts atom).2.2))
  injective := by
    intro first second same
    simp only [AccessiblePointedGraph.mk_kpairGraph] at same
    have outer := HSet.kpair_inj.mp same
    have inner := HSet.kpair_inj.mp outer.2
    apply atomParts_injective
    exact Prod.ext ((ArgumentCoding.ofEncodable Nat).injective outer.1)
      (Prod.ext ((ArgumentCoding.ofEncodable Nat).injective inner.1)
        ((ArgumentCoding.ofEncodable Nat).injective inner.2))

private def originNumber : Origin → Nat
  | .nearQuery => 0
  | .farQuery => 1
  | .firstEdge => 2
  | .secondEdge => 3
  | .directEdge => 4

private theorem originNumber_injective : Function.Injective originNumber := by
  intro first second same
  cases first <;> cases second <;> simp_all [originNumber]

def originCoding : ArgumentCoding Origin where
  graph origin := (ArgumentCoding.ofEncodable Nat).graph (originNumber origin)
  injective := fun _ _ same => originNumber_injective
    ((ArgumentCoding.ofEncodable Nat).injective same)

theorem material_derivations_distinct (n : Nat) :
    Material.reading atomCoding originCoding (direct n) ≠
      Material.reading atomCoding originCoding (indirect n) :=
  fun same => different_derivations n ((Material.reading_kernel _ _ _ _).mp same)

theorem material_facts_agree (n : Nat) :
    atomCoding.reading (direct n).fact = atomCoding.reading (indirect n).fact := rfl

theorem material_same_support_distinct_batches (n : Nat) :
    HSet.mk (Material.supportGraph atomCoding [direct n, direct n]) =
        HSet.mk (Material.supportGraph atomCoding (answers n)) ∧
      HSet.mk (Material.batchGraph atomCoding originCoding [direct n, direct n]) ≠
        HSet.mk (Material.batchGraph atomCoding originCoding (answers n)) := by
  constructor
  · apply (Material.support_kernel _ _ _).mpr
    rfl
  · intro same
    exact repeating_one_path_is_not_both_paths n ((Material.batch_kernel _ _ _ _).mp same)

theorem material_order_retained (n : Nat) :
    HSet.mk (Material.batchGraph atomCoding originCoding [direct n, indirect n]) ≠
      HSet.mk (Material.batchGraph atomCoding originCoding [indirect n, direct n]) := by
  intro same
  exact different_derivations n (List.cons.inj ((Material.batch_kernel _ _ _ _).mp same)).1

theorem material_repetition_retained (n : Nat) :
    HSet.mk (Material.batchGraph atomCoding originCoding [direct n]) ≠
      HSet.mk (Material.batchGraph atomCoding originCoding [direct n, direct n]) := by
  intro same
  have lengths := congrArg List.length ((Material.batch_kernel _ _ _ _).mp same)
  cases lengths

def supportedDestination (n : Nat) :
    ∀ member : BatchMember (answers n), Fin (member.val.destination + 1) :=
  (batchSectionEquiv (payloadFamily n) (answers n)).symm
    ⟨fun index => destination ((answers n).get index),
      compatible_on_batch (payloadFamily n) destination (destination_compatible n) (answers n)⟩

theorem supportedDestination_recovers (n : Nat) (index : BatchOccurrence (answers n)) :
    (batchSectionEquiv (payloadFamily n) (answers n) (supportedDestination n)).val index =
      destination ((answers n).get index) := by
  exact congrFun (congrArg Subtype.val ((batchSectionEquiv (payloadFamily n) (answers n)).apply_symm_apply
    ⟨fun index => destination ((answers n).get index),
      compatible_on_batch (payloadFamily n) destination (destination_compatible n) (answers n)⟩)) index

theorem route_not_batch_compatible (n : Nat) :
    ¬ Compatible (batchFamily (routeFamily n) (answers n))
      (fun index => usedIntermediate ((answers n).get index)) := by
  intro compatible
  have same := compatible ⟨0, by change 0 < 2; decide⟩ ⟨1, by change 1 < 2; decide⟩ rfl
  have values := eq_of_heq (Sigma.mk.inj_iff.mp same).2
  exact Bool.false_ne_true values

theorem route_not_from_batch_facts (n : Nat) :
    ¬ ∃ observed : ∀ _member : BatchMember (answers n), Bool,
      (batchSectionEquiv (routeFamily n) (answers n) observed).val =
        (fun index => usedIntermediate ((answers n).get index)) :=
  fun existsConsumer => route_not_batch_compatible n
    ((batch_compatible_iff_descends (routeFamily n) (answers n) _).mpr existsConsumer)

end Mettapedia.GSLT.ProgrammableSpaceEvidence.Controls
