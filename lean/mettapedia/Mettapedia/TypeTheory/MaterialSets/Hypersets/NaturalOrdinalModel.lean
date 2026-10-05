import Mettapedia.TypeTheory.MaterialSets.Hypersets.Operations
import Mettapedia.TypeTheory.MaterialSets.Hypersets.WellFounded

/-!
# Constructed material natural ordinals and infinity

The decreasing natural-number graph constructs every finite ordinal directly.
A new root over all of its generated pointed subgraphs constructs their
infinite material set at the original graph bound. Zero, successor, membership
induction and the least-inductive-set property are proved for this actual
object. Its members are well-founded even though the ambient carrier contains
the Quine atom.

The map from host naturals onto material members is explicitly defined and
proved injective and surjective. No inverse function is selected from the
propositional surjectivity proof. An executable host-valued decoder is a
separate capability from an infinite material set and its propositional laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel

universe u

def edge (parent child : ULift.{u, 0} Nat) : Prop := child.down < parent.down

def graph (number : Nat) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.generated edge (ULift.up number)

def ordinal (number : Nat) : HSet.{u} := HSet.mk (graph number)

theorem member_ordinal (number : Nat) (value : HSet.{u}) :
    value ∈ ordinal number ↔ ∃ earlier : Nat, earlier < number ∧ ordinal earlier = value := by
  change value ∈ HSet.decorate edge (ULift.up number) ↔ _
  refine HSet.mem_decorate.trans ?_
  constructor
  · rintro ⟨earlier, precedes, same⟩
    exact ⟨earlier.down, precedes, same⟩
  · rintro ⟨earlier, precedes, same⟩
    exact ⟨ULift.up earlier, precedes, same⟩

theorem ordinal_zero : ordinal 0 = (∅ : HSet.{u}) := by
  apply HSet.eq_empty_iff.mpr
  intro value belongs
  obtain ⟨earlier, impossible, _⟩ := (member_ordinal 0 value).mp belongs
  exact Nat.not_lt_zero earlier impossible

def successor (value : HSet.{u}) : HSet.{u} := insert value value

theorem ordinal_successor (number : Nat) :
    ordinal (number + 1) = successor (ordinal number : HSet.{u}) := by
  apply HSet.ext
  intro value
  refine (member_ordinal (number + 1) value).trans ?_
  change (∃ earlier, earlier < number + 1 ∧ ordinal earlier = value) ↔
    value ∈ insert (ordinal number) (ordinal number)
  rw [HSet.mem_insert_iff, member_ordinal]
  constructor
  · rintro ⟨earlier, precedes, same⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ precedes) with below | equal
    · exact Or.inr ⟨earlier, below, same⟩
    · exact Or.inl (same.symm.trans (congrArg ordinal equal))
  · rintro (same | ⟨earlier, precedes, earlierSame⟩)
    · exact ⟨number, Nat.lt_succ_self number, same.symm⟩
    · exact ⟨earlier, Nat.lt_succ_of_lt precedes, earlierSame⟩

theorem ordinal_wellFounded (number : Nat) : (ordinal number : HSet.{u}).WF := by
  induction number with
  | zero => exact ordinal_zero.symm ▸ HSet.wf_empty
  | succ number earlier =>
    exact (ordinal_successor number).symm ▸ earlier.insert earlier

theorem ordinal_not_selfMember (number : Nat) :
    (ordinal number : HSet.{u}) ∉ ordinal number :=
  (ordinal_wellFounded number).notMem_self

theorem ordinal_injective : Function.Injective (ordinal : Nat → HSet.{u}) := by
  intro first second same
  rcases Nat.lt_trichotomy first second with earlier | equal | later
  · have belongs : ordinal first ∈ ordinal second :=
      (member_ordinal second (ordinal first)).mpr ⟨first, earlier, rfl⟩
    exact (ordinal_not_selfMember first (same.symm ▸ belongs)).elim
  · exact equal
  · have belongs : ordinal second ∈ ordinal first :=
      (member_ordinal first (ordinal second)).mpr ⟨second, later, rfl⟩
    exact (ordinal_not_selfMember second (same ▸ belongs)).elim

theorem ordinal_member_ordinal (first second : Nat) :
    (ordinal first : HSet.{u}) ∈ ordinal second ↔ first < second := by
  refine (member_ordinal second (ordinal first)).trans ?_
  constructor
  · rintro ⟨earlier, precedes, same⟩
    exact ordinal_injective same ▸ precedes
  · intro precedes
    exact ⟨first, precedes, rfl⟩

/-- The root has every finite ordinal as a child. Its graph is constructed
uniformly from the entire small natural index carrier. -/
def naturals : HSet.{u} :=
  HSet.range (fun number : ULift.{u, 0} Nat => graph number.down)

theorem member_naturals (value : HSet.{u}) :
    value ∈ naturals ↔ ∃ number : Nat, ordinal number = value := by
  refine HSet.mem_range.trans ?_
  constructor
  · rintro ⟨number, same⟩
    exact ⟨number.down, same⟩
  · rintro ⟨number, same⟩
    exact ⟨ULift.up number, same⟩

theorem ordinal_member_naturals (number : Nat) :
    (ordinal number : HSet.{u}) ∈ naturals :=
  (member_naturals _).mpr ⟨number, rfl⟩

theorem zero_member_naturals : (∅ : HSet.{u}) ∈ naturals :=
  ordinal_zero ▸ ordinal_member_naturals 0

theorem successor_member_naturals {value : HSet.{u}} (belongs : value ∈ naturals) :
    successor value ∈ naturals := by
  obtain ⟨number, same⟩ := (member_naturals value).mp belongs
  exact (ordinal_successor number).trans (congrArg successor same) ▸
    ordinal_member_naturals (number + 1)

theorem infinity : ∃ carrier : HSet.{u}, (∅ : HSet.{u}) ∈ carrier ∧
    ∀ value ∈ carrier, successor value ∈ carrier :=
  ⟨naturals, zero_member_naturals, fun _ belongs => successor_member_naturals belongs⟩

/-- Induction permits every material predicate; it is local to the
constructed natural set, not membership induction for all hypersets. -/
theorem induction (predicate : HSet.{u} → Prop) (zero : predicate ∅)
    (step : ∀ value ∈ naturals, predicate value → predicate (successor value)) :
    ∀ value ∈ naturals, predicate value := by
  have numbered : ∀ number : Nat, predicate (ordinal number) := by
    intro number
    induction number with
    | zero => exact ordinal_zero.symm ▸ zero
    | succ number earlier =>
      exact (ordinal_successor number).symm ▸
        step (ordinal number) (ordinal_member_naturals number) earlier
  intro value belongs
  obtain ⟨number, same⟩ := (member_naturals value).mp belongs
  exact same ▸ numbered number

theorem least_inductive (carrier : HSet.{u}) (zero : (∅ : HSet.{u}) ∈ carrier)
    (step : ∀ value ∈ carrier, successor value ∈ carrier) : naturals ⊆ carrier :=
  induction (fun value => value ∈ carrier) zero (fun value _ belongs => step value belongs)

theorem naturals_transitive : ∀ value ∈ (naturals : HSet.{u}), value ⊆ naturals := by
  intro value belongs member included
  obtain ⟨number, same⟩ := (member_naturals value).mp belongs
  obtain ⟨earlier, _, earlierSame⟩ :=
    (member_ordinal number member).mp (same.symm ▸ included)
  exact earlierSame ▸ ordinal_member_naturals earlier

theorem naturals_wellFounded : (naturals : HSet.{u}).WF := by
  apply HSet.wf_of_forall_mem
  intro value belongs
  obtain ⟨number, same⟩ := (member_naturals value).mp belongs
  exact same ▸ ordinal_wellFounded number

def naturalMembers (number : Nat) : {value : HSet.{u} // value ∈ naturals} :=
  ⟨ordinal number, ordinal_member_naturals number⟩

theorem naturalMembers_injective : Function.Injective (naturalMembers :
    Nat → {value : HSet.{u} // value ∈ naturals}) :=
  fun _ _ same => ordinal_injective (congrArg Subtype.val same)

theorem naturalMembers_surjective : Function.Surjective (naturalMembers :
    Nat → {value : HSet.{u} // value ∈ naturals}) := by
  intro member
  obtain ⟨number, same⟩ := (member_naturals member.val).mp member.property
  exact ⟨number, Subtype.ext same⟩

namespace Controls

theorem zero_one_distinguished : (ordinal 0 : HSet.{u}) ≠ ordinal 1 :=
  fun same => Nat.zero_ne_one (ordinal_injective same)

theorem quine_not_natural : HSet.quineAtom.{u} ∉ naturals := by
  intro belongs
  exact HSet.not_wf_quineAtom (naturals_wellFounded.mem belongs)

theorem no_finite_ordinal_is_all_naturals (number : Nat) :
    (ordinal number : HSet.{u}) ≠ naturals := by
  intro same
  exact ordinal_not_selfMember number (same.symm ▸ ordinal_member_naturals number)

theorem naturals_not_empty : (naturals : HSet.{u}) ≠ ∅ :=
  fun same => HSet.notMem_empty ∅ (same ▸ zero_member_naturals)

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel
