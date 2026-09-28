import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Irreducible
import Mathlib.Order.WithBot
import Mathlib.Tactic.Tauto

/-!
# Confidentiality and integrity labels

Combining dependencies takes the join in the information-flow order. A product
of confidentiality with order-dual integrity therefore raises confidentiality
and lowers integrity. These facts need only lattices, not distributivity.

The optional meet/addition, join/multiplication semiring needs a bounded
distributive lattice. Its algebraic laws do not establish noninterference.
Even in a distributive lattice, a meet of alternative derivation labels can
appear observable when no derivation is observable. `InfPrime` is the precise
clearance condition used below; the compartment counterexample shows why it
cannot be omitted. At top clearance an empty meet also needs a presence bit.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InformationFlow

universe u v

-- Use the constructive finite-order instances, rather than inherited
-- complete-Boolean-algebra instances, in the executable controls.
local instance : SemilatticeInf Bool := Bool.instDistribLattice.toLattice.toSemilatticeInf
local instance : SemilatticeSup Bool := Bool.instDistribLattice.toLattice.toSemilatticeSup
local instance : OrderTop Bool := Bool.instBoundedOrder.toOrderTop

/-- The usual confidentiality order paired with the opposite integrity order. -/
abbrev Label (Confidentiality : Type u) (Integrity : Type v) :=
  Confidentiality × OrderDual Integrity

namespace Label

variable {C : Type u} {I : Type v}

@[simp] theorem le_iff [Preorder C] [Preorder I] (a b : Label C I) :
    a ≤ b ↔ a.1 ≤ b.1 ∧ OrderDual.ofDual b.2 ≤ OrderDual.ofDual a.2 :=
  Iff.rfl

/-- A result depending on both sources cannot have less confidentiality or
more integrity than their join permits. -/
theorem sup_le_iff [Lattice C] [Lattice I] (a b destination : Label C I) :
    a ⊔ b ≤ destination ↔
      a.1 ≤ destination.1 ∧ b.1 ≤ destination.1 ∧
      OrderDual.ofDual destination.2 ≤ OrderDual.ofDual a.2 ∧
      OrderDual.ofDual destination.2 ≤ OrderDual.ofDual b.2 := by
  change (a.1 ⊔ b.1 ≤ destination.1 ∧
    OrderDual.ofDual destination.2 ≤
      OrderDual.ofDual a.2 ⊓ OrderDual.ofDual b.2) ↔ _
  simp only [_root_.sup_le_iff, le_inf_iff]
  tauto

/-- Computing the dependency join takes confidentiality join and integrity
meet, with no special product-label implementation. -/
theorem join_confidentiality_integrity [Lattice C] [Lattice I]
    (a b : Label C I) :
    (a ⊔ b).1 = a.1 ⊔ b.1 ∧
      OrderDual.ofDual (a ⊔ b).2 =
        OrderDual.ofDual a.2 ⊓ OrderDual.ofDual b.2 := by
  exact ⟨rfl, rfl⟩

end Label

/-- A bounded distributive lattice as a commutative semiring: alternatives
take meet, combined sources take join, zero is top, and one is bottom.
This is an explicit structure, not a global instance on security labels. -/
@[instance_reducible] def infSupSemiring (L : Type u)
    [DistribLattice L] [BoundedOrder L] : CommSemiring L := by
  letI : Add L := ⟨(· ⊓ ·)⟩
  letI : Mul L := ⟨(· ⊔ ·)⟩
  letI : Zero L := ⟨⊤⟩
  letI : One L := ⟨⊥⟩
  exact {
    add_assoc := inf_assoc
    zero_add := top_inf_eq
    add_zero := inf_top_eq
    add_comm := inf_comm
    nsmul := nsmulRec
    mul_assoc := sup_assoc
    one_mul := bot_sup_eq
    mul_one := sup_bot_eq
    mul_comm := sup_comm
    left_distrib := sup_inf_left
    right_distrib := sup_inf_right
    zero_mul := top_sup_eq
    mul_zero := sup_top_eq
    natCast := fun n => if n = 0 then ⊤ else ⊥
    natCast_zero := rfl
    natCast_succ := by
      intro n
      change (if n + 1 = 0 then ⊤ else ⊥) =
        (if n = 0 then ⊤ else ⊥) ⊓ ⊥
      simp }

/-- The annotation attached to a finite set of alternative derivations when
meet is chosen as addition. It deliberately contains no multiplicity. -/
def alternativeLabel {L : Type u} [SemilatticeInf L] [OrderTop L]
    (labels : List L) : L :=
  labels.foldr (· ⊓ ·) ⊤

@[simp] theorem alternativeLabel_nil {L : Type u} [SemilatticeInf L] [OrderTop L] :
    alternativeLabel ([] : List L) = ⊤ := rfl

@[simp] theorem alternativeLabel_cons {L : Type u} [SemilatticeInf L] [OrderTop L]
    (label : L) (labels : List L) :
    alternativeLabel (label :: labels) = label ⊓ alternativeLabel labels := rfl

/-- At an inf-prime clearance, the meet represents existential access to at
least one derivation, including correct rejection of an empty derivation set. -/
theorem alternativeLabel_le_iff {L : Type u} [SemilatticeInf L] [OrderTop L]
    {clearance : L} (prime : InfPrime clearance) (labels : List L) :
    alternativeLabel labels ≤ clearance ↔
      ∃ label ∈ labels, label ≤ clearance := by
  induction labels with
  | nil => simp [top_le_iff, prime.ne_top]
  | cons label labels ih =>
    simp only [alternativeLabel_cons, prime.inf_le, ih, List.mem_cons]
    constructor
    · intro visible
      rcases visible with visible | ⟨other, member, visible⟩
      · exact ⟨label, Or.inl rfl, visible⟩
      · exact ⟨other, Or.inr member, visible⟩
    · rintro ⟨other, member, visible⟩
      rcases member with rfl | member
      · exact Or.inl visible
      · exact Or.inr ⟨other, member, visible⟩

/-- In a linearly ordered security policy every non-top clearance has the
required prime property. Partial orders require the stronger hypothesis above. -/
theorem alternativeLabel_le_iff_of_linearOrder {L : Type u}
    [LinearOrder L] [OrderTop L] {clearance : L} (nonTop : clearance ≠ ⊤)
    (labels : List L) :
    alternativeLabel labels ≤ clearance ↔
      ∃ label ∈ labels, label ≤ clearance := by
  apply alternativeLabel_le_iff
  constructor
  · intro maximal
    exact nonTop (le_antisymm le_top (maximal le_top))
  · intro left right below
    rcases le_total left right with ordered | ordered
    · exact Or.inl (by simpa only [inf_eq_left.mpr ordered] using below)
    · exact Or.inr (by simpa only [inf_eq_right.mpr ordered] using below)

/-- Adjoining a fresh top separates no derivation from every actual level,
including the greatest original security level. This fixes the empty-meet
problem for chains; it does not fix incomparable compartments. -/
theorem alternativeLabel_withTop_le_iff {L : Type u} [LinearOrder L]
    (clearance : L) (labels : List L) :
    alternativeLabel (labels.map fun label => (label : WithTop L)) ≤
      (clearance : WithTop L) ↔
      ∃ label ∈ labels, label ≤ clearance := by
  rw [alternativeLabel_le_iff_of_linearOrder WithTop.coe_ne_top]
  simp

/-- For arbitrary lattices, retain the set of authorized clearances instead
of collapsing alternatives to one meet. Alternative derivations take union. -/
theorem alternative_visibility_append {L : Type u} [Preorder L]
    (left right : List L) :
    {clearance | ∃ label ∈ left ++ right, label ≤ clearance} =
      {clearance | ∃ label ∈ left, label ≤ clearance} ∪
      {clearance | ∃ label ∈ right, label ≤ clearance} := by
  ext clearance
  simp only [Set.mem_ofPred_eq, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨label, member, visible⟩
    rcases member with member | member
    · exact Or.inl ⟨label, member, visible⟩
    · exact Or.inr ⟨label, member, visible⟩
  · rintro (⟨label, member, visible⟩ | ⟨label, member, visible⟩)
    · exact ⟨label, Or.inl member, visible⟩
    · exact ⟨label, Or.inr member, visible⟩

/-- Combining independent sources takes intersection of authorized clearance
sets. The proof uses join's universal property, without distributivity or a
linearly ordered policy. This law concerns existential visibility only. -/
theorem combined_visibility_eq_inter {L : Type u} [SemilatticeSup L]
    (left right : List L) :
    {clearance | ∃ a ∈ left, ∃ b ∈ right, a ⊔ b ≤ clearance} =
      {clearance | ∃ a ∈ left, a ≤ clearance} ∩
      {clearance | ∃ b ∈ right, b ≤ clearance} := by
  ext clearance
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, sup_le_iff]
  constructor
  · rintro ⟨a, memberA, b, memberB, visibleA, visibleB⟩
    exact ⟨⟨a, memberA, visibleA⟩, ⟨b, memberB, visibleB⟩⟩
  · rintro ⟨⟨a, memberA, visibleA⟩, ⟨b, memberB, visibleB⟩⟩
    exact ⟨a, memberA, b, memberB, visibleA, visibleB⟩

/-- Duplicate derivations disappear from a lattice annotation. This can be
appropriate for existential visibility, but cannot encode a bag count. -/
theorem alternativeLabel_duplicate {L : Type u} [SemilatticeInf L] [OrderTop L]
    (label : L) (labels : List L) :
    alternativeLabel (label :: label :: labels) =
      alternativeLabel (label :: labels) := by
  simp only [alternativeLabel_cons, ← inf_assoc, inf_idem]

/-- Independent compartments form a distributive lattice, yet their meet
can be public while neither alternative is public. Two Boolean membership
bits represent the two compartments. -/
theorem compartment_meet_does_not_imply_visible_derivation :
    let left : Bool × Bool := (true, false)
    let right : Bool × Bool := (false, true)
    alternativeLabel [left, right] ≤ (false, false) ∧
      ¬ (∃ label ∈ [left, right], label ≤ (false, false)) := by
  decide

/-- The greatest clearance accepts the empty meet even though there was no
derivation. Presence cannot be recovered from this annotation. -/
theorem empty_meet_is_not_existence :
    alternativeLabel ([] : List Bool) ≤ true ∧
      ¬ (∃ label ∈ ([] : List Bool), label ≤ true) := by
  decide

/-- Product labels enforce confidentiality and integrity independently. A
secret trustworthy source and a public untrusted source combine to neither
public nor trustworthy. -/
theorem confidentiality_integrity_join_control :
    let secretTrusted : Label Bool Bool := (true, OrderDual.toDual true)
    let publicUntrusted : Label Bool Bool := (false, OrderDual.toDual false)
    secretTrusted ⊔ publicUntrusted =
      (true, OrderDual.toDual false) ∧
    ¬ (secretTrusted ⊔ publicUntrusted ≤
      (false, OrderDual.toDual false)) ∧
    ¬ (secretTrusted ⊔ publicUntrusted ≤
      (true, OrderDual.toDual true)) := by
  decide

end Mettapedia.Logic.InformationFlow
