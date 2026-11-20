import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Step
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Countable.Basic

/-!
# Holding more rules adds occurrences: composition is not idempotent, and finite states are countable

When a program is a set of rules outside the state, two systems compose by the union of their
programs, and a program beside itself is itself. Here the rules are occurrences, and composing adds
them.

**Holding more rules** (`RState.hold`): the identities `ids`, new to the state, become held with the
given labels. The **bag of codes** a state holds (`RState.codeBag`) is additive under it
(`codeBag_hold`):

* `hold_ne`: holding a non-empty set of further occurrences changes the state, whatever their
  labels. In particular a state that holds the rules of a program, and the state that holds them
  once more at new identities, are different states: the equation `P ∪ P = P` has no counterpart.
* `codeBag_cancel`: the bag of codes cancels a common part. So the bag of codes is a map into a
  cancellative monoid that is additive under holding more rules and tells apart the states that an
  idempotent union identifies.

**Finite states are countable.** What a state shows (`RState.shown`: its frame and, at it, its
knowledge, its rows with their labels and its rule occurrences with their labels; the labels of
identities that are not present are not part of it) ranges over a countable type when frames, terms,
identities, codes and zones are countable (`shown_countable`). An infinite family of rules is held by
no state (`offers_finite`, for the rules of the present step): it is the ambient program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

universe uO uT uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {O : Type uOcc} {R : Type uR} {C : Type uC}
  {Z : Type uZ}

namespace RState

/-- **The bag of codes a state holds**: the code of each rule occurrence, with multiplicity. -/
def codeBag (s : RState Tm O R C Z) : Multiset C := s.rules.val.map fun ρ => (s.held ρ).code

/-- **Hold more rules**: the identities `ids` become held with the given labels. -/
def hold [DecidableEq R] (s : RState Tm O R C Z) (ids : Finset R)
    (label : R → Held Tm C Z s.frame) : RState Tm O R C Z :=
  { s with rules := s.rules ∪ ids, held := fun ρ => if ρ ∈ ids then label ρ else s.held ρ }

variable [DecidableEq R] (s : RState Tm O R C Z) (ids : Finset R)
  (label : R → Held Tm C Z s.frame)

/-- **The bag of codes is additive**: holding new occurrences adds their codes. -/
theorem codeBag_hold (disjoint : Disjoint s.rules ids) :
    (s.hold ids label).codeBag = s.codeBag + ids.val.map fun ρ => (label ρ).code := by
  have rules : (s.hold ids label).rules.val = s.rules.val + ids.val := by
    show (s.rules ∪ ids).val = _
    rw [← Finset.disjUnion_eq_union s.rules ids disjoint]
    rfl
  unfold codeBag
  rw [rules, Multiset.map_add]
  congr 1
  · apply Multiset.map_congr rfl
    intro ρ inside
    have outside : ρ ∉ ids := Finset.disjoint_left.mp disjoint (Finset.mem_val.mp inside)
    show (if ρ ∈ ids then label ρ else s.held ρ).code = (s.held ρ).code
    rw [if_neg outside]
  · apply Multiset.map_congr rfl
    intro ρ inside
    show (if ρ ∈ ids then label ρ else s.held ρ).code = (label ρ).code
    rw [if_pos (Finset.mem_val.mp inside)]

/-- **Holding more is never idempotent**: a non-empty set of new occurrences changes the state. -/
theorem hold_ne (disjoint : Disjoint s.rules ids) (nonempty : ids.Nonempty) :
    s.hold ids label ≠ s := by
  intro same
  have bags : Multiset.card (s.hold ids label).codeBag = Multiset.card s.codeBag :=
    congrArg (fun t : RState Tm O R C Z => Multiset.card t.codeBag) same
  rw [codeBag_hold s ids label disjoint, Multiset.card_add, Multiset.card_map] at bags
  have positive : 0 < ids.card := Finset.card_pos.mpr nonempty
  have cards : Multiset.card ids.val = ids.card := rfl
  omega

/-- Holding one more occurrence, at an identity new to the state, changes the state. -/
theorem hold_one_ne {ρ : R} (new : ρ ∉ s.rules) (label : R → Held Tm C Z s.frame) :
    s.hold {ρ} label ≠ s :=
  hold_ne s {ρ} label (Finset.disjoint_singleton_right.mpr new) (Finset.singleton_nonempty ρ)

/-- **The bag of codes cancels a common part**: if two states hold the same bag of codes after
holding new occurrences with the same codes, they held the same bag before. -/
theorem codeBag_cancel (t : RState Tm O R C Z) (ids' : Finset R) (label' : R → Held Tm C Z t.frame)
    (disjoint : Disjoint s.rules ids) (disjoint' : Disjoint t.rules ids')
    (added : (ids.val.map fun ρ => (label ρ).code) = ids'.val.map fun ρ => (label' ρ).code)
    (same : (s.hold ids label).codeBag = (t.hold ids' label').codeBag) : s.codeBag = t.codeBag := by
  rw [codeBag_hold s ids label disjoint, codeBag_hold t ids' label' disjoint', added] at same
  exact add_right_cancel same

end RState

/-! ## What a state shows -/

/-- A held rule is determined by its code, its arguments, whether it is linear, and its zone. -/
instance held_countable {a : Obj} [Countable (Tm a)] [Countable C] [Countable Z] :
    Countable (Held Tm C Z a) := by
  have injective : Function.Injective
      (fun h : Held Tm C Z a => (h.code, h.args, decide (h.mode = Mode.linear), h.zone)) := by
    rintro ⟨code, args, mode, zone⟩ ⟨code', args', mode', zone'⟩ same
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, modes, rfl⟩ := same
    cases mode <;> cases mode'
    · rfl
    · simp at modes
    · simp at modes
    · rfl
  exact injective.countable

/-- **What a state shows**: its frame and, at it, its knowledge, its rows with their labels, and its
rule occurrences with their labels. -/
def Shown (Tm : Obj → Type uT) (O : Type uOcc) (R : Type uR) (C : Type uC) (Z : Type uZ) :
    Type (max uO uT uOcc uR uC uZ) :=
  (a : Obj) × (EquationStore (Tm a) × Multiset (O × Tm a) × Multiset (R × Held Tm C Z a))

/-- What a state shows. -/
def RState.shown (s : RState Tm O R C Z) : Shown Tm O R C Z :=
  ⟨s.frame, s.knowledge, s.present.val.map fun o => (o, s.label o),
    s.rules.val.map fun ρ => (ρ, s.held ρ)⟩

/-- **Finite states are countable**: what states show ranges over a countable type when frames,
terms, identities, codes and zones are countable. -/
instance shown_countable [Countable Obj] [∀ a, Countable (Tm a)] [Countable O] [Countable R]
    [Countable C] [Countable Z] : Countable (Shown Tm O R C Z) := by
  unfold Shown
  infer_instance

/-- The rows and the rule occurrences a state shows are as many as it has. -/
theorem shown_cards (s : RState Tm O R C Z) :
    Multiset.card s.shown.2.2.1 = s.present.card ∧ Multiset.card s.shown.2.2.2 = s.rules.card :=
  ⟨Multiset.card_map _ _, Multiset.card_map _ _⟩

#print axioms RState.codeBag_hold
#print axioms RState.hold_ne
#print axioms RState.hold_one_ne
#print axioms RState.codeBag_cancel
#print axioms held_countable
#print axioms shown_countable
#print axioms shown_cards

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
