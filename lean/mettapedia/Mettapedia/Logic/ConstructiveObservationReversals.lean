/-! Constructive relational observation laws. These proofs use only the
logical rules of Lean's kernel: no choice, quotient or extensionality axiom.
The semantic boundary is stated pointwise, without equality of predicates. -/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstructiveObservationReversals

universe u v w
variable {A : Type u} {B : Type v} {O : Type w}

def View (models : A → Prop) (observe : A → O) (value : O) : Prop :=
  ∃ model, models model ∧ observe model = value

theorem view_iff_all_possible (left : A → Prop) (right : B → Prop)
    (observeLeft : A → O) (observeRight : B → O) :
    (∀ value, View left observeLeft value ↔ View right observeRight value) ↔
      ∀ query : O → Prop,
        (∃ model, left model ∧ query (observeLeft model)) ↔
        (∃ model, right model ∧ query (observeRight model)) := by
  constructor
  · intro same query
    constructor
    · rintro ⟨model, member, holds⟩
      obtain ⟨other, present, equal⟩ := (same (observeLeft model)).mp ⟨model, member, rfl⟩
      exact ⟨other, present, equal.symm ▸ holds⟩
    · rintro ⟨model, member, holds⟩
      obtain ⟨other, present, equal⟩ := (same (observeRight model)).mpr ⟨model, member, rfl⟩
      exact ⟨other, present, equal.symm ▸ holds⟩
  · intro same value
    exact same (· = value)

theorem view_iff_all_necessary (left : A → Prop) (right : B → Prop)
    (observeLeft : A → O) (observeRight : B → O) :
    (∀ value, View left observeLeft value ↔ View right observeRight value) ↔
      ∀ query : O → Prop,
        (∀ model, left model → query (observeLeft model)) ↔
        (∀ model, right model → query (observeRight model)) := by
  constructor
  · intro same query
    constructor
    · intro holds model member
      obtain ⟨other, present, equal⟩ := (same (observeRight model)).mpr ⟨model, member, rfl⟩
      exact equal ▸ holds other present
    · intro holds model member
      obtain ⟨other, present, equal⟩ := (same (observeLeft model)).mp ⟨model, member, rfl⟩
      exact equal ▸ holds other present
  · intro same value
    constructor
    · rintro ⟨model, member, equal⟩
      have observed := (same (View right observeRight)).mpr (fun other present => ⟨other, present, rfl⟩) model member
      exact equal ▸ observed
    · rintro ⟨model, member, equal⟩
      have observed := (same (View left observeLeft)).mp (fun other present => ⟨other, present, rfl⟩) model member
      exact equal ▸ observed

def visible (witness : Bool) : Prop := witness = false
def world (_witness : Bool) : Prop := True

theorem absence_without_coverage :
    (∀ witness, visible witness → world witness) ∧
      ((¬ ∃ witness, visible witness) ↔ (¬ ∃ witness, world witness)) ∧
      ¬ (∀ witness, world witness → visible witness) := by
  refine ⟨fun _ _ => trivial, ?_, ?_⟩
  · constructor
    · intro absent
      exact False.elim (absent ⟨false, rfl⟩)
    · intro absent
      exact False.elim (absent ⟨false, trivial⟩)
  · intro covers
    have impossible : true = false := covers true trivial
    cases impossible

theorem separate_models_do_not_supply_one_joint_model :
    (∃ model : Bool, model = false) ∧ (∃ model : Bool, model = true) ∧
      ¬ ∃ model : Bool, model = false ∧ model = true := by
  refine ⟨⟨false, rfl⟩, ⟨true, rfl⟩, ?_⟩
  rintro ⟨model, rfl, impossible⟩
  cases impossible

#print axioms view_iff_all_possible
#print axioms view_iff_all_necessary
#print axioms absence_without_coverage
#print axioms separate_models_do_not_supply_one_joint_model

end Mettapedia.Logic.ConstructiveObservationReversals
