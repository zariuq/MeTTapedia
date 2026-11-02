import Mettapedia.GSLT.Causality.ResourceTensorSequent
import Mettapedia.GSLT.Causality.FactLinearResources

/-!
# Tensor planning controls: leftovers, reuse, polarity and cyclic uses

The change/lemonade example preserves two leftover quarters. Its declared
rules are reusable, while each input resource remains linear. Exact empty
goals, partial empty goals, reversed rules and unsupported circular proof
uses are separated by checked positive and negative controls.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceTensorSequentControls

open Mettapedia.Logic
open Mettapedia.Logic.LinearLogic
open ResourceInteraction

inductive Item where
  | dollar
  | quarter
  | lemonade
deriving DecidableEq

open Item

def system : System Item where
  Site := Bool
  Instance _ := Unit
  consume := fun {rule} _ => if rule then {quarter, quarter, quarter} else {dollar}
  read _ := 0
  produce := fun {rule} _ => if rule then {lemonade} else {quarter, quarter, quarter, quarter}

def change : system.Entry := ⟨false, ()⟩
def drink : system.Entry := ⟨true, ()⟩

def initial : Multiset Item := {dollar, quarter}
def final : Multiset Item := {quarter, quarter, lemonade}

def diagram : system.HornProof initial final :=
  .cut (.tensor (.rule change) (.identity {quarter}))
    (.tensor (.identity {quarter, quarter}) (.rule drink))

theorem published_example_has_a_tensor_sequent_proof :
    ∃ proof : system.TensorProof (TensorSequent.atomContext initial) (TensorSequent.Formula.ofMultiset final),
      proof.uses = [change, drink] :=
  TensorSequent.ofHornAtomic diagram

theorem partial_lemonade_goal_retains_two_quarters :
    ∃ proof : system.TensorProof (TensorSequent.atomContext initial)
        (TensorSequent.Formula.ofMultiset (({lemonade} : Multiset Item) + {quarter, quarter})),
      proof.uses = [change, drink] := by
  obtain ⟨proof, uses⟩ := published_example_has_a_tensor_sequent_proof
  have same : final = ({lemonade} : Multiset Item) + {quarter, quarter} := by decide
  obtain ⟨packed, packedUses⟩ := TensorSequent.Derives.repackageGoal proof
    (right := TensorSequent.Formula.ofMultiset (({lemonade} : Multiset Item) + {quarter, quarter}))
    (by simpa only [TensorSequent.Formula.atoms_ofMultiset] using same)
  exact ⟨packed, packedUses.trans uses⟩

def price : Multiset Item →+ Nat where
  toFun bag := (bag.map fun item => match item with | dollar => 4 | quarter => 1 | lemonade => 3).sum
  map_zero' := rfl
  map_add' first second := by simp

theorem transitions_preserve_price (entry : system.Entry) :
    price (system.consume entry.2) = price (system.produce entry.2) := by
  cases entry with
  | mk rule input => cases rule <;> rfl

theorem no_exact_proof_discards_the_leftover_quarters :
    ¬ Nonempty (system.TensorProof (TensorSequent.atomContext initial) (TensorSequent.Formula.atom lemonade)) := by
  rintro ⟨proof⟩
  obtain ⟨actual, _⟩ := TensorSequent.toHornAtomic proof
  have impossible := actual.preserves_valuation price transitions_preserve_price
  change (5 : Nat) = 3 at impossible
  cases impossible

theorem a_rule_declaration_can_be_used_twice :
    ∃ proof : system.TensorProof (TensorSequent.atomContext ({dollar, dollar} : Multiset Item))
        (TensorSequent.Formula.ofMultiset
          (({quarter, quarter, quarter, quarter} : Multiset Item) + {quarter, quarter, quarter, quarter})),
      proof.uses = [change, change] :=
  TensorSequent.ofHornAtomic (.tensor (.rule change) (.rule change))

theorem declaration_reuse_does_not_duplicate_its_input_resource :
    ¬ Nonempty (system.TensorProof (TensorSequent.atomContext ({dollar} : Multiset Item))
      (TensorSequent.Formula.ofMultiset
        (({quarter, quarter, quarter, quarter} : Multiset Item) + {quarter, quarter, quarter, quarter}))) := by
  rintro ⟨proof⟩
  obtain ⟨actual, _⟩ := TensorSequent.toHornAtomic proof
  have impossible := actual.preserves_valuation price transitions_preserve_price
  rw [TensorSequent.Formula.atoms_ofMultiset] at impossible
  change (4 : Nat) = 8 at impossible
  cases impossible

theorem a_strict_unit_goal_does_not_erase_the_initial_state :
    ¬ Nonempty (system.TensorProof (TensorSequent.atomContext initial) .one) := by
  rintro ⟨proof⟩
  obtain ⟨actual, _⟩ := TensorSequent.toHornAtomic proof
  have impossible := actual.preserves_valuation price transitions_preserve_price
  change (5 : Nat) = 0 at impossible
  cases impossible

theorem a_partial_empty_goal_can_finish_with_everything_as_residual :
    ∃ residual, ∃ proof : system.TensorProof (TensorSequent.atomContext initial)
        (TensorSequent.Formula.ofMultiset ((0 : Multiset Item) + residual)), proof.uses = [] := by
  apply (system.partial_goal_iff_residual_tensor (fun _ => rfl) [] initial 0).mp
  exact ⟨initial, rfl, bot_le⟩

theorem no_rule_consumes_lemonade : system.ConsumesNoFacts (fun item => item = lemonade) := by
  intro rule input item member same
  subst item
  cases rule <;> simp [system] at member

private theorem lemonade_count_never_decreases : ∀ (trace : List system.Entry) {before after : Multiset Item},
    system.Fires trace before after → before.count lemonade ≤ after.count lemonade
  | [], _before, _after, destination => by rw [destination]
  | entry :: rest, before, _after, fires =>
      (system.factCount_le_fire no_rule_consumes_lemonade before entry.2 rfl).trans
        (lemonade_count_never_decreases rest fires.2)

theorem an_oriented_transition_is_not_its_reverse :
    ¬ Nonempty (system.TensorProof (TensorSequent.atomContext ({lemonade} : Multiset Item))
      (TensorSequent.Formula.ofMultiset ({quarter, quarter, quarter} : Multiset Item))) := by
  rintro ⟨proof⟩
  have runs := (system.tensor_sequent_iff_fires (fun _ => rfl) _ _ proof.uses).mp ⟨proof, rfl⟩
  have impossible := lemonade_count_never_decreases proof.uses runs
  have forbidden : ¬ (({lemonade} : Multiset Item).count lemonade ≤
      ({quarter, quarter, quarter} : Multiset Item).count lemonade) := by decide
  apply forbidden
  simpa only [TensorSequent.contextAtoms_atomContext, TensorSequent.Formula.atoms_ofMultiset] using impossible

def cycleSystem : System Nat where
  Site := Bool
  Instance _ := Unit
  consume := fun {rule} _ => if rule then {1} else {0}
  read _ := 0
  produce := fun {rule} _ => if rule then {0} else {1}

def cycleFirst : cycleSystem.Entry := ⟨false, ()⟩
def cycleSecond : cycleSystem.Entry := ⟨true, ()⟩

/-- A finite inductive proof cannot be bootstrapped by connecting the two
transition declarations in a cycle with no initial resource supplier. -/
theorem unsupported_circular_uses_do_not_form_a_tensor_proof :
    ¬ ∃ proof : cycleSystem.TensorProof 0 .one, proof.uses = [cycleFirst, cycleSecond] := by
  rintro ⟨proof, uses⟩
  have runs := (cycleSystem.tensor_sequent_iff_fires (fun _ => rfl) _ _ _).mp ⟨proof, uses⟩
  have enabled := runs.1
  change ({0} : Multiset Nat) ≤ 0 at enabled
  exact (by decide : ¬ ({0} : Multiset Nat) ≤ 0) enabled

end Mettapedia.GSLT.Causality.ResourceTensorSequentControls
