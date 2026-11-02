import Mettapedia.Logic.LinearLogic.TensorMLLEncoding
import Mettapedia.GSLT.Causality.ResourceTensorSequentControls

/-!
# Existing MLL proof controls for the finite-copy translation

A non-colliding atom encoding gives an actual existing MLL proof of the
change/lemonade example with two declaration copies. Independent signed-
weight semantics refutes leftover deletion for every finite declaration-copy
list, even outside the image of this compiler. A deliberately colliding code
demonstrates why the forward theorem is not a generic reflection theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.TensorMLLControls

open Mettapedia.GSLT.Logic
open Mettapedia.GSLT.Causality.ResourceTensorSequentControls
open TensorMLLEncoding
open Item

def code : Item → Nat
  | dollar => 0
  | quarter => 1
  | lemonade => 2

theorem code_injective : Function.Injective code := by
  intro first second same
  cases first <;> cases second <;> simp_all [code]

def weight : Nat → Int
  | 0 => 4
  | 1 => 1
  | _ => 3

def premises (entry : system.Entry) : Multiset Item := system.consume entry.2
def conclusions (entry : system.Entry) : Multiset Item := system.produce entry.2

theorem rules_are_balanced (entry : system.Entry) :
    (premises entry |>.map fun item => weight (code item)).sum =
      (conclusions entry |>.map fun item => weight (code item)).sum := by
  cases entry with
  | mk rule input => cases rule <;> rfl

theorem the_published_example_has_an_existing_MLL_proof :
    PropositionalMLL.Bag.Provable
      (encode code (TensorSequent.Formula.ofMultiset final) ::ₘ
        (negativeContext code (TensorSequent.atomContext initial) + ruleCopies code premises conclusions [change, drink])) := by
  obtain ⟨proof, uses⟩ := published_example_has_a_tensor_sequent_proof
  have actual := compile code proof
  unfold premises conclusions
  simpa only [uses] using actual

theorem repeated_declarations_are_two_distinct_formula_occurrences :
    (ruleCopies code premises conclusions [change, change]).card = 2 :=
  ruleCopies_card code premises conclusions [change, change]

/-- This obstruction applies to every proof of the full existing MLL
calculus, not just to tensor proofs produced by the translation. -/
theorem no_existing_MLL_proof_discards_the_leftovers (copies : List system.Entry) :
    ¬ PropositionalMLL.Bag.Provable
      (encode code (TensorSequent.Formula.atom lemonade) ::ₘ
        (negativeContext code (TensorSequent.atomContext initial) + ruleCopies code premises conclusions copies)) := by
  intro proof
  have zero := PropositionalMLL.Balance.bag_conserved weight proof
  have copiedZero := balanced_ruleCopies code weight premises conclusions rules_are_balanced copies
  have old : PropositionalMLL.Balance.bagTotal weight
      (negativeContext code (TensorSequent.atomContext initial)) = -5 := by
    rw [negative_atom_context]
    rfl
  rw [PropositionalMLL.Balance.bagTotal_cons, PropositionalMLL.Balance.bagTotal_add,
    copiedZero, old] at zero
  change (-2 : Int) = 0 at zero
  cases zero

def noRules (rule : Empty) : Multiset Nat := nomatch rule

def countZero : Multiset Nat →+ Nat where
  toFun bag := bag.count 0
  map_zero' := rfl
  map_add' _first _second := Multiset.count_add _ _ _

theorem a_colliding_code_cannot_support_generic_reflection :
    (¬ Nonempty (TensorSequent.Derives noRules noRules {TensorSequent.Formula.atom 0} (.atom 1))) ∧
      PropositionalMLL.Bag.Provable
        (encode (fun _ : Nat => 0) (TensorSequent.Formula.atom 1) ::ₘ
          negativeContext (fun _ : Nat => 0) {TensorSequent.Formula.atom 0}) := by
  constructor
  · rintro ⟨proof⟩
    obtain ⟨diagram, _⟩ := TensorSequent.toHorn proof
    have impossible := diagram.preserves_valuation countZero (fun rule => nomatch rule)
    change (1 : Nat) = 0 at impossible
    cases impossible
  · exact PropositionalMLL.Bag.atom 0

end Mettapedia.Logic.LinearLogic.TensorMLLControls
