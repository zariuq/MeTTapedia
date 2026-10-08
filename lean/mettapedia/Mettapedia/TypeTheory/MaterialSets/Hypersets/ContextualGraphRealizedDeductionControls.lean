import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedDeduction
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Varying contextual deduction controls

The node carrier grows at every natural stage. Membership first appears
at the next stage, so the complete future reading of implication differs
from a current-fibre function. Logical proof trees retain their authored
hypothesis positions and existential witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedDeductionControls

open CategoryTheory ContextualGraphDiagrams
open ContextualGraphFormulaRealization ContextualRealizedGraphs ContextualGraphRealizedDeduction
open GraphRealizedDeduction (Proof)

def growing : Diagram Nat where
  nodes := {
    obj point := Fin (point+2)
    map {_first _second} arrival := TypeCat.ofHom fun node =>
      ⟨node.val, Nat.lt_of_lt_of_le node.isLt (Nat.add_le_add_right (leOfHom arrival) 2)⟩
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge point _ _ := 0 < point
  edge_transport := fun {_ _} arrival {_ _} available => Nat.lt_of_lt_of_le available (leOfHom arrival)

def root (point : Nat) : Value Nat point :=
  ⟨growing, ⟨0, Nat.zero_lt_succ (point+1)⟩⟩

theorem root_move {first second : Nat} (arrival : first ⟶ second) :
    move Nat arrival (root first) = root second := rfl

theorem node_carrier_grows (point : Nat) :
    ¬ ∃ earlier : growing.nodes.obj point,
      growing.nodes.map (homOfLE (Nat.le_succ point)) earlier =
        (⟨point+2, Nat.lt_succ_self (point+2)⟩ : growing.nodes.obj (point+1)) := by
  rintro ⟨earlier, same⟩
  have value := congrArg Fin.val same
  change earlier.val = point+2 at value
  exact (Nat.ne_of_lt earlier.isLt) value

def allWitness : Proof ([] : List (Formula 0)) (.all (.exist (.equal 0 1))) :=
  .allIntro (.existIntro 0 (.equalRefl 0))

def materialWitness : Proof ([.member 0 0] : List (Formula 1)) (.exist (.member 0 1)) :=
  .existIntro 0 (.hypothesis (assumptions := [.member 0 0]) 0)

def equalityAction : Proof ([.equal 0 1, .member 2 0] : List (Formula 3)) (.member 2 1) :=
  .equalElim (body := .member 3 0)
    (.hypothesis (assumptions := [.equal 0 1, .member 2 0]) 0)
    (.hypothesis (assumptions := [.equal 0 1, .member 2 0]) 1)

def implicationIdentity {count : Nat} (formula : Formula count) : Proof [] (.imply formula formula) :=
  .implyIntro (.hypothesis (assumptions := [formula]) 0)

def environment (count point : Nat) : Environment Nat count point := fun _ => root point

abbrev membership : Formula 1 := .member 0 0
abbrev excludedMiddle : Formula 1 := .either membership (.imply membership .bottom)

def lateMember (point : Nat) (positive : 0 < point) : Member (root point) (root point) :=
  ⟨⟨⟨0, Nat.zero_lt_succ (point+1)⟩, positive⟩, Equal.refl (root point)⟩

theorem current_membership_empty : ¬ Nonempty (realize Nat membership 0 (environment 1 0)) := by
  rintro ⟨proof⟩
  exact Nat.not_lt_zero 0 proof.down.1.property

theorem later_membership_exists : Nonempty (realize Nat membership 1 (environment 1 1)) :=
  ⟨⟨lateMember 1 (by decide)⟩⟩

theorem full_future_negation_empty :
    ¬ Nonempty (realize Nat (.imply membership .bottom) 0 (environment 1 0)) := by
  rintro ⟨proof⟩
  exact PEmpty.elim (proof 1 (homOfLE (by decide : 0 ≤ 1)) ⟨lateMember 1 (by decide)⟩)

def presentOnlyNegation : realize Nat membership 0 (environment 1 0) → PEmpty :=
  fun proof => False.elim (current_membership_empty ⟨proof⟩)

theorem present_function_is_not_full_future_implication :
    Nonempty (realize Nat membership 0 (environment 1 0) → PEmpty) ∧
      ¬ Nonempty (realize Nat (.imply membership .bottom) 0 (environment 1 0)) :=
  ⟨⟨presentOnlyNegation⟩, full_future_negation_empty⟩

theorem excluded_middle_empty : ¬ Nonempty (realize Nat excludedMiddle 0 (environment 1 0)) := by
  rintro ⟨proof⟩
  exact proof.elim (fun member => current_membership_empty ⟨member⟩)
    (fun negative => full_future_negation_empty ⟨negative⟩)

/-- Actual deduction soundness rules out a classical deduction in this
intuitionistic syntax, witnessed by a genuinely varying interpretation. -/
theorem no_closed_excluded_middle : ¬ Nonempty (Proof [] excludedMiddle) := by
  rintro ⟨proof⟩
  exact excluded_middle_empty ⟨closed proof 0 (environment 1 0)⟩

def laterNewValue : Value Nat 2 := ⟨growing, ⟨3, by decide⟩⟩

theorem universal_retains_later_witness :
    (closed allWitness 0 (environment 0 0) 2 (homOfLE (by decide : 0 ≤ 2)) laterNewValue).1 =
      laterNewValue := rfl

def oneMemberReceipts : Receipts ([membership] : List (Formula 1)) (environment 1 1) :=
  consReceipts ⟨lateMember 1 (by decide)⟩
    (fun index => False.elim (Nat.not_lt_zero _ index.isLt))

theorem existential_retains_current_witness :
    (interpret materialWitness 1 (environment 1 1) oneMemberReceipts).1 = root 1 := rfl

/-- A full-future matching strategy with a different literal response.
Every future matching layer and every continuation is constructed. -/
def alternate {point : Nat} (first second : growing.nodes.obj point) :
    Equal (⟨growing, first⟩ : Value Nat point) ⟨growing, second⟩ :=
  ContextualGraphRealizers.corec growing growing
    (witness := fun _ _ _ => PUnit.{1})
    (fun _ _ _ _ future child =>
      ⟨⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos future.1)⟩, child.property⟩, PUnit.unit⟩)
    (fun _ _ _ _ future child =>
      ⟨⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos future.1)⟩, child.property⟩, PUnit.unit⟩)
    PUnit.unit

def alternativeMember : Member (root 1) (root 1) :=
  Member.transportParent (alternate (root 1).2 (root 1).2) (lateMember 1 (by decide))

def duplicateReceipts : Receipts ([membership, membership] : List (Formula 1)) (environment 1 1) :=
  consReceipts ⟨lateMember 1 (by decide)⟩
    (consReceipts ⟨alternativeMember⟩
      (fun index => False.elim (Nat.not_lt_zero _ index.isLt)))

theorem first_hypothesis_retains_first_receipt :
    ((interpret (.hypothesis (assumptions := [membership, membership]) 0) 1
      (environment 1 1) duplicateReceipts).down.1.val).val = 0 := rfl

theorem second_hypothesis_retains_second_receipt :
    ((interpret (.hypothesis (assumptions := [membership, membership]) 1) 1
      (environment 1 1) duplicateReceipts).down.1.val).val = 1 := rfl

def equalityReceipts (matching : Equal (root 1) (root 1)) :
    Receipts ([.equal 0 1, .member 2 0] : List (Formula 3)) (environment 3 1) :=
  consReceipts ⟨matching⟩
    (consReceipts ⟨lateMember 1 (by decide)⟩
      (fun index => False.elim (Nat.not_lt_zero _ index.isLt)))

theorem equality_elimination_reflexive_action :
    ((interpret equalityAction 1 (environment 3 1)
      (equalityReceipts (Equal.refl (root 1)))).down.1.val).val = 0 := rfl

theorem equality_elimination_alternative_action :
    ((interpret equalityAction 1 (environment 3 1)
      (equalityReceipts (alternate (root 1).2 (root 1).2))).down.1.val).val = 1 := rfl

/-- Equality supplied before any current edge exists still controls the
literal receipt chosen after restriction to a later context. -/
theorem equality_elimination_restricted_future_action :
    ((interpret equalityAction 1 (environment 3 1)
      (equalityReceipts (Equal.restrict (homOfLE (by decide : 0 ≤ 1))
        (alternate (root 0).2 (root 0).2)))).down.1.val).val = 1 := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedDeductionControls
