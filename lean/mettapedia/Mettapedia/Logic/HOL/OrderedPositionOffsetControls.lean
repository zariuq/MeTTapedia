import Mettapedia.Logic.HOL.OrderedPositionOffsetSemantics
import Mettapedia.Logic.HOL.OrderedPositionFunctionalityControls

/-!
# Distinct local positions, empty segments and invalid ordinals

Two positions in one nested segment share a child index but have different
absolute slots. The standard natural-number model rejects replacing one slot
by the other. Empty segments still admit an offset, but not a bounded child.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionOffsetControls
open OrderedPositionPrograms SuccessorOrder
open OrderedPositionProofControls (number Symbol zero successor one model values numbers full zero_preserved successor_preserved)
open OrderedPositionFunctionalityControls (assumptions arithmetic arithmetic_free assumptions_realizable)

def two : ClosedTerm Symbol number := .app successor one
def three : ClosedTerm Symbol number := .app successor two
def plan : Plan Symbol [] number .prop := [(one, .top), (two, .top), (zero, .bot), (one, .bot)]

def relation (ordinal : Nat) (localPos slot : ClosedTerm Symbol number) : ClosedFormula Symbol :=
  selectedOffsetAt zero successor ordinal plan Subst.id localPos slot

theorem relation_denote (ordinal : Nat) (localPos slot : ClosedTerm Symbol number) :
    (model.denote (relation ordinal localPos slot) @values).down ↔
      ordinal < 4 ∧ (model.denote slot @values).down =
        (([1, 2, 0, 1].take ordinal).sum + (model.denote localPos @values).down) := by
  have interpreted := selectedOffsetAt_denote zero successor model numbers full values zero_preserved successor_preserved
    ordinal plan values Subst.id localPos slot values (fun entry => nomatch entry)
  simp only [plan, evaluate, List.map_cons, List.map_nil, List.map_take,
    List.length_cons, List.length_nil] at interpreted
  change (model.denote (relation ordinal localPos slot) @values).down ↔
    ordinal < 4 ∧ (model.denote slot @values).down =
      (([1, 2, 0, 1].take ordinal).sum + (model.denote localPos @values).down) at interpreted
  exact interpreted

def firstNested : ProofSyntax Symbol [] (relation 1 zero one) :=
  selectedOffsetAt_later zero successor 0 (one, .top) [(two, .top), (zero, .bot), (one, .bot)] Subst.id
    zero one zero (sumZero successor zero one) (.eqRefl zero)

theorem firstNested_free : firstNested.FunctionExtensionalityFree := by
  apply selectedOffsetAt_later_free
  · exact sumZero_free _ _ _
  · trivial

def secondNested : ProofSyntax Symbol [] (relation 1 one two) :=
  selectedOffsetAt_later zero successor 0 (one, .top) [(two, .top), (zero, .bot), (one, .bot)] Subst.id
    one two one (sumStep successor zero one zero one (sumZero successor zero one)) (.eqRefl one)

theorem secondNested_free : secondNested.FunctionExtensionalityFree := by
  apply selectedOffsetAt_later_free
  · exact sumStep_free _ _ _ _ _ _ (sumZero_free _ _ _)
  · trivial

theorem firstNested_holds : (model.denote (relation 1 zero one) @values).down := by
  rw [relation_denote]
  decide +kernel

theorem secondNested_holds : (model.denote (relation 1 one two) @values).down := by
  rw [relation_denote]
  decide +kernel

theorem swapping_positions_refused : ¬ (model.denote (relation 1 one one) @values).down := by
  rw [relation_denote]
  decide +kernel

theorem zero_segment_offset_holds : (model.denote (relation 2 zero three) @values).down := by
  rw [relation_denote]
  decide +kernel

theorem zero_segment_child_refused :
    ¬ (model.denote (.app (.app (less successor) zero) zero) @values).down := by
  change ¬ (model.denote (less successor) values (model.denote zero values) (model.denote zero values)).down
  rw [less_iff model full successor values numbers successor_preserved]
  decide +kernel

theorem invalid_ordinal_refused : ¬ (model.denote (relation 4 zero three) @values).down := by
  rw [relation_denote]
  decide +kernel

theorem incorrect_slot_has_no_proof : ¬ Nonempty (ProofSyntax Symbol assumptions (relation 1 one one)) := by
  rintro ⟨proof⟩
  exact swapping_positions_refused (Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains full) (fun entry => nomatch entry) assumptions_realizable)

def slotExists (localPos : ClosedTerm Symbol number) : ProofSyntax Symbol assumptions
    (selectedOffsetExists zero successor 3 plan Subst.id localPos) :=
  selectedOffsetExists_proof zero successor plan ⟨3, by decide +kernel⟩ Subst.id localPos arithmetic.induction

theorem slotExists_free (localPos : ClosedTerm Symbol number) : (slotExists localPos).FunctionExtensionalityFree :=
  selectedOffsetExists_proof_free zero successor plan ⟨3, by decide +kernel⟩ Subst.id localPos
    arithmetic.induction arithmetic_free.2.2

#print axioms firstNested_free
#print axioms secondNested_free
#print axioms incorrect_slot_has_no_proof
#print axioms slotExists_free
end Mettapedia.Logic.HOL.OrderedPositionOffsetControls
