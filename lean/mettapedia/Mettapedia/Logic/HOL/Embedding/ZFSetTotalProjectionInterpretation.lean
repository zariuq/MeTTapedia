import Mettapedia.Logic.HOL.Embedding.ZFSetProjectionProofInterpretation
import Mettapedia.SetTheory.ZFSet.OrderedPairDefaults

/-!
# Total agreement of the selected and component-collecting projections

The comparison uses the specified `epsilonSet` interpretation, including its
empty default when the predicate has no witness. Retained computation on
actual pairs only needs the selection law and does not fix that default.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetTotalProjectionInterpretation
open ZFSetHenkinInterpretation (ChoiceSymbol epsilonSet epsilonSet_spec epsilonSet_default)
open ZFSetPairingProofInterpretation (core epsilon model value ordered_value value_weaken)
open Mettapedia.SetTheory
universe u

noncomputable def firstValue (point : ZFSet.{u}) : ZFSet.{u} :=
  epsilonSet (fun left => .up (∃ right, ZFSet.pair left right = point))

noncomputable def secondValue (point : ZFSet.{u}) : ZFSet.{u} :=
  epsilonSet (fun right => .up (ZFSet.pair (firstValue point) right = point))

theorem firstValue_pair (left right : ZFSet.{u}) : firstValue (ZFSet.pair left right) = left := by
  have selected := epsilonSet_spec (fun value => ULift.up (∃ other, ZFSet.pair value other = ZFSet.pair left right))
    (x := left) ⟨right,rfl⟩
  obtain ⟨other,equal⟩ := selected
  exact (ZFSet.pair_inj.mp equal).1

theorem secondValue_pair (left right : ZFSet.{u}) : secondValue (ZFSet.pair left right) = right := by
  have selected := epsilonSet_spec (fun value => ULift.up (ZFSet.pair (firstValue (ZFSet.pair left right)) value = ZFSet.pair left right))
    (x := right) (by rw [firstValue_pair])
  rw [firstValue_pair] at selected
  unfold secondValue
  rw [firstValue_pair]
  exact (ZFSet.pair_inj.mp selected).2

theorem firstValue_agrees (point : ZFSet.{u}) : firstValue point = ZFSetOrderedPair.first point := by
  classical
  by_cases paired : ∃ left right, point = ZFSet.pair left right
  · obtain ⟨left,right,rfl⟩ := paired
    rw [firstValue_pair,ZFSetOrderedPair.first_pair]
  · rw [ZFSetOrderedPair.first_of_not_pair point paired]
    apply epsilonSet_default
    rintro ⟨left,right,equal⟩
    exact paired ⟨left,right,equal.symm⟩

theorem secondValue_agrees (point : ZFSet.{u}) : secondValue point = ZFSetOrderedPair.second point := by
  classical
  by_cases paired : ∃ left right, point = ZFSet.pair left right
  · obtain ⟨left,right,rfl⟩ := paired
    rw [secondValue_pair,ZFSetOrderedPair.second_pair]
  · rw [ZFSetOrderedPair.second_of_not_pair point paired]
    apply epsilonSet_default
    rintro ⟨right,equal⟩
    exact paired ⟨firstValue point,right,equal.symm⟩

variable {Γ : Ctx Unit}

theorem first_value (point : Term ChoiceSymbol Γ SetPairingProofs.object) (valuation : model.{u}.Valuation Γ) :
    value (SetPairProjectionProofs.first core epsilon point) valuation = firstValue (value point valuation) := by
  change model.denote (HOL.weakenCtx Γ epsilon) valuation (fun left =>
    (model.denote (SetPairProjectionProofs.firstBody core epsilon point)
      (model.extend (σ := SetPairingProofs.object) valuation left))) = _
  rw [HenkinModel.denote_weakenCtx]
  change epsilonSet (fun left =>
    model.denote (SetPairProjectionProofs.firstBody core epsilon point)
      (model.extend (σ := SetPairingProofs.object) valuation left)) = _
  apply congrArg epsilonSet
  funext left
  apply ULift.ext
  apply propext
  change (∃ right : ZFSet.{u}, True ∧
    value (SetPairingProofs.ordered core epsilon (.var (.vs .vz)) (.var .vz))
      (model.extend (σ := SetPairingProofs.object) (model.extend (σ := SetPairingProofs.object) valuation left) right) =
    value (HOL.weaken (HOL.weaken point))
      (model.extend (σ := SetPairingProofs.object) (model.extend (σ := SetPairingProofs.object) valuation left) right)) ↔ _
  simp only [ordered_value,value_weaken,true_and]
  rfl

theorem second_value (point : Term ChoiceSymbol Γ SetPairingProofs.object) (valuation : model.{u}.Valuation Γ) :
    value (SetPairProjectionProofs.second core epsilon point) valuation = secondValue (value point valuation) := by
  change model.denote (HOL.weakenCtx Γ epsilon) valuation (fun right =>
    (model.denote (SetPairProjectionProofs.secondBody core epsilon point)
      (model.extend (σ := SetPairingProofs.object) valuation right))) = _
  rw [HenkinModel.denote_weakenCtx]
  change epsilonSet (fun right =>
    model.denote (SetPairProjectionProofs.secondBody core epsilon point)
      (model.extend (σ := SetPairingProofs.object) valuation right)) = _
  apply congrArg epsilonSet
  funext right
  apply ULift.ext
  apply propext
  change value (SetPairingProofs.ordered core epsilon (HOL.weaken (SetPairProjectionProofs.first core epsilon point)) (.var .vz))
      (model.extend (σ := SetPairingProofs.object) valuation right) =
    value (HOL.weaken point) (model.extend (σ := SetPairingProofs.object) valuation right) ↔ _
  rw [ordered_value,value_weaken,value_weaken,first_value]
  rfl

theorem projections_agree (point : Term ChoiceSymbol Γ SetPairingProofs.object) (valuation : model.{u}.Valuation Γ) :
    value (SetPairProjectionProofs.first core epsilon point) valuation = ZFSetOrderedPair.first (value point valuation) ∧
    value (SetPairProjectionProofs.second core epsilon point) valuation = ZFSetOrderedPair.second (value point valuation) :=
  ⟨(first_value point valuation).trans (firstValue_agrees _),
    (second_value point valuation).trans (secondValue_agrees _)⟩

end Mettapedia.Logic.HOL.Embedding.ZFSetTotalProjectionInterpretation
