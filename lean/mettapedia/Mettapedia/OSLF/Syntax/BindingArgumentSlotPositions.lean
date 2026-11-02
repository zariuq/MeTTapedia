import Mettapedia.OSLF.Syntax.BindingArgumentSlots
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite positions for typed binding fields

The typed field positions of an argument list correspond exactly to its finite
indices. Repeated field declarations retain distinct positions. Decidable
identity and finite enumeration require neither decidable equality nor a finite
carrier for the signature's sorts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ArgumentSlots

variable {S : Signature}

def toIndex : {arities : List (MetaArity S)} → Slot arities → Fin arities.length
  | [], ⟨_, impossible⟩ => nomatch impossible
  | _ :: _, ⟨_, .zero⟩ => 0
  | _ :: rest, ⟨field, .succ position⟩ => (toIndex (arities := rest) ⟨field, position⟩).succ

def ofIndex : (arities : List (MetaArity S)) → Fin arities.length → Slot arities
  | [], position => Fin.elim0 position
  | field :: rest, position => Fin.cases ⟨field, .zero⟩
      (fun tail => match ofIndex rest tail with | ⟨other, index⟩ => ⟨other, .succ index⟩) position

theorem ofIndex_toIndex : ∀ {arities : List (MetaArity S)} (slot : Slot arities),
    ofIndex arities (toIndex slot) = slot
  | [], ⟨_, impossible⟩ => nomatch impossible
  | _ :: _, ⟨_, .zero⟩ => rfl
  | _ :: rest, ⟨field, .succ position⟩ => by
      simp only [toIndex, ofIndex, Fin.cases_succ]
      rw [ofIndex_toIndex (arities := rest) ⟨field, position⟩]

theorem toIndex_ofIndex : ∀ (arities : List (MetaArity S)) (position : Fin arities.length),
    toIndex (ofIndex arities position) = position
  | [], position => Fin.elim0 position
  | field :: rest, position => by
      refine Fin.cases ?_ (fun tail => ?_) position
      · rfl
      · have shorter := toIndex_ofIndex rest tail
        cases opened : ofIndex rest tail with
        | mk other index =>
            rw [opened] at shorter
            change toIndex (match ofIndex rest tail with
              | ⟨other, index⟩ => (⟨other, Var.succ index⟩ : Slot (field :: rest))) = tail.succ
            rw [opened]
            exact congrArg Fin.succ shorter

def indexEquiv (arities : List (MetaArity S)) : Slot arities ≃ Fin arities.length where
  toFun := toIndex
  invFun := ofIndex arities
  left_inv := ofIndex_toIndex
  right_inv := toIndex_ofIndex arities

instance {arities : List (MetaArity S)} : DecidableEq (Slot arities) :=
  (indexEquiv arities).injective.decidableEq

instance {arities : List (MetaArity S)} : Fintype (Slot arities) :=
  Fintype.ofEquiv (Fin arities.length) (indexEquiv arities).symm

theorem cardinality (arities : List (MetaArity S)) : Fintype.card (Slot arities) = arities.length := by
  rw [Fintype.card_congr (indexEquiv arities), Fintype.card_fin]

end Mettapedia.OSLF.Binding.ArgumentSlots
