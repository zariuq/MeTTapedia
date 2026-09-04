import Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent

/-!
# The price of conversion: uniqueness of typing degrades to uniqueness up to conversion

This module states each side's price as a theorem over the dependent core of
`SimpleSliceOfDependent`; it does not select a native calculus.

* STT price (already proved there): genuine dependency is inexpressible —
  `dependentType_not_image`.
* DTT price (proved here): the moment a conversion rule enters, typing stops
  being syntax-directed.  `conv_breaks_uniqueness` exhibits one term with two
  syntactically different types.  `uniqueness_up_to_conv` shows exactly what
  survives: types are unique only up to convertibility — so a checker must
  decide (or be handed certificates for) conversion.  This is the
  proof-size/checking-cost trade stated in-tree.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent

open Expr

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Declarative convertibility: β at the root, reflexivity, symmetry,
transitivity.  Deliberately the smallest relation that makes the point. -/
inductive Conv : Expr Base Const → Expr Base Const → Prop where
  | beta (A b a : Expr Base Const) :
      Conv (app (lam A b) a) (substAt 0 a b)
  | refl (e : Expr Base Const) : Conv e e
  | symm {e₁ e₂ : Expr Base Const} : Conv e₁ e₂ → Conv e₂ e₁
  | trans {e₁ e₂ e₃ : Expr Base Const} : Conv e₁ e₂ → Conv e₂ e₃ → Conv e₁ e₃

/-- Typing with a conversion rule on top of the syntax-directed core. -/
inductive HasTypeC (Γ : List (Expr Base Const)) :
    Expr Base Const → Expr Base Const → Prop where
  | of {e A : Expr Base Const} : HasType Γ e A → HasTypeC Γ e A
  | conv {e A B : Expr Base Const} :
      HasTypeC Γ e A → Conv A B → HasTypeC Γ e B

/-- **The DTT price.**  With conversion, one term carries two syntactically
different types: syntax-directed checking is gone. -/
theorem conv_breaks_uniqueness (b : Base) :
    ∃ (e A B : Expr Base Const), A ≠ B ∧
      HasTypeC [] e A ∧ HasTypeC [] e B := by
  refine ⟨top, prop, app (lam (base b) prop) top, ?_, ?_, ?_⟩
  · intro h
    cases h
  · exact HasTypeC.of HasType.top
  · exact HasTypeC.conv (HasTypeC.of HasType.top)
      (Conv.symm (Conv.beta (base b) prop top))

/-- **What survives.**  Types remain unique up to convertibility, so a
checker for the converted theory must decide `Conv` (or be handed a
certificate for it): conversion work moves into checking or into the
certificate — nowhere else. -/
theorem uniqueness_up_to_conv {Γ : List (Expr Base Const)}
    {e A : Expr Base Const} (h₁ : HasTypeC Γ e A) :
    ∀ {B : Expr Base Const}, HasTypeC Γ e B → Conv A B := by
  induction h₁ with
  | of hA =>
    intro B h₂
    induction h₂ with
    | of hB => exact (hA.unique hB) ▸ Conv.refl _
    | conv _ step ih => exact Conv.trans ih step
  | conv _ step ih =>
    intro B h₂
    exact Conv.trans (Conv.symm step) (ih h₂)

/-- The conversion-free core keeps exact uniqueness (restated here beside its
degraded sibling for contrast). -/
theorem uniqueness_without_conv {Γ : List (Expr Base Const)}
    {e A B : Expr Base Const}
    (h₁ : HasType Γ e A) (h₂ : HasType Γ e B) : A = B :=
  h₁.unique h₂

#print axioms conv_breaks_uniqueness
#print axioms uniqueness_up_to_conv

end Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
