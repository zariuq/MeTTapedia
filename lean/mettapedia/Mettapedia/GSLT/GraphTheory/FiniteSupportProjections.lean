import Mathlib.Data.Finset.Sum

/-!
# Finite supports in a disjoint union

The component projections are operations on finite sets. They do not supply
a total injective graph-model coding: a code must also retain the support
outside the selected component.

They coincide with Mathlib's `Finset.toLeft` and `Finset.toRight`
(`PartialPair.projectLeft_eq_toLeft`, `PartialPair.projectRight_eq_toRight`).
-/

namespace Mettapedia.GSLT.GraphTheory

/-- Project a finite support to its left component. -/
def projectLeft {α β : Type*} [DecidableEq α] (support : Finset (α ⊕ β)) : Finset α :=
  support.filterMap (fun x => match x with | .inl a => some a | .inr _ => none)
    (by intro a b; cases a <;> cases b <;> simp [eq_comm])

/-- Project a finite support to its right component. -/
def projectRight {α β : Type*} [DecidableEq β] (support : Finset (α ⊕ β)) : Finset β :=
  support.filterMap (fun x => match x with | .inl _ => none | .inr b => some b)
    (by intro a b; cases a <;> cases b <;> simp [eq_comm])

end Mettapedia.GSLT.GraphTheory
