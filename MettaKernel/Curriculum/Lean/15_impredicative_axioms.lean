/- Lean 15 — KERNEL FEATURES: impredicative Prop (imax) + the trusted axiom base.
   `imax u 0 = 0` makes a forall landing in Prop a Prop regardless of the domain's
   universe.  Lean's logic rests on propext, Classical.choice, Quot.sound (funext is
   derived).  A faithful kernel must implement imax AND track these axioms. -/
namespace L15

-- IMPREDICATIVE Prop: quantify over Prop, or over ALL of Type, and still land in Prop
def ImpredTrue : Prop := ∀ (p : Prop), p → p
example : ImpredTrue := fun _ h => h
def BigProp : Prop := ∀ (α : Type), α → True
#check (BigProp : Prop)

-- the trusted axioms
theorem eq_of_iff (a b : Prop) (h : a ↔ b) : a = b := propext h
theorem em' (p : Prop) : p ∨ ¬ p := Classical.em p
theorem fun_ext (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := funext h

-- LEDGER: concrete syntax which trusted axioms each result depends on
#print axioms eq_of_iff
#print axioms em'
#print axioms fun_ext

end L15
