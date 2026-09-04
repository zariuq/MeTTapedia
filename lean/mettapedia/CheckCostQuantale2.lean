import Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.Algebra.QuantaleWeakness
abbrev LC := Multiplicative (OrderDual ENNReal)
noncomputable instance : CompleteLattice LC := inferInstanceAs (CompleteLattice (OrderDual ENNReal))
#synth Monoid LC
#synth CompleteLattice LC
example (x : LC) (s : Set LC) : x * sSup s = ⨆ y ∈ s, x * y := by
  change (OrderDual.ofDual x : ENNReal) + sInf (OrderDual.ofDual '' s) = _
  sorry
