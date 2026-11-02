import Mettapedia.Languages.Maude.BagCardinality

/-! Cardinality is unchanged by the source bag's ACU presentation. The
proof first uses the actual carrier's flattening law and then its authored
cardinality equations; it does not invoke the native normalizer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.BagCardinality

theorem card_presentation_equivalent (source : Term)
    (typed : HasSort Examples.cardinality.signature [] source "Bag")
    (letters : List String) (allowed : ∀ letter ∈ letters, Allowed letter)
    (presentation : operation.flatten source = letters.map token) :
    Equivalent Examples.cardinality [] "Nat" (card source) (numeral letters.length) := by
  have flattened := Equivalent.argument cardFrame
    (operation.equivalent_fold_flatten (by decide_cbv) typed)
  rw [presentation] at flattened
  exact flattened.trans (card_fold_equivalent letters allowed)

#print axioms card_presentation_equivalent

end Mettapedia.Languages.Maude.BagCardinality
