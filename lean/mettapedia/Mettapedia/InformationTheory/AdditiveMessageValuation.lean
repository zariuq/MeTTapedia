import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Additive valuations of commutative messages

A finite multiset is the free commutative monoid on its atoms.  Consequently,
an atomic cost extends uniquely to an additive value on multiset messages.
This is the precise algebraic core behind an MDL-like message valuation:
model and data messages compose by multiset addition, while their costs add.

The construction deliberately stops at the monoidal theorem it proves.  It is
not called a quantale merely because the target might later be embedded into a
Lawvere or tropical cost quantale; that stronger structure requires its own
complete-lattice and distributivity laws.

Reference: B. Goertzel, *Weakness Is All You Need: Quantale Weakness as a
Unifying Principle for Cognition* (2026), Section 3, for the generalized-MDL
motivation.  The free-commutative-monoid formulation and its uniqueness theorem
below state the mathematically supported part independently of the paper's
broader quantale proposal.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.AdditiveMessageValuation

universe uAtom uCost

variable {Atom : Type uAtom} {Cost : Type uCost}

/-- Cost assigned to each atom of a commutative message. -/
structure Valuation (Atom : Type uAtom) (Cost : Type uCost) where
  atomCost : Atom → Cost

namespace Valuation

variable [AddCommMonoid Cost]

/-- The additive extension of an atomic valuation to finite multiset
messages. -/
def value (valuation : Valuation Atom Cost) (message : Multiset Atom) : Cost :=
  (message.map valuation.atomCost).sum

@[simp]
theorem value_zero (valuation : Valuation Atom Cost) :
    valuation.value 0 = 0 := by
  simp [value]

@[simp]
theorem value_singleton (valuation : Valuation Atom Cost) (atom : Atom) :
    valuation.value {atom} = valuation.atomCost atom := by
  simp [value]

/-- Message composition is evaluated additively. -/
@[simp]
theorem value_add (valuation : Valuation Atom Cost)
    (left right : Multiset Atom) :
    valuation.value (left + right) =
      valuation.value left + valuation.value right := by
  simp [value]

/-- The additive extension as a bundled monoid homomorphism. -/
def toAddMonoidHom (valuation : Valuation Atom Cost) :
    Multiset Atom →+ Cost where
  toFun := valuation.value
  map_zero' := valuation.value_zero
  map_add' := valuation.value_add

/-- Universal property: an additive message evaluator is uniquely determined
by its values on singleton atoms. -/
theorem unique_additive_extension
    (valuation : Valuation Atom Cost)
    (candidate : Multiset Atom →+ Cost)
    (agreesOnAtoms : ∀ atom, candidate {atom} = valuation.atomCost atom) :
    candidate = valuation.toAddMonoidHom := by
  ext atom
  simpa [toAddMonoidHom] using agreesOnAtoms atom

/-- A model message and a data-given-model message evaluate as one composite
message. -/
theorem twoPartValue_eq_composite
    (valuation : Valuation Atom Cost)
    (modelMessage dataGivenModelMessage : Multiset Atom) :
    valuation.value modelMessage + valuation.value dataGivenModelMessage =
      valuation.value (modelMessage + dataGivenModelMessage) := by
  rw [value_add]

end Valuation

/-! ## Unit-length specialization and weighted control -/

/-- Every atom costs one natural-number unit. -/
def unitNat : Valuation Atom Nat where
  atomCost := fun _ => 1

/-- Unit additive valuation recovers ordinary multiset length exactly. -/
@[simp]
theorem unitNat_value (message : Multiset Atom) :
    unitNat.value message = message.card := by
  simp [Valuation.value, unitNat]

namespace WeightedCanary

/-- A nonuniform atomic cost used to show that additive valuation is
layer-relative rather than determined by message length. -/
def weightedBool : Valuation Bool Nat where
  atomCost
    | false => 1
    | true => 3

def twoLightAtoms : Multiset Bool := {false, false}
def oneHeavyAtom : Multiset Bool := {true}

theorem card_order : oneHeavyAtom.card < twoLightAtoms.card := by
  decide

/-- The nonuniform valuation reverses the ordinary length comparison. -/
theorem weighted_order_reverses_cardinality :
    weightedBool.value twoLightAtoms < weightedBool.value oneHeavyAtom := by
  decide

/-- Message length does not determine a nonuniform additive valuation. -/
theorem weightedValue_not_factorsThrough_card :
    ¬ (weightedBool.value).FactorsThrough Multiset.card := by
  intro factors
  let left : Multiset Bool := {false}
  let right : Multiset Bool := {true}
  have sameCard : left.card = right.card := by decide
  have equalValue := factors sameCard
  simp [left, right, weightedBool, Valuation.value] at equalValue

end WeightedCanary

end Mettapedia.InformationTheory.AdditiveMessageValuation

#print axioms Mettapedia.InformationTheory.AdditiveMessageValuation.Valuation.unique_additive_extension
#print axioms Mettapedia.InformationTheory.AdditiveMessageValuation.unitNat_value
#print axioms Mettapedia.InformationTheory.AdditiveMessageValuation.WeightedCanary.weightedValue_not_factorsThrough_card
