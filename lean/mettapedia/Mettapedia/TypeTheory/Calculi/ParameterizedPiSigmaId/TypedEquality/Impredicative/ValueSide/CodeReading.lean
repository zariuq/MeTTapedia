import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Carriers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.CodeConstants

/-!
# The code constants on the value side

Over every realizer algebra, a closed term with one meaning at an interpretable
carrier, in every world, is related to itself by the pack of the carrier, its
only denotation, and it is realized there by the realizers of its meaning
(`carrier_closed`).

For a package of proposition codes read by the value model, the code constants
have meanings at their carriers, in every world:

* implication, the function space of the meanings of its arguments
  (`read_imp`);
* a quantifier, Girard's clause at its carrier over the meanings of its
  argument (`read_all`);
* an equation, the identity candidate of the equality of the meanings of its
  arguments (`read_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Kind Carrier World Truth Read CodesRead)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

/-- **A closed term with one meaning at an interpretable carrier** is related to
itself by every denotation of the carrier's type, which is the carrier's pack,
and it is realized there by the realizers of its meaning. -/
theorem carrier_closed (laws : V.Laws) {k : Kind} {C : Carrier k}
    (hC : C.Interpretable V.toModel) {c : Tm Head 0} {v : C.V V.reading}
    (read : ∀ {m : Nat} (ξ : World V.reading m), Read V.reading ξ (liftClosed c) C v)
    {n : Nat} (ξ : World V.reading n) {P : Pack V n}
    (den : DenS V ξ (liftClosed (C.term V.toModel)) P) :
    P.rel (liftClosed c) (liftClosed c) ∧
      P.real (liftClosed c) = V.alg.Real V.toSetting V.star V.num C v := by
  obtain rfl := DenS.deterministic laws den ⟨LevelOrder.bot, carrier_interp laws hC ξ⟩
  exact ⟨(carrierPack_rel laws C ξ _ _).mpr ⟨v, read ξ, read ξ⟩,
    carrierPack_real laws C (read ξ)⟩

section Read

variable {K : Codes Head} (read : CodesRead V.toModel K)
include read

/-- Implication means the function space of the meanings of its arguments, in
every world. -/
theorem read_imp {n : Nat} (ξ : World V.reading n) :
    Read V.reading ξ (liftClosed (.const K.imp)) (.arr .prop (.arr .prop .prop))
      (fun X Y => V.reading.impMeaning X Y) := by
  change Read V.reading ξ (.const K.imp) _ _
  rw [read.imp]
  exact .genericArg fun X => .genericArg fun Y =>
    .prop (Truth.imp .refl (Read.generic' _ rfl).prop_inv (Read.generic' _ rfl).prop_inv)

omit read in
/-- A quantifier means Girard's clause at its carrier over the meanings of its
argument, in every world. -/
theorem read_all {a : DeclName} {k : Kind} {A : Carrier k}
    (carrier : V.allCarrier a = some ⟨k, A⟩) {n : Nat} (ξ : World V.reading n) :
    Read V.reading ξ (liftClosed (.const a)) (.arr (.arr A .prop) .prop)
      (fun φ => V.reading.allMeaning A φ) :=
  .genericArg fun _ => .prop (Truth.all carrier .refl (Read.generic' _ rfl))

omit read in
/-- An equation means the identity candidate of the equality of the meanings of
its arguments, in every world. -/
theorem read_eq {e : DeclName} {k : Kind} {A : Carrier k}
    (carrier : V.eqCarrier e = some ⟨k, A⟩) {n : Nat} (ξ : World V.reading n) :
    Read V.reading ξ (liftClosed (.const e)) (.arr A (.arr A .prop))
      (fun x y => V.reading.eqMeaning A x y) := by
  cases k with
  | gen =>
      exact .genericArg fun x => .genericArg fun y =>
        .prop (Truth.eq carrier .refl (Read.generic' _ rfl) (Read.generic' _ rfl))
  | data =>
      exact .dataArg fun {_ _ _} _ {_} rs => .dataArg fun {_ _ ρ'} _ {_} rs' =>
        .prop (Truth.eq carrier .refl (Read.data_rename rs ρ') (.data rs'))

end Read

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
