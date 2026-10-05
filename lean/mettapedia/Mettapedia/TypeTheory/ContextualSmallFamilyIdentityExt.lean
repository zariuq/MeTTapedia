import Mettapedia.TypeTheory.ContextualSmallFamilyIdentity

/-! Coordinate extensionality for the actual nested discrete identity
context. Both endpoint values are retained; the singleton witness is
compared only after its endpoint coordinates have been identified. -/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyIdentity

open CategoryTheory
open MaterialSets.Hypersets

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u)

theorem receipt_ext {point : D} (first second : (identityContext domain).obj point)
    (parameter : first.1.1.1 = second.1.1.1)
    (left : HEq first.1.1.2 second.1.1.2)
    (right : HEq first.1.2 second.1.2) : first = second := by
  rcases first with ⟨⟨⟨parameterFirst, leftFirst⟩, rightFirst⟩, witnessFirst⟩
  rcases second with ⟨⟨⟨parameterSecond, leftSecond⟩, rightSecond⟩, witnessSecond⟩
  dsimp only at parameter left right
  cases parameter
  cases eq_of_heq left
  cases eq_of_heq right
  change PresheafIdentityWitness.Witness leftFirst rightFirst at witnessFirst witnessSecond
  exact congrArg (fun witness =>
    (⟨⟨⟨parameterFirst, leftFirst⟩, rightFirst⟩, witness⟩ : (identityContext domain).obj point))
      ((PresheafIdentityWitness.encode_decode witnessFirst).symm.trans
        (PresheafIdentityWitness.encode_decode witnessSecond))

end Mettapedia.TypeTheory.ContextualSmallFamilyIdentity
