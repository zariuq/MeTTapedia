import Mettapedia.TypeTheory.DisplayedPresheafEvidenceCoherence
import Mettapedia.TypeTheory.DisplayedPresheafFamilyAction

/-!
# The coherent action of proof-retaining dependent sums

Native dependent sums along context maps form a covariant pseudofunctor.
Its identity and composition comparisons are the actual receipt removal
and reassociation maps. The bicategorical coherence laws compare complete
dependent certificates rather than only their predicate supports.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafEvidenceAction

open CategoryTheory CategoryTheory.Bicategory
open DisplayedPresheafTransport DisplayedPresheafEvidenceTransport
open DisplayedPresheafEvidenceCoherence

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The native sum action with all identity, composition and associativity
coherences in the standard pseudofunctor interface. -/
def sumPseudofunctor (C : Type u) [Category.{u} C] :
    LocallyDiscrete (Cᵒᵖ ⥤ Type u) ⥤ᵖ Cat.{u, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun P => Cat.of (DisplayedFamily P))
    (fun f => (transportFunctor f).toCatHom)
    (fun P => Cat.Hom.isoMk (identityFunctorIso P))
    (fun f g => Cat.Hom.isoMk (compositionFunctorIso f g).symm)
    (by
      intro P Q R S f g h
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      apply NatTrans.ext
      funext point
      apply ConcreteCategory.hom_ext
      intro receipt
      apply Subtype.ext
      rfl)
    (by
      intro P Q f
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      apply NatTrans.ext
      funext point
      apply ConcreteCategory.hom_ext
      intro receipt
      apply Subtype.ext
      rfl)
    (by
      intro P Q f
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      change (compositionIso f (𝟙 Q) A).inv ≫
        (identityIso (transport f A)).hom = 𝟙 _
      rw [← composition_right_unit]
      exact (compositionIso f (𝟙 Q) A).inv_hom_id)

end Mettapedia.TypeTheory.DisplayedPresheafEvidenceAction
