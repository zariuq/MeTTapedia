import Mettapedia.TypeTheory.ContextualSmallFamilyWTypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignatureEquivalence

/-!
# Dependent contextual signatures on small complete future cones

An arbitrary wider parameter is retained in the transported native shape
and body. Their natural signature equivalence induces a concrete small
future signature and full indexed W tree maps at every parameter.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWSignature

open CategoryTheory MaterialSets.Hypersets

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable {domain nextDomain : base.Elements ⥤ Type u}
variable {body : domain.Elements ⥤ Type u} {nextBody : nextDomain.Elements ⥤ Type u}
variable (data : WiderPresheafSignatureEquivalence.Signature (shape := domain) (nextShape := nextDomain)
  (position := body) (nextPosition := nextBody))

def signature (point : base.Elements) : ContextualWSignature.Signature
    (shape := ContextualSmallFamilyTypeFormers.futureDomain domain point)
    (nextShape := ContextualSmallFamilyTypeFormers.futureDomain nextDomain point)
    (position := ContextualSmallFamilyTypeFormers.futureBody domain body point)
    (nextPosition := ContextualSmallFamilyTypeFormers.futureBody nextDomain nextBody point) where
  shapes future := data.shapes ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future)
  shape_natural step label :=
    data.shape_natural ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step) label
  positions future label := data.positions
    ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj future) label
  position_natural step label branch :=
    data.position_natural ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step) label branch

noncomputable def equiv (point : base.Elements) :
    ContextualSmallFamilyWTypes.WAt domain body point ≃ ContextualSmallFamilyWTypes.WAt nextDomain nextBody point :=
  ContextualWSignatureEquivalence.naturalEquiv (signature data point) (ContextualSmallFamilyUniverse.root point.1)

end Mettapedia.TypeTheory.ContextualSmallFamilyWSignature
