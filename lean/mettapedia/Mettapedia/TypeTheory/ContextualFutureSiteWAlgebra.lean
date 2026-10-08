import Mettapedia.TypeTheory.ContextualFutureSiteWCones
import Mettapedia.TypeTheory.ContextualSiteWAlgebra
import Mettapedia.TypeTheory.WiderContextualWLocalChange

/-!
# Complete future-cone algebra comparison at independent universe bounds

An arbitrary wider-valued algebra on each original small future category
induces an algebra on the independently formed raised signature. The
construction uses actual branch maps and context inverses. Its fold agrees
with the original fold on every natural tree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualFutureSiteWAlgebra

open CategoryTheory MaterialSets.Hypersets
open ContextualWReindexing
open PowerClassPresheafBaseChange

universe u v h
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}

def algebraCast {E : Type u} [Category.{u} E] {first second : Signature E}
    (same : first = second) (target : E ⥤ Type h)
    (algebra : WiderContextualWAlgebras.Algebra first.1 first.2 target) :
    WiderContextualWAlgebras.Algebra second.1 second.2 target := by
  cases same
  exact algebra

theorem fold_cast {E : Type u} [Category.{u} E] {first second : Signature E}
    (same : first = second) (target : E ⥤ Type h)
    (algebra : WiderContextualWAlgebras.Algebra first.1 first.2 target)
    (point : E) (tree : Tree first point) :
    WiderContextualWAlgebras.fold second.1 second.2 (algebraCast same target algebra)
      (signatureEquiv same point tree) = WiderContextualWAlgebras.fold first.1 first.2 algebra tree := by
  cases same
  rfl

variable (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (point : (ContextualFutureSiteLift.base P).Elements)
variable (target : Future.Objects point.1.down ⥤ Type h)

abbrev upperTarget := PresheafSiteLift.compose (ContextualFutureSiteWCones.toRaisedCone point.1)
  (ContextualSiteWAlgebra.upperTarget target)

noncomputable def algebra
    (original : WiderContextualWAlgebras.Algebra
      (ContextualFutureSiteWCones.oldSignature domain body point).1
      (ContextualFutureSiteWCones.oldSignature domain body point).2 target) :
    WiderContextualWAlgebras.Algebra
      (ContextualSmallFamilyTypeFormers.futureDomain (ContextualFutureSiteLift.family P domain) point)
      (ContextualSmallFamilyTypeFormers.futureBody (ContextualFutureSiteLift.family P domain)
        (ContextualFutureSiteLift.body P domain body) point) (upperTarget point target) :=
  algebraCast (ContextualFutureSiteWCones.signature_comparison domain body point) (upperTarget point target)
    (WiderContextualWLocalChange.pullAlgebra (ContextualFutureSiteWCones.change point.1)
      (ContextualFutureSiteWCones.raisedSignature domain body point).1
      (ContextualFutureSiteWCones.raisedSignature domain body point).2
      (ContextualSiteWAlgebra.upperTarget target)
      (ContextualSiteWAlgebra.algebra (ContextualFutureSiteWCones.oldSignature domain body point).1
        (ContextualFutureSiteWCones.oldSignature domain body point).2 target original))

theorem fold_comparison
    (original : WiderContextualWAlgebras.Algebra
      (ContextualFutureSiteWCones.oldSignature domain body point).1
      (ContextualFutureSiteWCones.oldSignature domain body point).2 target)
    (tree : ContextualSmallFamilyWTypes.WAt domain body ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    WiderContextualWAlgebras.fold
        (ContextualSmallFamilyTypeFormers.futureDomain (ContextualFutureSiteLift.family P domain) point)
        (ContextualSmallFamilyTypeFormers.futureBody (ContextualFutureSiteLift.family P domain)
          (ContextualFutureSiteLift.body P domain body) point)
        (algebra domain body point target original)
        ((ContextualFutureSiteWCones.equiv domain body point).symm tree) =
      WiderContextualWAlgebras.fold
        (ContextualFutureSiteWCones.oldSignature domain body point).1
        (ContextualFutureSiteWCones.oldSignature domain body point).2 original tree := by
  let old := ContextualFutureSiteWCones.oldSignature domain body point
  let raised := ContextualFutureSiteWCones.raisedSignature domain body point
  let root := ContextualSmallFamilyUniverse.root point.1
  let raisedAlgebra := ContextualSiteWAlgebra.algebra old.1 old.2 target original
  let raisedTree := ContextualSiteW.raiseNatural old.1 old.2
    ((ContextualFutureSiteWCones.toRaisedCone point.1).obj root) tree
  let pulledAlgebra := WiderContextualWLocalChange.pullAlgebra (ContextualFutureSiteWCones.change point.1)
    raised.1 raised.2 (ContextualSiteWAlgebra.upperTarget target) raisedAlgebra
  let pulledTree := ContextualWLocalChange.naturalEquiv (ContextualFutureSiteWCones.change point.1)
    raised.1 raised.2 root raisedTree
  have comparedTree : (ContextualFutureSiteWCones.equiv domain body point).symm tree =
      signatureEquiv (ContextualFutureSiteWCones.signature_comparison domain body point) root pulledTree := by
    apply Subtype.ext
    exact eq_of_heq ((ContextualFutureSiteWCones.inverse_raw domain body point tree).trans
      (signatureEquiv_raw (ContextualFutureSiteWCones.signature_comparison domain body point) root pulledTree).symm)
  rw [comparedTree]
  exact (fold_cast (ContextualFutureSiteWCones.signature_comparison domain body point)
    (upperTarget point target) pulledAlgebra root pulledTree).trans
      ((WiderContextualWLocalChange.fold_baseChange (ContextualFutureSiteWCones.change point.1)
        raised.1 raised.2 (ContextualSiteWAlgebra.upperTarget target) raisedAlgebra root raisedTree).trans
        (ContextualSiteWAlgebra.fold_raise old.1 old.2 target original
          ((ContextualFutureSiteWCones.toRaisedCone point.1).obj root) tree))

end Mettapedia.TypeTheory.ContextualFutureSiteWAlgebra
