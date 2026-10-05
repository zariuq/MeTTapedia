import Mettapedia.TypeTheory.ContextualSmallFamilyWiderPolynomialCone
import Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitution

/-!
# Wider natural algebras on the original contextual W family

The full future constructor operates on the unchanged small tree carrier.
An algebra with independent result universe induces an actual wider algebra
on each small future cone. Root evaluation uses a proved parameter cast.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderAlgebra

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes
open ContextualSmallFamilyWiderPolynomial (futureTarget)
open PowerClassPresheafBaseChange

universe u v h
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

noncomputable def localConstructorValue (point : base.Elements) (future : Future.Objects point.1)
    (node : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature domain body (w domain body) point) future) :
    ContextualWReindexing.Tree (signature domain body point) future :=
  (WiderContextualWAlgebras.treeAlgebra (futureDomain domain point) (futureBody domain body point)).make
    future node.1
    (node.2.map (WiderPresheafDependentFunctions.Hom.ofNatTrans
      (ContextualSmallFamilyWCone.coneReadoutInverse domain body point)))

noncomputable def constructorValue (point : base.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body (w domain body) point) : WAt domain body point :=
  localConstructorValue domain body point (ContextualSmallFamilyUniverse.root point.1) node

theorem constructor_pointCast (point : base.Elements) {first second : Future.Objects point.1} (same : first = second)
    (node : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature domain body (w domain body) point) first) :
    ContextualWReindexing.pointEquiv (signature domain body point) same (localConstructorValue domain body point first node) =
      localConstructorValue domain body point second
        (WiderContextualWPolynomialReindexing.pointEquiv
          (ContextualSmallFamilyWiderPolynomial.signature domain body (w domain body) point) same node) := by
  cases same
  rfl

theorem localConstructor_readout (point : base.Elements) (future : Future.Objects point.1)
    (label : (futureDomain domain point).obj future)
    (branches : WiderContextualWAlgebras.Branches (futureDomain domain point) (futureBody domain body point)
      (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point)) label) :
    localConstructorValue domain body point future
      ⟨label, branches.map (WiderPresheafDependentFunctions.Hom.ofNatTrans
      (ContextualSmallFamilyWCone.coneReadout domain body point))⟩ =
      (WiderContextualWAlgebras.treeAlgebra (futureDomain domain point) (futureBody domain body point)).make future label branches := by
  apply Subtype.ext
  apply ContextualWTypes.RawTree.sup_eq_of_cast rfl
  intro next arrow position
  exact congrArg Subtype.val
    ((ContextualSmallFamilyWCone.coneEquiv domain body point next).symm_apply_apply
      (branches.app next arrow position))

noncomputable def destructorValue (point : base.Elements) (tree : WAt domain body point) :
    ContextualSmallFamilyWiderPolynomial.At domain body (w domain body) point := by
  rcases tree with ⟨tree, natural⟩
  cases tree with
  | sup label children =>
    let branches : WiderContextualWAlgebras.Branches (futureDomain domain point) (futureBody domain body point)
        (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point)) label := {
      app next arrow branch := ⟨children next arrow branch, natural.1 next arrow branch⟩
      naturality next last first later branch := Subtype.ext (natural.2 next last first later branch) }
    exact ⟨label, branches.map (WiderPresheafDependentFunctions.Hom.ofNatTrans
      (ContextualSmallFamilyWCone.coneReadout domain body point))⟩

theorem constructor_destructor (point : base.Elements) (tree : WAt domain body point) :
    constructorValue domain body point (destructorValue domain body point tree) = tree := by
  rcases tree with ⟨tree, natural⟩
  cases tree with
  | sup label children =>
    apply Subtype.ext
    apply ContextualWTypes.RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact congrArg Subtype.val
      ((ContextualSmallFamilyWCone.coneEquiv domain body point next).symm_apply_apply
        (⟨children next arrow branch, natural.1 next arrow branch⟩ :
          ContextualWReindexing.Tree (signature domain body point) next))

theorem destructor_constructor (point : base.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body (w domain body) point) :
    destructorValue domain body point (constructorValue domain body point node) = node := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk label)
  apply WiderContextualWAlgebras.Branches.ext
  intro next arrow branch
  exact (ContextualSmallFamilyWCone.coneEquiv domain body point next).apply_symm_apply (branches.app next arrow branch)

noncomputable def constructorEquiv (point : base.Elements) :
    ContextualSmallFamilyWiderPolynomial.At domain body (w domain body) point ≃ WAt domain body point where
  toFun := constructorValue domain body point
  invFun := destructorValue domain body point
  left_inv := destructor_constructor domain body point
  right_inv := constructor_destructor domain body point

def rootValueEquiv (target : base.Elements ⥤ Type h) (point : base.Elements) :
    (futureTarget target point).obj (ContextualSmallFamilyUniverse.root point.1) ≃ target.obj point :=
  ContextualSmallFamilyUniverse.typeEqualityEquiv
    (congrArg target.obj (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1 point.2))

variable {target : base.Elements ⥤ Type h}
abbrev Algebra := WiderPresheafDependentFunctions.Hom (ContextualSmallFamilyWiderPolynomial.polynomial domain body target) target

noncomputable def localAlgebra (algebra : Algebra domain body (target := target)) (point : base.Elements) :
    WiderContextualWAlgebras.Algebra (futureDomain domain point) (futureBody domain body point) (futureTarget target point) where
  make future label branches := algebra.app (ContextualSmallFamilyWCone.futurePoint point future)
    (ContextualSmallFamilyWiderPolynomialCone.coneEquiv domain body target point future ⟨label, branches⟩)
  naturality first second step label branches := by
    have square := algebra.naturality
      ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step)
      (ContextualSmallFamilyWiderPolynomialCone.coneEquiv domain body target point first ⟨label, branches⟩)
    exact square.trans (congrArg (algebra.app (ContextualSmallFamilyWCone.futurePoint point second))
      (ContextualSmallFamilyWiderPolynomialCone.coneEquiv_natural domain body target point step ⟨label, branches⟩))

noncomputable def foldValue (algebra : Algebra domain body (target := target)) (point : base.Elements)
    (tree : WAt domain body point) : target.obj point :=
  rootValueEquiv target point
    (WiderContextualWAlgebras.fold (futureDomain domain point) (futureBody domain body point)
      (localAlgebra domain body algebra point) tree)

theorem foldValue_heq (algebra : Algebra domain body (target := target)) (point : base.Elements) (tree : WAt domain body point) :
    HEq (foldValue domain body algebra point tree)
      (WiderContextualWAlgebras.fold (futureDomain domain point) (futureBody domain body point)
        (localAlgebra domain body algebra point) tree) :=
  ContextualSmallFamilyUniverse.cast_heq _ _


end Mettapedia.TypeTheory.ContextualSmallFamilyWiderAlgebra
