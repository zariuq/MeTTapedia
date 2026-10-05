import Mettapedia.TypeTheory.ContextualSmallFamilyWPolynomialCone
import Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitution

/-!
# Constructed full future W constructors and local algebra recursion

The constructor and destructor operate on complete compatible future
branches and are actual pointwise inverses. An arbitrary natural algebra
on the independently constructed polynomial induces a local algebra on
every small future cone, where indexed well-founded recursion supplies
the fold. Global coherence is treated separately from these constructions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWAlgebra

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

noncomputable def localConstructorValue (point : base.Elements) (future : Future.Objects point.1)
    (node : ContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWPolynomial.signature domain body (w domain body) point) future) :
    ContextualWReindexing.Tree (signature domain body point) future :=
  (ContextualWTypes.treeAlgebra (futureDomain domain point) (futureBody domain body point)).make
    future node.1
    (node.2.map (ContextualSmallFamilyWCone.coneReadoutInverse domain body point))

noncomputable def constructorValue (point : base.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point) : WAt domain body point :=
  localConstructorValue domain body point (ContextualSmallFamilyUniverse.root point.1) node

theorem constructor_pointCast (point : base.Elements) {first second : Future.Objects point.1} (same : first = second)
    (node : ContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWPolynomial.signature domain body (w domain body) point) first) :
    ContextualWReindexing.pointEquiv (signature domain body point) same (localConstructorValue domain body point first node) =
      localConstructorValue domain body point second
        (ContextualWPolynomialReindexing.pointEquiv
          (ContextualSmallFamilyWPolynomial.signature domain body (w domain body) point) same node) := by
  cases same
  rfl

theorem localConstructor_readout (point : base.Elements) (future : Future.Objects point.1)
    (label : (futureDomain domain point).obj future)
    (branches : ContextualWTypes.Branches (futureDomain domain point) (futureBody domain body point)
      (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point)) label) :
    localConstructorValue domain body point future
      ⟨label, branches.map (ContextualSmallFamilyWCone.coneReadout domain body point)⟩ =
      (ContextualWTypes.treeAlgebra (futureDomain domain point) (futureBody domain body point)).make future label branches := by
  apply Subtype.ext
  apply ContextualWTypes.RawTree.sup_eq_of_cast rfl
  intro next arrow position
  exact congrArg Subtype.val
    ((ContextualSmallFamilyWCone.coneEquiv domain body point next).symm_apply_apply
      (branches.app next arrow position))

noncomputable def destructorValue (point : base.Elements) (tree : WAt domain body point) :
    ContextualSmallFamilyWPolynomial.At domain body (w domain body) point := by
  rcases tree with ⟨tree, natural⟩
  cases tree with
  | sup label children =>
    let branches : ContextualWTypes.Branches (futureDomain domain point) (futureBody domain body point)
        (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point)) label := {
      app next arrow branch := ⟨children next arrow branch, natural.1 next arrow branch⟩
      naturality next last first later branch := Subtype.ext (natural.2 next last first later branch) }
    exact ⟨label, branches.map (ContextualSmallFamilyWCone.coneReadout domain body point)⟩

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
    (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point) :
    destructorValue domain body point (constructorValue domain body point node) = node := by
  rcases node with ⟨label, branches⟩
  apply congrArg (Sigma.mk label)
  apply ContextualWTypes.Branches.ext
  intro next arrow branch
  exact (ContextualSmallFamilyWCone.coneEquiv domain body point next).apply_symm_apply (branches.app next arrow branch)

noncomputable def constructorEquiv (point : base.Elements) :
    ContextualSmallFamilyWPolynomial.At domain body (w domain body) point ≃ WAt domain body point where
  toFun := constructorValue domain body point
  invFun := destructorValue domain body point
  left_inv := destructor_constructor domain body point
  right_inv := constructor_destructor domain body point

variable {target : base.Elements ⥤ Type u}
abbrev Algebra := NatTrans (ContextualSmallFamilyWPolynomial.polynomial domain body target) target

noncomputable def localAlgebra (algebra : Algebra domain body (target := target)) (point : base.Elements) :
    ContextualWTypes.Algebra (futureDomain domain point) (futureBody domain body point) (futureDomain target point) where
  make future label branches := algebra.app (ContextualSmallFamilyWCone.futurePoint point future)
    (ContextualSmallFamilyWPolynomialCone.coneEquiv domain body target point future ⟨label, branches⟩)
  naturality first second step label branches := by
    have square := congrArg (fun operation => operation
      (ContextualSmallFamilyWPolynomialCone.coneEquiv domain body target point first ⟨label, branches⟩))
      (algebra.naturality ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step))
    exact square.symm.trans (congrArg (algebra.app (ContextualSmallFamilyWCone.futurePoint point second))
      (ContextualSmallFamilyWPolynomialCone.coneEquiv_natural domain body target point step ⟨label, branches⟩))

noncomputable def foldValue (algebra : Algebra domain body (target := target)) (point : base.Elements)
    (tree : WAt domain body point) : target.obj point :=
  ContextualSmallFamilyUniverse.evaluationEquiv target point.1 point.2
    (ContextualWTypes.fold (futureDomain domain point) (futureBody domain body point)
      (localAlgebra domain body algebra point) tree)

theorem foldValue_heq (algebra : Algebra domain body (target := target)) (point : base.Elements) (tree : WAt domain body point) :
    HEq (foldValue domain body algebra point tree)
      (ContextualWTypes.fold (futureDomain domain point) (futureBody domain body point)
        (localAlgebra domain body algebra point) tree) :=
  ContextualSmallFamilyUniverse.cast_heq _ _

end Mettapedia.TypeTheory.ContextualSmallFamilyWAlgebra
