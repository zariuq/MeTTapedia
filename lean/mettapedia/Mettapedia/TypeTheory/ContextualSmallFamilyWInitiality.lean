import Mettapedia.TypeTheory.ContextualSmallFamilyWRecursion
import Mettapedia.TypeTheory.ContextualSmallFamilyWConstructor
import Mettapedia.TypeTheory.ContextualSmallFamilyWAction

/-!
# Initiality of the constructed original-bound contextual W family

The fold satisfies the full future constructor equation. Every natural
algebra morphism is this fold, by indexed recursion on the actual cone
trees. The parameter presheaf may occupy a larger host universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWInitiality

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes ContextualSmallFamilyWAlgebra
open ContextualSmallFamilyWRecursion PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable {target : base.Elements ⥤ Type u} (algebra : Algebra domain body (target := target))

theorem fold_beta (point : base.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point) :
    foldValue domain body algebra point (constructorValue domain body point node) =
      algebra.app point (ContextualSmallFamilyWAction.mapValue domain body (foldMap domain body algebra) point node) := by
  apply eq_of_heq
  let branches := node.2.map (ContextualSmallFamilyWCone.coneReadoutInverse domain body point)
  have nativeBeta := ContextualWTypes.fold_beta (futureDomain domain point) (futureBody domain body point)
    (localAlgebra domain body algebra point) node.1 branches
  have branchValues : branches.map
      (ContextualWTypes.foldMap (futureDomain domain point) (futureBody domain body point)
        (localAlgebra domain body algebra point)) =
      node.2.map (ContextualSmallFamilyWAction.onCone (foldMap domain body algebra) point) := by
    apply ContextualWTypes.Branches.ext
    intro future arrow position
    let value := node.2.app future arrow position
    let child := (ContextualSmallFamilyWCone.coneEquiv domain body point future).symm value
    have readout := fold_readout domain body algebra point future child
    have recovered := congrArg (foldValue domain body algebra (ContextualSmallFamilyWCone.futurePoint point future))
      ((ContextualSmallFamilyWCone.coneEquiv domain body point future).apply_symm_apply value)
    exact eq_of_heq (readout.symm.trans (heq_of_eq recovered))
  have afterBranches := congrArg
    ((localAlgebra domain body algebra point).make (ContextualSmallFamilyUniverse.root point.1) node.1) branchValues
  have afterReadout := naturalApplication_heq algebra
    (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1 point.2)
    (ContextualSmallFamilyWPolynomialCone.coneEquiv domain body target point
      (ContextualSmallFamilyUniverse.root point.1)
      (ContextualSmallFamilyWAction.mapValue domain body (foldMap domain body algebra) point node))
    (ContextualSmallFamilyWAction.mapValue domain body (foldMap domain body algebra) point node)
    (ContextualSmallFamilyWPolynomialCone.coneEquiv_root_heq domain body target point
      (ContextualSmallFamilyWAction.mapValue domain body (foldMap domain body algebra) point node))
  exact (foldValue_heq domain body algebra point (constructorValue domain body point node)).trans
    ((heq_of_eq nativeBeta).trans ((heq_of_eq afterBranches).trans afterReadout))

theorem fold_constructor :
    composeNat (ContextualSmallFamilyWConstructor.constructor domain body) (foldMap domain body algebra) =
      composeNat (ContextualSmallFamilyWAction.map domain body (foldMap domain body algebra)) algebra := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact fold_beta domain body algebra point

noncomputable def localCandidate (candidate : NatTrans (w domain body) target) (point : base.Elements) :
    NatTrans (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point))
      (futureDomain target point) :=
  composeNat (ContextualSmallFamilyWCone.coneReadout domain body point)
    (ContextualSmallFamilyWAction.onCone candidate point)

theorem localCandidate_constructor (candidate : NatTrans (w domain body) target)
    (constructorLaw : ∀ (point : base.Elements)
      (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point),
      candidate.app point (constructorValue domain body point node) =
        algebra.app point (ContextualSmallFamilyWAction.mapValue domain body candidate point node))
    (point : base.Elements) (future : Future.Objects point.1)
    (label : (futureDomain domain point).obj future)
    (branches : ContextualWTypes.Branches (futureDomain domain point) (futureBody domain body point)
      (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point)) label) :
    (localCandidate domain body candidate point).app future
      ((ContextualWTypes.treeAlgebra (futureDomain domain point) (futureBody domain body point)).make future label branches) =
      (localAlgebra domain body algebra point).make future label
        (branches.map (localCandidate domain body candidate point)) := by
  let inputNode : ContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWPolynomial.signature domain body (w domain body) point) future :=
    ⟨label, branches.map (ContextualSmallFamilyWCone.coneReadout domain body point)⟩
  have constructorReadout := (congrArg (ContextualSmallFamilyWCone.coneEquiv domain body point future)
    (localConstructor_readout domain body point future label branches)).symm.trans
      (ContextualSmallFamilyWConstructor.constructor_coneReadout domain body point future inputNode)
  have evaluated := congrArg (candidate.app (ContextualSmallFamilyWCone.futurePoint point future)) constructorReadout
  have law := constructorLaw (ContextualSmallFamilyWCone.futurePoint point future)
    (ContextualSmallFamilyWPolynomialCone.coneEquiv domain body (w domain body) point future inputNode)
  have actionSquare := ContextualSmallFamilyWAction.mapValue_coneReadout domain body candidate point future inputNode
  have afterAction := naturalApplication_heq algebra rfl _ _ actionSquare.symm
  have branchValues : inputNode.2.map (ContextualSmallFamilyWAction.onCone candidate point) =
      branches.map (localCandidate domain body candidate point) := by
    apply ContextualWTypes.Branches.ext
    intro next arrow position
    rfl
  have afterBranches := congrArg ((localAlgebra domain body algebra point).make future label) branchValues
  exact evaluated.trans (law.trans ((eq_of_heq afterAction).trans afterBranches))

theorem fold_unique (candidate : NatTrans (w domain body) target)
    (constructorLaw : ∀ (point : base.Elements)
      (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point),
      candidate.app point (constructorValue domain body point node) =
        algebra.app point (ContextualSmallFamilyWAction.mapValue domain body candidate point node)) :
    candidate = foldMap domain body algebra := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro tree
  apply eq_of_heq
  have localUnique := ContextualWTypes.fold_unique (futureDomain domain point) (futureBody domain body point)
    (localAlgebra domain body algebra point) (localCandidate domain body candidate point)
    (localCandidate_constructor domain body algebra candidate constructorLaw point)
  have rootValue := naturalApplication_heq candidate
    (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1 point.2)
    (ContextualSmallFamilyWCone.coneEquiv domain body point (ContextualSmallFamilyUniverse.root point.1) tree) tree
    (ContextualSmallFamilyWCone.coneEquiv_root_heq domain body point tree)
  have comparedFold := congrArg
    (fun operation => operation.app (ContextualSmallFamilyUniverse.root point.1) tree) localUnique
  exact rootValue.symm.trans ((heq_of_eq comparedFold).trans (foldValue_heq domain body algebra point tree).symm)

theorem initiality : ∃! candidate : NatTrans (w domain body) target,
    ∀ (point : base.Elements) (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body) point),
      candidate.app point (constructorValue domain body point node) =
        algebra.app point (ContextualSmallFamilyWAction.mapValue domain body candidate point node) := by
  refine ⟨foldMap domain body algebra, fold_beta domain body algebra, ?_⟩
  intro candidate law
  exact fold_unique domain body algebra candidate law

end Mettapedia.TypeTheory.ContextualSmallFamilyWInitiality
