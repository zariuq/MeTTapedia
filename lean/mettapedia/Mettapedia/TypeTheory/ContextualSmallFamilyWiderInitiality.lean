import Mettapedia.TypeTheory.ContextualSmallFamilyWiderRecursion
import Mettapedia.TypeTheory.ContextualSmallFamilyWiderConstructor
import Mettapedia.TypeTheory.ContextualSmallFamilyWiderAction

/-!
# Mixed-universe initiality of the original-bound contextual W family

The fold satisfies the full future constructor equation. Every natural
algebra morphism is this fold, by indexed recursion on the actual cone
trees. Both the parameter presheaf and arbitrary algebra consumers may occupy
independent larger host universes; the W carrier remains at its original bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderInitiality

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes ContextualSmallFamilyWiderAlgebra
open ContextualSmallFamilyWiderRecursion PowerClassPresheafBaseChange

universe u v h
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable {target : base.Elements ⥤ Type h} (algebra : Algebra domain body (target := target))

theorem fold_beta (point : base.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body (w domain body) point) :
    foldValue domain body algebra point (constructorValue domain body point node) =
      algebra.app point (ContextualSmallFamilyWiderAction.mapValue domain body (foldMap domain body algebra) point node) := by
  apply eq_of_heq
  let branches := node.2.map (WiderPresheafDependentFunctions.Hom.ofNatTrans
    (ContextualSmallFamilyWCone.coneReadoutInverse domain body point))
  have nativeBeta := WiderContextualWAlgebras.fold_beta (futureDomain domain point) (futureBody domain body point)
    (localAlgebra domain body algebra point) node.1 branches
  have branchValues : branches.map
      (WiderContextualWAlgebras.foldMap (futureDomain domain point) (futureBody domain body point)
        (localAlgebra domain body algebra point)) =
      node.2.map (ContextualSmallFamilyWiderAction.onCone (foldMap domain body algebra) point) := by
    apply WiderContextualWAlgebras.Branches.ext
    intro future arrow position
    let value := node.2.app future arrow position
    let child := (ContextualSmallFamilyWCone.coneEquiv domain body point future).symm value
    have readout := fold_readout domain body algebra point future child
    have recovered := congrArg (foldValue domain body algebra (ContextualSmallFamilyWCone.futurePoint point future))
      ((ContextualSmallFamilyWCone.coneEquiv domain body point future).apply_symm_apply value)
    exact eq_of_heq (readout.symm.trans (heq_of_eq recovered))
  have afterBranches := congrArg
    ((localAlgebra domain body algebra point).make (ContextualSmallFamilyUniverse.root point.1) node.1) branchValues
  have afterReadout := ContextualSmallFamilyNativeAdjunction.homApplication_heq algebra
    (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1 point.2)
    (ContextualSmallFamilyWiderPolynomialCone.coneEquiv domain body target point
      (ContextualSmallFamilyUniverse.root point.1)
      (ContextualSmallFamilyWiderAction.mapValue domain body (foldMap domain body algebra) point node))
    (ContextualSmallFamilyWiderAction.mapValue domain body (foldMap domain body algebra) point node)
    (ContextualSmallFamilyWiderPolynomialCone.coneEquiv_root_heq domain body target point
      (ContextualSmallFamilyWiderAction.mapValue domain body (foldMap domain body algebra) point node))
  exact (foldValue_heq domain body algebra point (constructorValue domain body point node)).trans
    ((heq_of_eq nativeBeta).trans ((heq_of_eq afterBranches).trans afterReadout))

theorem fold_constructor :
    (WiderPresheafDependentFunctions.Hom.ofNatTrans
      (ContextualSmallFamilyWiderConstructor.constructor domain body)).comp (foldMap domain body algebra) =
      (ContextualSmallFamilyWiderAction.map domain body (foldMap domain body algebra)).comp algebra := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point
  exact fold_beta domain body algebra point

noncomputable def localCandidate (candidate : WiderPresheafDependentFunctions.Hom (w domain body) target) (point : base.Elements) :
    WiderPresheafDependentFunctions.Hom (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point))
      (ContextualSmallFamilyWiderPolynomial.futureTarget target point) :=
  (WiderPresheafDependentFunctions.Hom.ofNatTrans
    (ContextualSmallFamilyWCone.coneReadout domain body point)).comp
      (ContextualSmallFamilyWiderAction.onCone candidate point)

theorem localCandidate_constructor (candidate : WiderPresheafDependentFunctions.Hom (w domain body) target)
    (constructorLaw : ∀ (point : base.Elements)
      (node : ContextualSmallFamilyWiderPolynomial.At domain body (w domain body) point),
      candidate.app point (constructorValue domain body point node) =
        algebra.app point (ContextualSmallFamilyWiderAction.mapValue domain body candidate point node))
    (point : base.Elements) (future : Future.Objects point.1)
    (label : (futureDomain domain point).obj future)
    (branches : WiderContextualWAlgebras.Branches (futureDomain domain point) (futureBody domain body point)
      (ContextualWTypes.family (futureDomain domain point) (futureBody domain body point)) label) :
    (localCandidate domain body candidate point).app future
      ((WiderContextualWAlgebras.treeAlgebra (futureDomain domain point) (futureBody domain body point)).make future label branches) =
      (localAlgebra domain body algebra point).make future label
        (branches.map (localCandidate domain body candidate point)) := by
  let inputNode : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature domain body (w domain body) point) future :=
    ⟨label, branches.map (WiderPresheafDependentFunctions.Hom.ofNatTrans
      (ContextualSmallFamilyWCone.coneReadout domain body point))⟩
  have constructorReadout := (congrArg (ContextualSmallFamilyWCone.coneEquiv domain body point future)
    (localConstructor_readout domain body point future label branches)).symm.trans
      (ContextualSmallFamilyWiderConstructor.constructor_coneReadout domain body point future inputNode)
  have evaluated := congrArg (candidate.app (ContextualSmallFamilyWCone.futurePoint point future)) constructorReadout
  have law := constructorLaw (ContextualSmallFamilyWCone.futurePoint point future)
    (ContextualSmallFamilyWiderPolynomialCone.coneEquiv domain body (w domain body) point future inputNode)
  have actionSquare := ContextualSmallFamilyWiderAction.mapValue_coneReadout domain body candidate point future inputNode
  have afterAction := ContextualSmallFamilyNativeAdjunction.homApplication_heq algebra rfl _ _ actionSquare.symm
  have branchValues : inputNode.2.map (ContextualSmallFamilyWiderAction.onCone candidate point) =
      branches.map (localCandidate domain body candidate point) := by
    apply WiderContextualWAlgebras.Branches.ext
    intro next arrow position
    rfl
  have afterBranches := congrArg ((localAlgebra domain body algebra point).make future label) branchValues
  exact evaluated.trans (law.trans ((eq_of_heq afterAction).trans afterBranches))

theorem fold_unique (candidate : WiderPresheafDependentFunctions.Hom (w domain body) target)
    (constructorLaw : ∀ (point : base.Elements)
      (node : ContextualSmallFamilyWiderPolynomial.At domain body (w domain body) point),
      candidate.app point (constructorValue domain body point node) =
        algebra.app point (ContextualSmallFamilyWiderAction.mapValue domain body candidate point node)) :
    candidate = foldMap domain body algebra := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point tree
  apply eq_of_heq
  have localUnique := WiderContextualWAlgebras.fold_unique (futureDomain domain point) (futureBody domain body point)
    (localAlgebra domain body algebra point) (localCandidate domain body candidate point)
    (localCandidate_constructor domain body algebra candidate constructorLaw point)
  have rootValue := ContextualSmallFamilyNativeAdjunction.homApplication_heq candidate
    (ContextualSmallFamilyUniverse.evaluationPoint_eq point.1 point.2)
    (ContextualSmallFamilyWCone.coneEquiv domain body point (ContextualSmallFamilyUniverse.root point.1) tree) tree
    (ContextualSmallFamilyWCone.coneEquiv_root_heq domain body point tree)
  have comparedFold := congrArg
    (fun operation => operation.app (ContextualSmallFamilyUniverse.root point.1) tree) localUnique
  exact rootValue.symm.trans ((heq_of_eq comparedFold).trans (foldValue_heq domain body algebra point tree).symm)

theorem initiality : ∃! candidate : WiderPresheafDependentFunctions.Hom (w domain body) target,
    ∀ (point : base.Elements) (node : ContextualSmallFamilyWiderPolynomial.At domain body (w domain body) point),
      candidate.app point (constructorValue domain body point node) =
        algebra.app point (ContextualSmallFamilyWiderAction.mapValue domain body candidate point node) := by
  refine ⟨foldMap domain body algebra, fold_beta domain body algebra, ?_⟩
  intro candidate law
  exact fold_unique domain body algebra candidate law

end Mettapedia.TypeTheory.ContextualSmallFamilyWiderInitiality
