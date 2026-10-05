import Mettapedia.TypeTheory.ContextualSmallFamilyWiderAlgebra

/-!
# Natural constructor for the mixed-universe W polynomial

The polynomial uses the new complete branch constructor, while the tree
carrier remains the original small indexed W family. The proof compares
complete polynomial branch values with constructed cone-tree inverses. Saved parameter equations are retained even when
prefixing histories is not globally injective.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderConstructor

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes ContextualSmallFamilyWiderAlgebra
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

theorem constructor_natural {first second : base.Elements} (step : first ⟶ second)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body (w domain body) first) :
    wMap domain body step (constructorValue domain body first node) =
      constructorValue domain body second (ContextualSmallFamilyWiderPolynomial.pMap domain body (w domain body) step node) := by
  apply Subtype.ext
  apply eq_of_heq
  refine (wMap_raw domain body step (constructorValue domain body first node)).trans ?_
  let oldSignature := ContextualSmallFamilyWiderPolynomial.signature domain body (w domain body) first
  let contextMap := ContextualSmallFamilyUniverse.futurePrefix step.1
  let root := ContextualSmallFamilyUniverse.root second.1
  let sourceNode := WiderContextualWPolynomialReindexing.pull contextMap oldSignature root
    ((WiderContextualWPolynomialReindexing.family oldSignature).map (ContextualSmallFamilyUniverse.rootArrow step.1) node)
  let newNode := ContextualSmallFamilyWiderPolynomial.pMap domain body (w domain body) step node
  have signatureEq := ContextualSmallFamilyWiderPolynomial.signature_prefix domain body (w domain body) step
  have nodeEq : HEq sourceNode newNode := (ContextualSmallFamilyWiderPolynomial.pMap_value domain body (w domain body) step node).symm
  have labels := WiderContextualWPolynomialReindexing.node_label_heq signatureEq root sourceNode newNode nodeEq
  have branches := WiderContextualWPolynomialReindexing.node_branches_heq signatureEq root sourceNode newNode nodeEq
  apply ContextualWReindexing.sup_heq (signature_prefix domain body step) rfl sourceNode.1 newNode.1 labels
  intro future firstArrow secondArrow arrows firstBranch secondBranch positions
  let oldChild := (ContextualSmallFamilyWCone.coneEquiv domain body first (contextMap.obj future)).symm
    (sourceNode.2.app future firstArrow firstBranch)
  let newChild := (ContextualSmallFamilyWCone.coneEquiv domain body second future).symm
    (newNode.2.app future secondArrow secondBranch)
  change HEq (ContextualWReindexing.pull contextMap (signature domain body first) future oldChild.val) newChild.val
  have values := WiderContextualWPolynomialReindexing.branch_app_heq signatureEq sourceNode.1 newNode.1 labels
    sourceNode.2 newNode.2 branches future firstArrow secondArrow arrows firstBranch secondBranch positions
  have prefixSquare := ContextualSmallFamilyWCone.prefix_readout_whole domain body step future oldChild
  have oldValue := (ContextualSmallFamilyWCone.coneEquiv domain body first (contextMap.obj future)).apply_symm_apply
    (sourceNode.2.app future firstArrow firstBranch)
  have readout : (ContextualSmallFamilyWCone.coneEquiv domain body second future)
      (ContextualSmallFamilyWCone.prefixEquiv domain body step future oldChild) =
        newNode.2.app future secondArrow secondBranch :=
    eq_of_heq (prefixSquare.symm.trans ((heq_of_eq oldValue).trans values))
  have children : ContextualSmallFamilyWCone.prefixEquiv domain body step future oldChild = newChild :=
    (ContextualSmallFamilyWCone.coneEquiv domain body second future).injective
      (readout.trans ((ContextualSmallFamilyWCone.coneEquiv domain body second future).apply_symm_apply
        (newNode.2.app future secondArrow secondBranch)).symm)
  exact (ContextualSmallFamilyWCone.prefixEquiv_raw domain body step future oldChild).symm.trans
    (heq_of_eq (congrArg Subtype.val children))

theorem localConstructor_prefix {first second : base.Elements} (step : first ⟶ second) (future : Future.Objects second.1)
    (node : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature domain body (w domain body) first)
      ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future)) :
    ContextualSmallFamilyWCone.prefixEquiv domain body step future
      (localConstructorValue domain body first ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) node) =
      localConstructorValue domain body second future
        (ContextualSmallFamilyWiderPolynomialCone.prefixEquiv domain body (w domain body) step future node) := by
  apply Subtype.ext
  apply eq_of_heq
  refine (ContextualSmallFamilyWCone.prefixEquiv_raw domain body step future
    (localConstructorValue domain body first ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) node)).trans ?_
  let oldSignature := ContextualSmallFamilyWiderPolynomial.signature domain body (w domain body) first
  let contextMap := ContextualSmallFamilyUniverse.futurePrefix step.1
  let sourceNode := WiderContextualWPolynomialReindexing.pull contextMap oldSignature future node
  let newNode := ContextualSmallFamilyWiderPolynomialCone.prefixEquiv domain body (w domain body) step future node
  have signatureEq := ContextualSmallFamilyWiderPolynomial.signature_prefix domain body (w domain body) step
  have nodeEq : HEq sourceNode newNode :=
    (ContextualSmallFamilyWiderPolynomialCone.prefixEquiv_value domain body (w domain body) step future node).symm
  have labels := WiderContextualWPolynomialReindexing.node_label_heq signatureEq future sourceNode newNode nodeEq
  have branches := WiderContextualWPolynomialReindexing.node_branches_heq signatureEq future sourceNode newNode nodeEq
  apply ContextualWReindexing.sup_heq (signature_prefix domain body step) rfl sourceNode.1 newNode.1 labels
  intro next firstArrow secondArrow arrows firstBranch secondBranch positions
  let oldChild := (ContextualSmallFamilyWCone.coneEquiv domain body first (contextMap.obj next)).symm
    (sourceNode.2.app next firstArrow firstBranch)
  let newChild := (ContextualSmallFamilyWCone.coneEquiv domain body second next).symm
    (newNode.2.app next secondArrow secondBranch)
  change HEq (ContextualWReindexing.pull contextMap (signature domain body first) next oldChild.val) newChild.val
  have values := WiderContextualWPolynomialReindexing.branch_app_heq signatureEq sourceNode.1 newNode.1 labels
    sourceNode.2 newNode.2 branches next firstArrow secondArrow arrows firstBranch secondBranch positions
  have prefixSquare := ContextualSmallFamilyWCone.prefix_readout_whole domain body step next oldChild
  have oldValue := (ContextualSmallFamilyWCone.coneEquiv domain body first (contextMap.obj next)).apply_symm_apply
    (sourceNode.2.app next firstArrow firstBranch)
  have readout : (ContextualSmallFamilyWCone.coneEquiv domain body second next)
      (ContextualSmallFamilyWCone.prefixEquiv domain body step next oldChild) =
        newNode.2.app next secondArrow secondBranch :=
    eq_of_heq (prefixSquare.symm.trans ((heq_of_eq oldValue).trans values))
  have children : ContextualSmallFamilyWCone.prefixEquiv domain body step next oldChild = newChild :=
    (ContextualSmallFamilyWCone.coneEquiv domain body second next).injective
      (readout.trans ((ContextualSmallFamilyWCone.coneEquiv domain body second next).apply_symm_apply
        (newNode.2.app next secondArrow secondBranch)).symm)
  exact (ContextualSmallFamilyWCone.prefixEquiv_raw domain body step next oldChild).symm.trans
    (heq_of_eq (congrArg Subtype.val children))

noncomputable def constructor :
    NatTrans (ContextualSmallFamilyWiderPolynomial.polynomial domain body (w domain body)) (w domain body) where
  app point := TypeCat.ofHom (constructorValue domain body point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro node
    exact (constructor_natural domain body step node).symm

noncomputable def destructor :
    NatTrans (w domain body) (ContextualSmallFamilyWiderPolynomial.polynomial domain body (w domain body)) where
  app point := TypeCat.ofHom (destructorValue domain body point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro tree
    apply (constructorEquiv domain body second).injective
    change constructorValue domain body second (destructorValue domain body second (wMap domain body step tree)) =
      constructorValue domain body second
        (ContextualSmallFamilyWiderPolynomial.pMap domain body (w domain body) step (destructorValue domain body first tree))
    exact (constructor_destructor domain body second (wMap domain body step tree)).trans
      ((congrArg (wMap domain body step) (constructor_destructor domain body first tree)).symm.trans
        (constructor_natural domain body step (destructorValue domain body first tree)))

theorem constructor_destructor_whole : composeNat (destructor domain body) (constructor domain body) = identityNat (w domain body) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact constructor_destructor domain body point

theorem destructor_constructor_whole :
    composeNat (constructor domain body) (destructor domain body) =
      identityNat (ContextualSmallFamilyWiderPolynomial.polynomial domain body (w domain body)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact destructor_constructor domain body point

theorem constructor_coneReadout (point : base.Elements) (future : Future.Objects point.1)
    (node : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature domain body (w domain body) point) future) :
    ContextualSmallFamilyWCone.coneEquiv domain body point future (localConstructorValue domain body point future node) =
      constructorValue domain body (ContextualSmallFamilyWCone.futurePoint point future)
        (ContextualSmallFamilyWiderPolynomialCone.coneEquiv domain body (w domain body) point future node) := by
  let root := ContextualSmallFamilyUniverse.root future.1
  let raised := WiderContextualWPolynomialReindexing.pointEquiv
    (ContextualSmallFamilyWiderPolynomial.signature domain body (w domain body) point)
    (ContextualSmallFamilyWCone.nativeRoot_eq point future).symm node
  change ContextualSmallFamilyWCone.prefixEquiv domain body (ContextualSmallFamilyWCone.futureStep point future) root
    (ContextualWReindexing.pointEquiv (signature domain body point)
      (ContextualSmallFamilyWCone.nativeRoot_eq point future).symm (localConstructorValue domain body point future node)) =
    localConstructorValue domain body (ContextualSmallFamilyWCone.futurePoint point future) root
      (ContextualSmallFamilyWiderPolynomialCone.prefixEquiv domain body (w domain body)
        (ContextualSmallFamilyWCone.futureStep point future) root raised)
  rw [constructor_pointCast]
  exact localConstructor_prefix domain body (ContextualSmallFamilyWCone.futureStep point future) root raised

end Mettapedia.TypeTheory.ContextualSmallFamilyWiderConstructor
