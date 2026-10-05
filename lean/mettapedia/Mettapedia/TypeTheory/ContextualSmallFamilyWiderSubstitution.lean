import Mettapedia.TypeTheory.ContextualSmallFamilyWiderInitiality

/-!
# Mixed-universe W algebra substitution over arbitrary parameters

The independently formed polynomial and W fibres are compared through
whole future signatures. Transported algebras and their folds retain
original target values, including under noninjective parameter maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderSubstitution

open CategoryTheory MaterialSets.Hypersets ContextualWitnessCover
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyTypeFormerCoherence
open ContextualSmallFamilyWTypes ContextualSmallFamilyWSubstitution ContextualSmallFamilyWiderAlgebra
open PowerClassPresheafBaseChange

universe u v w z h k l
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v} {other : D ⥤ Type w}
variable (change : NaturalHom other base) (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (target : base.Elements ⥤ Type h)


abbrev targetUnder (family : base.Elements ⥤ Type k) : other.Elements ⥤ Type k :=
  ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.elementMap change) family

def restrictHom {E : Type v} {K : Type w} [Category.{u} E] [Category.{u} K]
    (map : E ⥤ K) {first : K ⥤ Type h} {second : K ⥤ Type k}
    (operation : WiderPresheafDependentFunctions.Hom first second) :
    WiderPresheafDependentFunctions.Hom (ContextualSmallFamilyUniverse.restrict map first)
      (ContextualSmallFamilyUniverse.restrict map second) where
  app point := operation.app (map.obj point)
  naturality step value := operation.naturality (map.map step) value

theorem futureTarget_change (point : other.Elements) :
    ContextualSmallFamilyWiderPolynomial.futureTarget (targetUnder change target) point =
      ContextualSmallFamilyWiderPolynomial.futureTarget target
        ((ContextualSmallFamilyUniverse.elementMap change).obj point) := by
  refine Functor.hext (fun future => congrArg target.obj (changeFuturePoint_eq change point future).symm) ?_
  intro first second step
  exact ContextualSmallFamilyWiderPolynomial.familyArrow_heq target
    (changeFuturePoint_eq change point first).symm (changeFuturePoint_eq change point second).symm
    ((ContextualSmallFamilyUniverse.elementMap change).map
      ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map step))
    ((ContextualSmallFamilyUniverse.futureElement point.1 (change.app point.1 point.2)).map step)
    (ContextualSmallFamilyUniverse.elementsArrow_heq
      (changeFuturePoint_eq change point first).symm (changeFuturePoint_eq change point second).symm _ _ HEq.rfl)

theorem polynomial_signature_change (point : other.Elements) :
    ContextualSmallFamilyWiderPolynomial.signature domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj point) =
      ContextualSmallFamilyWiderPolynomial.signature (domainUnder change domain) (bodyUnder change domain body)
        (targetUnder change target) point :=
  Prod.ext (signature_change change domain body point) (futureTarget_change change target point).symm

def polynomialComparison (point : other.Elements) :
    ContextualSmallFamilyWiderPolynomial.At domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj point) ≃
      ContextualSmallFamilyWiderPolynomial.At (domainUnder change domain) (bodyUnder change domain body)
        (targetUnder change target) point :=
  WiderContextualWPolynomialReindexing.signatureEquiv (polynomial_signature_change change domain body target point)
    (ContextualSmallFamilyUniverse.root point.1)

theorem polynomialComparison_value (point : other.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    HEq (polynomialComparison change domain body target point node) node :=
  WiderContextualWPolynomialReindexing.signatureEquiv_heq _ _ _

theorem polynomialComparison_inverse_value (point : other.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At (domainUnder change domain) (bodyUnder change domain body)
      (targetUnder change target) point) :
    HEq ((polynomialComparison change domain body target point).symm node) node := by
  have compared := polynomialComparison_value change domain body target point
    ((polynomialComparison change domain body target point).symm node)
  exact compared.symm.trans
    (heq_of_eq ((polynomialComparison change domain body target point).apply_symm_apply node))

theorem polynomialComparison_natural {first second : other.Elements} (step : first ⟶ second)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj first)) :
    polynomialComparison change domain body target second
      (ContextualSmallFamilyWiderPolynomial.pMap domain body target
        ((ContextualSmallFamilyUniverse.elementMap change).map step) node) =
      ContextualSmallFamilyWiderPolynomial.pMap (domainUnder change domain) (bodyUnder change domain body)
        (targetUnder change target) step (polynomialComparison change domain body target first node) := by
  apply eq_of_heq
  have restricted := WiderContextualWPolynomialReindexing.restrict_signature_heq
    (polynomial_signature_change change domain body target first)
    (ContextualSmallFamilyUniverse.rootArrow step.1) node
    (polynomialComparison change domain body target first node)
    (polynomialComparison_value change domain body target first node).symm
  have pulled := WiderContextualWPolynomialReindexing.pull_congr
    (first := ContextualSmallFamilyUniverse.futurePrefix step.1) rfl
    (polynomial_signature_change change domain body target first) rfl _ _ restricted
  exact (polynomialComparison_value change domain body target second _).trans
    ((ContextualSmallFamilyWiderPolynomial.pMap_value domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).map step) node).trans
        (pulled.trans (ContextualSmallFamilyWiderPolynomial.pMap_value (domainUnder change domain)
          (bodyUnder change domain body) (targetUnder change target) step _).symm))

def polynomialSubstitution :
    NatTrans (targetUnder change (ContextualSmallFamilyWiderPolynomial.polynomial domain body target))
      (ContextualSmallFamilyWiderPolynomial.polynomial (domainUnder change domain) (bodyUnder change domain body)
        (targetUnder change target)) where
  app point := TypeCat.ofHom (polynomialComparison change domain body target point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    exact polynomialComparison_natural change domain body target step

def polynomialSubstitutionInverse :
    NatTrans (ContextualSmallFamilyWiderPolynomial.polynomial (domainUnder change domain) (bodyUnder change domain body)
      (targetUnder change target))
      (targetUnder change (ContextualSmallFamilyWiderPolynomial.polynomial domain body target)) where
  app point := TypeCat.ofHom (polynomialComparison change domain body target point).symm
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro node
    apply (polynomialComparison change domain body target second).injective
    change polynomialComparison change domain body target second
      ((polynomialComparison change domain body target second).symm
        (ContextualSmallFamilyWiderPolynomial.pMap _ _ _ step node)) =
      polynomialComparison change domain body target second
        (ContextualSmallFamilyWiderPolynomial.pMap domain body target
          ((ContextualSmallFamilyUniverse.elementMap change).map step)
          ((polynomialComparison change domain body target first).symm node))
    exact ((polynomialComparison change domain body target second).apply_symm_apply _).trans
      ((congrArg (ContextualSmallFamilyWiderPolynomial.pMap _ _ _ step)
        ((polynomialComparison change domain body target first).apply_symm_apply node)).symm.trans
          (polynomialComparison_natural change domain body target step _).symm)

theorem polynomialSubstitution_left :
    composeNat (polynomialSubstitution change domain body target) (polynomialSubstitutionInverse change domain body target) =
      identityNat (targetUnder change (ContextualSmallFamilyWiderPolynomial.polynomial domain body target)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (polynomialComparison change domain body target point).symm_apply_apply

theorem polynomialSubstitution_right :
    composeNat (polynomialSubstitutionInverse change domain body target) (polynomialSubstitution change domain body target) =
      identityNat (ContextualSmallFamilyWiderPolynomial.polynomial (domainUnder change domain) (bodyUnder change domain body)
        (targetUnder change target)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (polynomialComparison change domain body target point).apply_symm_apply

theorem polynomial_cone_readout (point : other.Elements) (future : Future.Objects point.1)
    (firstNode : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature domain body target
        ((ContextualSmallFamilyUniverse.elementMap change).obj point)) future)
    (secondNode : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature (domainUnder change domain) (bodyUnder change domain body)
        (targetUnder change target) point) future) (nodes : HEq firstNode secondNode) :
    HEq (ContextualSmallFamilyWiderPolynomialCone.coneEquiv domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj point) future firstNode)
      (ContextualSmallFamilyWiderPolynomialCone.coneEquiv (domainUnder change domain) (bodyUnder change domain body)
        (targetUnder change target) point future secondNode) := by
  have pulled := WiderContextualWPolynomialReindexing.pullData_congr
    (first := ContextualSmallFamilyUniverse.futurePrefix future.2) rfl
    (polynomial_signature_change change domain body target point) rfl firstNode secondNode nodes
    (ContextualSmallFamilyWCone.nativeRoot_eq ((ContextualSmallFamilyUniverse.elementMap change).obj point) future)
    (ContextualSmallFamilyWCone.nativeRoot_eq point future)
  exact (ContextualSmallFamilyWiderPolynomialCone.coneEquiv_value domain body target
    ((ContextualSmallFamilyUniverse.elementMap change).obj point) future firstNode).trans
      (pulled.trans (ContextualSmallFamilyWiderPolynomialCone.coneEquiv_value (domainUnder change domain)
        (bodyUnder change domain body) (targetUnder change target) point future secondNode).symm)

variable {target}
def substitutedAlgebra (algebra : Algebra domain body (target := target)) :
    Algebra (domainUnder change domain) (bodyUnder change domain body) (target := targetUnder change target) :=
  (WiderPresheafDependentFunctions.Hom.ofNatTrans
    (polynomialSubstitutionInverse change domain body target)).comp
      (restrictHom (ContextualSmallFamilyUniverse.elementMap change) algebra)

theorem localAlgebra_substitution (algebra : Algebra domain body (target := target)) (point : other.Elements) :
    HEq (localAlgebra domain body algebra ((ContextualSmallFamilyUniverse.elementMap change).obj point))
      (localAlgebra (domainUnder change domain) (bodyUnder change domain body)
        (substitutedAlgebra change domain body algebra) point) := by
  apply WiderContextualWAlgebraReindexing.algebra_ext_heq
    (polynomial_signature_change change domain body target point)
  intro future firstLabel secondLabel labels firstBranches secondBranches branches
  let firstNode : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature domain body target
        ((ContextualSmallFamilyUniverse.elementMap change).obj point)) future := ⟨firstLabel, firstBranches⟩
  let secondNode : WiderContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWiderPolynomial.signature (domainUnder change domain) (bodyUnder change domain body)
        (targetUnder change target) point) future := ⟨secondLabel, secondBranches⟩
  have nodeEq := WiderContextualWAlgebraReindexing.node_heq
    (polynomial_signature_change change domain body target point) future firstLabel secondLabel labels firstBranches secondBranches branches
  have readout := polynomial_cone_readout change domain body target point future firstNode secondNode nodeEq
  have recovered := polynomialComparison_inverse_value change domain body target
    (ContextualSmallFamilyWCone.futurePoint point future)
    (ContextualSmallFamilyWiderPolynomialCone.coneEquiv (domainUnder change domain) (bodyUnder change domain body)
      (targetUnder change target) point future secondNode)
  exact ContextualSmallFamilyNativeAdjunction.homApplication_heq algebra (changeFuturePoint_eq change point future) _ _ (readout.trans recovered.symm)

theorem fold_substitution (algebra : Algebra domain body (target := target)) (point : other.Elements)
    (tree : WAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    foldValue domain body algebra ((ContextualSmallFamilyUniverse.elementMap change).obj point) tree =
      foldValue (domainUnder change domain) (bodyUnder change domain body)
        (substitutedAlgebra change domain body algebra) point (wComparison change domain body point tree) := by
  apply eq_of_heq
  have nativeFold := WiderContextualWAlgebraReindexing.fold_heq
    (polynomial_signature_change change domain body target point) rfl
    (localAlgebra domain body algebra ((ContextualSmallFamilyUniverse.elementMap change).obj point))
    (localAlgebra (domainUnder change domain) (bodyUnder change domain body)
      (substitutedAlgebra change domain body algebra) point)
    (localAlgebra_substitution change domain body algebra point) tree (wComparison change domain body point tree)
    (wComparison_raw change domain body point tree).symm
  exact (foldValue_heq domain body algebra ((ContextualSmallFamilyUniverse.elementMap change).obj point) tree).trans
    (nativeFold.trans (foldValue_heq (domainUnder change domain) (bodyUnder change domain body)
      (substitutedAlgebra change domain body algebra) point (wComparison change domain body point tree)).symm)

theorem foldMap_substitution (algebra : Algebra domain body (target := target)) :
    restrictHom (ContextualSmallFamilyUniverse.elementMap change)
      (ContextualSmallFamilyWiderRecursion.foldMap domain body algebra) =
      (WiderPresheafDependentFunctions.Hom.ofNatTrans (wSubstitution change domain body)).comp
        (ContextualSmallFamilyWiderRecursion.foldMap (domainUnder change domain) (bodyUnder change domain body)
          (substitutedAlgebra change domain body algebra)) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point tree
  exact fold_substitution change domain body algebra point tree

theorem polynomialComparison_identity (point : base.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body target point) :
    HEq (polynomialComparison (ContextualSmallMapConstructions.identity base) domain body target point node) node :=
  polynomialComparison_value (ContextualSmallMapConstructions.identity base) domain body target point node

theorem polynomialComparison_composition {third : D ⥤ Type z}
    (first : NaturalHom other base) (later : NaturalHom third other) (point : third.Elements)
    (node : ContextualSmallFamilyWiderPolynomial.At domain body target
      ((ContextualSmallFamilyUniverse.elementMap (later.comp first)).obj point)) :
    HEq (polynomialComparison later (domainUnder first domain) (bodyUnder first domain body)
      (targetUnder first target) point
      (polynomialComparison first domain body target ((ContextualSmallFamilyUniverse.elementMap later).obj point) node))
      (polynomialComparison (later.comp first) domain body target point node) :=
  (polynomialComparison_value later (domainUnder first domain) (bodyUnder first domain body)
    (targetUnder first target) point _).trans
      ((polynomialComparison_value first domain body target ((ContextualSmallFamilyUniverse.elementMap later).obj point) node).trans
        (polynomialComparison_value (later.comp first) domain body target point node).symm)

theorem fold_substitution_identity (algebra : Algebra domain body (target := target))
    (point : base.Elements) (tree : WAt domain body point) :
    foldValue (domainUnder (ContextualSmallMapConstructions.identity base) domain)
      (bodyUnder (ContextualSmallMapConstructions.identity base) domain body)
      (substitutedAlgebra (ContextualSmallMapConstructions.identity base) domain body algebra) point
      (wComparison (ContextualSmallMapConstructions.identity base) domain body point tree) =
      foldValue domain body algebra point tree :=
  (fold_substitution (ContextualSmallMapConstructions.identity base) domain body algebra point tree).symm

theorem fold_substitution_composition {third : D ⥤ Type z}
    (first : NaturalHom other base) (later : NaturalHom third other)
    (algebra : Algebra domain body (target := target)) (point : third.Elements)
    (tree : WAt domain body ((ContextualSmallFamilyUniverse.elementMap (later.comp first)).obj point)) :
    foldValue (domainUnder later (domainUnder first domain))
      (bodyUnder later (domainUnder first domain) (bodyUnder first domain body))
      (substitutedAlgebra later (domainUnder first domain) (bodyUnder first domain body)
        (substitutedAlgebra first domain body algebra)) point
      (wComparison later (domainUnder first domain) (bodyUnder first domain body) point
        (wComparison first domain body ((ContextualSmallFamilyUniverse.elementMap later).obj point) tree)) =
      foldValue (domainUnder (later.comp first) domain) (bodyUnder (later.comp first) domain body)
        (substitutedAlgebra (later.comp first) domain body algebra) point
        (wComparison (later.comp first) domain body point tree) :=
  (fold_substitution later (domainUnder first domain) (bodyUnder first domain body)
    (substitutedAlgebra first domain body algebra) point _).symm.trans
      ((fold_substitution first domain body algebra ((ContextualSmallFamilyUniverse.elementMap later).obj point) tree).symm.trans
        (fold_substitution (later.comp first) domain body algebra point tree))

end Mettapedia.TypeTheory.ContextualSmallFamilyWiderSubstitution
