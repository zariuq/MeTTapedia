import Mettapedia.TypeTheory.ContextualWAlgebraReindexing

/-!
# Coherent contextual W recursion over wider parameters

Arbitrary natural algebras induce the actual cone algebras. Their prefix
coherence is derived from complete polynomial readouts and the saved
parameter equation. The fold uses indexed well-founded recursion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWRecursion

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWTypes ContextualSmallFamilyWAlgebra
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable {target : base.Elements ⥤ Type u} (algebra : Algebra domain body (target := target))

theorem localAlgebra_prefix {first second : base.Elements} (step : first ⟶ second) :
    HEq (ContextualWLocalChange.pullAlgebra (ContextualWLocalChange.prefixChange step.1)
      (futureDomain domain first) (futureBody domain body first) (futureDomain target first)
      (localAlgebra domain body algebra first)) (localAlgebra domain body algebra second) := by
  apply ContextualWAlgebraReindexing.algebra_ext_heq
    (ContextualSmallFamilyWPolynomial.signature_prefix domain body target step)
  intro future label otherLabel labels branches otherBranches branchEq
  let oldSignature := ContextualSmallFamilyWPolynomial.signature domain body target first
  let oldNode : ContextualWPolynomialReindexing.At oldSignature
      ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj future) :=
    ⟨label, ContextualWLocalChange.pushBranches (ContextualWLocalChange.prefixChange step.1)
      (futureDomain domain first) (futureBody domain body first) (futureDomain target first) future label branches⟩
  let sourceNode : ContextualWPolynomialReindexing.At
      (ContextualWPolynomialReindexing.under (ContextualSmallFamilyUniverse.futurePrefix step.1) oldSignature) future :=
    ⟨label, branches⟩
  let rightNode : ContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWPolynomial.signature domain body target second) future := ⟨otherLabel, otherBranches⟩
  have pullInverse : ContextualWPolynomialReindexing.pull (ContextualSmallFamilyUniverse.futurePrefix step.1)
      oldSignature future oldNode = sourceNode :=
    congrArg (Sigma.mk label) (ContextualWLocalChange.pull_pushBranches
      (ContextualWLocalChange.prefixChange step.1) (futureDomain domain first) (futureBody domain body first)
      (futureDomain target first) future label branches)
  have nodeEq := ContextualWAlgebraReindexing.node_heq
    (ContextualSmallFamilyWPolynomial.signature_prefix domain body target step) future label otherLabel labels
    branches otherBranches branchEq
  have transported := (ContextualSmallFamilyWPolynomialCone.prefixEquiv_value domain body target step future oldNode).trans
    ((heq_of_eq pullInverse).trans nodeEq)
  have readout := (ContextualSmallFamilyWPolynomialCone.prefix_readout domain body target step future oldNode).trans
    (heq_of_eq (congrArg (ContextualSmallFamilyWPolynomialCone.coneEquiv domain body target second future)
      (eq_of_heq transported)))
  exact naturalApplication_heq algebra (prefixPoint_eq step future) _ _ readout

theorem target_rootMap_heq {first second : base.Elements} (step : first ⟶ second)
    (left : target.obj first) (right : (futureDomain target first).obj (ContextualSmallFamilyUniverse.root first.1))
    (values : HEq left right) :
    HEq (target.map step left)
      ((futureDomain target first).map (ContextualSmallFamilyUniverse.rootArrow step.1) right) := by
  have source := ContextualSmallFamilyUniverse.evaluationPoint_eq first.1 first.2
  have destination : (ContextualSmallFamilyUniverse.futureElement first.1 first.2).obj
      ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj (ContextualSmallFamilyUniverse.root second.1)) = second :=
    Sigma.ext rfl (heq_of_eq ((congrArg (fun arrow => base.map arrow first.2)
      (Category.comp_id step.1)).trans step.2))
  exact (ContextualSmallFamilyUniverse.familyMap_heq target source destination
    ((ContextualSmallFamilyUniverse.futureElement first.1 first.2).map (ContextualSmallFamilyUniverse.rootArrow step.1)) step
    (ContextualSmallFamilyUniverse.elementsArrow_heq source destination _ _ HEq.rfl) right left values.symm).symm

theorem fold_natural {first second : base.Elements} (step : first ⟶ second) (tree : WAt domain body first) :
    target.map step (foldValue domain body algebra first tree) =
      foldValue domain body algebra second (wMap domain body step tree) := by
  apply eq_of_heq
  let restricted := (ContextualWTypes.family (futureDomain domain first) (futureBody domain body first)).map
    (ContextualSmallFamilyUniverse.rootArrow step.1) tree
  let coneChange := ContextualWLocalChange.prefixChange step.1
  let changed := ContextualWLocalChange.naturalEquiv coneChange (futureDomain domain first) (futureBody domain body first)
    (ContextualSmallFamilyUniverse.root second.1) restricted
  have firstMap := target_rootMap_heq (target := target) step (foldValue domain body algebra first tree)
    (ContextualWTypes.fold (futureDomain domain first) (futureBody domain body first)
      (localAlgebra domain body algebra first) tree) (foldValue_heq domain body algebra first tree)
  have oldNatural := ContextualWTypes.fold_natural (futureDomain domain first) (futureBody domain body first)
    (localAlgebra domain body algebra first) (ContextualSmallFamilyUniverse.rootArrow step.1) tree
  have changedFold := ContextualWLocalChange.fold_baseChange coneChange (futureDomain domain first) (futureBody domain body first)
    (futureDomain target first) (localAlgebra domain body algebra first) (ContextualSmallFamilyUniverse.root second.1) restricted
  have comparedFold := ContextualWAlgebraReindexing.fold_heq
    (ContextualSmallFamilyWPolynomial.signature_prefix domain body target step) rfl
    (ContextualWLocalChange.pullAlgebra coneChange (futureDomain domain first) (futureBody domain body first)
      (futureDomain target first) (localAlgebra domain body algebra first))
    (localAlgebra domain body algebra second) (localAlgebra_prefix domain body algebra step)
    changed (wMap domain body step tree) (wMap_raw domain body step tree).symm
  exact firstMap.trans ((heq_of_eq oldNatural).trans
    ((heq_of_eq changedFold).symm.trans (comparedFold.trans
      (foldValue_heq domain body algebra second (wMap domain body step tree)).symm)))

noncomputable def foldMap : NatTrans (w domain body) target where
  app point := TypeCat.ofHom (foldValue domain body algebra point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact (fold_natural domain body algebra step tree).symm

theorem fold_readout (point : base.Elements) (future : Future.Objects point.1)
    (tree : ContextualWReindexing.Tree (signature domain body point) future) :
    HEq (foldValue domain body algebra (ContextualSmallFamilyWCone.futurePoint point future)
      (ContextualSmallFamilyWCone.coneEquiv domain body point future tree))
      (ContextualWTypes.fold (futureDomain domain point) (futureBody domain body point)
        (localAlgebra domain body algebra point) tree) := by
  let step := ContextualSmallFamilyWCone.futureStep point future
  let next := ContextualSmallFamilyWCone.futurePoint point future
  let root := ContextualSmallFamilyUniverse.root future.1
  let raised := ContextualWReindexing.pointEquiv (signature domain body point)
    (ContextualSmallFamilyWCone.nativeRoot_eq point future).symm tree
  let coneChange := ContextualWLocalChange.prefixChange future.2
  let changed := ContextualWLocalChange.naturalEquiv coneChange (futureDomain domain point) (futureBody domain body point) root raised
  have changedCast := ContextualWReindexing.signatureEquiv_raw (signature_prefix domain body step) root changed
  have comparedFold := ContextualWAlgebraReindexing.fold_heq
    (ContextualSmallFamilyWPolynomial.signature_prefix domain body target step) rfl
    (ContextualWLocalChange.pullAlgebra coneChange (futureDomain domain point) (futureBody domain body point)
      (futureDomain target point) (localAlgebra domain body algebra point))
    (localAlgebra domain body algebra next) (localAlgebra_prefix domain body algebra step)
    changed (ContextualSmallFamilyWCone.coneEquiv domain body point future tree) changedCast.symm
  have changedFold := ContextualWLocalChange.fold_baseChange coneChange (futureDomain domain point) (futureBody domain body point)
    (futureDomain target point) (localAlgebra domain body algebra point) root raised
  have pointFold := ContextualWAlgebraReindexing.fold_heq
    (first := ContextualSmallFamilyWPolynomial.signature domain body target point) rfl
    (ContextualSmallFamilyWCone.nativeRoot_eq point future)
    (localAlgebra domain body algebra point) (localAlgebra domain body algebra point) HEq.rfl raised tree
    (ContextualWReindexing.pointEquiv_raw (signature domain body point)
      (ContextualSmallFamilyWCone.nativeRoot_eq point future).symm tree)
  exact (foldValue_heq domain body algebra next _).trans
    (comparedFold.symm.trans ((heq_of_eq changedFold).trans pointFold))

end Mettapedia.TypeTheory.ContextualSmallFamilyWRecursion
