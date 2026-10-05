import Mettapedia.TypeTheory.ContextualSmallFamilyWInitiality

/-!
# Full W algebra substitution over arbitrary wider parameters

The independently formed polynomial and W fibres are compared through
whole future signatures. Transported algebras and their folds retain
original target values, including under noninjective parameter maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitutionCoherence

open CategoryTheory MaterialSets.Hypersets ContextualWitnessCover
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyTypeFormerCoherence
open ContextualSmallFamilyWTypes ContextualSmallFamilyWSubstitution ContextualSmallFamilyWAlgebra
open PowerClassPresheafBaseChange

universe u v w z
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v} {other : D ⥤ Type w}
variable (change : NaturalHom other base) (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (target : base.Elements ⥤ Type u)

theorem polynomial_signature_change (point : other.Elements) :
    ContextualSmallFamilyWPolynomial.signature domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj point) =
      ContextualSmallFamilyWPolynomial.signature (domainUnder change domain) (bodyUnder change domain body)
        (domainUnder change target) point :=
  Prod.ext (signature_change change domain body point) (futureDomain_change change target point).symm

def polynomialComparison (point : other.Elements) :
    ContextualSmallFamilyWPolynomial.At domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj point) ≃
      ContextualSmallFamilyWPolynomial.At (domainUnder change domain) (bodyUnder change domain body)
        (domainUnder change target) point :=
  ContextualWPolynomialReindexing.signatureEquiv (polynomial_signature_change change domain body target point)
    (ContextualSmallFamilyUniverse.root point.1)

theorem polynomialComparison_value (point : other.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    HEq (polynomialComparison change domain body target point node) node :=
  ContextualWPolynomialReindexing.signatureEquiv_heq _ _ _

theorem polynomialComparison_inverse_value (point : other.Elements)
    (node : ContextualSmallFamilyWPolynomial.At (domainUnder change domain) (bodyUnder change domain body)
      (domainUnder change target) point) :
    HEq ((polynomialComparison change domain body target point).symm node) node := by
  have compared := polynomialComparison_value change domain body target point
    ((polynomialComparison change domain body target point).symm node)
  exact compared.symm.trans
    (heq_of_eq ((polynomialComparison change domain body target point).apply_symm_apply node))

theorem polynomialComparison_natural {first second : other.Elements} (step : first ⟶ second)
    (node : ContextualSmallFamilyWPolynomial.At domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj first)) :
    polynomialComparison change domain body target second
      (ContextualSmallFamilyWPolynomial.pMap domain body target
        ((ContextualSmallFamilyUniverse.elementMap change).map step) node) =
      ContextualSmallFamilyWPolynomial.pMap (domainUnder change domain) (bodyUnder change domain body)
        (domainUnder change target) step (polynomialComparison change domain body target first node) := by
  apply eq_of_heq
  have restricted := ContextualWPolynomialReindexing.restrict_signature_heq
    (polynomial_signature_change change domain body target first)
    (ContextualSmallFamilyUniverse.rootArrow step.1) node
    (polynomialComparison change domain body target first node)
    (polynomialComparison_value change domain body target first node).symm
  have pulled := ContextualWPolynomialReindexing.pull_congr
    (first := ContextualSmallFamilyUniverse.futurePrefix step.1) rfl
    (polynomial_signature_change change domain body target first) rfl _ _ restricted
  exact (polynomialComparison_value change domain body target second _).trans
    ((ContextualSmallFamilyWPolynomial.pMap_value domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).map step) node).trans
        (pulled.trans (ContextualSmallFamilyWPolynomial.pMap_value (domainUnder change domain)
          (bodyUnder change domain body) (domainUnder change target) step _).symm))

def polynomialSubstitution :
    NatTrans (domainUnder change (ContextualSmallFamilyWPolynomial.polynomial domain body target))
      (ContextualSmallFamilyWPolynomial.polynomial (domainUnder change domain) (bodyUnder change domain body)
        (domainUnder change target)) where
  app point := TypeCat.ofHom (polynomialComparison change domain body target point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    exact polynomialComparison_natural change domain body target step

def polynomialSubstitutionInverse :
    NatTrans (ContextualSmallFamilyWPolynomial.polynomial (domainUnder change domain) (bodyUnder change domain body)
      (domainUnder change target))
      (domainUnder change (ContextualSmallFamilyWPolynomial.polynomial domain body target)) where
  app point := TypeCat.ofHom (polynomialComparison change domain body target point).symm
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro node
    apply (polynomialComparison change domain body target second).injective
    change polynomialComparison change domain body target second
      ((polynomialComparison change domain body target second).symm
        (ContextualSmallFamilyWPolynomial.pMap _ _ _ step node)) =
      polynomialComparison change domain body target second
        (ContextualSmallFamilyWPolynomial.pMap domain body target
          ((ContextualSmallFamilyUniverse.elementMap change).map step)
          ((polynomialComparison change domain body target first).symm node))
    exact ((polynomialComparison change domain body target second).apply_symm_apply _).trans
      ((congrArg (ContextualSmallFamilyWPolynomial.pMap _ _ _ step)
        ((polynomialComparison change domain body target first).apply_symm_apply node)).symm.trans
          (polynomialComparison_natural change domain body target step _).symm)

theorem polynomialSubstitution_left :
    composeNat (polynomialSubstitution change domain body target) (polynomialSubstitutionInverse change domain body target) =
      identityNat (domainUnder change (ContextualSmallFamilyWPolynomial.polynomial domain body target)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (polynomialComparison change domain body target point).symm_apply_apply

theorem polynomialSubstitution_right :
    composeNat (polynomialSubstitutionInverse change domain body target) (polynomialSubstitution change domain body target) =
      identityNat (ContextualSmallFamilyWPolynomial.polynomial (domainUnder change domain) (bodyUnder change domain body)
        (domainUnder change target)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (polynomialComparison change domain body target point).apply_symm_apply

theorem polynomial_cone_readout (point : other.Elements) (future : Future.Objects point.1)
    (firstNode : ContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWPolynomial.signature domain body target
        ((ContextualSmallFamilyUniverse.elementMap change).obj point)) future)
    (secondNode : ContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWPolynomial.signature (domainUnder change domain) (bodyUnder change domain body)
        (domainUnder change target) point) future) (nodes : HEq firstNode secondNode) :
    HEq (ContextualSmallFamilyWPolynomialCone.coneEquiv domain body target
      ((ContextualSmallFamilyUniverse.elementMap change).obj point) future firstNode)
      (ContextualSmallFamilyWPolynomialCone.coneEquiv (domainUnder change domain) (bodyUnder change domain body)
        (domainUnder change target) point future secondNode) := by
  have pulled := ContextualWPolynomialReindexing.pullData_congr
    (first := ContextualSmallFamilyUniverse.futurePrefix future.2) rfl
    (polynomial_signature_change change domain body target point) rfl firstNode secondNode nodes
    (ContextualSmallFamilyWCone.nativeRoot_eq ((ContextualSmallFamilyUniverse.elementMap change).obj point) future)
    (ContextualSmallFamilyWCone.nativeRoot_eq point future)
  exact (ContextualSmallFamilyWPolynomialCone.coneEquiv_value domain body target
    ((ContextualSmallFamilyUniverse.elementMap change).obj point) future firstNode).trans
      (pulled.trans (ContextualSmallFamilyWPolynomialCone.coneEquiv_value (domainUnder change domain)
        (bodyUnder change domain body) (domainUnder change target) point future secondNode).symm)

theorem cone_tree_readout_raw (point : other.Elements) (future : Future.Objects point.1)
    (firstTree : ContextualWReindexing.Tree
      (signature domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)) future)
    (secondTree : ContextualWReindexing.Tree
      (signature (domainUnder change domain) (bodyUnder change domain body) point) future)
    (trees : HEq firstTree.val secondTree.val) :
    HEq (ContextualSmallFamilyWCone.coneEquiv domain body
      ((ContextualSmallFamilyUniverse.elementMap change).obj point) future firstTree).val
      (ContextualSmallFamilyWCone.coneEquiv (domainUnder change domain) (bodyUnder change domain body) point future secondTree).val := by
  have pulled := ContextualWReindexing.pullData_congr
    (first := ContextualSmallFamilyUniverse.futurePrefix future.2) rfl
    (signature_change change domain body point) rfl firstTree.val secondTree.val trees
    (ContextualSmallFamilyWCone.nativeRoot_eq ((ContextualSmallFamilyUniverse.elementMap change).obj point) future)
    (ContextualSmallFamilyWCone.nativeRoot_eq point future)
  exact (ContextualSmallFamilyWCone.coneEquiv_raw domain body
    ((ContextualSmallFamilyUniverse.elementMap change).obj point) future firstTree).trans
      (pulled.trans (ContextualSmallFamilyWCone.coneEquiv_raw (domainUnder change domain)
        (bodyUnder change domain body) point future secondTree).symm)

theorem tree_raw_of_heq {first second : base.Elements} (points : first = second)
    (left : WAt domain body first) (right : WAt domain body second) (values : HEq left right) : HEq left.val right.val := by
  cases points
  exact heq_of_eq (congrArg Subtype.val (eq_of_heq values))

theorem constructor_substitution (point : other.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body (w domain body)
      ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    wComparison change domain body point
      (constructorValue domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point) node) =
      constructorValue (domainUnder change domain) (bodyUnder change domain body) point
        (ContextualSmallFamilyWAction.mapValue (domainUnder change domain) (bodyUnder change domain body)
          (wSubstitution change domain body) point
          (polynomialComparison change domain body (w domain body) point node)) := by
  apply Subtype.ext
  apply eq_of_heq
  refine (wComparison_raw change domain body point
    (constructorValue domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point) node)).trans ?_
  let oldPoint := (ContextualSmallFamilyUniverse.elementMap change).obj point
  let newDomain := domainUnder change domain
  let newBody := bodyUnder change domain body
  let converted := polynomialComparison change domain body (w domain body) point node
  let formed := ContextualSmallFamilyWAction.mapValue newDomain newBody (wSubstitution change domain body) point converted
  have nodeEq := (polynomialComparison_value change domain body (w domain body) point node).symm
  have labels := ContextualWPolynomialReindexing.node_label_heq
    (polynomial_signature_change change domain body (w domain body) point)
    (ContextualSmallFamilyUniverse.root point.1) node converted nodeEq
  have branches := ContextualWPolynomialReindexing.node_branches_heq
    (polynomial_signature_change change domain body (w domain body) point)
    (ContextualSmallFamilyUniverse.root point.1) node converted nodeEq
  apply ContextualWReindexing.sup_heq (signature_change change domain body point) rfl node.1 formed.1 labels
  intro future firstArrow secondArrow arrows firstPosition secondPosition positions
  let oldValue := node.2.app future firstArrow firstPosition
  let convertedValue := converted.2.app future secondArrow secondPosition
  let oldChild := (ContextualSmallFamilyWCone.coneEquiv domain body oldPoint future).symm oldValue
  let transported := ContextualWReindexing.signatureEquiv (signature_change change domain body point) future oldChild
  let newChild := (ContextualSmallFamilyWCone.coneEquiv newDomain newBody point future).symm
    (formed.2.app future secondArrow secondPosition)
  have values := ContextualWPolynomialReindexing.branch_app_heq
    (polynomial_signature_change change domain body (w domain body) point) node.1 converted.1 labels
    node.2 converted.2 branches future firstArrow secondArrow arrows firstPosition secondPosition positions
  have valueRaw := tree_raw_of_heq domain body (changeFuturePoint_eq change point future) oldValue convertedValue values
  have readout := cone_tree_readout_raw change domain body point future oldChild transported
    (ContextualWReindexing.signatureEquiv_raw (signature_change change domain body point) future oldChild).symm
  have oldRecovered := congrArg Subtype.val
    ((ContextualSmallFamilyWCone.coneEquiv domain body oldPoint future).apply_symm_apply oldValue)
  have newValue := wComparison_raw change domain body (ContextualSmallFamilyWCone.futurePoint point future) convertedValue
  have row : ContextualSmallFamilyWCone.coneEquiv newDomain newBody point future transported =
      formed.2.app future secondArrow secondPosition := by
    apply Subtype.ext
    exact eq_of_heq (readout.symm.trans ((heq_of_eq oldRecovered).trans (valueRaw.trans newValue.symm)))
  have childEq : transported = newChild :=
    (ContextualSmallFamilyWCone.coneEquiv newDomain newBody point future).injective
      (row.trans ((ContextualSmallFamilyWCone.coneEquiv newDomain newBody point future).apply_symm_apply
        (formed.2.app future secondArrow secondPosition)).symm)
  exact (ContextualWReindexing.signatureEquiv_raw (signature_change change domain body point) future oldChild).symm.trans
    (heq_of_eq (congrArg Subtype.val childEq))

theorem constructor_substitution_whole :
    composeNat (ContextualSmallFamilyTypeFormerCoherence.restrictNat (ContextualSmallFamilyUniverse.elementMap change)
      (ContextualSmallFamilyWConstructor.constructor domain body)) (wSubstitution change domain body) =
      composeNat (composeNat (polynomialSubstitution change domain body (w domain body))
        (ContextualSmallFamilyWAction.map (domainUnder change domain) (bodyUnder change domain body)
          (wSubstitution change domain body)))
        (ContextualSmallFamilyWConstructor.constructor (domainUnder change domain) (bodyUnder change domain body)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact constructor_substitution change domain body point

variable {target}
def substitutedAlgebra (algebra : Algebra domain body (target := target)) :
    Algebra (domainUnder change domain) (bodyUnder change domain body) (target := domainUnder change target) :=
  composeNat (polynomialSubstitutionInverse change domain body target)
    (ContextualSmallFamilyTypeFormerCoherence.restrictNat (ContextualSmallFamilyUniverse.elementMap change) algebra)

theorem localAlgebra_substitution (algebra : Algebra domain body (target := target)) (point : other.Elements) :
    HEq (localAlgebra domain body algebra ((ContextualSmallFamilyUniverse.elementMap change).obj point))
      (localAlgebra (domainUnder change domain) (bodyUnder change domain body)
        (substitutedAlgebra change domain body algebra) point) := by
  apply ContextualWAlgebraReindexing.algebra_ext_heq
    (polynomial_signature_change change domain body target point)
  intro future firstLabel secondLabel labels firstBranches secondBranches branches
  let firstNode : ContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWPolynomial.signature domain body target
        ((ContextualSmallFamilyUniverse.elementMap change).obj point)) future := ⟨firstLabel, firstBranches⟩
  let secondNode : ContextualWPolynomialReindexing.At
      (ContextualSmallFamilyWPolynomial.signature (domainUnder change domain) (bodyUnder change domain body)
        (domainUnder change target) point) future := ⟨secondLabel, secondBranches⟩
  have nodeEq := ContextualWAlgebraReindexing.node_heq
    (polynomial_signature_change change domain body target point) future firstLabel secondLabel labels firstBranches secondBranches branches
  have readout := polynomial_cone_readout change domain body target point future firstNode secondNode nodeEq
  have recovered := polynomialComparison_inverse_value change domain body target
    (ContextualSmallFamilyWCone.futurePoint point future)
    (ContextualSmallFamilyWPolynomialCone.coneEquiv (domainUnder change domain) (bodyUnder change domain body)
      (domainUnder change target) point future secondNode)
  exact naturalApplication_heq algebra (changeFuturePoint_eq change point future) _ _ (readout.trans recovered.symm)

theorem fold_substitution (algebra : Algebra domain body (target := target)) (point : other.Elements)
    (tree : WAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    foldValue domain body algebra ((ContextualSmallFamilyUniverse.elementMap change).obj point) tree =
      foldValue (domainUnder change domain) (bodyUnder change domain body)
        (substitutedAlgebra change domain body algebra) point (wComparison change domain body point tree) := by
  apply eq_of_heq
  have nativeFold := ContextualWAlgebraReindexing.fold_heq
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
    ContextualSmallFamilyTypeFormerCoherence.restrictNat (ContextualSmallFamilyUniverse.elementMap change)
      (ContextualSmallFamilyWRecursion.foldMap domain body algebra) =
      composeNat (wSubstitution change domain body)
        (ContextualSmallFamilyWRecursion.foldMap (domainUnder change domain) (bodyUnder change domain body)
          (substitutedAlgebra change domain body algebra)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact fold_substitution change domain body algebra point

theorem tree_heq {E : Type u} [Category.{u} E]
    {firstSignature secondSignature : ContextualWReindexing.Signature E} (signatures : firstSignature = secondSignature)
    (point : E) (left : ContextualWReindexing.Tree firstSignature point)
    (right : ContextualWReindexing.Tree secondSignature point) (values : HEq left.val right.val) : HEq left right := by
  cases signatures
  exact heq_of_eq (Subtype.ext (eq_of_heq values))

theorem wComparison_heq (point : other.Elements)
    (tree : WAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    HEq (wComparison change domain body point tree) tree :=
  tree_heq (signature_change change domain body point).symm (ContextualSmallFamilyUniverse.root point.1)
    _ _ (wComparison_raw change domain body point tree)

theorem hom_heq {firstSource secondSource firstTarget secondTarget : Type u}
    (sources : firstSource = secondSource) (targets : firstTarget = secondTarget)
    (left : firstSource → firstTarget) (right : secondSource → secondTarget)
    (values : ∀ first second, HEq first second → HEq (left first) (right second)) :
    HEq (TypeCat.ofHom left) (TypeCat.ofHom right) := by
  cases sources
  cases targets
  apply heq_of_eq
  apply ConcreteCategory.hom_ext
  intro value
  exact eq_of_heq (values value value HEq.rfl)

theorem w_substitution_eq :
    domainUnder change (w domain body) = w (domainUnder change domain) (bodyUnder change domain body) := by
  refine Functor.hext (fun point => congrArg
    (fun data => ContextualWReindexing.Tree data (ContextualSmallFamilyUniverse.root point.1))
    (signature_change change domain body point)) ?_
  intro first second step
  apply hom_heq
    (congrArg (fun data => ContextualWReindexing.Tree data (ContextualSmallFamilyUniverse.root first.1))
      (signature_change change domain body first))
    (congrArg (fun data => ContextualWReindexing.Tree data (ContextualSmallFamilyUniverse.root second.1))
      (signature_change change domain body second))
  intro left right values
  have same : wComparison change domain body first left = right :=
    eq_of_heq ((wComparison_heq change domain body first left).trans values)
  have natural := wComparison_natural change domain body step left
  have afterInput := congrArg (wMap (domainUnder change domain) (bodyUnder change domain body) step) same
  exact (wComparison_heq change domain body second
    (wMap domain body ((ContextualSmallFamilyUniverse.elementMap change).map step) left)).symm.trans
      (heq_of_eq (natural.trans afterInput))

theorem wComparison_identity (point : base.Elements) (tree : WAt domain body point) :
    HEq (wComparison (ContextualSmallMapConstructions.identity base) domain body point tree) tree :=
  wComparison_heq (ContextualSmallMapConstructions.identity base) domain body point tree

theorem wComparison_composition {third : D ⥤ Type z}
    (first : NaturalHom other base) (later : NaturalHom third other) (point : third.Elements)
    (tree : WAt domain body ((ContextualSmallFamilyUniverse.elementMap (later.comp first)).obj point)) :
    HEq (wComparison later (domainUnder first domain) (bodyUnder first domain body) point
      (wComparison first domain body ((ContextualSmallFamilyUniverse.elementMap later).obj point) tree))
      (wComparison (later.comp first) domain body point tree) :=
  (wComparison_heq later (domainUnder first domain) (bodyUnder first domain body) point _).trans
    ((wComparison_heq first domain body ((ContextualSmallFamilyUniverse.elementMap later).obj point) tree).trans
      (wComparison_heq (later.comp first) domain body point tree).symm)

theorem polynomialComparison_identity (point : base.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body target point) :
    HEq (polynomialComparison (ContextualSmallMapConstructions.identity base) domain body target point node) node :=
  polynomialComparison_value (ContextualSmallMapConstructions.identity base) domain body target point node

theorem polynomialComparison_composition {third : D ⥤ Type z}
    (first : NaturalHom other base) (later : NaturalHom third other) (point : third.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body target
      ((ContextualSmallFamilyUniverse.elementMap (later.comp first)).obj point)) :
    HEq (polynomialComparison later (domainUnder first domain) (bodyUnder first domain body)
      (domainUnder first target) point
      (polynomialComparison first domain body target ((ContextualSmallFamilyUniverse.elementMap later).obj point) node))
      (polynomialComparison (later.comp first) domain body target point node) :=
  (polynomialComparison_value later (domainUnder first domain) (bodyUnder first domain body)
    (domainUnder first target) point _).trans
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

theorem w_decoder : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier (w domain body)) = w domain body :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq (w domain body)

theorem w_classifier_substitution (point : other.Elements) :
    ContextualSmallFamilyUniverse.familyCode (w (domainUnder change domain) (bodyUnder change domain body)) point.1 point.2 =
      ContextualSmallFamilyUniverse.familyCode (w domain body) point.1 (change.app point.1 point.2) :=
  (congrArg (fun family => ContextualSmallFamilyUniverse.familyCode family point.1 point.2)
    (w_substitution_eq change domain body).symm).trans
      (ContextualSmallFamilyUniverse.familyCode_substitution (w domain body) change point.1 point.2)

theorem classified_w_value (point : other.Elements)
    (tree : WAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    HEq ((ContextualSmallFamilyUniverse.classified (w (domainUnder change domain) (bodyUnder change domain body))).app
      point.1 ⟨point.2, wComparison change domain body point tree⟩).2 tree :=
  (ContextualSmallFamilyUniverse.classified_value_heq (w (domainUnder change domain) (bodyUnder change domain body))
    point.1 ⟨point.2, wComparison change domain body point tree⟩).trans (wComparison_heq change domain body point tree)

end Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitutionCoherence
