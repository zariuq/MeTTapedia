import Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitutionCoherence

/-!
# Current observations of complete future W polynomials

The independently formed polynomial retains the full future branch table.
Its root label and current branch evaluation commute with the native
parameter action. These maps expose an actual reduction span for material
readings without treating recentered cone diagrams as literal equals.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWObservation

open CategoryTheory ContextualWitnessCover ContextualSmallFamilyUniverse
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyWPolynomial
open MaterialSets.Hypersets PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (target : base.Elements ⥤ Type u)

def rootLabel (point : base.Elements) (node : At domain body target point) : domain.obj point :=
  evaluationEquiv domain point.1 point.2 node.1

theorem rootLabel_heq (point : base.Elements) (node : At domain body target point) :
    HEq (rootLabel domain body target point node) node.1 := ContextualSmallFamilyUniverse.cast_heq _ _

theorem rootLabel_natural {first second : base.Elements} (step : first ⟶ second)
    (node : At domain body target first) :
    domain.map step (rootLabel domain body target first node) =
      rootLabel domain body target second (pMap domain body target step node) := by
  let pulled := ContextualWPolynomialReindexing.pull (futurePrefix step.1)
    (signature domain body target first) (root second.1)
    ((ContextualWPolynomialReindexing.family (signature domain body target first)).map
      (rootArrow step.1) node)
  have labels := ContextualWPolynomialReindexing.node_label_heq
    (signature_prefix domain body target step) (root second.1) pulled
    (pMap domain body target step node) (pMap_value domain body target step node).symm
  exact eq_of_heq ((ContextualSmallFamilyWRecursion.target_rootMap_heq (target := domain) step
    (rootLabel domain body target first node) node.1 (rootLabel_heq domain body target first node)).trans
      (labels.trans (rootLabel_heq domain body target second (pMap domain body target step node)).symm))

def rootLabelMap : NatTrans (polynomial domain body target) domain where
  app point := TypeCat.ofHom (rootLabel domain body target point)
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro node
    exact (rootLabel_natural domain body target step node).symm


def rootArgument (point : base.Elements) (node : At domain body target point) : domain.Elements :=
  (futureArguments domain point).obj
    ⟨root point.1, (futureDomain domain point).map (𝟙 (root point.1)) node.1⟩

theorem rootArgument_eq (point : base.Elements) (node : At domain body target point) :
    rootArgument domain body target point node = ⟨point, rootLabel domain body target point node⟩ := by
  apply Sigma.ext (evaluationPoint_eq point.1 point.2)
  change HEq ((futureDomain domain point).map (𝟙 (root point.1)) node.1)
    (rootLabel domain body target point node)
  exact (heq_of_eq ((futureDomain domain point).map_id_apply (root point.1) node.1)).trans
    (rootLabel_heq domain body target point node).symm

def rootPosition (point : base.Elements) (node : At domain body target point)
    (branch : body.obj ⟨point, rootLabel domain body target point node⟩) :
    ContextualWTypes.Position (futureDomain domain point) (futureBody domain body point)
      node.1 (𝟙 (root point.1)) :=
  cast (congrArg body.obj (rootArgument_eq domain body target point node).symm) branch

theorem rootPosition_heq (point : base.Elements) (node : At domain body target point)
    (branch : body.obj ⟨point, rootLabel domain body target point node⟩) :
    HEq (rootPosition domain body target point node branch) branch :=
  ContextualSmallFamilyUniverse.cast_heq _ _

def evaluate (point : base.Elements) (node : At domain body target point)
    (branch : body.obj ⟨point, rootLabel domain body target point node⟩) : target.obj point :=
  evaluationEquiv target point.1 point.2
    (node.2.app (root point.1) (𝟙 (root point.1)) (rootPosition domain body target point node branch))

theorem evaluate_heq (point : base.Elements) (node : At domain body target point)
    (branch : body.obj ⟨point, rootLabel domain body target point node⟩) :
    HEq (evaluate domain body target point node branch)
      (node.2.app (root point.1) (𝟙 (root point.1)) (rootPosition domain body target point node branch)) :=
  ContextualSmallFamilyUniverse.cast_heq _ _

/-- Transfer only the actual dependent position through an equality of
polynomial signatures and its already proved node comparison. -/
def castPosition {E : Type u} [Category.{u} E]
    {first second : ContextualWPolynomialReindexing.Signature E}
    (signatures : first = second) {point : E}
    (left : ContextualWPolynomialReindexing.At first point)
    (right : ContextualWPolynomialReindexing.At second point) (nodes : HEq left right)
    {future : E} (arrow : point ⟶ future)
    (branch : ContextualWTypes.Position second.1.1 second.1.2 right.1 arrow) :
    ContextualWTypes.Position first.1.1 first.1.2 left.1 arrow := by
  cases signatures
  cases eq_of_heq nodes
  exact branch

theorem castPosition_heq {E : Type u} [Category.{u} E]
    {first second : ContextualWPolynomialReindexing.Signature E}
    (signatures : first = second) {point : E}
    (left : ContextualWPolynomialReindexing.At first point)
    (right : ContextualWPolynomialReindexing.At second point) (nodes : HEq left right)
    {future : E} (arrow : point ⟶ future)
    (branch : ContextualWTypes.Position second.1.1 second.1.2 right.1 arrow) :
    HEq (castPosition signatures left right nodes arrow branch) branch := by
  cases signatures
  cases eq_of_heq nodes
  rfl

theorem positionAlong_root_heq {first second : base.Elements} (step : first ⟶ second)
    (node : At domain body target first)
    (branch : body.obj ⟨first, rootLabel domain body target first node⟩) :
    HEq (ContextualWTypes.positionAlong (futureDomain domain first) (futureBody domain body first)
      node.1 (𝟙 (root first.1)) (rootArrow step.1) (rootPosition domain body target first node branch))
      (body.map (argumentStep domain step (rootLabel domain body target first node)) branch) := by
  let label := (futureDomain domain first).map (𝟙 (root first.1)) node.1
  let oldStep := (futureArguments domain first).map
    (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.argumentMap
      (futureDomain domain first) (rootArrow step.1) label)
  have source := rootArgument_eq domain body target first node
  have destinationBase : (futureElement first.1 first.2).obj
      ((futurePrefix step.1).obj (root second.1)) = second :=
    Sigma.ext rfl (heq_of_eq ((congrArg (fun arrow => base.map arrow first.2)
      (Category.comp_id step.1)).trans step.2))
  have destination : (futureArguments domain first).obj
      ⟨(futurePrefix step.1).obj (root second.1), (futureDomain domain first).map (rootArrow step.1) label⟩ =
        ⟨second, domain.map step (rootLabel domain body target first node)⟩ := by
    apply Sigma.ext destinationBase
    have labelSame : label = node.1 := (futureDomain domain first).map_id_apply _ _
    rw [labelSame]
    exact (ContextualSmallFamilyWRecursion.target_rootMap_heq (target := domain) step
      (rootLabel domain body target first node) node.1 (rootLabel_heq domain body target first node)).symm
  have arrows : HEq oldStep (argumentStep domain step (rootLabel domain body target first node)) :=
    elementArrow_heq source destination _ _
      (elementsArrow_heq (congrArg Sigma.fst source) destinationBase _ _ HEq.rfl)
  exact (ContextualSmallFamilyUniverse.cast_heq _ _).trans
    (familyMap_heq body source destination oldStep _ arrows
      (rootPosition domain body target first node branch) branch (rootPosition_heq domain body target first node branch))

theorem evaluate_natural {first second : base.Elements} (step : first ⟶ second)
    (node : At domain body target first)
    (branch : body.obj ⟨first, rootLabel domain body target first node⟩) :
    target.map step (evaluate domain body target first node branch) =
      evaluate domain body target second (pMap domain body target step node)
        (cast (congrArg (fun label => body.obj ⟨second, label⟩)
          (rootLabel_natural domain body target step node))
          (body.map (argumentStep domain step (rootLabel domain body target first node)) branch)) := by
  let newNode := pMap domain body target step node
  let newBranch := cast (congrArg (fun label => body.obj ⟨second, label⟩)
    (rootLabel_natural domain body target step node))
    (body.map (argumentStep domain step (rootLabel domain body target first node)) branch)
  let newPosition := rootPosition domain body target second newNode newBranch
  let pulled := ContextualWPolynomialReindexing.pull (futurePrefix step.1)
    (signature domain body target first) (root second.1)
    ((ContextualWPolynomialReindexing.family (signature domain body target first)).map
      (rootArrow step.1) node)
  have signatures := signature_prefix domain body target step
  have nodeEq : HEq pulled newNode := (pMap_value domain body target step node).symm
  let oldPosition := castPosition signatures pulled newNode nodeEq (𝟙 (root second.1)) newPosition
  have positionEq := castPosition_heq signatures pulled newNode nodeEq (𝟙 (root second.1)) newPosition
  have appEq := ContextualWPolynomialReindexing.branch_app_heq signatures
    pulled.1 newNode.1 (ContextualWPolynomialReindexing.node_label_heq signatures _ _ _ nodeEq)
    pulled.2 newNode.2 (ContextualWPolynomialReindexing.node_branches_heq signatures _ _ _ nodeEq)
    (root second.1) (𝟙 _) (𝟙 _) HEq.rfl oldPosition newPosition positionEq
  have nativeMap := ContextualSmallFamilyWRecursion.target_rootMap_heq (target := target) step
    (evaluate domain body target first node branch) _ (evaluate_heq domain body target first node branch)
  have natural := node.2.naturality (root first.1) ((futurePrefix step.1).obj (root second.1))
    (𝟙 _) (rootArrow step.1) (rootPosition domain body target first node branch)
  have arguments : HEq
      (ContextualWTypes.positionAlong (futureDomain domain first) (futureBody domain body first)
        node.1 (𝟙 _) (rootArrow step.1) (rootPosition domain body target first node branch))
      (ContextualWTypes.compositePosition (futureDomain domain first) (futureBody domain body first)
        node.1 (rootArrow step.1) ((futurePrefix step.1).map (𝟙 (root second.1))) oldPosition) :=
    (positionAlong_root_heq domain body target step node branch).trans
      (((ContextualSmallFamilyUniverse.cast_heq _ _).trans
        (positionEq.trans ((rootPosition_heq domain body target second newNode newBranch).trans
          (ContextualSmallFamilyUniverse.cast_heq _ _)))).symm)
  have nextSame := node.2.app_eq (by simp) _ _ arguments
  exact eq_of_heq (nativeMap.trans ((heq_of_eq natural).trans
    ((heq_of_eq nextSame).trans (appEq.trans (evaluate_heq domain body target second newNode newBranch).symm))))


theorem evaluate_node_congr (point : base.Elements) (first second : At domain body target point)
    (same : first = second)
    (left : body.obj ⟨point, rootLabel domain body target point first⟩)
    (right : body.obj ⟨point, rootLabel domain body target point second⟩)
    (branches : HEq left right) :
    evaluate domain body target point first left = evaluate domain body target point second right := by
  cases same
  cases eq_of_heq branches
  rfl

end Mettapedia.TypeTheory.ContextualSmallFamilyWObservation
