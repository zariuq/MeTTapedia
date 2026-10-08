import Mettapedia.TypeTheory.ContextualSmallFamilyWObservation

/-!
# W destructor observations commute with actual parameter substitution

The root label and evaluated current branch are extracted from the full
future polynomial. Their comparison follows from the existing whole W
constructor substitution and polynomial action, retaining the actual
dependent position transport.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWObservedSubstitution

open CategoryTheory MaterialSets.Hypersets ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyTypeFormers ContextualSmallFamilyTypeFormerCoherence
open ContextualSmallFamilyWTypes ContextualSmallFamilyWAlgebra ContextualSmallFamilyWObservation
open ContextualSmallFamilyWSubstitution ContextualSmallFamilyWSubstitutionCoherence

universe u v w
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v} {other : D ⥤ Type w}
variable (change : NaturalHom other base) (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

section Polynomial
variable (target : base.Elements ⥤ Type u)

theorem label_polynomialComparison (point : other.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body target ((elementMap change).obj point)) :
    rootLabel (domainUnder change domain) (bodyUnder change domain body) (domainUnder change target) point
      (polynomialComparison change domain body target point node) =
        rootLabel domain body target ((elementMap change).obj point) node := by
  have labels := ContextualWPolynomialReindexing.node_label_heq
    (polynomial_signature_change change domain body target point) (root point.1) node
    (polynomialComparison change domain body target point node)
    (polynomialComparison_value change domain body target point node).symm
  exact eq_of_heq ((rootLabel_heq (domainUnder change domain) (bodyUnder change domain body)
    (domainUnder change target) point _).trans
      (labels.symm.trans (rootLabel_heq domain body target ((elementMap change).obj point) node).symm))

theorem evaluate_polynomialComparison (point : other.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body target ((elementMap change).obj point))
    (first : body.obj ⟨(elementMap change).obj point, rootLabel domain body target ((elementMap change).obj point) node⟩)
    (second : (bodyUnder change domain body).obj ⟨point,
      rootLabel (domainUnder change domain) (bodyUnder change domain body) (domainUnder change target) point
        (polynomialComparison change domain body target point node)⟩) (branches : HEq first second) :
    evaluate domain body target ((elementMap change).obj point) node first =
      evaluate (domainUnder change domain) (bodyUnder change domain body) (domainUnder change target) point
        (polynomialComparison change domain body target point node) second := by
  let converted := polynomialComparison change domain body target point node
  have signatures := polynomial_signature_change change domain body target point
  have nodes := (polynomialComparison_value change domain body target point node).symm
  have labels := ContextualWPolynomialReindexing.node_label_heq signatures (root point.1) node converted nodes
  have values := ContextualWPolynomialReindexing.branch_app_heq signatures node.1 converted.1 labels
    node.2 converted.2 (ContextualWPolynomialReindexing.node_branches_heq signatures (root point.1) node converted nodes)
    (root point.1) (𝟙 (root point.1)) (𝟙 (root point.1)) HEq.rfl
    (rootPosition domain body target ((elementMap change).obj point) node first)
    (rootPosition (domainUnder change domain) (bodyUnder change domain body) (domainUnder change target) point converted second)
    ((rootPosition_heq domain body target ((elementMap change).obj point) node first).trans
      (branches.trans (rootPosition_heq (domainUnder change domain) (bodyUnder change domain body)
        (domainUnder change target) point converted second).symm))
  exact eq_of_heq ((evaluate_heq domain body target ((elementMap change).obj point) node first).trans
    (values.trans (evaluate_heq (domainUnder change domain) (bodyUnder change domain body)
      (domainUnder change target) point converted second).symm))

end Polynomial

theorem evaluate_action {firstTarget secondTarget : base.Elements ⥤ Type u}
    (operation : NatTrans firstTarget secondTarget) (point : base.Elements)
    (node : ContextualSmallFamilyWPolynomial.At domain body firstTarget point)
    (branch : body.obj ⟨point, rootLabel domain body firstTarget point node⟩) :
    evaluate domain body secondTarget point (ContextualSmallFamilyWAction.mapValue domain body operation point node) branch =
      operation.app point (evaluate domain body firstTarget point node branch) :=
  evaluationEquiv_natural operation point _

theorem destructor_substitution (point : other.Elements)
    (tree : WAt domain body ((elementMap change).obj point)) :
    destructorValue (domainUnder change domain) (bodyUnder change domain body) point
      (wComparison change domain body point tree) =
    ContextualSmallFamilyWAction.mapValue (domainUnder change domain) (bodyUnder change domain body)
      (wSubstitution change domain body) point
      (polynomialComparison change domain body (w domain body) point
        (destructorValue domain body ((elementMap change).obj point) tree)) := by
  apply (constructorEquiv (domainUnder change domain) (bodyUnder change domain body) point).injective
  exact (constructor_destructor (domainUnder change domain) (bodyUnder change domain body) point _).trans
    ((congrArg (wComparison change domain body point)
      (constructor_destructor domain body ((elementMap change).obj point) tree)).symm.trans
        (constructor_substitution change domain body point _))

theorem label_wComparison (point : other.Elements)
    (tree : WAt domain body ((elementMap change).obj point)) :
    rootLabel (domainUnder change domain) (bodyUnder change domain body)
      (w (domainUnder change domain) (bodyUnder change domain body)) point
      (destructorValue (domainUnder change domain) (bodyUnder change domain body) point
        (wComparison change domain body point tree)) =
    rootLabel domain body (w domain body) ((elementMap change).obj point)
      (destructorValue domain body ((elementMap change).obj point) tree) := by
  rw [destructor_substitution]
  exact label_polynomialComparison change domain body (w domain body) point _

theorem child_wComparison (point : other.Elements)
    (tree : WAt domain body ((elementMap change).obj point))
    (first : body.obj ⟨(elementMap change).obj point, rootLabel domain body (w domain body)
      ((elementMap change).obj point) (destructorValue domain body ((elementMap change).obj point) tree)⟩)
    (second : (bodyUnder change domain body).obj ⟨point,
      rootLabel (domainUnder change domain) (bodyUnder change domain body)
        (w (domainUnder change domain) (bodyUnder change domain body)) point
        (destructorValue (domainUnder change domain) (bodyUnder change domain body) point
          (wComparison change domain body point tree))⟩) (branches : HEq first second) :
    wComparison change domain body point
      (evaluate domain body (w domain body) ((elementMap change).obj point)
        (destructorValue domain body ((elementMap change).obj point) tree) first) =
    evaluate (domainUnder change domain) (bodyUnder change domain body)
      (w (domainUnder change domain) (bodyUnder change domain body)) point
      (destructorValue (domainUnder change domain) (bodyUnder change domain body) point
        (wComparison change domain body point tree)) second := by
  let original := destructorValue domain body ((elementMap change).obj point) tree
  let converted := polynomialComparison change domain body (w domain body) point original
  let branch := cast (congrArg (fun label => (bodyUnder change domain body).obj ⟨point, label⟩)
    (label_polynomialComparison change domain body (w domain body) point original).symm) first
  have branchSame : HEq branch first := ContextualSmallFamilyUniverse.cast_heq _ _
  have evaluated := evaluate_polynomialComparison change domain body (w domain body) point original first branch branchSame.symm
  have mapped := evaluate_action (domainUnder change domain) (bodyUnder change domain body)
    (wSubstitution change domain body) point converted branch
  exact (congrArg (wComparison change domain body point) evaluated).trans
    (mapped.symm.trans (evaluate_node_congr (domainUnder change domain) (bodyUnder change domain body)
      (w (domainUnder change domain) (bodyUnder change domain body)) point _ _
      (destructor_substitution change domain body point tree).symm branch second (branchSame.trans branches)))

end Mettapedia.TypeTheory.ContextualSmallFamilyWObservedSubstitution
