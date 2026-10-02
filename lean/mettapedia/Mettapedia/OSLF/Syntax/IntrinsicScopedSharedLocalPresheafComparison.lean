import Mettapedia.OSLF.Syntax.IntrinsicScopedSharedLocalTreeComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalModelPresheaf

/-!
# Retained-event comparison for the unpruned shared-to-local presentation

The shared free firing model and the actual local firing trees are compared
through their whole-history equivalence and genuine substitution actions.
The common action-presheaf construction then supplies the event and endpoint
comparison. No unused assignment is forgotten.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedSharedLocalPresheafComparison

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open AuthoredPositionedRulePolynomial (Judgment)
open IntrinsicScopedSharedLocalPolynomialComparison
open IntrinsicScopedSharedLocalTreeComparison
open IntrinsicScopedJudgmentActionPresheaf
open IntrinsicScopedConditionalPresheaf (Base)

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))

/-- The existing complete shared firing model, with its actual substitution action. -/
noncomputable abbrev sharedTreeModel (A : BindingCloneAlgebra.Algebra.{u} S) :=
  IntrinsicScopedConditionalSubstitution.SubstitutionModel.free R A

/-- The existing local indexed W-type with constructor and contextual actions. -/
noncomputable def localTreeModel (A : BindingCloneAlgebra.Algebra.{u} S) :
    IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.{u, u} (localRules R) A where
  carrier := IntrinsicScopedLocalPolynomial.Tree (localRules R) A
  act := IntrinsicScopedLocalPolynomial.substTree (localRules R) A
  act_identity := IntrinsicScopedLocalPolynomial.substTree_identity (localRules R) A
  act_comp := IntrinsicScopedLocalPolynomial.substTree_comp (localRules R) A
  rules := { act := fun _ _ layer => .roll layer.1 layer.2 }
  act_rules := by
    dsimp only [IntrinsicScopedLocalSubstitutionModel.RulesLaw]
    intros
    rfl

/-- The complete-history equivalence induces a natural map of retained events. -/
noncomputable def eventMap (A : BindingCloneAlgebra.Algebra.{u} S) :
    events (sharedTreeModel R A).toAction ⟶ events (localTreeModel R A).toAction :=
  mapEvents (toLocalTree R A) (toLocalTree_substTree R A)

noncomputable def inverseEventMap (A : BindingCloneAlgebra.Algebra.{u} S) :
    events (localTreeModel R A).toAction ⟶ events (sharedTreeModel R A).toAction :=
  mapEvents (toSharedTree R A) (toSharedTree_substTree R A)

/-- The natural event isomorphism retains every assignment at every history node. -/
noncomputable def eventIso (A : BindingCloneAlgebra.Algebra.{u} S) :
    events (sharedTreeModel R A).toAction ≅ events (localTreeModel R A).toAction where
  hom := eventMap R A
  inv := inverseEventMap R A
  hom_inv_id := by
    ext X event
    rcases event with ⟨sort, pair, tree⟩
    change (⟨sort, pair, toSharedTree R A _ (toLocalTree R A _ tree)⟩ :
      Event (sharedTreeModel R A).toAction X.unop.context) = ⟨sort, pair, tree⟩
    exact congrArg (fun value : IntrinsicScopedConditionalSubstitution.Tree R A
      (⟨X.unop.context, sort, pair⟩ : Judgment A) =>
        (⟨sort, pair, value⟩ : Event (sharedTreeModel R A).toAction X.unop.context))
      (IntrinsicScopedSharedLocalTreeComparison.toShared_toLocal R A _ tree)
  inv_hom_id := by
    ext X event
    rcases event with ⟨sort, pair, tree⟩
    change (⟨sort, pair, toLocalTree R A _ (toSharedTree R A _ tree)⟩ :
      Event (localTreeModel R A).toAction X.unop.context) = ⟨sort, pair, tree⟩
    exact congrArg (fun value : IntrinsicScopedLocalPolynomial.Tree (localRules R) A
      (⟨X.unop.context, sort, pair⟩ : Judgment A) =>
        (⟨sort, pair, value⟩ : Event (localTreeModel R A).toAction X.unop.context))
      (IntrinsicScopedSharedLocalTreeComparison.toLocal_toShared R A _ tree)

/-- Both endpoint maps are preserved by the complete-history comparison. -/
noncomputable def graphMap (A : BindingCloneAlgebra.Algebra.{u} S) :
    graph (sharedTreeModel R A).toAction ⟶ graph (localTreeModel R A).toAction :=
  mapGraph (toLocalTree R A) (toLocalTree_substTree R A)

noncomputable def inverseGraphMap (A : BindingCloneAlgebra.Algebra.{u} S) :
    graph (localTreeModel R A).toAction ⟶ graph (sharedTreeModel R A).toAction :=
  mapGraph (toSharedTree R A) (toSharedTree_substTree R A)

/-- The graph comparison is an isomorphism over the actual program states. -/
noncomputable def graphIso (A : BindingCloneAlgebra.Algebra.{u} S) :
    graph (sharedTreeModel R A).toAction ≅ graph (localTreeModel R A).toAction where
  hom := graphMap R A
  inv := inverseGraphMap R A
  hom_inv_id := by
    apply FreePresheafEventExtension.Hom.ext
    exact (eventIso R A).hom_inv_id
  inv_hom_id := by
    apply FreePresheafEventExtension.Hom.ext
    exact (eventIso R A).inv_hom_id

/-- Reverse support follows here from the actual whole-history coverage. -/
theorem reduction_eq (A : BindingCloneAlgebra.Algebra.{u} S) :
    reduction (sharedTreeModel R A).toAction = reduction (localTreeModel R A).toAction :=
  endpointImage_eq_of_coverage (graphMap R A)
    (mapEvents_surjective
      (Y := (sharedTreeModel R A).toAction) (Z := (localTreeModel R A).toAction)
      (toLocalTree R A) (toLocalTree_substTree R A)
      (fun j value => ⟨toSharedTree R A j value,
        IntrinsicScopedSharedLocalTreeComparison.toLocal_toShared R A j value⟩))

/-- At every context, shared and unpruned local retained witnesses have the same support. -/
theorem retainedWitness_iff (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A) :
    Nonempty ((sharedTreeModel R A).toAction.carrier j) ↔
      Nonempty ((localTreeModel R A).carrier j) :=
  ⟨fun ⟨tree⟩ => ⟨toLocalTree R A j tree⟩, fun ⟨tree⟩ => ⟨toSharedTree R A j tree⟩⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedSharedLocalPresheafComparison
