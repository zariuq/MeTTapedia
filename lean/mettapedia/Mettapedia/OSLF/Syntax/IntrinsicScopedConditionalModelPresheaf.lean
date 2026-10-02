import Mettapedia.OSLF.Syntax.BindingFunctionArgumentComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedJudgmentActionPresheaf

/-!
# Event presheaves of arbitrary substitution-operational models

The free firing-tree model is one instance of a more general fact. Any
lawful substitution-operational model carries an individual-evidence
presheaf on the same clone context category as its program states. This
construction retains all evidence values and uses the model's actual
substitution action; it does not replace events by an endpoint predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- An individual piece of evidence at its sorted source and target terms. -/
abbrev ModelEvent {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) (Γ : Ctx S) : Type u :=
  IntrinsicScopedJudgmentActionPresheaf.Event Y.toAction Γ

/-- Shared-rule models use the common retained-evidence substitution action. -/
noncomputable def mapModelEvent {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) {X Z : Base A} (f : X ⟶ Z) :
    ModelEvent R Y X.unop.context → ModelEvent R Y Z.unop.context :=
  IntrinsicScopedJudgmentActionPresheaf.mapEvent Y.toAction f

theorem mapModelEvent_id {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) (X : Base A) (event : ModelEvent R Y X.unop.context) :
    mapModelEvent R Y (𝟙 X) event = event :=
  IntrinsicScopedJudgmentActionPresheaf.mapEvent_id Y.toAction X event

theorem mapModelEvent_comp {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) {X V Z : Base A} (f : X ⟶ V) (g : V ⟶ Z)
    (event : ModelEvent R Y X.unop.context) :
    mapModelEvent R Y (f ≫ g) event = mapModelEvent R Y g (mapModelEvent R Y f event) :=
  IntrinsicScopedJudgmentActionPresheaf.mapEvent_comp Y.toAction f g event

/-- The evidence presheaf is constructed from the model's existing action. -/
noncomputable def modelEvents {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) : Base A ⥤ Type u :=
  IntrinsicScopedJudgmentActionPresheaf.events Y.toAction

/-- The source endpoint is the common natural endpoint projection. -/
def modelSource {A : BindingCloneAlgebra.Algebra.{u} S} (Y : SubstitutionModel R A) :
    modelEvents R Y ⟶ states A :=
  IntrinsicScopedJudgmentActionPresheaf.source Y.toAction

/-- The target endpoint is the common natural endpoint projection. -/
def modelTarget {A : BindingCloneAlgebra.Algebra.{u} S} (Y : SubstitutionModel R A) :
    modelEvents R Y ⟶ states A :=
  IntrinsicScopedJudgmentActionPresheaf.target Y.toAction

/-- The model graph retains every individual piece of operational evidence. -/
noncomputable def modelGraph {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) : FreePresheafEventExtension.Graph (states A) :=
  IntrinsicScopedJudgmentActionPresheaf.graph Y.toAction

/-- A morphism of substitution-operational models maps each retained event
to its interpreted evidence at the same sorted endpoints. -/
def mapModelEvents
    {A : BindingCloneAlgebra.Algebra.{u} S} {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) : modelEvents R Y ⟶ modelEvents R Z :=
  IntrinsicScopedJudgmentActionPresheaf.mapEvents
    (fun j => h.evidence.toFun () j) h.preserves

/-- Every lawful model map preserves both endpoint maps while retaining
its individual evidence map. -/
def mapModelGraph
    {A : BindingCloneAlgebra.Algebra.{u} S} {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) : modelGraph R Y ⟶ modelGraph R Z :=
  IntrinsicScopedJudgmentActionPresheaf.mapGraph
    (fun j => h.evidence.toFun () j) h.preserves

/-- The graph construction is functorial on genuine evidence-preserving
model maps, with no extra target coverage or injectivity condition. -/
noncomputable def modelGraphFunctor
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    SubstitutionModel R A ⥤
      FreePresheafEventExtension.Graph (states A) where
  obj Y := modelGraph R Y
  map h := mapModelGraph R h
  map_id Y := by
    apply FreePresheafEventExtension.Hom.ext
    ext X event
    rfl
  map_comp f g := by
    apply FreePresheafEventExtension.Hom.ext
    ext X event
    rfl

/-- The endpoint predicate is a separate image observation of the event
graph. This image exists in the concrete presheaf model; no image structure
is claimed for an arbitrary finitely complete target. -/
noncomputable def modelReduction
    {A : BindingCloneAlgebra.Algebra.{u} S} (Y : SubstitutionModel R A) :
    Subfunctor (FunctorToTypes.prod (states A) (states A)) :=
  IntrinsicScopedJudgmentActionPresheaf.reduction Y.toAction

/-- The observed one-step relation holds exactly when the model retains
some evidence at that sorted pair of program endpoints. -/
theorem mem_modelReduction_iff
    {A : BindingCloneAlgebra.Algebra.{u} S} (Y : SubstitutionModel R A) (X : Base A)
    (sort : S.Srt) (first last : A.substitution.Carrier X.unop.context sort) :
    ((⟨sort, first⟩, ⟨sort, last⟩) : (states A).obj X × (states A).obj X) ∈
        (modelReduction R Y).obj X ↔
      Nonempty (Y.evidence.carrier ()
        (⟨X.unop.context, sort, (first, last)⟩ : Judgment A)) :=
  IntrinsicScopedJudgmentActionPresheaf.mem_reduction_iff Y.toAction X sort first last

/-- Every ordinary model interpretation preserves the one-step existence
predicate in the forward direction. It need not cover additional target
events or reflect reductions. -/
theorem modelReduction_le
    {A : BindingCloneAlgebra.Algebra.{u} S} {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) : modelReduction R Y ≤ modelReduction R Z :=
  IntrinsicScopedJudgmentActionPresheaf.endpointImage_le_of_hom (mapModelGraph R h)

/-- The model-level event construction specializes exactly to the already
established free firing-tree presheaf. -/
theorem free_modelEvents_eq
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    modelEvents R (SubstitutionModel.free R A) = events R A := rfl

theorem free_modelGraph_eq
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    modelGraph R (SubstitutionModel.free R A) = graph R A := rfl

theorem free_modelReduction_eq
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    modelReduction R (SubstitutionModel.free R A) = reduction R A := rfl

#print axioms modelEvents
#print axioms modelGraph
#print axioms mem_modelReduction_iff
#print axioms mapModelGraph
#print axioms modelGraphFunctor
#print axioms modelReduction_le
#print axioms free_modelEvents_eq
#print axioms free_modelReduction_eq

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
