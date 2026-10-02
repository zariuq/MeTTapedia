import Mettapedia.OSLF.Syntax.IntrinsicScopedJudgmentActionPresheaf
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalSubstitutionModel

/-!
# Retained event presheaves of rule-local substitution models

The actual evidence carrier and contextual action of a rule-local model
supply its event presheaf. Both endpoints are natural, and the image predicate
holds exactly when that model retains an indexed witness. No global telescope
is introduced. Comparisons with a shared telescope require an actual evidence
map; reverse support is proved here under actual target-witness coverage.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalModelPresheaf

open _root_.CategoryTheory
open IntrinsicScopedConditionalPresheaf (Base states)
open IntrinsicScopedLocalPolynomial (LocalRule)
open IntrinsicScopedLocalSubstitutionModel (SubstitutionModel)
open AuthoredPositionedRulePolynomial (Judgment)

universe u w
variable {S : Signature} (R : List (LocalRule S))
variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- Each event retains the actual local model's evidence and sorted endpoints. -/
abbrev ModelEvent (Y : SubstitutionModel.{u, w} R A) (Γ : Ctx S) : Type (max u w) :=
  IntrinsicScopedJudgmentActionPresheaf.Event Y.toAction Γ

/-- Reindex the retained evidence by the model's existing substitution action. -/
noncomputable def mapModelEvent (Y : SubstitutionModel.{u, w} R A)
    {X Z : Base A} (f : X ⟶ Z) :
    ModelEvent R Y X.unop.context → ModelEvent R Y Z.unop.context :=
  IntrinsicScopedJudgmentActionPresheaf.mapEvent Y.toAction f

/-- The presheaf uses no rule-telescope conversion or replacement evidence. -/
noncomputable def modelEvents (Y : SubstitutionModel.{u, w} R A) :
    Base A ⥤ Type (max u w) :=
  IntrinsicScopedJudgmentActionPresheaf.events Y.toAction

/-- The explicit common-universe state object for arbitrary local evidence. -/
def modelStates (A : BindingCloneAlgebra.Algebra.{u} S) : Base A ⥤ Type (max u w) :=
  IntrinsicScopedJudgmentActionPresheaf.liftedStates.{u, w} A

def modelSource (Y : SubstitutionModel.{u, w} R A) : modelEvents R Y ⟶ modelStates.{u, w} A :=
  IntrinsicScopedJudgmentActionPresheaf.liftedSource Y.toAction

def modelTarget (Y : SubstitutionModel.{u, w} R A) : modelEvents R Y ⟶ modelStates.{u, w} A :=
  IntrinsicScopedJudgmentActionPresheaf.liftedTarget Y.toAction

/-- The actual local evidence graph retains every witness in its own universe. -/
noncomputable def modelGraph (Y : SubstitutionModel.{u, w} R A) :
    FreePresheafEventExtension.Graph (modelStates.{u, w} A) :=
  IntrinsicScopedJudgmentActionPresheaf.liftedGraph Y.toAction

/-- Reduction is the endpoint image of retained local evidence. -/
noncomputable def modelReduction (Y : SubstitutionModel.{u, w} R A) :
    Subfunctor (FunctorToTypes.prod (modelStates.{u, w} A) (modelStates.{u, w} A)) :=
  IntrinsicScopedJudgmentActionPresheaf.liftedReduction Y.toAction

/-- Every section of the image has an actual local witness, and every
retained witness supplies a section of that endpoint image. -/
theorem mem_modelReduction_iff (Y : SubstitutionModel.{u, w} R A)
    (X : Base A) (sort : S.Srt) (first last : A.substitution.Carrier X.unop.context sort) :
    ((ULift.up ⟨sort, first⟩, ULift.up ⟨sort, last⟩) :
      (modelStates.{u, w} A).obj X × (modelStates.{u, w} A).obj X) ∈
        (modelReduction R Y).obj X ↔
      Nonempty (Y.carrier ⟨X.unop.context, sort, (first, last)⟩) :=
  IntrinsicScopedJudgmentActionPresheaf.mem_liftedReduction_iff Y.toAction X sort first last

/-- An ordinary local model map acts naturally on the retained evidence. -/
def mapModelEvents {Y Z : SubstitutionModel.{u, w} R A}
    (h : SubstitutionModel.Hom R A Y Z) : modelEvents R Y ⟶ modelEvents R Z :=
  IntrinsicScopedJudgmentActionPresheaf.mapEvents
    (fun j => h.evidence.toFun () j) h.preserves

/-- Local model maps preserve both natural endpoint projections. -/
def mapModelGraph {Y Z : SubstitutionModel.{u, w} R A}
    (h : SubstitutionModel.Hom R A Y Z) : modelGraph R Y ⟶ modelGraph R Z :=
  IntrinsicScopedJudgmentActionPresheaf.mapLiftedGraph
    (fun j => h.evidence.toFun () j) h.preserves

/-- Every local interpretation preserves reductions forward. -/
theorem modelReduction_le {Y Z : SubstitutionModel.{u, w} R A}
    (h : SubstitutionModel.Hom R A Y Z) : modelReduction R Y ≤ modelReduction R Z :=
  IntrinsicScopedJudgmentActionPresheaf.endpointImage_le_of_hom (mapModelGraph R h)

/-- Reverse support follows from actual indexed witness coverage; it does
not assert an inverse map or preserve multiplicities of unused assignments. -/
theorem modelReduction_eq_of_coverage {Y Z : SubstitutionModel.{u, w} R A}
    (h : SubstitutionModel.Hom R A Y Z)
    (coverage : ∀ j, Function.Surjective (h.evidence.toFun () j)) :
    modelReduction R Y = modelReduction R Z :=
  IntrinsicScopedJudgmentActionPresheaf.liftedReduction_eq_of_coverage
    (fun j => h.evidence.toFun () j) h.preserves coverage

/-- Forgetting the explicit lift at matching universes is natural in all
context substitutions and commutes with both local endpoint maps. -/
def modelStatesIso (A : BindingCloneAlgebra.Algebra.{u} S) :
    modelStates.{u, u} A ≅ states A :=
  IntrinsicScopedJudgmentActionPresheaf.liftedStatesIso A

theorem modelSource_statesIso (Y : SubstitutionModel.{u, u} R A) :
    modelSource R Y ≫ (modelStatesIso A).hom =
      IntrinsicScopedJudgmentActionPresheaf.source Y.toAction :=
  IntrinsicScopedJudgmentActionPresheaf.liftedSource_statesIso Y.toAction

theorem modelTarget_statesIso (Y : SubstitutionModel.{u, u} R A) :
    modelTarget R Y ≫ (modelStatesIso A).hom =
      IntrinsicScopedJudgmentActionPresheaf.target Y.toAction :=
  IntrinsicScopedJudgmentActionPresheaf.liftedTarget_statesIso Y.toAction

/-- The local model graph construction is functorial on all model maps. -/
noncomputable def modelGraphFunctor (A : BindingCloneAlgebra.Algebra.{u} S) :
    SubstitutionModel.{u, w} R A ⥤ FreePresheafEventExtension.Graph (modelStates.{u, w} A) where
  obj Y := modelGraph R Y
  map h := mapModelGraph R h
  map_id Y := by
    apply FreePresheafEventExtension.Hom.ext
    ext X event
    rfl
  map_comp first second := by
    apply FreePresheafEventExtension.Hom.ext
    ext X event
    rfl

/-- A rule-local node retains the model's action on its whole ordered
premise family, each child at its declared binder-local judgment. -/
def ruleEvent (Y : SubstitutionModel.{u, w} R A) {j : Judgment A}
    (shape : IntrinsicScopedLocalPolynomial.Shape R A j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      Y.carrier (IntrinsicScopedLocalPolynomial.childJudgment R A shape.1 position)) :
    ModelEvent R Y j.1 :=
  ⟨j.2.1, j.2.2, Y.rules.act () j ⟨shape, children⟩⟩

/-- Every actual rule action supplies a retained reduction section. -/
theorem ruleEvent_mem_reduction (Y : SubstitutionModel.{u, w} R A) {j : Judgment A}
    (shape : IntrinsicScopedLocalPolynomial.Shape R A j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      Y.carrier (IntrinsicScopedLocalPolynomial.childJudgment R A shape.1 position)) :
    let X : Base A := Opposite.op
      (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
        A.substitution.toClone j.1)
    ((ULift.up ⟨j.2.1, j.2.2.1⟩, ULift.up ⟨j.2.1, j.2.2.2⟩) :
      (modelStates.{u, w} A).obj X × (modelStates.{u, w} A).obj X) ∈
      (modelReduction R Y).obj X := by
  exact (mem_modelReduction_iff R Y
    (Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
      A.substitution.toClone j.1)) j.2.1 j.2.2.1 j.2.2.2).mpr
        ⟨Y.rules.act () j ⟨shape, children⟩⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalModelPresheaf
