import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels
import Mettapedia.OSLF.Syntax.IndexedOperationalModelReindex
import Mettapedia.OSLF.Syntax.MonoidEquationRung

/-!
# Comparing scoped substitution models with indexed operational models

An intrinsic conditional presentation already has a functor of rule
polynomials over its binding/equation models. A substitution-operational
model has more structure than an algebra for that polynomial: its evidence
also admits a contextual substitution action, compatible with each rule
constructor. Forgetting that action preserves the actual authored base,
the individual firing evidence, and maps of that evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

open CategoryTheory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IndexedOperationalModelsOver
open Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M)) (E : List (EqAxiom S M))

/-- Forget the contextual action while retaining each constructor action,
its recursively supplied premise evidence, and its equation-model base. -/
noncomputable def forgetSubstitution :
    SubstitutionOperationalModel R E ⥤
      IntrinsicScopedConditionalPolynomial.Model R E where
  obj X := { base := X.base, evidence := X.model.evidence }
  map f :=
    { base := f.base
      evidence :=
        { presentation := presentationMap R f.base
          toFun := f.evidence.toFun
          preserves := f.evidence.commutes }
      presentationEq := rfl }
  map_id := by
    intro X
    apply IndexedOperationalModelsOver.Hom.ext (presentationFunctor R E)
    · rfl
    · apply Equipped.Map.ext_of_pointwise rfl
      intro b i value
      rfl
  map_comp := by
    intro X Y Z f g
    apply IndexedOperationalModelsOver.Hom.ext (presentationFunctor R E)
    · rfl
    · apply Equipped.Map.ext_of_pointwise rfl
      intro b i value
      rfl

/-- A substitution-model map is determined by its underlying authored-base
map and evidence map. Thus forgetting the action is faithful. -/
instance forgetSubstitution_faithful :
    (forgetSubstitution R E).Faithful where
  map_injective := by
    intro X Y f g same
    have baseEq : f.base = g.base :=
      congrArg IndexedOperationalModelsOver.Hom.base same
    apply SubstitutionOperationalModel.Hom.ext
    · exact baseEq
    · intro j value
      cases f with
      | mk fBase fEvidence fPreserves =>
        cases g with
        | mk gBase gEvidence gPreserves =>
          change fBase = gBase at baseEq
          cases baseEq
          have evidenceEq := congrArg
            (fun h : IndexedOperationalModelsOver.Hom (presentationFunctor R E)
              ((forgetSubstitution R E).obj X) ((forgetSubstitution R E).obj Y) =>
              h.evidence) same
          injection evidenceEq with _ evidenceFunEq
          exact heq_of_eq
            (congrFun (congrFun (congrFun evidenceFunEq ()) j) value)

/-- The free scoped substitution model and the free indexed rule-algebra
model have exactly the same underlying equation model and firing trees. -/
theorem forgetSubstitution_free
    (X : FreeBindingEquationModel.Model E) :
    (forgetSubstitution R E).obj (SubstitutionOperationalModel.free R X) =
      IndexedOperationalModelsOver.free (presentationFunctor R E) X := by
  rfl

/-- The initial scoped operational interpretation has the same carrier and
rule algebra as the previously constructed initial indexed model. -/
theorem forgetSubstitution_presented :
    (forgetSubstitution R E).obj (SubstitutionOperationalModel.presented R E) =
      IntrinsicScopedConditionalPolynomial.presented R E := by
  rfl

/-- The interpretation of free firing histories is the same on both sides
of the comparison. This compares the actual recursive folds, including
ordered premise evidence, rather than merely comparing their carriers. -/
theorem forgetSubstitution_lift
    (X : FreeBindingEquationModel.Model E)
    (Y : SubstitutionOperationalModel R E)
    (baseMap : FreeBindingClone.Hom X.algebra Y.base.algebra) :
    (forgetSubstitution R E).map (SubstitutionOperationalModel.lift R X Y baseMap) =
      IndexedOperationalModelsOver.lift (presentationFunctor R E)
        ((forgetSubstitution R E).obj Y) baseMap := by
  apply IndexedOperationalModelsOver.Hom.ext (presentationFunctor R E)
  · rfl
  · apply Equipped.Map.ext_of_pointwise rfl
    intro b i value
    rfl

section NoAutomaticSubstitution

universe u

variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- With no rule constructors, an indexed evidence algebra may be supported
at just one contextual judgment. This is a legitimate polynomial algebra;
the absent constructor shapes impose no further closure condition. -/
def pointEvidence (j₀ : AuthoredPositionedRulePolynomial.Judgment A) :
    OperationalRuleModels.Model
      (rules ([] : List (Rule S M)) A) where
  carrier := fun _ j => ULift.{u} (PLift (j = j₀))
  rules :=
    { act := by
        intro b j layer
        exact Fin.elim0 layer.1.1.index }

/-- If a contextual substitution moves the supported judgment, this
otherwise lawful evidence algebra cannot carry a substitution action.
Thus the substitution-operational model class is strictly more structured
than the category of bare indexed rule algebras whenever such a move exists. -/
theorem pointEvidence_no_substitution_action
    (j₀ : AuthoredPositionedRulePolynomial.Judgment A)
    {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier j₀.1 Δ)
    (moves : substJudgment j₀ σ ≠ j₀) :
    ¬ ∃ X : SubstitutionModel ([] : List (Rule S M)) A,
      X.evidence = pointEvidence j₀ := by
  rintro ⟨X, equal⟩
  have atSource : X.evidence.carrier () j₀ := by
    rw [equal]
    exact ⟨⟨rfl⟩⟩
  have atTarget := X.act j₀ atSource σ (substJudgment j₀ σ) rfl
  have observed : (pointEvidence (M := M) j₀).carrier ()
      (substJudgment j₀ σ) := by
    rw [← equal]
    exact atTarget
  have forced : substJudgment j₀ σ = j₀ := by
    exact observed.down.down
  exact moves forced

end NoAutomaticSubstitution

namespace MonoidNegativeControl

open Mettapedia.OSLF.Binding.MonoidEquationRung

private abbrev A := BindingCloneAlgebra.terms sig

/-- The monoid unit gives a concrete closed, well-sorted judgment. -/
def unitJudgment : AuthoredPositionedRulePolynomial.Judgment A :=
  ⟨[], .element, unitT, unitT⟩

/-- Weakening the empty context requires no term assignments. -/
def weakenToOne : BindingSubstitutionAlgebra.Environment sig
    A.substitution.Carrier unitJudgment.1 [.element] :=
  fun _ v => nomatch v

theorem weaken_moves :
    substJudgment unitJudgment weakenToOne ≠ unitJudgment := by
  intro equality
  have contextEq := congrArg Sigma.fst equality
  cases contextEq

/-- Even for the authored monoid signature with no operational rules,
an arbitrary indexed evidence carrier need not admit the contextual
substitution required of a genuine scoped operational interpretation. -/
theorem pointEvidence_has_no_action :
    ¬ ∃ X : SubstitutionModel
        ([] : List (Rule sig metas)) A,
      X.evidence = pointEvidence unitJudgment :=
  pointEvidence_no_substitution_action unitJudgment
    weakenToOne weaken_moves

end MonoidNegativeControl

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
