import Mettapedia.OSLF.Syntax.SemanticContextualMetavariables
import Mettapedia.OSLF.Syntax.FreeBindingEquationModel
import Mettapedia.OSLF.Syntax.IndexedRulePresentationCategory
import Mettapedia.OSLF.Syntax.IndexedOperationalModelsOver

/-!
# Positioned authored rewrites over semantic binding models

An authored positioned rewrite has a rule index, a valuation of its declared
metavariables, and a closing environment for its ordinary variables. These
are retained as constructor data even when distinct occurrences have equal
endpoints. Interpretation in a binding clone supplies a sorted judgment. A
binding-clone morphism maps the occurrence and its judgment coherently.

This polynomial contains the base rules with no recursive premises. It is
the varying-semantic-model counterpart of the fixed-state event-graph
presentation; conditional and congruence rules require additional premise
positions and their local binder contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.BindingEquationalModels
open Mettapedia.OSLF.Binding.BindingEquationInterpretation
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory

universe u v w

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (PositionedRewrite (withMetas S M)))

/-- A sorted, contextual pair of interpreted program states. -/
abbrev Judgment (A : BindingCloneAlgebra.Algebra.{u} S) :=
  Σ Γ : Ctx S, Σ sort : S.Srt,
    A.substitution.Carrier Γ sort × A.substitution.Carrier Γ sort

/-- One authored base-rule occurrence, with its actual index, semantic
metavariable values, and ordinary closing environment. -/
structure RuleInstance (A : BindingCloneAlgebra.Algebra.{u} S) where
  index : Fin R.length
  ambient : Ctx S
  valuation : Valuation (M := M) A ambient
  close : BindingSubstitutionAlgebra.Environment S
    A.substitution.Carrier (R.get index).ctx ambient

/-- The two interpreted endpoints of this occurrence retain their ambient
context and declared result sort. -/
def judgmentOf (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : RuleInstance R A) : Judgment A :=
  ⟨occurrence.ambient, (R.get occurrence.index).sort,
    interpretSchema A occurrence.valuation
      (fun _ var => A.substitution.injectVar var) occurrence.close
      (R.get occurrence.index).lhs,
    interpretSchema A occurrence.valuation
      (fun _ var => A.substitution.injectVar var) occurrence.close
      (R.get occurrence.index).rhs⟩

/-- Constructor shapes are individual rule occurrences whose interpreted
endpoint judgment is the given index. -/
abbrev Shape (A : BindingCloneAlgebra.Algebra.{u} S)
    (j : Judgment A) :=
  {occurrence : RuleInstance R A // judgmentOf R A occurrence = j}

/-- The base-rule polynomial has one constructor for each interpreted
occurrence and no recursive premise positions. -/
def rules (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedPolynomial Unit (fun _ => Judgment A) where
  Shape _ j := Shape R A j
  Position _ := Empty
  next _ impossible := impossible.elim

/-- Map a sorted judgment along a binding-clone morphism. -/
def mapJudgment {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) : Judgment A → Judgment B
  | ⟨Γ, sort, source, target⟩ =>
      ⟨Γ, sort, h.raw.map source, h.raw.map target⟩

theorem mapJudgment_id (A : BindingCloneAlgebra.Algebra.{u} S)
    (j : Judgment A) :
    mapJudgment (FreeBindingClone.Hom.id A) j = j := by
  cases j with
  | mk Γ rest =>
    cases rest with
    | mk sort endpoints => rfl

theorem mapJudgment_comp
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    {C : BindingCloneAlgebra.Algebra.{w} S}
    (f : FreeBindingClone.Hom A B) (g : FreeBindingClone.Hom B C)
    (j : Judgment A) :
    mapJudgment (FreeBindingClone.Hom.comp f g) j =
      mapJudgment g (mapJudgment f j) := by
  cases j with
  | mk Γ rest =>
    cases rest with
    | mk sort endpoints => rfl

/-- Transport one occurrence without forgetting its authored rule index or
its contextual metavariable and ordinary-variable assignments. -/
def mapInstance {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    (occurrence : RuleInstance R A) : RuleInstance R B where
  index := occurrence.index
  ambient := occurrence.ambient
  valuation := mapValuation h occurrence.valuation
  close := fun sort var => h.raw.map (occurrence.close sort var)

theorem mapInstance_id (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : RuleInstance R A) :
    mapInstance R (FreeBindingClone.Hom.id A) occurrence = occurrence := by
  cases occurrence
  rfl

theorem mapInstance_comp
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    {C : BindingCloneAlgebra.Algebra.{w} S}
    (f : FreeBindingClone.Hom A B) (g : FreeBindingClone.Hom B C)
    (occurrence : RuleInstance R A) :
    mapInstance R (FreeBindingClone.Hom.comp f g) occurrence =
      mapInstance R g (mapInstance R f occurrence) := by
  cases occurrence
  rfl

/-- The interpreted endpoints of every mapped authored occurrence are the
image of its original endpoint judgment. -/
theorem mapInstance_judgment
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    (occurrence : RuleInstance R A) :
    judgmentOf R B (mapInstance R h occurrence) =
      mapJudgment h (judgmentOf R A occurrence) := by
  rcases occurrence with ⟨index, ambient, valuation, close⟩
  have sourceEq := interpretSchema_map h valuation
    (fun _ var => A.substitution.injectVar var) close (R.get index).lhs
  have targetEq := interpretSchema_map h valuation
    (fun _ var => A.substitution.injectVar var) close (R.get index).rhs
  have ambientEq :
      (fun s var => h.raw.map (A.substitution.injectVar var) :
        BindingSubstitutionAlgebra.Environment S B.substitution.Carrier
          ambient ambient) =
      (fun _ var => B.substitution.injectVar var) := by
    funext s var
    exact h.raw.map_variable var
  rw [ambientEq] at sourceEq targetEq
  simp only [judgmentOf, mapInstance, mapJudgment]
  rw [sourceEq, targetEq]

/-- Map a constructor at its exact sorted judgment. -/
def mapShape {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : Shape R A j) :
    Shape R B (mapJudgment h j) :=
  ⟨mapInstance R h shape.1,
    (mapInstance_judgment R h shape.1).trans
      (congrArg (mapJudgment h) shape.2)⟩

theorem mapShape_id (A : BindingCloneAlgebra.Algebra.{u} S)
    {j : Judgment A} (shape : Shape R A j) :
    mapShape R (FreeBindingClone.Hom.id A) shape = shape := by
  apply Subtype.ext
  exact mapInstance_id R A shape.1

theorem mapShape_comp
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    {C : BindingCloneAlgebra.Algebra.{w} S}
    (f : FreeBindingClone.Hom A B) (g : FreeBindingClone.Hom B C)
    {j : Judgment A} (shape : Shape R A j) :
    mapShape R (FreeBindingClone.Hom.comp f g) shape =
      mapShape R g (mapShape R f shape) := by
  apply Subtype.ext
  exact mapInstance_comp R f g shape.1

/-- The semantic positioned-rule polynomial as a presentation with one
context base object. Contexts remain inside its sorted judgment indices. -/
def presentation (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedRulePresentationCategory.Presentation Unit where
  Judgment _ := Judgment A
  rules := rules R A

/-- A binding-clone map preserves every base-rule constructor. With no
recursive premises, the position equivalence is the unique empty one. -/
def presentationMap
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) :
    presentation R A ⟶ presentation R B where
  judgment _ := mapJudgment h
  rules := {
    onShape := fun _ _ shape => mapShape R h shape
    onPosition := fun _ _ _ => Equiv.refl Empty
    onNext := by intro _ _ _ impossible; exact impossible.elim
  }

/-- Identity on semantic equation models acts identically on every retained
authored base-rule occurrence. -/
theorem presentationMap_id (A : BindingCloneAlgebra.Algebra.{u} S) :
    presentationMap R (FreeBindingClone.Hom.id A) =
      𝟙 (presentation R A) := by
  apply IndexedRulePresentationCategory.Presentation.Map.ext
  · funext b j
    exact mapJudgment_id A j
  · apply heq_of_eq
    apply IndexedRulePolynomialMorphisms.Hom.ext_of_subsingleton_positions
    · funext b j shape
      exact mapShape_id R A shape
    · intro b j shape
      change Subsingleton Empty
      infer_instance

/-- Semantic model maps compose on every authored occurrence, not merely on
the relation obtained by forgetting constructor identity. -/
theorem presentationMap_comp
    {A B C : BindingCloneAlgebra.Algebra.{u} S}
    (f : FreeBindingClone.Hom A B)
    (g : FreeBindingClone.Hom B C) :
    presentationMap R (FreeBindingClone.Hom.comp f g) =
      presentationMap R f ≫ presentationMap R g := by
  apply IndexedRulePresentationCategory.Presentation.Map.ext
  · funext b j
    exact mapJudgment_comp f g j
  · apply heq_of_eq
    apply IndexedRulePolynomialMorphisms.Hom.ext_of_subsingleton_positions
    · funext b j shape
      exact mapShape_comp R f g shape
    · intro b j shape
      change Subsingleton Empty
      infer_instance

/-- The authored base-rule presentation varies functorially over semantic
models of any selected equation theory. Equation satisfaction belongs to the
base model; this rule functor retains the individual positioned occurrences. -/
def presentationFunctor (E : List (EqAxiom S M)) :
    FreeBindingEquationModel.Model.{0} E ⥤
      IndexedRulePresentationCategory.Presentation Unit where
  obj X := presentation R X.algebra
  map h := presentationMap R h
  map_id X := presentationMap_id R X.algebra
  map_comp f g := presentationMap_comp R f g

/-- A semantic binding-equation model with an action interpreting every
authored positioned base-rule occurrence. -/
abbrev Model (E : List (EqAxiom S M)) :=
  IndexedOperationalModelsOver.Model (presentationFunctor R E)

/-- An interpretation preserves the binding-equation model, each authored
rule constructor, and its individual firing evidence. -/
abbrev Hom (E : List (EqAxiom S M)) (A B : Model R E) :=
  IndexedOperationalModelsOver.Hom (presentationFunctor R E) A B

/-- The free operational model over the authored equation quotient. -/
noncomputable def presented (E : List (EqAxiom S M)) : Model R E :=
  IndexedOperationalModelsOver.free (presentationFunctor R E)
    (FreeBindingEquationModel.presented E)

/-- Freely adjoining authored base-rule firings is left adjoint to
forgetting their evidence algebra. -/
noncomputable def freeAdjunction (E : List (EqAxiom S M)) :
    IndexedOperationalModelsOver.freeFunctor (presentationFunctor R E) ⊣
      IndexedOperationalModelsOver.forget (presentationFunctor R E) :=
  IndexedOperationalModelsOver.freeAdjunction (presentationFunctor R E)

/-- The unique simultaneous interpretation of binding syntax, equations,
and positioned base-rule firing evidence into a target model. -/
noncomputable def interpret (E : List (EqAxiom S M)) (target : Model R E) :
    Hom R E (presented R E) target :=
  IndexedOperationalModelsOver.initialHom (presentationFunctor R E)
    (FreeBindingEquationModel.presentedIsInitial E) target

/-- The binding/equation component of the combined interpretation is the
existing unique interpretation of the authored equation quotient. -/
theorem interpret_base (E : List (EqAxiom S M)) (target : Model R E) :
    (interpret R E target).base =
      FreeBindingEquationModel.interpretHom target.base := by
  rfl

/-- The free equation quotient with freely generated individual authored
base-rule firings is initial in the combined model category. -/
noncomputable def presentedIsInitial (E : List (EqAxiom S M)) :
    CategoryTheory.Limits.IsInitial (presented R E) :=
  IndexedOperationalModelsOver.freeIsInitial (presentationFunctor R E)
    (FreeBindingEquationModel.presentedIsInitial E)

#print axioms mapInstance_judgment
#print axioms mapShape_comp
#print axioms presentationMap_id
#print axioms presentationMap_comp
#print axioms presentationFunctor
#print axioms freeAdjunction
#print axioms interpret_base
#print axioms presentedIsInitial

end Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial
