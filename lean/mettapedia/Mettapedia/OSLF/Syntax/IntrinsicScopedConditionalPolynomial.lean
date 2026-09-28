import Mettapedia.OSLF.Syntax.SemanticScopedPremiseInterpretation

/-!
# Intrinsic scoped conditional rules as indexed polynomials

A rule has an authored positioned conclusion and an ordered list of step
premises. Each premise carries its own binder context and endpoint sort.
Interpreting the rule in a binding clone yields one constructor occurrence
and one recursive position for each premise. The positions retain their list
indices even when two child judgments happen to be equal.

This is the intrinsic binding-signature interface. Compiling arbitrary
canonical `LanguageDef` patterns, collection rests, root queries, and
premise-produced assignments into it is a separate source comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open CategoryTheory CategoryTheory.Limits

universe u v w

/-- One intrinsically typed rule, with its selected redex position and a
finite ordered family of recursive, binder-local step premises. -/
structure Rule (S : Signature) (M : List (MetaArity S)) where
  conclusion : PositionedRewrite (withMetas S M)
  premises : List (LocalStepPremise (withMetas S M) conclusion.ctx)

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- One rule occurrence retains its selected authored declaration,
contextual metavariable assignment, and ordinary closing environment. -/
structure Instance (A : BindingCloneAlgebra.Algebra.{u} S) where
  index : Fin R.length
  ambient : Ctx S
  valuation : Valuation (M := M) A ambient
  close : BindingSubstitutionAlgebra.Environment S
    A.substitution.Carrier (R.get index).conclusion.ctx ambient

/-- The semantic conclusion at this exact sorted ambient judgment. -/
def conclusionJudgment (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A) : Judgment A :=
  ⟨occurrence.ambient, (R.get occurrence.index).conclusion.sort,
    interpretSchema A occurrence.valuation
      (fun _ var => A.substitution.injectVar var) occurrence.close
      (R.get occurrence.index).conclusion.lhs,
    interpretSchema A occurrence.valuation
      (fun _ var => A.substitution.injectVar var) occurrence.close
      (R.get occurrence.index).conclusion.rhs⟩

/-- Each recursive premise requests a child in its own binder-extended
context, with its exact authored position in the ordered premise list. -/
def childJudgment (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A)
    (position : Fin (R.get occurrence.index).premises.length) : Judgment A :=
  interpretPremise A occurrence.valuation occurrence.close
    ((R.get occurrence.index).premises.get position)

/-- One constructor shape is an individual rule occurrence whose
interpreted conclusion is the given judgment. -/
abbrev Shape (A : BindingCloneAlgebra.Algebra.{u} S)
    (judgment : Judgment A) :=
  {occurrence : Instance R A // conclusionJudgment R A occurrence = judgment}

/-- The ordered conditional-rule polynomial. Its recursive positions are
precisely the authored premise indices, including duplicates. -/
def rules (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedPolynomial Unit (fun _ => Judgment A) where
  Shape _ judgment := Shape R A judgment
  Position shape := Fin (R.get shape.1.index).premises.length
  next shape position := childJudgment R A shape.1 position

/-- Transport a complete constructor occurrence along a binding-clone
interpretation while preserving its rule index and ambient context. -/
def mapInstance {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (occurrence : Instance R A) :
    Instance R B where
  index := occurrence.index
  ambient := occurrence.ambient
  valuation := mapValuation h occurrence.valuation
  close := fun sort var => h.raw.map (occurrence.close sort var)

theorem mapInstance_id (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A) :
    mapInstance R (FreeBindingClone.Hom.id A) occurrence = occurrence := by
  cases occurrence
  rfl

theorem mapInstance_comp
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    {C : BindingCloneAlgebra.Algebra.{w} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C)
    (occurrence : Instance R A) :
    mapInstance R (FreeBindingClone.Hom.comp first second) occurrence =
      mapInstance R second (mapInstance R first occurrence) := by
  cases occurrence
  rfl

/-- Every mapped conclusion has exactly the mapped pair of endpoints. -/
theorem mapInstance_conclusion
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    (occurrence : Instance R A) :
    conclusionJudgment R B (mapInstance R h occurrence) =
      mapJudgment h (conclusionJudgment R A occurrence) := by
  rcases occurrence with ⟨index, ambient, valuation, close⟩
  have sourceEq := interpretSchema_map h valuation
    (fun _ var => A.substitution.injectVar var) close
    (R.get index).conclusion.lhs
  have targetEq := interpretSchema_map h valuation
    (fun _ var => A.substitution.injectVar var) close
    (R.get index).conclusion.rhs
  have ambientEq :
      (fun sort var => h.raw.map (A.substitution.injectVar var) :
        BindingSubstitutionAlgebra.Environment S B.substitution.Carrier
          ambient ambient) =
      (fun _ var => B.substitution.injectVar var) := by
    funext sort var
    exact h.raw.map_variable var
  rw [ambientEq] at sourceEq targetEq
  simp only [conclusionJudgment, mapInstance, mapJudgment]
  rw [sourceEq, targetEq]

/-- Mapping a rule occurrence also maps every requested premise judgment,
including its binder-local extension and original list position. -/
theorem mapInstance_child
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    (occurrence : Instance R A)
    (position : Fin (R.get occurrence.index).premises.length) :
    childJudgment R B (mapInstance R h occurrence) position =
      mapJudgment h (childJudgment R A occurrence position) := by
  exact interpretPremise_map h occurrence.valuation occurrence.close
    ((R.get occurrence.index).premises.get position)

/-- Transport one constructor while preserving its exact conclusion
judgment and every ordered premise position. -/
def mapShape {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {judgment : Judgment A} (shape : Shape R A judgment) :
    Shape R B (mapJudgment h judgment) :=
  ⟨mapInstance R h shape.1,
    (mapInstance_conclusion R h shape.1).trans
      (congrArg (mapJudgment h) shape.2)⟩

theorem mapShape_id (A : BindingCloneAlgebra.Algebra.{u} S)
    {judgment : Judgment A} (shape : Shape R A judgment) :
    mapShape R (FreeBindingClone.Hom.id A) shape = shape := by
  apply Subtype.ext
  exact mapInstance_id R A shape.1

theorem mapShape_comp
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    {C : BindingCloneAlgebra.Algebra.{w} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C)
    {judgment : Judgment A} (shape : Shape R A judgment) :
    mapShape R (FreeBindingClone.Hom.comp first second) shape =
      mapShape R second (mapShape R first shape) := by
  apply Subtype.ext
  exact mapInstance_comp R first second shape.1

/-- A context-indexed presentation of the intrinsic conditional rules. -/
def presentation (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedRulePresentationCategory.Presentation Unit where
  Judgment _ := Judgment A
  rules := rules R A

/-- A binding-model map gives a cartesian translation of the conditional
rule presentation. Each premise position is preserved bijectively, while
its requested child judgment is mapped by `interpretPremise_map`. -/
def presentationMap
    {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) :
    presentation R A ⟶ presentation R B where
  judgment _ := mapJudgment h
  rules := {
    onShape := fun _ _ shape => mapShape R h shape
    onPosition := fun _ _ shape => Equiv.refl
      (Fin (R.get shape.1.index).premises.length)
    onNext := by
      intro _ _ shape position
      exact mapInstance_child R h shape.1 position
  }

theorem presentationMap_id (A : BindingCloneAlgebra.Algebra.{u} S) :
    presentationMap R (FreeBindingClone.Hom.id A) =
      𝟙 (presentation R A) := by
  rfl

theorem presentationMap_comp
    {A B C : BindingCloneAlgebra.Algebra.{u} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C) :
    presentationMap R (FreeBindingClone.Hom.comp first second) =
      presentationMap R first ≫ presentationMap R second := by
  rfl

/-- The same authored conditional-rule presentation varies functorially
over all semantic models satisfying a selected equation list. -/
def presentationFunctor (E : List (EqAxiom S M)) :
    FreeBindingEquationModel.Model.{0} E ⥤
      IndexedRulePresentationCategory.Presentation Unit where
  obj X := presentation R X.algebra
  map h := presentationMap R h
  map_id X := presentationMap_id R X.algebra
  map_comp first second := presentationMap_comp R first second

/-- A semantic equation model equipped with an action for every intrinsic
scoped conditional constructor and all its recursive child evidence. -/
abbrev Model (E : List (EqAxiom S M)) :=
  IndexedOperationalModelsOver.Model (presentationFunctor R E)

/-- Freely generated proof-relevant conditional derivations over the
authored binding/equation quotient. -/
noncomputable def presented (E : List (EqAxiom S M)) : Model R E :=
  IndexedOperationalModelsOver.free (presentationFunctor R E)
    (FreeBindingEquationModel.presented E)

/-- The conditional-rule interpretation is left adjoint to forgetting
individual proof-relevant firing trees. -/
noncomputable def freeAdjunction (E : List (EqAxiom S M)) :
    IndexedOperationalModelsOver.freeFunctor (presentationFunctor R E) ⊣
      IndexedOperationalModelsOver.forget (presentationFunctor R E) :=
  IndexedOperationalModelsOver.freeAdjunction (presentationFunctor R E)

/-- The free intrinsic binding/equation/conditional-rule model is initial
for its exact declared structure. -/
noncomputable def presentedIsInitial (E : List (EqAxiom S M)) :
    IsInitial (presented R E) :=
  IndexedOperationalModelsOver.freeIsInitial (presentationFunctor R E)
    (FreeBindingEquationModel.presentedIsInitial E)

#print axioms presentationMap
#print axioms presentationFunctor
#print axioms presentedIsInitial

#print axioms mapInstance_conclusion
#print axioms mapInstance_child

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
