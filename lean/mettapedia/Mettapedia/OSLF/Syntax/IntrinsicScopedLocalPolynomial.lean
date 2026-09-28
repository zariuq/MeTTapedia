import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels

/-!
# Conditional rule families with local metavariable telescopes

Each declaration carries its own metavariable telescope. Selecting a rule
therefore selects the type of its valuation; an occurrence has no assignments
for declarations belonging only to other rules. The ordered list index is
retained even when two declarations have identical conclusions.
Use of every declared metavariable and recovery from a source are separate
properties of the individual authored rules.

The selected-rule adapter uses the existing intrinsic rule interpretation.
The resulting heterogeneous family uses the existing indexed polynomial,
cartesian presentation maps, and free firing trees.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open CategoryTheory CategoryTheory.Limits

universe u v w

/-- An authored rule together with its own declared metavariable telescope. -/
abbrev LocalRule (S : Signature) :=
  Σ M : List (MetaArity S), IntrinsicScopedConditionalPolynomial.Rule S M

variable {S : Signature} (R : List (LocalRule S))

/-- A selected declaration determines the valuation's domain. -/
structure Instance (A : BindingCloneAlgebra.Algebra.{u} S) where
  index : Fin R.length
  ambient : Ctx S
  valuation : Valuation (M := (R.get index).1) A ambient
  close : Environment S A.substitution.Carrier
    (R.get index).2.conclusion.ctx ambient

/-- View a local occurrence in the existing singleton-rule semantics. -/
def Instance.toSingleton {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : Instance R A) :
    IntrinsicScopedConditionalPolynomial.Instance [(R.get occurrence.index).2] A where
  index := 0
  ambient := occurrence.ambient
  valuation := occurrence.valuation
  close := occurrence.close

/-- Insert a singleton occurrence at its selected declaration address. -/
def Instance.ofSingleton {A : BindingCloneAlgebra.Algebra.{u} S}
    (index : Fin R.length)
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance [(R.get index).2] A) :
    Instance R A where
  index := index
  ambient := occurrence.ambient
  valuation := occurrence.valuation
  close := by
    have zero : occurrence.index = 0 := Fin.eq_zero occurrence.index
    simpa only [zero, List.get_cons_zero] using occurrence.close

@[simp] theorem Instance.ofSingleton_toSingleton
    {A : BindingCloneAlgebra.Algebra.{u} S} (occurrence : Instance R A) :
    Instance.ofSingleton R occurrence.index (occurrence.toSingleton R) = occurrence := by
  cases occurrence
  rfl

/-- Interpret the conclusion using the existing singleton-rule adapter. -/
def conclusionJudgment (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A) : Judgment A :=
  IntrinsicScopedConditionalPolynomial.conclusionJudgment
    [(R.get occurrence.index).2] A (occurrence.toSingleton R)

/-- Each premise retains its own authored binder context and list address. -/
def childJudgment (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A)
    (position : Fin (R.get occurrence.index).2.premises.length) : Judgment A :=
  IntrinsicScopedConditionalPolynomial.childJudgment
    [(R.get occurrence.index).2] A (occurrence.toSingleton R) position

abbrev Shape (A : BindingCloneAlgebra.Algebra.{u} S) (judgment : Judgment A) :=
  {occurrence : Instance R A // conclusionJudgment R A occurrence = judgment}

/-- The proof-relevant rule polynomial, with heterogeneous constructor data. -/
def rules (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedPolynomial Unit (fun _ => Judgment A) where
  Shape _ judgment := Shape R A judgment
  Position shape := Fin (R.get shape.1.index).2.premises.length
  next shape position := childJudgment R A shape.1 position

def mapInstance {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (occurrence : Instance R A) : Instance R B where
  index := occurrence.index
  ambient := occurrence.ambient
  valuation := mapValuation h occurrence.valuation
  close := fun sort var => h.raw.map (occurrence.close sort var)

@[simp] theorem toSingleton_mapInstance
    {A : BindingCloneAlgebra.Algebra.{u} S} {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (occurrence : Instance R A) :
    (mapInstance R h occurrence).toSingleton R =
      IntrinsicScopedConditionalPolynomial.mapInstance
        [(R.get occurrence.index).2] h (occurrence.toSingleton R) := rfl

theorem mapInstance_id (A : BindingCloneAlgebra.Algebra.{u} S)
    (occurrence : Instance R A) :
    mapInstance R (FreeBindingClone.Hom.id A) occurrence = occurrence := by
  cases occurrence
  rfl

theorem mapInstance_comp
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S} {C : BindingCloneAlgebra.Algebra.{w} S}
    (first : FreeBindingClone.Hom A B) (second : FreeBindingClone.Hom B C)
    (occurrence : Instance R A) :
    mapInstance R (FreeBindingClone.Hom.comp first second) occurrence =
      mapInstance R second (mapInstance R first occurrence) := by
  cases occurrence
  rfl

theorem mapInstance_conclusion
    {A : BindingCloneAlgebra.Algebra.{u} S} {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (occurrence : Instance R A) :
    conclusionJudgment R B (mapInstance R h occurrence) =
      mapJudgment h (conclusionJudgment R A occurrence) :=
  IntrinsicScopedConditionalPolynomial.mapInstance_conclusion
    [(R.get occurrence.index).2] h (occurrence.toSingleton R)

theorem mapInstance_child
    {A : BindingCloneAlgebra.Algebra.{u} S} {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (occurrence : Instance R A)
    (position : Fin (R.get occurrence.index).2.premises.length) :
    childJudgment R B (mapInstance R h occurrence) position =
      mapJudgment h (childJudgment R A occurrence position) :=
  IntrinsicScopedConditionalPolynomial.mapInstance_child
    [(R.get occurrence.index).2] h (occurrence.toSingleton R) position

def mapShape {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) {j : Judgment A} (shape : Shape R A j) :
    Shape R B (mapJudgment h j) :=
  ⟨mapInstance R h shape.1,
    (mapInstance_conclusion R h shape.1).trans (congrArg (mapJudgment h) shape.2)⟩

def presentation (A : BindingCloneAlgebra.Algebra.{u} S) :
    IndexedRulePresentationCategory.Presentation Unit where
  Judgment _ := Judgment A
  rules := rules R A

/-- A base interpretation preserves the selected rule and every premise. -/
def presentationMap {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) : presentation R A ⟶ presentation R B where
  judgment _ := mapJudgment h
  rules := {
    onShape := fun _ _ shape => mapShape R h shape
    onPosition := fun _ _ shape => Equiv.refl
      (Fin (R.get shape.1.index).2.premises.length)
    onNext := fun _ _ shape position => mapInstance_child R h shape.1 position }

theorem presentationMap_id (A : BindingCloneAlgebra.Algebra.{u} S) :
    presentationMap R (FreeBindingClone.Hom.id A) = 𝟙 (presentation R A) := rfl

theorem presentationMap_comp {A B C : BindingCloneAlgebra.Algebra.{u} S}
    (first : FreeBindingClone.Hom A B) (second : FreeBindingClone.Hom B C) :
    presentationMap R (FreeBindingClone.Hom.comp first second) =
      presentationMap R first ≫ presentationMap R second := rfl

/-- Rule-local evidence varies over any independently chosen equation telescope. -/
def presentationFunctor {M : List (MetaArity S)} (E : List (EqAxiom S M)) :
    FreeBindingEquationModel.Model.{0} E ⥤
      IndexedRulePresentationCategory.Presentation Unit where
  obj X := presentation R X.algebra
  map h := presentationMap R h
  map_id X := presentationMap_id R X.algebra
  map_comp first second := presentationMap_comp R first second

abbrev Tree (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A) :=
  IndexedPolynomial.Fix (rules R A) () j

/-- Interpret every constructor and child of a local-rule firing history. -/
noncomputable def mapTree {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (j : Judgment A) :
    Tree R A j → Tree R B (mapJudgment h j) :=
  (presentationMap R h).rules.mapFix () j

theorem mapTree_id (A : BindingCloneAlgebra.Algebra.{u} S)
    (j : Judgment A) (tree : Tree R A j) :
    mapTree R (FreeBindingClone.Hom.id A) j tree = tree :=
  Hom.mapFix_id (rules R A) () j tree

theorem mapTree_comp {A B C : BindingCloneAlgebra.Algebra.{u} S}
    (first : FreeBindingClone.Hom A B) (second : FreeBindingClone.Hom B C)
    (j : Judgment A) (tree : Tree R A j) :
    mapTree R (FreeBindingClone.Hom.comp first second) j tree =
      mapTree R second (mapJudgment first j) (mapTree R first j tree) :=
  Hom.mapFix_comp (presentationMap R first).rules
    (presentationMap R second).rules () j tree

abbrev Model {M : List (MetaArity S)} (E : List (EqAxiom S M)) :=
  IndexedOperationalModelsOver.Model (presentationFunctor R E)

noncomputable def presented {M : List (MetaArity S)} (E : List (EqAxiom S M)) :
    Model R E :=
  IndexedOperationalModelsOver.free (presentationFunctor R E)
    (FreeBindingEquationModel.presented E)

noncomputable def presentedIsInitial {M : List (MetaArity S)}
    (E : List (EqAxiom S M)) : IsInitial (presented R E) :=
  IndexedOperationalModelsOver.freeIsInitial (presentationFunctor R E)
    (FreeBindingEquationModel.presentedIsInitial E)

#print axioms mapInstance_conclusion
#print axioms mapInstance_child
#print axioms mapTree_comp
#print axioms presentedIsInitial

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
