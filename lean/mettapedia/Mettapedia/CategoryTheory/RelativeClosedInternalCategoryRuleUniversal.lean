import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryRuleInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorExtension

/-!
# Coherent classification of actual operational rule declarations

An independent candidate retains primitive base/object comparisons and
separate local readings of old operators and fresh firing functions. These
readings earn all endpoint laws, the entire generated interpretation and
its unique admitted natural comparison. The whole original interpretation
is recovered through the comparison. No operational equation or whole
generated-arrow comparison is supplied as a model field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.RuleUniversal

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation

universe k w

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type k} [Category.{k} D] {symbols : Symbols.{k}}
variable {original : Signature (C := D) (symbols := symbols)}
variable (categoryMap : SignatureMap (Presentation.signature vertex) original)
variable {Index : Type k} (declarations : Index → RulePresentation.Declaration vertex categoryMap)
variable (formed : HeaderFormation original)
variable {E : Type w} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable (meanings : Assignment D symbols E) (realized : Realization original meanings)
variable (firing : ∀ origin, RuleInterpretation.premise vertex categoryMap declarations meanings realized origin ⟶
  RuleInterpretation.edges vertex categoryMap meanings realized)
variable (candidate : Object (RulePresentation.signature vertex categoryMap declarations) ⥤ E)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]
variable (images : AtomicPresentation.PrimitiveImages candidate
  (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing))

abbrev extracted := FunctorNormalization.assignment
  (CoherentExtension.presented candidate
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) images)
      (RulePresentation.headers vertex categoryMap declarations formed)

structure LocalReadings : Prop where
  original (origin : symbols.ArrowName) :
    (extracted vertex categoryMap declarations formed meanings realized firing candidate images).arrow (Sum.inl origin) =
      meanings.arrow origin
  firing (origin : Index) :
    (extracted vertex categoryMap declarations formed meanings realized firing candidate images).arrow (Sum.inr origin) =
      RuleInterpretation.arrowValue vertex categoryMap declarations meanings realized firing origin

variable (readings : LocalReadings vertex categoryMap declarations formed meanings realized firing candidate images)

include readings in
theorem all_arrow_readings : CoherentExtension.ArrowImages candidate
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) images
      (RulePresentation.headers vertex categoryMap declarations formed) where
  arrow origin := by
    cases origin with
    | inl origin => exact readings.original origin
    | inr origin => exact readings.firing origin

include readings in
theorem locally_realized : Realization (RulePresentation.signature vertex categoryMap declarations)
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) := by
  have reconstructed := FunctorNormalization.reconstruction_realization
    (CoherentExtension.presented candidate
      (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) images)
        (RulePresentation.headers vertex categoryMap declarations formed)
  exact (CoherentExtension.assignment_equal candidate
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) images
      (RulePresentation.headers vertex categoryMap declarations formed)
        (all_arrow_readings vertex categoryMap declarations formed meanings realized firing candidate images readings)) ▸ reconstructed

include readings in
theorem endpointLaws : RuleInterpretation.LocalLaws vertex categoryMap declarations meanings realized firing :=
  (RuleInterpretation.realization_iff vertex categoryMap declarations meanings realized firing).mp
    (locally_realized vertex categoryMap declarations formed meanings realized firing candidate images readings)

def interpreted := RuleInterpretation.functor vertex categoryMap declarations meanings realized firing
  (endpointLaws vertex categoryMap declarations formed meanings realized firing candidate images readings)

def comparison : candidate ≅ interpreted vertex categoryMap declarations formed meanings realized firing candidate images readings :=
  CoherentExtension.comparison candidate
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) images
      (RulePresentation.headers vertex categoryMap declarations formed)
        (all_arrow_readings vertex categoryMap declarations formed meanings realized firing candidate images readings)
          (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing
            (endpointLaws vertex categoryMap declarations formed meanings realized firing candidate images readings))

abbrev CellAdmission := CoherentExtension.CellAdmission candidate
  (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) images
    (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing
      (endpointLaws vertex categoryMap declarations formed meanings realized firing candidate images readings))

theorem comparison_admitted : CellAdmission vertex categoryMap declarations formed meanings realized firing candidate images readings
    (comparison vertex categoryMap declarations formed meanings realized firing candidate images readings).hom :=
  CoherentExtension.comparison_admitted candidate
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) images
      (RulePresentation.headers vertex categoryMap declarations formed)
        (all_arrow_readings vertex categoryMap declarations formed meanings realized firing candidate images readings)
          (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing
            (endpointLaws vertex categoryMap declarations formed meanings realized firing candidate images readings))

theorem admitted_cell_unique
    (cell : candidate ⟶ interpreted vertex categoryMap declarations formed meanings realized firing candidate images readings)
    (components : CellAdmission vertex categoryMap declarations formed meanings realized firing candidate images readings cell) :
    cell = (comparison vertex categoryMap declarations formed meanings realized firing candidate images readings).hom :=
  CoherentExtension.admitted_cell_unique candidate
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) images
      (RulePresentation.headers vertex categoryMap declarations formed)
        (all_arrow_readings vertex categoryMap declarations formed meanings realized firing candidate images readings)
          (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing
            (endpointLaws vertex categoryMap declarations formed meanings realized firing candidate images readings)) cell components

@[instance_reducible] def admittedIsoUnique :
    Unique {iso : candidate ≅ interpreted vertex categoryMap declarations formed meanings realized firing candidate images readings //
      CellAdmission vertex categoryMap declarations formed meanings realized firing candidate images readings iso.hom} :=
  CoherentExtension.admittedIsoUnique candidate
    (RuleInterpretation.assignment vertex categoryMap declarations meanings realized firing) images
      (RuleInterpretation.realization vertex categoryMap declarations meanings realized firing
        (endpointLaws vertex categoryMap declarations formed meanings realized firing candidate images readings))
          (RulePresentation.headers vertex categoryMap declarations formed)
            (all_arrow_readings vertex categoryMap declarations formed meanings realized firing candidate images readings)

def originalComparison : (RulePresentation.arrowInclusion vertex categoryMap declarations).functor ⋙
    (RulePresentation.equationInclusion vertex categoryMap declarations).functor ⋙ candidate ≅
      RuleInterpretation.originalFunctor meanings realized :=
  Functor.isoWhiskerLeft (RulePresentation.arrowInclusion vertex categoryMap declarations).functor
    (Functor.isoWhiskerLeft (RulePresentation.equationInclusion vertex categoryMap declarations).functor
      (comparison vertex categoryMap declarations formed meanings realized firing candidate images readings)) ≪≫
    eqToIso (RuleInterpretation.complete_original_restriction vertex categoryMap declarations meanings realized firing
      (endpointLaws vertex categoryMap declarations formed meanings realized firing candidate images readings))

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.RuleUniversal
