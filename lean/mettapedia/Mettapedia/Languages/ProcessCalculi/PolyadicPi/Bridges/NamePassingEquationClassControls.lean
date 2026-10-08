import Mettapedia.Languages.LambdaCalculus.NamePassingAuthoredInternalCategory
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEquationClassOperationalFunctor
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalControls

/-!
# Static quotient, real edge and retained-origin controls

A scope equation identifies the endpoints of two distinct authored active
positions. Both positions compile to actual COMM occurrences, with distinct
reaction trees, while their compiled endpoint classes agree. The binding
rule opens only its body premise, and the classified extension contains a
real beta there. Static equations preserve node counts and do not adopt beta
as equality. Suspended abstraction is outside the active edge profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEquationClassControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open NamePassingOpenInterpretation NamePassingOperationalEvents

abbrev Γ := NamePassingOpenInterpretation.Controls.sourceScope
abbrev Δ := NamePassingOpenInterpretation.Controls.targetScope

def applicationPosition : SourceEvent Γ :=
  .application NamePassingOpenInterpretation.Controls.referenceName
    (.carrier NamePassingOpenInterpretation.Controls.referenceName NamePassingOpenInterpretation.Controls.firstHole
      NamePassingOperationalControls.beta)

def carrierPosition : SourceEvent Γ :=
  .carrier NamePassingOpenInterpretation.Controls.referenceName NamePassingOpenInterpretation.Controls.firstHole
    (.application NamePassingOpenInterpretation.Controls.referenceName NamePassingOperationalControls.beta)

theorem independent_source_equation :
    NamePassing.Presentation.StaticEq applicationPosition.source carrierPosition.source :=
  .appCarrier _ _ _ _

theorem independent_target_equation :
    NamePassing.Presentation.StaticEq applicationPosition.target carrierPosition.target :=
  .appCarrier _ _ _ _

theorem same_complete_class_endpoints :
    (Quotient.mk _ applicationPosition.source : NamePassingEquationClassOperationalFunctor.SourceClass Γ) =
      Quotient.mk _ carrierPosition.source ∧
    (Quotient.mk _ applicationPosition.target : NamePassingEquationClassOperationalFunctor.SourceClass Γ) =
      Quotient.mk _ carrierPosition.target :=
  ⟨Quotient.sound (NamePassing.AuthoredEquations.staticEq_complete independent_source_equation),
    Quotient.sound (NamePassing.AuthoredEquations.staticEq_complete independent_target_equation)⟩

theorem actual_positions_distinct : applicationPosition ≠ carrierPosition := by
  intro same
  cases same

theorem both_positions_are_actual :
    NamePassing.AuthoredClassified.StepModulo applicationPosition.source applicationPosition.target ∧
      NamePassing.AuthoredClassified.StepModulo carrierPosition.source carrierPosition.target :=
  ⟨NamePassing.AuthoredClassified.active_toModulo applicationPosition.occurrence,
    NamePassing.AuthoredClassified.active_toModulo carrierPosition.occurrence⟩

theorem same_compiled_complete_class_endpoints :
    NamePassingEquationClassOperationalFunctor.compileClass NamePassingOperationalControls.inputs
      (Quotient.mk _ applicationPosition.source) =
      NamePassingEquationClassOperationalFunctor.compileClass NamePassingOperationalControls.inputs
        (Quotient.mk _ carrierPosition.source) ∧
    NamePassingEquationClassOperationalFunctor.compileClass NamePassingOperationalControls.inputs
      (Quotient.mk _ applicationPosition.target) =
      NamePassingEquationClassOperationalFunctor.compileClass NamePassingOperationalControls.inputs
        (Quotient.mk _ carrierPosition.target) :=
  ⟨congrArg (NamePassingEquationClassOperationalFunctor.compileClass NamePassingOperationalControls.inputs)
      same_complete_class_endpoints.1,
    congrArg (NamePassingEquationClassOperationalFunctor.compileClass NamePassingOperationalControls.inputs)
      same_complete_class_endpoints.2⟩

def applicationCommunication : TargetEvent Δ :=
  mapEvent applicationPosition NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn

def carrierCommunication : TargetEvent Δ :=
  mapEvent carrierPosition NamePassingOpenInterpretation.Controls.environment NamePassingOpenInterpretation.Controls.secondReturn

theorem compiled_reaction_positions_distinct :
    applicationCommunication.reaction ≠ carrierCommunication.reaction := by
  intro same
  cases same

theorem both_compiled_events_are_public_steps :
    StepModulo applicationCommunication.source applicationCommunication.target ∧
      StepModulo carrierCommunication.source carrierCommunication.target :=
  ⟨applicationCommunication.sound, carrierCommunication.sound⟩

theorem no_class_endpoint_occurrence_decoder :
    ¬ ∃ decode : NamePassingEquationClassOperationalFunctor.SourceClass Γ ×
        NamePassingEquationClassOperationalFunctor.SourceClass Γ → SourceEvent Γ,
      ∀ event, decode (Quotient.mk _ event.source, Quotient.mk _ event.target) = event := by
  rintro ⟨decode, correct⟩
  have same : (Quotient.mk _ applicationPosition.source,
      Quotient.mk _ applicationPosition.target) =
      (Quotient.mk _ carrierPosition.source, Quotient.mk _ carrierPosition.target) :=
    Prod.ext same_complete_class_endpoints.1 same_complete_class_endpoints.2
  exact actual_positions_distinct
    ((correct applicationPosition).symm.trans ((congrArg decode same).trans (correct carrierPosition)))

def boundReference : NamePassing.Presentation.Program (.nm :: .nm :: Γ) :=
  NamePassing.Presentation.reference (.var .zero)

def boundBeta : SourceEvent (.nm :: Γ) := .beta boundReference (.var .zero)

def definitionOccurrence :
    IntrinsicScopedLocalPolynomial.Instance NamePassing.AuthoredOperationalProfile.rules
      NamePassing.AuthoredOperationalProfile.raw :=
  NamePassing.AuthoredOperationalProfile.definitionOccurrence NamePassingOpenInterpretation.Controls.firstHole
    boundBeta.source boundBeta.target

theorem complete_binder_premise_readout
    (position : Fin (NamePassing.AuthoredOperationalProfile.rules.get definitionOccurrence.index).2.premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment NamePassing.AuthoredOperationalProfile.rules
      NamePassing.AuthoredOperationalProfile.raw definitionOccurrence position =
      (⟨NamePassing.Presentation.Srt.nm :: Γ, NamePassing.Presentation.Srt.tm,
        NamePassing.Presentation.application (NamePassing.Presentation.abstraction boundReference) (.var .zero),
        NamePassing.Presentation.reference (.var .zero)⟩ :
          AuthoredPositionedRulePolynomial.Judgment NamePassing.AuthoredOperationalProfile.raw) := by
  exact NamePassing.AuthoredOperationalProfile.definition_child _ _ _ position

def definedBeta : SourceEvent Γ := .definition NamePassingOpenInterpretation.Controls.firstHole boundBeta

theorem stored_value_stays_outside_binder :
    IntrinsicScopedLocalPolynomial.conclusionJudgment NamePassing.AuthoredOperationalProfile.rules
      NamePassing.AuthoredOperationalProfile.raw definitionOccurrence =
      (⟨Γ, NamePassing.Presentation.Srt.tm,
        NamePassing.Presentation.definition NamePassingOpenInterpretation.Controls.firstHole boundBeta.source,
        NamePassing.Presentation.definition NamePassingOpenInterpretation.Controls.firstHole boundBeta.target⟩ :
          AuthoredPositionedRulePolynomial.Judgment NamePassing.AuthoredOperationalProfile.raw) :=
  NamePassing.AuthoredOperationalProfile.definition_conclusion _ _ _

theorem actual_classified_binder_firing :
    IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction NamePassing.AuthoredOperationalProfile.rules
      NamePassing.AuthoredEquations.equations definedBeta.source definedBeta.target :=
  (NamePassing.AuthoredClassified.extension_iff_stepModulo _ _).mpr
    (NamePassing.AuthoredClassified.active_toModulo definedBeta.occurrence)

private theorem static_size {Θ : Ctx NamePassing.Presentation.signature}
    {first last : NamePassing.Presentation.Program Θ}
    (same : NamePassing.Presentation.StaticEq first last) : termSize first = termSize last := by
  induction same with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ before after => exact before.trans after
  | appDefinition value body argument =>
      simp only [NamePassing.Presentation.application, NamePassing.Presentation.definition,
        termSize, argsSize, Mettapedia.OSLF.Binding.weaken, termSize_rename]
      omega
  | appCarrier name value body argument =>
      simp only [NamePassing.Presentation.application, NamePassing.Presentation.carrier, termSize, argsSize]
      omega
  | abstraction _ ih =>
      simpa only [NamePassing.Presentation.abstraction, termSize, argsSize] using congrArg (fun n => n + 0 + 1) ih
  | application argument _ ih =>
      simpa only [NamePassing.Presentation.application, termSize, argsSize] using
        congrArg (fun n => n + (termSize argument + 0) + 1) ih
  | definition _ _ values bodies =>
      simp only [NamePassing.Presentation.definition, termSize, argsSize]
      rw [values, bodies]
  | carrier name _ _ values bodies =>
      simp only [NamePassing.Presentation.carrier, termSize, argsSize]
      rw [values, bodies]

/-- Operational beta is a real edge, and is not an extra static equation. -/
theorem beta_not_static_equality :
    ¬ NamePassing.Presentation.StaticEq boundBeta.source boundBeta.target := by
  intro same
  have sizes := static_size same
  change 5 = 2 at sizes
  omega

theorem suspended_abstraction_has_no_active_edge
    (last : NamePassing.Presentation.Program Γ) :
    ¬ Nonempty (NamePassing.Presentation.ActiveEdge
      (NamePassing.Presentation.abstraction NamePassingOperationalControls.boundReference) last) := by
  rintro ⟨edge⟩
  cases edge with
  | root root => cases root

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEquationClassControls
