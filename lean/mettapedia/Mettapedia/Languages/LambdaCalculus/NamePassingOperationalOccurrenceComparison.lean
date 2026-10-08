import Mettapedia.Languages.LambdaCalculus.NamePassingOperationalDiagram

/-!
# Complete correspondence with the authored active edge family

The independent beta/fetch occurrence trees correspond bijectively to the
complete dependent total of authored active edges. Both endpoints and every
active position are retained. The correspondence makes no static equation
quotient or observational identification of occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.OperationalDiagram

open Mettapedia.OSLF.Binding Presentation

abbrev TotalOccurrence (Γ : Ctx signature) :=
  Σ first : Program Γ, Σ last : Program Γ, ActiveEdge first last

def Event.totalOccurrence {Γ : Ctx signature} (event : Event Γ) : TotalOccurrence Γ :=
  ⟨event.source, event.target, event.occurrence⟩

theorem Event.total_fromOccurrence {Γ : Ctx signature} {first last : Program Γ}
    (supplied : ActiveEdge first last) :
    (Event.fromOccurrence supplied).totalOccurrence = ⟨first, last, supplied⟩ := by
  induction supplied with
  | root root => cases root <;> rfl
  | application argument before ih =>
      exact congrArg (fun input : TotalOccurrence _ =>
        (⟨Presentation.application input.1 argument, Presentation.application input.2.1 argument,
          ActiveEdge.application argument input.2.2⟩ : TotalOccurrence _)) ih
  | definition value before ih =>
      exact congrArg (fun input : TotalOccurrence _ =>
        (⟨Presentation.definition value input.1, Presentation.definition value input.2.1,
          ActiveEdge.definition value input.2.2⟩ : TotalOccurrence _)) ih
  | carrier name value before ih =>
      exact congrArg (fun input : TotalOccurrence _ =>
        (⟨Presentation.carrier name value input.1, Presentation.carrier name value input.2.1,
          ActiveEdge.carrier name value input.2.2⟩ : TotalOccurrence _)) ih

def occurrenceEquiv (Γ : Ctx signature) : Event Γ ≃ TotalOccurrence Γ where
  toFun := Event.totalOccurrence
  invFun := fun supplied => Event.fromOccurrence supplied.2.2
  left_inv := Event.from_occurrence
  right_inv := fun supplied => Event.total_fromOccurrence supplied.2.2

theorem total_source {Γ : Ctx signature} (event : Event Γ) :
    (occurrenceEquiv Γ event).1 = event.source := rfl

theorem total_target {Γ : Ctx signature} (event : Event Γ) :
    (occurrenceEquiv Γ event).2.1 = event.target := rfl

end Mettapedia.Languages.LambdaCalculus.NamePassing.OperationalDiagram
