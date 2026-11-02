import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority

/-! # Composition and final consistency of actual schema-authority runs -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority.System

universe uT uS uO uN uI uR uX
variable {T : Type uT} {S : Type uS} {O : Type uO} {N : Type uN}
    {I : Type uI} {R : Type uR} {X : Type uX} [DecidableEq O]
    {location : O → N} {protectedOccurrence : O → Prop}
    {system : SchemaPublicationAuthority.System R N I O location protectedOccurrence}
    {activate : R → X → Option (RuleInstance T)} {action : SubstitutionAction T S} {label : O → T}

theorem Run.append {before middle after : Configuration T O} {first second : List I}
    (left : system.Run activate action label before first middle)
    (right : system.Run activate action label middle second after) :
    system.Run activate action label before (first ++ second) after := by
  induction left with
  | nil => exact right
  | cons stepped rest earlier => exact .cons stepped (earlier right)

theorem step_consistent {before after : Configuration T O} {actor : I}
    (stepped : system.Step activate action label actor before after) : action.Consistent after.equations := by
  obtain ⟨schema, installed, inputs, rule, computed, picked, qualified, formed, rfl⟩ := stepped
  exact qualified.consistent

theorem Run.consistent {before after : Configuration T O} {schedule : List I}
    (run : system.Run activate action label before schedule after) (background : action.Consistent before.equations) :
    action.Consistent after.equations := by
  induction run with
  | nil => exact background
  | cons stepped rest earlier => exact earlier (step_consistent stepped)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority.System
