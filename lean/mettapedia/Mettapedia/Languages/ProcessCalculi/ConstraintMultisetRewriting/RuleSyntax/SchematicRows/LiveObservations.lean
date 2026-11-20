import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.State

/-!
# A typed view of live rows, retaining knowledge and occurrence identity

Labels can be inspected only with evidence of physical presence. The view
keeps the exact frame, knowledge and every live row, including intensional
schema code and captured-variable sharing. It forgets only missing label slots;
it does not quotient equal payloads at different occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.LiveObservations

universe uO uT uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {O : Type uOcc}

structure At (Tm : Obj → Type uT) (O : Type uOcc) (a : Obj) where
  knowledge : EquationStore (Tm a)
  present : Finset O
  label : (o : O) → o ∈ present → Row Tm a

abbrev View (Tm : Obj → Type uT) (O : Type uOcc) := (a : Obj) × At Tm O a

def observe (source : SchematicRows.State Tm O) : View Tm O :=
  ⟨source.frame, ⟨source.knowledge, source.present, fun o _ => source.label o⟩⟩

theorem observe_eq (a : Obj) (firstKnowledge secondKnowledge : EquationStore (Tm a))
    (firstPresent secondPresent : Finset O) (firstLabels secondLabels : O → Row Tm a)
    (knowledge : firstKnowledge = secondKnowledge) (present : firstPresent = secondPresent)
    (labels : ∀ o ∈ firstPresent, firstLabels o = secondLabels o) :
    observe (⟨a, firstKnowledge, firstPresent, firstLabels⟩ : SchematicRows.State Tm O) =
      observe (⟨a, secondKnowledge, secondPresent, secondLabels⟩ : SchematicRows.State Tm O) := by
  subst secondKnowledge secondPresent
  have same : (fun o (_ : o ∈ firstPresent) => firstLabels o) =
      (fun o (_ : o ∈ firstPresent) => secondLabels o) :=
    funext fun o => funext fun member => labels o member
  exact congrArg (fun label => (⟨a, ⟨firstKnowledge, firstPresent, label⟩⟩ : View Tm O)) same

def occurrenceCount (view : View Tm O) : Nat := view.2.present.card

#print axioms observe_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.LiveObservations
