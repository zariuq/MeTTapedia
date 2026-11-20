import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.LiveObservations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

/-! # Live views erase dead slots without erasing knowledge or duplicate resources -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.LiveObservations.Controls

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationMachine (RowTerms)
open ApplicationSyntax (symbol)

def deadOne : SchematicRows.State RowTerms Nat := ⟨PUnit.unit, [], ∅, fun _ => .shared (symbol 20)⟩
def deadTwo : SchematicRows.State RowTerms Nat := ⟨PUnit.unit, [], ∅, fun _ => .shared (symbol 21)⟩

def rawSymbol {a : PUnit} : Row RowTerms a → Option Nat
  | .shared (.const (.sym name)) => some name
  | _ => none

theorem dead_states_are_distinct : deadOne ≠ deadTwo := by
  intro same
  have impossible := congrArg (fun state : SchematicRows.State RowTerms Nat => rawSymbol (state.label 0)) same
  cases impossible

theorem dead_slots_not_observed : observe deadOne = observe deadTwo := by
  exact observe_eq (Tm := RowTerms) (O := Nat) PUnit.unit [] [] ∅ ∅ (fun _ => .shared (symbol 20)) (fun _ => .shared (symbol 21))
    rfl rfl (fun o member => False.elim (Finset.notMem_empty o member))

def oneOccurrence : SchematicRows.State RowTerms Nat := ⟨PUnit.unit, [], {0}, fun _ => .shared (symbol 20)⟩
def twoOccurrences : SchematicRows.State RowTerms Nat := ⟨PUnit.unit, [], {0, 1}, fun _ => .shared (symbol 20)⟩

theorem duplicate_payloads_keep_occurrences : observe oneOccurrence ≠ observe twoOccurrences := by
  intro same
  have counts := congrArg occurrenceCount same
  have impossible : 1 = (2 : Nat) := counts
  cases impossible

def withKnowledge : SchematicRows.State RowTerms Nat :=
  ⟨PUnit.unit, [(symbol 20, symbol 21)], {0}, fun _ => .shared (symbol 20)⟩

def knowledgeLength (view : View RowTerms Nat) : Nat := view.2.knowledge.length

theorem knowledge_not_erased : observe oneOccurrence ≠ observe withKnowledge := by
  intro same
  have lengths := congrArg knowledgeLength same
  have impossible : 0 = (1 : Nat) := lengths
  cases impossible

#print axioms dead_states_are_distinct
#print axioms dead_slots_not_observed
#print axioms duplicate_payloads_keep_occurrences
#print axioms knowledge_not_erased

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.LiveObservations.Controls
