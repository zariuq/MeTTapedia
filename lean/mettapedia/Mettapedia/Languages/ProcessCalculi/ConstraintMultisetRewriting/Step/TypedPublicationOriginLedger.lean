import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRunTransport
import Mathlib.Data.List.Forall2

/-!
# Per-event source correspondence in the retained origin ledger

Every paired target event is the actual transported original application at
its current state comparison. The source candidate retains its rule-table
index and its source permission proof. These facts strengthen mere equality
of word lengths. They do not supply a permission invariant for an arbitrary
new target programme.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransport

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

def RelatedEvents (source target : Σ state : State rules O, Application levels O state) : Prop :=
  ∃ comparison : PlainIso levels source.1 target.1, target.2 = application comparison source.2

theorem move_word_relation {source target : State rules O} (comparison : PlainIso levels source target)
    (run : (realizationStep levels O).Run source) :
    List.Forall₂ RelatedEvents run.word (move comparison run).word := by
  induction run generalizing target with
  | nil state => exact .nil
  | cons candidate accepted rest ih =>
      exact .cons ⟨comparison, rfl⟩ (ih (after comparison candidate accepted))

variable {program : Program levels O}
  {permission : {state : State rules O} → Candidate program state → Prop}

theorem execution_permissions {state : State rules O} (execution : program.Execution permission state) :
    ∀ event ∈ execution.word, permission event.2 := by
  induction execution with
  | nil state => intro event member; exact False.elim (List.not_mem_nil member)
  | cons candidate admitted allowed rest ih =>
      intro event member
      rcases List.mem_cons.mp member with same | later
      · subst event
        exact allowed
      · exact ih event later

theorem ledger_correspondence {source target : State rules O} (comparison : PlainIso levels source target)
    (execution : program.Execution permission source)
    {old : Σ state : State rules O, Candidate program state}
    {new : Σ state : State rules O, Application levels O state}
    (member : (old, new) ∈ ledger comparison execution) :
    ∃ localComparison : PlainIso levels old.1 new.1,
      new.2 = application localComparison old.2.application := by
  have related := move_word_relation comparison (realize execution)
  rw [realize_word] at related
  have sourceRelated := List.forall₂_map_left_iff.mp related
  exact List.forall₂_zip sourceRelated member

theorem ledger_permissions {source target : State rules O} (comparison : PlainIso levels source target)
    (execution : program.Execution permission source)
    {old : Σ state : State rules O, Candidate program state}
    {new : Σ state : State rules O, Application levels O state}
    (member : (old, new) ∈ ledger comparison execution) : permission old.2 :=
  execution_permissions execution old (List.of_mem_zip member).1

theorem ledger_rule_indices {source target : State rules O} (comparison : PlainIso levels source target)
    (execution : program.Execution permission source) :
    (ledger comparison execution).map (fun pair => pair.1.2.ruleIndex.val) = origins execution := by
  have original := congrArg (List.map (fun event => event.2.ruleIndex.val)) (ledger_sources comparison execution)
  simpa only [List.map_map, Function.comp_def, origins] using original

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransport.ledger_correspondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransport.ledger_permissions
