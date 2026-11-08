import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixAskControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModelControls

/-!
# General declaration extension preserves asks without old-frame inhabitants

An infinite source is embedded at odd target identities, beside new unary
declarations. An empty source also extends even though it has no closed
term. A collapsing binding substitution supplies the negative boundary:
arity preservation alone does not reflect the original ask.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualPrefixModels
open ContextualConjunctiveControls (locals captures a p schemaRows)
open ContextualSelectionViews.Controls (base atom)

def target : Nat ⊕ Nat → MetaArity base
  | .inl _ => ([()], ())
  | .inr _ => ([], ())

def oddNames : Extension captures where
  Names := Nat ⊕ Nat
  declarations := target
  name name := .inr (2 * name + 1)
  injective := by
    intro first second same
    have values := Sum.inr.inj same
    omega
  preserves _ := rfl

theorem the_new_target_has_unary_declarations : (target (Sum.inl 0)).1 = [()] := rfl

theorem the_source_names_really_move_to_odd_identities :
    oddNames.name 0 = .inr 1 ∧ oddNames.name 1 = .inr 3 ∧ oddNames.name 42 = .inr 85 := ⟨rfl, rfl, rfl⟩

theorem the_schema_count_survives_the_nonsurjective_infinite_embedding :
    ContextualGuardSemantics.Ask locals (ContextualFrameUnifier.mapProblem oddNames.assignment [])
      (fun occurrence => (schemaRows occurrence).map locals oddNames.assignment) {7}
      ((Check.count (p a) 1).map (instantiate oddNames.assignment)) :=
  (ContextualGuardSemantics.Ask.extension_iff locals oddNames [] schemaRows {7} (.count (p a) 1)).mpr
    ContextualPrefixAskControls.old_schema_count

def caller : Term (signature base captures) [] () := generator captures 0
def sharedRows (_ : Nat) : ContextualStoredRows.Row locals captures [] () := .shared caller

theorem the_source_caller_equality_is_not_entailed :
    ¬ ContextualGuardSemantics.Ask locals [] sharedRows ∅ (.equal caller a) := by
  intro ask
  have same := ask Nat captures (generator captures) (fun _ member => by cases member)
  change caller = a at same
  have heads := (Term.op.inj same).1
  cases heads

theorem the_extra_names_cannot_discharge_the_caller_check :
    ¬ ContextualGuardSemantics.Ask locals (ContextualFrameUnifier.mapProblem oddNames.assignment [])
      (fun occurrence => (sharedRows occurrence).map locals oddNames.assignment) ∅
      ((Check.equal caller a).map (instantiate oddNames.assignment)) := by
  intro extended
  exact the_source_caller_equality_is_not_entailed
    ((ContextualGuardSemantics.Ask.extension_iff locals oddNames [] sharedRows ∅ (.equal caller a)).mp extended)

def prior : EquationStore (Term (signature base captures) [] ()) := [(caller, a)]
def sourceModel : Assignment captures captures := fun _ => a

theorem the_actual_lifted_model_satisfies_the_moved_prefix :
    ContextualFrameUnifier.Models (oddNames.liftModel sourceModel)
      (ContextualFrameUnifier.mapProblem oddNames.assignment prior) := by
  apply (oddNames.models_liftModel_iff sourceModel prior).mpr
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  with_unfolding_all rfl

namespace EmptySource

open ContextualPrefixModelControls (emptySignature noDeclarations no_old_closed_term)

abbrev declaration (name : Nat) : MetaArity emptySignature := if name = 0 then ([], ()) else ([()], ())

def extension : Extension noDeclarations where
  Names := Nat
  declarations := declaration
  name name := nomatch name
  injective := by intro name; cases name
  preserves name := nomatch name

theorem there_is_no_total_retraction_into_the_old_declarations :
    ¬ Nonempty (Assignment declaration noDeclarations) := by
  rintro ⟨assignment⟩
  exact no_old_closed_term (assignment 0)

theorem the_empty_prefix_still_has_an_extended_model :
    ∃ (Future : Type) (future : Future → MetaArity emptySignature)
      (candidate : Assignment declaration future),
      ContextualFrameUnifier.Models candidate
        (ContextualFrameUnifier.mapProblem extension.assignment
          ([] : EquationStore (Term (signature emptySignature noDeclarations) [] ()))) := by
  apply (extension.exists_model_iff _).mpr
  exact ⟨Empty, noDeclarations, (fun name => nomatch name), fun _ member => by cases member⟩

end EmptySource

namespace CollapsingChange

open ContextualPrefixModelControls (emptySignature noDeclarations callers aliasCallers)

def first : Term (signature emptySignature callers) [] () := generator callers false
def second : Term (signature emptySignature callers) [] () := generator callers true
def rows (_ : Nat) : ContextualStoredRows.Row noDeclarations callers [] () := .shared first

theorem the_original_equality_is_not_entailed :
    ¬ ContextualGuardSemantics.Ask noDeclarations [] rows ∅ (.equal first second) := by
  intro ask
  have same := ask Bool callers (generator callers) (fun _ member => by cases member)
  change first = second at same
  have heads := (Term.op.inj same).1
  have names := congrArg Operator.key (Sum.inr.inj heads)
  cases names

theorem a_binding_substitution_can_manufacture_the_ask :
    ContextualGuardSemantics.Ask noDeclarations (ContextualFrameUnifier.mapProblem aliasCallers [])
      (fun occurrence => (rows occurrence).map noDeclarations aliasCallers) ∅
      ((Check.equal first second).map (instantiate aliasCallers)) ∧
      ¬ ContextualGuardSemantics.Ask noDeclarations [] rows ∅ (.equal first second) := by
  refine ⟨?_, the_original_equality_is_not_entailed⟩
  intro Future future candidate _
  have same : instantiate aliasCallers first = instantiate aliasCallers second := by
    rw [first, second, instantiate_generator, instantiate_generator]
    rfl
  exact congrArg (instantiate candidate) same

end CollapsingChange

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionControls
