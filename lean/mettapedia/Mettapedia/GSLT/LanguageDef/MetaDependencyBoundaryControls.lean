import Mettapedia.GSLT.LanguageDef.MetaDependencyBoundary
import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceControls

/-!
# Declared dependencies are not ambient depth

These controls use the existing authored occurrence-control language and its
derived binding signature. No second constructor inventory or metavariable
calculus is introduced. Both declaration styles are represented in the same
existing `withMetas` extension.
-/

namespace Mettapedia.GSLT.LanguageDef.MetaDependencyControls

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Binding
open WellSorted.OccurrenceControls (a b language constantA)
open BindingSyntax

set_option autoImplicit false

abbrev signature := signatureOf language

/-- The first declaration is closed; the second permits exactly one A input. -/
abbrev declarations : List (MetaArity signature) := [([], a), ([a], a)]

abbrev closedIndex : Fin declarations.length := ⟨0, by decide⟩
abbrev dependentIndex : Fin declarations.length := ⟨1, by decide⟩

def constant {ambient : Ctx signature} : Term signature ambient a :=
  .op (.constructor constantA (by simp [language])
    (by simp [WellSorted.UsesBareCollection, constantA]) .nil) .nil

def usesArgument : (i : Fin declarations.length) →
    Term signature (declarations.get i).1 (declarations.get i).2 := by
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) j) i
  · exact constant
  · exact .var .zero

def ignoresArgument : (i : Fin declarations.length) →
    Term signature (declarations.get i).1 (declarations.get i).2 := by
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) j) i
  · exact constant
  · exact constant

def emptyArguments (ambient : Ctx signature) : Ren signature [] ambient :=
  fun _ position => nomatch position

def oldArgument : Ren signature [a] [a, a] := fun _ position => by
  cases position with
  | zero => exact .succ .zero
  | succ impossible => exact nomatch impossible

def newestArgument : Ren signature [a] [a, a] := fun _ position => by
  cases position with
  | zero => exact .zero
  | succ impossible => exact nomatch impossible

def addBinder : Ren signature [a, a] [b, a, a] := fun _ position => .succ position

/-- An ambient A does not grant a closed metavariable access to it. -/
theorem closed_at_nonempty_scope :
    instantiate usesArgument
      (rename (emptyArguments [a]) (metaVar closedIndex)) =
      (constant : Term signature [a] a) := by
  exact instantiate_metaVar_arguments usesArgument closedIndex (emptyArguments [a])

theorem dependency_at_shallow_scope :
    instantiate usesArgument (metaVar dependentIndex) =
      (Term.var .zero : Term signature [a] a) := by
  rw [instantiate_metaVar]
  rfl

/-- The same declaration may select the older A beneath a new A binder. -/
theorem dependency_at_deeper_scope :
    instantiate usesArgument (rename oldArgument (metaVar dependentIndex)) =
      (Term.var (.succ .zero) : Term signature [a, a] a) := by
  exact instantiate_metaVar_arguments usesArgument dependentIndex oldArgument

/-- A further differently typed binder transports the selected old argument. -/
theorem dependency_under_further_binder :
    instantiate usesArgument
      (rename addBinder (rename oldArgument (metaVar dependentIndex))) =
      (Term.var (.succ (.succ .zero)) : Term signature [b, a, a] a) := by
  exact instantiate_metaVar_arguments_comp usesArgument dependentIndex oldArgument addBinder

theorem new_binder_does_not_capture :
    instantiate usesArgument (rename oldArgument (metaVar dependentIndex)) ≠
      (Term.var .zero : Term signature [a, a] a) := by
  rw [dependency_at_deeper_scope]
  intro equal
  cases equal

/-- Choosing the new variable explicitly is meaningful, but it is a different
argument selection, not the weakening of the old occurrence. -/
theorem explicitly_select_new_binder :
    instantiate usesArgument (rename newestArgument (metaVar dependentIndex)) =
      (Term.var .zero : Term signature [a, a] a) := by
  exact instantiate_metaVar_arguments usesArgument dependentIndex newestArgument

theorem argument_choices_observably_differ :
    erase (instantiate usesArgument (rename oldArgument (metaVar dependentIndex))) ≠
      erase (instantiate usesArgument (rename newestArgument (metaVar dependentIndex))) := by
  rw [dependency_at_deeper_scope, explicitly_select_new_binder]
  decide

/-- Declared permission to use an argument does not require actually using it. -/
theorem allowed_argument_can_be_ignored :
    instantiate ignoresArgument (rename oldArgument (metaVar dependentIndex)) =
      (constant : Term signature [a, a] a) ∧
    instantiate ignoresArgument (rename newestArgument (metaVar dependentIndex)) =
      (constant : Term signature [a, a] a) := by
  exact ⟨instantiate_metaVar_arguments ignoresArgument dependentIndex oldArgument,
    instantiate_metaVar_arguments ignoresArgument dependentIndex newestArgument⟩

theorem permissions_not_ambient_depth :
    (declarations.get dependentIndex).1.length = 1 ∧
      ([a, a] : Ctx signature).length = 2 ∧
      ([b, a, a] : Ctx signature).length = 3 := by decide

theorem closed_and_dependent_same_result_sort :
    (declarations.get closedIndex).2 = (declarations.get dependentIndex).2 ∧
      (declarations.get closedIndex).1 ≠ (declarations.get dependentIndex).1 := by decide

theorem closed_dependency_has_no_variable : ¬ Nonempty (Var ([] : Ctx signature) a) := by
  rintro ⟨position⟩
  exact nomatch position

/-- The old occurrence analysis retains the actual typed scopes, but cannot
choose between these declarations: both have the same result type. -/
theorem occurrence_scope_retained_without_permission_choice :
    WellSorted.TypedAt language WellSorted.OccurrenceControls.free
      WellSorted.OccurrenceControls.holeTerm WellSorted.OccurrenceControls.aSite
      [] (.base "Pack") [a] a ∧
    WellSorted.TypedAt language WellSorted.OccurrenceControls.free
      WellSorted.OccurrenceControls.holeTerm WellSorted.OccurrenceControls.bSite
      [] (.base "Pack") [b] a :=
  ⟨WellSorted.OccurrenceControls.under_a_scope, WellSorted.OccurrenceControls.under_b_scope⟩

end Mettapedia.GSLT.LanguageDef.MetaDependencyControls
