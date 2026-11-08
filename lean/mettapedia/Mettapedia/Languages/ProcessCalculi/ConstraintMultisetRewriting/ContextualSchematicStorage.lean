import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStep
import Mettapedia.OSLF.Syntax.ContextualFamilyComposition

/-!
# Ordinary stored atoms are private schemas

`store` is the ordinary storage entry: the atom's schematic metavariables
are placed in the private component, before any reader opens the atom.
The existing selected-use machinery then gives each read or take its own
instance. One instance uses one assignment for the whole atom, preserving
aliases between a stored rule's head and body.

An explicitly shared reference uses `Row.shared`; an explicitly captured schema
uses `Row.schema` with its declared shared component. Ordinary storage does
not turn its schematic variables into such references. The raw occurrence
step still operates on already prepared terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRows

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

universe u
variable {S : Signature} {Local Shared Next : Type} {O : Type u}
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def privateSource : Assignment locals (ContextualSelectionViews.source locals captures) :=
  fun name => generator (ContextualSelectionViews.source locals captures) (.inl name)

/-- Store an ordinary atom. Its unresolved schematic variables belong to
the atom's private template, not to the caller's shared variable frame. -/
def store {Γ : Ctx S} {sort : S.Srt} (atom : Term (signature S locals) Γ sort) :
    Row locals captures Γ sort :=
  .schema (instantiate (privateSource locals captures) atom)

def instanceAt (scope : Nat) :
    Assignment locals (ContextualSelectionViews.target locals captures) :=
  fun name => generator (ContextualSelectionViews.target locals captures) (.inl (ScopedVar.at scope name))

/-- Every part of one stored atom uses the same fresh assignment. -/
theorem view_store (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (atom : Term (signature S locals) Γ sort) :
    viewAt locals captures scope (store locals captures atom) =
      instantiate (instanceAt locals captures scope) atom := by
  dsimp only [store,viewAt,ContextualFreshening.termAt]
  rw [instantiate_comp]
  congr 1
  funext name
  exact instantiate_generator (ContextualFreshening.assignment locals captures scope) (.inl name)

/-- A caller-frame substitution cannot specialize an ordinary stored atom.
This includes assignments obtained by solving earlier read instances. -/
theorem map_store {next : Next → MetaArity S} (assignment : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (atom : Term (signature S locals) Γ sort) :
    (store locals captures atom).map locals assignment = store locals next atom := by
  dsimp only [store,Row.map]
  congr 1
  rw [instantiate_comp]
  congr 1
  funext name
  exact instantiate_generator (liftCaptures locals assignment) (.inl name)

/-- The ordinary read entry uses a port scope, not the stored variable's
original identifier or its physical occurrence identifier. -/
theorem prepared_read_store (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (port : Fin selection.read.length)
    (atom : Term (signature S locals) Γ sort)
    (stored : rows (selection.read.get port) = store locals captures atom) :
    (ContextualActivatedStep.prepared locals captures occupied selection rule rows).read port =
      instantiate (instanceAt locals captures
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port))) atom := by
  rw [ContextualActivatedStep.prepared_read_view,stored,view_store]

/-- Consumption freshens the selected schema in the same way; physical
exclusivity remains a separate condition on the selected occurrences. -/
theorem prepared_take_store (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (port : Fin selection.taken.length)
    (atom : Term (signature S locals) Γ sort)
    (stored : rows (selection.taken.get port) = store locals captures atom) :
    (ContextualActivatedStep.prepared locals captures occupied selection rule rows).taken port =
      instantiate (instanceAt locals captures
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port))) atom := by
  rw [ContextualActivatedStep.prepared_taken_view,stored,view_store]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRows
