import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeRenaming

/-!
# Exact selected scalar instances under arbitrary private names

The state is obtained from the existing matcher. Its successful selection
and repeated-formal behaviour are checked before transport by a permutation;
no second unifier or assumed selected-substitution equation is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeScalarInstances

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open RetainedTypePayloads

def world : ExternalView := fun tag key => .grounded (.custom tag key)
def seed : String := "rangeScalar"
def seedState : TypeScopeMatcher.State :=
  (TypeScopeMatcher.unify world Atom.var (.symbol "Number") (.var seed)).getD Atom.var

theorem seed_selected :
    TypeScopeMatcher.unify world Atom.var (.symbol "Number") (.var seed) = some seedState := by
  unfold seedState
  cbv

theorem seed_value : seedState seed = .symbol "Number" := by cbv

theorem seed_safe : TypeScopeMatcher.SafeState seedState := by
  intro name
  cbv
  split <;> rfl

theorem seed_repeated :
    TypeScopeMatcher.unify world seedState (.symbol "Number") (.symbol "Number") = some seedState := by
  cbv
  congr 1
  funext name
  change substA Atom.var (seedState name) = seedState name
  exact substA_var_self _

theorem seed_rejects_string :
    TypeScopeMatcher.unify world seedState (.symbol "String") (.symbol "Number") = none := by cbv

def permutation (name : String) : Equiv.Perm String := Equiv.swap seed name
def state (name : String) : TypeScopeMatcher.State := TypeScopeRenaming.renameState (permutation name) seedState

theorem rename_initial (rename : Equiv.Perm String) :
    TypeScopeRenaming.renameState rename Atom.var = Atom.var := by
  funext name
  simp [TypeScopeRenaming.renameState, renameAtom]

theorem selected (name : String) :
    TypeScopeMatcher.unify world Atom.var (.symbol "Number") (.var name) = some (state name) := by
  have renamed := TypeScopeRenaming.unify_rename world (permutation name) Atom.var
    (fun _ => rfl) (.symbol "Number") (.var seed) rfl rfl
  simpa [rename_initial, renameAtom, permutation, seed_selected, state] using renamed

theorem selected_value (name : String) : state name name = .symbol "Number" := by
  simp [state, TypeScopeRenaming.renameState, permutation, seed_value, renameAtom]

theorem repeated (name : String) :
    TypeScopeMatcher.unify world (state name) (.symbol "Number") (.symbol "Number") = some (state name) := by
  have renamed := TypeScopeRenaming.unify_rename world (permutation name) seedState seed_safe
    (.symbol "Number") (.symbol "Number") rfl rfl
  simpa [renameAtom, seed_repeated, state] using renamed

theorem rejects_string (name : String) :
    TypeScopeMatcher.unify world (state name) (.symbol "String") (.symbol "Number") = none := by
  have renamed := TypeScopeRenaming.unify_rename world (permutation name) seedState seed_safe
    (.symbol "String") (.symbol "Number") rfl rfl
  simpa [renameAtom, seed_rejects_string, state] using renamed

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeScalarInstances
