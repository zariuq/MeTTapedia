import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnAliasEntry

/-!
# Alias return is not entry-value stability

The actual source unifier can bind an open input and its returned alias
together. This validates the current-read property while refuting the
stronger unchanged-entry-read claim in the absence of groundness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnAliasControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ScopedReturnLocal

def input : Atom := .var "x"
def recipe : Atom := .var "p"
def before : Equations := [(recipe, input)]
def known : Atom := .symbol "Known"
def after : Equations := before ++ [(input, known)]

theorem reached_alias_can_change_with_its_input :
    refine before input known = some after ∧
      observations before [input, recipe] = some [input, input] ∧
      observations after [input, recipe] = some [known, known] := by cbv

theorem current_alias_observation (environment : Environment) (solved : Solves environment before) :
    read environment recipe = read environment input :=
  solved (recipe, input) (by simp [before])

theorem alias_relation_does_not_supply_a_fixed_entry_value :
    ¬∃ value, ProtectedSlots.Fixed before input value := by
  rintro ⟨value, fixed⟩
  let first : Environment := fun _ => encode (.grounded (.int 7))
  let second : Environment := fun _ => encode known
  have firstSolved : Solves first before := by
    intro equation present
    cases List.mem_singleton.mp present
    simp [EagerDFS.Destination.read, first, recipe, input, encode, Mettapedia.Logic.LP.Subst.applyTerm]
  have secondSolved : Solves second before := by
    intro equation present
    cases List.mem_singleton.mp present
    simp [EagerDFS.Destination.read, second, recipe, input, encode, Mettapedia.Logic.LP.Subst.applyTerm]
  have firstRead := fixed first firstSolved
  have secondRead := fixed second secondSolved
  have conflict := firstRead.trans secondRead.symm
  simp [EagerDFS.Destination.read, first, second, input, known, encode, decode,
    Mettapedia.Logic.LP.Subst.applyTerm] at conflict

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnAliasControls
