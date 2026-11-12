import Mettapedia.Languages.MeTTa.PeTTa.StreamingScopeReachability

/-!
# Full-frontier allocation and genuinely unused entry scopes

A future identity hidden in a bank/frame/cell is not ignored. Merely fitting
the post-entry counter does not establish that the entry activation is unused.
These are invariant counterexamples, not runtime name restrictions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingScopeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)
open Mettapedia.Languages.MeTTa.PeTTa
open Streaming.ScopeInvariant

def future : Atom := .var (Unifying.freshName 0 "x")
def base : Streaming.State := {world := {state := Effects.empty},agenda := []}

theorem future_is_not_preallocated : ¬Unifying.Supported (Mettapedia.ScopedString.Before 0) future := by
  intro supported
  have allocated := supported (Unifying.freshName 0 "x") (by simp [future,atomFreeVars])
  obtain ⟨scope,earlier,name,equal⟩ := allocated
  omega

def hiddenBank : Streaming.State := {base with agenda := [.collect 0 [] [] [⟨future,[]⟩]]}

theorem collection_bank_participates : ¬WellScoped hiddenBank := by
  intro good
  have active := (head_and_tail good rfl).1
  have packet := active.2.2 ⟨future,[]⟩ (by simp)
  exact future_is_not_preallocated packet.1

def hiddenFrame : Streaming.State :=
  {base with agenda := [.execute ⟨.returned [],[.source (.bind (.symbol "pattern") future)]⟩]}

theorem saved_caller_participates : ¬WellScoped hiddenFrame := by
  intro good
  have active := (head_and_tail good rfl).1
  have frame := active.2 (.source (.bind (.symbol "pattern") future)) (by simp)
  exact future_is_not_preallocated frame.2

def pollutedWorld : Streaming.World :=
  {state := {Effects.empty with cells := fun name => if name == "slot" then some future else none}}

theorem post_entry_bound_alone_passes :
    worldSupported (Mettapedia.ScopedString.Before 1) pollutedWorld := by
  constructor
  · intro name value stored
    change (if name == "slot" then some future else none) = some value at stored
    split at stored
    · cases stored
      exact ScopedSource.renamed_allocated 0 (.var "x")
    · cases stored
  · simp [pollutedWorld]

theorem unused_entry_condition_fails :
    ¬worldSupported (Mettapedia.ScopedString.Before pollutedWorld.uses) pollutedWorld := by
  intro good
  exact future_is_not_preallocated (good.1 "slot" future (by rfl))

theorem reusing_that_activation_aliases_the_cell :
    Unifying.rename pollutedWorld.uses (.var "x") = future ∧
      pollutedWorld.state.cells "slot" = some future := ⟨rfl,rfl⟩

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingScopeControls
