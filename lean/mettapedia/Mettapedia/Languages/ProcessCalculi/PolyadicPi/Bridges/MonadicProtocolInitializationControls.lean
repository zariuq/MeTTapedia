import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolInitialization

/-!
# Entry controls for actual tuple occurrences

Equal messages create two offered slots with distinct private positions.
Listeners keep their original guarded bodies in the ordinary frame. A guard
that activates another binary output obtains a new offered slot only when
its received fields actually open that body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.InitializationControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open MonadicProtocol MonadicProtocol.Capabilities MonadicProtocol.RuntimeState
open MonadicProtocol.Initialization ScopedActiveFrontier

abbrev context : Ctx sig := [.nm, .nm, .nm]
abbrev subject : Var context .nm := .zero
abbrev first : Var context .nm := .succ .zero
abbrev second : Var context .nm := .succ (.succ .zero)

def message : Proc context := out2 (.var subject) (.var first) (.var second)
def duplicates : Proc context := par message message
theorem duplicateGuarded : Guarded duplicates := .par (.out2 _ _ _) (.out2 _ _ _)
def duplicateEntry := guarded_entry duplicateGuarded

theorem duplicate_offers_retained : duplicateEntry.offers.length = 2 := by
  dsimp [duplicateEntry, guarded_entry]
  change (offers (ScopedActiveFrontier.normalize (par message message)).atoms).length = 2
  rw [ScopedActiveFrontier.normalize_par]
  change (offers (ScopedActiveFrontier.merge
    (ScopedActiveFrontier.normalize (out2 (.var subject) (.var first) (.var second)))
    (ScopedActiveFrontier.normalize (out2 (.var subject) (.var first) (.var second)))).atoms).length = 2
  rw [ScopedActiveFrontier.normalize_out2]
  rfl
theorem no_unselected_frame_occurrences : duplicateEntry.residual = [] := by
  dsimp [duplicateEntry, guarded_entry]
  change frameAtoms (ScopedActiveFrontier.normalize (par message message)).atoms = []
  rw [ScopedActiveFrontier.normalize_par]
  change frameAtoms (ScopedActiveFrontier.merge
    (ScopedActiveFrontier.normalize (out2 (.var subject) (.var first) (.var second)))
    (ScopedActiveFrontier.normalize (out2 (.var subject) (.var first) (.var second)))).atoms = []
  rw [ScopedActiveFrontier.normalize_out2]
  rfl

/-- The public messages are equal, but their sessions are genuinely distinct.
No set-valued catalog or equality deduplication controls their multiplicity. -/
theorem duplicate_sessions_distinct :
    key (Γ := context) 2 ⟨0, by decide⟩ .session ≠ key 2 ⟨1, by decide⟩ .session := by
  intro equal
  have owners := (key_injective 2 ⟨0, by decide⟩ ⟨1, by decide⟩ .session .session equal).1
  have impossible := congrArg Fin.val owners
  cases impossible

theorem duplicate_entry_actual :
    StructuralEq duplicates
        (duplicateEntry.scope.close
          (registrySource (offeredRegistry duplicateEntry.offers) (parallel duplicateEntry.residual))) ∧
      StructuralEq (lower duplicates)
        (duplicateEntry.scope.close
          ((privateScope duplicateEntry.offers.length).close
            (registryTarget (offeredRegistry duplicateEntry.offers) (parallel duplicateEntry.residual)))) :=
  ⟨duplicateEntry.source, duplicateEntry.target⟩

def chainedBody : Proc (.nm :: .nm :: context) :=
  out2 (.var (.succ (.succ subject))) (.var .zero) (.var (.succ .zero))
def listener : Proc context := inp2 (.var subject) chainedBody
theorem listenerGuarded : Guarded listener := .inp2 _ (.out2 _ _ _)
abbrev listenerEntry := guarded_entry listenerGuarded

theorem suspended_output_is_not_an_offer : listenerEntry.offers = [] := by
  change offers (normalize listener).atoms = []
  change offers (ScopedActiveFrontier.normalize (inp2 (.var subject) chainedBody)).atoms = []
  rw [ScopedActiveFrontier.normalize_inp2]
  rfl
theorem listener_remains_one_actual_occurrence :
    HEq listenerEntry.residual ([listener] : List (Proc context)) := by
  change HEq (frameAtoms (normalize listener).atoms) ([listener] : List (Proc context))
  change HEq (frameAtoms (ScopedActiveFrontier.normalize (inp2 (.var subject) chainedBody)).atoms)
    ([listener] : List (Proc context))
  rw [ScopedActiveFrontier.normalize_inp2]
  rfl

theorem actual_activation :
    Step (par message listener) (openPair chainedBody (.var first) (.var second)) := .comm2 _ _ _ _

theorem field_order_retained : openPair chainedBody (.var first) (.var second) = message := rfl

theorem activated_output_gets_an_offer :
    (guarded_entry ((Guarded.out2 _ _ _ : Guarded message))).offers.length = 1 := by
  dsimp [guarded_entry]
  rw [ScopedActiveFrontier.normalize_out2]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.InitializationControls
