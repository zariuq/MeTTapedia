import Mettapedia.Machines.TIsa.CellEffects

/-!
# Guarded instruction admission over storage-carrier rules

Replacing cells is a storage mechanism. The instruction meaning is supplied
by its actual guard on the listed old/new words. Restricting carrier firings
by that guard gives exactly the guarded resource profile, on arbitrary worlds.
The unrestricted carrier deliberately permits incorrect arithmetic results.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Admission

open Cells CellEffects Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Logic.ResourceFrame

universe u
variable {Key : Type u} [DecidableEq Key]

structure CarrierInvocation (Key : Type u) where
  before : Key → Word
  after : Key → Word

/-- The unguarded storage carrier, kept distinct from instruction semantics. -/
def carrier (recipes : List (Recipe Key)) : System.{u, u} (Cell Key) where
  Site := ULift.{u} (Fin recipes.length)
  Instance := fun _ => CarrierInvocation Key
  consume := fun {index} invocation => encode recipes[index.down].writes invocation.before
  read := fun {index} invocation => encode recipes[index.down].reads invocation.before
  produce := fun {index} invocation => encode recipes[index.down].writes invocation.after

def allowed (recipes : List (Recipe Key)) (entry : (carrier recipes).Entry) : Prop :=
  let recipe := recipes[entry.1.down]
  recipe.guard (recipe.inputs.map entry.2.before) (recipe.outputs.map entry.2.after) = true

/-- The guard is necessary and sufficient; the carrier alone is not an ISA. -/
theorem admitted_carrier_iff (recipes : List (Recipe Key)) (before after : Multiset (Cell Key)) :
    selectedStep (carrier recipes) (allowed recipes) before after ↔
      (profile recipes).theory.rewrites before after := by
  constructor
  · rintro ⟨⟨index, invocation⟩, guarded, enabled, endpoint⟩
    let checked : Invocation recipes[index.down] := ⟨invocation.before, invocation.after, guarded⟩
    exact ⟨index, checked, enabled, endpoint⟩
  · rintro ⟨index, invocation, enabled, endpoint⟩
    let raw : CarrierInvocation Key := ⟨invocation.before, invocation.after⟩
    exact ⟨⟨index, raw⟩, invocation.guarded, enabled, endpoint⟩

theorem guarded_is_carrier (recipes : List (Recipe Key)) (before after : Multiset (Cell Key))
    (step : (profile recipes).theory.rewrites before after) :
    (carrier recipes).theory.rewrites before after := by
  obtain ⟨entry, _, enabled, endpoint⟩ := (admitted_carrier_iff recipes before after).mpr step
  exact ⟨entry.1, entry.2, enabled, endpoint⟩

namespace Controls

private def addTwice : Recipe Nat where
  inputs := [0, 0]
  outputs := [0]
  guard := fun inputs outputs => match inputs, outputs with
    | [left, right], [result] => result == left + right
    | _, _ => false

private def bad : (carrier [addTwice]).Entry :=
  ⟨ULift.up ⟨0, by decide⟩, ⟨fun _ => 7, fun _ => 15⟩⟩

private def good : (carrier [addTwice]).Entry :=
  ⟨ULift.up ⟨0, by decide⟩, ⟨fun _ => 7, fun _ => 14⟩⟩

example : (carrier [addTwice]).Enables (encode {0} (fun _ => 7)) bad.2 := by
  simp [System.Enables, carrier, bad, Recipe.writes, Recipe.reads, addTwice, encode]
example : ¬allowed [addTwice] bad := by
  change ¬addTwice.guard [7, 7] [15] = true
  decide
example : allowed [addTwice] good := by
  change addTwice.guard [7, 7] [14] = true
  decide

end Controls

end Mettapedia.Machines.TIsa.Admission
