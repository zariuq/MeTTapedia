import Mettapedia.Machines.BranchLocalNeed.Representation
import Mettapedia.Machines.BranchLocalNeed.LocalSteps

/-!
# Representation transport for actual local Need transitions

The existing reference specification compatibility is extended by one local
equation for silent transitions. This yields an exact ordered-successor law;
heap, ownership, receipt and work behavior comes from the existing maps.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedRepresentation

open NeedReference

variable {O L R U V F N E O' L' R' U' V' F' N' E' : Type}

theorem Mapping.effects_map
    (mapping : Mapping O L R U V F N E O' L' R' U' V' F' N' E')
    (world : World O U V F N E) :
    (mapping.mapWorld world).receipts.effects = world.receipts.effects.map mapping.effect := by
  simp only [Mapping.mapWorld, Mapping.mapReceipts, ReceiptGraph.effects,
    ← List.map_reverse, List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro node member
  rcases node with ⟨identity, parents, payload⟩
  cases payload <;> rfl

theorem local_step_map
    (mapping : Mapping O L R U V F N E O' L' R' U' V' F' N' E')
    (source : NeedLocalSteps.Extension O L R U V F N E)
    (target : NeedLocalSteps.Extension O' L' R' U' V' F' N' E')
    (compatible : Compatible mapping source.reference target.reference)
    (localLaw : ∀ state, target.localStep (mapping.state state) =
      (source.localStep state).map mapping.state)
    (machine : Machine O L R U V F N E) :
    (NeedLocalSteps.step source machine).map mapping.mapMachine =
      NeedLocalSteps.step target (mapping.mapMachine machine) := by
  cases control : machine.control with
  | run state stack =>
      simp only [NeedLocalSteps.step, Mapping.mapMachine_control, control, Mapping.mapControl, localLaw]
      cases intercepted : source.localStep state with
      | none => simpa only [intercepted, Option.map_none] using compatible.step_map machine
      | some next =>
          simp only [Option.map_some, List.map_cons, List.map_nil,
            Mapping.map_finished, Mapping.mapControl]
          rfl
  | force cell stack =>
      simpa only [NeedLocalSteps.step, Mapping.mapMachine_control, control, Mapping.mapControl]
        using compatible.step_map machine
  | returned result stack =>
      simpa only [NeedLocalSteps.step, Mapping.mapMachine_control, control, Mapping.mapControl]
        using compatible.step_map machine
  | halted result =>
      simpa only [NeedLocalSteps.step, Mapping.mapMachine_control, control, Mapping.mapControl]
        using compatible.step_map machine

end Mettapedia.Machines.BranchLocalNeed.NeedRepresentation
