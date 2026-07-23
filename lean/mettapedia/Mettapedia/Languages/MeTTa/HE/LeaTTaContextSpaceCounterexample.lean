import MettaHyperonFull.Minimal.Interpreter

/-!
# Grounded context-space handle

The published interpreter returns its current `DynSpace` as a grounded atom.
Before repair #23, LeaTTa returned the ordinary symbol `&self`, losing both the
host-object boundary and the identity of a named context selected by `evalc`.

These canaries pin the repaired representation: `context-space` emits an opaque
`SpaceType` grounding, that handle is accepted by space consumers, and the
printed `&self` spelling is not confused with the runtime constructor.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaContextSpaceCounterexample

open Metta
open Metta.Minimal

private def contextInstruction : Atom :=
  .expr [.sym "context-space"]

private def contextItem : Item :=
  { stack := atomToStack contextInstruction [], bnd := [] }

private def defaultEnv : MinEnv :=
  MinEnv.ofAtomsGT [] []

/-- The default evaluation context is an opaque grounded `SpaceType`. -/
theorem default_context_space_is_grounded :
    interpretStack1 defaultEnv 1 St.init contextItem =
      ([finItem [] (contextSpaceAtom "&self") []], St.init) := by
  simp [interpretStack1, contextItem, contextInstruction, atomToStack,
    defaultEnv, MinEnv.ofAtomsGT]

/-- A derived environment exposes its own context identity, not `&self`. -/
theorem named_context_space_is_preserved :
    let namedEnv := { defaultEnv with contextName := "&named" }
    interpretStack1 namedEnv 1 St.init contextItem =
      ([finItem [] (contextSpaceAtom "&named") []], St.init) := by
  simp [interpretStack1, contextItem, contextInstruction, atomToStack,
    defaultEnv, MinEnv.ofAtomsGT]

/-- Evaluator-produced opaque handles are valid inputs to space consumers. -/
theorem grounded_context_handle_resolves :
    spaceName World.empty (contextSpaceAtom "&named") = some "&named" := by
  rfl

/-- Selecting a named context through `evalc` records that identity in the
derived environment consumed by the nested evaluator. -/
theorem evalc_environment_remembers_named_context :
    (evalEnvForSpace defaultEnv World.empty (contextSpaceAtom "&named")).map
        (fun selected => selected.contextName) = some "&named" := by
  simp [evalEnvForSpace, spaceName, resolveTok, defaultEnv,
    MinEnv.ofAtomsGT, contextSpaceAtom]

/-- Opaque space handles keep the familiar surface spelling without becoming
symbols internally. -/
theorem default_context_pretty :
    Metta.Pretty.atom (contextSpaceAtom "&self") = "&self" := by
  simp [Metta.Pretty.atom, Metta.Pretty.ground, contextSpaceAtom]

/-- Historical negative canary: the opaque handle is not an ordinary symbol. -/
theorem context_handle_is_not_symbol :
    contextSpaceAtom "&self" ≠ Atom.sym "&self" := by
  simp [contextSpaceAtom]

end Mettapedia.Languages.MeTTa.HE.LeaTTaContextSpaceCounterexample
