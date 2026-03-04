/-!
# MeTTa-Calculus Premise Relation/Builtin Names

Single source of truth for relation and builtin identifiers shared across:

- rewrite-rule premises in `Syntax.lean`
- premise IR declarations in `Premises.lean`
- executable relation environment in `Reduction.lean`

This prevents string-drift between syntax, IR, and runtime wiring.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

/-- Relation used by COMM premise lookup. -/
def relMettaComm : String := "mettaComm"

/-- Relation used by REFL to request COMM-only one-step targets. -/
def relMettaStepNoReflect : String := "mettaStepNoReflect"

/-- Builtin used by premise IR to enumerate COMM witnesses. -/
def builtinMettaCommWitness : String := "mettaCommWitness"

/-- Builtin used by premise IR to enumerate COMM-only one-step targets. -/
def builtinMettaCommOnlyStep : String := "mettaCommOnlyStep"

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

