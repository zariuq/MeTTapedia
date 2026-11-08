import Mettapedia.Languages.Lean.Recursion.MeasuredCore
import Mettapedia.Languages.Lean.Recursion.StructuralCore
import Mettapedia.Languages.Lean.Recursion.RelationalCore
import Mettapedia.Languages.Lean.Recursion.Wrappers

/-!
# Source functions and their accessible recursion implementations

The nonrecursive wrappers retain their actual conditions, source equations
and calls. Their implementations are the measured and proof-argument
recursors derived in the imported modules.
-/

namespace Mettapedia.Languages.Lean.Recursion.Core

open Wrappers

derive_recursion_wrapper Nat.div using [Nat.div.go] as Div
derive_recursion_wrapper Nat.modCore using [Nat.modCore.go] as ModCore
derive_recursion_wrapper Nat.mod using [Nat.modCore] as Mod
derive_recursion_wrapper Nat.minFac using [Nat.minFacAux] as MinFac

end Mettapedia.Languages.Lean.Recursion.Core
