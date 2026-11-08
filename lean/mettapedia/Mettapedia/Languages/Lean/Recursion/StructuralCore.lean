import Init.Data.Nat.Div.Basic
import Mettapedia.Languages.Lean.Recursion.Derive

/-!
# Proof-argument recursion reached by division and remainder

The source's Nat.brecOn motive retains the invariant x < fuel. Its recursive
source equations supply the call arguments and branch conditions; each fuel
decrease is checked at those actual arguments.
-/

namespace Mettapedia.Languages.Lean.Recursion.StructuralCore

open Derive

derive_recursion_interface Nat.div.go as DivGo
derive_recursion_interface Nat.modCore.go as ModGo

end Mettapedia.Languages.Lean.Recursion.StructuralCore
