import Mettapedia.Languages.MeTTa.PeTTa.DestinationVariableSupport
import Lean.Elab.Tactic.CbvSimproc

/-! # Opt-in support reduction before evaluating the first-order codec -/

set_option autoImplicit false

namespace Mettapedia.Tools.CbvDestinationSupport

open Lean Meta
open Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination

cbv_simproc_decl encodedSupport ((encode _).freeVars) := fun expression => do
  let_expr Mettapedia.Logic.LP.Term.freeVars _ _ encoded := expression | return .rfl
  let_expr encode atom := encoded | return .rfl
  let proof ← mkAppM ``encode_variable_support #[atom]
  let proofType ← inferType proof
  let_expr Eq _ _ replacement := proofType | return .rfl
  return .step (← Sym.share replacement) proof

end Mettapedia.Tools.CbvDestinationSupport
