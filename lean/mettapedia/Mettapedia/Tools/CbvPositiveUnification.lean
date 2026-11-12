import Mettapedia.Logic.LP.PositiveUnificationEvaluation
import Lean.Elab.Tactic.CbvSimproc
import Lean.Meta.Tactic.Cbv.Main

/-!
# Opt-in checked evaluation of successful finite unification

The existing bounded solver proposes a substitution. Its equality certificate
and the exact bounded/total correspondence justify the rewrite. A bounded
failure declines the shortcut; it is never treated as total rejection.
-/

set_option autoImplicit false

namespace Mettapedia.Tools.CbvPositiveUnification

open Lean Meta
open Mettapedia.Logic.LP

cbv_simproc_decl successfulUnification (@unifyTotal _ ?_ ?_ ?_ _) := fun expression => do
  if expression.hasFVar || expression.hasMVar then return .rfl
  let arguments := expression.getAppArgs
  unless arguments.size == 5 do return .rfl
  let bounded ← mkAppOptM ``unifyFuel
    #[some arguments[0]!, some arguments[1]!, some arguments[2]!,
      some arguments[3]!, some (mkNatLit 128), some arguments[4]!]
  let computation ← Tactic.Cbv.cbvEntry bounded
  let .step replacement certificate .. := computation | return .rfl
  unless replacement.isAppOfArity ``Option.some 2 do return .rfl
  let optionType ← inferType bounded
  let projection ← withLocalDeclD `answer optionType fun answer => do
    mkLambdaFVars #[answer] (← mkAppM ``Option.isSome #[answer])
  let success ← mkAppM ``congrArg #[projection, certificate]
  let agreement ← mkAppOptM ``PositiveUnificationEvaluation.total_eq_fuel_of_success
    #[some arguments[0]!, some arguments[1]!, some arguments[2]!,
      some arguments[3]!, some (mkNatLit 128), some arguments[4]!, some success]
  let proof ← mkAppM ``Eq.trans #[agreement, certificate]
  return .step (← Sym.share replacement) proof

end Mettapedia.Tools.CbvPositiveUnification
