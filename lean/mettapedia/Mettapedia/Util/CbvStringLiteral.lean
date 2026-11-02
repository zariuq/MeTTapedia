import Lean.Elab.Tactic.CbvSimproc
import Lean.Meta.StringLitProof
import Lean.Meta.Sym.LitValues

/-!
# Opt-in proof-producing reduction of literal string decisions

This elaboration helper constructs ordinary equality or inequality proofs,
then uses proof irrelevance to identify the corresponding decision value.
It does not add an axiom or use native_decide. Consumers enable the simproc
locally and keep String.decEq opaque to the ordinary cbv unfolding path.
-/

namespace Mettapedia.Util.CbvStringLiteral

open Lean Meta

cbv_simproc_decl stringDecision (String.decEq _ _) := fun expression => do
  let_expr String.decEq first second := expression | return .rfl
  let some firstValue := Sym.getStringValue? first | return .rfl
  let some secondValue := Sym.getStringValue? second | return .rfl
  let literalProof ← if firstValue == secondValue then mkEqRefl first
    else mkStringLitNeProof firstValue secondValue
  let constructor := if firstValue == secondValue then ``Decidable.isTrue else ``Decidable.isFalse
  let result ← mkAppM constructor #[literalProof]
  let result ← Sym.share result
  let proof ← mkAppM ``Subsingleton.elim #[expression, result]
  return .step result proof

end Mettapedia.Util.CbvStringLiteral
