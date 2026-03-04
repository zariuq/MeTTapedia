import Mettapedia.OSLF.MeTTaIL.PremiseDatalog
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RelationNames

/-!
# MeTTa-Calculus Premises as PremiseProgram

IR-level premise program for the MeTTa-calculus rewrite rules:

- `mettaComm(t, u, p, q, pOut, qOut)`
- `mettaStepNoReflect(src, tgt)`

## Design note

The executable reduction in `Reduction.lean` remains the operational source of
truth (`mettaCalcRelEnv`) and uses direct Lean functions for unification and
COMM-only stepping. This file provides the backend-facing datalog contract with
named builtins so exporters and artifact checks can reason about premise wiring.

## Builtin contracts

- `mettaCommWitness(t, u, p, q)` returns zero or more witness values encoded as
  `MRef(pOut, qOut)`.
- `mettaCommOnlyStep(src)` returns zero or more `tgt` one-step COMM-only
  reducts (`mettaCalcCommOnly`).

## Source attribution

Semantics aligns with:

- `/home/zar/claude/hyperon/rho4u/metta-calculus/metta-calculus.core.tex`
- relation-name discipline inspired by
  `/home/zar/claude/lean-projects/mettapedia/Mettapedia/Languages/MeTTa/HE/HEPremises.lean`
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Premises

open Mettapedia.OSLF.MeTTaIL.PremiseDatalog
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

private def mettaCommRules : List PRule :=
  [ { headRel := relMettaComm
      headArgs := [ .var "t", .var "u", .var "p", .var "q", .var "pOut", .var "qOut" ]
      body := [ .computeMany builtinMettaCommWitness
                  [.var "t", .var "u", .var "p", .var "q"] "pair"
              , .deconstruct (.var "pair") "MRef" ["pOut", "qOut"] ]
      clauseName := some "mettaComm_builtin_witness" } ]

private def mettaStepNoReflectRules : List PRule :=
  [ { headRel := relMettaStepNoReflect
      headArgs := [ .var "src", .var "tgt" ]
      body := [ .computeMany builtinMettaCommOnlyStep [.var "src"] "tgt" ]
      clauseName := some "mettaStepNoReflect_comm_only_step" } ]

private def mettaCalcBuiltins : List BuiltinFn :=
  [ { name := builtinMettaCommWitness, arity := 4 }
  , { name := builtinMettaCommOnlyStep, arity := 1 }
  ]

private def mettaCalcAscentHints : List BackendHint :=
  [ { builtinName := builtinMettaCommWitness
      backend := "ascent"
      template := builtinMettaCommWitness ++ "({0}, {1}, {2}, {3})" }
  , { builtinName := builtinMettaCommOnlyStep
      backend := "ascent"
      template := builtinMettaCommOnlyStep ++ "({0})" }
  ]

/-- Premise IR contract for the MeTTa-calculus reduction rules. -/
def mettaCalcPremises : PremiseProgram where
  relations :=
    [ { name := relMettaComm
        paramTypes := ["Term", "Term", "Proc", "Proc", "Proc", "Proc"] }
    , { name := relMettaStepNoReflect
        paramTypes := ["Proc", "Proc"] }
    ]
  rules := mettaCommRules ++ mettaStepNoReflectRules
  builtins := mettaCalcBuiltins
  backendHints := mettaCalcAscentHints
  coreGroundEvalRelation := none
  stateConstructor := none

example : mettaCalcPremises.wellFormed = true := by
  native_decide

example : mettaCalcPremises.isStratified = true := by
  native_decide

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Premises
