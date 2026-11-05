import Mettapedia.OSLF.MeTTaIL.PremiseDatalog
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RelationNames

/-!
# MeTTa-Calculus Premises as PremiseProgram

IR-level premise program for the MeTTa-calculus rewrite rules:

- `mettaComm(t, u, p, q, pOut, qOut)`
- `mettaStepNoReflect(src, tgt)`

## Design note

The operational semantics is the corrected step `Corrected.cstep` and the
relational `Corrected.Step` (`CorrectedReduction.lean`). This file provides the
backend-facing datalog contract with named builtins so exporters and artifact
checks can reason about premise wiring. The runtime that answers it is
`Adequacy.correctedRelEnv`; the naive reading's environment `mettaCalcRelEnv`
in `Reduction.lean` is kept only for the separating theorems.

## Builtin contracts

- `mettaCommWitness(t, u, p, q)` returns zero or more witness values encoded as
  `MRef(pOut, qOut)`: the two inputs opened apart with fresh names, their
  patterns unified by the principal, idempotent unifier, and the dot applied
  once to each continuation with every pattern variable quoted
  (`Adequacy.correctedCommWitness`). A rule sees only its own bag, so the
  runtime supplies the free names of the process being stepped, and the fresh
  names avoid them as well.
- `mettaCommOnlyStep(src)` returns zero or more `tgt` one-step COMM-only
  reducts (`mettaCalcCommOnly`) under that witness.

## Source attribution

Semantics aligns with:

- `hyperon/rho4u/metta-calculus/metta-calculus.core.tex`
- relation-name discipline inspired by
  `lean/mettapedia/Mettapedia/Languages/MeTTa/HE/HEPremises.lean`
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
  decide +kernel

example : mettaCalcPremises.isStratified = true := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Premises
