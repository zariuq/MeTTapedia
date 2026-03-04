import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Premises

/-!
# MeTTa-Calculus Premise Adequacy Scaffold

Scaffold bridge from the IR premise contract (`Premises.lean`) to executable
runtime reduction (`Reduction.lean`).

This establishes:

- all declared relation/builtin names are implemented by runtime dispatch
- builtin adapters have explicit executable specs
- a premise-contract step view is definitionally aligned with `step`

The next extension step is a full theorem connecting this runtime adapter path
to a generic `PremiseProgram` evaluator with builtin callbacks.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Adequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Premises

private def runtimeImplementsRel (rel : String) : Bool :=
  rel == relMettaComm || rel == relMettaStepNoReflect

private def runtimeImplementsBuiltin (name : String) : Bool :=
  name == builtinMettaCommWitness || name == builtinMettaCommOnlyStep

theorem runtime_covers_declared_relations :
    (mettaCalcPremises.relations.map (·.name)).all runtimeImplementsRel = true := by
  native_decide

theorem runtime_covers_declared_builtins :
    (mettaCalcPremises.builtins.map (·.name)).all runtimeImplementsBuiltin = true := by
  native_decide

theorem comm_witness_adapter_spec (t u p q : Pattern) :
    mettaCalcBuiltinMany builtinMettaCommWitness [t, u, p, q] =
      (match unifyPattern? t u with
       | some σ => [.apply "MRef" [applyDot σ p, applyDot σ q]]
       | none => []) := by
  simp [mettaCalcBuiltinMany, mettaCommWitnessBuiltinMany]
  rfl

theorem comm_only_step_adapter_spec (src : Proc) :
    mettaCalcBuiltinMany builtinMettaCommOnlyStep [src] = commOnlyStep src := by
  have hneq : (builtinMettaCommOnlyStep == builtinMettaCommWitness) = false := by
    native_decide
  simp [mettaCalcBuiltinMany, mettaCommOnlyStepBuiltinMany, hneq]

/-- Step semantics viewed explicitly as “rewrite + premise contract runtime”. -/
def stepViaPremiseContract (p : Proc) : List Proc :=
  Mettapedia.OSLF.MeTTaIL.Engine.rewriteWithContextWithPremisesUsing mettaCalcRelEnv mettaCalc p

theorem stepViaPremiseContract_eq_step (p : Proc) :
    stepViaPremiseContract p = step p := by
  simp [stepViaPremiseContract, step]

def ReducesViaPremiseContract (p q : Proc) : Prop :=
  q ∈ stepViaPremiseContract p

theorem reducesViaPremiseContract_iff_reduces {p q : Proc} :
    ReducesViaPremiseContract p q ↔ Reduces p q := by
  simp [ReducesViaPremiseContract, Reduces, stepViaPremiseContract_eq_step]

theorem premise_contract_comm_canary :
    demoCommTarget ∈ stepViaPremiseContract demoCommSource := by
  simpa [stepViaPremiseContract, step] using
    (show demoCommTarget ∈ step demoCommSource from by native_decide)

theorem premise_contract_refl_canary :
    demoReflectTarget ∈ stepViaPremiseContract demoReflectSource := by
  simpa [stepViaPremiseContract, step] using
    (show demoReflectTarget ∈ step demoReflectSource from by native_decide)

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Adequacy
