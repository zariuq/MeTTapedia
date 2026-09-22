import Mettapedia.Languages.PartrecMachine.Adequacy
import Mettapedia.GSLT.Core.OperationalRealization

/-!
# Mathlib's machine is realized in the generated theory

`Adequacy` shows that each step of Mathlib's `Turing.ToPartrec` machine is a
nonempty reduction sequence in the authored language.  This module states the
same thing as a structure the development already has for compilation: an
`OperationalRealization` from Mathlib's machine, viewed as a theory, to the theory
the OSLF construction generates from the authored language.

* Mathlib's machine is the theory of configurations under its step function, with
  syntactic equality as its equations (`mathlibMachine`).
* Every pending evaluation reduces to its eager result along an explicit path
  (`normalPath`), and every returning configuration to its successor
  (`retPath`).  The paths are built by recursion on codes and continuations, one
  generated step at a time; no path is chosen from a mere existence proof.
* `machineRealization` maps configurations by `encCfg` and each machine step to
  its path.  A machine step can take several generated steps, because the
  authored language reduces pending evaluations that Mathlib evaluates eagerly,
  which is the expansion this structure exists to record.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Turing.ToPartrec

/-- The theory the OSLF construction generates from the authored machine. -/
abbrev machineTheory : GSLT := langGSLT partrecMachine

/-- Mathlib's machine as a theory: configurations under its step function. -/
def mathlibMachine : GSLT :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.equalityGSLT Cfg fun cfg next => next ∈ step cfg

/-- One reduction as a path of the generated theory. -/
def reductionPath {source target : Pattern} (reduces : Reduces source target) :
    ExecutionPath machineTheory source target :=
  .cons ⟨(reduces_iff_generatedStep source target).mp reduces⟩ (.refl target)

/-- A reduction followed by a path. -/
def reductionThen {source middle target : Pattern} (reduces : Reduces source middle)
    (rest : ExecutionPath machineTheory middle target) : ExecutionPath machineTheory source target :=
  .cons ⟨(reduces_iff_generatedStep source middle).mp reduces⟩ rest

/-- **A pending evaluation reduces to its eager result**, along an explicit path. -/
def normalPath : (c : Code) → (k : Cont) → (v : List ℕ) →
    ExecutionPath machineTheory (normalTerm c k v) (encCfg (stepNormal c k v))
  | .zero', _, _ => reductionPath (reduces_normal_iff.mpr rfl)
  | .succ, _, _ => reductionPath (reduces_normal_iff.mpr rfl)
  | .tail, _, _ => reductionPath (reduces_normal_iff.mpr rfl)
  | .cons f fs, k, v => reductionThen (reduces_normal_iff.mpr rfl) (normalPath f (.cons₁ fs v k) v)
  | .comp f g, k, v => reductionThen (reduces_normal_iff.mpr rfl) (normalPath g (.comp f k) v)
  | .fix f, k, v => reductionThen (reduces_normal_iff.mpr rfl) (normalPath f (.fix f k) v)
  | .case f g, k, v =>
      match head : v.headI with
      | 0 =>
          have endpoint : encCfg (stepNormal f k v.tail) = encCfg (stepNormal (.case f g) k v) := by
            simp [stepNormal, head]
          reductionThen (reduces_normal_iff.mpr (by simp [normalReduct, head]))
            (endpoint ▸ normalPath f k v.tail)
      | y + 1 =>
          have endpoint : encCfg (stepNormal g k (y :: v.tail)) =
              encCfg (stepNormal (.case f g) k v) := by
            simp [stepNormal, head]
          reductionThen (reduces_normal_iff.mpr (by simp [normalReduct, head]))
            (endpoint ▸ normalPath g k (y :: v.tail))

/-- **A returning configuration reduces to its successor**, along an explicit path. -/
def retPath : (k : Cont) → (v : List ℕ) →
    ExecutionPath machineTheory (encCfg (.ret k v)) (encCfg (stepRet k v))
  | .halt, _ => reductionPath (reduces_ret_iff.mpr rfl)
  | .cons₁ fs as k, v => reductionThen (reduces_ret_iff.mpr rfl) (normalPath fs (.cons₂ v k) as)
  | .cons₂ ns k, v => reductionThen (reduces_ret_iff.mpr rfl) (retPath k (ns.headI :: v))
  | .comp f k, v => reductionThen (reduces_ret_iff.mpr rfl) (normalPath f k v)
  | .fix f k, v =>
      if zero : v.headI = 0 then
        have endpoint : encCfg (stepRet k v.tail) = encCfg (stepRet (.fix f k) v) := by
          simp [stepRet, zero]
        reductionThen (reduces_ret_iff.mpr (by simp [retReduct, zero]))
          (endpoint ▸ retPath k v.tail)
      else
        have endpoint : encCfg (stepNormal f (.fix f k) v.tail) = encCfg (stepRet (.fix f k) v) := by
          simp [stepRet, zero]
        reductionThen (reduces_ret_iff.mpr (by simp [retReduct, zero]))
          (endpoint ▸ normalPath f (.fix f k) v.tail)

/-- Each machine step as a path of the generated theory. -/
def machineStepPath : {cfg next : Cfg} → next ∈ step cfg →
    ExecutionPath machineTheory (encCfg cfg) (encCfg next)
  | .halt _, _, stepped => False.elim (by simp [step] at stepped)
  | .ret k v, _, stepped => congrArg encCfg (Option.some.inj stepped) ▸ retPath k v

/-- **Mathlib's machine is realized in the generated theory of the authored
machine.** -/
def machineRealization : OperationalRealization mathlibMachine machineTheory where
  mapTerm := encCfg
  mapEquiv := fun {left right} equivalent => by
    change left = right at equivalent
    subst equivalent
    exact machineTheory.equations.iseqv.refl _
  mapStep := fun stepped => machineStepPath stepped

#print axioms normalPath
#print axioms retPath
#print axioms machineRealization

end Mettapedia.Languages.PartrecMachine
