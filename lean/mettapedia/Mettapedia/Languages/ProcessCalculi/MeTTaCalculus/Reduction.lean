import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.StructuralCongruence
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RelationNames
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.Languages.ProcessCalculi.Common.Common
import Mathlib.Data.Finset.Basic

/-!
# The naive executable reading of MeTTa-calculus reduction

This module is the naive reading of the symmetric MeTTa-calculus, kept as the
record of its defects. It is not the semantics. The semantics is the corrected
step `Corrected.cstep` and the relational `Corrected.Step` in
`CorrectedReduction.lean`: a principal, idempotent, occurs-checked unifier, the
two inputs opened apart with fresh names, and the dot applied once.

The naive reading:

- `COMM` unifies the two patterns as written with `unifyPattern?`, whose
  triangular binding list `applyDot` reads in one pass, and substitutes into
  both continuations without renaming the inputs apart;
- `REFL` uses one-step lookahead in the COMM-only fragment.

It captures a free name of one input with the other input's bound name, depends
on the choice of bound names, misses COMM between inputs that share a bound
name, accepts a cyclic problem that has no unifier, and has no nested REFL
result. The separating theorems are `MeTTaOperationsComm.Executable` and
`Corrected.Controls`; they are the only clients of `step` and `unifyPattern?`.

## Source attribution

Semantics follows:

- the F1R3FLY MeTTa-calculus manuscript, `metta-calculus.core.tex`

especially:

- `COMM`: `for(t <- x)P | for(u <- x)Q → P·σ | Q·σ`
- `REFL`: `x?P → for((P') <- x)0` when `P → P'`

The naive profile bounds unification and contextual traversal and
restricts the REFL premise to COMM-only stepping. `ReflectionClosure.lean`
states the displayed four rules as a relation; the nested-reflection
separation is `Corrected.Controls.naive_step_misses_nested_reflection`.
Consequently this executor is not an implementation of the displayed rules.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! ## Unification and dot-substitution -/

mutual
def occursFVar (x : String) : Pattern → Bool
  | .bvar _ => false
  | .fvar y => x == y
  | .apply _ args => occursFVarList x args
  | .lambda _nm b => occursFVar x b
  | .multiLambda _ _nms b => occursFVar x b
  | .subst b r => occursFVar x b || occursFVar x r
  | .collection _ elems rest =>
      occursFVarList x elems ||
      match rest with
      | some rv => x == rv
      | none => false

def occursFVarList (x : String) : List Pattern → Bool
  | [] => false
  | p :: ps => occursFVar x p || occursFVarList x ps
end

private def unifyLoop : Nat → List (Pattern × Pattern) → Bindings → Option Bindings
  | 0, _, _ => none
  | _ + 1, [], σ => some σ
  | fuel + 1, (sRaw, tRaw) :: eqs, σ =>
      let s := applyBindings σ sRaw
      let t := applyBindings σ tRaw
      if s == t then
        unifyLoop fuel eqs σ
      else
        match s, t with
        | .fvar x, term =>
            if occursFVar x term then none
            else
              match σ.lookup x with
              | some existing => unifyLoop fuel ((existing, term) :: eqs) σ
              | none => unifyLoop fuel eqs ((x, term) :: σ)
        | term, .fvar x =>
            if occursFVar x term then none
            else
              match σ.lookup x with
              | some existing => unifyLoop fuel ((term, existing) :: eqs) σ
              | none => unifyLoop fuel eqs ((x, term) :: σ)
        | .bvar n, .bvar m =>
            if n == m then unifyLoop fuel eqs σ else none
        | .apply c1 args1, .apply c2 args2 =>
            if c1 == c2 && args1.length == args2.length then
              unifyLoop fuel (List.zip args1 args2 ++ eqs) σ
            else
              none
        | .lambda _nm1 b1, .lambda _nm2 b2 =>
            unifyLoop fuel ((b1, b2) :: eqs) σ
        | .multiLambda n1 _nms1 b1, .multiLambda n2 _nms2 b2 =>
            if n1 == n2 then unifyLoop fuel ((b1, b2) :: eqs) σ else none
        | .subst b1 r1, .subst b2 r2 =>
            unifyLoop fuel ((b1, b2) :: (r1, r2) :: eqs) σ
        | .collection ct1 es1 rest1, .collection ct2 es2 rest2 =>
            if ct1 == ct2 && rest1 == rest2 && es1.length == es2.length then
              unifyLoop fuel (List.zip es1 es2 ++ eqs) σ
            else
              none
        | _, _ => none

/-- The naive reading's unifier. It returns a triangular binding list and
resolves terms through that list only one link deep, so its occurs check
misses a cycle through the list and it accepts a problem that has no unifier
(`Corrected.Controls.old_unifier_accepts_cycle`).
Kept for the separating theorems; the semantics unifies with
`Corrected.unify`, which is principal, idempotent and occurs-checked. -/
def unifyPattern? (lhs rhs : Pattern) : Option Bindings :=
  -- Fixed fuel keeps this executable even when `Pattern.sizeOf` is noncomputable.
  unifyLoop 256 [(lhs, rhs)] []

/-- The dotted bindings: every bound value quoted into a name. -/
def dotBindings (σ : Bindings) : Bindings :=
  σ.map (fun (x, v) => (x, nQuote v))

/-- The dot: substitute the dotted bindings in one pass. For an idempotent
principal unifier, such as the one `Corrected.unify` returns, this is the
manuscript's `P·σ̇` (`Corrected.applyDot_unify`), and the corrected step
applies it so, once per continuation. Applied to the naive reading's
triangular list it reads only the first link of a chain. -/
def applyDot (σ : Bindings) (p : Proc) : Proc :=
  applyBindings (dotBindings σ) p

/-! ## Premise environments for executable COMM/REFL -/

/-- The naive reading's runtime adapter for premise builtin `mettaCommWitness`:
the patterns unified as written and both continuations dotted, without opening
the inputs apart. Returns witness values encoded as `MRef(pOut, qOut)` to
match the `Premises.lean` rule body deconstruction. The corrected adapter is
`Adequacy.correctedCommWitness`. -/
def mettaCommWitnessBuiltinMany : List Pattern → List Pattern
  | [t, u, p, q] =>
      match unifyPattern? t u with
      | some σ =>
          let pOut := applyDot σ p
          let qOut := applyDot σ q
          [.apply "MRef" [pOut, qOut]]
      | none => []
  | _ => []

private def commWitnessPair? : Pattern → Option (Proc × Proc)
  | .apply "MRef" [pOut, qOut] => some (pOut, qOut)
  | _ => none

private def mettaCommTuplesFromBuiltin : List Pattern → List (List Pattern)
  | [t, u, p, q, _, _] =>
      (mettaCommWitnessBuiltinMany [t, u, p, q]).filterMap fun witness =>
        match commWitnessPair? witness with
        | some (pOut, qOut) => some [t, u, p, q, pOut, qOut]
        | none => none
  | _ => []

private def commOnlyRelEnv : RelationEnv where
  tuples := fun rel args =>
    if rel == relMettaComm then mettaCommTuplesFromBuiltin args else []

/-- Explicit contextual-depth bound for the executable frontier.  The
unbounded semantics remains `ContextualStep.Step`. -/
def executableContextFuel : Nat := 64

/-- The naive reading's COMM-only lookahead. -/
def commOnlyStep (p : Proc) : List Proc :=
  reductsUsing commOnlyRelEnv mettaCalcCommOnly executableContextFuel p

/-- The naive reading's runtime adapter for premise builtin `mettaCommOnlyStep`. -/
def mettaCommOnlyStepBuiltinMany : List Pattern → List Pattern
  | [src] => commOnlyStep src
  | _ => []

/-- The naive reading's builtin dispatch for the MeTTa-calculus premise builtins. -/
def mettaCalcBuiltinMany (builtin : String) (args : List Pattern) : List Pattern :=
  if builtin == builtinMettaCommWitness then
    mettaCommWitnessBuiltinMany args
  else if builtin == builtinMettaCommOnlyStep then
    mettaCommOnlyStepBuiltinMany args
  else
    []

private def mettaStepNoReflectTuplesFromBuiltin : List Pattern → List (List Pattern)
  | [src, _] =>
      (mettaCalcBuiltinMany builtinMettaCommOnlyStep [src]).map (fun tgt => [src, tgt])
  | _ => []

/-- The naive reading's relation environment. `mettaStepNoReflect` uses COMM-only
stepping to avoid recursive premise self-reference through REFL. -/
def mettaCalcRelEnv : RelationEnv where
  tuples := fun rel args =>
    if rel == relMettaComm then
      mettaCommTuplesFromBuiltin args
    else if rel == relMettaStepNoReflect then
      mettaStepNoReflectTuplesFromBuiltin args
    else
      []

/-- **The naive reading of the step**, not the semantics. It captures
(`MeTTaOperationsComm.Executable.executable_capture`), is not alpha-invariant,
fires a COMM without a unifier (`Corrected.Controls.old_step_fires_without_unifier`)
and has no nested REFL result. Kept for the separating theorems; the semantics
is `Corrected.cstep`. -/
def step (p : Proc) : List Proc :=
  reductsUsing mettaCalcRelEnv mettaCalc executableContextFuel p

/-! ## Canaries of the naive reading

The processes are the shared canaries. `demoCommCapture` and
`demoReflectCapture` are the naive reading's reducts: `@0 | @0` identifies the
second input's free `a` with the first input's bound `a`. The corrected
reducts are `@0 | a` and its listener (`demoCommReduct` and
`demoReflectReduct` in `PaperMap.lean`, `Corrected.Controls.corrected_canary`). The examples below record the naive
reading's behaviour; they are not the semantics. -/

def demoChan : Name := nQuote pZero

def demoCommSource : Proc :=
  pPar [
    pFor (.fvar "a") demoChan (.fvar "a"),
    pFor pZero demoChan (.fvar "a")
  ]

/-- The naive reading's capturing reduct of `demoCommSource`. -/
def demoCommCapture : Proc := pPar [nQuote pZero, nQuote pZero]

def demoBlocked : Proc :=
  pPar [
    pFor pZero demoChan pZero,
    pFor (tSym "Other") demoChan pZero
  ]

def demoReflectSource : Proc := pReflect demoChan demoCommSource

/-- The naive reading's listener for `demoReflectSource`, quoting the capturing reduct. -/
def demoReflectCapture : Proc := pFor (tProc demoCommCapture) demoChan pZero

example : unifyPattern? (.fvar "x") pZero = some [("x", pZero)] := by
  decide +kernel

example : unifyPattern? pZero (tSym "Mismatch") = none := by
  decide +kernel

example : demoCommCapture ∈ step demoCommSource := by
  decide +kernel

example : step demoBlocked = [] := by
  decide +kernel

example : demoReflectCapture ∈ step demoReflectSource := by
  decide +kernel

example : step (pReflect demoChan demoBlocked) = [] := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
