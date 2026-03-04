import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.StructuralCongruence
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RelationNames
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.Languages.ProcessCalculi.Common.Common
import Mathlib.Data.Finset.Basic

/-!
# MeTTa-Calculus Reduction (Executable)

Executable one-step semantics for the symmetric MeTTa-calculus:

- `COMM` uses a lightweight first-order unifier over `Pattern`
- `REFL` uses one-step lookahead in the COMM-only fragment

## Source attribution

Semantics follows:

- `/home/zar/claude/hyperon/rho4u/metta-calculus/metta-calculus.core.tex`

especially:

- `COMM`: `for(t <- x)P | for(u <- x)Q → P·σ | Q·σ`
- `REFL`: `x?P → for((P') <- x)0` when `P → P'`
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine

/-! ## Unification and dot-substitution -/

mutual
def occursFVar (x : String) : Pattern → Bool
  | .bvar _ => false
  | .fvar y => x == y
  | .apply _ args => occursFVarList x args
  | .lambda b => occursFVar x b
  | .multiLambda _ b => occursFVar x b
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
        | .lambda b1, .lambda b2 =>
            unifyLoop fuel ((b1, b2) :: eqs) σ
        | .multiLambda n1 b1, .multiLambda n2 b2 =>
            if n1 == n2 then unifyLoop fuel ((b1, b2) :: eqs) σ else none
        | .subst b1 r1, .subst b2 r2 =>
            unifyLoop fuel ((b1, b2) :: (r1, r2) :: eqs) σ
        | .collection ct1 es1 rest1, .collection ct2 es2 rest2 =>
            if ct1 == ct2 && rest1 == rest2 && es1.length == es2.length then
              unifyLoop fuel (List.zip es1 es2 ++ eqs) σ
            else
              none
        | _, _ => none

/-- Lightweight first-order unification used by `COMM` premise generation. -/
def unifyPattern? (lhs rhs : Pattern) : Option Bindings :=
  -- Fixed fuel keeps this executable even when `Pattern.sizeOf` is noncomputable.
  unifyLoop 256 [(lhs, rhs)] []

/-- Dot-substitution from the paper:
turn variable-to-term bindings into variable-to-name bindings by quoting RHS. -/
def dotBindings (σ : Bindings) : Bindings :=
  σ.map (fun (x, v) => (x, nQuote v))

def applyDot (σ : Bindings) (p : Proc) : Proc :=
  applyBindings (dotBindings σ) p

/-! ## Premise environments for executable COMM/REFL -/

/-- Runtime adapter for premise builtin `mettaCommWitness`.
Returns witness values encoded as `MRef(pOut, qOut)` to match the
`Premises.lean` rule body deconstruction. -/
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

def commOnlyStep (p : Proc) : List Proc :=
  rewriteWithContextWithPremisesUsing commOnlyRelEnv mettaCalcCommOnly p

/-- Runtime adapter for premise builtin `mettaCommOnlyStep`. -/
def mettaCommOnlyStepBuiltinMany : List Pattern → List Pattern
  | [src] => commOnlyStep src
  | _ => []

/-- Runtime builtin-dispatch entry for MeTTa-calculus premise builtins. -/
def mettaCalcBuiltinMany (builtin : String) (args : List Pattern) : List Pattern :=
  if builtin == builtinMettaCommWitness then
    mettaCommWitnessBuiltinMany args
  else if builtin == builtinMettaCommOnlyStep then
    mettaCommOnlyStepBuiltinMany args
  else
    []

/-- Single-result variant of `mettaCalcBuiltinMany`. -/
def mettaCalcBuiltin (builtin : String) (args : List Pattern) : Option Pattern :=
  (mettaCalcBuiltinMany builtin args).head?

private def mettaStepNoReflectTuplesFromBuiltin : List Pattern → List (List Pattern)
  | [src, _] =>
      (mettaCalcBuiltinMany builtinMettaCommOnlyStep [src]).map (fun tgt => [src, tgt])
  | _ => []

/-- Relation environment for full MeTTa-calculus execution.
`mettaStepNoReflect` intentionally uses COMM-only stepping to avoid recursive
premise self-reference through REFL. -/
def mettaCalcRelEnv : RelationEnv where
  tuples := fun rel args =>
    if rel == relMettaComm then
      mettaCommTuplesFromBuiltin args
    else if rel == relMettaStepNoReflect then
      mettaStepNoReflectTuplesFromBuiltin args
    else
      []

def step (p : Proc) : List Proc :=
  rewriteWithContextWithPremisesUsing mettaCalcRelEnv mettaCalc p

/-- Canonicalized one-step results (duplicate-insensitive view). -/
def stepCanonical (p : Proc) : Finset Proc := (step p).toFinset

def Reduces (p q : Proc) : Prop := q ∈ step p

def ReducesCanonical (p q : Proc) : Prop := q ∈ stepCanonical p

notation:50 p " ↦ " q => Reduces p q

notation:50 p " ↦ₙ " q => ReducesCanonical p q

open _root_.ProcessCalculi

abbrev ReducesStar := ProcessCalculi.RTClosureProp Reduces

notation:50 p " ↦* " q => ReducesStar p q

/-- Canonical-step membership is equivalent to raw-step membership. -/
theorem mem_stepCanonical_iff_mem_step {p q : Proc} :
    q ∈ stepCanonical p ↔ q ∈ step p := by
  simp [stepCanonical]

/-- Canonical reduction proposition is equivalent to raw reduction proposition. -/
theorem reducesCanonical_iff_reduces {p q : Proc} :
    ReducesCanonical p q ↔ Reduces p q := by
  simpa [ReducesCanonical, Reduces] using (mem_stepCanonical_iff_mem_step (p := p) (q := q))

/-- Reduction modulo structural congruence. -/
inductive ReducesSC : Proc → Proc → Prop where
  | base (p q : Proc) : Reduces p q → ReducesSC p q
  | equiv (p0 p1 q1 q0 : Proc) :
      SC p0 p1 → ReducesSC p1 q1 → SC q1 q0 → ReducesSC p0 q0

abbrev ReducesSCStar := ProcessCalculi.RTClosureProp ReducesSC

theorem reduces_to_reducesSC {p q : Proc} (h : Reduces p q) : ReducesSC p q :=
  ReducesSC.base p q h

theorem reducesSC_mod {p0 p1 q1 q0 : Proc}
    (hp : SC p0 p1) (h : ReducesSC p1 q1) (hq : SC q1 q0) : ReducesSC p0 q0 :=
  ReducesSC.equiv p0 p1 q1 q0 hp h hq

/-! ## Positive and negative canaries -/

def demoChan : Name := nQuote pZero

def demoCommSource : Proc :=
  pPar [
    pFor (.fvar "a") demoChan (.fvar "a"),
    pFor pZero demoChan (.fvar "a")
  ]

def demoCommTarget : Proc := pPar [nQuote pZero, nQuote pZero]

def demoBlocked : Proc :=
  pPar [
    pFor pZero demoChan pZero,
    pFor (tSym "Other") demoChan pZero
  ]

def demoReflectSource : Proc := pReflect demoChan demoCommSource

def demoReflectTarget : Proc := pFor (tProc demoCommTarget) demoChan pZero

example : unifyPattern? (.fvar "x") pZero = some [("x", pZero)] := by
  native_decide

example : unifyPattern? pZero (tSym "Mismatch") = none := by
  native_decide

example : demoCommTarget ∈ step demoCommSource := by
  native_decide

example : step demoBlocked = [] := by
  native_decide

example : demoReflectTarget ∈ step demoReflectSource := by
  native_decide

example : step (pReflect demoChan demoBlocked) = [] := by
  native_decide

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
