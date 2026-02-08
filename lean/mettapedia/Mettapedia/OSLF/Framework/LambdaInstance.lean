import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Formula

/-!
# Lambda Calculus OSLF Instance

Second example instantiation of the OSLF pipeline, validating that the
generic framework works for languages beyond the ρ-calculus.

## Language Definition

Simple untyped lambda calculus with:
- One sort: `Term`
- Constructors: `App(f, a)`, `Lam(x.body)`
- One rewrite rule: β-reduction `App(Lam(x.body), arg) ~> body[arg/x]`

## Pipeline

```
lambdaCalc : LanguageDef
    ↓ langRewriteSystem
lambdaRS : RewriteSystem
    ↓ langSpan
lambdaSpan : ReductionSpan
    ↓ langOSLF
lambdaOSLF : OSLFTypeSystem  (with proven Galois connection)
```

## Limitations

The generic MeTTaIL engine only provides congruence under collection constructors
(bag/set/vec), not under `.apply` nodes. This means β-reduction only fires at the
top level. Multi-step reduction handles terms where the outermost constructor is a
β-redex, but cannot reduce inner sub-applications without a congruence rule.

## References

- Church, "The Calculi of Lambda Conversion" (1941)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.Framework.LambdaInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Formula

/-! ## Language Definition -/

/-- Simple untyped lambda calculus as a `LanguageDef`.

    - **Types**: `["Term"]`
    - **Constructors**: `App(f, a)`, `Lam(x.body)`
    - **β-reduction**: `App(Lam(x.body), arg) ~> body[arg/x]`

    Free variables use `Pattern.fvar`, bound variables use `Pattern.bvar`
    (locally nameless representation). -/
def lambdaCalc : LanguageDef := {
  name := "LambdaCalc",
  types := ["Term"],
  terms := [
    -- App . f:Term, a:Term |- f " " a : Term
    { label := "App", category := "Term",
      params := [.simple "f" (.base "Term"), .simple "a" (.base "Term")],
      syntaxPattern := [.nonTerminal "f", .nonTerminal "a"] },
    -- Lam . ^x.body:[Term -> Term] |- "λ" x "." body : Term
    { label := "Lam", category := "Term",
      params := [.abstraction "body" (.arrow (.base "Term") (.base "Term"))],
      syntaxPattern := [.terminal "λ", .nonTerminal "x", .terminal ".", .nonTerminal "body"] }
  ],
  equations := [],
  rewrites := [
    -- β-reduction: App(Lam(x.body), arg) ~> body[arg/x]
    { name := "Beta",
      typeContext := [("body", .base "Term"), ("arg", .base "Term")],
      premises := [],
      left := .apply "App" [.apply "Lam" [.lambda (.fvar "body")], .fvar "arg"],
      right := .subst (.fvar "body") (.fvar "arg") }
  ]
}

/-! ## OSLF Pipeline Instantiation -/

/-- The OSLF type system for lambda calculus.
    Galois connection ◇ ⊣ □ is proven automatically. -/
def lambdaOSLF := langOSLF lambdaCalc "Term"

/-- The Galois connection for lambda calculus. -/
theorem lambdaGalois :
    GaloisConnection (langDiamond lambdaCalc) (langBox lambdaCalc) :=
  langGalois lambdaCalc

/-! ## Helper Constructors -/

/-- Application: `f a` -/
private def app (f a : Pattern) : Pattern := .apply "App" [f, a]

/-- Lambda abstraction: `λ.body` (locally nameless: bound var is BVar 0) -/
private def lam (body : Pattern) : Pattern :=
  .apply "Lam" [.lambda body]

/-- Simple display for lambda terms -/
private partial def termToString : Pattern → String
  | .fvar x => x
  | .bvar n => s!"#{n}"
  | .apply "App" [f, a] => "(" ++ termToString f ++ " " ++ termToString a ++ ")"
  | .apply "Lam" [.lambda body] => "(λ." ++ termToString body ++ ")"
  | p => repr p |>.pretty

private instance : ToString Pattern := ⟨termToString⟩

/-! ## Executable Demos -/

-- Demo 1: Identity — (λ.#0) 0 ~> 0
#eval! do
  let zero := Pattern.fvar "0"
  let term := app (lam (.bvar 0)) zero
  let reducts := rewriteWithContext lambdaCalc term
  IO.println s!"Demo 1: (λ.#0) 0"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 2: K combinator — (λ.λ.#1) 0 ~> λ.0
#eval! do
  let zero := Pattern.fvar "0"
  let term := app (lam (lam (.bvar 1))) zero
  let reducts := rewriteWithContext lambdaCalc term
  IO.println s!"Demo 2: (λ.λ.#1) 0"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 3: Multi-step — (λ.#0) ((λ.#0) 0) ~>* 0
#eval! do
  let zero := Pattern.fvar "0"
  let inner := app (lam (.bvar 0)) zero
  let term := app (lam (.bvar 0)) inner
  let nf := fullRewriteToNormalForm lambdaCalc term 100
  IO.println s!"Demo 3: (λ.#0) ((λ.#0) 0)"
  IO.println s!"  normal form: {nf}"

-- Demo 4: Self-application — (λ.#0 #0) a ~> a a
#eval! do
  let a := Pattern.fvar "a"
  let term := app (lam (app (.bvar 0) (.bvar 0))) a
  let reducts := rewriteWithContext lambdaCalc term
  IO.println s!"Demo 4: (λ.#0 #0) a"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 5: Formula checker — can (λ.#0) 0 reduce? (◇⊤ should be sat)
#eval! do
  let zero := Pattern.fvar "0"
  let term := app (lam (.bvar 0)) zero
  let noAtoms : AtomCheck := fun _ _ => false
  let result := check (rewriteWithContext lambdaCalc) noAtoms 50 term (.dia .top)
  IO.println s!"Demo 5: Can (λ.#0) 0 reduce?"
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 6: Normal form can't reduce (◇⊤ should be unsat)
#eval! do
  let zero := Pattern.fvar "0"
  let noAtoms : AtomCheck := fun _ _ => false
  let result := check (rewriteWithContext lambdaCalc) noAtoms 50 zero (.dia .top)
  IO.println s!"Demo 6: Can 0 reduce?"
  IO.println s!"  check (◇⊤) = {result}"

/-! ## Locally Nameless Correctness Canaries

In locally nameless representation, binder capture is impossible by construction.
These tests verify that previously-problematic cases now reduce correctly. -/

-- Canary 7: K combinator with inner binder — (λ.λ.#1) 0 ~> λ.0
-- In the old named representation, this triggered a capture bug.
-- In locally nameless, BVar 1 correctly refers to the outer binder.
#eval! do
  let zero := Pattern.fvar "0"
  -- (λ.λ.#1) where #1 is the outer bound var
  let term := app (lam (lam (.bvar 1))) zero
  let reducts := rewriteWithContext lambdaCalc term
  IO.println s!"Canary 7: (λ.λ.#1) 0 — formerly-buggy K combinator"
  IO.println s!"  reducts ({reducts.length}): expected 1 (capture impossible in LN)"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Canary 8: Simple identity — (λ.#0) 0 ~> 0
#eval! do
  let zero := Pattern.fvar "0"
  let term := app (lam (.bvar 0)) zero
  let reducts := rewriteWithContext lambdaCalc term
  IO.println s!"Canary 8: (λ.#0) 0 — identity"
  IO.println s!"  reducts ({reducts.length}): expected 1"
  for r in reducts do
    IO.println s!"    -> {r}"
  assert! reducts.length == 1

-- Canary 9 (proven): identity ≠ constant function (structural inequality)
theorem identity_neq_constant :
    -- Identity: λ.#0
    let identity := lam (.bvar 0)
    -- Constant: λ.a (returns free variable "a")
    let constant := lam (.fvar "a")
    identity ≠ constant := by
  simp only [lam]
  decide

-- Verification: OSLF pipeline type-checks
#check lambdaOSLF
#check lambdaGalois

end Mettapedia.OSLF.Framework.LambdaInstance
