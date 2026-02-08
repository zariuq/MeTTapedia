import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Formula

/-!
# TinyML OSLF Instance

Fourth example instantiation of the OSLF pipeline: a call-by-value
λ-calculus with booleans, pairs, and thunks. Exercises the full
OSLF→GSLT categorical bridge with:

- **Two sorts**: `Expr`, `Val`
- **Two sort-crossing constructors**: `Inject : Val → Expr`, `Thunk : Expr → Val`
- **Six reduction rules**: β, force, ifTrue, ifFalse, fstPair, sndPair

## Sort Structure

```
        Thunk
  Expr ←———— Val
    |            ↑
    |  Inject    |
    +————————→   +
```

This mirrors the ρ-calculus NQuote/PDrop structure:
- `Thunk : Expr → Val` (quoting: freezes an expression as a value, like NQuote)
- `Inject : Val → Expr` (reflecting: injects a value into expression, like PDrop)

## Typing Actions (from DerivedTyping)

- `Thunk` (domain = Expr = procSort): **quoting** → introduces ◇
- `Inject` (codomain = Expr = procSort): **reflecting** → introduces □
- `Thunk ∘ Inject` (Val→Val): □ ∘ ◇
- `Inject ∘ Thunk` (Expr→Expr): ◇ ∘ □

## Language Summary

```
Expr ::= App(f:Expr, a:Expr)           -- application
       | If(c:Expr, t:Expr, e:Expr)    -- conditional
       | Fst(e:Expr) | Snd(e:Expr)     -- projections
       | Inject(v:Val)                 -- value injection
Val  ::= BoolT | BoolF                 -- boolean literals
       | Lam(^body:[Val→Expr])          -- CBV lambda
       | PairV(a:Val, b:Val)            -- pair
       | Thunk(e:Expr)                 -- delayed expression
```

## Reduction Rules (CBV)

```
β:        App(Inject(Lam(^body)), Inject(v)) ~> body[v/x]
Force:    Inject(Thunk(e))                   ~> e
IfTrue:   If(Inject(BoolT), t, e)            ~> t
IfFalse:  If(Inject(BoolF), t, e)            ~> e
FstPair:  Fst(Inject(PairV(a, b)))           ~> Inject(a)
SndPair:  Snd(Inject(PairV(a, b)))           ~> Inject(b)
```

The CBV strategy is encoded syntactically: β-reduction requires both the
function and argument to be wrapped in `Inject(-)`, ensuring arguments
are evaluated to values before substitution.

## References

- Plotkin, "Call-by-name, call-by-value and the lambda-calculus" (1975)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.Framework.TinyMLInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.ConstructorFibration
open Mettapedia.OSLF.Framework.ModalEquivalence
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.OSLF.Formula

/-! ## Language Definition -/

/-- TinyML: a call-by-value λ-calculus with booleans, pairs, and thunks.

    - **Sorts**: `["Expr", "Val"]`
    - **Expr constructors**: `App`, `If`, `Fst`, `Snd`, `Inject` (Val→Expr)
    - **Val constructors**: `BoolT`, `BoolF`, `Lam`, `PairV`, `Thunk` (Expr→Val)
    - **Reductions**: β, force, ifTrue, ifFalse, fstPair, sndPair -/
def tinyML : LanguageDef := {
  name := "TinyML",
  types := ["Expr", "Val"],
  terms := [
    -- App . f:Expr, a:Expr |- f " " a : Expr
    { label := "App", category := "Expr",
      params := [.simple "f" (.base "Expr"), .simple "a" (.base "Expr")],
      syntaxPattern := [.nonTerminal "f", .nonTerminal "a"] },
    -- If . c:Expr, t:Expr, e:Expr |- "if" c "then" t "else" e : Expr
    { label := "If", category := "Expr",
      params := [.simple "c" (.base "Expr"), .simple "t" (.base "Expr"),
                 .simple "e" (.base "Expr")],
      syntaxPattern := [.terminal "if", .nonTerminal "c", .terminal "then",
                        .nonTerminal "t", .terminal "else", .nonTerminal "e"] },
    -- Fst . e:Expr |- "fst" e : Expr
    { label := "Fst", category := "Expr",
      params := [.simple "e" (.base "Expr")],
      syntaxPattern := [.terminal "fst", .nonTerminal "e"] },
    -- Snd . e:Expr |- "snd" e : Expr
    { label := "Snd", category := "Expr",
      params := [.simple "e" (.base "Expr")],
      syntaxPattern := [.terminal "snd", .nonTerminal "e"] },
    -- Inject . v:Val |- v : Expr  (sort crossing: Val → Expr)
    { label := "Inject", category := "Expr",
      params := [.simple "v" (.base "Val")],
      syntaxPattern := [.nonTerminal "v"] },
    -- BoolT . |- "true" : Val
    { label := "BoolT", category := "Val", params := [],
      syntaxPattern := [.terminal "true"] },
    -- BoolF . |- "false" : Val
    { label := "BoolF", category := "Val", params := [],
      syntaxPattern := [.terminal "false"] },
    -- Lam . ^body:[Val→Expr] |- "λ" "." body : Val
    { label := "Lam", category := "Val",
      params := [.abstraction "body" (.arrow (.base "Val") (.base "Expr"))],
      syntaxPattern := [.terminal "λ", .terminal ".", .nonTerminal "body"] },
    -- PairV . a:Val, b:Val |- "(" a "," b ")" : Val
    { label := "PairV", category := "Val",
      params := [.simple "a" (.base "Val"), .simple "b" (.base "Val")],
      syntaxPattern := [.terminal "(", .nonTerminal "a", .terminal ",",
                        .nonTerminal "b", .terminal ")"] },
    -- Thunk . e:Expr |- "thunk" e : Val  (sort crossing: Expr → Val)
    { label := "Thunk", category := "Val",
      params := [.simple "e" (.base "Expr")],
      syntaxPattern := [.terminal "thunk", .nonTerminal "e"] }
  ],
  equations := [],
  rewrites := [
    -- β: App(Inject(Lam(^body)), Inject(v)) ~> body[v/x]
    { name := "Beta",
      typeContext := [("body", .base "Expr"), ("v", .base "Val")],
      premises := [],
      left := .apply "App" [.apply "Inject" [.apply "Lam" [.lambda (.fvar "body")]],
                             .apply "Inject" [.fvar "v"]],
      right := .subst (.fvar "body") (.fvar "v") },
    -- Force: Inject(Thunk(e)) ~> e
    { name := "Force",
      typeContext := [("e", .base "Expr")],
      premises := [],
      left := .apply "Inject" [.apply "Thunk" [.fvar "e"]],
      right := .fvar "e" },
    -- IfTrue: If(Inject(BoolT), t, e) ~> t
    { name := "IfTrue",
      typeContext := [("t", .base "Expr"), ("e", .base "Expr")],
      premises := [],
      left := .apply "If" [.apply "Inject" [.apply "BoolT" []], .fvar "t", .fvar "e"],
      right := .fvar "t" },
    -- IfFalse: If(Inject(BoolF), t, e) ~> e
    { name := "IfFalse",
      typeContext := [("t", .base "Expr"), ("e", .base "Expr")],
      premises := [],
      left := .apply "If" [.apply "Inject" [.apply "BoolF" []], .fvar "t", .fvar "e"],
      right := .fvar "e" },
    -- FstPair: Fst(Inject(PairV(a, b))) ~> Inject(a)
    { name := "FstPair",
      typeContext := [("a", .base "Val"), ("b", .base "Val")],
      premises := [],
      left := .apply "Fst" [.apply "Inject" [.apply "PairV" [.fvar "a", .fvar "b"]]],
      right := .apply "Inject" [.fvar "a"] },
    -- SndPair: Snd(Inject(PairV(a, b))) ~> Inject(b)
    { name := "SndPair",
      typeContext := [("a", .base "Val"), ("b", .base "Val")],
      premises := [],
      left := .apply "Snd" [.apply "Inject" [.apply "PairV" [.fvar "a", .fvar "b"]]],
      right := .apply "Inject" [.fvar "b"] }
  ]
}

/-! ## OSLF Pipeline Instantiation -/

/-- The OSLF type system for TinyML (Expr is the process sort).
    Galois connection ◇ ⊣ □ is proven automatically. -/
def tinyMLOSLF := langOSLF tinyML "Expr"

/-- The Galois connection for TinyML. -/
theorem tinyMLGalois :
    GaloisConnection (langDiamond tinyML) (langBox tinyML) :=
  langGalois tinyML

/-! ## Constructor Category Instantiation -/

/-- The Expr sort object in TinyML's constructor category. -/
def tinyExpr : LangSort tinyML := ⟨"Expr", by decide⟩

/-- The Val sort object in TinyML's constructor category. -/
def tinyVal : LangSort tinyML := ⟨"Val", by decide⟩

/-- TinyML has exactly 2 sort-crossing constructors: Inject and Thunk. -/
theorem tinyML_crossings :
    unaryCrossings tinyML = [("Inject", "Val", "Expr"), ("Thunk", "Expr", "Val")] := by
  native_decide

/-- The Inject arrow: Val → Expr. -/
def injectArrow : SortArrow tinyML tinyVal tinyExpr :=
  ⟨"Inject", by native_decide⟩

/-- The Thunk arrow: Expr → Val. -/
def thunkArrow : SortArrow tinyML tinyExpr tinyVal :=
  ⟨"Thunk", by native_decide⟩

/-- The ConstructorObj wrapper for Expr. -/
def tinyExprObj : ConstructorObj tinyML := ⟨tinyExpr⟩

/-- The ConstructorObj wrapper for Val. -/
def tinyValObj : ConstructorObj tinyML := ⟨tinyVal⟩

/-- Inject morphism in the constructor category. -/
def injectMor : tinyValObj ⟶ tinyExprObj :=
  injectArrow.toPath

/-- Thunk morphism in the constructor category. -/
def thunkMor : tinyExprObj ⟶ tinyValObj :=
  thunkArrow.toPath

/-! ## Constructor Semantics -/

/-- Inject's semantic function: wraps a pattern in `Inject(-)`. -/
theorem inject_sem (p : Pattern) :
    arrowSem tinyML injectArrow p = .apply "Inject" [p] := rfl

/-- Thunk's semantic function: wraps a pattern in `Thunk(-)`. -/
theorem thunk_sem (p : Pattern) :
    arrowSem tinyML thunkArrow p = .apply "Thunk" [p] := rfl

/-- Thunk∘Inject semantic: `Thunk(Inject(-))`. -/
theorem thunkInject_sem (p : Pattern) :
    pathSem tinyML (SortPath.cons injectMor thunkArrow) p =
    .apply "Thunk" [.apply "Inject" [p]] := rfl

/-- Inject∘Thunk semantic: `Inject(Thunk(-))`. -/
theorem injectThunk_sem (p : Pattern) :
    pathSem tinyML (SortPath.cons thunkMor injectArrow) p =
    .apply "Inject" [.apply "Thunk" [p]] := rfl

/-! ## Change-of-Base -/

/-- Inject pullback: pull Expr predicates back to Val.
    `Inject*(φ)(v) = φ(Inject(v))` -/
example (φ : Pattern → Prop) (v : Pattern) :
    constructorPullback tinyML injectMor φ v =
    φ (.apply "Inject" [v]) := rfl

/-- Thunk pullback: pull Val predicates back to Expr.
    `Thunk*(α)(e) = α(Thunk(e))` -/
example (α : Pattern → Prop) (e : Pattern) :
    constructorPullback tinyML thunkMor α e =
    α (.apply "Thunk" [e]) := rfl

/-- Inject direct image: push Val predicates forward to Expr.
    `∃_Inject(α)(q) = ∃ v, Inject(v) = q ∧ α(v)` -/
example (α : Pattern → Prop) (q : Pattern) :
    constructorDirectImage tinyML injectMor α q =
    (∃ v, Pattern.apply "Inject" [v] = q ∧ α v) := rfl

/-- Thunk direct image: push Expr predicates forward to Val.
    `∃_Thunk(φ)(q) = ∃ e, Thunk(e) = q ∧ φ(e)` -/
example (φ : Pattern → Prop) (q : Pattern) :
    constructorDirectImage tinyML thunkMor φ q =
    (∃ e, Pattern.apply "Thunk" [e] = q ∧ φ e) := rfl

/-- Adjunction: `∃_Inject ⊣ Inject*`. -/
theorem inject_di_pb_adj :
    GaloisConnection (constructorDirectImage tinyML injectMor)
                     (constructorPullback tinyML injectMor) :=
  constructorDiPbAdj tinyML injectMor

/-- Adjunction: `∃_Thunk ⊣ Thunk*`. -/
theorem thunk_di_pb_adj :
    GaloisConnection (constructorDirectImage tinyML thunkMor)
                     (constructorPullback tinyML thunkMor) :=
  constructorDiPbAdj tinyML thunkMor

/-! ## Typing Actions (from DerivedTyping) -/

/-- Thunk is classified as **quoting** (domain = Expr = procSort).
    Introduces ◇ (diamond). -/
theorem thunk_is_quoting :
    classifyArrow tinyML "Expr" thunkArrow = .quoting := by
  simp [classifyArrow, tinyExpr]

/-- Inject is classified as **reflecting** (codomain = Expr = procSort).
    Introduces □ (box). -/
theorem inject_is_reflecting :
    classifyArrow tinyML "Expr" injectArrow = .reflecting := by
  simp only [classifyArrow, tinyVal]
  decide

/-- Thunk typing action = ◇ (diamond).
    When `e : (Expr, φ)`, the typing rule gives `thunk(e) : (Val, ◇φ)`. -/
theorem thunk_action_eq_diamond (φ : Pattern → Prop) :
    typingAction tinyML "Expr" thunkArrow φ = langDiamond tinyML φ := by
  simp [typingAction, thunk_is_quoting, roleAction]

/-- Inject typing action = □ (box).
    When `v : (Val, α)`, the typing rule gives `inject(v) : (Expr, □α)`. -/
theorem inject_action_eq_box (α : Pattern → Prop) :
    typingAction tinyML "Expr" injectArrow α = langBox tinyML α := by
  simp [typingAction, inject_is_reflecting, roleAction]

/-- The Galois connection between Thunk and Inject typing actions: ◇ ⊣ □.
    Analogous to the ρ-calculus NQuote/PDrop Galois pair. -/
theorem tinyML_typing_action_galois :
    GaloisConnection
      (typingAction tinyML "Expr" thunkArrow)
      (typingAction tinyML "Expr" injectArrow) := by
  simp only [funext (thunk_action_eq_diamond), funext (inject_action_eq_box)]
  exact tinyMLGalois

/-! ## Helper Constructors -/

private def app (f a : Pattern) : Pattern := .apply "App" [f, a]
private def ite (c t e : Pattern) : Pattern := .apply "If" [c, t, e]
private def fst (e : Pattern) : Pattern := .apply "Fst" [e]
private def snd (e : Pattern) : Pattern := .apply "Snd" [e]
private def inject (v : Pattern) : Pattern := .apply "Inject" [v]
private def boolT : Pattern := .apply "BoolT" []
private def boolF : Pattern := .apply "BoolF" []
private def lam (body : Pattern) : Pattern := .apply "Lam" [.lambda body]
private def pairV (a b : Pattern) : Pattern := .apply "PairV" [a, b]
private def thunk (e : Pattern) : Pattern := .apply "Thunk" [e]

/-- Display for TinyML terms -/
private partial def exprToString : Pattern → String
  | .fvar x => x
  | .bvar n => s!"#{n}"
  | .apply "App" [f, a] => "(" ++ exprToString f ++ " " ++ exprToString a ++ ")"
  | .apply "If" [c, t, e] =>
    "(if " ++ exprToString c ++ " then " ++ exprToString t ++ " else " ++ exprToString e ++ ")"
  | .apply "Fst" [e] => "(fst " ++ exprToString e ++ ")"
  | .apply "Snd" [e] => "(snd " ++ exprToString e ++ ")"
  | .apply "Inject" [v] => exprToString v
  | .apply "BoolT" [] => "true"
  | .apply "BoolF" [] => "false"
  | .apply "Lam" [.lambda body] => "(λ." ++ exprToString body ++ ")"
  | .apply "PairV" [a, b] => "(" ++ exprToString a ++ ", " ++ exprToString b ++ ")"
  | .apply "Thunk" [e] => "(thunk " ++ exprToString e ++ ")"
  | p => repr p |>.pretty

private instance : ToString Pattern := ⟨exprToString⟩

/-! ## Executable Demos -/

-- Demo 1: β-reduction — (λ.#0) true ~> true
#eval! do
  let term := app (inject (lam (.bvar 0))) (inject boolT)
  let reducts := rewriteWithContext tinyML term
  IO.println "Demo 1: (λ.#0) true  [identity applied to true]"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 2: Force — inject(thunk(e)) ~> e
#eval! do
  let e := app (inject boolT) (inject boolF)
  let term := inject (thunk e)
  let reducts := rewriteWithContext tinyML term
  IO.println "Demo 2: inject(thunk(true false))  [force a thunk]"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 3: If-true — if true then a else b ~> a
#eval! do
  let a := inject (lam (.bvar 0))
  let b := inject boolF
  let term := ite (inject boolT) a b
  let reducts := rewriteWithContext tinyML term
  IO.println "Demo 3: if true then (λ.#0) else false"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 4: If-false — if false then a else b ~> b
#eval! do
  let a := inject boolT
  let b := inject boolF
  let term := ite (inject boolF) a b
  let reducts := rewriteWithContext tinyML term
  IO.println "Demo 4: if false then true else false"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 5: Fst projection — fst (a, b) ~> inject(a)
#eval! do
  let term := fst (inject (pairV boolT boolF))
  let reducts := rewriteWithContext tinyML term
  IO.println "Demo 5: fst (true, false)"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 6: Snd projection — snd (a, b) ~> inject(b)
#eval! do
  let term := snd (inject (pairV boolT boolF))
  let reducts := rewriteWithContext tinyML term
  IO.println "Demo 6: snd (true, false)"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Demo 7: Force then β — inject(thunk(app(inject(λ.#0), inject(true)))) ~>* true
-- Step 1: force fires at top level, yielding app(inject(λ.#0), inject(true))
-- Step 2: β fires at top level, yielding true
#eval! do
  let inner := app (inject (lam (.bvar 0))) (inject boolT)
  let term := inject (thunk inner)
  let nf := fullRewriteToNormalForm tinyML term 100
  IO.println "Demo 7: inject(thunk((λ.#0) true)) ~>* true  [force then β]"
  IO.println s!"  normal form: {nf}"

-- Demo 8: IfTrue then β — if true then (λ.#0) false else true ~>* false
-- Step 1: ifTrue fires, yielding app(inject(λ.#0), inject(false))
-- Step 2: β fires, yielding false
#eval! do
  let thenBranch := app (inject (lam (.bvar 0))) (inject boolF)
  let term := ite (inject boolT) thenBranch (inject boolT)
  let nf := fullRewriteToNormalForm tinyML term 100
  IO.println "Demo 8: if true then ((λ.#0) false) else true ~>* false  [if then β]"
  IO.println s!"  normal form: {nf}"

-- Demo 9: Three-step chain — inject(thunk(if true then fst(true, false) else false)) ~>* true
-- Step 1: force → if true then fst(inject(true, false)) else inject(false)
-- Step 2: ifTrue → fst(inject(true, false))
-- Step 3: fstPair → inject(true)
#eval! do
  let body := ite (inject boolT) (fst (inject (pairV boolT boolF))) (inject boolF)
  let term := inject (thunk body)
  let nf := fullRewriteToNormalForm tinyML term 100
  IO.println "Demo 9: inject(thunk(if true then fst(true,false) else false)) ~>* true"
  IO.println s!"  normal form: {nf}"

-- Demo 10: Formula checker — can (λ.#0) true reduce? (◇⊤ should be sat)
#eval! do
  let term := app (inject (lam (.bvar 0))) (inject boolT)
  let noAtoms : AtomCheck := fun _ _ => false
  let result := check (rewriteWithContext tinyML) noAtoms 50 term (.dia .top)
  IO.println "Demo 10: Can (λ.#0) true reduce?"
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 11: Normal form can't reduce (◇⊤ should be unsat)
#eval! do
  let noAtoms : AtomCheck := fun _ _ => false
  let result := check (rewriteWithContext tinyML) noAtoms 50 (inject boolT) (.dia .top)
  IO.println "Demo 11: Can inject(true) reduce?"
  IO.println s!"  check (◇⊤) = {result}"

/-! ## Structural Theorems -/

/-- Boolean values are distinct. -/
theorem boolT_ne_boolF : boolT ≠ boolF := by decide

/-- inject(true) is a normal form: no reductions apply. -/
theorem inject_boolT_is_nf :
    rewriteWithContext tinyML (inject boolT) = [] := by native_decide

/-- inject(false) is a normal form. -/
theorem inject_boolF_is_nf :
    rewriteWithContext tinyML (inject boolF) = [] := by native_decide

/-- β-reduction fires on `(λ.#0) true`. -/
theorem beta_fires :
    (rewriteWithContext tinyML
      (app (inject (lam (.bvar 0))) (inject boolT))).length = 1 := by
  native_decide

/-- Force fires on `inject(thunk(inject(true)))`. -/
theorem force_fires :
    (rewriteWithContext tinyML
      (inject (thunk (inject boolT)))).length = 1 := by
  native_decide

/-- IfTrue fires when condition is inject(BoolT). -/
theorem ifTrue_fires :
    (rewriteWithContext tinyML
      (ite (inject boolT) (inject boolT) (inject boolF))).length = 1 := by
  native_decide

/-- FstPair fires on fst(inject(pairV(true, false))). -/
theorem fstPair_fires :
    (rewriteWithContext tinyML
      (fst (inject (pairV boolT boolF)))).length = 1 := by
  native_decide

/-! ## Pipeline Verification -/

-- All pipeline components type-check
#check tinyMLOSLF
#check tinyMLGalois
#check tinyML_crossings
#check inject_di_pb_adj
#check thunk_di_pb_adj
#check tinyML_typing_action_galois

/-! ## Comparison with ρ-Calculus

| TinyML           | ρ-Calculus       | Role                    |
|------------------|------------------|-------------------------|
| Expr             | Proc             | Process sort (reduces)  |
| Val              | Name             | Data sort               |
| Thunk : Expr→Val | NQuote : Proc→Name | Quoting (introduces ◇) |
| Inject : Val→Expr| PDrop : Name→Proc | Reflecting (introduces □)|
| β-reduction      | COMM rule        | Main computation rule   |
| Force            | Quote-Drop       | Quoting/reflecting cancel|
| If/Fst/Snd       | PAR congruence   | Structural reductions   |

The key structural parallel is:
- `inject(thunk(e)) ~> e` in TinyML ↔ `*(@ p) ~> p` in ρ-calculus
- Both are instances of the Galois connection ◇ ⊣ □ at the typing level
-/

end Mettapedia.OSLF.Framework.TinyMLInstance
