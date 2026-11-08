import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramTranslation

/-!
# The source core of expression execution, and its rules

A small untyped source language over S-expressions, with a reference semantics (`Step`) on
multisets of rows. Variables are de Bruijn indices; names are display.

* **Expressions**: `var i`, `lam b`, `app f a`, `let_ s b` (lexical: `s` in the enclosing scope, `b`
  sees its value at index `0`, which shadows), `quote c` (inert data capturing its scope),
  `activate e`, `atom d`, `amb l r` (choice), `add e` and `remove e` (effects on fact rows),
  `await k` (suspend the continuation under the name `k`), `demandE k e` (demand `k` with a value),
  `call k` (run the current definition of `k`) and `redefine k u c` (install version `u` of `k`).
* **Values**: closures `clo b ρ`, quoted code `code c ρ`, atoms `atom d`.
* **Rows**: threads `ev e ρ κ` and `ret v κ`; facts `fact v`; suspended continuations `susp k κ`;
  demands `demand k v`; definitions `defn k u c` (name, version, closed code); citations `cite k u`.

The reference semantics is an environment machine (Landin's SECD, Felleisen–Friedman's CEK) over
the multiset of rows. Application uses the closure's captured scope; a let binds one value, seen by
every use; a choice is one step; facts are added and removed immediately; a demand resumes a
suspended continuation by taking the demand and reading the continuation; a call reads the current
definition and leaves a citation of the version it used.

**Its rules** are a family of schemas (`schema`), well formed (`schema_wellFormed`), and they
present the reference semantics exactly (`step_iff_rewrites`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation

/-! ## Tagged S-expressions and patterns -/

def t0 (k : ℕ) : Sx := .sym k
def t1 (k : ℕ) (a : Sx) : Sx := .cell (.sym k) a
def t2 (k : ℕ) (a b : Sx) : Sx := .cell (.sym k) (.cell a b)
def t3 (k : ℕ) (a b c : Sx) : Sx := .cell (.sym k) (.cell a (.cell b c))

def p0 (k : ℕ) : Pat := .sym k
def p1 (k : ℕ) (a : Pat) : Pat := .cell (.sym k) a
def p2 (k : ℕ) (a b : Pat) : Pat := .cell (.sym k) (.cell a b)
def p3 (k : ℕ) (a b c : Pat) : Pat := .cell (.sym k) (.cell a (.cell b c))

/-! ## Syntax -/

-- indices
def zero : Sx := t0 3
def succ (i : Sx) : Sx := t1 4 i
-- expressions
def var (i : Sx) : Sx := t1 2 i
def lam (b : Sx) : Sx := t1 5 b
def app (f a : Sx) : Sx := t2 6 f a
def let_ (s b : Sx) : Sx := t2 7 s b
def quote (c : Sx) : Sx := t1 8 c
def activate (e : Sx) : Sx := t1 9 e
/-- An atom: as an expression it evaluates to itself, as a value it is data. -/
def atom (d : Sx) : Sx := t1 10 d
def amb (l r : Sx) : Sx := t2 11 l r
def add (e : Sx) : Sx := t1 12 e
def remove (e : Sx) : Sx := t1 13 e
def await (k : Sx) : Sx := t1 14 k
def demandE (k e : Sx) : Sx := t2 15 k e
def call (k : Sx) : Sx := t1 16 k
def redefine (k u c : Sx) : Sx := t3 17 k u c
-- values
def clo (b ρ : Sx) : Sx := t2 18 b ρ
def code (c ρ : Sx) : Sx := t2 19 c ρ
-- scopes and continuations
def nil : Sx := t0 20
def cons (v ρ : Sx) : Sx := t2 21 v ρ
-- frames
def appL (a ρ : Sx) : Sx := t2 22 a ρ
def appR (v : Sx) : Sx := t1 23 v
def letK (b ρ : Sx) : Sx := t2 24 b ρ
def actK : Sx := t0 25
def addK : Sx := t0 26
def removeK : Sx := t0 27
def demandK (k : Sx) : Sx := t1 28 k
-- rows
def ev (e ρ κ : Sx) : Sx := t3 29 e ρ κ
def ret (v κ : Sx) : Sx := t2 30 v κ
def fact (v : Sx) : Sx := t1 31 v
def susp (k κ : Sx) : Sx := t2 32 k κ
def demand (k v : Sx) : Sx := t2 33 k v
def defn (k u c : Sx) : Sx := t3 34 k u c
def cite (k u : Sx) : Sx := t2 35 k u

/-! ## The reference semantics -/

/-- **The reference semantics**: one machine step on the multiset of rows. -/
inductive Step : Multiset Sx → Multiset Sx → Prop
  | varZero (v ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (var zero) (cons v ρ) κ ::ₘ W) (ret v κ ::ₘ W)
  | varSucc (i v ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (var (succ i)) (cons v ρ) κ ::ₘ W) (ev (var i) ρ κ ::ₘ W)
  | lam (b ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (lam b) ρ κ ::ₘ W) (ret (clo b ρ) κ ::ₘ W)
  | app (f a ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (app f a) ρ κ ::ₘ W) (ev f ρ (cons (appL a ρ) κ) ::ₘ W)
  | appL (v a ρ κ : Sx) (W : Multiset Sx) :
      Step (ret v (cons (appL a ρ) κ) ::ₘ W) (ev a ρ (cons (appR v) κ) ::ₘ W)
  | beta (v b ρ κ : Sx) (W : Multiset Sx) :
      Step (ret v (cons (appR (clo b ρ)) κ) ::ₘ W) (ev b (cons v ρ) κ ::ₘ W)
  | let_ (s b ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (let_ s b) ρ κ ::ₘ W) (ev s ρ (cons (letK b ρ) κ) ::ₘ W)
  | letK (v b ρ κ : Sx) (W : Multiset Sx) :
      Step (ret v (cons (letK b ρ) κ) ::ₘ W) (ev b (cons v ρ) κ ::ₘ W)
  | quote (c ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (quote c) ρ κ ::ₘ W) (ret (code c ρ) κ ::ₘ W)
  | activate (e ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (activate e) ρ κ ::ₘ W) (ev e ρ (cons actK κ) ::ₘ W)
  | activateK (c ρ κ : Sx) (W : Multiset Sx) :
      Step (ret (code c ρ) (cons actK κ) ::ₘ W) (ev c ρ κ ::ₘ W)
  | atom (d ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (atom d) ρ κ ::ₘ W) (ret (atom d) κ ::ₘ W)
  | ambL (l r ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (amb l r) ρ κ ::ₘ W) (ev l ρ κ ::ₘ W)
  | ambR (l r ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (amb l r) ρ κ ::ₘ W) (ev r ρ κ ::ₘ W)
  | add (e ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (add e) ρ κ ::ₘ W) (ev e ρ (cons addK κ) ::ₘ W)
  | addK (v κ : Sx) (W : Multiset Sx) :
      Step (ret v (cons addK κ) ::ₘ W) (ret v κ ::ₘ fact v ::ₘ W)
  | remove (e ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (remove e) ρ κ ::ₘ W) (ev e ρ (cons removeK κ) ::ₘ W)
  | removeK (v κ : Sx) (W : Multiset Sx) :
      Step (ret v (cons removeK κ) ::ₘ fact v ::ₘ W) (ret v κ ::ₘ W)
  | await (k ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (await k) ρ κ ::ₘ W) (susp k κ ::ₘ W)
  | demand (k e ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (demandE k e) ρ κ ::ₘ W) (ev e ρ (cons (demandK k) κ) ::ₘ W)
  | demandK (v k κ : Sx) (W : Multiset Sx) :
      Step (ret v (cons (demandK k) κ) ::ₘ W) (ret v κ ::ₘ demand k v ::ₘ W)
  | resume (k v κ : Sx) (W : Multiset Sx) :
      Step (demand k v ::ₘ susp k κ ::ₘ W) (ret v κ ::ₘ susp k κ ::ₘ W)
  | call (k u c ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (call k) ρ κ ::ₘ defn k u c ::ₘ W) (ev c nil κ ::ₘ cite k u ::ₘ defn k u c ::ₘ W)
  | redefine (k u c u₀ c₀ ρ κ : Sx) (W : Multiset Sx) :
      Step (ev (redefine k u c) ρ κ ::ₘ defn k u₀ c₀ ::ₘ W) (ret (atom u) κ ::ₘ defn k u c ::ₘ W)

/-! ## The rules as schemas -/

/-- The rules of the source core. -/
inductive RuleName where
  | varZero | varSucc | lam | app | appL | beta | let_ | letK | quote | activate | activateK
  | atom | ambL | ambR | add | addK | remove | removeK | await | demand | demandK | resume
  | call | redefine
  deriving DecidableEq

section Patterns


private def x0 : Pat := .var 0
private def x1 : Pat := .var 1
private def x2 : Pat := .var 2
private def x3 : Pat := .var 3
private def x4 : Pat := .var 4
private def x5 : Pat := .var 5
private def x6 : Pat := .var 6

/-- **The rules as schemas**: take patterns, read patterns and made terms. -/
def schema : RuleName → Schema
  | .varZero => ⟨[p3 29 (p1 2 (p0 3)) (p2 21 x0 x1) x2], [], [p2 30 x0 x2]⟩
  | .varSucc => ⟨[p3 29 (p1 2 (p1 4 x0)) (p2 21 x1 x2) x3], [], [p3 29 (p1 2 x0) x2 x3]⟩
  | .lam => ⟨[p3 29 (p1 5 x0) x1 x2], [], [p2 30 (p2 18 x0 x1) x2]⟩
  | .app => ⟨[p3 29 (p2 6 x0 x1) x2 x3], [], [p3 29 x0 x2 (p2 21 (p2 22 x1 x2) x3)]⟩
  | .appL => ⟨[p2 30 x0 (p2 21 (p2 22 x1 x2) x3)], [], [p3 29 x1 x2 (p2 21 (p1 23 x0) x3)]⟩
  | .beta => ⟨[p2 30 x0 (p2 21 (p1 23 (p2 18 x1 x2)) x3)], [], [p3 29 x1 (p2 21 x0 x2) x3]⟩
  | .let_ => ⟨[p3 29 (p2 7 x0 x1) x2 x3], [], [p3 29 x0 x2 (p2 21 (p2 24 x1 x2) x3)]⟩
  | .letK => ⟨[p2 30 x0 (p2 21 (p2 24 x1 x2) x3)], [], [p3 29 x1 (p2 21 x0 x2) x3]⟩
  | .quote => ⟨[p3 29 (p1 8 x0) x1 x2], [], [p2 30 (p2 19 x0 x1) x2]⟩
  | .activate => ⟨[p3 29 (p1 9 x0) x1 x2], [], [p3 29 x0 x1 (p2 21 (p0 25) x2)]⟩
  | .activateK => ⟨[p2 30 (p2 19 x0 x1) (p2 21 (p0 25) x2)], [], [p3 29 x0 x1 x2]⟩
  | .atom => ⟨[p3 29 (p1 10 x0) x1 x2], [], [p2 30 (p1 10 x0) x2]⟩
  | .ambL => ⟨[p3 29 (p2 11 x0 x1) x2 x3], [], [p3 29 x0 x2 x3]⟩
  | .ambR => ⟨[p3 29 (p2 11 x0 x1) x2 x3], [], [p3 29 x1 x2 x3]⟩
  | .add => ⟨[p3 29 (p1 12 x0) x1 x2], [], [p3 29 x0 x1 (p2 21 (p0 26) x2)]⟩
  | .addK => ⟨[p2 30 x0 (p2 21 (p0 26) x1)], [], [p2 30 x0 x1, p1 31 x0]⟩
  | .remove => ⟨[p3 29 (p1 13 x0) x1 x2], [], [p3 29 x0 x1 (p2 21 (p0 27) x2)]⟩
  | .removeK => ⟨[p2 30 x0 (p2 21 (p0 27) x1), p1 31 x0], [], [p2 30 x0 x1]⟩
  | .await => ⟨[p3 29 (p1 14 x0) x1 x2], [], [p2 32 x0 x2]⟩
  | .demand => ⟨[p3 29 (p2 15 x0 x1) x2 x3], [], [p3 29 x1 x2 (p2 21 (p1 28 x0) x3)]⟩
  | .demandK => ⟨[p2 30 x0 (p2 21 (p1 28 x1) x2)], [], [p2 30 x0 x2, p2 33 x1 x0]⟩
  | .resume => ⟨[p2 33 x0 x1], [p2 32 x0 x2], [p2 30 x1 x2]⟩
  | .call => ⟨[p3 29 (p1 16 x0) x1 x2], [p3 34 x0 x3 x4], [p3 29 x4 (p0 20) x2, p2 35 x0 x3]⟩
  | .redefine => ⟨[p3 29 (p3 17 x0 x1 x2) x3 x4, p3 34 x0 x5 x6], [], [p2 30 (p1 10 x1) x4, p3 34 x0 x1 x2]⟩

end Patterns

/-- **Every rule is well formed**: its made variables are matched, and it has at most one read
pattern. -/
theorem schema_wellFormed (i : RuleName) : (schema i).WellFormed := by
  cases i <;> exact ⟨by decide, by decide⟩

/-- An assignment from a list of rows. -/
def args (l : List Sx) (x : ℕ) : Sx := l.getD x default

/-- **The schemas present the reference semantics exactly.** -/
theorem step_iff_rewrites (W W' : Multiset Sx) : Step W W' ↔ Rewrites schema W W' := by
  constructor
  · intro step
    cases step with
    | varZero v ρ κ W => exact ⟨.varZero, args [v, ρ, κ], W, rfl, rfl⟩
    | varSucc i v ρ κ W => exact ⟨.varSucc, args [i, v, ρ, κ], W, rfl, rfl⟩
    | lam b ρ κ W => exact ⟨.lam, args [b, ρ, κ], W, rfl, rfl⟩
    | app f a ρ κ W => exact ⟨.app, args [f, a, ρ, κ], W, rfl, rfl⟩
    | appL v a ρ κ W => exact ⟨.appL, args [v, a, ρ, κ], W, rfl, rfl⟩
    | beta v b ρ κ W => exact ⟨.beta, args [v, b, ρ, κ], W, rfl, rfl⟩
    | let_ s b ρ κ W => exact ⟨.let_, args [s, b, ρ, κ], W, rfl, rfl⟩
    | letK v b ρ κ W => exact ⟨.letK, args [v, b, ρ, κ], W, rfl, rfl⟩
    | quote c ρ κ W => exact ⟨.quote, args [c, ρ, κ], W, rfl, rfl⟩
    | activate e ρ κ W => exact ⟨.activate, args [e, ρ, κ], W, rfl, rfl⟩
    | activateK c ρ κ W => exact ⟨.activateK, args [c, ρ, κ], W, rfl, rfl⟩
    | atom d ρ κ W => exact ⟨.atom, args [d, ρ, κ], W, rfl, rfl⟩
    | ambL l r ρ κ W => exact ⟨.ambL, args [l, r, ρ, κ], W, rfl, rfl⟩
    | ambR l r ρ κ W => exact ⟨.ambR, args [l, r, ρ, κ], W, rfl, rfl⟩
    | add e ρ κ W => exact ⟨.add, args [e, ρ, κ], W, rfl, rfl⟩
    | addK v κ W => exact ⟨.addK, args [v, κ], W, rfl, rfl⟩
    | remove e ρ κ W => exact ⟨.remove, args [e, ρ, κ], W, rfl, rfl⟩
    | removeK v κ W => exact ⟨.removeK, args [v, κ], W, rfl, rfl⟩
    | await k ρ κ W => exact ⟨.await, args [k, ρ, κ], W, rfl, rfl⟩
    | demand k e ρ κ W => exact ⟨.demand, args [k, e, ρ, κ], W, rfl, rfl⟩
    | demandK v k κ W => exact ⟨.demandK, args [v, k, κ], W, rfl, rfl⟩
    | resume k v κ W => exact ⟨.resume, args [k, v, κ], W, rfl, rfl⟩
    | call k u c ρ κ W => exact ⟨.call, args [k, ρ, κ, u, c], W, rfl, rfl⟩
    | redefine k u c u₀ c₀ ρ κ W => exact ⟨.redefine, args [k, u, c, ρ, κ, u₀, c₀], W, rfl, rfl⟩
  · rintro ⟨i, θ, F, rfl, rfl⟩
    cases i with
    | varZero => exact .varZero (θ 0) (θ 1) (θ 2) F
    | varSucc => exact .varSucc (θ 0) (θ 1) (θ 2) (θ 3) F
    | lam => exact .lam (θ 0) (θ 1) (θ 2) F
    | app => exact .app (θ 0) (θ 1) (θ 2) (θ 3) F
    | appL => exact .appL (θ 0) (θ 1) (θ 2) (θ 3) F
    | beta => exact .beta (θ 0) (θ 1) (θ 2) (θ 3) F
    | let_ => exact .let_ (θ 0) (θ 1) (θ 2) (θ 3) F
    | letK => exact .letK (θ 0) (θ 1) (θ 2) (θ 3) F
    | quote => exact .quote (θ 0) (θ 1) (θ 2) F
    | activate => exact .activate (θ 0) (θ 1) (θ 2) F
    | activateK => exact .activateK (θ 0) (θ 1) (θ 2) F
    | atom => exact .atom (θ 0) (θ 1) (θ 2) F
    | ambL => exact .ambL (θ 0) (θ 1) (θ 2) (θ 3) F
    | ambR => exact .ambR (θ 0) (θ 1) (θ 2) (θ 3) F
    | add => exact .add (θ 0) (θ 1) (θ 2) F
    | addK => exact .addK (θ 0) (θ 1) F
    | remove => exact .remove (θ 0) (θ 1) (θ 2) F
    | removeK => exact .removeK (θ 0) (θ 1) F
    | await => exact .await (θ 0) (θ 1) (θ 2) F
    | demand => exact .demand (θ 0) (θ 1) (θ 2) (θ 3) F
    | demandK => exact .demandK (θ 0) (θ 1) (θ 2) F
    | resume => exact .resume (θ 0) (θ 1) (θ 2) F
    | call => exact .call (θ 0) (θ 3) (θ 4) (θ 1) (θ 2) F
    | redefine => exact .redefine (θ 0) (θ 1) (θ 2) (θ 5) (θ 6) (θ 3) (θ 4) F

theorem step_eq_rewrites : Step = Rewrites schema := by
  funext W W'
  exact propext (step_iff_rewrites W W')

#print axioms schema_wellFormed
#print axioms step_iff_rewrites
#print axioms step_eq_rewrites

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
