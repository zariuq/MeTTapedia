/-
# Gauthier `org` languageDef — the base OEIS program-synthesis language (GSLT term + operational R)

Operationally defines the term grammar `T` and the small-step evaluator (the rewrite side `R`) of the
base language in Gauthier–Olšák–Urban's OEIS program-synthesis family ("Alien Coding" / QSynt). This is
the `org` signature: 16 first-order operators over integer-list register states, evaluated by a
fuel-bounded tree interpreter. Variants (`pow`, `array`, `turing`, `ramsey`, `wrat`, …) are additional
signatures over the same substrate and live in sibling files.

Grounded (real, not invented) in the QSynt source:
  * `repos/oeis-synthesis/src/kernel.sml` — `org_operl`: the operator table + arities
      (`0 1 2 + - * / % cond loop x y compr loop2`, plus `push pop` under the memo profile).
  * `repos/oeis-synthesis/src/exec_memo.sml` — the evaluator: `mk_e` (binary head-combine, keep left
      tail), `cond_f` (`hd(f1) ≤ 0`), `push_f`/`pop_f`, `helper` (for-loop), `loop_f`/`loop2_f`, and
      `compr_next`/`compr_loop` (comprehension).

The evaluator is total via `fuel`, matching QSynt's abstract-timer cutoff.  Register discipline: a program
is evaluated against two register lists `x`, `y` (seeded `x = [n]`, `y = [0]` for OEIS term `a(n)`);
`loop`/`loop2`/`compr` rebind the registers for their sub-programs.
-/

namespace Mettapedia.GSLT.LanguageDef.Gauthier

/-- The `org` operator vocabulary (16 ops).  Variants extend this in sibling files. -/
inductive Op where
  | zero | one | two
  | addi | diff | mult | divi | modu
  | cond | loop | x | y | compr | loop2
  | push | pop
  deriving DecidableEq, Repr

/-- Arity = number of child sub-programs each operator takes. -/
def Op.arity : Op → Nat
  | .zero | .one | .two | .x | .y => 0
  | .pop => 1
  | .addi | .diff | .mult | .divi | .modu | .compr | .push => 2
  | .cond | .loop => 3
  | .loop2 => 5

/-- How many *leading* children are sub-PROGRAMS re-evaluated with rebound registers
    (`loop` f, `compr` f, `loop2` f g), vs value arguments. Recorded for the parser/GNN graph view. -/
def Op.hoArity : Op → Nat
  | .loop => 1
  | .compr => 1
  | .loop2 => 2
  | _ => 0

/-- The term grammar `T`: operator trees.  Well-formedness (child count = `arity`) is enforced by the
    evaluator returning `none` on a mismatch (so `Prog` itself stays a plain container). -/
inductive Prog where
  | node : Op → List Prog → Prog
  deriving Repr

namespace Prog
/-- Convenience nullary/`n`-ary builders. -/
def z : Prog := .node .zero []
def o : Prog := .node .one []
def tw : Prog := .node .two []
def X : Prog := .node .x []
def Y : Prog := .node .y []
def addi (a b : Prog) : Prog := .node .addi [a, b]
def diff (a b : Prog) : Prog := .node .diff [a, b]
def mult (a b : Prog) : Prog := .node .mult [a, b]
def divi (a b : Prog) : Prog := .node .divi [a, b]
def modu (a b : Prog) : Prog := .node .modu [a, b]
def cond (c t e : Prog) : Prog := .node .cond [c, t, e]
def loop (f n x0 : Prog) : Prog := .node .loop [f, n, x0]
def compr (f n : Prog) : Prog := .node .compr [f, n]
def loop2 (f g n a b : Prog) : Prog := .node .loop2 [f, g, n, a, b]
def push (a b : Prog) : Prog := .node .push [a, b]
def pop (a : Prog) : Prog := .node .pop [a]
end Prog

/-! ## Well-formedness — the term-grammar invariant `T` (parser-facing)

The MIK/CeTTa parser (`gauthier-org-g` lane) must produce exactly the well-formed trees: every node's
child count equals its operator's arity.  This is the first-order analog of the LF LanguageDef's
`WellScoped` scope invariant.  The evaluator is defined on all of `Prog` (returning `none` off the
invariant), so `WellFormed` is a *separate* predicate rather than a refinement of the carrier. -/

/-- Structural well-formedness: at every node, `children.length = op.arity`, recursively. -/
inductive WellFormed : Prog → Prop where
  | node {op : Op} {ch : List Prog} :
      ch.length = op.arity → (∀ c ∈ ch, WellFormed c) → WellFormed (.node op ch)

-- Positive: the builders produce well-formed trees (constructors are arity-correct by construction).
example : WellFormed Prog.X := .node rfl (by intro c hc; cases hc)
example (a b : Prog) (ha : WellFormed a) (hb : WellFormed b) : WellFormed (Prog.mult a b) :=
  .node rfl (by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ha
    · rcases List.mem_cons.mp hc' with rfl | hc''
      · exact hb
      · cases hc'')
-- Negative: an arity violation (`mult` with one child) is *not* well-formed — this is what the
-- parser must reject and what makes `WellFormed` non-vacuous.
example : ¬ WellFormed (.node .mult [Prog.X]) := by
  intro h; cases h with | node hlen _ => simp [Op.arity] at hlen

/-- `mk_e` (exec_memo.sml): both lists must be nonempty; combine the heads, keep the LEFT tail. -/
def mkE (f : Int → Int → Int) : List Int → List Int → Option (List Int)
  | a :: m, b :: _ => some (f a b :: m)
  | _, _ => none

/-- Floor division / floor modulo, matching SML `IntInf.div` / `IntInf.mod`; guard divisor 0. -/
def sdiv (a b : Int) : Option Int := if b = 0 then none else some (Int.fdiv a b)
def smod (a b : Int) : Option Int := if b = 0 then none else some (Int.fmod a b)

mutual
/-- The evaluator (the operational `R`).  `eval fuel p x y` runs program `p` with register lists `x`,`y`.
    `loop`/`loop2` iterate via `loopIter`/`loop2Iter`; `compr` via `comprNext`/`comprLoop`.
    Total by `fuel` (QSynt's abstract-timer analog); `none` = fuel exhausted, ill-formed, or a partial
    op (empty head, div-by-zero). -/
def eval : Nat → Prog → List Int → List Int → Option (List Int)
  | 0, _, _, _ => none
  | fuel + 1, .node op ch, x, y =>
    match op, ch with
    | .zero, [] => some [0]
    | .one,  [] => some [1]
    | .two,  [] => some [2]
    | .x,    [] => some x
    | .y,    [] => some y
    | .addi, [a, b] => do let va ← eval fuel a x y; let vb ← eval fuel b x y; mkE (· + ·) va vb
    | .diff, [a, b] => do let va ← eval fuel a x y; let vb ← eval fuel b x y; mkE (· - ·) va vb
    | .mult, [a, b] => do let va ← eval fuel a x y; let vb ← eval fuel b x y; mkE (· * ·) va vb
    | .divi, [a, b] => do
        let va ← eval fuel a x y; let vb ← eval fuel b x y
        match va, vb with
        | av :: am, bv :: _ => do let q ← sdiv av bv; some (q :: am)
        | _, _ => none
    | .modu, [a, b] => do
        let va ← eval fuel a x y; let vb ← eval fuel b x y
        match va, vb with
        | av :: am, bv :: _ => do let r ← smod av bv; some (r :: am)
        | _, _ => none
    | .cond, [c, t, e] => do
        let vc ← eval fuel c x y
        match vc with
        | cv :: _ => if cv ≤ 0 then eval fuel t x y else eval fuel e x y
        | [] => none
    | .push, [a, b] => do
        let va ← eval fuel a x y; let vb ← eval fuel b x y
        match va with
        | av :: _ => some (av :: vb)
        | [] => none
    | .pop, [a] => do
        let va ← eval fuel a x y
        match va with
        | [] => none
        | [z] => some [z]
        | _ :: m => some m
    | .loop, [f, n, x0] => do
        let vn ← eval fuel n x y
        let vx0 ← eval fuel x0 x y
        match vn with
        | nv :: _ => loopIter fuel f nv.toNat vx0 [1]
        | [] => none
    | .loop2, [f, g, n, a, b] => do
        let vn ← eval fuel n x y
        let va ← eval fuel a x y
        let vb ← eval fuel b x y
        match vn with
        | nv :: _ => loop2Iter fuel f g nv.toNat va vb
        | [] => none
    | .compr, [f, n] => do
        let vn ← eval fuel n x y
        match vn with
        | nv :: _ => comprLoop fuel f nv (-1) [-1]
        | [] => none
    | _, _ => none

/-- `helper` specialised to `loop`: iterate `k` times, `x1 := f(x1, counter)`, counter `:= [head+1]`. -/
def loopIter : Nat → Prog → Nat → List Int → List Int → Option (List Int)
  | 0, _, _, _, _ => none
  | _, _, 0, x1, _ => some x1
  | fuel + 1, f, k + 1, x1, x2 => do
      let x1' ← eval fuel f x1 x2
      loopIter fuel f k x1' [x2.headD 0 + 1]

/-- `helper` for `loop2`: iterate `k` times, `(x1,x2) := (f(x1,x2), g(x1,x2))` (both from the OLD pair);
    return the first register. -/
def loop2Iter : Nat → Prog → Prog → Nat → List Int → List Int → Option (List Int)
  | 0, _, _, _, _, _ => none
  | _, _, _, 0, x1, _ => some x1
  | fuel + 1, f, g, k + 1, x1, x2 => do
      let x1' ← eval fuel f x1 x2
      let x2' ← eval fuel g x1 x2
      loop2Iter fuel f g k x1' x2'

/-- `compr_next`: from candidate list `xc`, advance until `hd(f(xc,[0])) ≤ 0`; return that `[k]`. -/
def comprNext : Nat → Prog → List Int → Option (List Int)
  | 0, _, _ => none
  | fuel + 1, f, xc => do
      let v ← eval fuel f xc [0]
      match v with
      | cv :: _ => if cv ≤ 0 then some xc else comprNext fuel f [xc.headD 0 + 1]
      | [] => none

/-- `compr_loop`: collect the `n`-th satisfying element (0-indexed); `i` starts `-1`, `x` starts `[-1]`. -/
def comprLoop : Nat → Prog → Int → Int → List Int → Option (List Int)
  | 0, _, _, _, _ => none
  | fuel + 1, f, n, i, xcur =>
      if i ≥ n then some xcur
      else do
        let nx ← comprNext fuel f [xcur.headD 0 + 1]
        comprLoop fuel f n (i + 1) nx
end

/-- OEIS term `a(k)`: run `p` at register seeds `x = [k]`, `y = [0]`, take the head of the result. -/
def term (fuel : Nat) (p : Prog) (k : Int) : Option Int :=
  (eval fuel p [k] [0]).bind List.head?

/-- The sequence prefix `a(0), …, a(len-1)`. -/
def seqPrefix (fuel : Nat) (p : Prog) (len : Nat) : List (Option Int) :=
  (List.range len).map (fun k => term fuel p (Int.ofNat k))

/-! ## Extensional equivalence — the GSLT equations `E`

Two programs are equated when they compute the same result at every fuel and register seeding.  This
is the denotational equality of the language: the pullback of `Option (List Int)`-equality along
`eval`, hence a genuine equivalence.  Packaged as a `Setoid` to match the `GSLT.equations` field.  (The
term-rewriting side `R` of the GSLT is the big-step `eval` itself; a small-step configuration calculus
is a separate, later packaging — not forced here.) -/

/-- `p ≈ q`: `eval` agrees on `p` and `q` for all fuel and all register seedings. -/
def Extensional (p q : Prog) : Prop := ∀ fuel x y, eval fuel p x y = eval fuel q x y

theorem Extensional.refl (p : Prog) : Extensional p p := fun _ _ _ => rfl
theorem Extensional.symm {p q : Prog} (h : Extensional p q) : Extensional q p :=
  fun f x y => (h f x y).symm
theorem Extensional.trans {p q r : Prog}
    (h₁ : Extensional p q) (h₂ : Extensional q r) : Extensional p r :=
  fun f x y => (h₁ f x y).trans (h₂ f x y)

/-- The GSLT equations `E` as a `Setoid` on the term grammar. -/
def extSetoid : Setoid Prog where
  r := Extensional
  iseqv := ⟨Extensional.refl, fun h => Extensional.symm h, fun h₁ h₂ => Extensional.trans h₁ h₂⟩

/-! ## Validation: known OEIS programs must reproduce their sequences (the O1 oracle, in Lean). -/

open Prog

-- A000004 (all zeros): the constant-zero program `A`.
#eval seqPrefix 200 z 8                         -- [0,0,0,0,0,0,0,0]
-- A000007 (1,0,0,…): `K B A I` = cond(x, one, zero).
#eval seqPrefix 200 (cond X o z) 8              -- [1,0,0,0,0,0,0,0]
-- A001477 (identity 0,1,2,…): `K` = x.
#eval seqPrefix 200 X 8                          -- [0,1,2,3,4,5,6,7]
-- A000290 (squares): `K K F` = x*x.
#eval seqPrefix 200 (mult X X) 8                 -- [0,1,4,9,16,25,36,49]
-- A005843 (evens): x+x.
#eval seqPrefix 200 (addi X X) 8                 -- [0,2,4,6,8,10,12,14]
-- A000142 (factorial): `loop(x*y, x, one)` — iterate n times multiplying by the counter.
#eval seqPrefix 400 (loop (mult X Y) X o) 7      -- [1,1,2,6,24,120,720]

end Mettapedia.GSLT.LanguageDef.Gauthier
