/-
# Gauthier `minimal` languageDef — the six-operator core of the OEIS family

The smallest signature in Gauthier–Olšák–Urban's OEIS program-synthesis family: just
`zero x y suc pred loop`.  Unlike the `org` memo profile (register lists, see `Base.lean`), the
`minimal`/`array`/`turing` variants run on the *scalar-triple* substrate `exec.sml`: a program denotes
a function `(x, y, z) ↦ Int` on a triple of integer registers, and the OEIS term is `a(n) = eval` at
seed `(n, 0, 0)`.  This file formalizes that substrate for the `minimal` signature.

Grounded (real, not invented) in the QSynt source:
  * `repos/oeis-synthesis/src/kernel.sml` — `minimal_operl = [zero,x,y,suc(1),pred(1),loop(3)]`.
  * `repos/oeis-synthesis/src/exec.sml` — the scalar executor: `suc_f = mk_unf (·+1)`,
      `pred_f = mk_unf (·-1)`, `x_f/y_f = (x,y,z)↦x / ↦y`, `loop_f` via `loop3_f_aux`, and the OEIS
      seeding `mk_exec_onev p = fn x => f (x, 0, 0)`.

The loop is the whole language: `loop3_f_aux f₁ f₂ f₃ n x₁ x₂ x₃` iterates `n` times, updating
`(x₁,x₂,x₃) := (f₁,f₂,f₃)(x₁,x₂,x₃)` and returning `x₁`.  For `loop f n x₀` the specialization fixes
`f₂ = (·+1)` (a counter in `x₂`, starting `1`) and `f₃ = id` (the original input `x₀` preserved in
`x₃`), so the body `f` sees `(accumulator, counter, input)`.  Total via `fuel`, matching the abstract
timer.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierMinimal

/-- The `minimal` operator vocabulary (6 ops, in `minimal_execv` index order). -/
inductive Op where
  | zero | x | y | suc | pred | loop
  deriving DecidableEq, Repr

/-- Arity = number of child sub-programs. -/
def Op.arity : Op → Nat
  | .zero | .x | .y => 0
  | .suc | .pred => 1
  | .loop => 3

/-- The term grammar `T`: operator trees (QSynt's `Ins (id, args)`). -/
inductive Prog where
  | node : Op → List Prog → Prog
  deriving Repr

namespace Prog
def z : Prog := .node .zero []
def X : Prog := .node .x []
def Y : Prog := .node .y []
def suc (a : Prog) : Prog := .node .suc [a]
def pred (a : Prog) : Prog := .node .pred [a]
def loop (f n x0 : Prog) : Prog := .node .loop [f, n, x0]
end Prog

/-- Structural well-formedness (the parser-facing `T`-invariant): child count = arity, recursively. -/
inductive WellFormed : Prog → Prop where
  | node {op : Op} {ch : List Prog} :
      ch.length = op.arity → (∀ c ∈ ch, WellFormed c) → WellFormed (.node op ch)

-- Positive/negative examples: the builders are arity-correct; an arity violation is rejected.
example (f n x0 : Prog) (hf : WellFormed f) (hn : WellFormed n) (hx : WellFormed x0) :
    WellFormed (Prog.loop f n x0) :=
  .node rfl (by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hf
    · rcases List.mem_cons.mp hc' with rfl | hc''
      · exact hn
      · rcases List.mem_cons.mp hc'' with rfl | hc'''
        · exact hx
        · cases hc''')
example : ¬ WellFormed (.node .suc []) := by
  intro h; cases h with | node hlen _ => simp [Op.arity] at hlen

/-! ## The scalar-triple evaluator (the operational `R`)

`eval fuel p x y z` runs program `p` on register triple `(x,y,z)` and returns a scalar.  `loop` iterates
via `loopIter`; the body is re-evaluated with `(accumulator, counter, input)`. -/

mutual
/-- Big-step evaluator: `(x,y,z) ↦ Int`, total by `fuel`; `none` = fuel exhausted or ill-formed. -/
def eval : Nat → Prog → Int → Int → Int → Option Int
  | 0, _, _, _, _ => none
  | fuel + 1, .node op ch, x, y, z =>
    match op, ch with
    | .zero, [] => some 0
    | .x,    [] => some x
    | .y,    [] => some y
    | .suc,  [a] => (· + 1) <$> eval fuel a x y z
    | .pred, [a] => (· - 1) <$> eval fuel a x y z
    | .loop, [f, n, x0] => do
        let vn  ← eval fuel n x y z
        let vx0 ← eval fuel x0 x y z
        loopIter fuel f vn.toNat vx0 1 vx0
    | _, _ => none

/-- `loop3_f_aux` specialized to `loop`: iterate `k` times, `x₁ := f(x₁, counter, input)`, counter `+1`
    each step, input `x₃` held constant; return `x₁`. -/
def loopIter : Nat → Prog → Nat → Int → Int → Int → Option Int
  | 0, _, _, _, _, _ => none
  | _, _, 0, x1, _, _ => some x1
  | fuel + 1, f, k + 1, x1, x2, x3 => do
      let x1' ← eval fuel f x1 x2 x3
      loopIter fuel f k x1' (x2 + 1) x3
end

/-- OEIS term `a(k)`: run `p` at seed `(k, 0, 0)` (the scalar output is the term — no `head`). -/
def term (fuel : Nat) (p : Prog) (k : Int) : Option Int := eval fuel p k 0 0

/-- The sequence prefix `a(0), …, a(len-1)`. -/
def seqPrefix (fuel : Nat) (p : Prog) (len : Nat) : List (Option Int) :=
  (List.range len).map (fun k => term fuel p (Int.ofNat k))

/-! ## Extensional equivalence — the GSLT equations `E`. -/

/-- `p ≈ q`: `eval` agrees for all fuel and all register triples. -/
def Extensional (p q : Prog) : Prop := ∀ fuel x y z, eval fuel p x y z = eval fuel q x y z

theorem Extensional.refl (p : Prog) : Extensional p p := fun _ _ _ _ => rfl
theorem Extensional.symm {p q : Prog} (h : Extensional p q) : Extensional q p :=
  fun f x y z => (h f x y z).symm
theorem Extensional.trans {p q r : Prog}
    (h₁ : Extensional p q) (h₂ : Extensional q r) : Extensional p r :=
  fun f x y z => (h₁ f x y z).trans (h₂ f x y z)

/-- The GSLT equations `E` as a `Setoid`. -/
def extSetoid : Setoid Prog where
  r := Extensional
  iseqv := ⟨Extensional.refl, fun h => Extensional.symm h, fun h₁ h₂ => Extensional.trans h₁ h₂⟩

/-! ## Validation: `minimal` programs reproduce known sequences. -/

open Prog

-- A001477 identity: `x`.
#eval seqPrefix 400 X 8                         -- [0,1,2,3,4,5,6,7]
-- A020725-ish successor: `suc x` = n+1.
#eval seqPrefix 400 (suc X) 8                   -- [1,2,3,4,5,6,7,8]
-- predecessor: `pred x` = n-1.
#eval seqPrefix 400 (pred X) 8                  -- [-1,0,1,2,3,4,5,6]
-- A005843 doubling: `loop (suc x) x x` — iterate n times +1 from n ⇒ 2n.
#eval seqPrefix 400 (loop (suc X) X X) 8        -- [0,2,4,6,8,10,12,14]
-- A008585 tripling: `loop (suc (suc x)) x x` — iterate n times +2 from n ⇒ 3n.
#eval seqPrefix 400 (loop (suc (suc X)) X X) 8  -- [0,3,6,9,12,15,18,21]

end Mettapedia.GSLT.LanguageDef.GauthierMinimal
