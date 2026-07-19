/-
# Gauthier `pow` languageDef — the loop-free arithmetic+exponentiation signature

The `pow` variant of Gauthier–Olšák–Urban's OEIS family is unusual: it has **no loop, no `y`, no
comprehension** — only arithmetic plus exponentiation and the constant `ten`.  Every program is a
finite arithmetic expression, so evaluation is unconditionally terminating (the `fuel` here can never
be the reason a `pow` program fails; it is kept only to share the family's uniform interface).  The
state is the single scalar `x` (`exec_pow.sml`: `x_f = mk_nullf (fn x => x)`), and the OEIS term is
`a(n) = eval` at `x = n`.

Grounded (real, not invented) in the QSynt source:
  * `repos/oeis-synthesis/src/kernel.sml` — `pow_operl = [zero,one,two,addi,diff,mult,divi,modu,cond,
      pow(2),x,ten]`.
  * `repos/oeis-synthesis/src/exec_pow.sml` — `ten_f = 10`, `pow (a,b)`: `b = 0 ⇒ 1`; `a = 0 ⇒ 0`;
      a size guard (folded into the abstract timer here); else `IntInf.pow (a, b)`.  `divi`/`modu` are
      SML `div`/`mod` (floor), guarded against a zero divisor.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierPow

/-- The `pow` operator vocabulary (12 ops, in `pow_execv` index order). -/
inductive Op where
  | zero | one | two | addi | diff | mult | divi | modu | cond | pow | x | ten
  deriving DecidableEq, Repr

/-- Arity = number of child sub-programs. -/
def Op.arity : Op → Nat
  | .zero | .one | .two | .x | .ten => 0
  | .addi | .diff | .mult | .divi | .modu | .pow => 2
  | .cond => 3

/-- The term grammar `T`: operator trees (QSynt's `Ins (id, args)`). -/
inductive Prog where
  | node : Op → List Prog → Prog
  deriving Repr

namespace Prog
def z : Prog := .node .zero []
def o : Prog := .node .one []
def tw : Prog := .node .two []
def X : Prog := .node .x []
def ten : Prog := .node .ten []
def addi (a b : Prog) : Prog := .node .addi [a, b]
def diff (a b : Prog) : Prog := .node .diff [a, b]
def mult (a b : Prog) : Prog := .node .mult [a, b]
def divi (a b : Prog) : Prog := .node .divi [a, b]
def modu (a b : Prog) : Prog := .node .modu [a, b]
def cond (c t e : Prog) : Prog := .node .cond [c, t, e]
def pow (a b : Prog) : Prog := .node .pow [a, b]
end Prog

/-- Structural well-formedness (the parser-facing `T`-invariant): child count = arity, recursively. -/
inductive WellFormed : Prog → Prop where
  | node {op : Op} {ch : List Prog} :
      ch.length = op.arity → (∀ c ∈ ch, WellFormed c) → WellFormed (.node op ch)

-- Positive/negative examples.
example (a b : Prog) (ha : WellFormed a) (hb : WellFormed b) : WellFormed (Prog.pow a b) :=
  .node rfl (by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ha
    · rcases List.mem_cons.mp hc' with rfl | hc''
      · exact hb
      · cases hc'')
example : ¬ WellFormed (.node .pow [Prog.X]) := by
  intro h; cases h with | node hlen _ => simp [Op.arity] at hlen

/-- Floor division / floor modulo (SML `div`/`mod`), guarding a zero divisor. -/
def sdiv (a b : Int) : Option Int := if b = 0 then none else some (Int.fdiv a b)
def smod (a b : Int) : Option Int := if b = 0 then none else some (Int.fmod a b)

/-- `pow (a,b)` (`exec_pow.sml`): `b = 0 ⇒ 1` (so `0^0 = 1`); then `a = 0 ⇒ 0`; a negative exponent
    makes `IntInf.pow` partial (raises for `|a| ≥ 2`) so we fail; otherwise `a ^ b`.  The source's
    size guard against huge results is a resource cutoff, here subsumed by the abstract timer. -/
def powInt (a b : Int) : Option Int :=
  if b = 0 then some 1
  else if a = 0 then some 0
  else if b < 0 then none
  else some (a ^ b.toNat)

/-! ## The scalar evaluator (the operational `R`), on state `x : Int`.

No loop/comprehension ⇒ structurally terminating; `fuel` only unifies the interface. -/

/-- Big-step evaluator `x ↦ Int`.  `none` = ill-formed / division-or-power failure (fuel is never the
    limiting factor for `pow`). -/
def eval : Nat → Prog → Int → Option Int
  | 0, _, _ => none
  | fuel + 1, .node op ch, x =>
    match op, ch with
    | .zero, [] => some 0
    | .one,  [] => some 1
    | .two,  [] => some 2
    | .ten,  [] => some 10
    | .x,    [] => some x
    | .addi, [a, b] => do let va ← eval fuel a x; let vb ← eval fuel b x; some (va + vb)
    | .diff, [a, b] => do let va ← eval fuel a x; let vb ← eval fuel b x; some (va - vb)
    | .mult, [a, b] => do let va ← eval fuel a x; let vb ← eval fuel b x; some (va * vb)
    | .divi, [a, b] => do let va ← eval fuel a x; let vb ← eval fuel b x; sdiv va vb
    | .modu, [a, b] => do let va ← eval fuel a x; let vb ← eval fuel b x; smod va vb
    | .pow,  [a, b] => do let va ← eval fuel a x; let vb ← eval fuel b x; powInt va vb
    | .cond, [c, t, e] => do
        let vc ← eval fuel c x
        if vc ≤ 0 then eval fuel t x else eval fuel e x
    | _, _ => none

/-- OEIS term `a(k)`: run `p` at scalar seed `x = k`. -/
def term (fuel : Nat) (p : Prog) (k : Int) : Option Int := eval fuel p k

/-- The sequence prefix `a(0), …, a(len-1)`. -/
def seqPrefix (fuel : Nat) (p : Prog) (len : Nat) : List (Option Int) :=
  (List.range len).map (fun k => term fuel p (Int.ofNat k))

/-! ## Extensional equivalence — the GSLT equations `E`. -/

/-- `p ≈ q`: `eval` agrees for all fuel and all scalar states. -/
def Extensional (p q : Prog) : Prop := ∀ fuel x, eval fuel p x = eval fuel q x

theorem Extensional.refl (p : Prog) : Extensional p p := fun _ _ => rfl
theorem Extensional.symm {p q : Prog} (h : Extensional p q) : Extensional q p :=
  fun f x => (h f x).symm
theorem Extensional.trans {p q r : Prog}
    (h₁ : Extensional p q) (h₂ : Extensional q r) : Extensional p r :=
  fun f x => (h₁ f x).trans (h₂ f x)

/-- The GSLT equations `E` as a `Setoid`. -/
def extSetoid : Setoid Prog where
  r := Extensional
  iseqv := ⟨Extensional.refl, fun h => Extensional.symm h, fun h₁ h₂ => Extensional.trans h₁ h₂⟩

/-! ## Validation: `pow` programs reproduce known sequences. -/

open Prog

-- A001477 identity: `x`.
#eval seqPrefix 100 X 8                    -- [0,1,2,3,4,5,6,7]
-- A000290 squares: `pow x two` = n².
#eval seqPrefix 100 (pow X tw) 8           -- [0,1,4,9,16,25,36,49]
-- A000079 powers of two: `pow two x` = 2ⁿ.
#eval seqPrefix 100 (pow tw X) 8           -- [1,2,4,8,16,32,64,128]
-- A000312 n^n (with 0^0 = 1): `pow x x`.
#eval seqPrefix 100 (pow X X) 7            -- [1,1,4,27,256,3125,46656]
-- A002378 oblong n²+n: `addi (mult x x) x`.
#eval seqPrefix 100 (addi (mult X X) X) 8  -- [0,2,6,12,20,30,42,56]

end Mettapedia.GSLT.LanguageDef.GauthierPow
