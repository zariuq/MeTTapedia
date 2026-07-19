/-
# Gauthier E2 two-list language family: one evaluator, many list-substrate tables

This file is milestone 3's register-list substrate.  It imports `E1.lean` only to reuse the approved
generic syntax/parser layer (`Entry`, `Signature`, `Prog`, `WellFormed`, `recognize`,
`recognize_sound`).  The evaluator below is a separate E2 core over two integer-list registers.

Grounding:
  * `repos/oeis-synthesis/src/kernel.sml` lines 293-320 and 350-358: `org`, `ramsey`, `arcagi`,
    `matchback`, and list-op table variants.
  * `repos/oeis-synthesis/src/kernel.sml` lines 489-497 and 514: higher-order arities for these tables.
  * `repos/oeis-synthesis/src/exec_memo.sml` lines 190-235: constants, list registers, arithmetic,
    conditionals, `push`, and `pop`.
  * `repos/oeis-synthesis/src/exec_memo.sml` lines 293-321 and 327-375: `loop`, `loop2`, `loop2snd`,
    and comprehension.
  * `repos/oeis-synthesis/src/exec_memo.sml` lines 381-393: `back`.
  * `repos/oeis-synthesis/src/exec_memo.sml` lines 399-440 and 457-470: arcagi primitives and
    evaluator table assembly.
  * `repos/oeis-synthesis/src/exec_intl.sml` lines 138-146 and 232-244: `edge` and ramsey/int-list
    table assembly.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.E1

namespace Mettapedia.GSLT.LanguageDef.GauthierE2

open Mettapedia.GSLT.LanguageDef.GauthierE1

/-- Primitive semantics available on the E2 two-list substrate. -/
inductive Prim where
  | zero | one | two
  | addi | diff | mult | divi | modu
  | cond | loop | x | y | compr | loop2
  | push | pop | loop2snd
  | back | edge
  | equalcolor | isOut | isColori | isEqual
  | inputHeight | inputWidth | commonHeight | commonWidth
  deriving DecidableEq, Repr

/-- External data used by the oracle-like E2 variants (`matchback`, `ramsey`, `arcagi`). -/
structure World where
  backValues : List Int
  edgeValues : List Int
  matrix : List (List Int)
  colors : List Int
  inputHeight : Int
  inputWidth : Int
  commonHeight : Int
  commonWidth : Int
  deriving Repr

def defaultBackValues : List Int :=
  [-57, 19, -58, 100, -46, 0, 39, 82, 89, 1, 81, -83, 49, 94, 59, 55]

def defaultWorld : World :=
  { backValues := defaultBackValues
  , edgeValues := []
  , matrix := [[0]]
  , colors := [0]
  , inputHeight := 1
  , inputWidth := 1
  , commonHeight := 1
  , commonWidth := 1
  }

def head? : List Int → Option Int
  | [] => none
  | x :: _ => some x

def singletonHeadIncr : List Int → Option (List Int)
  | [] => none
  | x :: _ => some [x + 1]

/-- `mk_e` (`exec_memo.sml` lines 197-200): combine heads and keep the left tail. -/
def mkE (f : Int → Int → Option Int) : List Int → List Int → Option (List Int)
  | a :: m, b :: _ => do
      let c ← f a b
      some (c :: m)
  | _, _ => none

def add? (a b : Int) : Option Int := some (a + b)
def sub? (a b : Int) : Option Int := some (a - b)
def mul? (a b : Int) : Option Int := some (a * b)

def matrixGet? (w : World) (a b : Int) : Option Int :=
  if a < 0 then none
  else if b < 0 then none
  else
    match listGet? w.matrix a.toNat with
    | none => none
    | some row => listGet? row b.toNat

def colorGet? (w : World) (i : Int) : Option Int :=
  if i < 0 then none else listGet? w.colors i.toNat

def intIndexMod? (values : List Int) (a : Int) : Option Int :=
  match values.length with
  | 0 => none
  | n + 1 =>
      let m := Int.fmod a (Int.ofNat (n + 1))
      listGet? values m.toNat

mutual

/-- E2 evaluator.  `none` means fuel exhaustion, arity/tag mismatch, or an explicit partial operation. -/
def eval : Nat → Signature Prim → Prog → List Int → List Int → World → Option (List Int)
  | 0, _, _, _, _, _ => none
  | fuel + 1, sig, .node id ch, x, y, w =>
      match entryAt sig id with
      | none => none
      | some e =>
          match e.prim, ch with
          | .zero, [] => some [0]
          | .one, [] => some [1]
          | .two, [] => some [2]
          | .x, [] => some x
          | .y, [] => some y
          | .addi, [a, b] => do
              let va ← eval fuel sig a x y w
              let vb ← eval fuel sig b x y w
              mkE add? va vb
          | .diff, [a, b] => do
              let va ← eval fuel sig a x y w
              let vb ← eval fuel sig b x y w
              mkE sub? va vb
          | .mult, [a, b] => do
              let va ← eval fuel sig a x y w
              let vb ← eval fuel sig b x y w
              mkE mul? va vb
          | .divi, [a, b] => do
              let va ← eval fuel sig a x y w
              let vb ← eval fuel sig b x y w
              mkE sdiv va vb
          | .modu, [a, b] => do
              let va ← eval fuel sig a x y w
              let vb ← eval fuel sig b x y w
              mkE smod va vb
          | .cond, [c, t, e'] => do
              let vc ← eval fuel sig c x y w
              let hc ← head? vc
              if hc ≤ 0 then eval fuel sig t x y w else eval fuel sig e' x y w
          | .push, [a, b] => do
              let va ← eval fuel sig a x y w
              let vb ← eval fuel sig b x y w
              let ha ← head? va
              some (ha :: vb)
          | .pop, [a] => do
              let va ← eval fuel sig a x y w
              match va with
              | [] => none
              | [z] => some [z]
              | _ :: zs => some zs
          | .loop, [f, n, x0] => do
              let vn ← eval fuel sig n x y w
              let vx0 ← eval fuel sig x0 x y w
              let hn ← head? vn
              if hn < 0 then some vx0 else loopIter fuel sig f hn.toNat vx0 [1] w
          | .loop2, [f, g, n, a, b] => do
              let vn ← eval fuel sig n x y w
              let va ← eval fuel sig a x y w
              let vb ← eval fuel sig b x y w
              let hn ← head? vn
              if hn < 0 then some va else loop2Iter fuel sig f g hn.toNat va vb w
          | .loop2snd, [f, g, n, a, b] => do
              let vn ← eval fuel sig n x y w
              let va ← eval fuel sig a x y w
              let vb ← eval fuel sig b x y w
              let hn ← head? vn
              if hn < 0 then some vb else loop2sndIter fuel sig f g hn.toNat va vb w
          | .compr, [f, n] => do
              let vn ← eval fuel sig n x y w
              let hn ← head? vn
              if hn < 0 then none else comprSearch fuel sig f hn.toNat 0 [0] w
          | .back, [a] => do
              let va ← eval fuel sig a x y w
              let ha ← head? va
              if ha < 0 then some [0]
              else
                match listGet? w.backValues ha.toNat with
                | none => none
                | some v => some [v]
          | .edge, [a] => do
              let va ← eval fuel sig a x y w
              let ha ← head? va
              match intIndexMod? w.edgeValues ha with
              | none => none
              | some v => some [v]
          | .equalcolor, [a, b, c, d] => do
              let va ← eval fuel sig a x y w; let vb ← eval fuel sig b x y w
              let vc ← eval fuel sig c x y w; let vd ← eval fuel sig d x y w
              let ha ← head? va; let hb ← head? vb; let hc ← head? vc; let hd ← head? vd
              match matrixGet? w ha hb, matrixGet? w hc hd with
              | some ca, some cb => if ca = cb then some [1] else some [0]
              | _, _ => some [-1]
          | .isOut, [a, b] => do
              let va ← eval fuel sig a x y w; let vb ← eval fuel sig b x y w
              let ha ← head? va; let hb ← head? vb
              match matrixGet? w ha hb with
              | some _ => some [0]
              | none => some [1]
          | .isColori, [a, b, c] => do
              let va ← eval fuel sig a x y w; let vb ← eval fuel sig b x y w
              let vc ← eval fuel sig c x y w
              let ha ← head? va; let hb ← head? vb; let hc ← head? vc
              match matrixGet? w ha hb, colorGet? w hc with
              | some cell, some color => if cell = color then some [1] else some [0]
              | _, _ => some [-1]
          | .isEqual, [a, b] => do
              let va ← eval fuel sig a x y w; let vb ← eval fuel sig b x y w
              let ha ← head? va; let hb ← head? vb
              if ha = hb then some [1] else some [0]
          | .inputHeight, [] => some [w.inputHeight]
          | .inputWidth, [] => some [w.inputWidth]
          | .commonHeight, [] => some [w.commonHeight]
          | .commonWidth, [] => some [w.commonWidth]
          | _, _ => none

def loopIter : Nat → Signature Prim → Prog → Nat → List Int → List Int → World → Option (List Int)
  | 0, _, _, _, _, _, _ => none
  | _, _, _, 0, x1, _, _ => some x1
  | fuel + 1, sig, f, k + 1, x1, x2, w => do
      let x1' ← eval fuel sig f x1 x2 w
      let x2' ← singletonHeadIncr x2
      loopIter fuel sig f k x1' x2' w

def loop2Iter :
    Nat → Signature Prim → Prog → Prog → Nat → List Int → List Int → World → Option (List Int)
  | 0, _, _, _, _, _, _, _ => none
  | _, _, _, _, 0, x1, _, _ => some x1
  | fuel + 1, sig, f, g, k + 1, x1, x2, w => do
      let x1' ← eval fuel sig f x1 x2 w
      let x2' ← eval fuel sig g x1 x2 w
      loop2Iter fuel sig f g k x1' x2' w

def loop2sndIter :
    Nat → Signature Prim → Prog → Prog → Nat → List Int → List Int → World → Option (List Int)
  | 0, _, _, _, _, _, _, _ => none
  | _, _, _, _, 0, _, x2, _ => some x2
  | fuel + 1, sig, f, g, k + 1, x1, x2, w => do
      let x1' ← eval fuel sig f x1 x2 w
      let x2' ← eval fuel sig g x1 x2 w
      loop2sndIter fuel sig f g k x1' x2' w

def comprSearch :
    Nat → Signature Prim → Prog → Nat → Nat → List Int → World → Option (List Int)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, sig, f, target, seen, cand, w => do
      let v ← eval fuel sig f cand [0] w
      let hv ← head? v
      if hv ≤ 0 then
        if seen ≥ target then some cand
        else do
          let cand' ← singletonHeadIncr cand
          comprSearch fuel sig f target (seen + 1) cand' w
      else do
        let cand' ← singletonHeadIncr cand
        comprSearch fuel sig f target seen cand' w

end

def termWithWorld (fuel : Nat) (sig : Signature Prim) (p : Prog) (k : Int) (w : World) : Option Int := do
  let out ← eval fuel sig p [k] [0] w
  head? out

def term (fuel : Nat) (sig : Signature Prim) (p : Prog) (k : Int) : Option Int :=
  termWithWorld fuel sig p k defaultWorld

def seqPrefix (fuel : Nat) (sig : Signature Prim) (p : Prog) (len : Nat) : List (Option Int) :=
  (List.range len).map (fun k => term fuel sig p (Int.ofNat k))

/-! ## Extensional equivalence -/

def Extensional (sig : Signature Prim) (p q : Prog) : Prop :=
  ∀ fuel x y w, eval fuel sig p x y w = eval fuel sig q x y w

theorem Extensional.refl (sig : Signature Prim) (p : Prog) : Extensional sig p p :=
  fun _ _ _ _ => rfl

theorem Extensional.symm {sig : Signature Prim} {p q : Prog}
    (h : Extensional sig p q) : Extensional sig q p :=
  fun fuel x y w => (h fuel x y w).symm

theorem Extensional.trans {sig : Signature Prim} {p q r : Prog}
    (h₁ : Extensional sig p q) (h₂ : Extensional sig q r) : Extensional sig p r :=
  fun fuel x y w => (h₁ fuel x y w).trans (h₂ fuel x y w)

def extSetoid (sig : Signature Prim) : Setoid Prog where
  r := Extensional sig
  iseqv :=
    ⟨ Extensional.refl sig
    , fun h => Extensional.symm h
    , fun h₁ h₂ => Extensional.trans h₁ h₂
    ⟩

/-! ## Table instances -/

def orgSignature : Signature Prim :=
  [ entry "zero" 0 0 .zero, entry "one" 0 0 .one, entry "two" 0 0 .two
  , entry "addi" 2 0 .addi, entry "diff" 2 0 .diff, entry "mult" 2 0 .mult
  , entry "divi" 2 0 .divi, entry "modu" 2 0 .modu, entry "cond" 3 0 .cond
  , entry "loop" 3 1 .loop, entry "x" 0 0 .x, entry "y" 0 0 .y
  , entry "compr" 2 1 .compr, entry "loop2" 5 2 .loop2
  ]

def listOps : Signature Prim :=
  [ entry "push" 2 0 .push, entry "pop" 1 0 .pop ]

def intlSignature : Signature Prim := orgSignature ++ listOps
def smtSignature : Signature Prim := orgSignature ++ listOps ++ [entry "loop2snd" 5 2 .loop2snd]
def matchbackSignature : Signature Prim := orgSignature ++ listOps ++ [entry "back" 1 0 .back]

def ramseySignature : Signature Prim :=
  [ entry "zero" 0 0 .zero, entry "one" 0 0 .one, entry "two" 0 0 .two
  , entry "addi" 2 0 .addi, entry "diff" 2 0 .diff, entry "mult" 2 0 .mult
  , entry "divi" 2 0 .divi, entry "modu" 2 0 .modu, entry "cond" 3 0 .cond
  , entry "loop" 3 1 .loop, entry "x" 0 0 .x, entry "y" 0 0 .y
  , entry "loop2" 5 2 .loop2, entry "push" 2 0 .push, entry "pop" 1 0 .pop
  , entry "edge" 1 0 .edge
  ]

def arcagiSignature : Signature Prim :=
  orgSignature ++ listOps ++
  [ entry "equalcolor" 4 0 .equalcolor
  , entry "is_out" 2 0 .isOut
  , entry "is_colori" 3 0 .isColori
  , entry "is_equal" 2 0 .isEqual
  , entry "input_heigth" 0 0 .inputHeight
  , entry "input_width" 0 0 .inputWidth
  , entry "common_height" 0 0 .commonHeight
  , entry "common_width" 0 0 .commonWidth
  ]

namespace P
def z : Prog := .node 0 []
def o : Prog := .node 1 []
def tw : Prog := .node 2 []
def addi (a b : Prog) : Prog := .node 3 [a, b]
def diff (a b : Prog) : Prog := .node 4 [a, b]
def mult (a b : Prog) : Prog := .node 5 [a, b]
def divi (a b : Prog) : Prog := .node 6 [a, b]
def modu (a b : Prog) : Prog := .node 7 [a, b]
def cond (c t e : Prog) : Prog := .node 8 [c, t, e]
def loop (f n x0 : Prog) : Prog := .node 9 [f, n, x0]
def X : Prog := .node 10 []
def Y : Prog := .node 11 []
def compr (f n : Prog) : Prog := .node 12 [f, n]
def loop2 (f g n a b : Prog) : Prog := .node 13 [f, g, n, a, b]
def push (a b : Prog) : Prog := .node 14 [a, b]
def pop (a : Prog) : Prog := .node 15 [a]
def smtLoop2snd (f g n a b : Prog) : Prog := .node 16 [f, g, n, a, b]
def back (a : Prog) : Prog := .node 16 [a]
def ramseyLoop2 (f g n a b : Prog) : Prog := .node 12 [f, g, n, a, b]
def ramseyPush (a b : Prog) : Prog := .node 13 [a, b]
def ramseyPop (a : Prog) : Prog := .node 14 [a]
def edge (a : Prog) : Prog := .node 15 [a]
def equalcolor (a b c d : Prog) : Prog := .node 16 [a, b, c, d]
def isOut (a b : Prog) : Prog := .node 17 [a, b]
def isColori (a b c : Prog) : Prog := .node 18 [a, b, c]
def isEqual (a b : Prog) : Prog := .node 19 [a, b]
def inputHeight : Prog := .node 20 []
def inputWidth : Prog := .node 21 []
def commonHeight : Prog := .node 22 []
def commonWidth : Prog := .node 23 []
end P

/-! ## Non-vacuity and parser examples -/

example : WellFormed orgSignature (P.mult P.X P.X) :=
  recognize_sound (sig := orgSignature) (toks := [10, 10, 5]) (p := P.mult P.X P.X) rfl

example : ¬ WellFormed orgSignature (.node 5 [P.X]) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [entryAt, listGet?, orgSignature] at hentry
      cases hentry
      simp [entry] at hlen

example : WellFormed intlSignature (P.push P.X P.Y) :=
  recognize_sound (sig := intlSignature) (toks := [10, 11, 14]) (p := P.push P.X P.Y) rfl

example : WellFormed smtSignature (P.smtLoop2snd P.X P.Y P.X P.X P.Y) :=
  recognize_sound (sig := smtSignature) (toks := [10, 11, 10, 10, 11, 16])
    (p := P.smtLoop2snd P.X P.Y P.X P.X P.Y) rfl

example : WellFormed matchbackSignature (P.back P.X) :=
  recognize_sound (sig := matchbackSignature) (toks := [10, 16]) (p := P.back P.X) rfl

example : WellFormed ramseySignature (P.edge P.X) :=
  recognize_sound (sig := ramseySignature) (toks := [10, 15]) (p := P.edge P.X) rfl

example : WellFormed arcagiSignature (P.isEqual P.X P.X) :=
  recognize_sound (sig := arcagiSignature) (toks := [10, 10, 19]) (p := P.isEqual P.X P.X) rfl

example : ¬ WellFormed arcagiSignature (.node 16 [P.X, P.X]) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [entryAt, listGet?, arcagiSignature, orgSignature, listOps] at hentry
      cases hentry
      simp [entry] at hlen

/-! ## Validation -/

-- E2 `org`: factorial by `loop (mult x y) x one`.
#eval seqPrefix 400 orgSignature (P.loop (P.mult P.X P.Y) P.X P.o) 7
-- List ops: push the input onto `[0]`, then pop back to `[0]`.
#eval seqPrefix 80 intlSignature (P.pop (P.push P.X P.Y)) 6
-- Matchback default vector, grounded in `exec_memo.sml` lines 381-383.
#eval seqPrefix 80 matchbackSignature (P.back P.X) 5
-- Ramsey edge oracle with explicit world values.
#eval (List.range 5).map
  (fun k => termWithWorld 80 ramseySignature (P.edge P.X) (Int.ofNat k)
    { defaultWorld with edgeValues := [7, 8, 9] })
-- Arcagi default 1x1 matrix and dimensions.
#eval term 80 arcagiSignature (P.equalcolor P.z P.z P.z P.z) 0
#eval seqPrefix 80 arcagiSignature (P.isOut P.X P.z) 4
-- SMT `loop2snd`: increment the second register `x` times, returning the second component.
#eval seqPrefix 200 smtSignature
  (P.smtLoop2snd (P.addi P.X P.o) (P.addi P.Y P.o) P.X P.X P.Y) 6
-- Explicit partial operations.
#eval eval 20 orgSignature (P.divi P.X P.z) [5] [0] defaultWorld
#eval eval 20 orgSignature (P.modu P.X P.z) [5] [0] defaultWorld
#eval eval 20 intlSignature (P.pop P.Y) [0] [] defaultWorld
#eval eval 20 matchbackSignature (P.back P.X) [99] [0] defaultWorld
#eval eval 20 ramseySignature (P.edge P.X) [0] [0] defaultWorld

end Mettapedia.GSLT.LanguageDef.GauthierE2
