/-
# Gauthier `wrat`: rational-list typed variant

This is the `wrat` substrate from `repos/oeis-synthesis/src/exec_wrat.sml`: the base `org` evaluator
is retyped from integer lists to rational lists, then extended with `push`, `pop`, `while2`, rational
division `divr`, and `floor`.  The parser layer is shared with `E1.lean`: table entries are data,
program nodes store table indices, and `recognize_sound` supplies the WellFormed proof.

Grounding:
  * `kernel.sml` lines 367-372: `wrat_operl`.
  * `kernel.sml` lines 468-475 and 489-514: higher-order arities, especially `while2` with ho-arity 3.
  * `exec_wrat.sml` lines 103-283: rational-list evaluator, loops, `while2`, comprehension, and table
    assembly.
  * `exec_prim.sml` lines 58-142 and 263-280: rational primitives and OEIS integer return.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.E1
import Mettapedia.GSLT.LanguageDef.Gauthier.Number

namespace Mettapedia.GSLT.LanguageDef.GauthierWrat

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierNumber

inductive Prim where
  | zero | one | two
  | addi | diff | mult | divi | modu
  | cond | loop | x | y | compr | loop2
  | push | pop | while2 | divr | floor
  deriving DecidableEq, Repr

def head? : List RatVal -> Option RatVal
  | [] => none
  | x :: _ => some x

def singletonHeadIncr : List RatVal -> Option (List RatVal)
  | [] => none
  | x :: _ => some [RatVal.incr x]

def mkE (f : RatVal -> RatVal -> Option RatVal) : List RatVal -> List RatVal -> Option (List RatVal)
  | a :: m, b :: _ => do
      let c <- f a b
      some (c :: m)
  | _, _ => none

def pushl : List RatVal -> List RatVal -> Option (List RatVal)
  | a :: _, ys => some (a :: ys)
  | [], _ => none

def popl : List RatVal -> Option (List RatVal)
  | [] => none
  | [a] => some [a]
  | _ :: m => some m

def bound? (xs : List RatVal) : Option Int := do
  let x <- head? xs
  RatVal.returnInt? x

mutual

def eval : Nat -> Signature Prim -> Prog -> List RatVal -> List RatVal -> Option (List RatVal)
  | 0, _, _, _, _ => none
  | fuel + 1, sig, .node id ch, x, y =>
      match entryAt sig id with
      | none => none
      | some e =>
          match e.prim, ch with
          | .zero, [] => some [RatVal.zero]
          | .one, [] => some [RatVal.one]
          | .two, [] => some [RatVal.two]
          | .x, [] => some x
          | .y, [] => some y
          | .addi, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              mkE RatVal.add? va vb
          | .diff, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              mkE RatVal.sub? va vb
          | .mult, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              mkE RatVal.mul? va vb
          | .divi, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              mkE RatVal.divi? va vb
          | .modu, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              mkE RatVal.modu? va vb
          | .cond, [c, t, e'] => do
              let vc <- eval fuel sig c x y
              let hc <- head? vc
              if RatVal.leq0 hc then eval fuel sig t x y else eval fuel sig e' x y
          | .push, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              pushl va vb
          | .pop, [a] => do
              let va <- eval fuel sig a x y
              popl va
          | .loop, [f, n, x0] => do
              let vn <- eval fuel sig n x y
              let vx0 <- eval fuel sig x0 x y
              let hn <- bound? vn
              if hn <= 0 then some vx0 else loopIter fuel sig f hn.toNat vx0 [RatVal.one]
          | .loop2, [f, g, n, a, b] => do
              let vn <- eval fuel sig n x y
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              let hn <- bound? vn
              if hn <= 0 then some va else loop2Iter fuel sig f g hn.toNat va vb
          | .while2, [f, g, p, a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              while2Iter fuel sig f g p va vb
          | .compr, [f, n] => do
              let vn <- eval fuel sig n x y
              let hn <- bound? vn
              if hn < 0 then none else comprSearch fuel sig f hn.toNat 0 [RatVal.zero]
          | .divr, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              mkE RatVal.divr? va vb
          | .floor, [a] => do
              let va <- eval fuel sig a x y
              match va with
              | [] => none
              | h :: t => do
                  let h' <- RatVal.floor? h
                  some (h' :: t)
          | _, _ => none

def loopIter : Nat -> Signature Prim -> Prog -> Nat -> List RatVal -> List RatVal ->
    Option (List RatVal)
  | 0, _, _, _, _, _ => none
  | _, _, _, 0, x1, _ => some x1
  | fuel + 1, sig, f, k + 1, x1, x2 => do
      let x1' <- eval fuel sig f x1 x2
      let x2' <- singletonHeadIncr x2
      loopIter fuel sig f k x1' x2'

def loop2Iter : Nat -> Signature Prim -> Prog -> Prog -> Nat -> List RatVal -> List RatVal ->
    Option (List RatVal)
  | 0, _, _, _, _, _, _ => none
  | _, _, _, _, 0, x1, _ => some x1
  | fuel + 1, sig, f, g, k + 1, x1, x2 => do
      let x1' <- eval fuel sig f x1 x2
      let x2' <- eval fuel sig g x1 x2
      loop2Iter fuel sig f g k x1' x2'

def while2Iter : Nat -> Signature Prim -> Prog -> Prog -> Prog -> List RatVal -> List RatVal ->
    Option (List RatVal)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, sig, f, g, p, x1, x2 => do
      let vp <- eval fuel sig p x1 x2
      let hp <- head? vp
      if RatVal.leq0 hp then some x1
      else do
        let x1' <- eval fuel sig f x1 x2
        let x2' <- eval fuel sig g x1 x2
        while2Iter fuel sig f g p x1' x2'

def comprSearch : Nat -> Signature Prim -> Prog -> Nat -> Nat -> List RatVal ->
    Option (List RatVal)
  | 0, _, _, _, _, _ => none
  | fuel + 1, sig, f, target, seen, cand => do
      let v <- eval fuel sig f cand [RatVal.zero]
      let hv <- head? v
      if RatVal.leq0 hv then
        if seen >= target then some cand
        else do
          let cand' <- singletonHeadIncr cand
          comprSearch fuel sig f target (seen + 1) cand'
      else do
        let cand' <- singletonHeadIncr cand
        comprSearch fuel sig f target seen cand'

end

def term (fuel : Nat) (sig : Signature Prim) (p : Prog) (k : Int) : Option Int := do
  let out <- eval fuel sig p [RatVal.ofInt k] [RatVal.zero]
  let h <- head? out
  RatVal.returnInt? h

def seqPrefix (fuel : Nat) (sig : Signature Prim) (p : Prog) (len : Nat) : List (Option Int) :=
  (List.range len).map (fun k => term fuel sig p (Int.ofNat k))

def Extensional (sig : Signature Prim) (p q : Prog) : Prop :=
  forall fuel x y, eval fuel sig p x y = eval fuel sig q x y

theorem Extensional.refl (sig : Signature Prim) (p : Prog) : Extensional sig p p :=
  fun _ _ _ => rfl

theorem Extensional.symm {sig : Signature Prim} {p q : Prog}
    (h : Extensional sig p q) : Extensional sig q p :=
  fun fuel x y => (h fuel x y).symm

theorem Extensional.trans {sig : Signature Prim} {p q r : Prog}
    (h1 : Extensional sig p q) (h2 : Extensional sig q r) : Extensional sig p r :=
  fun fuel x y => (h1 fuel x y).trans (h2 fuel x y)

def extSetoid (sig : Signature Prim) : Setoid Prog where
  r := Extensional sig
  iseqv :=
    ⟨ Extensional.refl sig
    , fun h => Extensional.symm h
    , fun h1 h2 => Extensional.trans h1 h2
    ⟩

def orgSignature : Signature Prim :=
  [ entry "zero" 0 0 .zero, entry "one" 0 0 .one, entry "two" 0 0 .two
  , entry "addi" 2 0 .addi, entry "diff" 2 0 .diff, entry "mult" 2 0 .mult
  , entry "divi" 2 0 .divi, entry "modu" 2 0 .modu, entry "cond" 3 0 .cond
  , entry "loop" 3 1 .loop, entry "x" 0 0 .x, entry "y" 0 0 .y
  , entry "compr" 2 1 .compr, entry "loop2" 5 2 .loop2
  ]

def wratOps : Signature Prim :=
  [ entry "push" 2 0 .push, entry "pop" 1 0 .pop, entry "while2" 5 3 .while2
  , entry "divr" 2 0 .divr, entry "floor" 1 0 .floor
  ]

def wratSignature : Signature Prim := orgSignature ++ wratOps

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
def while2 (f g p a b : Prog) : Prog := .node 16 [f, g, p, a, b]
def divr (a b : Prog) : Prog := .node 17 [a, b]
def floor (a : Prog) : Prog := .node 18 [a]
end P

example : WellFormed wratSignature (P.floor (P.divr P.X P.tw)) :=
  recognize_sound (sig := wratSignature) (toks := [10, 2, 17, 18])
    (p := P.floor (P.divr P.X P.tw)) rfl

example : WellFormed wratSignature
    (P.while2 (P.addi P.X P.o) P.Y (P.diff P.tw P.X) P.z P.z) :=
  recognize_sound (sig := wratSignature) (toks := [10, 1, 3, 11, 2, 10, 4, 0, 0, 16])
    (p := P.while2 (P.addi P.X P.o) P.Y (P.diff P.tw P.X) P.z P.z) rfl

example : ¬ WellFormed wratSignature (.node 16 [P.X]) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [entryAt, listGet?, wratSignature, orgSignature, wratOps] at hentry
      cases hentry
      simp [entry] at hlen

#eval seqPrefix 200 wratSignature P.X 8
#eval seqPrefix 200 wratSignature (P.floor (P.divr P.X P.tw)) 8
#eval seqPrefix 400 wratSignature (P.loop (P.mult P.X P.Y) P.X P.o) 7
#eval seqPrefix 200 wratSignature (P.while2 (P.addi P.X P.o) P.Y (P.diff P.tw P.X) P.z P.z) 4
#eval eval 20 wratSignature (P.divi P.X P.z) [RatVal.ofInt 5] [RatVal.zero]
#eval eval 20 wratSignature (P.modu P.X P.z) [RatVal.ofInt 5] [RatVal.zero]
#eval eval 20 wratSignature (P.divr P.X P.z) [RatVal.ofInt 5] [RatVal.zero]
#eval eval 20 wratSignature (P.pop P.Y) [RatVal.zero] []

end Mettapedia.GSLT.LanguageDef.GauthierWrat
