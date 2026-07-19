/-
# Gauthier `ctree`: complex-tree typed variant

This is the complex-tree substrate from `repos/oeis-synthesis/src/exec_ctree.sml`.  The base `org`
operators act on the root label of a complex-valued tree while preserving the left operand's tree
shape; tree operators (`push`, `pop`, `popr`, `push2`) manipulate the tree structure; rational/complex
operators (`cdivr`, `cfloor`, `cnumer`, `cdenom`, `cgcd`, `cimag`, `crealpart`, `cimagpart`) mirror
`exec_prim.sml`.

The parser layer is shared with `E1.lean`: `Signature` entries are first-class data, `Prog` stores
table indices, and `recognize_sound` checks well-formedness for this table without a new parser proof.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.E1
import Mettapedia.GSLT.LanguageDef.Gauthier.Number

namespace Mettapedia.GSLT.LanguageDef.GauthierCTree

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierNumber

inductive Prim where
  | zero | one | two
  | addi | diff | mult | divi | modu
  | cond | loop | x | y | compr | loop2
  | push | pop | popr | push2
  | cdivr | cfloor | cnumer | cdenom | cgcd
  | cimag | crealpart | cimagpart
  deriving DecidableEq, Repr

def binRoot? (f : ComplexVal -> ComplexVal -> Option ComplexVal)
    (a b : CTree) : Option CTree :=
  CTree.binRoot? f a b

def unaryRoot? (f : ComplexVal -> Option ComplexVal) (a : CTree) : Option CTree :=
  CTree.mapRoot? f a

mutual

def eval : Nat -> Signature Prim -> Prog -> CTree -> CTree -> Option CTree
  | 0, _, _, _, _ => none
  | fuel + 1, sig, .node id ch, x, y =>
      match entryAt sig id with
      | none => none
      | some e =>
          match e.prim, ch with
          | .zero, [] => some CTree.zero
          | .one, [] => some CTree.one
          | .two, [] => some CTree.two
          | .x, [] => some x
          | .y, [] => some y
          | .addi, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              binRoot? ComplexVal.add? va vb
          | .diff, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              binRoot? ComplexVal.sub? va vb
          | .mult, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              binRoot? ComplexVal.mul? va vb
          | .divi, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              binRoot? ComplexVal.divi? va vb
          | .modu, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              binRoot? ComplexVal.modu? va vb
          | .cond, [c, t, e'] => do
              let vc <- eval fuel sig c x y
              if ComplexVal.leq0 vc.root then eval fuel sig t x y else eval fuel sig e' x y
          | .push, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              some (CTree.push va vb)
          | .pop, [a] => do
              let va <- eval fuel sig a x y
              some va.pop
          | .popr, [a] => do
              let va <- eval fuel sig a x y
              some va.popr
          | .push2, [a, b, c] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              let vc <- eval fuel sig c x y
              some (CTree.push2 va vb vc)
          | .loop, [f, n, x0] => do
              let vn <- eval fuel sig n x y
              let vx0 <- eval fuel sig x0 x y
              let hn <- CTree.bound? vn
              if hn <= 0 then some vx0 else loopIter fuel sig f hn.toNat vx0 CTree.one
          | .loop2, [f, g, n, a, b] => do
              let vn <- eval fuel sig n x y
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              let hn <- CTree.bound? vn
              if hn <= 0 then some va else loop2Iter fuel sig f g hn.toNat va vb
          | .compr, [f, n] => do
              let vn <- eval fuel sig n x y
              let hn <- CTree.bound? vn
              if hn < 0 then none else comprSearch fuel sig f hn.toNat 0 CTree.zero
          | .cdivr, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              binRoot? ComplexVal.divr? va vb
          | .cfloor, [a] => do
              let va <- eval fuel sig a x y
              unaryRoot? ComplexVal.floor? va
          | .cnumer, [a] => do
              let va <- eval fuel sig a x y
              unaryRoot? ComplexVal.numer? va
          | .cdenom, [a] => do
              let va <- eval fuel sig a x y
              unaryRoot? ComplexVal.denom? va
          | .cgcd, [a, b] => do
              let va <- eval fuel sig a x y
              let vb <- eval fuel sig b x y
              binRoot? ComplexVal.gcd? va vb
          | .cimag, [] => some CTree.imag
          | .crealpart, [a] => do
              let va <- eval fuel sig a x y
              some (va.replaceRoot va.root.realPart)
          | .cimagpart, [a] => do
              let va <- eval fuel sig a x y
              some (va.replaceRoot va.root.imagPart)
          | _, _ => none

def loopIter : Nat -> Signature Prim -> Prog -> Nat -> CTree -> CTree -> Option CTree
  | 0, _, _, _, _, _ => none
  | _, _, _, 0, x1, _ => some x1
  | fuel + 1, sig, f, k + 1, x1, x2 => do
      let x1' <- eval fuel sig f x1 x2
      loopIter fuel sig f k x1' x2.incr

def loop2Iter : Nat -> Signature Prim -> Prog -> Prog -> Nat -> CTree -> CTree -> Option CTree
  | 0, _, _, _, _, _, _ => none
  | _, _, _, _, 0, x1, _ => some x1
  | fuel + 1, sig, f, g, k + 1, x1, x2 => do
      let x1' <- eval fuel sig f x1 x2
      let x2' <- eval fuel sig g x1 x2
      loop2Iter fuel sig f g k x1' x2'

def comprSearch : Nat -> Signature Prim -> Prog -> Nat -> Nat -> CTree -> Option CTree
  | 0, _, _, _, _, _ => none
  | fuel + 1, sig, f, target, seen, cand => do
      let v <- eval fuel sig f cand CTree.zero
      if ComplexVal.leq0 v.root then
        if seen >= target then some cand
        else comprSearch fuel sig f target (seen + 1) cand.incr
      else comprSearch fuel sig f target seen cand.incr

end

def term (fuel : Nat) (sig : Signature Prim) (p : Prog) (k : Int) : Option Int := do
  let out <- eval fuel sig p (CTree.ofComplex { re := RatVal.ofInt k, im := RatVal.zero }) CTree.zero
  CTree.returnInt? out

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

def ctreeOps : Signature Prim :=
  [ entry "push" 2 0 .push, entry "pop" 1 0 .pop, entry "popr" 1 0 .popr
  , entry "push2" 3 0 .push2, entry "cdivr" 2 0 .cdivr, entry "cfloor" 1 0 .cfloor
  , entry "cnumer" 1 0 .cnumer, entry "cdenom" 1 0 .cdenom, entry "cgcd" 2 0 .cgcd
  , entry "cimag" 0 0 .cimag, entry "crealpart" 1 0 .crealpart
  , entry "cimagpart" 1 0 .cimagpart
  ]

def ctreeSignature : Signature Prim := orgSignature ++ ctreeOps

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
def popr (a : Prog) : Prog := .node 16 [a]
def push2 (a b c : Prog) : Prog := .node 17 [a, b, c]
def cdivr (a b : Prog) : Prog := .node 18 [a, b]
def cfloor (a : Prog) : Prog := .node 19 [a]
def cnumer (a : Prog) : Prog := .node 20 [a]
def cdenom (a : Prog) : Prog := .node 21 [a]
def cgcd (a b : Prog) : Prog := .node 22 [a, b]
def cimag : Prog := .node 23 []
def crealpart (a : Prog) : Prog := .node 24 [a]
def cimagpart (a : Prog) : Prog := .node 25 [a]
end P

example : WellFormed ctreeSignature (P.cfloor (P.cdivr P.X P.tw)) :=
  recognize_sound (sig := ctreeSignature) (toks := [10, 2, 18, 19])
    (p := P.cfloor (P.cdivr P.X P.tw)) rfl

example : WellFormed ctreeSignature (P.popr (P.push2 P.X P.o P.tw)) :=
  recognize_sound (sig := ctreeSignature) (toks := [10, 1, 2, 17, 16])
    (p := P.popr (P.push2 P.X P.o P.tw)) rfl

example : ¬ WellFormed ctreeSignature (.node 17 [P.X, P.X]) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [entryAt, listGet?, ctreeSignature, orgSignature, ctreeOps] at hentry
      cases hentry
      simp [entry] at hlen

#eval seqPrefix 200 ctreeSignature P.X 8
#eval seqPrefix 200 ctreeSignature (P.cfloor (P.cdivr P.X P.tw)) 8
#eval seqPrefix 400 ctreeSignature (P.loop (P.mult P.X P.Y) P.X P.o) 7
#eval seqPrefix 120 ctreeSignature (P.push P.X P.Y) 5
#eval seqPrefix 120 ctreeSignature (P.pop (P.push P.X P.Y)) 5
#eval seqPrefix 120 ctreeSignature (P.popr (P.push2 P.X P.o P.tw)) 5
#eval seqPrefix 120 ctreeSignature (P.cimagpart P.cimag) 4
#eval eval 20 ctreeSignature (P.divi P.X P.z)
  (CTree.ofComplex { re := RatVal.ofInt 5, im := RatVal.zero }) CTree.zero
#eval eval 20 ctreeSignature (P.cdivr P.cimag P.z) CTree.zero CTree.zero
#eval eval 20 ctreeSignature (P.cdenom P.cimag) CTree.zero CTree.zero

end Mettapedia.GSLT.LanguageDef.GauthierCTree
