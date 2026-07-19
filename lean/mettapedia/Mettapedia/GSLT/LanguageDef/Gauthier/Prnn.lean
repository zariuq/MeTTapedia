/-
# Gauthier PRNN languageDef

This file models the `exec_prnn.sml` recurrent/list-valued substrate as its own
Gauthier languageDef.  It reuses the generic E1 syntax and parser layer, but the
evaluator is distinct: programs run over two integer-list registers and may read
the PRNN globals `prog`, `seq`, and `embv`.

Grounding:
  * `repos/oeis-synthesis/src/kernel.sml` lines 372-373: `prnn_operl`.
  * `repos/oeis-synthesis/src/kernel.sml` lines 466-478: extra PRNN higher-order arities.
  * `repos/oeis-synthesis/src/exec_prnn.sml` lines 157-174: constants/registers/arithmetic.
  * `repos/oeis-synthesis/src/exec_prnn.sml` lines 179-203: conditionals, `push`, and `pop`.
  * `repos/oeis-synthesis/src/exec_prnn.sml` lines 265-338: loops and comprehension.
  * `repos/oeis-synthesis/src/exec_prnn.sml` lines 348-372: `prog`, `embv`, `seq`, and `execv`.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.E1

namespace Mettapedia.GSLT.LanguageDef.GauthierPrnn

open Mettapedia.GSLT.LanguageDef.GauthierE1

inductive Prim where
  | zero | one | two
  | addi | diff | mult | divi | modu
  | cond | loop | x | y | compr | loop2
  | push | pop | prog | embv | seq
  deriving DecidableEq, Repr

structure Env where
  prog : List Int
  seq : List Int
  embv : List (List Int)
  deriving Repr

def defaultEnv : Env := { prog := [], seq := [], embv := [] }

def head? : List Int -> Option Int
  | [] => none
  | x :: _ => some x

def singletonHeadIncr : List Int -> Option (List Int)
  | [] => none
  | x :: _ => some [x + 1]

def mkE (f : Int -> Int -> Option Int) : List Int -> List Int -> Option (List Int)
  | a :: m, b :: _ => do
      let c <- f a b
      some (c :: m)
  | _, _ => none

def add? (a b : Int) : Option Int := some (a + b)
def sub? (a b : Int) : Option Int := some (a - b)
def mul? (a b : Int) : Option Int := some (a * b)

def modIndex? (i : Int) : Nat -> Option Nat
  | 0 => none
  | n + 1 =>
      let d := Int.ofNat (n + 1)
      let r := Int.fmod i d
      let r' := if r < 0 then r + d else r
      some r'.toNat

def embvGet? (env : Env) (i : Int) : Option (List Int) := do
  let n <- modIndex? i env.embv.length
  listGet? env.embv n

mutual

def eval : Nat -> Signature Prim -> Prog -> List Int -> List Int -> Env -> Option (List Int)
  | 0, _, _, _, _, _ => none
  | fuel + 1, sig, .node id ch, x, y, env =>
      match entryAt sig id with
      | none => none
      | some e =>
          match e.prim, ch with
          | .zero, [] => some [0]
          | .one, [] => some [1]
          | .two, [] => some [2]
          | .x, [] => some x
          | .y, [] => some y
          | .prog, [] => some env.prog
          | .seq, [] => some env.seq
          | .embv, [a] => do
              let va <- eval fuel sig a x y env
              let ha <- head? va
              embvGet? env ha
          | .addi, [a, b] => do
              let va <- eval fuel sig a x y env
              let vb <- eval fuel sig b x y env
              mkE add? va vb
          | .diff, [a, b] => do
              let va <- eval fuel sig a x y env
              let vb <- eval fuel sig b x y env
              mkE sub? va vb
          | .mult, [a, b] => do
              let va <- eval fuel sig a x y env
              let vb <- eval fuel sig b x y env
              mkE mul? va vb
          | .divi, [a, b] => do
              let va <- eval fuel sig a x y env
              let vb <- eval fuel sig b x y env
              mkE sdiv va vb
          | .modu, [a, b] => do
              let va <- eval fuel sig a x y env
              let vb <- eval fuel sig b x y env
              mkE smod va vb
          | .cond, [c, t, e'] => do
              let vc <- eval fuel sig c x y env
              let hc <- head? vc
              if hc <= 0 then eval fuel sig t x y env else eval fuel sig e' x y env
          | .push, [a, b] => do
              let va <- eval fuel sig a x y env
              let vb <- eval fuel sig b x y env
              let ha <- head? va
              some (ha :: vb)
          | .pop, [a] => do
              let va <- eval fuel sig a x y env
              match va with
              | [] => none
              | [z] => some [z]
              | _ :: zs => some zs
          | .loop, [f, n, x0] => do
              let vn <- eval fuel sig n x y env
              let vx0 <- eval fuel sig x0 x y env
              let hn <- head? vn
              if hn <= 0 then some vx0 else loopIter fuel sig f hn.toNat vx0 [1] env
          | .loop2, [f, g, n, a, b] => do
              let vn <- eval fuel sig n x y env
              let va <- eval fuel sig a x y env
              let vb <- eval fuel sig b x y env
              let hn <- head? vn
              if hn <= 0 then some va else loop2Iter fuel sig f g hn.toNat va vb env
          | .compr, [f, n] => do
              let vn <- eval fuel sig n x y env
              let hn <- head? vn
              comprSearch fuel sig f hn (-1) [-1] env
          | _, _ => none

def loopIter :
    Nat -> Signature Prim -> Prog -> Nat -> List Int -> List Int -> Env -> Option (List Int)
  | 0, _, _, _, _, _, _ => none
  | _, _, _, 0, x1, _, _ => some x1
  | fuel + 1, sig, f, k + 1, x1, x2, env => do
      let x1' <- eval fuel sig f x1 x2 env
      let x2' <- singletonHeadIncr x2
      loopIter fuel sig f k x1' x2' env

def loop2Iter :
    Nat -> Signature Prim -> Prog -> Prog -> Nat -> List Int -> List Int -> Env -> Option (List Int)
  | 0, _, _, _, _, _, _, _ => none
  | _, _, _, _, 0, x1, _, _ => some x1
  | fuel + 1, sig, f, g, k + 1, x1, x2, env => do
      let x1' <- eval fuel sig f x1 x2 env
      let x2' <- eval fuel sig g x1 x2 env
      loop2Iter fuel sig f g k x1' x2' env

def comprSearch :
    Nat -> Signature Prim -> Prog -> Int -> Int -> List Int -> Env -> Option (List Int)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, sig, f, target, seen, cand, env =>
      if seen >= target then some cand
      else do
        let cand' <- singletonHeadIncr cand
        let v <- eval fuel sig f cand' [0] env
        let hv <- head? v
        if hv <= 0 then
          comprSearch fuel sig f target (seen + 1) cand' env
        else
          comprSearch fuel sig f target seen cand' env

end

def termWithEnv (fuel : Nat) (sig : Signature Prim) (p : Prog) (k : Int) (env : Env) :
    Option Int := do
  let out <- eval fuel sig p [k] [0] env
  head? out

def term (fuel : Nat) (sig : Signature Prim) (p : Prog) (k : Int) : Option Int :=
  termWithEnv fuel sig p k defaultEnv

def seqPrefix (fuel : Nat) (sig : Signature Prim) (p : Prog) (len : Nat) :
    List (Option Int) :=
  (List.range len).map (fun k => term fuel sig p (Int.ofNat k))

def Extensional (sig : Signature Prim) (p q : Prog) : Prop :=
  forall fuel x y env, eval fuel sig p x y env = eval fuel sig q x y env

theorem Extensional.refl (sig : Signature Prim) (p : Prog) : Extensional sig p p :=
  fun _ _ _ _ => rfl

theorem Extensional.symm {sig : Signature Prim} {p q : Prog}
    (h : Extensional sig p q) : Extensional sig q p :=
  fun fuel x y env => (h fuel x y env).symm

theorem Extensional.trans {sig : Signature Prim} {p q r : Prog}
    (h1 : Extensional sig p q) (h2 : Extensional sig q r) : Extensional sig p r :=
  fun fuel x y env => (h1 fuel x y env).trans (h2 fuel x y env)

def extSetoid (sig : Signature Prim) : Setoid Prog where
  r := Extensional sig
  iseqv := {
    refl := Extensional.refl sig
    symm := fun h => Extensional.symm h
    trans := fun h1 h2 => Extensional.trans h1 h2
  }

def prnnSignature : Signature Prim :=
  [ entry "zero" 0 0 .zero
  , entry "one" 0 0 .one
  , entry "two" 0 0 .two
  , entry "addi" 2 0 .addi
  , entry "diff" 2 0 .diff
  , entry "mult" 2 0 .mult
  , entry "divi" 2 0 .divi
  , entry "modu" 2 0 .modu
  , entry "cond" 3 0 .cond
  , entry "loop" 3 1 .loop
  , entry "x" 0 0 .x
  , entry "y" 0 0 .y
  , entry "compr" 2 1 .compr
  , entry "loop2" 5 2 .loop2
  , entry "push" 2 0 .push
  , entry "pop" 1 0 .pop
  , entry "prog" 0 0 .prog
  , entry "embv" 1 0 .embv
  , entry "seq" 0 0 .seq
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
def prog : Prog := .node 16 []
def embv (a : Prog) : Prog := .node 17 [a]
def seq : Prog := .node 18 []

end P

theorem push_wellFormed : WellFormed prnnSignature (P.push P.X P.Y) :=
  recognize_sound (sig := prnnSignature) (toks := [10, 11, 14])
    (p := P.push P.X P.Y) rfl

theorem embv_wellFormed : WellFormed prnnSignature (P.embv P.X) :=
  recognize_sound (sig := prnnSignature) (toks := [10, 17])
    (p := P.embv P.X) rfl

theorem bad_embv_not_wellFormed :
    Not (WellFormed prnnSignature (.node 17 [])) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [prnnSignature, entryAt, listGet?] at hentry
      cases hentry
      simp [entry] at hlen

theorem bad_seq_not_wellFormed :
    Not (WellFormed prnnSignature (.node 18 [P.X])) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [prnnSignature, entryAt, listGet?] at hentry
      cases hentry
      simp [entry] at hlen

def sampleEnv : Env :=
  { prog := [42, 7], seq := [3, 1, 4], embv := [[5], [8], [13]] }

-- PRNN/org factorial by `loop (mult x y) x one`.
#eval seqPrefix 500 prnnSignature (P.loop (P.mult P.X P.Y) P.X P.o) 7
-- List operations.
#eval seqPrefix 80 prnnSignature (P.pop (P.push P.X P.Y)) 6
-- PRNN globals.
#eval termWithEnv 40 prnnSignature P.prog 0 sampleEnv
#eval termWithEnv 40 prnnSignature P.seq 0 sampleEnv
#eval termWithEnv 40 prnnSignature (P.embv P.X) 1 sampleEnv
-- Comprehension starts at `[-1]` and returns the first nonpositive candidate for target zero.
#eval term 120 prnnSignature (P.compr P.X P.z) 0
-- Explicit partial operations.
#eval eval 20 prnnSignature (P.divi P.X P.z) [5] [0] defaultEnv
#eval eval 20 prnnSignature (P.modu P.X P.z) [5] [0] defaultEnv
#eval eval 20 prnnSignature (P.pop P.Y) [0] [] defaultEnv
#eval eval 20 prnnSignature (P.embv P.X) [0] [0] defaultEnv

end Mettapedia.GSLT.LanguageDef.GauthierPrnn
