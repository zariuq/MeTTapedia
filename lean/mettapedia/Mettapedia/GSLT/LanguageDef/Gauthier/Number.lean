/-
# Source-style rationals and complexes for Gauthier's typed OEIS variants

This file isolates the numeric substrate shared by the `wrat` and `ctree` executors.  It follows
`repos/oeis-synthesis/src/exec_prim.sml`: rationals are normalized integer pairs, complex numbers are
pairs of rationals, integer division/modulo stay partial at zero divisors, and rational integer
division/modulo are available only when both operands are integer rationals.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierNumber

/-- Source rational `rat = IntInf.int * IntInf.int`, kept normalized with positive denominator. -/
structure RatVal where
  num : Int
  den : Int
  deriving DecidableEq, Repr

def RatVal.ofInt (n : Int) : RatVal := { num := n, den := 1 }

def RatVal.reduce (n d : Int) : Option RatVal :=
  if d = 0 then none
  else
    let n' := if d < 0 then -n else n
    let d' := if d < 0 then -d else d
    match Nat.gcd n'.natAbs d'.natAbs with
    | 0 => none
    | g + 1 =>
        let divisor : Int := Int.ofNat (g + 1)
        some { num := Int.fdiv n' divisor, den := Int.fdiv d' divisor }

def RatVal.zero : RatVal := RatVal.ofInt 0
def RatVal.one : RatVal := RatVal.ofInt 1
def RatVal.two : RatVal := RatVal.ofInt 2
def RatVal.negOne : RatVal := RatVal.ofInt (-1)

def RatVal.add? (a b : RatVal) : Option RatVal :=
  RatVal.reduce (a.num * b.den + b.num * a.den) (a.den * b.den)

def RatVal.sub? (a b : RatVal) : Option RatVal :=
  RatVal.reduce (a.num * b.den - b.num * a.den) (a.den * b.den)

def RatVal.mul? (a b : RatVal) : Option RatVal :=
  RatVal.reduce (a.num * b.num) (a.den * b.den)

def RatVal.divr? (a b : RatVal) : Option RatVal :=
  if b.num = 0 then none else RatVal.reduce (a.num * b.den) (a.den * b.num)

def RatVal.divi? (a b : RatVal) : Option RatVal :=
  if a.den = 1 && b.den = 1 then
    if b.num = 0 then none else some (RatVal.ofInt (Int.fdiv a.num b.num))
  else none

def RatVal.modu? (a b : RatVal) : Option RatVal :=
  if a.den = 1 && b.den = 1 then
    if b.num = 0 then none else some (RatVal.ofInt (Int.fmod a.num b.num))
  else none

def RatVal.gcd? (a b : RatVal) : Option RatVal :=
  if a.den = 1 && b.den = 1 then
    some (RatVal.ofInt (Int.ofNat (Nat.gcd a.num.natAbs b.num.natAbs)))
  else none

def RatVal.floor? (a : RatVal) : Option RatVal :=
  if a.den = 0 then none else some (RatVal.ofInt (Int.fdiv a.num a.den))

def RatVal.numer? (a : RatVal) : Option RatVal := some (RatVal.ofInt a.num)
def RatVal.denom? (a : RatVal) : Option RatVal := some (RatVal.ofInt a.den)

def RatVal.leq0 (a : RatVal) : Bool := a.num <= 0

/-- Source `rincr`: increment the numerator, used on integer-valued counters. -/
def RatVal.incr (a : RatVal) : RatVal := { a with num := a.num + 1 }

def RatVal.floorInt? (a : RatVal) : Option Int := do
  let q <- RatVal.floor? a
  some q.num

def RatVal.returnInt? (a : RatVal) : Option Int :=
  if a.den = 1 then some a.num else RatVal.floorInt? a

/-- Source complex `complex = rat * rat`. -/
structure ComplexVal where
  re : RatVal
  im : RatVal
  deriving DecidableEq, Repr

def ComplexVal.zero : ComplexVal := { re := RatVal.zero, im := RatVal.zero }
def ComplexVal.one : ComplexVal := { re := RatVal.one, im := RatVal.zero }
def ComplexVal.two : ComplexVal := { re := RatVal.two, im := RatVal.zero }
def ComplexVal.imag : ComplexVal := { re := RatVal.zero, im := RatVal.one }
def ComplexVal.negOne : ComplexVal := { re := RatVal.negOne, im := RatVal.zero }

def RatVal.isZero (a : RatVal) : Bool := a.num = 0
def ComplexVal.hasZeroImag (a : ComplexVal) : Bool := RatVal.isZero a.im

def ComplexVal.add? (a b : ComplexVal) : Option ComplexVal := do
  let re <- RatVal.add? a.re b.re
  let im <- RatVal.add? a.im b.im
  some { re, im }

def ComplexVal.sub? (a b : ComplexVal) : Option ComplexVal := do
  let re <- RatVal.sub? a.re b.re
  let im <- RatVal.sub? a.im b.im
  some { re, im }

def ComplexVal.mul? (a b : ComplexVal) : Option ComplexVal := do
  let ac <- RatVal.mul? a.re b.re
  let bd <- RatVal.mul? a.im b.im
  let bc <- RatVal.mul? a.im b.re
  let ad <- RatVal.mul? a.re b.im
  let re <- RatVal.sub? ac bd
  let im <- RatVal.add? bc ad
  some { re, im }

def ComplexVal.divr? (a b : ComplexVal) : Option ComplexVal := do
  let c2 <- RatVal.mul? b.re b.re
  let d2 <- RatVal.mul? b.im b.im
  let denom <- RatVal.add? c2 d2
  let ac <- RatVal.mul? a.re b.re
  let bd <- RatVal.mul? a.im b.im
  let bc <- RatVal.mul? a.im b.re
  let ad <- RatVal.mul? a.re b.im
  let reNum <- RatVal.add? ac bd
  let imNum <- RatVal.sub? bc ad
  let re <- RatVal.divr? reNum denom
  let im <- RatVal.divr? imNum denom
  some { re, im }

def ComplexVal.realIntegerBin? (f : RatVal -> RatVal -> Option RatVal)
    (a b : ComplexVal) : Option ComplexVal :=
  if ComplexVal.hasZeroImag a && ComplexVal.hasZeroImag b then do
    let re <- f a.re b.re
    some { re, im := RatVal.zero }
  else none

def ComplexVal.divi? : ComplexVal -> ComplexVal -> Option ComplexVal :=
  ComplexVal.realIntegerBin? RatVal.divi?

def ComplexVal.modu? : ComplexVal -> ComplexVal -> Option ComplexVal :=
  ComplexVal.realIntegerBin? RatVal.modu?

def ComplexVal.gcd? : ComplexVal -> ComplexVal -> Option ComplexVal :=
  ComplexVal.realIntegerBin? RatVal.gcd?

def ComplexVal.realUnary? (f : RatVal -> Option RatVal) (a : ComplexVal) : Option ComplexVal :=
  if ComplexVal.hasZeroImag a then do
    let re <- f a.re
    some { re, im := RatVal.zero }
  else none

def ComplexVal.floor? : ComplexVal -> Option ComplexVal :=
  ComplexVal.realUnary? RatVal.floor?

def ComplexVal.numer? : ComplexVal -> Option ComplexVal :=
  ComplexVal.realUnary? RatVal.numer?

def ComplexVal.denom? : ComplexVal -> Option ComplexVal :=
  ComplexVal.realUnary? RatVal.denom?

def ComplexVal.realPart (a : ComplexVal) : ComplexVal := { re := a.re, im := RatVal.zero }
def ComplexVal.imagPart (a : ComplexVal) : ComplexVal := { re := a.im, im := RatVal.zero }
def ComplexVal.leq0 (a : ComplexVal) : Bool := RatVal.leq0 a.re
def ComplexVal.incr (a : ComplexVal) : ComplexVal := { a with re := RatVal.incr a.re }

def ComplexVal.returnInt? (a : ComplexVal) : Option Int :=
  if ComplexVal.hasZeroImag a && a.re.den = 1 then some a.re.num else RatVal.floorInt? a.re

/-- Source complex-valued tree. -/
inductive CTree where
  | leaf : ComplexVal -> CTree
  | node1 : ComplexVal -> CTree -> CTree
  | node2 : ComplexVal -> CTree -> CTree -> CTree
  deriving DecidableEq, Repr

def CTree.root : CTree -> ComplexVal
  | .leaf c => c
  | .node1 c _ => c
  | .node2 c _ _ => c

def CTree.replaceRoot (c : ComplexVal) : CTree -> CTree
  | .leaf _ => .leaf c
  | .node1 _ t => .node1 c t
  | .node2 _ l r => .node2 c l r

def CTree.mapRoot? (f : ComplexVal -> Option ComplexVal) (t : CTree) : Option CTree := do
  let c <- f t.root
  some (t.replaceRoot c)

def CTree.binRoot? (f : ComplexVal -> ComplexVal -> Option ComplexVal)
    (a b : CTree) : Option CTree := do
  let c <- f a.root b.root
  some (a.replaceRoot c)

def CTree.ofComplex (c : ComplexVal) : CTree := .leaf c
def CTree.zero : CTree := CTree.ofComplex ComplexVal.zero
def CTree.one : CTree := CTree.ofComplex ComplexVal.one
def CTree.two : CTree := CTree.ofComplex ComplexVal.two
def CTree.imag : CTree := CTree.ofComplex ComplexVal.imag
def CTree.negOne : CTree := CTree.ofComplex ComplexVal.negOne

def CTree.pop : CTree -> CTree
  | .leaf c => .leaf c
  | .node1 _ t => t
  | .node2 _ l _ => l

def CTree.popr : CTree -> CTree
  | .leaf c => .leaf c
  | .node1 c t => .node1 c t
  | .node2 _ _ r => r

def CTree.push (a b : CTree) : CTree := .node1 a.root b
def CTree.push2 (a b c : CTree) : CTree := .node2 a.root b c
def CTree.incr (t : CTree) : CTree := CTree.ofComplex (ComplexVal.incr t.root)
def CTree.bound? (t : CTree) : Option Int := ComplexVal.returnInt? t.root
def CTree.returnInt? (t : CTree) : Option Int := ComplexVal.returnInt? t.root

end Mettapedia.GSLT.LanguageDef.GauthierNumber
