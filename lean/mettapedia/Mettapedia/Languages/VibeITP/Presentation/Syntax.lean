import Mettapedia.Languages.VibeITP.Spec.Derivation
import Mettapedia.GSLT.LanguageDef.FirstOrderRules

/-!
# Vibe-ITP presentation: data constructors, judgments, and encodings

The hosted kernel works on first-order data.  Numbers are binary numerals with
a unique representation (`VN0`, or `VNPos` of a positive numeral built from
`VP1`, `VPO`, `VPI`).  A Vibe term keeps the kernel's own de Bruijn discipline:
a bound variable carries its index, a literal carries its bytes, and an
application carries its head symbol, its arguments, and the two annotations the
kernel maintains for every term (the number of enclosing binders needed to
close it and whether it applies a free variable).  A head symbol carries its
allocation identity, its kind, and the binder count of each argument, so the
binding structure of a term is readable from the term itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.VibeITP.Spec

/-! ## Data constructors -/

def cP1 : Pattern := .apply "VP1" []
def cPO (p : Pattern) : Pattern := .apply "VPO" [p]
def cPI (p : Pattern) : Pattern := .apply "VPI" [p]
def cN0 : Pattern := .apply "VN0" []
def cNPos (p : Pattern) : Pattern := .apply "VNPos" [p]
def cU0 : Pattern := .apply "VU0" []
def cUS (u : Pattern) : Pattern := .apply "VUS" [u]
def cFalse : Pattern := .apply "VFalse" []
def cTrue : Pattern := .apply "VTrue" []
def cNil : Pattern := .apply "VNil" []
def cCons (x xs : Pattern) : Pattern := .apply "VCons" [x, xs]
def cKConst : Pattern := .apply "VKConst" []
def cKFvar : Pattern := .apply "VKFvar" []
def cSym (id kind binders : Pattern) : Pattern := .apply "VSym" [id, kind, binders]
def cAnn (depth fv : Pattern) : Pattern := .apply "VAnn" [depth, fv]
def cBVar (index : Pattern) : Pattern := .apply "VBVar" [index]
def cLit (bytes : Pattern) : Pattern := .apply "VLit" [bytes]
def cApp (sym args ann : Pattern) : Pattern := .apply "VApp" [sym, args, ann]

/-- Data constructors with their arities. -/
def constructorArities : List (String × Nat) :=
  [("VP1", 0), ("VPO", 1), ("VPI", 1), ("VN0", 0), ("VNPos", 1),
   ("VU0", 0), ("VUS", 1), ("VFalse", 0), ("VTrue", 0), ("VNil", 0),
   ("VCons", 2), ("VKConst", 0), ("VKFvar", 0), ("VSym", 3), ("VAnn", 2),
   ("VBVar", 1), ("VLit", 1), ("VApp", 3)]

/-! ## Judgments -/

def jPSucc (p q : Pattern) : Pattern := .apply "VPSucc" [p, q]
def jPAdd (p q r : Pattern) : Pattern := .apply "VPAdd" [p, q, r]
def jPAddC (p q r : Pattern) : Pattern := .apply "VPAddC" [p, q, r]
def jNAdd (a b c : Pattern) : Pattern := .apply "VNAdd" [a, b, c]
def jNLt (a b : Pattern) : Pattern := .apply "VNLt" [a, b]
def jNLe (a b : Pattern) : Pattern := .apply "VNLe" [a, b]
def jPMul (p q r : Pattern) : Pattern := .apply "VPMul" [p, q, r]
def jNMul (a b c : Pattern) : Pattern := .apply "VNMul" [a, b, c]
def jNDivMod (a b q r : Pattern) : Pattern := .apply "VNDivMod" [a, b, q, r]
def jNMod64 (a c : Pattern) : Pattern := .apply "VNMod64" [a, c]
def jPBits (p u : Pattern) : Pattern := .apply "VPBits" [p, u]
def jNWord (a : Pattern) : Pattern := .apply "VNWord" [a]
def jNMonus (a b c : Pattern) : Pattern := .apply "VNMonus" [a, b, c]
def jNMax (a b c : Pattern) : Pattern := .apply "VNMax" [a, b, c]
def jBOr (x y z : Pattern) : Pattern := .apply "VBOr" [x, y, z]
def jLen (xs n : Pattern) : Pattern := .apply "VLen" [xs, n]
def jNth (xs i x : Pattern) : Pattern := .apply "VNth" [xs, i, x]
def jBytes (xs : Pattern) : Pattern := .apply "VBytes" [xs]
def jSymDecl (s : Pattern) : Pattern := .apply "VSymDecl" [s]
def jWf (t : Pattern) : Pattern := .apply "VWf" [t]
def jWfArgs (bs ts d fv : Pattern) : Pattern := .apply "VWfArgs" [bs, ts, d, fv]
def jKindFv (kind fv fv' : Pattern) : Pattern := .apply "VKindFv" [kind, fv, fv']
def jDepth (t d : Pattern) : Pattern := .apply "VDepth" [t, d]
def jHasFv (t f : Pattern) : Pattern := .apply "VHasFv" [t, f]
def jAnnArgs (bs ts d fv : Pattern) : Pattern := .apply "VAnnArgs" [bs, ts, d, fv]
def jShift (a c t t' : Pattern) : Pattern := .apply "VShift" [a, c, t, t']
def jShiftArgs (a c bs ts ts' : Pattern) : Pattern := .apply "VShiftArgs" [a, c, bs, ts, ts']
def jSubst (n args off t t' : Pattern) : Pattern := .apply "VSubst" [n, args, off, t, t']
def jSubstArgs (n args off bs ts ts' : Pattern) : Pattern :=
  .apply "VSubstArgs" [n, args, off, bs, ts, ts']
def jSubstTop (n args t t' : Pattern) : Pattern := .apply "VSubstTop" [n, args, t, t']
def jInst (f v n off t t' : Pattern) : Pattern := .apply "VInst" [f, v, n, off, t, t']
def jInstArgs (f v n off bs ts ts' : Pattern) : Pattern :=
  .apply "VInstArgs" [f, v, n, off, bs, ts, ts']
def jNatLit (n bytes : Pattern) : Pattern := .apply "VNatLit" [n, bytes]
def jArities (fvars bs : Pattern) : Pattern := .apply "VArities" [fvars, bs]
def jAllFvar (fvars : Pattern) : Pattern := .apply "VAllFvar" [fvars]
def jHintsIn (hints n : Pattern) : Pattern := .apply "VHintsIn" [hints, n]
def jOcc (fvars t hints rest : Pattern) : Pattern := .apply "VOcc" [fvars, t, hints, rest]
def jOccArgs (fvars ts hints rest : Pattern) : Pattern :=
  .apply "VOccArgs" [fvars, ts, hints, rest]
def jEtas (fvars etas : Pattern) : Pattern := .apply "VEtas" [fvars, etas]
def jDescBVars (n vars : Pattern) : Pattern := .apply "VDescBVars" [n, vars]
def jDefStmt (c fvars hints value stmt : Pattern) : Pattern :=
  .apply "VDefStmt" [c, fvars, hints, value, stmt]
def jThm (φ : Pattern) : Pattern := .apply "VThm" [φ]

/-- Judgment heads with their arities. -/
def judgmentArities : List (String × Nat) :=
  [("VPSucc", 2), ("VPAdd", 3), ("VPAddC", 3), ("VNAdd", 3), ("VNLt", 2),
   ("VNLe", 2), ("VPMul", 3), ("VNMul", 3), ("VNDivMod", 4), ("VNMod64", 2),
   ("VPBits", 2), ("VNWord", 1), ("VNMonus", 3), ("VNMax", 3), ("VBOr", 3),
   ("VLen", 2), ("VNth", 3), ("VBytes", 1), ("VSymDecl", 1), ("VWf", 1),
   ("VWfArgs", 4), ("VKindFv", 3), ("VDepth", 2), ("VHasFv", 2), ("VAnnArgs", 4),
   ("VShift", 4), ("VShiftArgs", 5), ("VSubst", 5), ("VSubstArgs", 6),
   ("VSubstTop", 4), ("VInst", 6), ("VInstArgs", 7), ("VNatLit", 2),
   ("VArities", 2), ("VAllFvar", 1), ("VHintsIn", 2), ("VOcc", 4), ("VOccArgs", 4),
   ("VEtas", 2), ("VDescBVars", 2), ("VDefStmt", 5), ("VThm", 1)]

/-! ## Encodings -/

/-- Positive binary numeral of `n ≥ 1`; `fuel` bounds the number of halvings. -/
def encPosFuel : Nat → Nat → Pattern
  | 0, _ => cP1
  | fuel + 1, n =>
      if n ≤ 1 then cP1
      else if n % 2 = 0 then cPO (encPosFuel fuel (n / 2))
      else cPI (encPosFuel fuel (n / 2))

def encPos (n : Nat) : Pattern := encPosFuel n n

def encNat (n : Nat) : Pattern := if n = 0 then cN0 else cNPos (encPos n)

def encUnary : Nat → Pattern
  | 0 => cU0
  | n + 1 => cUS (encUnary n)

def encBool (b : Bool) : Pattern := if b then cTrue else cFalse

def encList : List Pattern → Pattern
  | [] => cNil
  | x :: xs => cCons x (encList xs)

def encNatList (ns : List Nat) : Pattern := encList (ns.map encNat)

def encBytes (bytes : List UInt8) : Pattern := encList (bytes.map fun b => encNat b.toNat)

def encKind : SymKind → Pattern
  | .constant => cKConst
  | .fvar => cKFvar

/-- Numeric identity of a symbol: its protected slot for built-ins, and
`13 + n` for the `n`-th allocated symbol. -/
def symNumber : SymId → Nat
  | .builtin b => b.slot
  | .fresh n => protectedSymbolSlots + n

def encSym (sig : Sig) (s : SymId) : Pattern :=
  match sig s with
  | some info => cSym (encNat (symNumber s)) (encKind info.kind) (encNatList info.binders)
  | none => cSym (encNat (symNumber s)) cKConst cNil

mutual
def encTerm (sig : Sig) : Term → Pattern
  | .bvar i => cBVar (encNat i)
  | .lit bytes => cLit (encBytes bytes)
  | .app s args =>
      cApp (encSym sig s) (encTermList sig args)
        (cAnn (encNat (depthArgs sig s 0 args))
          (encBool (isFvarSym sig s || hasFvarList sig args)))

def encTermList (sig : Sig) : List Term → Pattern
  | [] => cNil
  | a :: as => cCons (encTerm sig a) (encTermList sig as)
end

/-! ## Constants used by the rules -/

def patTwo64 : Pattern := encNat wordBound
def patMaxWord : Pattern := encNat (wordBound - 1)
def patByteBound : Pattern := encNat 256
def patWordBits : Pattern := encUnary 64
def patOne : Pattern := encNat 1
def patEight : Pattern := encNat 8

/-- Closed annotation of an application all of whose arguments are closed
and free of free-variable applications. -/
def patAnnClosed : Pattern := cAnn cN0 cFalse

def patBuiltinSym (b : Builtin) : Pattern := encSym (sigOf fun _ => none) (.builtin b)

end Mettapedia.Languages.VibeITP.Presentation
