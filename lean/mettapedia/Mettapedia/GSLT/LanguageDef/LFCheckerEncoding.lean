/-
# LF checker encoding

The parser emits boundary `String` constants.  This module interns those names
into finite `Nat` keys before checking, then runs a pure rewrite presentation for
the E2c-1 checker shape: Bad propagation, bounded normal forms, syntactic
conversion, and finite `sigT` lookup.
-/
import Mettapedia.GSLT.InternedNames
import Mettapedia.GSLT.LanguageDef.LFTyping
import Mettapedia.GSLT.LanguageDef.LFEngineParserSim

namespace Mettapedia.GSLT.LanguageDef.LFCheckerEncoding

open MeTTaIL
open Mettapedia.GSLT.LanguageDef.LFEnc

set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

/-! ## Interned LF signature names. -/

def lfNameTable : Mettapedia.GSLT.InternedNames.Table :=
  { names := ["prop", "nat", "A", "B", "z", "prf", "imp", "eqn", "rfl", "hImpAB", "hA", "mpAB"] }

def kProp : Nat := 0
def kNat : Nat := 1
def kA : Nat := 2
def kB : Nat := 3
def kZ : Nat := 4
def kPrf : Nat := 5
def kImp : Nat := 6
def kEqn : Nat := 7
def kRfl : Nat := 8
def kHImpAB : Nat := 9
def kHA : Nat := 10
def kMpAB : Nat := 11

theorem intern_prop : Mettapedia.GSLT.InternedNames.Table.intern? lfNameTable "prop" = some kProp := rfl
theorem intern_nat : Mettapedia.GSLT.InternedNames.Table.intern? lfNameTable "nat" = some kNat := rfl
theorem intern_unknown : Mettapedia.GSLT.InternedNames.Table.intern? lfNameTable "unknown" = none := rfl

def iName (k : Nat) : AST := peano k

def nProp : AST := iName kProp
def nNat : AST := iName kNat
def nA : AST := iName kA
def nB : AST := iName kB
def nZ : AST := iName kZ
def nPrf : AST := iName kPrf
def nImp : AST := iName kImp
def nEqn : AST := iName kEqn
def nRfl : AST := iName kRfl
def nHImpAB : AST := iName kHImpAB
def nHA : AST := iName kHA
def nMpAB : AST := iName kMpAB

def typeS : AST := con0 "type"
def kindS : AST := con0 "kind"

def iPropT : AST := Con nProp
def iNatT : AST := Con nNat
def iA : AST := Con nA
def iB : AST := Con nB
def iZ : AST := Con nZ
def iPrf (P : AST) : AST := App (Con nPrf) P
def iImp (P Q : AST) : AST := App (App (Con nImp) P) Q
def iEqn (x y : AST) : AST := App (App (Con nEqn) x) y
def iImpAB : AST := iImp iA iB

def checkerFuel : Nat := 32

/-! ## Boundary encoding for expected types. -/

def encName? (x : String) : Option AST :=
  (Mettapedia.GSLT.InternedNames.Table.intern? lfNameTable x).map fun k => peano k

def checkBad : AST := con0 "CheckBad"
def someT (t : AST) : AST := .sexp (.id "SomeT") [t]

def encTyCore? : LF.Term -> Option AST
  | .srt .type => some (Srt typeS)
  | .srt .kind => some (Srt kindS)
  | .var k => some (Var (peano k))
  | .con x => (encName? x).map fun k => Con k
  | .pi A B =>
      match encTyCore? A, encTyCore? B with
      | some A', some B' => some (Pi A' B')
      | _, _ => none
  | .lam A b =>
      match encTyCore? A, encTyCore? b with
      | some A', some b' => some (Lam A' b')
      | _, _ => none
  | .app f a =>
      match encTyCore? f, encTyCore? a with
      | some f', some a' => some (App f' a')
      | _, _ => none

def encTy? (t : LF.Term) : Option AST :=
  encTyCore? (LFTyping.nf LFTyping.corpusSig checkerFuel t)

def encTy (t : LF.Term) : AST :=
  match encTy? t with
  | some u => u
  | none => checkBad

theorem encTy_rflZ :
    encTy LFTyping.rflZTy = iEqn iZ iZ := rfl

theorem encTy_unknown :
    encTy (.con "unknown") = checkBad := rfl

/-! ## Checker runtime constructors. -/

def ttrue : AST := con0 "true"
def ffalse : AST := con0 "false"
def checkOk : AST := Ok (con0 "type-ok")
def checkErr (e : AST) : AST := Err e

def addN (a b : AST) : AST := .sexp (.id "addN") [a, b]
def predN (a : AST) : AST := .sexp (.id "predN") [a]
def liftT (d c t : AST) : AST := .sexp (.id "liftT") [d, c, t]
def liftVarT (d c k b : AST) : AST := .sexp (.id "liftVarT") [d, c, k, b]
def substT (j s t : AST) : AST := .sexp (.id "substT") [j, s, t]
def substVarLT (j s k b : AST) : AST := .sexp (.id "substVarLT") [j, s, k, b]
def nfT (fuel t : AST) : AST := .sexp (.id "nfT") [fuel, t]
def nfPi1 (fuel B r : AST) : AST := .sexp (.id "nfPi1") [fuel, B, r]
def nfPi2 (A r : AST) : AST := .sexp (.id "nfPi2") [A, r]
def nfLam1 (fuel b r : AST) : AST := .sexp (.id "nfLam1") [fuel, b, r]
def nfLam2 (A r : AST) : AST := .sexp (.id "nfLam2") [A, r]
def nfApp1 (fuel a r : AST) : AST := .sexp (.id "nfApp1") [fuel, a, r]
def nfApp2 (fuel f r : AST) : AST := .sexp (.id "nfApp2") [fuel, f, r]
def nfAppT (fuel f a : AST) : AST := .sexp (.id "nfAppT") [fuel, f, a]
def convT (fuel A B : AST) : AST := .sexp (.id "convT") [fuel, A, B]
def convA (fuel B r : AST) : AST := .sexp (.id "convA") [fuel, B, r]
def convB (A r : AST) : AST := .sexp (.id "convB") [A, r]
def eqT (A B : AST) : AST := .sexp (.id "eqT") [A, B]
def sigTCall (x : AST) : AST := .sexp (.id "sigT") [x]
def retT (t : AST) : AST := .sexp (.id "retT") [t]
def ctxLookupAuxT (depth ctx idx : AST) : AST := .sexp (.id "ctxLookupAuxT") [depth, ctx, idx]
def ctxLookupT (ctx idx : AST) : AST := .sexp (.id "ctxLookupT") [ctx, idx]
def inferT (fuel ctx t : AST) : AST := .sexp (.id "inferT") [fuel, ctx, t]
def inferPi1 (fuel ctx A B r : AST) : AST := .sexp (.id "inferPi1") [fuel, ctx, A, B, r]
def inferPi2 (r : AST) : AST := .sexp (.id "inferPi2") [r]
def inferLam1 (fuel ctx A body r : AST) : AST := .sexp (.id "inferLam1") [fuel, ctx, A, body, r]
def inferLam2 (A r : AST) : AST := .sexp (.id "inferLam2") [A, r]
def inferApp1 (fuel ctx a r : AST) : AST := .sexp (.id "inferApp1") [fuel, ctx, a, r]
def inferApp2 (B a b : AST) : AST := .sexp (.id "inferApp2") [B, a, b]
def checkT (fuel ctx t A : AST) : AST := .sexp (.id "checkT") [fuel, ctx, t, A]
def checkK (fuel A r : AST) : AST := .sexp (.id "checkK") [fuel, A, r]
def verdict (b : AST) : AST := .sexp (.id "verdict") [b]
def internTerm (t : AST) : AST := .sexp (.id "internTerm") [t]
def internPi1 (B r : AST) : AST := .sexp (.id "internPi1") [B, r]
def internPi2 (A r : AST) : AST := .sexp (.id "internPi2") [A, r]
def internLam1 (b r : AST) : AST := .sexp (.id "internLam1") [b, r]
def internLam2 (A r : AST) : AST := .sexp (.id "internLam2") [A, r]
def internApp1 (a r : AST) : AST := .sexp (.id "internApp1") [a, r]
def internApp2 (f r : AST) : AST := .sexp (.id "internApp2") [f, r]
def lfcheckK (A r : AST) : AST := .sexp (.id "lfcheckK") [A, r]
def lfcheckI (A r : AST) : AST := .sexp (.id "lfcheckI") [A, r]
def lfcheck (toks A : AST) : AST := .sexp (.id "lfcheck") [toks, A]

def checkerFuelA : AST := peano checkerFuel

/-! ## Pure checker rewrite rules. -/

def arithmeticRules : List RewriteDecl := [
    rw "add-z" (addN Z (pv "m")) (pv "m"),
    rw "add-s" (addN (S (pv "n")) (pv "m")) (S (addN (pv "n") (pv "m"))),
    rw "pred-z" (predN Z) Z,
    rw "pred-s" (predN (S (pv "n"))) (pv "n")
  ]

def internRules : List RewriteDecl := [
    rw "intern-var" (internTerm (Var (pv "k"))) (someT (Var (pv "k"))),
    rw "intern-srt-type" (internTerm (Srt typeS)) (someT (Srt typeS)),
    rw "intern-srt-kind" (internTerm (Srt kindS)) (someT (Srt kindS)),
    rw "intern-srt-bad" (internTerm (Srt (pv "s"))) checkBad,
    rw "intern-con-prop" (internTerm (Con (con0 "prop"))) (someT iPropT),
    rw "intern-con-nat" (internTerm (Con (con0 "nat"))) (someT iNatT),
    rw "intern-con-A" (internTerm (Con (con0 "A"))) (someT iA),
    rw "intern-con-B" (internTerm (Con (con0 "B"))) (someT iB),
    rw "intern-con-z" (internTerm (Con (con0 "z"))) (someT iZ),
    rw "intern-con-prf" (internTerm (Con (con0 "prf"))) (someT (Con nPrf)),
    rw "intern-con-imp" (internTerm (Con (con0 "imp"))) (someT (Con nImp)),
    rw "intern-con-eqn" (internTerm (Con (con0 "eqn"))) (someT (Con nEqn)),
    rw "intern-con-rfl" (internTerm (Con (con0 "rfl"))) (someT (Con nRfl)),
    rw "intern-con-hImpAB" (internTerm (Con (con0 "hImpAB"))) (someT (Con nHImpAB)),
    rw "intern-con-hA" (internTerm (Con (con0 "hA"))) (someT (Con nHA)),
    rw "intern-con-mpAB" (internTerm (Con (con0 "mpAB"))) (someT (Con nMpAB)),
    rw "intern-con-bad" (internTerm (Con (pv "x"))) checkBad,
    rw "intern-pi" (internTerm (Pi (pv "A") (pv "B"))) (internPi1 (pv "B") (internTerm (pv "A"))),
    rw "intern-pi1-ok" (internPi1 (pv "B") (someT (pv "A"))) (internPi2 (pv "A") (internTerm (pv "B"))),
    rw "intern-pi1-bad" (internPi1 (pv "B") checkBad) checkBad,
    rw "intern-pi2-ok" (internPi2 (pv "A") (someT (pv "B"))) (someT (Pi (pv "A") (pv "B"))),
    rw "intern-pi2-bad" (internPi2 (pv "A") checkBad) checkBad,
    rw "intern-lam" (internTerm (Lam (pv "A") (pv "b"))) (internLam1 (pv "b") (internTerm (pv "A"))),
    rw "intern-lam1-ok" (internLam1 (pv "b") (someT (pv "A"))) (internLam2 (pv "A") (internTerm (pv "b"))),
    rw "intern-lam1-bad" (internLam1 (pv "b") checkBad) checkBad,
    rw "intern-lam2-ok" (internLam2 (pv "A") (someT (pv "b"))) (someT (Lam (pv "A") (pv "b"))),
    rw "intern-lam2-bad" (internLam2 (pv "A") checkBad) checkBad,
    rw "intern-app" (internTerm (App (pv "f") (pv "a"))) (internApp1 (pv "a") (internTerm (pv "f"))),
    rw "intern-app1-ok" (internApp1 (pv "a") (someT (pv "f"))) (internApp2 (pv "f") (internTerm (pv "a"))),
    rw "intern-app1-bad" (internApp1 (pv "a") checkBad) checkBad,
    rw "intern-app2-ok" (internApp2 (pv "f") (someT (pv "a"))) (someT (App (pv "f") (pv "a"))),
    rw "intern-app2-bad" (internApp2 (pv "f") checkBad) checkBad
  ]

def sigRules : List RewriteDecl := [
    rw "sig-prop" (sigTCall nProp) (someT (Srt typeS)),
    rw "sig-nat" (sigTCall nNat) (someT (Srt typeS)),
    rw "sig-A" (sigTCall nA) (someT iPropT),
    rw "sig-B" (sigTCall nB) (someT iPropT),
    rw "sig-z" (sigTCall nZ) (someT iNatT),
    rw "sig-prf" (sigTCall nPrf) (someT (Pi iPropT (Srt typeS))),
    rw "sig-imp" (sigTCall nImp) (someT (Pi iPropT (Pi iPropT iPropT))),
    rw "sig-eqn" (sigTCall nEqn) (someT (Pi iNatT (Pi iNatT (Srt typeS)))),
    rw "sig-rfl" (sigTCall nRfl) (someT (Pi iNatT (iEqn (Var Z) (Var Z)))),
    rw "sig-hImpAB" (sigTCall nHImpAB) (someT (iPrf iImpAB)),
    rw "sig-hA" (sigTCall nHA) (someT (iPrf iA)),
    rw "sig-mpAB" (sigTCall nMpAB) (someT (Pi (iPrf iImpAB) (Pi (iPrf iA) (iPrf iB)))),
    rw "sig-bad" (sigTCall (pv "x")) checkBad
  ]

def termOpsRules : List RewriteDecl := [
    -- lift
    rw "lift-var" (liftT (pv "d") (pv "c") (Var (pv "k")))
      (liftVarT (pv "d") (pv "c") (pv "k") (ltT (pv "k") (pv "c"))),
    rw "lift-var-lt" (liftVarT (pv "d") (pv "c") (pv "k") (con0 "tt")) (Var (pv "k")),
    rw "lift-var-ge" (liftVarT (pv "d") (pv "c") (pv "k") (con0 "ff")) (Var (addN (pv "k") (pv "d"))),
    rw "lift-srt" (liftT (pv "d") (pv "c") (Srt (pv "s"))) (Srt (pv "s")),
    rw "lift-con" (liftT (pv "d") (pv "c") (Con (pv "x"))) (Con (pv "x")),
    rw "lift-pi" (liftT (pv "d") (pv "c") (Pi (pv "A") (pv "B")))
      (Pi (liftT (pv "d") (pv "c") (pv "A")) (liftT (pv "d") (S (pv "c")) (pv "B"))),
    rw "lift-lam" (liftT (pv "d") (pv "c") (Lam (pv "A") (pv "b")))
      (Lam (liftT (pv "d") (pv "c") (pv "A")) (liftT (pv "d") (S (pv "c")) (pv "b"))),
    rw "lift-app" (liftT (pv "d") (pv "c") (App (pv "f") (pv "a")))
      (App (liftT (pv "d") (pv "c") (pv "f")) (liftT (pv "d") (pv "c") (pv "a"))),
    -- substitution
    rw "subst-var-hit" (substT (pv "j") (pv "s") (Var (pv "j"))) (pv "s"),
    rw "subst-var-miss" (substT (pv "j") (pv "s") (Var (pv "k")))
      (substVarLT (pv "j") (pv "s") (pv "k") (ltT (pv "j") (pv "k"))),
    rw "subst-var-lt" (substVarLT (pv "j") (pv "s") (pv "k") (con0 "tt")) (Var (predN (pv "k"))),
    rw "subst-var-ge" (substVarLT (pv "j") (pv "s") (pv "k") (con0 "ff")) (Var (pv "k")),
    rw "subst-srt" (substT (pv "j") (pv "s") (Srt (pv "u"))) (Srt (pv "u")),
    rw "subst-con" (substT (pv "j") (pv "s") (Con (pv "x"))) (Con (pv "x")),
    rw "subst-pi" (substT (pv "j") (pv "s") (Pi (pv "A") (pv "B")))
      (Pi (substT (pv "j") (pv "s") (pv "A"))
        (substT (S (pv "j")) (liftT (S Z) Z (pv "s")) (pv "B"))),
    rw "subst-lam" (substT (pv "j") (pv "s") (Lam (pv "A") (pv "b")))
      (Lam (substT (pv "j") (pv "s") (pv "A"))
        (substT (S (pv "j")) (liftT (S Z) Z (pv "s")) (pv "b"))),
    rw "subst-app" (substT (pv "j") (pv "s") (App (pv "f") (pv "a")))
      (App (substT (pv "j") (pv "s") (pv "f")) (substT (pv "j") (pv "s") (pv "a")))
  ]

def nfRules : List RewriteDecl := [
    rw "nf-z" (nfT Z (pv "t")) (someT (pv "t")),
    rw "nf-srt" (nfT (S (pv "f")) (Srt (pv "s"))) (someT (Srt (pv "s"))),
    rw "nf-var" (nfT (S (pv "f")) (Var (pv "k"))) (someT (Var (pv "k"))),
    rw "nf-con" (nfT (S (pv "f")) (Con (pv "x"))) (someT (Con (pv "x"))),
    rw "nf-pi" (nfT (S (pv "f")) (Pi (pv "A") (pv "B"))) (nfPi1 (pv "f") (pv "B") (nfT (pv "f") (pv "A"))),
    rw "nf-pi1" (nfPi1 (pv "f") (pv "B") (someT (pv "A"))) (nfPi2 (pv "A") (nfT (pv "f") (pv "B"))),
    rw "nf-pi2" (nfPi2 (pv "A") (someT (pv "B"))) (someT (Pi (pv "A") (pv "B"))),
    rw "nf-lam" (nfT (S (pv "f")) (Lam (pv "A") (pv "b"))) (nfLam1 (pv "f") (pv "b") (nfT (pv "f") (pv "A"))),
    rw "nf-lam1" (nfLam1 (pv "f") (pv "b") (someT (pv "A"))) (nfLam2 (pv "A") (nfT (pv "f") (pv "b"))),
    rw "nf-lam2" (nfLam2 (pv "A") (someT (pv "b"))) (someT (Lam (pv "A") (pv "b"))),
    rw "nf-app" (nfT (S (pv "f")) (App (pv "g") (pv "a"))) (nfApp1 (pv "f") (pv "a") (nfT (pv "f") (pv "g"))),
    rw "nf-app1" (nfApp1 (pv "f") (pv "a") (someT (pv "g"))) (nfApp2 (pv "f") (pv "g") (nfT (pv "f") (pv "a"))),
    rw "nf-app2" (nfApp2 (pv "f") (pv "g") (someT (pv "a"))) (nfAppT (pv "f") (pv "g") (pv "a")),
    rw "nfapp-z" (nfAppT Z (pv "g") (pv "a")) (someT (App (pv "g") (pv "a"))),
    rw "nfapp-beta" (nfAppT (S (pv "f")) (Lam (pv "A") (pv "body")) (pv "a"))
      (nfT (pv "f") (substT Z (pv "a") (pv "body"))),
    rw "nfapp-fall" (nfAppT (S (pv "f")) (pv "g") (pv "a")) (someT (App (pv "g") (pv "a")))
  ]

def checkerRulesCore : List RewriteDecl := [
    rw "ret-srt" (retT (Srt (pv "s"))) (someT (Srt (pv "s"))),
    rw "ret-con" (retT (Con (pv "x"))) (someT (Con (pv "x"))),
    rw "ret-var" (retT (Var (pv "k"))) (someT (Var (pv "k"))),
    rw "ret-pi" (retT (Pi (pv "A") (pv "B"))) (someT (Pi (pv "A") (pv "B"))),
    rw "ret-lam" (retT (Lam (pv "A") (pv "b"))) (someT (Lam (pv "A") (pv "b"))),
    rw "ret-app" (retT (App (pv "f") (pv "a"))) (someT (App (pv "f") (pv "a"))),
    rw "eqT-hit" (eqT (pv "A") (pv "A")) ttrue,
    rw "eqT-miss" (eqT (pv "A") (pv "B")) ffalse,
    rw "conv" (convT (pv "f") (pv "A") (pv "B")) (convA (pv "f") (pv "B") (nfT (pv "f") (pv "A"))),
    rw "convA" (convA (pv "f") (pv "B") (someT (pv "A"))) (convB (pv "A") (nfT (pv "f") (pv "B"))),
    rw "convB" (convB (pv "A") (someT (pv "B"))) (eqT (pv "A") (pv "B")),
    rw "ctx-lookup" (ctxLookupT (pv "ctx") (pv "i")) (ctxLookupAuxT Z (pv "ctx") (pv "i")),
    rw "ctx-nil" (ctxLookupAuxT (pv "d") Nil (pv "i")) checkBad,
    rw "ctx-zero" (ctxLookupAuxT (pv "d") (Cons (pv "A") (pv "rest")) Z)
      (retT (liftT (S (pv "d")) Z (pv "A"))),
    rw "ctx-succ" (ctxLookupAuxT (pv "d") (Cons (pv "A") (pv "rest")) (S (pv "i")))
      (ctxLookupAuxT (S (pv "d")) (pv "rest") (pv "i")),
    rw "infer-z" (inferT Z (pv "ctx") (pv "t")) checkBad,
    rw "infer-type" (inferT (S (pv "f")) (pv "ctx") (Srt typeS)) (someT (Srt kindS)),
    rw "infer-kind" (inferT (S (pv "f")) (pv "ctx") (Srt kindS)) checkBad,
    rw "infer-con" (inferT (S (pv "f")) (pv "ctx") (Con (pv "x"))) (sigTCall (pv "x")),
    rw "infer-var" (inferT (S (pv "f")) (pv "ctx") (Var (pv "i"))) (ctxLookupT (pv "ctx") (pv "i")),
    rw "infer-pi" (inferT (S (pv "f")) (pv "ctx") (Pi (pv "A") (pv "B")))
      (inferPi1 (pv "f") (pv "ctx") (pv "A") (pv "B") (inferT (pv "f") (pv "ctx") (pv "A"))),
    rw "infer-pi1-type" (inferPi1 (pv "f") (pv "ctx") (pv "A") (pv "B") (someT (Srt typeS)))
      (inferPi2 (inferT (pv "f") (Cons (pv "A") (pv "ctx")) (pv "B"))),
    rw "infer-pi1-bad" (inferPi1 (pv "f") (pv "ctx") (pv "A") (pv "B") checkBad) checkBad,
    rw "infer-pi1-other" (inferPi1 (pv "f") (pv "ctx") (pv "A") (pv "B") (someT (pv "T"))) checkBad,
    rw "infer-pi2-sort" (inferPi2 (someT (Srt (pv "s")))) (someT (Srt (pv "s"))),
    rw "infer-pi2-bad" (inferPi2 checkBad) checkBad,
    rw "infer-pi2-other" (inferPi2 (someT (pv "T"))) checkBad,
    rw "infer-lam" (inferT (S (pv "f")) (pv "ctx") (Lam (pv "A") (pv "body")))
      (inferLam1 (pv "f") (pv "ctx") (pv "A") (pv "body") (inferT (pv "f") (pv "ctx") (pv "A"))),
    rw "infer-lam1-type" (inferLam1 (pv "f") (pv "ctx") (pv "A") (pv "body") (someT (Srt typeS)))
      (inferLam2 (pv "A") (inferT (pv "f") (Cons (pv "A") (pv "ctx")) (pv "body"))),
    rw "infer-lam1-bad" (inferLam1 (pv "f") (pv "ctx") (pv "A") (pv "body") checkBad) checkBad,
    rw "infer-lam1-other" (inferLam1 (pv "f") (pv "ctx") (pv "A") (pv "body") (someT (pv "T"))) checkBad,
    rw "infer-lam2-ok" (inferLam2 (pv "A") (someT (pv "B"))) (someT (Pi (pv "A") (pv "B"))),
    rw "infer-lam2-bad" (inferLam2 (pv "A") checkBad) checkBad,
    rw "infer-app" (inferT (S (pv "f")) (pv "ctx") (App (pv "g") (pv "a")))
      (inferApp1 (pv "f") (pv "ctx") (pv "a") (inferT (pv "f") (pv "ctx") (pv "g"))),
    rw "infer-app1-pi" (inferApp1 (pv "f") (pv "ctx") (pv "a") (someT (Pi (pv "A") (pv "B"))))
      (inferApp2 (pv "B") (pv "a") (checkT (pv "f") (pv "ctx") (pv "a") (pv "A"))),
    rw "infer-app1-bad" (inferApp1 (pv "f") (pv "ctx") (pv "a") checkBad) checkBad,
    rw "infer-app1-other" (inferApp1 (pv "f") (pv "ctx") (pv "a") (someT (pv "T"))) checkBad,
    rw "infer-app2-true" (inferApp2 (pv "B") (pv "a") ttrue) (retT (substT Z (pv "a") (pv "B"))),
    rw "infer-app2-false" (inferApp2 (pv "B") (pv "a") ffalse) checkBad,
    rw "check-z" (checkT Z (pv "ctx") (pv "t") (pv "A")) ffalse,
    rw "check-s" (checkT (S (pv "f")) (pv "ctx") (pv "t") (pv "A"))
      (checkK (pv "f") (pv "A") (inferT (pv "f") (pv "ctx") (pv "t"))),
    rw "checkK-ok" (checkK (pv "f") (pv "A") (someT (pv "B"))) (convT (pv "f") (pv "B") (pv "A")),
    rw "checkK-bad" (checkK (pv "f") (pv "A") checkBad) ffalse,
    rw "verdict-true" (verdict ttrue) checkOk,
    rw "verdict-false" (verdict ffalse) (checkErr (con0 "type-reject")),
    rw "lfcheck" (lfcheck (pv "toks") (pv "A")) (lfcheckK (pv "A") (lfrec (pv "toks"))),
    rw "lfcheckK-err" (lfcheckK (pv "A") (Err (pv "e"))) (checkErr (pv "e")),
    rw "lfcheckK-ok" (lfcheckK (pv "A") (Ok (pv "raw"))) (lfcheckI (pv "A") (internTerm (pv "raw"))),
    rw "lfcheckI-bad-type" (lfcheckI checkBad (someT (pv "t"))) (checkErr (con0 "unknown-type-name")),
    rw "lfcheckI-bad-term" (lfcheckI (pv "A") checkBad) (checkErr (con0 "unknown-term-name")),
    rw "lfcheckI-ok" (lfcheckI (pv "A") (someT (pv "t"))) (verdict (checkT checkerFuelA Nil (pv "t") (pv "A")))
  ]

def checkerRules : List RewriteDecl :=
  arithmeticRules ++ internRules ++ sigRules ++ termOpsRules ++ nfRules ++ checkerRulesCore

/-- The full parser-plus-typechecker presentation. Parser rules stay first, so parser dispatch is
unchanged until the `lfcheck` continuation receives `Ok` or `Err`. -/
def pTC : Presentation :=
  .mk [] [] [] (Presentation.rewrites pLF ++ checkerRules) []

/-! ## Corpus gates through the certified normalizer. -/

theorem intern_rflZ_engine :
    eval pTC 80 (internTerm (App (Con (con0 "rfl")) (Con (con0 "z"))))
      = someT (App (Con nRfl) (Con nZ)) := by rfl

theorem sig_rfl_engine :
    eval pTC 80 (sigTCall nRfl) = someT (Pi iNatT (iEqn (Var Z) (Var Z))) := by rfl

theorem check_rflZ_direct_engine :
    eval pTC 500 (verdict (checkT checkerFuelA Nil (App (Con nRfl) (Con nZ)) (iEqn iZ iZ)))
      = checkOk := by rfl

theorem lfcheck_rflZ_engine :
    eval pTC 1000
      (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks LF.cToks1)
        (encTy LFTyping.rflZTy)) = checkOk := by
  rfl

def idProofToks : AST :=
  Cons tLAM (Cons (tId (con0 "h")) (Cons tCOLON
    (Cons (tId (con0 "prf")) (Cons (tId (con0 "A"))
      (Cons tDOT (Cons (tId (con0 "h")) Nil))))))

theorem lfcheck_id_engine :
    eval pTC 2500 (lfcheck idProofToks (encTy LFTyping.idProofTy)) = checkOk := by
  rfl

def mpProofToks : AST :=
  Cons (tId (con0 "mpAB")) (Cons (tId (con0 "hImpAB")) (Cons (tId (con0 "hA")) Nil))

theorem lfcheck_mp_engine :
    eval pTC 2500 (lfcheck mpProofToks (encTy LFTyping.mpProofTy)) = checkOk := by
  rfl

theorem lfcheck_bad_rfl_engine :
    eval pTC 1000
      (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks LF.cToks1)
        (encTy LFTyping.badRflTy)) = checkErr (con0 "type-reject") := by
  rfl

theorem lfcheck_bad_parse_engine :
    eval pTC 1000
      (lfcheck (Mettapedia.GSLT.LanguageDef.LFEngineCorr.encToks LF.cToks8)
        (encTy LFTyping.rflZTy)) = checkErr (con0 "paren-malformed") := by
  rfl

theorem lfcheckK_error_engine (A e : AST) :
    eval pTC 1 (lfcheckK A (Err e)) = checkErr e := by
  rfl

end Mettapedia.GSLT.LanguageDef.LFCheckerEncoding
