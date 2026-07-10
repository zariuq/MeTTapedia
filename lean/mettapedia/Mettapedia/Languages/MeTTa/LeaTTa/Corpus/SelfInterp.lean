import MeTTaIL.Semantics.Eval

/-!
# Verified MeTTa, entry 05 -- self-interpreter finite corpus checks

This module encodes the Stage-1 `mi-eval` interpreter as a pure
`MeTTaIL.Presentation` and checks finite corpus examples through the certified
fuel-bounded normalizer.

Fragment v1: the deterministic MOPS core needed by the equality-rule corpus
entries -- `(= lhs rhs)` equalities, immutable encoded facts for the entry-04
one-fact query, first-order `$`-variable matching, leftmost reduction,
fuel-bounded normalization.

Excluded here: `superpose`/`collapse` nondeterminism, grounded guest
operations, mutable spaces/state.  The entry-04 `match &self` case below is the
finite immutable fact-table query only; it is not general spaces/state.

Integrity: finite checks below are by kernel reduction (`rfl`) over
`MeTTaIL.eval`; no placeholder proof commands are used.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp

open MeTTaIL

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

def con0 (s : String) : AST := .sexp (.id s) []
def app (s : String) (args : List AST) : AST := .sexp (.id s) args
def pv (v : String) : AST := .var (.base v)
def rw (name : String) (lhs rhs : AST) : RewriteDecl := { name := name, rw := .base lhs rhs }

def FZ : AST := con0 "FZ"
def FS (n : AST) : AST := app "FS" [n]

def Z : AST := con0 "Z"
def S (n : AST) : AST := app "S" [n]
def Nil : AST := con0 "Nil"
def Cons (x xs : AST) : AST := app "Cons" [x, xs]
def N (x : AST) : AST := app "N" [x]

def MINil : AST := con0 "MINil"
def MICons (x xs : AST) : AST := app "MICons" [x, xs]
def MISym (s : String) : AST := app "MISym" [con0 s]
def MIVar (v : String) : AST := app "MIVar" [con0 v]
def MIApp (h : String) (args : AST) : AST := app "MIApp" [con0 h, args]

def MIRNil : AST := con0 "MIRNil"
def MIRule (lhs rhs : AST) : AST := app "MIRule" [lhs, rhs]
def MIFact (fact : AST) : AST := app "MIFact" [fact]
def MIRCons (r rs : AST) : AST := app "MIRCons" [r, rs]

def MIBNil : AST := con0 "MIBNil"
def MIBCons (v t rest : AST) : AST := app "MIBCons" [v, t, rest]
def MINone : AST := con0 "MINone"
def MISome (t : AST) : AST := app "MISome" [t]

def MIMatchOk (bs : AST) : AST := app "MIMatchOk" [bs]
def MIMatchFail : AST := con0 "MIMatchFail"
def MIRootStep (t : AST) : AST := app "MIRootStep" [t]
def MINoRoot : AST := con0 "MINoRoot"
def MIStep (t : AST) : AST := app "MIStep" [t]
def MINoStep : AST := con0 "MINoStep"
def MIArgsStep (args : AST) : AST := app "MIArgsStep" [args]
def MINoArgsStep : AST := con0 "MINoArgsStep"
def MIDone (t : AST) : AST := app "MIDone" [t]
def MIExhausted (t : AST) : AST := app "MIExhausted" [t]

def miLookup (v bs : AST) : AST := app "mi-lookup" [v, bs]
def miMatchVar (v term bs : AST) : AST := app "mi-match-var" [v, term, bs]
def miMatchVarK (v term bs r : AST) : AST := app "mi-match-varK" [v, term, bs, r]
def miMatchList (ps ts bs : AST) : AST := app "mi-match-list" [ps, ts, bs]
def miMatchListK (ps ts r : AST) : AST := app "mi-match-listK" [ps, ts, r]
def miMatch (pat term bs : AST) : AST := app "mi-match" [pat, term, bs]
def miSubst (bs term : AST) : AST := app "mi-subst" [bs, term]
def miSubstVarK (orig r : AST) : AST := app "mi-subst-varK" [orig, r]
def miSubstList (bs args : AST) : AST := app "mi-subst-list" [bs, args]
def miQueryRoot (rules pat template : AST) : AST := app "mi-query-root" [rules, pat, template]
def miQueryRootK (rest pat template r : AST) : AST := app "mi-query-rootK" [rest, pat, template, r]
def miRoot (rules term : AST) : AST := app "mi-root" [rules, term]
def miRootTable (rules term : AST) : AST := app "mi-root-table" [rules, term]
def miRootK (rest term rhs r : AST) : AST := app "mi-rootK" [rest, term, rhs, r]
def miStepArgs (rules args : AST) : AST := app "mi-step-args" [rules, args]
def miStepArgsK (rules x xs r : AST) : AST := app "mi-step-argsK" [rules, x, xs, r]
def miStepArgsRestK (x r : AST) : AST := app "mi-step-args-restK" [x, r]
def miStep (rules term : AST) : AST := app "mi-step" [rules, term]
def miStepRootK (rules term r : AST) : AST := app "mi-step-rootK" [rules, term, r]
def miStepAppK (h r : AST) : AST := app "mi-step-appK" [h, r]
def miEval (rules term fuel : AST) : AST := app "mi-eval" [rules, term, fuel]
def miEvalK (rules term fuel r : AST) : AST := app "mi-evalK" [rules, term, fuel, r]
def miRun (rules term fuel : AST) : AST := app "mi-run" [rules, term, fuel]
def miDecodeVerdict (v : AST) : AST := app "mi-decode-verdict" [v]
def miDecode (t : AST) : AST := app "mi-decode" [t]

def vV : AST := pv "v"
def vW : AST := pv "w"
def vT : AST := pv "t"
def vOld : AST := pv "old"
def vRest : AST := pv "rest"
def vTerm : AST := pv "term"
def vBs : AST := pv "bs"
def vBs2 : AST := pv "bs2"
def vP : AST := pv "p"
def vPs : AST := pv "ps"
def vTs : AST := pv "ts"
def vX : AST := pv "x"
def vXs : AST := pv "xs"
def vRules : AST := pv "rules"
def vFuel : AST := pv "fuel"
def vNext : AST := pv "next"
def vH : AST := pv "h"
def vArgs : AST := pv "args"
def vArgs2 : AST := pv "args2"
def vLhs : AST := pv "lhs"
def vRhs : AST := pv "rhs"
def vR : AST := pv "r"
def vFact : AST := pv "fact"

def miRules : List RewriteDecl := [
  rw "lookup-nil" (miLookup vV MIBNil) MINone,
  rw "lookup-hit" (miLookup vV (MIBCons vV vT vRest)) (MISome vT),
  rw "lookup-miss" (miLookup vV (MIBCons vW vT vRest)) (miLookup vV vRest),

  rw "match-var" (miMatchVar vV vTerm vBs) (miMatchVarK vV vTerm vBs (miLookup vV vBs)),
  rw "match-var-none" (miMatchVarK vV vTerm vBs MINone) (MIMatchOk (MIBCons vV vTerm vBs)),
  rw "match-var-same" (miMatchVarK vV vTerm vBs (MISome vTerm)) (MIMatchOk vBs),
  rw "match-var-diff" (miMatchVarK vV vTerm vBs (MISome vOld)) MIMatchFail,

  rw "match-list-nil-ok" (miMatchList MINil MINil vBs) (MIMatchOk vBs),
  rw "match-list-nil-fail" (miMatchList MINil vTs vBs) MIMatchFail,
  rw "match-list-cons" (miMatchList (MICons vP vPs) (MICons vT vTs) vBs)
    (miMatchListK vPs vTs (miMatch vP vT vBs)),
  rw "match-list-cons-fail" (miMatchList (MICons vP vPs) vTs vBs) MIMatchFail,
  rw "match-listK-ok" (miMatchListK vPs vTs (MIMatchOk vBs2)) (miMatchList vPs vTs vBs2),
  rw "match-listK-fail" (miMatchListK vPs vTs MIMatchFail) MIMatchFail,

  rw "match-var-pattern" (miMatch (app "MIVar" [vV]) vTerm vBs) (miMatchVar vV vTerm vBs),
  rw "match-sym-same" (miMatch (app "MISym" [vV]) (app "MISym" [vV]) vBs) (MIMatchOk vBs),
  rw "match-sym-fail" (miMatch (app "MISym" [vV]) vTerm vBs) MIMatchFail,
  rw "match-app-same" (miMatch (app "MIApp" [vH, vArgs]) (app "MIApp" [vH, vArgs2]) vBs)
    (miMatchList vArgs vArgs2 vBs),
  rw "match-app-fail" (miMatch (app "MIApp" [vH, vArgs]) vTerm vBs) MIMatchFail,

  rw "subst-var" (miSubst vBs (app "MIVar" [vV])) (miSubstVarK (app "MIVar" [vV]) (miLookup vV vBs)),
  rw "subst-var-some" (miSubstVarK vTerm (MISome vT)) vT,
  rw "subst-var-none" (miSubstVarK vTerm MINone) vTerm,
  rw "subst-sym" (miSubst vBs (app "MISym" [vV])) (app "MISym" [vV]),
  rw "subst-app" (miSubst vBs (app "MIApp" [vH, vArgs])) (app "MIApp" [vH, miSubstList vBs vArgs]),
  rw "subst-list-nil" (miSubstList vBs MINil) MINil,
  rw "subst-list-cons" (miSubstList vBs (MICons vX vXs))
    (MICons (miSubst vBs vX) (miSubstList vBs vXs)),

  rw "query-root-nil" (miQueryRoot MIRNil vP vT) MINoRoot,
  rw "query-root-fact" (miQueryRoot (MIRCons (MIFact vFact) vRest) vP vT)
    (miQueryRootK vRest vP vT (miMatch vP vFact MIBNil)),
  rw "query-root-rule-skip" (miQueryRoot (MIRCons (MIRule vLhs vRhs) vRest) vP vT)
    (miQueryRoot vRest vP vT),
  rw "query-rootK-ok" (miQueryRootK vRest vP vT (MIMatchOk vBs))
    (MIRootStep (miSubst vBs vT)),
  rw "query-rootK-fail" (miQueryRootK vRest vP vT MIMatchFail)
    (miQueryRoot vRest vP vT),

  rw "root-match-self"
    (miRoot vRules (MIApp "match" (MICons (MISym "Self") (MICons vP (MICons vT MINil)))))
    (miQueryRoot vRules vP vT),
  rw "root-default" (miRoot vRules vTerm) (miRootTable vRules vTerm),
  rw "root-table-nil" (miRootTable MIRNil vTerm) MINoRoot,
  rw "root-table-fact-skip" (miRootTable (MIRCons (MIFact vFact) vRest) vTerm)
    (miRootTable vRest vTerm),
  rw "root-table-cons" (miRootTable (MIRCons (MIRule vLhs vRhs) vRest) vTerm)
    (miRootK vRest vTerm vRhs (miMatch vLhs vTerm MIBNil)),
  rw "rootK-ok" (miRootK vRest vTerm vRhs (MIMatchOk vBs)) (MIRootStep (miSubst vBs vRhs)),
  rw "rootK-fail" (miRootK vRest vTerm vRhs MIMatchFail) (miRootTable vRest vTerm),

  rw "step-args-nil" (miStepArgs vRules MINil) MINoArgsStep,
  rw "step-args-cons" (miStepArgs vRules (MICons vX vXs))
    (miStepArgsK vRules vX vXs (miStep vRules vX)),
  rw "step-argsK-step" (miStepArgsK vRules vX vXs (MIStep vNext))
    (MIArgsStep (MICons vNext vXs)),
  rw "step-argsK-none" (miStepArgsK vRules vX vXs MINoStep)
    (miStepArgsRestK vX (miStepArgs vRules vXs)),
  rw "step-args-rest-step" (miStepArgsRestK vX (MIArgsStep vXs))
    (MIArgsStep (MICons vX vXs)),
  rw "step-args-rest-none" (miStepArgsRestK vX MINoArgsStep) MINoArgsStep,

  rw "step" (miStep vRules vTerm) (miStepRootK vRules vTerm (miRoot vRules vTerm)),
  rw "step-root" (miStepRootK vRules vTerm (MIRootStep vNext)) (MIStep vNext),
  rw "step-app" (miStepRootK vRules (app "MIApp" [vH, vArgs]) MINoRoot)
    (miStepAppK vH (miStepArgs vRules vArgs)),
  rw "step-non-app" (miStepRootK vRules vTerm MINoRoot) MINoStep,
  rw "step-app-args" (miStepAppK vH (MIArgsStep vArgs2)) (MIStep (app "MIApp" [vH, vArgs2])),
  rw "step-app-none" (miStepAppK vH MINoArgsStep) MINoStep,

  rw "eval-zero" (miEval vRules vTerm FZ) (MIExhausted vTerm),
  rw "eval-succ" (miEval vRules vTerm (FS vFuel))
    (miEvalK vRules vTerm vFuel (miStep vRules vTerm)),
  rw "evalK-step" (miEvalK vRules vTerm vFuel (MIStep vNext)) (miEval vRules vNext vFuel),
  rw "evalK-done" (miEvalK vRules vTerm vFuel MINoStep) (MIDone vTerm),

  rw "run" (miRun vRules vTerm vFuel) (miDecodeVerdict (miEval vRules vTerm vFuel)),
  rw "decode-done" (miDecodeVerdict (MIDone vTerm)) (miDecode vTerm),
  rw "decode-exhausted" (miDecodeVerdict (MIExhausted vTerm)) (MIExhausted vTerm),
  rw "decode-Z" (miDecode (MISym "Z")) Z,
  rw "decode-Nil" (miDecode (MISym "Nil")) Nil,
  rw "decode-S" (miDecode (MIApp "S" (MICons vX MINil))) (S (miDecode vX)),
  rw "decode-Cons" (miDecode (MIApp "Cons" (MICons vX (MICons vXs MINil))))
    (Cons (miDecode vX) (miDecode vXs)),
  rw "decode-N" (miDecode (MIApp "N" (MICons vX MINil))) (N (miDecode vX))
]

def pMI : Presentation := .mk [] [] [] miRules []

def fuel : Nat → AST
  | 0 => FZ
  | n + 1 => FS (fuel n)

def miZ : AST := MISym "Z"
def miNil : AST := MISym "Nil"
def miS (x : AST) : AST := MIApp "S" (MICons x MINil)
def miCons (x xs : AST) : AST := MIApp "Cons" (MICons x (MICons xs MINil))
def miAdd (x y : AST) : AST := MIApp "add" (MICons x (MICons y MINil))
def miListAppend (x y : AST) : AST := MIApp "listAppend" (MICons x (MICons y MINil))
def miLen (x : AST) : AST := MIApp "len" (MICons x MINil)
def miRev (x : AST) : AST := MIApp "rev" (MICons x MINil)
def miN (x : AST) : AST := MIApp "N" (MICons x MINil)
def miVerifiedAnswer (x : AST) : AST := MIApp "verified-answer" (MICons x MINil)
def miMatchSelf (pattern template : AST) : AST :=
  MIApp "match" (MICons (MISym "Self") (MICons pattern (MICons template MINil)))

def rulesAdd : AST :=
  MIRCons
    (MIRule (miAdd miZ (MIVar "n")) (MIVar "n"))
    (MIRCons
      (MIRule (miAdd (miS (MIVar "m")) (MIVar "n"))
        (miS (miAdd (MIVar "m") (MIVar "n"))))
      MIRNil)

def rulesAppendLen : AST :=
  MIRCons
    (MIRule (miListAppend miNil (MIVar "ys")) (MIVar "ys"))
    (MIRCons
      (MIRule (miListAppend (miCons (MIVar "x") (MIVar "xs")) (MIVar "ys"))
        (miCons (MIVar "x") (miListAppend (MIVar "xs") (MIVar "ys"))))
      (MIRCons
        (MIRule (miLen miNil) miZ)
        (MIRCons
          (MIRule (miLen (miCons (MIVar "x") (MIVar "xs")))
            (miS (miLen (MIVar "xs"))))
          MIRNil)))

def rulesRev : AST :=
  MIRCons
    (MIRule (miListAppend miNil (MIVar "ys")) (MIVar "ys"))
    (MIRCons
      (MIRule (miListAppend (miCons (MIVar "x") (MIVar "xs")) (MIVar "ys"))
        (miCons (MIVar "x") (miListAppend (MIVar "xs") (MIVar "ys"))))
      (MIRCons
        (MIRule (miRev miNil) miNil)
        (MIRCons
          (MIRule (miRev (miCons (MIVar "x") (MIVar "xs")))
            (miListAppend (miRev (MIVar "xs")) (miCons (MIVar "x") miNil)))
          MIRNil)))

def miOne : AST := miS miZ
def miTwo : AST := miS miOne
def miThree : AST := miS miTwo

def rulesMatchQuery : AST :=
  MIRCons
    (MIFact (miVerifiedAnswer (miN miTwo)))
    MIRNil

def miList01 : AST := miCons miZ (miCons miOne miNil)
def miList2 : AST := miCons miTwo miNil
def miList012 : AST := miCons miZ (miCons miOne (miCons miTwo miNil))
def miList210 : AST := miCons miTwo (miCons miOne (miCons miZ miNil))
def miMatchQuery : AST :=
  miMatchSelf (miVerifiedAnswer (MIVar "answer")) (MIVar "answer")
def miMissingQuery : AST :=
  miMatchSelf (MIApp "missing-answer" (MICons (MIVar "answer") MINil)) (MIVar "answer")

theorem self_add_0_1 :
    eval pMI 120 (miRun rulesAdd (miAdd miZ miOne) (fuel 6)) = S Z := by
  rfl

theorem self_add_2_1 :
    eval pMI 1000 (miRun rulesAdd (miAdd miTwo miOne) (fuel 10)) = S (S (S Z)) := by
  rfl

theorem self_append_01_2 :
    eval pMI 3000 (miRun rulesAppendLen (miListAppend miList01 miList2) (fuel 20)) =
      Cons Z (Cons (S Z) (Cons (S (S Z)) Nil)) := by
  rfl

theorem self_len_append_01_2 :
    eval pMI 5000 (miRun rulesAppendLen (miLen (miListAppend miList01 miList2)) (fuel 30)) =
      S (S (S Z)) := by
  rfl

theorem self_rev_012 :
    eval pMI 12000 (miRun rulesRev (miRev miList012) (fuel 40)) =
      Cons (S (S Z)) (Cons (S Z) (Cons Z Nil)) := by
  rfl

theorem self_rev_involution_eval_012 :
    eval pMI 12000 (miEval rulesRev (miRev (miRev miList012)) (fuel 40)) =
      MIDone miList012 := by
  rfl

theorem self_rev_involution_decode_012 :
    eval pMI 300 (miDecodeVerdict (MIDone miList012)) =
      Cons Z (Cons (S Z) (Cons (S (S Z)) Nil)) := by
  rfl

theorem self_match_query_answer :
    eval pMI 500 (miRun rulesMatchQuery miMatchQuery (fuel 8)) = N (S (S Z)) := by
  rfl

theorem self_match_query_missing_stays :
    eval pMI 500 (miEval rulesMatchQuery miMissingQuery (fuel 8)) =
      MIDone miMissingQuery := by
  rfl

theorem self_nonmatching_query_stays :
    eval pMI 80 (miEval MIRNil (MIApp "missing" (MICons miZ MINil)) (fuel 3)) =
      MIDone (MIApp "missing" (MICons miZ MINil)) := by
  rfl

theorem self_fuel_exhaustion_visible :
    eval pMI 30 (miEval rulesAdd (miAdd miTwo miOne) FZ) =
      MIExhausted (miAdd miTwo miOne) := by
  rfl

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp
