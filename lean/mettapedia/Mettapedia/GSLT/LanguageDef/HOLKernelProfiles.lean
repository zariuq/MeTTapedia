import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.LogicSemantics
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# HOL Kernel Profiles

This module pins two distinct HOL kernel profiles as `LanguageDef` values:

* `holLightEqKernel`: the HOL Light equality-kernel rule set from
  `repos/itp-curriculum-sources/hol_light/fusion.ml`, with implication and
  conjunction treated as definitions rather than primitive proof rules.
* `hol4LcfKernel`: the HOL4 LCF rule set from
  `repos/itp-curriculum-sources/hol4/src/prekernel/FinalThm-sig.sml` and
  `repos/itp-curriculum-sources/hol4/src/thm/std-thm.ML`, where `DISCH` and
  `MP` are primitive.

The shared object syntax is deliberately small and abstract: HOL terms,
hypothesis sets, theorem sequents, and proof-rule certificates.  The important
distinction here is the kernel rule set.  The module also records an honesty
check: the current OSLF reducer consumes rewrite rules and premise queries; a
generic bridge now saturates finite Datalog clauses from `logic` into the
relation environment, while full checker adequacy remains open.
-/

namespace Mettapedia.GSLT.LanguageDef.HOLKernelProfiles

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis

private def ty (name : String) : TypeExpr :=
  .base name

private def termCtor (label category : String) (params : List (String × String)) :
    GrammarRule :=
  { label := label
    category := category
    params := params.map fun (name, typeName) => .simple name (ty typeName)
    syntaxPattern := [] }

private def rel (name : String) (args : List String) : LogicDecl :=
  .relation { name := name, argTypes := args.map ty }

private def ruleNote (text : String) : LogicDecl :=
  .ruleText text

private def datalogAtom (relName : String) (args : List DatalogTerm) : DatalogAtom :=
  { rel := relName, args := args }

private def datalogRule (name relName : String) (args : List DatalogTerm)
    (body : List DatalogAtom) : LogicDecl :=
  .datalogClause
    { name := name
      head := datalogAtom relName args
      body := body }

private def datalogFact (name relName : String) (args : List String) : LogicDecl :=
  datalogRule name relName (args.map DatalogTerm.const) []

private def pvar (name : String) : Pattern :=
  .fvar name

private def app (name : String) (args : List Pattern := []) : Pattern :=
  .apply name args

private def check (name : String) (proof : Pattern) : Pattern :=
  app name [proof]

/-- Root rule results for these kernel profiles.  The profile rules have no
contextual premises, so contextual depth one is exact. -/
private def kernelReducts (relEnv : RelationEnv) (lang : LanguageDef)
    (term : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises relEnv) lang 1 term

private def ok (name : String) (thm : Pattern) : Pattern :=
  app name [thm]

private def seq (hyps concl : Pattern) : Pattern :=
  app "Seq" [hyps, concl]

private def eqTerm (lhs rhs : Pattern) : Pattern :=
  app "Eq" [lhs, rhs]

private def impTerm (ant cons : Pattern) : Pattern :=
  app "Imp" [ant, cons]

private def aTerm : Pattern :=
  app "A"

private def bTerm : Pattern :=
  app "B"

private def andTermAA : Pattern :=
  app "AndAA"

private def appTerm (fn arg : Pattern) : Pattern :=
  app "App" [fn, arg]

private def absTerm (v body : Pattern) : Pattern :=
  app "AbsTerm" [v, body]

private def emptyHyps : Pattern :=
  app "EmptyHyps"

private def hyp (p : Pattern) : Pattern :=
  app "Hyp" [p]

private def unionHyps (h₁ h₂ : Pattern) : Pattern :=
  app "UnionHyps" [h₁, h₂]

private def removeHyp (p h : Pattern) : Pattern :=
  app "RemoveHyp" [p, h]

private def instTypeTerm (theta p : Pattern) : Pattern :=
  app "InstTypeTerm" [theta, p]

private def instTypeHyps (theta h : Pattern) : Pattern :=
  app "InstTypeHyps" [theta, h]

private def instTerm (sigma p : Pattern) : Pattern :=
  app "InstTerm" [sigma, p]

private def instHyps (sigma h : Pattern) : Pattern :=
  app "InstHyps" [sigma, h]

private def betaResult (redex result : Pattern) : Premise :=
  .relationQuery "betaResult" [redex, result]

private def isBool (p : Pattern) : Premise :=
  .relationQuery "isBool" [p]

private def notFreeIn (v h : Pattern) : Premise :=
  .relationQuery "notFreeIn" [v, h]

private def rw (name : String) (premises : List Premise) (lhs rhs : Pattern) :
    RewriteRule :=
  { name := name, typeContext := [], premises := premises, left := lhs, right := rhs }

private def proofArticle (witness exported result : Pattern) (children : List ProofArticle) :
    ProofArticle :=
  { witness := witness, exported := exported, result := result, children := children }

private def commonTypes : List TypeDecl :=
  [ TypeDecl.plain "HolTerm"
  , TypeDecl.plain "HolHyps"
  , TypeDecl.plain "HolThm"
  , TypeDecl.plain "HolProof"
  , TypeDecl.plain "HolJudgment"
  , TypeDecl.plain "HolSubst" ]

private def commonTerms : List GrammarRule :=
  [ termCtor "A" "HolTerm" []
  , termCtor "B" "HolTerm" []
  , termCtor "C" "HolTerm" []
  , termCtor "AndAA" "HolTerm" []
  , termCtor "F" "HolTerm" []
  , termCtor "G" "HolTerm" []
  , termCtor "X" "HolTerm" []
  , termCtor "Y" "HolTerm" []
  , termCtor "Theta" "HolSubst" []
  , termCtor "Sigma" "HolSubst" []
  , termCtor "EmptyHyps" "HolHyps" []
  , termCtor "Hyp" "HolHyps" [("p", "HolTerm")]
  , termCtor "UnionHyps" "HolHyps" [("h1", "HolHyps"), ("h2", "HolHyps")]
  , termCtor "RemoveHyp" "HolHyps" [("p", "HolTerm"), ("h", "HolHyps")]
  , termCtor "Seq" "HolThm" [("hyps", "HolHyps"), ("concl", "HolTerm")]
  , termCtor "Eq" "HolTerm" [("lhs", "HolTerm"), ("rhs", "HolTerm")]
  , termCtor "Imp" "HolTerm" [("ant", "HolTerm"), ("cons", "HolTerm")]
  , termCtor "App" "HolTerm" [("fn", "HolTerm"), ("arg", "HolTerm")]
  , termCtor "AbsTerm" "HolTerm" [("v", "HolTerm"), ("body", "HolTerm")]
  , termCtor "InstTypeTerm" "HolTerm" [("theta", "HolSubst"), ("p", "HolTerm")]
  , termCtor "InstTypeHyps" "HolHyps" [("theta", "HolSubst"), ("h", "HolHyps")]
  , termCtor "InstTerm" "HolTerm" [("sigma", "HolSubst"), ("p", "HolTerm")]
  , termCtor "InstHyps" "HolHyps" [("sigma", "HolSubst"), ("h", "HolHyps")]
  , termCtor "HLCheck" "HolJudgment" [("proof", "HolProof")]
  , termCtor "HLOk" "HolJudgment" [("thm", "HolThm")]
  , termCtor "H4Check" "HolJudgment" [("proof", "HolProof")]
  , termCtor "H4Ok" "HolJudgment" [("thm", "HolThm")] ]

private def holLightProofTerms : List GrammarRule :=
  [ termCtor "HL_REFL" "HolProof" [("p", "HolTerm")]
  , termCtor "HL_TRANS" "HolProof" [("pq", "HolThm"), ("qr", "HolThm")]
  , termCtor "HL_MK_COMB" "HolProof" [("fg", "HolThm"), ("xy", "HolThm")]
  , termCtor "HL_ABS" "HolProof" [("v", "HolTerm"), ("eq", "HolThm")]
  , termCtor "HL_BETA" "HolProof" [("redex", "HolTerm")]
  , termCtor "HL_ASSUME" "HolProof" [("p", "HolTerm")]
  , termCtor "HL_EQ_MP" "HolProof" [("eq", "HolThm"), ("p", "HolThm")]
  , termCtor "HL_DEDUCT_ANTISYM" "HolProof" [("pq", "HolThm"), ("qp", "HolThm")]
  , termCtor "HL_INST_TYPE" "HolProof" [("theta", "HolSubst"), ("thm", "HolThm")]
  , termCtor "HL_INST" "HolProof" [("sigma", "HolSubst"), ("thm", "HolThm")]
  , termCtor "HL_CONJ_AA_REPLAY" "HolProof" [("left", "HolThm"), ("right", "HolThm")]
  , termCtor "HL_CONJUNCT1_AA_REPLAY" "HolProof" [("conj", "HolThm")]
  , termCtor "HL_IMP_DEF_AA" "HolProof" [] ]

private def hol4ProofTerms : List GrammarRule :=
  [ termCtor "H4_ASSUME" "HolProof" [("p", "HolTerm")]
  , termCtor "H4_REFL" "HolProof" [("p", "HolTerm")]
  , termCtor "H4_BETA_CONV" "HolProof" [("redex", "HolTerm")]
  , termCtor "H4_ABS" "HolProof" [("v", "HolTerm"), ("eq", "HolThm")]
  , termCtor "H4_DISCH" "HolProof" [("p", "HolTerm"), ("thm", "HolThm")]
  , termCtor "H4_MP" "HolProof" [("imp", "HolThm"), ("arg", "HolThm")]
  , termCtor "H4_SUBST" "HolProof" [("sigma", "HolSubst"), ("template", "HolTerm"), ("thm", "HolThm")]
  , termCtor "H4_INST_TYPE" "HolProof" [("theta", "HolSubst"), ("thm", "HolThm")] ]

private def sideConditionLogic : List LogicDecl :=
  [ rel "isBool" ["HolTerm"]
  , rel "holBoolSeed" ["HolTerm"]
  , rel "notFreeIn" ["HolTerm", "HolHyps"]
  , rel "betaResult" ["HolTerm", "HolTerm"]
  , datalogFact "holBoolSeed-A" "holBoolSeed" ["A"]
  , datalogFact "holBoolSeed-B" "holBoolSeed" ["B"]
  , datalogFact "holBoolSeed-AndAA" "holBoolSeed" ["AndAA"]
  , datalogRule "isBool-from-seed" "isBool" [.var "P"]
      [datalogAtom "holBoolSeed" [.var "P"]] ]

private def P := pvar "P"
private def Q := pvar "Q"
private def R := pvar "R"
private def Fv := pvar "Fv"
private def Gv := pvar "Gv"
private def Xv := pvar "Xv"
private def Yv := pvar "Yv"
private def H1v := pvar "H1"
private def H2v := pvar "H2"
private def ThetaV := pvar "ThetaV"
private def SigmaV := pvar "SigmaV"

private def holLightRewrites : List RewriteRule :=
  [ rw "HL_REFL" []
      (check "HLCheck" (app "HL_REFL" [P]))
      (ok "HLOk" (seq emptyHyps (eqTerm P P)))
  , rw "HL_TRANS" []
      (check "HLCheck" (app "HL_TRANS" [seq H1v (eqTerm P Q), seq H2v (eqTerm Q R)]))
      (ok "HLOk" (seq (unionHyps H1v H2v) (eqTerm P R)))
  , rw "HL_MK_COMB" []
      (check "HLCheck" (app "HL_MK_COMB" [seq H1v (eqTerm Fv Gv), seq H2v (eqTerm Xv Yv)]))
      (ok "HLOk" (seq (unionHyps H1v H2v) (eqTerm (appTerm Fv Xv) (appTerm Gv Yv))))
  , rw "HL_ABS" [notFreeIn Xv H1v]
      (check "HLCheck" (app "HL_ABS" [Xv, seq H1v (eqTerm P Q)]))
      (ok "HLOk" (seq H1v (eqTerm (absTerm Xv P) (absTerm Xv Q))))
  , rw "HL_BETA" [betaResult P Q]
      (check "HLCheck" (app "HL_BETA" [P]))
      (ok "HLOk" (seq emptyHyps (eqTerm P Q)))
  , rw "HL_ASSUME" [isBool P]
      (check "HLCheck" (app "HL_ASSUME" [P]))
      (ok "HLOk" (seq (hyp P) P))
  , rw "HL_EQ_MP" []
      (check "HLCheck" (app "HL_EQ_MP" [seq H1v (eqTerm P Q), seq H2v P]))
      (ok "HLOk" (seq (unionHyps H1v H2v) Q))
  , rw "HL_DEDUCT_ANTISYM" []
      (check "HLCheck" (app "HL_DEDUCT_ANTISYM" [seq H1v P, seq H2v Q]))
      (ok "HLOk" (seq (unionHyps (removeHyp Q H1v) (removeHyp P H2v)) (eqTerm P Q)))
  , rw "HL_INST_TYPE" []
      (check "HLCheck" (app "HL_INST_TYPE" [ThetaV, seq H1v P]))
      (ok "HLOk" (seq (instTypeHyps ThetaV H1v) (instTypeTerm ThetaV P)))
  , rw "HL_INST" []
      (check "HLCheck" (app "HL_INST" [SigmaV, seq H1v P]))
      (ok "HLOk" (seq (instHyps SigmaV H1v) (instTerm SigmaV P))) ]

private def holLightBoolReplayRewrites : List RewriteRule :=
  [ rw "HL_EQ_MP_EMPTY"
      []
      (check "HLCheck" (app "HL_EQ_MP" [seq emptyHyps (eqTerm P Q), seq emptyHyps P]))
      (ok "HLOk" (seq emptyHyps Q))
  , rw "HL_DEDUCT_ANTISYM_SINGLETON"
      []
      (check "HLCheck" (app "HL_DEDUCT_ANTISYM" [seq (hyp Q) P, seq (hyp P) Q]))
      (ok "HLOk" (seq emptyHyps (eqTerm P Q)))
  , rw "HL_CONJ_AA_REPLAY"
      [isBool aTerm]
      (check "HLCheck" (app "HL_CONJ_AA_REPLAY" [seq (hyp aTerm) aTerm, seq (hyp aTerm) aTerm]))
      (ok "HLOk" (seq (hyp aTerm) andTermAA))
  , rw "HL_CONJUNCT1_AA_REPLAY"
      [isBool andTermAA]
      (check "HLCheck" (app "HL_CONJUNCT1_AA_REPLAY" [seq (hyp andTermAA) andTermAA]))
      (ok "HLOk" (seq (hyp andTermAA) aTerm))
  , rw "HL_IMP_DEF_AA"
      []
      (check "HLCheck" (app "HL_IMP_DEF_AA"))
      (ok "HLOk" (seq emptyHyps (eqTerm (eqTerm andTermAA aTerm) (impTerm aTerm aTerm)))) ]

private def holLightProfileRewrites : List RewriteRule :=
  holLightRewrites ++ holLightBoolReplayRewrites

private def hol4Rewrites : List RewriteRule :=
  [ rw "H4_ASSUME" [isBool P]
      (check "H4Check" (app "H4_ASSUME" [P]))
      (ok "H4Ok" (seq (hyp P) P))
  , rw "H4_REFL" []
      (check "H4Check" (app "H4_REFL" [P]))
      (ok "H4Ok" (seq emptyHyps (eqTerm P P)))
  , rw "H4_BETA_CONV" [betaResult P Q]
      (check "H4Check" (app "H4_BETA_CONV" [P]))
      (ok "H4Ok" (seq emptyHyps (eqTerm P Q)))
  , rw "H4_ABS" [notFreeIn Xv H1v]
      (check "H4Check" (app "H4_ABS" [Xv, seq H1v (eqTerm P Q)]))
      (ok "H4Ok" (seq H1v (eqTerm (absTerm Xv P) (absTerm Xv Q))))
  , rw "H4_DISCH" [isBool P]
      (check "H4Check" (app "H4_DISCH" [P, seq H1v Q]))
      (ok "H4Ok" (seq (removeHyp P H1v) (impTerm P Q)))
  , rw "H4_MP" []
      (check "H4Check" (app "H4_MP" [seq H1v (impTerm P Q), seq H2v P]))
      (ok "H4Ok" (seq (unionHyps H1v H2v) Q))
  , rw "H4_SUBST" []
      (check "H4Check" (app "H4_SUBST" [SigmaV, R, seq H1v P]))
      (ok "H4Ok" (seq (instHyps SigmaV H1v) (instTerm SigmaV R)))
  , rw "H4_INST_TYPE" []
      (check "H4Check" (app "H4_INST_TYPE" [ThetaV, seq H1v P]))
      (ok "H4Ok" (seq (instTypeHyps ThetaV H1v) (instTypeTerm ThetaV P))) ]

/-- HOL Light equality-kernel profile: `DISCH` and `MP` are not primitive rules. -/
def holLightEqKernel : LanguageDef :=
  { name := "HOLLightEqKernel"
    types := commonTypes
    terms := commonTerms ++ holLightProofTerms
    equations := []
    rewrites := holLightProfileRewrites
    logic :=
      sideConditionLogic ++
      [ ruleNote "Source primitive block: fusion.ml REFL TRANS MK_COMB ABS BETA ASSUME EQ_MP DEDUCT_ANTISYM INST_TYPE INST"
      , ruleNote "Bounded source replay block: bool.ml CONJ/CONJUNCT1/DISCH for A ==> A through IMP_DEF and equality-kernel rules"
      , ruleNote "Connectives are definitional: bool.ml T_DEF AND_DEF IMP_DEF FORALL_DEF" ]
    oracles := [] }

/-- HOL4 LCF profile: `DISCH` and `MP` are primitive rules. -/
def hol4LcfKernel : LanguageDef :=
  { name := "HOL4LcfKernel"
    types := commonTypes
    terms := commonTerms ++ hol4ProofTerms
    equations := []
    rewrites := hol4Rewrites
    logic :=
      sideConditionLogic ++
      [ ruleNote "Source primitive block: FinalThm-sig.sml ASSUME REFL BETA_CONV ABS DISCH MP SUBST INST_TYPE"
      , ruleNote "Implementation anchor: std-thm.ML primitive rules of inference" ]
    oracles := [] }

def holLightNoLogic : LanguageDef :=
  { holLightEqKernel with logic := [] }

def hol4NoLogic : LanguageDef :=
  { hol4LcfKernel with logic := [] }

def holLightLogicRelationEnv : RelationEnv :=
  Mettapedia.OSLF.MeTTaIL.LogicSemantics.logicDatalogRelationEnv holLightEqKernel

def hol4LogicRelationEnv : RelationEnv :=
  Mettapedia.OSLF.MeTTaIL.LogicSemantics.logicDatalogRelationEnv hol4LcfKernel

def holLightNoLogicRelationEnv : RelationEnv :=
  Mettapedia.OSLF.MeTTaIL.LogicSemantics.logicDatalogRelationEnv holLightNoLogic

def hol4NoLogicRelationEnv : RelationEnv :=
  Mettapedia.OSLF.MeTTaIL.LogicSemantics.logicDatalogRelationEnv hol4NoLogic

/-- OSLF construction endpoint using relation tuples induced by finite `logic` closure. -/
def holLightOSLF :=
  langOSLFWithLogic holLightEqKernel "HolJudgment"

/-- OSLF construction endpoint using relation tuples induced by finite `logic` closure. -/
def hol4OSLF :=
  langOSLFWithLogic hol4LcfKernel "HolJudgment"

def A : Pattern := aTerm
def B : Pattern := bTerm
def AndAA : Pattern := andTermAA

def hol4DischWitness : Pattern :=
  check "H4Check" (app "H4_DISCH" [A, seq (hyp A) A])

def hol4DischResult : Pattern :=
  ok "H4Ok" (seq (removeHyp A (hyp A)) (impTerm A A))

def hol4AssumeAWitness : Pattern :=
  check "H4Check" (app "H4_ASSUME" [A])

def hol4AssumeAResult : Pattern :=
  ok "H4Ok" (seq (hyp A) A)

def hol4MPWitness : Pattern :=
  check "H4Check" (app "H4_MP" [seq emptyHyps (impTerm A B), seq (hyp A) A])

def hol4MPResult : Pattern :=
  ok "H4Ok" (seq (unionHyps emptyHyps (hyp A)) B)

def hol4BadMPWitness : Pattern :=
  check "H4Check" (app "H4_MP" [seq emptyHyps (impTerm A B), seq (hyp B) B])

def hol4SelfMPWitness : Pattern :=
  check "H4Check"
    (app "H4_MP"
      [ seq (removeHyp A (hyp A)) (impTerm A A)
      , seq (hyp A) A ])

def hol4SelfMPResult : Pattern :=
  ok "H4Ok" (seq (unionHyps (removeHyp A (hyp A)) (hyp A)) A)

def holLightReflWitness : Pattern :=
  check "HLCheck" (app "HL_REFL" [A])

def holLightReflResult : Pattern :=
  ok "HLOk" (seq emptyHyps (eqTerm A A))

def holLightBadEqMPWitness : Pattern :=
  check "HLCheck" (app "HL_EQ_MP" [seq emptyHyps (eqTerm A B), seq (hyp B) B])

def holLightAssumeAWitness : Pattern :=
  check "HLCheck" (app "HL_ASSUME" [A])

def holLightAssumeAResult : Pattern :=
  ok "HLOk" (seq (hyp A) A)

def holLightAssumeAndAAWitness : Pattern :=
  check "HLCheck" (app "HL_ASSUME" [AndAA])

def holLightAssumeAndAAResult : Pattern :=
  ok "HLOk" (seq (hyp AndAA) AndAA)

def holLightConjAAWitness : Pattern :=
  check "HLCheck" (app "HL_CONJ_AA_REPLAY" [seq (hyp A) A, seq (hyp A) A])

def holLightConjAAResult : Pattern :=
  ok "HLOk" (seq (hyp A) AndAA)

def holLightConjunct1AAWitness : Pattern :=
  check "HLCheck" (app "HL_CONJUNCT1_AA_REPLAY" [seq (hyp AndAA) AndAA])

def holLightConjunct1AAResult : Pattern :=
  ok "HLOk" (seq (hyp AndAA) A)

def holLightDischAACoreWitness : Pattern :=
  check "HLCheck" (app "HL_DEDUCT_ANTISYM" [seq (hyp A) AndAA, seq (hyp AndAA) A])

def holLightDischAACoreResult : Pattern :=
  ok "HLOk" (seq emptyHyps (eqTerm AndAA A))

def holLightImpDefAAWitness : Pattern :=
  check "HLCheck" (app "HL_IMP_DEF_AA")

def holLightImpDefAAResult : Pattern :=
  ok "HLOk" (seq emptyHyps (eqTerm (eqTerm AndAA A) (impTerm A A)))

def holLightSelfImpWitness : Pattern :=
  check "HLCheck"
    (app "HL_EQ_MP"
      [ seq emptyHyps (eqTerm (eqTerm AndAA A) (impTerm A A))
      , seq emptyHyps (eqTerm AndAA A) ])

def holLightSelfImpResult : Pattern :=
  ok "HLOk" (seq emptyHyps (impTerm A A))

def holLightPrimitiveDischShortcutWitness : Pattern :=
  check "HLCheck" (app "H4_DISCH" [A, seq (hyp A) A])

def holLightBadSelfImpWitness : Pattern :=
  check "HLCheck"
    (app "HL_EQ_MP"
      [ seq emptyHyps (eqTerm (eqTerm AndAA B) (impTerm A A))
      , seq emptyHyps (eqTerm AndAA A) ])

def hol4AssumeAArticle : ProofArticle :=
  proofArticle hol4AssumeAWitness (seq (hyp A) A) hol4AssumeAResult []

def hol4DischArticle : ProofArticle :=
  proofArticle hol4DischWitness (seq (removeHyp A (hyp A)) (impTerm A A))
    hol4DischResult [hol4AssumeAArticle]

def hol4SelfMPArticle : ProofArticle :=
  proofArticle hol4SelfMPWitness (seq (unionHyps (removeHyp A (hyp A)) (hyp A)) A)
    hol4SelfMPResult [hol4DischArticle, hol4AssumeAArticle]

def hol4BadMPArticle : ProofArticle :=
  proofArticle hol4BadMPWitness (seq (unionHyps emptyHyps (hyp B)) B)
    (ok "H4Ok" (seq (unionHyps emptyHyps (hyp B)) B)) []

def holLightAssumeAArticle : ProofArticle :=
  proofArticle holLightAssumeAWitness (seq (hyp A) A) holLightAssumeAResult []

def holLightAssumeAndAAArticle : ProofArticle :=
  proofArticle holLightAssumeAndAAWitness (seq (hyp AndAA) AndAA)
    holLightAssumeAndAAResult []

def holLightConjAAArticle : ProofArticle :=
  proofArticle holLightConjAAWitness (seq (hyp A) AndAA) holLightConjAAResult
    [holLightAssumeAArticle, holLightAssumeAArticle]

def holLightConjunct1AAArticle : ProofArticle :=
  proofArticle holLightConjunct1AAWitness (seq (hyp AndAA) A)
    holLightConjunct1AAResult [holLightAssumeAndAAArticle]

def holLightDischAACoreArticle : ProofArticle :=
  proofArticle holLightDischAACoreWitness (seq emptyHyps (eqTerm AndAA A))
    holLightDischAACoreResult [holLightConjAAArticle, holLightConjunct1AAArticle]

def holLightImpDefAAArticle : ProofArticle :=
  proofArticle holLightImpDefAAWitness
    (seq emptyHyps (eqTerm (eqTerm AndAA A) (impTerm A A)))
    holLightImpDefAAResult []

def holLightSelfImpArticle : ProofArticle :=
  proofArticle holLightSelfImpWitness (seq emptyHyps (impTerm A A))
    holLightSelfImpResult [holLightImpDefAAArticle, holLightDischAACoreArticle]

def holLightPrimitiveDischShortcutArticle : ProofArticle :=
  proofArticle holLightPrimitiveDischShortcutWitness (seq emptyHyps (impTerm A A))
    (ok "HLOk" (seq emptyHyps (impTerm A A))) [holLightAssumeAArticle]

def holLightBadSelfImpArticle : ProofArticle :=
  proofArticle holLightBadSelfImpWitness (seq emptyHyps (impTerm A A))
    holLightSelfImpResult [holLightImpDefAAArticle, holLightDischAACoreArticle]

#guard
    (Mettapedia.OSLF.MeTTaIL.LogicSemantics.logicFactRelationEnv hol4LcfKernel).tuples
      "isBool" [A] == []

#guard
    hol4LogicRelationEnv.tuples "isBool" [A] == [[A], [B], [AndAA]]

#guard
    hol4NoLogicRelationEnv.tuples "isBool" [A] == []

#guard
    kernelReducts hol4LogicRelationEnv hol4LcfKernel hol4DischWitness ==
      [hol4DischResult]

#guard
    kernelReducts hol4NoLogicRelationEnv hol4NoLogic hol4DischWitness ==
      []

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel hol4DischWitness ==
      []

#guard
    kernelReducts hol4LogicRelationEnv hol4LcfKernel hol4MPWitness ==
      [hol4MPResult]

#guard
    kernelReducts hol4LogicRelationEnv hol4LcfKernel hol4BadMPWitness ==
      []

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel hol4MPWitness ==
      []

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel holLightReflWitness ==
      [holLightReflResult]

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel holLightBadEqMPWitness ==
      []

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel holLightAssumeAWitness ==
      [holLightAssumeAResult]

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel holLightAssumeAndAAWitness ==
      [holLightAssumeAndAAResult]

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel holLightConjAAWitness ==
      [holLightConjAAResult]

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel holLightConjunct1AAWitness ==
      [holLightConjunct1AAResult]

#guard
    (kernelReducts holLightLogicRelationEnv holLightEqKernel
      holLightDischAACoreWitness).contains holLightDischAACoreResult

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel holLightImpDefAAWitness ==
      [holLightImpDefAAResult]

#guard
    (kernelReducts holLightLogicRelationEnv holLightEqKernel
      holLightSelfImpWitness).contains holLightSelfImpResult

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel
      holLightPrimitiveDischShortcutWitness == []

#guard
    kernelReducts holLightLogicRelationEnv holLightEqKernel
      holLightBadSelfImpWitness == []

#guard
    checkProofArticleWithEnv hol4LogicRelationEnv hol4LcfKernel 4 hol4SelfMPArticle

#guard
    checkProofArticleWithEnv holLightLogicRelationEnv holLightEqKernel 4 hol4SelfMPArticle == false

#guard
    checkProofArticleWithEnv hol4LogicRelationEnv hol4LcfKernel 2 hol4BadMPArticle == false

#guard
    checkProofArticleWithEnv holLightLogicRelationEnv holLightEqKernel 6 holLightSelfImpArticle

#guard
    checkProofArticleWithEnv hol4LogicRelationEnv hol4LcfKernel 6 holLightSelfImpArticle == false

#guard
    checkProofArticleWithEnv holLightLogicRelationEnv holLightEqKernel 3
      holLightPrimitiveDischShortcutArticle == false

#guard
    checkProofArticleWithEnv holLightLogicRelationEnv holLightEqKernel 6
      holLightBadSelfImpArticle == false

example : holLightRewrites.length = 10 := rfl
example : holLightProfileRewrites.length = 15 := rfl
example : hol4LcfKernel.rewrites.length = 8 := by decide
example : holLightEqKernel.logic.length = 11 := rfl
example : hol4LcfKernel.logic.length = 10 := rfl
#guard LanguageDef.validate holLightEqKernel == []
#guard LanguageDef.validate hol4LcfKernel == []

end Mettapedia.GSLT.LanguageDef.HOLKernelProfiles
