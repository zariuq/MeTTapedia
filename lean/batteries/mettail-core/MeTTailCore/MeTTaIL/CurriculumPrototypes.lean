import MeTTailCore.MeTTaIL.Profile

/-!
# Curriculum-shaped MeTTaIL language prototypes

This file sketches how the MeTTaKernel curriculum can be seen as a family of
MeTTaIL `LanguageDef`s.  The intent is not to replace a trusted kernel with
search or rewriting; it is to make the mathematical objects of the curricula
explicit as GSLT-shaped signatures: sorts, constructors, equations, rewrites,
and certificate-checking redexes.

The trusted kernel boundary remains outside these definitions: a future kernel
must validate finite certificates and mint theorem objects only through a small
audited rule set.
-/

namespace MeTTailCore.MeTTaIL.CurriculumPrototypes

open MeTTailCore.MeTTaIL.Syntax

namespace DSL

def ty (name : String) : TypeExpr := .base name
def arr (dom cod : TypeExpr) : TypeExpr := .arrow dom cod

def p (name typeName : String) : TermParam :=
  .simple name (ty typeName)

def abs (name dom cod : String) : TermParam :=
  .abstraction name (arr (ty dom) (ty cod))

def kw (s : String) : SyntaxItem := .terminal s
def nt (s : String) : SyntaxItem := .nonTerminal s

def gr (label category : String) (params : List TermParam)
    (items : List SyntaxItem := []) : GrammarRule where
  label := label
  category := category
  params := params
  syntaxPattern := items

def v (name : String) : Pattern := .fvar name
def c (name : String) : Pattern := .apply name []
def app (ctor : String) (args : List Pattern) : Pattern := .apply ctor args

def eqn (name : String) (left right : Pattern)
    (premises : List Premise := []) : Equation where
  name := name
  typeContext := []
  premises := premises
  left := left
  right := right

def rw (name : String) (left right : Pattern)
    (premises : List Premise := []) : RewriteRule where
  name := name
  typeContext := []
  premises := premises
  left := left
  right := right

end DSL

open DSL

/-- Extra metadata for the curriculum-facing role of a `LanguageDef`. -/
structure CurriculumLanguage where
  name : String
  foundation : String
  language : LanguageDef
  curriculumRungs : List String
  trustedBoundary : List String
deriving Repr

/-! ## LCF / HOL profile -/

def lcfHolTerms : List GrammarRule := [
  gr "TyBool" "Ty" [] [kw "bool"],
  gr "TyFun" "Ty" [p "a" "Ty", p "b" "Ty"] [nt "Ty", kw "->", nt "Ty"],
  gr "TmVar" "Tm" [p "x" "Name", p "a" "Ty"] [nt "Name", kw ":", nt "Ty"],
  gr "TmConst" "Tm" [p "c" "Name", p "a" "Ty"] [nt "Name", kw ":", nt "Ty"],
  gr "TmApp" "Tm" [p "f" "Tm", p "x" "Tm"] [kw "(", nt "Tm", nt "Tm", kw ")"],
  gr "TmLam" "Tm" [p "a" "Ty", abs "x" "Tm" "Tm"] [kw "lam", nt "Ty", kw ".", nt "Tm"],
  gr "PEq" "Prop" [p "a" "Ty", p "l" "Tm", p "r" "Tm"] [nt "Tm", kw "=", nt "Tm"],
  gr "PImp" "Prop" [p "p" "Prop", p "q" "Prop"] [nt "Prop", kw "==>", nt "Prop"],
  gr "JThm" "Judgment" [p "p" "Prop"] [kw "|-", nt "Prop"],
  gr "CRefl" "Cert" [p "t" "Tm"] [kw "REFL", nt "Tm"],
  gr "CAssume" "Cert" [p "p" "Prop"] [kw "ASSUME", nt "Prop"],
  gr "CDisch" "Cert" [p "p" "Prop", p "c" "Cert"] [kw "DISCH", nt "Prop", nt "Cert"],
  gr "CMP" "Cert" [p "cf" "Cert", p "cx" "Cert"] [kw "MP", nt "Cert", nt "Cert"],
  gr "CBeta" "Cert" [p "t" "Tm"] [kw "BETA_CONV", nt "Tm"],
  gr "Check" "Judgment" [p "c" "Cert", p "j" "Judgment"] [kw "check", nt "Cert", kw ":", nt "Judgment"]
]

def lcfHolEquations : List Equation := [
  eqn "BetaEq"
    (app "TmApp" [app "TmLam" [v "a", .lambda (v "body")], v "x"])
    (.subst (v "body") (v "x"))
]

def lcfHolRewrites : List RewriteRule := [
  rw "CheckRefl"
    (app "Check" [app "CRefl" [v "t"], app "JThm" [app "PEq" [v "a", v "t", v "t"]]])
    (app "JThm" [app "PEq" [v "a", v "t", v "t"]]),
  rw "CheckDisch"
    (app "Check" [app "CDisch" [v "p", v "c"], app "JThm" [app "PImp" [v "p", v "q"]]])
    (app "JThm" [app "PImp" [v "p", v "q"]]),
  rw "CheckBeta"
    (app "Check" [app "CBeta" [v "t"], app "JThm" [app "PEq" [v "a", v "t", v "u"]]])
    (app "JThm" [app "PEq" [v "a", v "t", v "u"]])
]

def lcfHolLanguage : LanguageDef where
  name := "LCF_HOL_Core"
  types := ["Name", "Ty", "Tm", "Prop", "Cert", "Judgment"]
  terms := lcfHolTerms
  equations := lcfHolEquations
  rewrites := lcfHolRewrites
  congruenceCollections := []

def lcfHolCurriculum : CurriculumLanguage where
  name := "LCF/HOL"
  foundation := "classical higher-order simple type theory with LCF theorem construction"
  language := lcfHolLanguage
  curriculumRungs := [
    "HOL01 logic and tactics",
    "HOL02 induction",
    "HOL03 definitions, datatypes, inductives",
    "HOL04 higher-order quantification and Hilbert choice",
    "HOL05 classical reasoning",
    "HOL06 primitive LCF kernel rules"
  ]
  trustedBoundary := [
    "Only primitive certificate rules may produce closed theorem judgments.",
    "Search, tactics, and generated rewrites may propose certificates but do not mint theorems."
  ]

/-! ## HOTG / Megalodon profile -/

def hotgTerms : List GrammarRule :=
  lcfHolTerms ++ [
    gr "TySet" "Ty" [] [kw "set"],
    gr "SetEmpty" "Tm" [] [kw "Empty"],
    gr "SetUnion" "Tm" [p "x" "Tm"] [kw "Union", nt "Tm"],
    gr "SetPower" "Tm" [p "x" "Tm"] [kw "Power", nt "Tm"],
    gr "SetOmega" "Tm" [] [kw "omega"],
    gr "SetUniverse" "Tm" [p "x" "Tm"] [kw "UnivOf", nt "Tm"],
    gr "PIn" "Prop" [p "x" "Tm", p "y" "Tm"] [nt "Tm", kw ":e", nt "Tm"],
    gr "PSubq" "Prop" [p "x" "Tm", p "y" "Tm"] [nt "Tm", kw "c=", nt "Tm"],
    gr "CExt" "Cert" [p "x" "Tm", p "y" "Tm", p "cxy" "Cert", p "cyx" "Cert"]
      [kw "set_ext", nt "Tm", nt "Tm", nt "Cert", nt "Cert"],
    gr "CInInd" "Cert" [p "p" "Tm", p "step" "Cert"] [kw "In_ind", nt "Tm", nt "Cert"],
    gr "CChoice" "Cert" [p "p" "Prop"] [kw "Eps", nt "Prop"],
    gr "CTGUniverse" "Cert" [p "x" "Tm"] [kw "TG", nt "Tm"]
  ]

def hotgRewrites : List RewriteRule :=
  lcfHolRewrites ++ [
    rw "CheckSetExt"
      (app "Check" [app "CExt" [v "x", v "y", v "cxy", v "cyx"],
        app "JThm" [app "PEq" [app "TySet" [], v "x", v "y"]]])
      (app "JThm" [app "PEq" [app "TySet" [], v "x", v "y"]]),
    rw "CheckMembershipInduction"
      (app "Check" [app "CInInd" [v "p", v "step"], app "JThm" [v "goal"]])
      (app "JThm" [v "goal"]),
    rw "CheckTGUniverse"
      (app "Check" [app "CTGUniverse" [v "x"], app "JThm" [app "PIn" [v "x", app "SetUniverse" [v "x"]]]])
      (app "JThm" [app "PIn" [v "x", app "SetUniverse" [v "x"]]])
  ]

def hotgLanguage : LanguageDef where
  name := "HOTG_Megalodon_Core"
  types := ["Name", "Ty", "Tm", "Prop", "Cert", "Judgment"]
  terms := hotgTerms
  equations := lcfHolEquations
  rewrites := hotgRewrites
  congruenceCollections := []

def hotgCurriculum : CurriculumLanguage where
  name := "Megalodon/HOTG"
  foundation := "higher-order Tarski-Grothendieck set theory as a HOL-family profile"
  language := hotgLanguage
  curriculumRungs := [
    "Megalodon 01-03 propositions, tactics, sets",
    "Megalodon 04 extensionality and membership induction",
    "Megalodon 05 Tarski-Grothendieck universe",
    "Megalodon 06 pairing, singletons, choice, naturals",
    "Megalodon 07 separation and replacement-shaped examples"
  ]
  trustedBoundary := [
    "HOTG axioms are ledgered theory constants, not kernel rules.",
    "Megalodon proof scripts elaborate to certificates for the HOTG profile."
  ]

/-! ## Lean-grade DTT profile -/

def dttTerms : List GrammarRule := [
  gr "LevelZero" "Level" [] [kw "0"],
  gr "LevelSucc" "Level" [p "u" "Level"] [kw "succ", nt "Level"],
  gr "LevelMax" "Level" [p "u" "Level", p "v" "Level"] [kw "max", nt "Level", nt "Level"],
  gr "LevelIMax" "Level" [p "u" "Level", p "v" "Level"] [kw "imax", nt "Level", nt "Level"],
  gr "CtxEmpty" "Ctx" [] [kw "."],
  gr "CtxSnoc" "Ctx" [p "g" "Ctx", p "a" "Ty"] [nt "Ctx", kw ",", nt "Ty"],
  gr "Sort" "Ty" [p "u" "Level"] [kw "Sort", nt "Level"],
  gr "PropSort" "Ty" [] [kw "Prop"],
  gr "Pi" "Ty" [p "a" "Ty", abs "x" "Term" "Ty"] [kw "Pi", nt "Ty", kw ".", nt "Ty"],
  gr "Sigma" "Ty" [p "a" "Ty", abs "x" "Term" "Ty"] [kw "Sigma", nt "Ty", kw ".", nt "Ty"],
  gr "Lam" "Term" [p "a" "Ty", abs "x" "Term" "Term"] [kw "fun", nt "Ty", kw "=>", nt "Term"],
  gr "App" "Term" [p "f" "Term", p "x" "Term"] [kw "(", nt "Term", nt "Term", kw ")"],
  gr "Pair" "Term" [p "x" "Term", p "y" "Term"] [kw "(", nt "Term", kw ",", nt "Term", kw ")"],
  gr "Fst" "Term" [p "p" "Term"] [kw "fst", nt "Term"],
  gr "Snd" "Term" [p "p" "Term"] [kw "snd", nt "Term"],
  gr "Eq" "Ty" [p "a" "Ty", p "x" "Term", p "y" "Term"] [nt "Term", kw "=", nt "Term"],
  gr "Refl" "Term" [p "x" "Term"] [kw "rfl", nt "Term"],
  gr "Inductive" "Ty" [p "name" "Name", p "u" "Level"] [kw "inductive", nt "Name"],
  gr "Recursor" "Term" [p "name" "Name", p "motive" "Term"] [kw "rec", nt "Name", nt "Term"],
  gr "Quot" "Ty" [p "a" "Ty", p "rel" "Term"] [kw "Quot", nt "Ty", nt "Term"],
  gr "QuotMk" "Term" [p "rel" "Term", p "x" "Term"] [kw "Quot.mk", nt "Term", nt "Term"],
  gr "QuotLift" "Term" [p "f" "Term", p "respect" "Term", p "q" "Term"] [kw "Quot.lift", nt "Term", nt "Term", nt "Term"],
  gr "DTTCheck" "Judgment" [p "g" "Ctx", p "t" "Term", p "a" "Ty"] [nt "Ctx", kw "|-", nt "Term", kw ":", nt "Ty"]
]

def dttEquations : List Equation := [
  eqn "PiBeta"
    (app "App" [app "Lam" [v "a", .lambda (v "body")], v "x"])
    (.subst (v "body") (v "x")),
  eqn "SigmaFstBeta"
    (app "Fst" [app "Pair" [v "x", v "y"]])
    (v "x"),
  eqn "SigmaSndBeta"
    (app "Snd" [app "Pair" [v "x", v "y"]])
    (v "y"),
  eqn "QuotLiftMk"
    (app "QuotLift" [v "f", v "respect", app "QuotMk" [v "rel", v "x"]])
    (app "App" [v "f", v "x"])
]

def dttRewrites : List RewriteRule := [
  rw "CheckRefl"
    (app "DTTCheck" [v "g", app "Refl" [v "x"], app "Eq" [v "a", v "x", v "x"]])
    (app "DTTCheck" [v "g", app "Refl" [v "x"], app "Eq" [v "a", v "x", v "x"]]),
  rw "CheckQuotLift"
    (app "DTTCheck" [v "g", app "QuotLift" [v "f", v "respect", v "q"], v "b"])
    (app "DTTCheck" [v "g", app "QuotLift" [v "f", v "respect", v "q"], v "b"])
]

def dttLanguage : LanguageDef where
  name := "LeanGrade_DTT_Core"
  types := ["Name", "Level", "Ctx", "Ty", "Term", "Judgment"]
  terms := dttTerms
  equations := dttEquations
  rewrites := dttRewrites
  congruenceCollections := []

def dttCurriculum : CurriculumLanguage where
  name := "Coq/Lean DTT"
  foundation := "dependent type theory with universes, conversion, inductives, and quotients"
  language := dttLanguage
  curriculumRungs := [
    "Coq ICL 01-15",
    "Lean 01-07 DTT core",
    "Lean 08-12 proof construction, classes, monads, tactics, conv, metaprogramming",
    "Lean 13 quotients",
    "Lean 14 proof irrelevance and eta",
    "Lean 15 impredicative Prop and trusted axioms"
  ]
  trustedBoundary := [
    "Elaboration and tactics produce terms; the kernel checks contexts, conversion, and recursor rules.",
    "Lean axioms such as propext, Classical.choice, and Quot.sound remain ledgered assumptions."
  ]

/-! ## Program-verification profile -/

def programVerificationTerms : List GrammarRule := [
  gr "TyBool" "Ty" [] [kw "Bool"],
  gr "TyNat" "Ty" [] [kw "Nat"],
  gr "TyArr" "Ty" [p "a" "Ty", p "b" "Ty"] [nt "Ty", kw "->", nt "Ty"],
  gr "EVar" "Expr" [p "x" "Name"] [nt "Name"],
  gr "EAbs" "Expr" [p "a" "Ty", abs "x" "Expr" "Expr"] [kw "lam", nt "Ty", kw ".", nt "Expr"],
  gr "EApp" "Expr" [p "f" "Expr", p "x" "Expr"] [kw "(", nt "Expr", nt "Expr", kw ")"],
  gr "Skip" "Cmd" [] [kw "skip"],
  gr "Assign" "Cmd" [p "x" "Name", p "e" "Expr"] [nt "Name", kw ":=", nt "Expr"],
  gr "Seq" "Cmd" [p "c1" "Cmd", p "c2" "Cmd"] [nt "Cmd", kw ";", nt "Cmd"],
  gr "Hoare" "Triple" [p "pre" "Assertion", p "cmd" "Cmd", p "post" "Assertion"]
    [kw "{{", nt "Assertion", kw "}}", nt "Cmd", kw "{{", nt "Assertion", kw "}}"],
  gr "ProgressCert" "PVCert" [p "e" "Expr"] [kw "progress", nt "Expr"],
  gr "PreservationCert" "PVCert" [p "e" "Expr"] [kw "preservation", nt "Expr"],
  gr "SubstitutionCert" "PVCert" [p "e" "Expr"] [kw "subst-lemma", nt "Expr"],
  gr "HoareSoundCert" "PVCert" [p "t" "Triple"] [kw "hoare-sound", nt "Triple"],
  gr "PVCheck" "PVJudgment" [p "c" "PVCert", p "j" "PVJudgment"] [kw "check", nt "PVCert", kw ":", nt "PVJudgment"],
  gr "PVTheorem" "PVJudgment" [p "name" "Name"] [kw "|-", nt "Name"]
]

def programVerificationEquations : List Equation := [
  eqn "StlcBeta"
    (app "EApp" [app "EAbs" [v "a", .lambda (v "body")], v "x"])
    (.subst (v "body") (v "x"))
]

def programVerificationRewrites : List RewriteRule := [
  rw "CheckProgress"
    (app "PVCheck" [app "ProgressCert" [v "e"], app "PVTheorem" [c "progress"]])
    (app "PVTheorem" [c "progress"]),
  rw "CheckPreservation"
    (app "PVCheck" [app "PreservationCert" [v "e"], app "PVTheorem" [c "preservation"]])
    (app "PVTheorem" [c "preservation"]),
  rw "CheckHoareSound"
    (app "PVCheck" [app "HoareSoundCert" [v "triple"], app "PVTheorem" [c "hoare_sound"]])
    (app "PVTheorem" [c "hoare_sound"])
]

def programVerificationLanguage : LanguageDef where
  name := "ProgramVerification_Core"
  types := ["Name", "Ty", "Expr", "Cmd", "Assertion", "Triple", "PVCert", "PVJudgment"]
  terms := programVerificationTerms
  equations := programVerificationEquations
  rewrites := programVerificationRewrites
  congruenceCollections := []

def programVerificationCurriculum : CurriculumLanguage where
  name := "Program verification"
  foundation := "program logics and typed operational semantics over the same certificate discipline"
  language := programVerificationLanguage
  curriculumRungs := [
    "PV01 Imp big-step semantics",
    "PV02 Hoare soundness",
    "PV03 binder-free type-safety prelude",
    "PV04 real STLC progress",
    "PV05 real STLC substitution and preservation",
    "HOL4CakeML verified function and CakeML translation",
    "MeTTaM1 metta-ref ledger and oracle checks"
  ]
  trustedBoundary := [
    "Program evaluators and oracle tests are not proofs unless backed by certificates.",
    "CakeML/HOL artifacts sit in the proved/tested/executed ledger rather than being collapsed."
  ]

/-- The first tranche of curriculum-shaped GSLT profiles. -/
def allCurriculumLanguages : List CurriculumLanguage := [
  lcfHolCurriculum,
  hotgCurriculum,
  dttCurriculum,
  programVerificationCurriculum
]

/-- A small derived summary useful for downstream exporters or status tooling. -/
def curriculumSummary : List (String × String × Nat × Nat × Nat) :=
  allCurriculumLanguages.map fun c =>
    (c.name, c.foundation, c.language.terms.length, c.language.equations.length, c.language.rewrites.length)

/-! ## Executable smoke examples

These are intentionally small.  They show that the prototypes are not just
metadata: the existing `SpecBundle` engine can run a rewrite step over them.
They are not a replacement for the future trusted kernel checker.
-/

namespace ExecutableExamples

open MeTTailCore.MeTTaIL.Profile

def lcfHolBundle : SpecBundle where
  language := lcfHolLanguage

def reflQuery : Pattern :=
  app "Check" [
    app "CRefl" [c "x"],
    app "JThm" [app "PEq" [c "num", c "x", c "x"]]
  ]

def reflJudgment : Pattern :=
  app "JThm" [app "PEq" [c "num", c "x", c "x"]]

def reflStepResult : List Pattern :=
  SpecBundle.rewriteStep lcfHolBundle reflQuery

example : reflStepResult = [reflJudgment] := by
  native_decide

end ExecutableExamples

end MeTTailCore.MeTTaIL.CurriculumPrototypes
