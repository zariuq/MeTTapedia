import Mettapedia.GSLT.LanguageDef.InferenceExtraction
import Mettapedia.GSLT.LanguageDef.LogicExtension

/-!
# Source-scale HOL kernel definitions

Unlike the finite `HOLKernelProfiles` calibration, these language definitions
use an open byte-string carrier for names and recursive HOL type, term,
hypothesis, and substitution syntax.  Primitive rules expose every operation
whose result must be certified by a source adapter as an explicit relation
premise.  Proof-relevant extraction therefore retains both theorem premises
and ordered side-condition evidence.
-/

namespace Mettapedia.GSLT.LanguageDef.HOLSourceKernel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtraction
open Mettapedia.GSLT.LanguageDef.LogicExtension

private def ty (name : String) : TypeExpr := .base name

private def termCtor (label category : String) (parameters : List (String × String)) :
    GrammarRule :=
  { label
    category
    params := parameters.map fun (name, typeName) => .simple name (ty typeName)
    syntaxPattern := [] }

private def rel (name : String) (arguments : List String) : LogicDeclaration :=
  .relation { name, argTypes := arguments.map ty }

private def app (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def pvar (name : String) : Pattern := .fvar name

private def rw (name : String) (premises : List Premise) (left right : Pattern) :
    RewriteRule :=
  { name, typeContext := [], premises, left, right }

private def query (name : String) (arguments : List Pattern) : Premise :=
  .relationQuery name arguments

private def check (head : String) (proof : Pattern) : Pattern := app head [proof]
private def ok (head : String) (result : Pattern) : Pattern := app head [result]

def nameHead (value : String) : String :=
  "$hol.name." ++ String.intercalate "." (value.toUTF8.toList.map fun byte =>
    toString byte.toNat)

def encodeName (value : String) : Pattern :=
  app (nameHead value)

private def tyNil : Pattern := app "TyNil"
private def tyCons (head tail : Pattern) : Pattern := app "TyCons" [head, tail]
private def tyList (values : List Pattern) : Pattern := values.foldr tyCons tyNil
private def tyApp (name : String) (arguments : List Pattern := []) : Pattern :=
  app "TyApp" [encodeName name, tyList arguments]

private def boolTy : Pattern := app "$hol.type.bool"
private def funTy (domain codomain : Pattern) : Pattern := tyApp "fun" [domain, codomain]

private def tmVar (name : Pattern) (type : Pattern) : Pattern := app "TmVar" [name, type]
private def tmConst (name : String) (type : Pattern) : Pattern :=
  app "TmConst" [encodeName name, type]
private def tmApp (function argument : Pattern) : Pattern := app "TmApp" [function, argument]
private def tmAbs (binder body : Pattern) : Pattern := app "TmAbs" [binder, body]

private def eqTerm (type left right : Pattern) : Pattern :=
  let equalityType := funTy type (funTy type boolTy)
  tmApp (tmApp (tmConst "=" equalityType) left) right

private def impTerm (antecedent consequent : Pattern) : Pattern :=
  let implicationType := funTy boolTy (funTy boolTy boolTy)
  tmApp (tmApp (tmConst "==>" implicationType) antecedent) consequent

private def hypsNil : Pattern := app "HypsNil"
private def hypsCons (head tail : Pattern) : Pattern := app "HypsCons" [head, tail]
private def seq (hypotheses conclusion : Pattern) : Pattern := app "Seq" [hypotheses, conclusion]

private def commonTypes : List TypeDecl :=
  [ "HolName", "HolType", "HolTypeList", "HolTerm", "HolHyps",
    "HolThm", "HolResult", "HolProof", "HolJudgment", "HolTermMap", "HolTypeMap",
    "HolSubst" ].map
      TypeDecl.plain

private def commonTerms : List GrammarRule :=
  [ termCtor (nameHead "=") "HolName" []
  , termCtor (nameHead "==>") "HolName" []
  , termCtor (nameHead "bool") "HolName" []
  , termCtor (nameHead "fun") "HolName" []
  , termCtor "$hol.type.bool" "HolType" []
  , termCtor "TyVar" "HolType" [("name", "HolName")]
  , termCtor "TyApp" "HolType" [("name", "HolName"), ("arguments", "HolTypeList")]
  , termCtor "TyNil" "HolTypeList" []
  , termCtor "TyCons" "HolTypeList" [("head", "HolType"), ("tail", "HolTypeList")]
  , termCtor "TmVar" "HolTerm" [("name", "HolName"), ("type", "HolType")]
  , termCtor "TmConst" "HolTerm" [("name", "HolName"), ("type", "HolType")]
  , termCtor "TmApp" "HolTerm" [("function", "HolTerm"), ("argument", "HolTerm")]
  , termCtor "TmAbs" "HolTerm" [("variable", "HolTerm"), ("body", "HolTerm")]
  , termCtor "HypsNil" "HolHyps" []
  , termCtor "HypsCons" "HolHyps" [("head", "HolTerm"), ("tail", "HolHyps")]
  , termCtor "TermMapNil" "HolTermMap" []
  , termCtor "TermMapCons" "HolTermMap"
      [("redex", "HolTerm"), ("residue", "HolTerm"), ("tail", "HolTermMap")]
  , termCtor "TypeMapNil" "HolTypeMap" []
  , termCtor "TypeMapCons" "HolTypeMap"
      [("redex", "HolType"), ("residue", "HolType"), ("tail", "HolTypeMap")]
  , termCtor "Subst" "HolSubst" [("types", "HolTypeMap"), ("terms", "HolTermMap")]
  , termCtor "Seq" "HolThm" [("hypotheses", "HolHyps"), ("conclusion", "HolTerm")]
  , termCtor "ResultThm" "HolResult" [("theorem", "HolThm")]
  , termCtor "HLCheck" "HolJudgment" [("proof", "HolProof")]
  , termCtor "HLOk" "HolJudgment" [("theorem", "HolThm")]
  , termCtor "H4Check" "HolJudgment" [("proof", "HolProof")]
  , termCtor "H4Ok" "HolJudgment" [("theorem", "HolThm")] ]

private def holLightProofTerms : List GrammarRule :=
  [ termCtor "HL_REFL" "HolProof" [("term", "HolTerm")]
  , termCtor "HL_TRANS" "HolProof"
      [("left", "HolThm"), ("right", "HolThm"), ("outputHypotheses", "HolHyps")]
  , termCtor "HL_MK_COMB" "HolProof"
      [("functionEquality", "HolThm"), ("argumentEquality", "HolThm"),
       ("leftApplication", "HolTerm"), ("rightApplication", "HolTerm"),
       ("outputHypotheses", "HolHyps")]
  , termCtor "HL_ABS" "HolProof"
      [("variable", "HolTerm"), ("equality", "HolThm"),
       ("leftAbstraction", "HolTerm"), ("rightAbstraction", "HolTerm")]
  , termCtor "HL_BETA" "HolProof" [("redex", "HolTerm"), ("result", "HolTerm")]
  , termCtor "HL_ASSUME" "HolProof" [("proposition", "HolTerm")]
  , termCtor "HL_EQ_MP" "HolProof"
      [("equality", "HolThm"), ("premise", "HolThm"), ("outputHypotheses", "HolHyps")]
  , termCtor "HL_DEDUCT_ANTISYM" "HolProof"
      [("left", "HolThm"), ("right", "HolThm"), ("leftRemainder", "HolHyps"),
       ("rightRemainder", "HolHyps"), ("outputHypotheses", "HolHyps")]
  , termCtor "HL_INST" "HolProof"
      [("substitution", "HolSubst"), ("input", "HolThm"), ("output", "HolResult")]
  , termCtor "HL_INST_TYPE" "HolProof"
      [("substitution", "HolSubst"), ("input", "HolThm"), ("output", "HolResult")]
  , termCtor "HL_AXIOM" "HolProof" [("theorem", "HolResult")]
  , termCtor "HL_DEFINITION" "HolProof"
      [("name", "HolName"), ("type", "HolType"), ("right", "HolTerm")]
  , termCtor "HL_TYPE_DEFINITION" "HolProof"
      [("parent", "HolThm"), ("name", "HolName"), ("type", "HolType"),
       ("term", "HolTerm"), ("output", "HolResult")] ]

private def hol4ProofTerms : List GrammarRule :=
  [ termCtor "H4_ASSUME" "HolProof" [("proposition", "HolTerm")]
  , termCtor "H4_REFL" "HolProof" [("term", "HolTerm")]
  , termCtor "H4_BETA_CONV" "HolProof" [("redex", "HolTerm"), ("result", "HolTerm")]
  , termCtor "H4_ABS" "HolProof"
      [("variable", "HolTerm"), ("equality", "HolThm"),
       ("leftAbstraction", "HolTerm"), ("rightAbstraction", "HolTerm")]
  , termCtor "H4_DISCH" "HolProof"
      [("proposition", "HolTerm"), ("input", "HolThm"),
       ("outputHypotheses", "HolHyps")]
  , termCtor "H4_MP" "HolProof"
      [("implication", "HolThm"), ("argument", "HolThm"),
       ("outputHypotheses", "HolHyps")]
  , termCtor "H4_SUBST" "HolProof"
      [("substitution", "HolSubst"), ("template", "HolTerm"),
       ("input", "HolThm"), ("output", "HolResult")]
  , termCtor "H4_INST_TYPE" "HolProof"
      [("substitution", "HolSubst"), ("input", "HolThm"), ("output", "HolResult")] ]

private def sideRelations : LogicProgram :=
  [ rel "termHasType" ["HolTerm", "HolType"]
  , rel "isBool" ["HolTerm"]
  , rel "alphaEq" ["HolTerm", "HolTerm"]
  , rel "hypUnion" ["HolHyps", "HolHyps", "HolHyps"]
  , rel "hypRemove" ["HolTerm", "HolHyps", "HolHyps"]
  , rel "appResult" ["HolTerm", "HolTerm", "HolTerm"]
  , rel "absResult" ["HolTerm", "HolTerm", "HolTerm"]
  , rel "notFreeIn" ["HolTerm", "HolHyps"]
  , rel "betaResult" ["HolTerm", "HolTerm"]
  , rel "substResult" ["HolSubst", "HolThm", "HolThm"]
  , rel "axiomAllowed" ["HolThm"]
  , rel "definitionAllowed" ["HolName", "HolType", "HolTerm"]
  , rel "constResult" ["HolName", "HolType", "HolTerm"]
  , rel "typeDefinitionResult" ["HolThm", "HolName", "HolType", "HolTerm", "HolThm"] ]

private def P := pvar "P"
private def Q := pvar "Q"
private def Q2 := pvar "Q2"
private def R := pvar "R"
private def F := pvar "F"
private def G := pvar "G"
private def X := pvar "X"
private def Y := pvar "Y"
private def V := pvar "V"
private def T := pvar "T"
private def T2 := pvar "T2"
private def TI := pvar "TI"
private def TF := pvar "TF"
private def TX := pvar "TX"
private def TO := pvar "TO"
private def H1 := pvar "H1"
private def H2 := pvar "H2"
private def HO := pvar "HO"
private def HR1 := pvar "HR1"
private def HR2 := pvar "HR2"
private def FX := pvar "FX"
private def GY := pvar "GY"
private def VP := pvar "VP"
private def VQ := pvar "VQ"
private def S := pvar "S"
private def Input := pvar "Input"
private def Output := pvar "Output"
private def N := pvar "N"
private def C := pvar "C"

private def holLightRewrites : List RewriteRule :=
  [ rw "HL_REFL" [query "termHasType" [P, T]]
      (check "HLCheck" (app "HL_REFL" [P]))
      (ok "HLOk" (seq hypsNil (eqTerm T P P)))
  , rw "HL_TRANS"
      [query "alphaEq" [Q, Q2], query "hypUnion" [H1, H2, HO]]
      (check "HLCheck" (app "HL_TRANS"
        [seq H1 (eqTerm T P Q), seq H2 (eqTerm T2 Q2 R), HO]))
      (ok "HLOk" (seq HO (eqTerm T P R)))
  , rw "HL_MK_COMB"
      [query "appResult" [F, X, FX], query "appResult" [G, Y, GY],
       query "hypUnion" [H1, H2, HO], query "termHasType" [FX, TO]]
      (check "HLCheck" (app "HL_MK_COMB"
        [seq H1 (eqTerm TF F G), seq H2 (eqTerm TX X Y), FX, GY, HO]))
      (ok "HLOk" (seq HO (eqTerm TO FX GY)))
  , rw "HL_ABS"
      [query "absResult" [V, P, VP], query "absResult" [V, Q, VQ],
       query "notFreeIn" [V, H1], query "termHasType" [VP, TO]]
      (check "HLCheck" (app "HL_ABS" [V, seq H1 (eqTerm TI P Q), VP, VQ]))
      (ok "HLOk" (seq H1 (eqTerm TO VP VQ)))
  , rw "HL_BETA" [query "betaResult" [P, Q], query "termHasType" [Q, T]]
      (check "HLCheck" (app "HL_BETA" [P, Q]))
      (ok "HLOk" (seq hypsNil (eqTerm T P Q)))
  , rw "HL_ASSUME" [query "isBool" [P]]
      (check "HLCheck" (app "HL_ASSUME" [P]))
      (ok "HLOk" (seq (hypsCons P hypsNil) P))
  , rw "HL_EQ_MP"
      [query "alphaEq" [P, Q2], query "hypUnion" [H1, H2, HO]]
      (check "HLCheck" (app "HL_EQ_MP"
        [seq H1 (eqTerm boolTy P Q), seq H2 Q2, HO]))
      (ok "HLOk" (seq HO Q))
  , rw "HL_DEDUCT_ANTISYM"
      [query "hypRemove" [Q, H1, HR1], query "hypRemove" [P, H2, HR2],
       query "hypUnion" [HR1, HR2, HO], query "termHasType" [P, T],
       query "termHasType" [Q, T]]
      (check "HLCheck" (app "HL_DEDUCT_ANTISYM"
        [seq H1 P, seq H2 Q, HR1, HR2, HO]))
      (ok "HLOk" (seq HO (eqTerm T P Q)))
  , rw "HL_INST" [query "substResult" [S, Input, Output]]
      (check "HLCheck" (app "HL_INST" [S, Input, app "ResultThm" [Output]]))
      (ok "HLOk" Output)
  , rw "HL_INST_TYPE" [query "substResult" [S, Input, Output]]
      (check "HLCheck" (app "HL_INST_TYPE" [S, Input, app "ResultThm" [Output]]))
      (ok "HLOk" Output)
  , rw "HL_AXIOM" [query "axiomAllowed" [Output]]
      (check "HLCheck" (app "HL_AXIOM" [app "ResultThm" [Output]]))
      (ok "HLOk" Output)
  , rw "HL_DEFINITION"
      [query "definitionAllowed" [N, T, P], query "constResult" [N, T, C]]
      (check "HLCheck" (app "HL_DEFINITION" [N, T, P]))
      (ok "HLOk" (seq hypsNil (eqTerm T C P)))
  , rw "HL_TYPE_DEFINITION"
      [query "typeDefinitionResult" [Input, N, T, P, Output]]
      (check "HLCheck"
        (app "HL_TYPE_DEFINITION" [Input, N, T, P, app "ResultThm" [Output]]))
      (ok "HLOk" Output) ]

private def hol4Rewrites : List RewriteRule :=
  [ rw "H4_ASSUME" [query "isBool" [P]]
      (check "H4Check" (app "H4_ASSUME" [P]))
      (ok "H4Ok" (seq (hypsCons P hypsNil) P))
  , rw "H4_REFL" [query "termHasType" [P, T]]
      (check "H4Check" (app "H4_REFL" [P]))
      (ok "H4Ok" (seq hypsNil (eqTerm T P P)))
  , rw "H4_BETA_CONV" [query "betaResult" [P, Q], query "termHasType" [Q, T]]
      (check "H4Check" (app "H4_BETA_CONV" [P, Q]))
      (ok "H4Ok" (seq hypsNil (eqTerm T P Q)))
  , rw "H4_ABS"
      [query "absResult" [V, P, VP], query "absResult" [V, Q, VQ],
       query "notFreeIn" [V, H1], query "termHasType" [VP, TO]]
      (check "H4Check" (app "H4_ABS" [V, seq H1 (eqTerm TI P Q), VP, VQ]))
      (ok "H4Ok" (seq H1 (eqTerm TO VP VQ)))
  , rw "H4_DISCH" [query "hypRemove" [P, H1, HO], query "isBool" [P]]
      (check "H4Check" (app "H4_DISCH" [P, seq H1 Q, HO]))
      (ok "H4Ok" (seq HO (impTerm P Q)))
  , rw "H4_MP" [query "hypUnion" [H1, H2, HO]]
      (check "H4Check" (app "H4_MP" [seq H1 (impTerm P Q), seq H2 P, HO]))
      (ok "H4Ok" (seq HO Q))
  , rw "H4_SUBST" [query "substResult" [S, Input, Output]]
      (check "H4Check" (app "H4_SUBST" [S, R, Input, app "ResultThm" [Output]]))
      (ok "H4Ok" Output)
  , rw "H4_INST_TYPE" [query "substResult" [S, Input, Output]]
      (check "H4Check" (app "H4_INST_TYPE" [S, Input, app "ResultThm" [Output]]))
      (ok "H4Ok" Output) ]

def holLightSourceKernel : LanguageDef :=
  { name := "HOLLightSourceKernel"
    types := commonTypes
    terms := commonTerms ++ holLightProofTerms
    equations := []
    rewrites := holLightRewrites }

def hol4SourceKernel : LanguageDef :=
  { name := "HOL4SourceKernel"
    types := commonTypes
    terms := commonTerms ++ hol4ProofTerms
    equations := []
    rewrites := hol4Rewrites }

def holLightSourceLogic : AdmittedProgram holLightSourceKernel :=
  ⟨sideRelations, by decide⟩

def hol4SourceLogic : AdmittedProgram hol4SourceKernel :=
  ⟨sideRelations, by decide⟩

def holLightSourceProfile : EvidenceProfile :=
  { checkHead := "HLCheck"
    okHead := "HLOk"
    proofCategory := "HolProof"
    evidenceCategory := "HolThm"
    derivedHead := "$hol.thm"
    relationHeadPrefix := "$hol.rel." }

def hol4SourceProfile : EvidenceProfile :=
  { checkHead := "H4Check"
    okHead := "H4Ok"
    proofCategory := "HolProof"
    evidenceCategory := "HolThm"
    derivedHead := "$hol.thm"
    relationHeadPrefix := "$hol.rel." }

def holLightSourceDefinition? : Option CalculusLanguageDef :=
  rawDefinition? holLightSourceProfile holLightSourceKernel
    holLightSourceLogic.1

def hol4SourceDefinition? : Option CalculusLanguageDef :=
  rawDefinition? hol4SourceProfile hol4SourceKernel hol4SourceLogic.1

#guard LanguageDef.validate holLightSourceKernel == []
#guard LanguageDef.validate hol4SourceKernel == []
#guard holLightSourceDefinition?.isSome
#guard hol4SourceDefinition?.isSome
#guard holLightSourceDefinition?.map (·.rules.length) == some 13
#guard hol4SourceDefinition?.map (·.rules.length) == some 8

end Mettapedia.GSLT.LanguageDef.HOLSourceKernel
