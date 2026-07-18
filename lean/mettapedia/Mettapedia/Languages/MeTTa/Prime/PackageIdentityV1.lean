import Mettapedia.Languages.MeTTa.Prime.MinimalCheckingPackage
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
import MeTTailCore.Crypto.SHA256

/-!
# Prime package identity V1 calibration

This is an independent Lean construction of the exact package serialized by
`prime_package_identity_v1.metta`.  The MeTTa path uses CeTTa's generic `repr`
and native SHA-256; this path uses an explicit recursive renderer and the Lean
SHA-256 implementation.  The gate compares their emitted bytes and digest.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.PackageAuthority

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

structure PackageIdentityV1 where
  format : String
  dialect : String
  semanticVersion : String
  digest : String
deriving Repr, DecidableEq

structure PrimeRulePackageV1 where
  format : String
  dialect : String
  semanticVersion : String
  rules : List RuleSchema
  conversions : List RuleSchema
deriving Repr

private def app (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def pvar (name : String) : Pattern := .fvar name

private def schema (id : String) (metavariables : List (String × Nat))
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ⟨id⟩, metavariables, premises, conclusion }

private def ppiA : Pattern := app "ppi.A"
private def ppiB : Pattern := app "ppi.B"
private def ppiImp (left right : Pattern) : Pattern :=
  app "ppi.Imp" [left, right]
private def ppiProves (formula : Pattern) : Pattern :=
  app "ppi.Proves" [formula]
private def ppiConvertible (left right : Pattern) : Pattern :=
  app "ppi.Convertible" [left, right]

private def ruleA : RuleSchema :=
  schema "ppi.ax-a" [] [] (ppiProves ppiA)

private def ruleImp : RuleSchema :=
  schema "ppi.ax-imp" [] [] (ppiProves (ppiImp ppiA ppiB))

private def ruleMp : RuleSchema :=
  schema "ppi.mp" [("antecedent", 0), ("consequent", 0)]
    [ppiProves (pvar "antecedent"),
     ppiProves (ppiImp (pvar "antecedent") (pvar "consequent"))]
    (ppiProves (pvar "consequent"))

private def conversionRefl : RuleSchema :=
  schema "ppi.conv-refl" [("term", 0)] []
    (ppiConvertible (pvar "term") (pvar "term"))

def package : PrimeRulePackageV1 :=
  { format := "prime-rule-package-v1"
    dialect := "prime"
    semanticVersion := "0.5"
    rules := [ruleA, ruleImp, ruleMp]
    conversions := [conversionRefl] }

def PrimeRulePackageV1.canonicalBytes (package : PrimeRulePackageV1) : String :=
  s!"(PrimeRulePackageV1 {quote package.format} {quote package.dialect} " ++
    s!"{quote package.semanticVersion} {renderList renderRule package.rules} " ++
    s!"{renderList renderRule package.conversions})"

def PrimeRulePackageV1.identity (package : PrimeRulePackageV1) :
    PackageIdentityV1 :=
  { format := package.format
    dialect := package.dialect
    semanticVersion := package.semanticVersion
    digest := MeTTailCore.Crypto.SHA256.sha256Hex package.canonicalBytes }

private def dataConstructor (label : String) (arity : Nat) : GrammarRule :=
  { label
    category := "PrimeMinimalData"
    params := (List.range arity).map fun index =>
      .simple ("argument" ++ toString index) (.base "PrimeMinimalData")
    syntaxPattern := [] }

private def cacheLanguage : LanguageDef :=
  { name := "PrimeMinimalCheckingCache"
    types := [TypeDecl.plain "PrimeMinimalData"]
    terms := [dataConstructor "ppi.A" 0,
      dataConstructor "ppi.Imp" 2, dataConstructor "ppi.B" 0]
    equations := []
    rewrites := [] }

def cache : Presentation :=
  { language := cacheLanguage
    judgments := [
      { head := "ppi.Proves", arity := 1 },
      { head := "ppi.Convertible", arity := 2 }]
    rules := package.rules ++ package.conversions }

def validatePackage (candidate : PrimeRulePackageV1)
    (cached : Presentation) : Bool :=
  candidate.format == "prime-rule-package-v1" &&
    candidate.dialect == "prime" &&
    candidate.semanticVersion == "0.5" &&
    match Mettapedia.Languages.MeTTa.Prime.MinimalCheckingPackage.project
        (candidate.rules ++ candidate.conversions) with
    | .error _ => false
    | .ok projected =>
        renderPresentation projected == renderPresentation cached &&
          cached.isValidV2

private def premiseMutated : PrimeRulePackageV1 :=
  { package with
    rules := [ruleA, ruleImp,
      schema "ppi.mp" [("antecedent", 0), ("consequent", 0)]
        [ppiProves ppiB,
         ppiProves (ppiImp (pvar "antecedent") (pvar "consequent"))]
        (ppiProves (pvar "consequent"))] }

private def swapped : PrimeRulePackageV1 :=
  { package with rules := [ruleImp, ruleA, ruleMp] }

private def conversionMutated : PrimeRulePackageV1 :=
  { package with
    conversions := [schema "ppi.conv-refl" [("term", 0)] []
      (ppiConvertible (pvar "term") ppiA)] }

private def wrongCache : Presentation := { cache with judgments := [] }

def main : IO Unit := do
  unless validatePackage package cache do
    throw <| IO.userError "independently reconstructed package was rejected"
  if validatePackage package wrongCache then
    throw <| IO.userError "cache from another package was accepted"
  if package.canonicalBytes == premiseMutated.canonicalBytes then
    throw <| IO.userError "premise mutation preserved canonical bytes"
  if package.canonicalBytes == swapped.canonicalBytes then
    throw <| IO.userError "rule swap preserved canonical bytes"
  if package.canonicalBytes == conversionMutated.canonicalBytes then
    throw <| IO.userError "conversion mutation preserved canonical bytes"
  if package.identity.digest == premiseMutated.identity.digest then
    throw <| IO.userError "premise mutation preserved digest"
  if package.identity.digest == swapped.identity.digest then
    throw <| IO.userError "rule swap preserved digest"
  if package.identity.digest == conversionMutated.identity.digest then
    throw <| IO.userError "conversion mutation preserved digest"
  IO.println "PRIME_PACKAGE_CANONICAL_BEGIN"
  IO.println package.canonicalBytes
  IO.println "PRIME_PACKAGE_CANONICAL_END"
  IO.println "PRIME_PACKAGE_DIGEST_BEGIN"
  IO.println package.identity.digest
  IO.println "PRIME_PACKAGE_DIGEST_END"
  IO.println "PRIME_PACKAGE_MUTANT_DIGESTS_BEGIN"
  IO.println premiseMutated.identity.digest
  IO.println swapped.identity.digest
  IO.println conversionMutated.identity.digest
  IO.println "PRIME_PACKAGE_MUTANT_DIGESTS_END"
  IO.println "(PrimePackageIdentityLeanSummaryV1 8 8 0)"

end Mettapedia.Languages.MeTTa.Prime.PackageAuthority

def main : IO Unit :=
  Mettapedia.Languages.MeTTa.Prime.PackageAuthority.main
