import Mettapedia.Ethics.FormalEthicsNativeNIK
import Mettapedia.Languages.SUMO.Native.SourceTheory

/-!
# Executable source-to-NIK canaries for Formal Ethics

These checks run the SUO-KIF lexer, parser, signature extraction, domain-guard
elaborator, and native SUMO checker as compiled code.  Keeping source-string
evaluation outside theorem statements avoids constructing enormous kernel
reduction terms; the accepted proof itself remains a kernel-checked theorem in
`FormalEthicsNativeNIK`.
-/

namespace Mettapedia.Ethics.FormalEthicsNativeNIKCanary

open Mettapedia.Ethics.FormalEthicsNativeNIK
open Mettapedia.Languages.SUMO.Native

private def sourceTheory : SourceTheory.Theory :=
  SourceTheory.assemble
    [ { sourceId := "SUMO class inheritance"
        text := inheritanceSource }
    , { sourceId := "Formal Ethics KDT hierarchy"
        text := formalEthicsSource } ]

private def domainSource : String :=
  "(domain instance 1 Entity)\n" ++
  "(domain instance 2 Class)\n" ++
  "(domain subclass 1 Class)\n" ++
  "(domain subclass 2 Class)\n"

private def guardedSourceTheory : SourceTheory.Theory :=
  SourceTheory.assemble
    [ { sourceId := "SUMO core domain declarations"
        text := domainSource }
    , { sourceId := "SUMO class inheritance"
        text := inheritanceSource }
    , { sourceId := "Formal Ethics KDT hierarchy"
        text := formalEthicsSource } ]

private def checks : List (String × Bool) :=
  [ ("source slice has no assembly issue", sourceTheory.clean)
  , ("source slice contains five formulas", sourceTheory.assumptions.length == 5)
  , ("source elaboration exactly matches native assumptions",
      sourceTheory.assumptions == logicalAssumptions)
  , ("native NIK derives KDT as an EthicalTheory",
      NIKAuthority.entailmentChecker.check
        kdtEthicalClaim kdtEthicalCertificate)
  , ("native NIK rejects an unrelated retargeted conclusion",
      !NIKAuthority.entailmentChecker.check
        unrelatedVirtueClaim kdtEthicalCertificate)
  , ("guarded source slice has no assembly issue", guardedSourceTheory.clean)
  , ("guarded source extracts the exact domain restrictions",
      guardedSourceTheory.signature.domainRestrictions ==
        instanceRestrictions ++ subclassRestrictions)
  , ("guarded source elaboration exactly matches native assumptions",
      guardedSourceTheory.assumptions.drop 4 == guardedAssumptions)
  , ("signature inference contributes the exact eight domain facts",
      SignatureInference.domainConsequences
        formalEthicsSignature guardedAssumptions ==
          formalEthicsDomainConsequences)
  , ("signature-aware NIK derives the fully guarded consequence",
      SignatureInference.checker.check guardedKdtEthicalClaim
        guardedKdtEthicalCertificate)
  , ("signature-aware NIK rejects an unrelated guarded conclusion",
      !SignatureInference.checker.check guardedUnrelatedVirtueClaim
        guardedKdtEthicalCertificate) ]

def run : IO UInt32 := do
  let mut failed := 0
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS: {name}"
    else
      failed := failed + 1
      IO.eprintln s!"FAIL: {name}"
  unless sourceTheory.assumptions == logicalAssumptions do
    IO.eprintln s!"source assumptions: {repr sourceTheory.assumptions}"
    IO.eprintln s!"native assumptions: {repr logicalAssumptions}"
  unless guardedSourceTheory.assumptions.drop 4 == guardedAssumptions do
    IO.eprintln s!"guarded source assumptions: {repr (guardedSourceTheory.assumptions.drop 4)}"
    IO.eprintln s!"guarded native assumptions: {repr guardedAssumptions}"
  IO.println s!"Formal Ethics native NIK canaries: {checks.length - failed}/{checks.length}"
  pure (if failed = 0 then 0 else 1)

end Mettapedia.Ethics.FormalEthicsNativeNIKCanary

def main : IO UInt32 :=
  Mettapedia.Ethics.FormalEthicsNativeNIKCanary.run
