import Mettapedia.Languages.SUMO.Native.NIKAuthority
import Mettapedia.Languages.SUMO.Native.SourceElaboration
import Mettapedia.Languages.SUMO.Native.SourceTheory

/-!
# Executable canaries for direct SUO-KIF elaboration

These tests execute through the lexer, parser, named logical classifier, and
intrinsic scope resolver.  They are kept out of the library module so Lean's
kernel does not build enormous reduction proofs for source strings.
-/

namespace Mettapedia.Languages.SUMO.Native.SourceElaborationCanary

open Mettapedia.Languages.SUMO.Native
open Mettapedia.Languages.SUMO.Native.SourceElaboration

private def emptySignature : SourceSignature :=
  SourceSignature.empty

private def formulaSignature : SourceSignature :=
  { formulaArguments := [("believes", 2)] }

private def selfApplication : Sentence String String :=
  .atom (.constant "instance")
    (.term (.constant "instance")
      (.term (.constant "BinaryPredicate") .nil))

private def variableRelation : Sentence String String :=
  .allObject (.atom (.var 0) (.singleton (.constant "Human")))

private def formulaArgument : Sentence String String :=
  .atom (.constant "believes")
    (.term (.constant "Mary")
      (.term
        (.quote
          (.atom (.constant "likes")
            (.term (.constant "John")
              (.term (.constant "Sue") .nil))))
        .nil))

private def mixedRowQuantifier : Sentence String String :=
  .allRow
    (.allObject
      (.equal
        (.application (.constant "ListFn")
          (.row 0 (.term (.var 0) .nil)))
        (.application (.constant "ListFn")
          (.row 0 (.term (.var 0) .nil)))))

private def kappaFormula : Sentence String String :=
  .equal
    (.kappa
      (.atom (.constant "instance")
        (.term (.var 0) (.term (.constant "Human") .nil))))
    (.constant "HumanClass")

private def assertedFormulaVariable : Sentence String String :=
  .allObject (.not (.asserted (.var 0)))

private def implicationIdentityCertificate : Certificate String String 0 0 :=
  .implicationIntroduction selfApplication (.hypothesis 0)

/-- A complete source-to-native-NIK receipt.  Source elaboration and proof
checking are independent computations: the former resolves SUO-KIF syntax and
scope, while the latter reconstructs a conclusion solely from native rules. -/
private def sourceToNativeNIKReceipt : Bool :=
  match elaborateSource emptySignature
      "(=> (instance instance BinaryPredicate) (instance instance BinaryPredicate))" with
  | .ok sourceFormula =>
      NIKAuthority.checker.check sourceFormula implicationIdentityCertificate
  | .error _ => false

private def sourceMortalEntailment : Option NIKAuthority.EntailmentClaim :=
  match elaborateSource emptySignature
      "(=> (instance instance BinaryPredicate) (mortal Socrates))",
      elaborateSource emptySignature "(instance instance BinaryPredicate)",
      elaborateSource emptySignature "(mortal Socrates)" with
  | .ok rule, .ok premise, .ok conclusion =>
      some { assumptions := [rule, premise], conclusion := conclusion }
  | _, _, _ => none

private def sourceContextualNIKReceipt : Bool :=
  match sourceMortalEntailment with
  | some claim =>
      NIKAuthority.entailmentChecker.check claim NIKAuthority.mortalCertificate
  | none => false

private def reversedSourceModusPonensRejected : Bool :=
  match sourceMortalEntailment with
  | some claim =>
      !NIKAuthority.entailmentChecker.check claim
        (.implicationElimination (.hypothesis 1) (.hypothesis 0))
  | none => false

private def assembledSourceTheoryNIKReceipt : Bool :=
  let theory := SourceTheory.assemble
    [{ sourceId := "modus-ponens-source"
       text :=
        "(=> (instance instance BinaryPredicate) (mortal Socrates))\n\
         (instance instance BinaryPredicate)" }]
  match elaborateSource emptySignature "(mortal Socrates)" with
  | .ok conclusion =>
      theory.clean && theory.entries.length == 2 &&
        NIKAuthority.entailmentChecker.check
          (theory.entailmentClaim conclusion) NIKAuthority.mortalCertificate
  | .error _ => false

private def checks : List (String × Bool) :=
  [ ("self-application",
      decide (elaborateSource emptySignature
        "(instance instance BinaryPredicate)" = .ok selfApplication)),
    ("variable relation operator",
      decide (elaborateSource emptySignature
        "(forall (?REL) (?REL Human))" = .ok variableRelation)),
    ("formula-valued argument",
      decide (elaborateSource formulaSignature
        "(believes Mary (likes John Sue))" = .ok formulaArgument)),
    ("mixed row and ordinary quantifier",
      decide (elaborateSource emptySignature
        "(forall (@ROW ?ITEM) (equal (ListFn @ROW ?ITEM) (ListFn @ROW ?ITEM)))" =
          .ok mixedRowQuantifier)),
    ("KappaFn binder",
      decide (elaborateSource
        { formulaArguments := [("KappaFn", 2)] }
        "(equal (KappaFn ?X (instance ?X Human)) HumanClass)" =
          .ok kappaFormula)),
    ("formula variable assertion",
      decide (elaborateSource emptySignature "(not ?FORMULA)" =
        .ok assertedFormulaVariable)),
    ("source to native NIK receipt", sourceToNativeNIKReceipt),
    ("source contextual NIK modus ponens", sourceContextualNIKReceipt),
    ("reject reversed source modus ponens", reversedSourceModusPonensRejected),
    ("assembled source theory to contextual NIK", assembledSourceTheoryNIKReceipt),
    ("reject malformed implication",
      match elaborateSource emptySignature "(=> (P) (Q) (R))" with
      | .error (.elaboration
          { kind := .wrongLogicalArity "=>" 2 3, .. }) => true
      | _ => false),
    ("reject row operator",
      match elaborateSource emptySignature "(forall (@ROW) (@ROW Human))" with
      | .error (.elaboration
          { kind := .rowVariableInOperatorPosition "@ROW", .. }) => true
      | _ => false) ]

def run : IO UInt32 := do
  let mut failed := 0
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS: {name}"
    else
      failed := failed + 1
      IO.eprintln s!"FAIL: {name}"
  IO.println s!"source elaboration canaries: {checks.length - failed}/{checks.length}"
  pure (if failed = 0 then 0 else 1)

end Mettapedia.Languages.SUMO.Native.SourceElaborationCanary

def main : IO UInt32 :=
  Mettapedia.Languages.SUMO.Native.SourceElaborationCanary.run
