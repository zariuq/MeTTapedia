import Mettapedia.GSLT.Parsing.PlainBnfDenotationValueCodec
import Algorithms.MeTTa.Simple.Parser

/-!
# Independent whole-result denotation fixtures

These fixtures start at the structured-document boundary, not at raw BNF
bytes. Expected outputs come from the independent typed/physical denotation
fold. The native gate must run the authored admission and denotation programs;
it must not use this module as an alternative production evaluator.

The existing `decodeCandidate_physicalDenote` theorem connects every expected
value to typed denotation. Finite native agreement is regression evidence,
not an all-input source-execution correspondence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Tools.ExportPlainBnfDenotationCases

open Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
open Mettapedia.GSLT.Parsing.PlainBnfStructuredValueCodec
open Mettapedia.GSLT.Parsing.PlainBnfDenotationValueCodec
open Mettapedia.GSLT.LanguageDef.CettaWire

structure Specimen where
  name : String
  document : Document
  authority : GrammarAuthority

private def span (start stop : Nat) : SourceSpan := ⟨start, stop⟩

private def alternative (elements : List Element) (start stop : Nat) : Alternative :=
  ⟨elements, span start stop⟩

private def rule (name : String) (alternatives : List Alternative)
    (start stop : Nat) : Entry :=
  .rule name ⟨alternatives, span start stop⟩ (span start stop)

private def authority : GrammarAuthority := ⟨"start", []⟩

def literalSpecimen : Specimen :=
  { name := "literal"
    document := ⟨[rule "start"
      [alternative [.literal "a" (span 14 17)] 14 17] 0 17], span 0 18⟩
    authority }

def epsilonSpecimen : Specimen :=
  { name := "two-distinct-epsilon-occurrences"
    document := ⟨[rule "start"
      [alternative [] 14 14,
       alternative [.literal "" (span 17 19)] 17 19] 0 19], span 0 20⟩
    authority }

def recursiveSpecimen : Specimen :=
  { name := "recursive-ordered-duplicates-and-escaping"
    document :=
      ⟨[.comment "retained ; comment" (span 0 21), .blank (span 21 22),
        rule "start"
          [alternative
            [.reference "leaf" (span 37 43), .literal "" (span 44 46),
             .literal "λ\n\"\\;" (span 47 63), .reference "leaf" (span 64 70)] 37 70,
           alternative [.reference "leaf" (span 73 79)] 73 79,
           alternative [.reference "leaf" (span 82 88)] 82 88] 22 88,
        rule "leaf"
          [alternative [.literal "a" (span 100 103)] 100 103,
           alternative [.reference "leaf" (span 106 112)] 106 112] 89 112],
       span 0 113⟩
    authority }

def lexicalSpecimen : Specimen :=
  { name := "typed-points-and-except-lexical-context"
    document := ⟨[rule "start"
      [alternative
        [.reference "digit" (span 14 21), .reference "other" (span 22 29),
         .reference "start" (span 30 37)] 14 37,
       alternative [] 40 40] 0 40], span 0 41⟩
    authority :=
      { startName := "start"
        lexicalDeclarations :=
          [⟨"digit", "Digits", .points [48, 55, 57], "digit-token", ⟨"fixture", 2⟩⟩,
           ⟨"other", "Other", .except [0, 10, 34, 92], "other-token", ⟨"fixture", 7⟩⟩] } }

/-- Vary the number of alternative and reference occurrences independently
of the implementation's suffix-building loops. -/
def occurrenceSpecimen (count : Nat) : Specimen :=
  { name := s!"occurrences-{count}"
    document :=
      ⟨[rule "start"
          ((List.range (count + 1)).map fun index =>
            alternative
              (List.replicate index (.reference "leaf" (span 20 26)) ++
                [.literal "a" (span 27 30)]) 20 30) 0 40,
        rule "leaf" [alternative [.literal "b" (span 53 56)] 53 56] 41 56],
       span 0 57⟩
    authority }

def specimens : List Specimen :=
  [literalSpecimen, epsilonSpecimen, recursiveSpecimen, lexicalSpecimen] ++
    ([1, 2, 4, 8].map occurrenceSpecimen)

def expected (specimen : Specimen) : Term :=
  physicalDenote specimen.document specimen.authority

theorem expected_has_typed_meaning (specimen : Specimen) :
    decodeCandidate (expected specimen) =
      some (denote specimen.document specimen.authority) :=
  decodeCandidate_physicalDenote specimen.document specimen.authority

private def prelude : String :=
  "(= (lean-bnf-test:denote (bnf-v1:grammar-input $document $authority))\n" ++
  "  (case (bnf:admit-grammar-input (bnf-v1:grammar-input $document $authority))\n" ++
  "    (((BNF:GrammarInputAdmitted $input)\n" ++
  "       (let $validation (bnf:validate-input $input)\n" ++
  "         (case $validation\n" ++
  "           (((BNFSemanticValidationAcceptedV1 $start $definitions $lexicals $analysis)\n" ++
  "              (bnf-internal:denote-document-candidate $document $validation))\n" ++
  "            ($other (LeanBnfAdmissionFailedV1 $other))))))\n" ++
  "     ($other (LeanBnfShapeAdmissionFailedV1 $other)))))\n"

mutual
  /-- Deliberately reproduce the rejected nullary-to-symbol codec mutation.
  This is only fault-injection input for the differential gate. -/
  def eraseEmptyConstructors : Term → Term
    | .application head [] =>
        if head ∈ ["bnf-v1:text-nil", "bnf-v1:elements-nil",
            "bnf-v1:alternatives-nil", "bnf-v1:entries-nil",
            "bnf-v1:scalars-nil", "bnf-v1:lexical-declarations-nil"] then
          .symbol head
        else .application head []
    | .application head arguments =>
        .application head (eraseEmptyConstructorArguments arguments)
    | term => term

  def eraseEmptyConstructorArguments : List Term → List Term
    | [] => []
    | term :: terms => eraseEmptyConstructors term :: eraseEmptyConstructorArguments terms
end

private def caseVariable (index : Nat) : String := s!"$case{index}"

/-- Expected strings are deliberately not embedded in executable PeTTa
source. They are compared as output data, independently of PeTTa's document
splitter and its distinct quoted-string surface restrictions. -/
def renderProgram (mutate : Bool) : String :=
  let result := "(PlainBnfDenotationResultsV1" ++
    String.join ((List.range specimens.length).map fun index =>
      " " ++ caseVariable index) ++ ")"
  let query := specimens.zipIdx.foldr (fun (specimen, index) body =>
    let input := encodeGrammarInput specimen.document specimen.authority
    let input := if mutate then eraseEmptyConstructors input else input
    "(let " ++ caseVariable index ++ " (lean-bnf-test:denote " ++
      input.render ++ ") " ++ body ++ ")") result
  prelude ++ "!" ++ query ++ "\n"

def program : String :=
  renderProgram false

def mutatedProgram : String :=
  renderProgram true

def expectedTerm : Term :=
  .application "PlainBnfDenotationResultsV1" (specimens.map expected)

def expectedOutput : String :=
  expectedTerm.render ++ "\n"

mutual
  /-- Source-data observation through the existing S-expression carrier.
  No Pattern lowering (and hence no nullary collapse) participates. -/
  def sourceData : Term → Algorithms.MeTTa.Simple.Parser.SExpr
    | .symbol name => .atom name
    | .string value => .atom (reprStr value)
    | .natural value => .atom (toString value)
    | .application head arguments => .list (.atom head :: sourceDataArguments arguments)

  def sourceDataArguments : List Term → List Algorithms.MeTTa.Simple.Parser.SExpr
    | [] => []
    | term :: terms => sourceData term :: sourceDataArguments terms
end

open Algorithms.MeTTa.Simple.Parser in
/-- Require the public structured refusal, not a changed answer, runtime
fault, or diagnostic prose matched to the current implementation. -/
def isShapeRefusal : SExpr → Bool
  | .list [.atom "LeanBnfShapeAdmissionFailedV1",
      .list [.atom "BNF:GrammarInputRejected", .atom "type_mismatch", .atom message]] =>
      message.startsWith "\"" && message.endsWith "\""
  | _ => false

open Algorithms.MeTTa.Simple.Parser in
def resultsMatch (mutated : Bool) (expected actual : List SExpr) : Bool :=
  actual.length == expected.length &&
    if mutated then actual.all isShapeRefusal else actual == expected

private def refusalSpecimen : Algorithms.MeTTa.Simple.Parser.SExpr :=
  .list [.atom "LeanBnfShapeAdmissionFailedV1",
    .list [.atom "BNF:GrammarInputRejected", .atom "type_mismatch", .atom "\"detail\""]]

-- Qualify the gate itself against missing, duplicate, wrong, and fault results.
#guard resultsMatch false [.atom "expected"] [.atom "expected"]
#guard !resultsMatch false [.atom "expected"] []
#guard !resultsMatch false [.atom "expected"] [.atom "expected", .atom "expected"]
#guard !resultsMatch false [.atom "expected"] [.atom "wrong"]
#guard resultsMatch true [.atom "expected"] [refusalSpecimen]
#guard !resultsMatch true [.atom "expected"] [.atom "wrong"]
#guard !resultsMatch true [.atom "expected"]
  [.list [.atom "LeanBnfShapeAdmissionFailedV1",
    .list [.atom "BNF:ReadFault", .atom "type_mismatch", .atom "\"detail\""]]]
#guard !resultsMatch true [.atom "expected"] []
#guard !resultsMatch true [.atom "expected"] [refusalSpecimen, refusalSpecimen]

def checkOutput (mutated : Bool) (path : String) : IO UInt32 := do
  let contents ← IO.FS.readFile path
  -- The library load emits one Boolean acknowledgement before the query.
  -- Match the whole output stream, so extra results cannot be ignored.
  match Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
      MeTTailCore.MeTTaSyntax.he ("(" ++ contents ++ ")") with
  | .error error =>
      IO.eprintln s!"native denotation output is not one structured result: {error.render}"
      return 1
  | .ok (.list [.atom "true", .list (.atom "PlainBnfDenotationResultsV1" :: actual)]) =>
      let expected := specimens.map fun specimen => sourceData (expected specimen)
      if actual.length != expected.length then
        IO.eprintln "native denotation changed the fixture result count"
        return 1
      let mismatches := (actual.zip expected).zipIdx.filter fun ((got, wanted), _) =>
        got != wanted
      if mutated then
        if !resultsMatch true expected actual then
          IO.eprintln "the nullary-constructor mutation did not produce explicit shape refusals"
          return 1
        IO.println s!"(PlainBnfLeanDenotationNullaryMutationRefusedV1Summary {specimens.length} {actual.length} 0)"
        return 0
      if !resultsMatch false expected actual then
        for (_, index) in mismatches do
          match specimens[index]? with
          | some specimen => IO.eprintln s!"whole-result mismatch: {specimen.name}"
          | none => IO.eprintln s!"whole-result mismatch at unexpected index {index}"
        return 1
      IO.println s!"(PlainBnfLeanDenotationNativeV1Summary {specimens.length} {specimens.length} 0)"
      return 0
  | .ok _ =>
      IO.eprintln "native denotation output has the wrong result wrapper"
      return 1

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["--check", path] => checkOutput false path
  | ["--check-mutant", path] => checkOutput true path
  | [programPath, expectedPath, mutatedPath] =>
      IO.FS.writeFile programPath program
      IO.FS.writeFile expectedPath expectedOutput
      IO.FS.writeFile mutatedPath mutatedProgram
      IO.println s!"(PlainBnfLeanDenotationFixturesV1 {specimens.length})"
      return 0
  | _ =>
      IO.eprintln "usage: ExportPlainBnfDenotationCases PROGRAM_OUT EXPECTED_OUTPUT_OUT MUTATED_PROGRAM_OUT"
      return 2

#print axioms expected_has_typed_meaning

end Mettapedia.GSLT.Tools.ExportPlainBnfDenotationCases

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.Tools.ExportPlainBnfDenotationCases.run arguments
