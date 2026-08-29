import Mettapedia.Languages.Metamath.MM2SourceEventTransformation

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition

def fixtureSource : String :=
  "$( Unit Test 38: Whitespace in valid compressed proof $)\n" ++
  "$c wff |- $.\n" ++
  "$v x $.\n" ++
  "wf $f wff x $.\n" ++
  "ax $a |- x $.\n" ++
  "th $p |- x $= ( ax )   A\n  B   $.\n"

def fixtureRoot : String := "unit.mm"
def fixtureOwner : Atom := stringAtom "compressed-raw-unit"

def fixtureFiles : FileMap := fun name =>
  if name = fixtureRoot then some fixtureSource.toUTF8 else none

/-- The exact provenance-carrying syntax expected from `fixtureSource`. -/
def fixtureStatements : List RawStatement :=
  [.constDecl
      { fileId := fixtureRoot, start := 57, stop := 59 }
      [{ span := { fileId := fixtureRoot, start := 60, stop := 63 },
          name := "wff" },
       { span := { fileId := fixtureRoot, start := 64, stop := 66 },
          name := "|-" }]
      { fileId := fixtureRoot, start := 67, stop := 69 },
   .varDecl
      { fileId := fixtureRoot, start := 70, stop := 72 }
      [{ span := { fileId := fixtureRoot, start := 73, stop := 74 },
          name := "x" }]
      { fileId := fixtureRoot, start := 75, stop := 77 },
   .floating
      { fileId := fixtureRoot, start := 81, stop := 83 }
      { span := { fileId := fixtureRoot, start := 78, stop := 80 },
        name := "wf" }
      { span := { fileId := fixtureRoot, start := 84, stop := 87 },
        name := "wff" }
      { span := { fileId := fixtureRoot, start := 88, stop := 89 },
        name := "x" }
      { fileId := fixtureRoot, start := 90, stop := 92 },
   .axiomatic
      { fileId := fixtureRoot, start := 96, stop := 98 }
      { span := { fileId := fixtureRoot, start := 93, stop := 95 },
        name := "ax" }
      { span := { fileId := fixtureRoot, start := 99, stop := 101 },
        name := "|-" }
      [{ span := { fileId := fixtureRoot, start := 102, stop := 103 },
          name := "x" }]
      { fileId := fixtureRoot, start := 104, stop := 106 },
   .provable
      { fileId := fixtureRoot, start := 110, stop := 112 }
      { span := { fileId := fixtureRoot, start := 107, stop := 109 },
        name := "th" }
      { span := { fileId := fixtureRoot, start := 113, stop := 115 },
        name := "|-" }
      [{ span := { fileId := fixtureRoot, start := 116, stop := 117 },
          name := "x" }]
      (.compressed
        { fileId := fixtureRoot, start := 121, stop := 122 }
        [{ span := { fileId := fixtureRoot, start := 123, stop := 125 },
            name := "ax" }]
        { fileId := fixtureRoot, start := 126, stop := 127 }
        [{ span := { fileId := fixtureRoot, start := 130, stop := 131 },
            bytes := [65] },
         { span := { fileId := fixtureRoot, start := 134, stop := 135 },
            bytes := [66] }])
      { fileId := fixtureRoot, start := 118, stop := 120 }
      { fileId := fixtureRoot, start := 138, stop := 140 }]

def fixtureProofOwner : Atom := sourceProofOwnerAtom fixtureOwner 4

def fixtureBodyA : Atom :=
  indexedRow "compressed-body-word" fixtureProofOwner 0
    (compressedWordAtom [65])

def fixtureBodyB : Atom :=
  indexedRow "compressed-body-word" fixtureProofOwner 1
    (compressedWordAtom [66])

def fixtureProofEnd : Atom :=
  .expression [.symbol "mm-proof-end", fixtureProofOwner, natAtom 2]

def fixtureHeaderControl : Atom :=
  .expression
    [.symbol "mm-compressed-header-control", fixtureOwner,
      fixtureProofOwner, natAtom 0]

def atomHasHead (name : String) : Atom → Bool
  | .expression (.symbol head :: _) => head == name
  | _ => false

def fixtureExactStatementsCheck : Bool :=
  match transformRawSource fixtureOwner fixtureFiles bookSpecPolicy
      fixtureRoot with
  | .error _ => false
  | .ok artifact => artifact.statements == fixtureStatements

def fixtureDerivedRows : List Atom :=
  match sourceDerivedProofRows fixtureOwner fixtureStatements with
  | .rejected _ => []
  | .ok rows => rows

end Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary
