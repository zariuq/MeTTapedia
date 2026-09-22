/-
Emit the CArith0 pilot artifacts (standalone C, embeddable shadow C, test
vectors, and reference output) into the selected directory, from the printer and semantics proved in
`Mettapedia.GSLT.LanguageDef.ArithmeticCArith0Pilot`.
Run: `lake env lean --run scripts/EmitCArith0Pilot.lean [output-directory]`
Then: `gcc -O2 -o carith0 carith0_gen.c -lgmp && ./carith0 < vectors.txt | diff expected.txt -`
-/
import Mettapedia.GSLT.LanguageDef.ArithmeticCArith0Pilot
open Mettapedia.GSLT.LanguageDef.ArithmeticCArith0Pilot
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger

def vectors : List (CoreOp × Int × Int) :=
  let ops := allOps
  let pairs : List (Int × Int) :=
    [(7,2),(-7,2),(7,-2),(-7,-2),(6,2),(0,5),(5,0),(-5,0),(0,0),
     (123456789012345678901234567890, 987654321),
     (-123456789012345678901234567890, 987654321),
     (9223372036854775807, -1), (-9223372036854775808, -1), (1, 1), (-1, -1)]
  ops.flatMap (fun op => pairs.map (fun (a, b) => (op, a, b)))

def inputLines : String :=
  String.intercalate "\n" (vectors.map (fun (op, a, b) =>
    opTag op ++ " " ++ toString a ++ " " ++ toString b)) ++ "\n"

def expectedLines : String :=
  String.intercalate "\n" (vectors.map (fun (op, a, b) =>
    referenceLine op a b)) ++ "\n"

def vectorTable : String :=
  String.intercalate "\n" (vectors.map (fun (op, a, b) =>
    opTag op ++ "\t" ++ toString a ++ "\t" ++ toString b ++ "\t" ++
      referenceLine op a b)) ++ "\n"

def outputPath (directory name : String) : String :=
  if directory.endsWith "/" then directory ++ name else directory ++ "/" ++ name

def main (args : List String) : IO UInt32 := do
  let directory := args.head?.getD "."
  IO.FS.createDirAll directory
  IO.FS.writeFile (outputPath directory "carith0_gen.c") emitProgram
  IO.FS.writeFile (outputPath directory "carith0_shadow_v1.generated.h") emitShadowHeader
  IO.FS.writeFile (outputPath directory "carith0_shadow_v1.generated.c") emitShadowSource
  IO.FS.writeFile (outputPath directory "carith0_shadow_vectors_v1.tsv") vectorTable
  IO.FS.writeFile (outputPath directory "vectors.txt") inputLines
  IO.FS.writeFile (outputPath directory "expected.txt") expectedLines
  IO.println s!"emitted {vectors.length} vectors"
  return 0
