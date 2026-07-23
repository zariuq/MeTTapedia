import Mettapedia.Languages.Metamath.SourceGSLTOperations

/-!
# Export the source-derived Metamath operation GSLTs
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTOperationsMeTTaExport

open Mettapedia.Languages.Metamath.SourceGSLTOperations

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [foldOutputPath, checkerOutputPath] =>
      if validateSourceOperationPresentation then
        IO.FS.writeFile foldOutputPath renderedSourceFold
        IO.FS.writeFile checkerOutputPath renderedSourceChecker
        IO.println <|
          s!"wrote {renderedSourceFold.toUTF8.size} fold bytes and " ++
            s!"{renderedSourceChecker.toUTF8.size} checker bytes"
        pure 0
      else
        IO.eprintln
          "Metamath source-operation GSLT validation failed"
        pure 1
  | _ =>
      IO.eprintln <|
        "usage: SourceGSLTOperationsMeTTaExport " ++
          "<source-fold.metta> <source-checker.metta>"
      pure 2

end Mettapedia.Languages.Metamath.SourceGSLTOperationsMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.SourceGSLTOperationsMeTTaExport.main arguments
