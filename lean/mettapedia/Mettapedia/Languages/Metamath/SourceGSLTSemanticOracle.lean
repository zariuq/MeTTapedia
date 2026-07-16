import Mettapedia.Languages.Metamath.MMLean4SemanticView

/-!
# Semantic oracle for checked Metamath source ledgers

The grammar-derived parser owns the complete ordered source ledger.  This
module gives that ledger an independent semantic anchor by running the same
source bytes through the verified `mm-lean4` reader and retaining its final
declaration database.  It does not construct a second syntax ledger.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTSemanticOracle

open Mettapedia.Languages.Metamath.MMLean4SemanticView

private def readCheckedDatabase (sourcePath : String) : IO Metamath.Verify.DB := do
  let sourceBytes ← IO.FS.readBinFile sourcePath
  pure <|
    Metamath.Verify.checkBytes sourceBytes
      Metamath.Verify.ModeConfig.soundDefault

def main (arguments : List String) : IO UInt32 := do
  let paths ← match arguments with
    | [demo0, miu, peano, distinctVariables, normal, compressed] =>
        pure [demo0, miu, peano, distinctVariables, normal, compressed]
    | _ =>
        IO.eprintln
          "usage: SourceGSLTSemanticOracle <demo0.mm> <miu.mm> <peano.mm> <dv.mm> <normal.mm> <compressed.mm>"
        return 2
  let databases ← paths.mapM readCheckedDatabase
  if hAccepted : databases.all readerAccepted = true then
    have _agreements : ∀ database ∈ databases, ReaderAgreement database := by
      intro database hDatabase
      exact readerAccepted_sound <|
        (List.all_eq_true.mp hAccepted) database hDatabase
    match databases with
    | [demo0, miu, peano, distinctVariables, normal, compressed] =>
        if hSame : semanticDatabasesAgree normal compressed = true then
          have _semanticAgreement :
              semanticDatabaseView normal = semanticDatabaseView compressed :=
            semanticDatabasesAgree_sound hSame
          let objectCounts :=
            [demo0, miu, peano, distinctVariables, normal, compressed].map
              fun database => database.objects.toList.length
          IO.println
            s!"MMSourceSemanticOracleSummary 6 {reprStr objectCounts} True"
          pure 0
        else
          IO.eprintln
            "normal and compressed sources produced different semantic databases"
          pure 1
    | _ =>
        IO.eprintln "internal source-arity mismatch"
        pure 1
  else
    IO.eprintln
      s!"at least one source was rejected by mm-lean4: {reprStr (databases.map readerAccepted)}"
    pure 1

end Mettapedia.Languages.Metamath.SourceGSLTSemanticOracle

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.SourceGSLTSemanticOracle.main arguments
