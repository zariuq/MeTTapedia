import Mettapedia.GSLT.LanguageDef.Gauthier.FrozenCandidates49

namespace Mettapedia.GSLT.LanguageDef.GauthierCandidateEvaluationExport

open Mettapedia.GSLT.LanguageDef.GauthierE2
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierFrozenCandidates49

private def evaluationFuel : Nat := 4096

private def renderActual : Option Int → String
  | none => "none"
  | some value => toString value

private def renderPosition (target : AdjudicationTarget) (position : Nat) : String :=
  let index := target.spec.index position
  let expected := target.spec.value index
  let actual := term evaluationFuel orgMemoSignature target.candidate.program (Int.ofNat position)
  String.intercalate "\t"
    [ target.oeisId
    , target.candidate.programSha256
    , toString position
    , toString index
    , toString expected
    , renderActual actual
    , if position < target.publishedTermCount then "published" else "generated"
    ]

private def exportTarget (target : AdjudicationTarget) : IO Unit := do
  for position in List.range (max (target.publishedTermCount + 10) 140) do
    IO.println (renderPosition target position)

def main : IO Unit := do
  IO.println "oeis_id\tprogram_sha256\tposition\toeis_index\texpected\tactual\tregion"
  for target in targets do
    exportTarget target

end Mettapedia.GSLT.LanguageDef.GauthierCandidateEvaluationExport

def main : IO Unit :=
  Mettapedia.GSLT.LanguageDef.GauthierCandidateEvaluationExport.main
