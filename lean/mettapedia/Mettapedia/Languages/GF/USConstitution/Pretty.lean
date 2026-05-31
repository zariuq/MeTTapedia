import Mettapedia.Languages.GF.PGFPretty
import Mettapedia.Languages.GF.USConstitution.GeneratedConformance

/-!
# Pretty Layer for US Constitution GF Witnesses

This is the human-facing view above the generated ParseEng witnesses.
It does not replace `Generated.Witnesses`; it renders the same
`ExportedTree` values through a reversible `FormalGF` view.
-/

namespace Mettapedia.Languages.GF.USConstitution.Pretty

open Mettapedia.Languages.GF.PGFWitnessIR
open Mettapedia.Languages.GF.PGFPretty
open Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

private def bulletList (label : String) (items : List String) : String :=
  if items.isEmpty then
    label ++ ": []\n"
  else
    label ++ ":\n" ++ String.intercalate "\n" (items.map fun item => "- " ++ item) ++ "\n"

def prettyParses (cid : ClauseId) : List String :=
  (clauseParses cid).map ExportedTree.prettyFormalGF

def parseRoundTrips (cid : ClauseId) : Bool :=
  (clauseParses cid).all ExportedTree.formalGFRoundTrips

abbrev CorrectionId :=
  Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.CorrectionId

def correctionsFor (cid : ClauseId) : List CorrectionId :=
  Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionsForClause cid

def correctionKindName (corr : CorrectionId) : String :=
  match Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionKind corr with
  | .exactSubfragment => "exact subfragment"
  | .contextCompletion => "context completion"

def correctionPrettyParses (corr : CorrectionId) : List String :=
  (Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionParses corr).map
    ExportedTree.prettyFormalGF

def correctionRoundTrips (corr : CorrectionId) : Bool :=
  (Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionParses corr).all
    ExportedTree.formalGFRoundTrips

def prettyCorrectionReport (corr : CorrectionId) : String :=
  "Correction kind: " ++ correctionKindName corr ++ "\n" ++
  "Parser input: " ++
    Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionParserInput corr ++ "\n" ++
  "Confidence: " ++
    toString (Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.confidencePermille corr) ++
    "/1000\n" ++
  "Justification: " ++
    Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionJustification corr ++ "\n" ++
  "Accepted parses: " ++
    toString (Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.acceptedParseCount corr) ++
    "\n" ++
  bulletList "GF linearization"
    (Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionGFLinearizations corr) ++
  bulletList "GF bracketed linearization"
    (Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionGFBracketedLinearizations corr) ++
  "FormalGF structural round-trip: " ++ toString (correctionRoundTrips corr) ++ "\n" ++
  "Pretty GF:\n" ++ String.intercalate "\n\n---\n\n" (correctionPrettyParses corr)

def prettyClauseReport (cid : ClauseId) : String :=
  "Clause: " ++ clauseAnchor cid ++ "\n" ++
  "Source: " ++ clauseText cid ++ "\n" ++
  "Parser input: " ++ parserInput cid ++ "\n" ++
  "Accepted parses: " ++ toString (acceptedParseCount cid) ++ "\n" ++
  bulletList "GF linearization" (clauseGFLinearizations cid) ++
  bulletList "GF bracketed linearization" (clauseGFBracketedLinearizations cid) ++
  "FormalGF structural round-trip: " ++ toString (parseRoundTrips cid) ++ "\n" ++
  "Pretty GF:\n" ++ String.intercalate "\n\n---\n\n" (prettyParses cid)

def prettyClauseReportWithCorrections (cid : ClauseId) : String :=
  let corrections := correctionsFor cid
  prettyClauseReport cid ++
  if corrections.isEmpty then
    ""
  else
    "\n\nContext/exact-subfragment repair witnesses:\n\n" ++
      String.intercalate "\n\n--- correction ---\n\n" (corrections.map prettyCorrectionReport)

def articleISelectedClauseIds : List ClauseId := [
  .articleISection1Vesting,
  .articleISection2HouseComposition,
  .articleISection2RepresentativeAge,
  .articleISection3SenateImpeachments,
  .articleISection5Rules,
  .articleISection7EveryBillPresented,
  .articleISection7PresidentSigns,
  .articleISection7BecomesLaw,
  .articleISection8DeclareWar,
  .articleISection9Habeas,
  .articleISection9NoTitleOfNobility
]

def articleISelectedPrettyReport : String :=
  "Article I selected GF witness lane\n" ++
  "Exact ParseEng witnesses where available; context/exact-subfragment repairs shown separately.\n\n" ++
  String.intercalate "\n\n==============================\n\n"
    (articleISelectedClauseIds.map prettyClauseReportWithCorrections)

def articleVIIRatificationPretty : String :=
  prettyClauseReport .articleVIIRatification

example : articleISelectedClauseIds.length = 11 := by decide
example : (prettyParses .articleVIIRatification).length = acceptedParseCount .articleVIIRatification := by
  decide

end Mettapedia.Languages.GF.USConstitution.Pretty
