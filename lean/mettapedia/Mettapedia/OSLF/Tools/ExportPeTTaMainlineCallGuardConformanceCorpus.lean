import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport

/-- Write the conformance corpus wire. -/
def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport.exportCorpus arguments
