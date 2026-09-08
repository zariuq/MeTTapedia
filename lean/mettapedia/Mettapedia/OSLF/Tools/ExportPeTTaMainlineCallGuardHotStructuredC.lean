import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport

/-- Write the generated hot dispatch program wire. -/
def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport.exportHot arguments
