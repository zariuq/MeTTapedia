import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport

/-- Write the StructuredC language wire and the generated cold program wire. -/
def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport.exportCold arguments
