import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport

/-- Write the generated hot transition program wire and the primitive
catalog wire. -/
def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCExport.exportHotTransition
    arguments
