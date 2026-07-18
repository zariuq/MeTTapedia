import Mettapedia.OSLF.Framework.ConstructorCategory

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax

-- RUN the OSLF algorithm on the rho-calculus GSLT → OUTPUT its NTT crossings.
#eval s!"rho NTT crossing count = {(unaryCrossings rhoCalc).length}"
#eval unaryCrossings rhoCalc

-- native_decide REPLACEMENT: `decide` (sound kernel reduction, no compiled oracle)
-- proves the real OSLF crossing-membership goals — the exact NTTDiagnostics pattern.
example : ("PDrop", "Name", "Proc") ∈ unaryCrossings rhoCalc := by decide
example : ("NQuote", "Proc", "Name") ∈ unaryCrossings rhoCalc := by decide
