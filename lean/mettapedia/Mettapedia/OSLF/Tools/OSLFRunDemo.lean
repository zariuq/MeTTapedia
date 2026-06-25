import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL

-- RUN the OSLF algorithm on the rho-calculus GSLT → OUTPUT its NTT crossings.
#eval s!"rho NTT crossing count = {(unaryCrossings rhoCalcProcessCore).length}"
#eval unaryCrossings rhoCalcProcessCore

-- native_decide REPLACEMENT: `decide` (sound kernel reduction, no compiled oracle)
-- proves the real OSLF crossing-membership goals — the exact NTTDiagnostics pattern.
example : ("PDrop", "Name", "Proc") ∈ unaryCrossings rhoCalcProcessCore := by decide
example : ("NQuote", "Proc", "Name") ∈ unaryCrossings rhoCalcProcessCore := by decide
