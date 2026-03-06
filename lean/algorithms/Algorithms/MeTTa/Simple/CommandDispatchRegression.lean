import Algorithms.MeTTa.Simple.RuntimeProfile

namespace Algorithms.MeTTa.Simple.CommandDispatchRegression

open Algorithms.MeTTa.Simple

#guard normalizeDialect " He " = "he"
#guard normalizeDialect "PeTTa" = "petta"

#guard (runtimeProfileOfDialect? "he").map (·.dialect) = some "he"
#guard (runtimeProfileOfDialect? "PETTA").map (·.dialect) = some "petta"
#guard runtimeProfileOfDialect? "unknown" = none

#guard
  match runDialectDispatch? ["run", "--dialect", "he", "--json", "x.metta"] with
  | some (p, asJson, file) =>
      p.dialect = "he" && asJson = true && file = "x.metta"
  | none => false

#guard
  match runDialectDispatch? ["run", "--dialect", "PeTTa", "x.metta"] with
  | some (p, asJson, file) =>
      p.dialect = "petta" && asJson = false && file = "x.metta"
  | none => false

#guard runDialectDispatch? ["run", "--dialect", "bad", "x.metta"] = none

#guard
  match replDialectDispatch? ["repl", "--dialect", "HE"] with
  | some p => p.dialect = "he"
  | none => false

#guard
  match replDialectDispatch? ["repl", "--dialect", "petta"] with
  | some p => p.includeDefaultPeTTaLibrary = true
  | none => false

#guard replDialectDispatch? ["repl", "--dialect", "bad"] = none

end Algorithms.MeTTa.Simple.CommandDispatchRegression
