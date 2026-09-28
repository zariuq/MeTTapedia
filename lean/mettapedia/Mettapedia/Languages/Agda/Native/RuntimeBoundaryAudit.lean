import Mettapedia.Languages.Agda.Native.ReferenceMain
import Lean.Elab.Command

/-! Audit the compiled execution closure, including transitive imports. -/

open Lean Lean.Elab.Command

run_cmd do
  let forbidden := [
    `Mettapedia.Languages.Agda.Specification,
    `Mettapedia.Languages.Agda.StaticSpecification,
    `Mettapedia.Languages.Agda.StaticMetatheory,
    `Mettapedia.Languages.Agda.SourceEvidence,
    `Mettapedia.Languages.Agda.SourceMetatheory,
    `Mettapedia.Languages.Agda.Adequacy,
    `Mettapedia.Languages.Agda.Reference,
    `Mettapedia.Languages.Agda.Core,
    `Mettapedia.Languages.Agda.CoreGSLT,
    `Mettapedia.Languages.Agda.Intrinsic]
  let env ← getEnv
  for imported in env.header.modules do
    if forbidden.any (fun family => family.isPrefixOf imported.module) then
      throwError "Execution imports forbidden source/checker family: {imported.module}"
  logInfo m!"Compiled execution boundary passed: {env.header.modules.size} imported modules checked."
