import Algorithms.MeTTa.LookupPlans
import Algorithms.MeTTa.PeTTa.Lowering
import Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge
import Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIR
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness

/-!
# PeTTa Artifact Bundle

Single PeTTa-side entrypoint for the shared native-runner artifact trio:

- `petta.lookup_plan.*`
- `petta.execution_contract.*`
- `petta.transition_spec.*`
- `petta.rewrite_ir.*`

The lookup plan is dialect-level and static. The transition and rewrite
artifacts are program-level and derived from a concrete `PeTTaSpace`.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.Artifacts

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge

/--
Bridge a runtime-lowered `FrozenPeTTaConfig` into the formal `PeTTaSpace`
artifact source. This is intentionally program-parametric: the shared runtime
artifacts should be derived from the concrete lowered PeTTa program, not from
an invented static dialect language.
-/
def frozenConfigToPeTTaSpace
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) : PeTTaSpace :=
  { facts := cfg.facts.map coreToSpecPattern
    rules := (Algorithms.MeTTa.PeTTa.toLanguageDef cfg).rewrites.map coreToSpecRewriteRule }

/--
The formal PeTTa rule-preserving compilation path sees exactly the rewrite list
produced by runtime lowering. Names and auxiliary `LanguageDef` metadata may
differ, but the rewrite graph consumed by transition/rewrite artifact derivation
is identical after the explicit core/spec syntax bridge.
-/
theorem frozenConfigToPeTTaSpace_facts_roundTrip
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) :
    (frozenConfigToPeTTaSpace cfg).facts.map specToCorePattern = cfg.facts := by
  simp [frozenConfigToPeTTaSpace, pattern_list_roundTrip]

theorem frozenConfigToPeTTaSpace_rewrites_roundTrip
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) :
    (frozenConfigToPeTTaSpace cfg).rules.map specToCoreRewriteRule =
      (Algorithms.MeTTa.PeTTa.toLanguageDef cfg).rewrites := by
  simp [frozenConfigToPeTTaSpace, rewriteRule_list_roundTrip]

theorem frozenConfigToPeTTaSpace_rewrites_eq_runtimeLowering
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) :
    ((Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef
      (frozenConfigToPeTTaSpace cfg)).rewrites).map specToCoreRewriteRule =
        (Algorithms.MeTTa.PeTTa.toLanguageDef cfg).rewrites := by
  simp [Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef,
    frozenConfigToPeTTaSpace_rewrites_roundTrip]

private def writeLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  let artifact := Algorithms.MeTTa.LookupPlans.pettaLookupPlanArtifact
  let jsonPath := outDir / "petta.lookup_plan.json"
  let checksumPath := outDir / "petta.lookup_plan.checksum"
  IO.FS.createDirAll outDir
  IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
  pure 0

private def checkLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  let artifact := Algorithms.MeTTa.LookupPlans.pettaLookupPlanArtifact
  let jsonPath := outDir / "petta.lookup_plan.json"
  let checksumPath := outDir / "petta.lookup_plan.checksum"
  try
    let jsonText ← IO.FS.readFile jsonPath
    let checksumText ← IO.FS.readFile checksumPath
    let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
    let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
    if jsonOk && checksumOk then
      pure 0
    else
      pure 3
  catch _ =>
    pure 2

def exportPeTTaArtifacts (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  let a ← writeLookupPlan outDir
  let b ← Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract.exportPeTTaExecutionContract outDir
  let c ← Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec.exportPeTTaTransitionSpec outDir s
  let d ← Mettapedia.Languages.MeTTa.PeTTa.RewriteIR.exportPeTTaRewriteIR outDir s
  if a == 0 && b == 0 && c == 0 && d == 0 then
    IO.println s!"exported petta artifact bundle to {outDir}"
    pure 0
  else
    pure 2

def checkPeTTaArtifacts (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  let a ← checkLookupPlan outDir
  let b ← Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract.checkPeTTaExecutionContract outDir
  let c ← Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec.checkPeTTaTransitionSpec outDir s
  let d ← Mettapedia.Languages.MeTTa.PeTTa.RewriteIR.checkPeTTaRewriteIR outDir s
  if a == 0 && b == 0 && c == 0 && d == 0 then
    IO.println s!"[ok] petta artifact bundle matches at {outDir}"
    pure 0
  else
    pure 3

def exportFrozenPeTTaArtifacts
    (outDir : System.FilePath)
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) : IO UInt32 :=
  exportPeTTaArtifacts outDir (frozenConfigToPeTTaSpace cfg)

def checkFrozenPeTTaArtifacts
    (outDir : System.FilePath)
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) : IO UInt32 :=
  checkPeTTaArtifacts outDir (frozenConfigToPeTTaSpace cfg)

end Mettapedia.Languages.MeTTa.PeTTa.Artifacts
