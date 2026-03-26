import Algorithms.MeTTa.LookupPlans
import Algorithms.MeTTa.PeTTa.Lowering
import Mettapedia.Languages.MeTTa.PeTTa.LookupPlan
import Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge
import Mettapedia.Languages.MeTTa.PeTTa.ArtifactBundle
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness

namespace Mettapedia.Conformance.PeTTaArtifactBridge

open Algorithms.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge

theorem pettaSpaceMatchFamily_eq_algorithms :
    Mettapedia.Languages.MeTTa.PeTTa.LookupPlan.pettaSpaceMatchFamily =
      Algorithms.MeTTa.LookupPlans.pettaSpaceMatchFamily := rfl

theorem pettaGetAtomsFamily_eq_algorithms :
    Mettapedia.Languages.MeTTa.PeTTa.LookupPlan.pettaGetAtomsFamily =
      Algorithms.MeTTa.LookupPlans.pettaGetAtomsFamily := rfl

theorem pettaLookupPlanArtifact_eq_algorithms :
    Mettapedia.Languages.MeTTa.PeTTa.LookupPlan.pettaLookupPlanArtifact =
      Algorithms.MeTTa.LookupPlans.pettaLookupPlanArtifact := rfl

theorem pettaLookupPlanArtifact_renderJson_eq_algorithms :
    Mettapedia.Languages.MeTTa.PeTTa.LookupPlan.pettaLookupPlanArtifact.renderJson =
      Algorithms.MeTTa.LookupPlans.pettaLookupPlanArtifact.renderJson := by
  simp [pettaLookupPlanArtifact_eq_algorithms]

theorem pettaLookupPlanArtifact_checksumString_eq_algorithms :
    Mettapedia.Languages.MeTTa.PeTTa.LookupPlan.pettaLookupPlanArtifact.checksumString =
      Algorithms.MeTTa.LookupPlans.pettaLookupPlanArtifact.checksumString := by
  simp [pettaLookupPlanArtifact_eq_algorithms]

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
    (frozenConfigToPeTTaSpace cfg).rules.mapM specToCoreRewriteRule =
      .ok (Algorithms.MeTTa.PeTTa.toLanguageDef cfg).rewrites := by
  simpa [frozenConfigToPeTTaSpace, Function.comp] using
    rewriteRule_list_roundTrip ((Algorithms.MeTTa.PeTTa.toLanguageDef cfg).rewrites)

theorem frozenConfigToPeTTaSpace_rewrites_eq_runtimeLowering
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) :
    ((Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef
      (frozenConfigToPeTTaSpace cfg)).rewrites).mapM specToCoreRewriteRule =
        .ok (Algorithms.MeTTa.PeTTa.toLanguageDef cfg).rewrites := by
  simpa [Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef] using
    frozenConfigToPeTTaSpace_rewrites_roundTrip cfg

def exportFrozenPeTTaArtifacts
    (outDir : System.FilePath)
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PeTTa.Artifacts.exportPeTTaArtifacts outDir (frozenConfigToPeTTaSpace cfg)

def checkFrozenPeTTaArtifacts
    (outDir : System.FilePath)
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PeTTa.Artifacts.checkPeTTaArtifacts outDir (frozenConfigToPeTTaSpace cfg)

end Mettapedia.Conformance.PeTTaArtifactBridge
