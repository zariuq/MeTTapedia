import Mettapedia.Languages.MeTTa.PeTTa.ArtifactBundle
import Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge
import Mettapedia.Conformance.PeTTaArtifactBridge

/-!
# PeTTa Artifact Bundle

Public compatibility facade for the PeTTa artifact bundle and runtime bridge.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.Artifacts

open Mettapedia.Languages.MeTTa.PeTTa.ProfileBridge

abbrev frozenConfigToPeTTaSpace := Mettapedia.Conformance.PeTTaArtifactBridge.frozenConfigToPeTTaSpace

theorem frozenConfigToPeTTaSpace_facts_roundTrip
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) :
    (frozenConfigToPeTTaSpace cfg).facts.map specToCorePattern = cfg.facts :=
  Mettapedia.Conformance.PeTTaArtifactBridge.frozenConfigToPeTTaSpace_facts_roundTrip cfg

theorem frozenConfigToPeTTaSpace_rewrites_roundTrip
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) :
    (frozenConfigToPeTTaSpace cfg).rules.map specToCoreRewriteRule =
      (Algorithms.MeTTa.PeTTa.toLanguageDef cfg).rewrites :=
  Mettapedia.Conformance.PeTTaArtifactBridge.frozenConfigToPeTTaSpace_rewrites_roundTrip cfg

theorem frozenConfigToPeTTaSpace_rewrites_eq_runtimeLowering
    (cfg : Algorithms.MeTTa.PeTTa.FrozenPeTTaConfig) :
    ((Mettapedia.Languages.MeTTa.PeTTa.LPSoundness.pettaSpaceToLangDef
      (frozenConfigToPeTTaSpace cfg)).rewrites).map specToCoreRewriteRule =
        (Algorithms.MeTTa.PeTTa.toLanguageDef cfg).rewrites :=
  Mettapedia.Conformance.PeTTaArtifactBridge.frozenConfigToPeTTaSpace_rewrites_eq_runtimeLowering cfg

abbrev exportFrozenPeTTaArtifacts := Mettapedia.Conformance.PeTTaArtifactBridge.exportFrozenPeTTaArtifacts
abbrev checkFrozenPeTTaArtifacts := Mettapedia.Conformance.PeTTaArtifactBridge.checkFrozenPeTTaArtifacts

end Mettapedia.Languages.MeTTa.PeTTa.Artifacts
