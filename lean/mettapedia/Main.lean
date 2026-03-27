import Mettapedia.Languages.MeTTa.HE.LookupPlan
import Mettapedia.Languages.MeTTa.HE.TransitionSpec
import Mettapedia.Languages.MeTTa.HE.RewriteIR
import Mettapedia.Languages.MeTTa.HE.RewriteIRV2
import Mettapedia.Languages.MeTTa.HE.ContractExport
import Mettapedia.Languages.MeTTa.HE.SyntaxSpec
import Mettapedia.Languages.MeTTa.HE.ScopeContract
import Mettapedia.Languages.MeTTa.HE.NativeProfile
import Mettapedia.Languages.MeTTa.HE.RuntimeContract
import Mettapedia.Languages.MeTTa.HE.ArtifactBundle
import Mettapedia.Languages.MeTTa.SearchPolicyContract

private def usage : String :=
  String.intercalate "\n"
    [ "mettapedia commands:"
    , "  lookup-plan export-he <out-dir>"
    , "  lookup-plan export-he            (default out-dir: artifacts/lookup)"
    , "  lookup-plan check-he <out-dir>"
    , "  lookup-plan check-he             (default out-dir: artifacts/lookup)"
    , "  transition-spec export-he <out-dir>"
    , "  transition-spec export-he            (default out-dir: artifacts/transition)"
    , "  transition-spec check-he <out-dir>"
    , "  transition-spec check-he             (default out-dir: artifacts/transition)"
    , "  rewrite-ir export-he <out-dir>"
    , "  rewrite-ir export-he                 (default out-dir: artifacts/transition)"
    , "  rewrite-ir check-he <out-dir>"
    , "  rewrite-ir check-he                  (default out-dir: artifacts/transition)"
    , "  rewrite-ir-v2 export-he <out-dir>"
    , "  rewrite-ir-v2 export-he               (default out-dir: artifacts/transition)"
    , "  rewrite-ir-v2 check-he <out-dir>"
    , "  rewrite-ir-v2 check-he                (default out-dir: artifacts/transition)"
    , "  execution-contract export-he <out-dir>"
    , "  execution-contract export-he          (default out-dir: artifacts/transition)"
    , "  execution-contract check-he <out-dir>"
    , "  execution-contract check-he           (default out-dir: artifacts/transition)"
    , "  syntax-authority export-he <out-dir>"
    , "  syntax-authority export-he            (default out-dir: artifacts/syntax)"
    , "  syntax-authority check-he <out-dir>"
    , "  syntax-authority check-he             (default out-dir: artifacts/syntax)"
    , "  scope-contract export-he <out-dir>"
    , "  scope-contract export-he             (default out-dir: artifacts/transition)"
    , "  scope-contract check-he <out-dir>"
    , "  scope-contract check-he              (default out-dir: artifacts/transition)"
    , "  native-profile export-he <out-dir>"
    , "  native-profile export-he             (default out-dir: artifacts/transition)"
    , "  native-profile check-he <out-dir>"
    , "  native-profile check-he              (default out-dir: artifacts/transition)"
    , "  runtime-contract export-he <out-dir>"
    , "  runtime-contract export-he           (default out-dir: artifacts/transition)"
    , "  runtime-contract check-he <out-dir>"
    , "  runtime-contract check-he            (default out-dir: artifacts/transition)"
    , "  search-policy export-metta <out-dir>"
    , "  search-policy export-metta           (default out-dir: artifacts/transition)"
    , "  search-policy check-metta <out-dir>"
    , "  search-policy check-metta            (default out-dir: artifacts/transition)"
    , "  bundle export-he"
    , "  bundle check-he"
    ]

private def defaultLookupOutDir : System.FilePath :=
  "artifacts/lookup"

private def defaultTransitionOutDir : System.FilePath :=
  "artifacts/transition"

private def defaultSyntaxOutDir : System.FilePath :=
  "artifacts/syntax"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["lookup-plan", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.exportHeLookupPlan outDir
  | ["lookup-plan", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.exportHeLookupPlan defaultLookupOutDir
  | ["lookup-plan", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.checkHeLookupPlan outDir
  | ["lookup-plan", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.LookupPlan.checkHeLookupPlan defaultLookupOutDir
  | ["transition-spec", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.TransitionSpec.exportHeTransitionSpec outDir
  | ["transition-spec", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.TransitionSpec.exportHeTransitionSpec defaultTransitionOutDir
  | ["transition-spec", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.TransitionSpec.checkHeTransitionSpec outDir
  | ["transition-spec", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.TransitionSpec.checkHeTransitionSpec defaultTransitionOutDir
  | ["rewrite-ir", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIR.exportHeRewriteIR outDir
  | ["rewrite-ir", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIR.exportHeRewriteIR defaultTransitionOutDir
  | ["rewrite-ir", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIR.checkHeRewriteIR outDir
  | ["rewrite-ir", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIR.checkHeRewriteIR defaultTransitionOutDir
  | ["rewrite-ir-v2", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIRV2.exportHeRewriteIRV2 outDir
  | ["rewrite-ir-v2", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIRV2.exportHeRewriteIRV2 defaultTransitionOutDir
  | ["rewrite-ir-v2", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIRV2.checkHeRewriteIRV2 outDir
  | ["rewrite-ir-v2", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.RewriteIRV2.checkHeRewriteIRV2 defaultTransitionOutDir
  | ["execution-contract", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.ExecutionContract.exportHeExecutionContract outDir
  | ["execution-contract", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.ExecutionContract.exportHeExecutionContract defaultTransitionOutDir
  | ["execution-contract", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.ExecutionContract.checkHeExecutionContract outDir
  | ["execution-contract", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.ExecutionContract.checkHeExecutionContract defaultTransitionOutDir
  | ["syntax-authority", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.exportHeSyntaxAuthority outDir
  | ["syntax-authority", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.exportHeSyntaxAuthority defaultSyntaxOutDir
  | ["syntax-authority", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.checkHeSyntaxAuthority outDir
  | ["syntax-authority", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.checkHeSyntaxAuthority defaultSyntaxOutDir
  | ["scope-contract", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.ScopeContract.exportHeScopeContract outDir
  | ["scope-contract", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.ScopeContract.exportHeScopeContract defaultTransitionOutDir
  | ["scope-contract", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.ScopeContract.checkHeScopeContract outDir
  | ["scope-contract", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.ScopeContract.checkHeScopeContract defaultTransitionOutDir
  | ["native-profile", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.NativeProfile.exportHeNativeProfile outDir
  | ["native-profile", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.NativeProfile.exportHeNativeProfile defaultTransitionOutDir
  | ["native-profile", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.NativeProfile.checkHeNativeProfile outDir
  | ["native-profile", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.NativeProfile.checkHeNativeProfile defaultTransitionOutDir
  | ["runtime-contract", "export-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.RuntimeContract.exportHeRuntimeContract outDir
  | ["runtime-contract", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.RuntimeContract.exportHeRuntimeContract defaultTransitionOutDir
  | ["runtime-contract", "check-he", outDir] =>
      Mettapedia.Languages.MeTTa.HE.RuntimeContract.checkHeRuntimeContract outDir
  | ["runtime-contract", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.RuntimeContract.checkHeRuntimeContract defaultTransitionOutDir
  | ["search-policy", "export-metta", outDir] =>
      Mettapedia.Languages.MeTTa.SearchPolicyContract.exportMeTTaSearchPolicyContract outDir
  | ["search-policy", "export-metta"] =>
      Mettapedia.Languages.MeTTa.SearchPolicyContract.exportMeTTaSearchPolicyContract defaultTransitionOutDir
  | ["search-policy", "check-metta", outDir] =>
      Mettapedia.Languages.MeTTa.SearchPolicyContract.checkMeTTaSearchPolicyContract outDir
  | ["search-policy", "check-metta"] =>
      Mettapedia.Languages.MeTTa.SearchPolicyContract.checkMeTTaSearchPolicyContract defaultTransitionOutDir
  | ["bundle", "export-he"] =>
      Mettapedia.Languages.MeTTa.HE.ArtifactBundle.exportHeManifest
        defaultTransitionOutDir defaultLookupOutDir defaultSyntaxOutDir
  | ["bundle", "check-he"] =>
      Mettapedia.Languages.MeTTa.HE.ArtifactBundle.checkHeManifest
        defaultTransitionOutDir defaultLookupOutDir defaultSyntaxOutDir
  | _ =>
      IO.println usage
      pure 1
