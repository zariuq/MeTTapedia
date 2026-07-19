/-
# Hash-pinned certified-mask fixtures

The output records the Pure goal-shape and exact-viability decisions together
with the conversion-free LF boundary.  Source hashes are supplied by the
launcher so the generator never contains a self-referential hash.
-/

import Mettapedia.GSLT.LanguageDef.Pure.CertifiedMask
import Mettapedia.GSLT.LanguageDef.LF.ProfileChecker

namespace Mettapedia.GSLT.LanguageDef.PureCertifiedMaskFixturesMain

open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRoot
open Mettapedia.GSLT.LanguageDef.PureCertifiedMask
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.GSLT.LanguageDef.LFProfileChecker

private def jsonString (value : String) : String :=
  "\"" ++ value ++ "\""

private def jsonBool (value : Bool) : String :=
  if value then "true" else "false"

private def renderMeta (genericHash pureHash betaRootHash profileHash
    diagnosticHash generatorHash : String) : String :=
  "{" ++
    "\"kind\":\"meta\"," ++
    "\"schema\":\"gslt.certified_mask.pure_dtt_boundary.v1\"," ++
    "\"row_count\":5," ++
    "\"generic_certified_mask_sha256\":" ++ jsonString genericHash ++ "," ++
    "\"pure_certified_mask_sha256\":" ++ jsonString pureHash ++ "," ++
    "\"beta_atomic_root_sha256\":" ++ jsonString betaRootHash ++ "," ++
    "\"lf_profile_checker_sha256\":" ++ jsonString profileHash ++ "," ++
    "\"eq_symm_diagnostic_sha256\":" ++ jsonString diagnosticHash ++ "," ++
    "\"fixture_generator_sha256\":" ++ jsonString generatorHash ++
  "}"

private def renderPiHead : String :=
  "{" ++
    "\"kind\":\"goal_shape\"," ++
    "\"name\":\"pi_bare_head\"," ++
    "\"hard_prune\":" ++
      jsonBool (goalShapeRejects? betaRootIdentityGoal piBareHead) ++ "," ++
    "\"expected\":true" ++
  "}"

private def renderPiLambda : String :=
  "{" ++
    "\"kind\":\"goal_shape\"," ++
    "\"name\":\"pi_lambda\"," ++
    "\"hard_prune\":" ++
      jsonBool (goalShapeRejects? betaRootIdentityGoal betaRootIdentityTerm) ++ "," ++
    "\"expected\":false" ++
  "}"

private def renderImpossibleState : String :=
  "{" ++
    "\"kind\":\"state_viability\"," ++
    "\"name\":\"zero_budget_unfinished\"," ++
    "\"hard_prune\":" ++ jsonBool
      ((betaViabilityStateTest betaRootIdentityGoal).test impossibleStateNode) ++ "," ++
    "\"expected\":true" ++
  "}"

private def renderIdentityInitial : String :=
  "{" ++
    "\"kind\":\"state_viability\"," ++
    "\"name\":\"identity_initial_reachable\"," ++
    "\"hard_prune\":" ++ jsonBool
      ((betaViabilityStateTest betaRootIdentityGoal).test identityInitialNode) ++ "," ++
    "\"expected\":false" ++
  "}"

private def renderConversionBoundary : String :=
  let exactAccept :=
    checkProof indexed exactTypeSignature [] .con (.con "betaTyped") betaRedexType
  let betaEquivalentAccept :=
    checkProof indexed exactTypeSignature [] .con (.con "betaTyped") (.srt .type)
  "{" ++
    "\"kind\":\"trust_boundary\"," ++
    "\"name\":\"beta_equivalent_not_syntactically_equal\"," ++
    "\"exact_type_accept\":" ++ jsonBool exactAccept ++ "," ++
    "\"beta_equivalent_expected_accept\":" ++ jsonBool betaEquivalentAccept ++ "," ++
    "\"dttbench_v5_authenticated\":false," ++
    "\"required_route\":\"conversion-capable LF/MIK\"" ++
  "}"

def renderFixtures (genericHash pureHash betaRootHash profileHash
    diagnosticHash generatorHash : String) : String :=
  String.intercalate "\n"
    [ renderMeta genericHash pureHash betaRootHash profileHash diagnosticHash generatorHash
    , renderPiHead
    , renderPiLambda
    , renderImpossibleState
    , renderIdentityInitial
    , renderConversionBoundary
    ] ++ "\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [genericHash, pureHash, betaRootHash, profileHash, diagnosticHash,
      generatorHash, mode, outputPath] =>
      let expected := renderFixtures genericHash pureHash betaRootHash profileHash
        diagnosticHash generatorHash
      match mode with
      | "write" =>
          IO.FS.writeFile outputPath expected
          IO.println s!"wrote {expected.toUTF8.size} bytes to {outputPath}"
          pure 0
      | "check" =>
          let actual ← IO.FS.readFile outputPath
          if actual = expected then
            IO.println s!"fixture parity OK: {outputPath}"
            pure 0
          else
            IO.eprintln "certified-mask fixture drift"
            pure 1
      | _ =>
          IO.eprintln "mode must be write or check"
          pure 1
  | _ =>
      IO.eprintln
        "usage: CertifiedMaskFixturesMain <six source hashes> (write|check) <output.jsonl>"
      pure 1

end Mettapedia.GSLT.LanguageDef.PureCertifiedMaskFixturesMain

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.PureCertifiedMaskFixturesMain.main arguments
