import Mettapedia.Languages.MeTTa.HE.FileRunner

/-!
# HE Core File Conformance

This module runs a curated subset of the *actual* CeTTa HE core `.metta` files.
The goal is not to overclaim support; the goal is to keep real-file pressure on
LeanHE and to record both a positive and a negative boundary.

Positive example:
- `he_a1_symbols.metta`, `he_a3_twoside.metta`, `he_b0_chaining_prelim.metta`,
  and `he_b1_equal_chain.metta` currently run end-to-end with zero errors.

Negative example:
- `he_b2_backchain.metta` still exposes missing direct/backchain-style reasoning.
-/

namespace Mettapedia.Conformance.HECoreFiles

open Mettapedia.Languages.MeTTa.HE

/-- Core files that currently pass end-to-end through the real HE file runner. -/
def supportedCoreFiles : List String :=
  [ "he_a1_symbols.metta"
  , "he_a3_twoside.metta"
  , "he_b0_chaining_prelim.metta"
  , "he_b1_equal_chain.metta"
  ]

/-- Representative core files that still mark real implementation gaps today. -/
def representativeGapCoreFiles : List String :=
  [ "he_b2_backchain.metta"
  , "he_b3_direct.metta"
  ]

def runSupportedCoreChecks : IO (List (String × Bool)) := do
  supportedCoreFiles.mapM fun name => do
    let path ← resolveCoreFile name
    let diag ← runHEFileDiagnostics path
    pure (name, diag.errors = 0)

def supportedCoreFilesPass : IO Bool := do
  pure <| (← runSupportedCoreChecks).all Prod.snd

def observeGapCoreChecks : IO (List (String × Nat)) := do
  representativeGapCoreFiles.mapM fun name => do
    let path ← resolveCoreFile name
    let diag ← runHEFileDiagnostics path
    pure (name, diag.errors)

def printCoreCheckSummary : IO UInt32 := do
  let supported ← runSupportedCoreChecks
  let gaps ← observeGapCoreChecks
  IO.println "LeanHE real-file supported core lane:"
  for (name, ok) in supported do
    IO.println s!"  [{if ok then "ok" else "fail"}] {name}"
  IO.println "LeanHE real-file representative gap lane:"
  for (name, errors) in gaps do
    IO.println s!"  [observed errors={errors}] {name}"
  let pass := supported.all Prod.snd
  IO.println s!"summary: supported_pass={pass} supported_total={supported.length} gap_examples={gaps.length}"
  pure (if pass then 0 else 2)

end Mettapedia.Conformance.HECoreFiles
