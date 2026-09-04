import Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification

/-!
# Qualify a generated M0GC profile

This executable reads three independently supplied artifacts: the authored
semantic-softtype IR, the generated physical profile JSON, and the projected
MM0 source bytes.  It succeeds only when the proof-carrying qualification in
`M0GCGeneratedProfileQualification` accepts all identities, declarations,
layouts, fingerprints, and source/physical rule pairs.

Maturity boundary: this command exercises the fully connected bounded M0GC
proof of concept.  It does not certify an optimized table organization,
official MMB compatibility, the compiled C object, or a universal NIK host.
-/

namespace Mettapedia.OSLF.Tools.QualifyM0GCGeneratedProfile

open Mettapedia.GSLT.LanguageDef.M0GCGeneratedProfileQualification

private def usage : String :=
  "usage: QualifyM0GCGeneratedProfile <source-ir.json> " ++
    "<physical-profile.json> <projected-source.mm0>"

private def run (sourcePath profilePath projectedSourcePath : String) :
    IO UInt32 := do
  let sourceText ← IO.FS.readFile sourcePath
  let profileText ← IO.FS.readFile profilePath
  let sourceBytes ← IO.FS.readBinFile projectedSourcePath
  match qualify sourceText profileText sourceBytes with
  | .error message =>
      IO.eprintln message
      pure 1
  | .ok qualified =>
      let candidate := qualified.1
      let mutation := candidate.mutateFirstRuleFingerprint
      if mutation.connected then
        IO.eprintln "negative fingerprint mutation was incorrectly accepted"
        pure 2
      else
        IO.println "M0GC generated profile qualification: accepted"
        IO.println s!"rules: {candidate.source.rules.length}"
        IO.println s!"symbols: {candidate.physical.profile.symbols.size}"
        IO.println ("template nodes: " ++
          toString candidate.physical.tables.templates.nodes.size)
        IO.println ("template children: " ++
          toString candidate.physical.tables.templates.children.length)
        IO.println ("premise roots: " ++
          toString candidate.physical.tables.premiseRoots.length)
        IO.println ("profile sha256: " ++
          candidate.physical.recordedProfileDigest)
        IO.println ("source sha256: " ++
          candidate.physical.recordedSourceDigest)
        IO.println "negative first-fingerprint mutation: rejected"
        pure 0

def _root_.main (arguments : List String) : IO UInt32 :=
  match arguments with
  | [sourcePath, profilePath, projectedSourcePath] =>
      run sourcePath profilePath projectedSourcePath
  | _ => do
      IO.eprintln usage
      pure 64

end Mettapedia.OSLF.Tools.QualifyM0GCGeneratedProfile
