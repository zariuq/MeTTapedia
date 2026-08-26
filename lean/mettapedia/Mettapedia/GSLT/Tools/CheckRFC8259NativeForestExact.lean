import Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT
import Mettapedia.GSLT.Parsing.ClassAwareGroundedChart
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestWire

/-!
# Root-relative completeness check for an RFC 8259 native forest

This opt-in executable resolves the physical identities emitted beside a
native ParserPack forest against the independently authored RFC 8259 plan,
then runs the exhaustive two-sided validator for the exported physical
choices. Neither packet can authorize the other: malformed, noncanonical,
absent, or ambiguous identity rows are rejected before semantic validation.

The second gate computes an independent finite grounded chart from the
supplied RFC profile, ParserPack plan, and scalar input, prunes it from the
whole-input root, and checks that every live physical family occurs in the
decoded native forest.  Passing supplies the `RootParserComplete`
backward-lift obligation without requiring irrelevant local saturation.
-/

namespace Mettapedia.GSLT.Tools.CheckRFC8259NativeForestExact

open Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT
open Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT
open Mettapedia.GSLT.Parsing.ClassAwareGroundedChart
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestParserCompleteness

abbrev IdentitySnapshot :=
  Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityWire.Snapshot
abbrev ForestSnapshot :=
  Mettapedia.GSLT.Parsing.ClassAwareNativeForestWire.Snapshot

private def usage : String :=
  "usage: CheckRFC8259NativeForestExact backend identities.pni1 forest.cnf1"

private def canonicalIdentitySnapshot? (bytes : List UInt8) :
    Option IdentitySnapshot := do
  let snapshot <-
    Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityWire.decodeSnapshot?
      bytes
  if Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityWire.encodeSnapshot
      snapshot = bytes then some snapshot else none

private def canonicalForestSnapshot? (bytes : List UInt8) :
    Option ForestSnapshot := do
  let snapshot <-
    Mettapedia.GSLT.Parsing.ClassAwareNativeForestWire.decodeSnapshot? bytes
  if Mettapedia.GSLT.Parsing.ClassAwareNativeForestWire.encodeSnapshot
      snapshot = bytes then some snapshot else none

def run (args : List String) : IO UInt32 := do
  match args with
  | [backend, identityPath, forestPath] =>
      let identityBytes <- IO.FS.readBinFile identityPath
      let forestBytes <- IO.FS.readBinFile forestPath
      match canonicalIdentitySnapshot? identityBytes.data.toList with
      | none =>
          IO.eprintln
            "ParserPack identity snapshot is not a canonical PNI1 packet"
          pure 1
      | some identitySnapshot =>
          match canonicalForestSnapshot? forestBytes.data.toList with
          | none =>
              IO.eprintln
                "native forest snapshot is not a canonical CNF1 packet"
              pure 1
          | some forestSnapshot =>
              match forestSnapshot.completedView? with
              | none =>
                  IO.eprintln
                    "native forest snapshot is not a completed semantic view"
                  pure 1
              | some view =>
                  if validateResolvedReferenceCompleteRepresentation
                      identitySnapshot view rfc8259ParserProfile
                      rfc8259ParserPackPlan then
                    IO.println s!"(RFC8259NativeForestParserCompleteSummary {backend} {view.nodes.length} {view.choices.length} {view.roots.length} {identitySnapshot.productions.length})"
                    pure 0
                  else
                    match identitySnapshot.resolveInventory?
                        rfc8259ParserPackPlan with
                    | none =>
                        IO.eprintln
                          "native semantic identities do not resolve uniquely"
                    | some inventory =>
                        if Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyCompleteness.validateExactFamilyRepresentation
                            view inventory rfc8259ParserProfile
                            rfc8259ParserPackPlan then
                          let target := decodedForestData view inventory
                            rfc8259ParserProfile
                          let reference := referenceForest rfc8259ParserProfile
                            rfc8259ParserPackPlan view.codepoints
                          let missingRoots := reference.roots.filter
                            fun root => !(root ∈ target.roots)
                          let missingFamilies := reference.families.filter
                            fun family => !(family ∈ target.families)
                          IO.eprintln s!"native forest is internally exact but omits live root-relative reference data: missing roots={missingRoots.length}, families={missingFamilies.length}"
                          match missingRoots.head? with
                          | some root => IO.eprintln s!"first missing root: {repr root}"
                          | none => pure ()
                          match missingFamilies.head? with
                          | some family => IO.eprintln s!"first missing family: {repr family}"
                          | none => pure ()
                        else
                          IO.eprintln
                            "native identities and choices are not internally exact"
                    pure 1
  | _ =>
      IO.eprintln usage
      pure 1

end Mettapedia.GSLT.Tools.CheckRFC8259NativeForestExact

def main (args : List String) : IO UInt32 :=
  Mettapedia.GSLT.Tools.CheckRFC8259NativeForestExact.run args
