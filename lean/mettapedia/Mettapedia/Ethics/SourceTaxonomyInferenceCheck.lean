import Mettapedia.Ethics.SourceTaxonomyInference

/-!
# Executable certified-taxonomy check for the Formal Ethics source

The checker decodes one SUO-KIF file into taxonomy facts and replays the two
certificates from `SourceTaxonomyInference`.  It also requires rejection of a
reversed source leaf.  Structural and declaration errors remain fatal, so a
certificate cannot conceal a malformed input file.
-/

set_option autoImplicit false

open Mettapedia.Languages.KIF
open Mettapedia.Languages.KIF.TaxonomyInference

namespace Mettapedia.Ethics.SourceTaxonomyInferenceCheck

open SourceTaxonomyInference

def subclassFactCount (facts : List SourceFact) : Nat :=
  (facts.filter fun
    | .subclass _ _ => true
    | .instance _ _ => false).length

def instanceFactCount (facts : List SourceFact) : Nat :=
  (facts.filter fun
    | .subclass _ _ => false
    | .instance _ _ => true).length

def containsEvery (facts required : List SourceFact) : Bool :=
  required.all facts.contains

unsafe def checkFile (path : String) : IO UInt32 := do
  let source ← IO.FS.readFile path
  match lex source with
  | .error failure =>
      IO.eprintln s!"lexical error: {repr failure}"
      return 1
  | .ok lexed =>
      let parsed := parse lexed
      let inventory := declarationInventory parsed
      let facts := factsFromDeclarations inventory.declarations
      let targetLeavesPresent := containsEvery facts targetCenteredRequiredFacts
      let kdtLeavesPresent := containsEvery facts kdtRequiredFacts
      let targetAccepted :=
        targetCenteredEthicalCertificate.valid (taxonomyRuleWitness facts)
      let kdtAccepted := kdtEthicalCertificate.valid (taxonomyRuleWitness facts)
      let reverseAccepted :=
        reversedTargetCenteredLeaf.valid (taxonomyRuleWitness facts)
      IO.println s!"top-level forms: {parsed.forms.length}"
      IO.println s!"structural errors: {parsed.errors.length}"
      for failure in parsed.errors do
        IO.eprintln s!"structural error: {repr failure}"
      IO.println s!"declaration errors: {inventory.errors.length}"
      for failure in inventory.errors do
        IO.eprintln s!"declaration error: {repr failure}"
      IO.println s!"decoded taxonomy facts: {facts.length}"
      IO.println s!"decoded subclass facts: {subclassFactCount facts}"
      IO.println s!"decoded instance facts: {instanceFactCount facts}"
      IO.println s!"target-centered source leaves present: {targetLeavesPresent}"
      IO.println s!"target-centered -> ethical certificate accepted: {targetAccepted}"
      IO.println s!"KDT source leaves present: {kdtLeavesPresent}"
      IO.println s!"KDT -> ethical certificate accepted: {kdtAccepted}"
      IO.println s!"reversed source leaf accepted: {reverseAccepted}"
      return if parsed.errors.isEmpty && inventory.errors.isEmpty &&
          targetLeavesPresent && kdtLeavesPresent && targetAccepted &&
          kdtAccepted && !reverseAccepted then 0 else 1

end Mettapedia.Ethics.SourceTaxonomyInferenceCheck

unsafe def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] => Mettapedia.Ethics.SourceTaxonomyInferenceCheck.checkFile path
  | _ =>
      IO.eprintln "usage: ethics-source-taxonomy-check <source.kif>"
      return 2
