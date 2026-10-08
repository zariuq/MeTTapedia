import Mettapedia.GSLT.LanguageDef.ModuleFormat.Envelope
import Mettapedia.GSLT.LanguageDef.ExtensionComposition

/-!
# Module envelopes as a compositional coGSLT

A declaration is a structured `module/1` value. Bundle equations and ordered
concatenation come from the existing declaration-document GSLT. Elaboration
uses the partial envelope decoder; malformed declarations fail the entire
bundle. Combining authored modules does not certify dependency resolution or
export-language execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition

abbrev Document := DeclarationDocument Value

def elaborateDocument? (limits : Limits) (document : Document) :
    Option (List (Module limits)) := document.values.mapM (decode? limits)

def quoteModules (limits : Limits) (modules : List (Module limits)) : Document :=
  .bundle ((modules.map fun module => encodeRaw module.val).map .declaration)

@[simp] theorem elaborate_quoteModules (limits : Limits)
    (modules : List (Module limits)) :
    elaborateDocument? limits (quoteModules limits modules) = some modules := by
  unfold elaborateDocument? quoteModules
  rw [DeclarationDocument.values_bundle_map]
  exact mapM_encode_decode (fun module => encodeRaw module.val) (decode? limits)
    modules (fun module _ => decode_encode limits module)

/-- The existing compositional-elaboration interface, instantiated by the
actual partial envelope decoder rather than a total structural isomorphism. -/
def moduleSystem (limits : Limits) : GSLT.CompositionalElaboration (List (Module limits)) where
  authoring := ExactDeclarationCodec.documentCompositional Value
  elaboration := {
    elaborate := elaborateDocument? limits
    quote := quoteModules limits
    elaborate_quote := elaborate_quoteModules limits
    equation := by
      intro first second equivalent
      change first.values = second.values at equivalent
      unfold elaborateDocument?
      rw [equivalent]
    rewrite := by
      intro first second impossible
      exact False.elim impossible }
  emptyPayload := []
  merge := fun first second => some (first ++ second)
  elaborate_empty := by
    change elaborateDocument? limits (.bundle []) = some []
    simp [elaborateDocument?, DeclarationDocument.values, DeclarationDocument.valuesList]
  elaborate_append := by
    intro first second
    change Document at first second
    change elaborateDocument? limits (.bundle [first, second]) = _
    simp [elaborateDocument?, DeclarationDocument.values,
      DeclarationDocument.valuesList]

/-- Module declaration payloads attach over any existing core without
changing that core. Further export admission may depend on the core. -/
def moduleLayer (Base : Type) (limits : Limits) : CompositionalLayer Base where
  Fiber := fun _ => List (Module limits)
  system := fun _ => moduleSystem limits

/-- This is the established coGSLT interface, obtained from the established
compositional layer; no parallel extension framework is introduced. -/
def moduleCoGSLT (Base : Type) (limits : Limits) : CoGSLTLayer Base :=
  (moduleLayer Base limits).toCoGSLTLayer

/-- The payload merge is forced by the authored bundle law. -/
theorem module_merge (limits : Limits) (first second : List (Module limits)) :
    (moduleSystem limits).toPartialMonoid.op first second = some (first ++ second) := rfl

theorem elaborateDocument_append (limits : Limits) (first second : Document) :
    elaborateDocument? limits (.bundle [first, second]) =
      (elaborateDocument? limits first).bind fun left =>
        (elaborateDocument? limits second).bind fun right => some (left ++ right) :=
  (moduleSystem limits).elaborate_append first second

/-- Failed frame admission cannot be hidden by a surrounding bundle. -/
theorem append_rejected_left (limits : Limits) (first second : Document)
    (rejected : elaborateDocument? limits first = none) :
    elaborateDocument? limits (.bundle [first, second]) = none := by
  have law := elaborateDocument_append limits first second
  rw [law, rejected]
  rfl

/-- Failed frame admission on the right also rejects the complete bundle. -/
theorem append_rejected_right (limits : Limits) (first second : Document)
    (rejected : elaborateDocument? limits second = none) :
    elaborateDocument? limits (.bundle [first, second]) = none := by
  have law := elaborateDocument_append limits first second
  rw [law, rejected]
  cases elaborateDocument? limits first <;> rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat
