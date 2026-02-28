/-!
# DocText Policy

Canonical ownership for repository prose generation:

- All README/document AST + GF-English generation modules must live under
  `Mettapedia/DocText/`.
- `Mettapedia/Languages/GF/Examples/*Readme*` may exist only as compatibility shims
  importing `Mettapedia.DocText.*`.
- Natural-language claims should be generated compositionally via GF helpers.
- Ordinary declarative prose must be emitted from GF claim renderers (`render*Claim`).
- Headings are English and must be generated from a module-local GF heading renderer
  (`render*Heading`) with parse-back checks.
- In README trees, typed technical blocks are restricted:
  - `syntaxItems` are allowed for symbolic patterns.
  - `codeBlock` and `pathItems` are allowed for non-English technical literals.
  - `apiItems` are allowed only for identifier/member inventories (no prose fallback).
    If an item is not essentially a proper noun/identifier, it must be GF-generated
    as a claim (`render*Claim`) instead.
- Generic `.bulletItem` / `.bulletList` should not be used for prose-bearing content.

This file is normative guidance for AI agent work in this repository.
-/

namespace Mettapedia.DocText.Policy

/-- Canonical root for README/document AST + generation code. -/
def canonicalRoot : String := "Mettapedia/DocText/"

/-- Allowed non-claim technical block classes in compositional README trees. -/
def allowedTechnicalBlocks : List String :=
  [ "code_block"
  , "path_items"
  , "api_items"
  , "syntax_items"
  ]

/-- Heading policy: heading lines must be emitted by GF heading renderers. -/
def headingPolicy : String :=
  "headings_must_be_gf_generated"

/-- Non-canonical legacy path retained only for shims. -/
def legacyShimRoot : String := "Mettapedia/Languages/GF/Examples/"

#eval s!"DocText canonical root: {canonicalRoot}"

end Mettapedia.DocText.Policy
