/-
# GFCore.ConceptId — Grounded concept identifiers

Replaces bare `GroundedLexeme` with concept IDs grounded in
WordNet synsets, SUMO types, and Wikidata QIDs.

Matching prefers synset-level identity over string comparison.
-/

namespace GFCore

/-- A grounded concept identifier.
    Links a GF function name to external knowledge bases. -/
structure ConceptId where
  gfFun    : String                -- "star_8_N" (GF abstract function name)
  cat      : String                -- "N" (GF category)
  synset?  : Option String := none -- "02514825-n" (WordNet synset ID)
  sumoType?: Option String := none -- "Star" (SUMO class)
  qid?     : Option String := none -- "Q523" (Wikidata QID)
  gloss?   : Option String := none -- "a celestial body of hot gases"
  deriving Repr, DecidableEq, BEq, Inhabited

namespace ConceptId

/-- Human-readable base name: strip sense number and category suffix.
    "star_8_N" → "star", "produce_6_V2" → "produce" -/
def baseName (c : ConceptId) : String :=
  let parts := c.gfFun.splitOn "_"
  if parts.length ≥ 3 then
    String.intercalate "_" (parts.take (parts.length - 2))
  else if parts.length == 2 then
    parts[0]!
  else c.gfFun

/-- Concept identity: synset match OR baseName match.
    Synset agreement is definitive identity.
    BaseName match is fallback — GF parse may pick wrong sense,
    so synset disagreement does NOT reject baseName match.
    Council (de Paiva): "Without WSD, baseName is our best handle." -/
def sameAs (a b : ConceptId) : Bool :=
  match a.synset?, b.synset? with
  | some s1, some s2 => s1 == s2 || a.baseName == b.baseName
  | _, _ => a.baseName == b.baseName

/-- Variable-aware matching: `?`-prefixed gfFun matches anything. -/
def matchesUnify (a b : ConceptId) : Bool :=
  a.gfFun.startsWith "?" || b.gfFun.startsWith "?" || a.sameAs b

/-- Create from a GF function name and category (no grounding yet). -/
def fromGF (gfFun cat : String) : ConceptId :=
  { gfFun, cat }

/-- Create with synset grounding. -/
def grounded (gfFun cat synset : String) : ConceptId :=
  { gfFun, cat, synset? := some synset }

end ConceptId

end GFCore
