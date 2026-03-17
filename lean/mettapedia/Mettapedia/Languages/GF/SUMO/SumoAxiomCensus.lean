/-
# SUMO Axiom Census — Per-Concept Usage BinaryEvidence

For each concept flagged by SumoRepairRunner as disagreeing between SUMO KIF,
Enache's GF encoding, and our Lean encoding, this module records:
- How the concept is used in SUMO axioms (process-like, attribute-like, relation-like)
- What concepts it is used alongside (similarity peers)
- What Enache decided and why
- What the causal/semantic role is

This evidence feeds into the RepairLog decisions.

## BinaryEvidence Source Key
- Merge.kif lines cited directly
- Mid-level-ontology.kif (MLO) lines cited directly
- emotion.kif, FOET seed ontology lines cited where applicable
- "axiom census" = grep of (instance ?X Concept) and similar patterns
-/

import Mettapedia.Languages.GF.Core

namespace Mettapedia.Languages.GF.SUMO.AxiomCensus

/-- A single usage of a concept in a SUMO axiom. -/
structure AxiomUsage where
  source : String        -- "Merge.kif:1234" or "MLO:5678"
  pattern : String       -- the axiom pattern, e.g., "(instance ?X Pain)"
  usageType : String     -- "process-like" | "attribute-like" | "relation-like" | "class-decl"
  note : String          -- explanation
  deriving Repr

/-- Full usage evidence for a flagged concept. -/
structure ConceptEvidence where
  concept : String
  flagType : String                -- from RepairRunner: "MISSING_GF", "FLATTENED", etc.
  usages : List AxiomUsage
  similarityPeers : List String    -- concepts used alongside in axioms
  enacheDecision : Option String   -- what Enache did (if applicable)
  causalRole : Option String       -- "cause" | "effect" | "neutral" | "meta"
  recommendation : String          -- our recommendation
  automatable : Bool               -- can the recommendation be automated?
  deriving Repr

instance : ToString ConceptEvidence where
  toString e :=
    let peers := String.intercalate ", " e.similarityPeers
    s!"[{e.flagType}] {e.concept}\n" ++
    s!"  Usages: {e.usages.length} ({e.usages.map AxiomUsage.usageType})\n" ++
    s!"  Peers: {peers}\n" ++
    s!"  Enache: {e.enacheDecision.getD "—"}\n" ++
    s!"  Causal: {e.causalRole.getD "—"}\n" ++
    s!"  Recommendation: {e.recommendation}\n" ++
    s!"  Automatable: {e.automatable}\n"

/-! ## BinaryEvidence for Flagged Concepts -/

def flaggedConceptEvidence : List ConceptEvidence :=
  [
    -- ═══════════════════════════════════════════════════════════════
    -- MISSING_GF: Relation (S0)
    -- ═══════════════════════════════════════════════════════════════
    { concept := "Relation"
    , flagType := "MISSING_GF"
    , usages :=
        [ { source := "Merge.kif:2194"
          , pattern := "(subclass Relation Abstract)"
          , usageType := "class-decl"
          , note := "Top-level declaration" }
        , { source := "Merge.kif:2196-2250"
          , pattern := "(domain Relation N Class) etc."
          , usageType := "relation-like"
          , note := "Used to define domain/range constraints on other relations" }
        , { source := "Merge.kif:2593"
          , pattern := "(subclass InheritableRelation Relation)"
          , usageType := "class-decl"
          , note := "Parent for InheritableRelation" }
        ]
    , similarityPeers := ["Predicate", "Function", "InheritableRelation",
                          "SingleValuedRelation", "BinaryRelation"]
    , enacheDecision := some "Not encoded as class. Relations are GF formula-level constructors."
    , causalRole := some "meta"
    , recommendation := "Accept Enache's design: Relation hierarchy is part of " ++
        "GF's type system, not an ontological class to be classified. " ++
        "Our encoding adds it for completeness but it's structural, not semantic."
    , automatable := true }

    -- ═══════════════════════════════════════════════════════════════
    -- MISSING_GF: AutonomousAgent (S1)
    -- ═══════════════════════════════════════════════════════════════
  , { concept := "AutonomousAgent"
    , flagType := "MISSING_GF"
    , usages :=
        [ { source := "Merge.kif:1591"
          , pattern := "(subclass AutonomousAgent Object)"
          , usageType := "class-decl"
          , note := "Intermediate level between Object and SentientAgent" }
        , { source := "Merge.kif:1593-1599"
          , pattern := "(=> (instance ?X AutonomousAgent) (exists (?Y) ...))"
          , usageType := "process-like"
          , note := "AutonomousAgent implies the entity has beliefs/desires — used " ++
              "in the definition of agent autonomy" }
        , { source := "Merge.kif:2469"
          , pattern := "(domain agent 2 AutonomousAgent)"
          , usageType := "relation-like"
          , note := "Second argument of `agent` relation must be AutonomousAgent" }
        , { source := "FOET:1147"
          , pattern := "(subclass VirtuousAgent AutonomousAgent)"
          , usageType := "class-decl"
          , note := "FOET ethics concepts inherit from AutonomousAgent" }
        ]
    , similarityPeers := ["SentientAgent", "CognitiveAgent", "Agent", "Object",
                          "GeopoliticalArea", "Organization", "Group"]
    , enacheDecision := some "Skipped entirely. SentientAgent → Agent (= Object) directly."
    , causalRole := some "neutral"
    , recommendation := "Keep in our encoding. AutonomousAgent is the correct domain for " ++
        "`agent` relation (Merge.kif:2469), for FOET VirtuousAgent/ViciousAgent parents, " ++
        "and for GeopoliticalArea/Organization/Group multi-inheritance. " ++
        "Enache's omission caused the `agent` relation domain to be too broad."
    , automatable := false }

    -- ═══════════════════════════════════════════════════════════════
    -- FLATTENED: SentientAgent (S1)
    -- ═══════════════════════════════════════════════════════════════
  , { concept := "SentientAgent"
    , flagType := "FLATTENED"
    , usages :=
        [ { source := "Merge.kif:1601"
          , pattern := "(subclass SentientAgent AutonomousAgent)"
          , usageType := "class-decl"
          , note := "KIF: SentientAgent ⊂ AutonomousAgent" }
        , { source := "Merge.kif:1603-1609"
          , pattern := "(=> (instance ?X SentientAgent) ...feelings...)"
          , usageType := "attribute-like"
          , note := "SentientAgent implies capacity for feelings/sensations" }
        ]
    , similarityPeers := ["CognitiveAgent", "AutonomousAgent", "Animal", "Human"]
    , enacheDecision := some "Placed under Agent (= Object), skipping AutonomousAgent."
    , causalRole := some "neutral"
    , recommendation := "Our encoding is correct: SentientAgent ⊂ AutonomousAgent " ++
        "as per KIF. The flattening in GF loses the AutonomousAgent/SentientAgent " ++
        "distinction that FOET needs."
    , automatable := true }

    -- ═══════════════════════════════════════════════════════════════
    -- MISSING_GF: Predicate / Function / InheritableRelation (S1)
    -- ═══════════════════════════════════════════════════════════════
  , { concept := "Predicate"
    , flagType := "MISSING_GF"
    , usages :=
        [ { source := "Merge.kif:3378-3379"
          , pattern := "(subclass Predicate Relation) (subclass Predicate InheritableRelation)"
          , usageType := "class-decl"
          , note := "Multi-inheritance: Relation + InheritableRelation" }
        , { source := "Merge.kif:3381ff"
          , pattern := "(subclass BinaryPredicate Predicate)"
          , usageType := "class-decl"
          , note := "Parent for arity-specific predicates" }
        ]
    , similarityPeers := ["Relation", "Function", "BinaryPredicate", "TernaryPredicate"]
    , enacheDecision := some "Not encoded as class. Same as Relation."
    , causalRole := some "meta"
    , recommendation := "Accept: Predicate, Function, InheritableRelation are meta-level " ++
        "concepts about the structure of relations, not domain objects. " ++
        "Encoding them as classes in our hierarchy is for completeness only."
    , automatable := true }

  , { concept := "Function"
    , flagType := "MISSING_GF"
    , usages :=
        [ { source := "Merge.kif:3389-3390"
          , pattern := "(subclass Function SingleValuedRelation) (subclass Function InheritableRelation)"
          , usageType := "class-decl"
          , note := "Multi-inheritance" }
        ]
    , similarityPeers := ["Predicate", "SingleValuedRelation", "UnaryFunction", "BinaryFunction"]
    , enacheDecision := some "Not encoded as class."
    , causalRole := some "meta"
    , recommendation := "Accept: same as Predicate."
    , automatable := true }

  , { concept := "InheritableRelation"
    , flagType := "MISSING_GF"
    , usages :=
        [ { source := "Merge.kif:2593"
          , pattern := "(subclass InheritableRelation Relation)"
          , usageType := "class-decl"
          , note := "Distinguishes relations inherited by subclasses" }
        ]
    , similarityPeers := ["Relation", "Predicate", "Function"]
    , enacheDecision := some "Not encoded."
    , causalRole := some "meta"
    , recommendation := "Accept: meta-level concept."
    , automatable := true }

    -- ═══════════════════════════════════════════════════════════════
    -- TOO_TIGHT: attribute relation
    -- ═══════════════════════════════════════════════════════════════
  , { concept := "attribute (relation)"
    , flagType := "TOO_TIGHT"
    , usages :=
        [ { source := "Merge.kif:1754-1755"
          , pattern := "(domain attribute 1 Object) (domain attribute 2 Attribute)"
          , usageType := "relation-like"
          , note := "KIF declares domain 1 as Object, not Agent" }
        , { source := "usage census"
          , pattern := "Most uses: (attribute ?AGENT some-attr)"
          , usageType := "attribute-like"
          , note := "Commonly used with agents, but domain allows any Object" }
        , { source := "MLO:various"
          , pattern := "(attribute ?OBJ Male), (attribute ?REGION Climate)"
          , usageType := "attribute-like"
          , note := "Used with non-agent Objects too: regions, artifacts, organisms" }
        ]
    , similarityPeers := ["property", "manner", "instance"]
    , enacheDecision := some "El Object → El Attribute → Formula (matches KIF)"
    , causalRole := some "neutral"
    , recommendation := "FIXED: Changed from El_Agent to El_Object to match KIF " ++
        "domain declaration. Our previous narrowing was incorrect."
    , automatable := true }

    -- ═══════════════════════════════════════════════════════════════
    -- TOO_TIGHT: contraryAttribute relation
    -- ═══════════════════════════════════════════════════════════════
  , { concept := "contraryAttribute (relation)"
    , flagType := "TOO_TIGHT"
    , usages :=
        [ { source := "Merge.kif:448"
          , pattern := "(instance contraryAttribute VariableArityRelation)"
          , usageType := "relation-like"
          , note := "SUMO declares variable arity" }
        , { source := "Merge.kif:449"
          , pattern := "(instance contraryAttribute Predicate)"
          , usageType := "relation-like"
          , note := "Also a Predicate (generic, not BinaryPredicate)" }
        , { source := "emotion.kif:1071"
          , pattern := "(contraryAttribute Pleasure Pain)"
          , usageType := "attribute-like"
          , note := "Binary use — the Pain/Attribute witness" }
        , { source := "Merge.kif:various"
          , pattern := "(contraryAttribute Hot Warm Cold)"
          , usageType := "attribute-like"
          , note := "Ternary use — temperature scale with three contrary values" }
        ]
    , similarityPeers := ["exhaustiveAttribute", "disjointDecomposition"]
    , enacheDecision := some "[El Attribute] -> Formula (variable-arity list type in GF)"
    , causalRole := some "neutral"
    , recommendation := "Known simplification: we encode as binary. Full encoding " ++
        "would require GF list types. The binary encoding is sufficient for the " ++
        "Pain/Attribute detection but misses ternary+ cases. Document as limitation."
    , automatable := true }

    -- ═══════════════════════════════════════════════════════════════
    -- SILENT_REPAIR: Pain (from RepairLog, not in runner because
    -- Pain is an individual, not a class — but adding here for
    -- completeness of the census)
    -- ═══════════════════════════════════════════════════════════════
  , { concept := "Pain (individual)"
    , flagType := "SILENT_REPAIR"
    , usages :=
        [ { source := "MLO:21097"
          , pattern := "(subclass Pain PathologicProcess)"
          , usageType := "process-like"
          , note := "SUMO's own taxonomy: Pain IS-A PathologicProcess" }
        , { source := "MLO:6724"
          , pattern := "(instance ?P1 Pain) (located ?P1 ?H)"
          , usageType := "process-like"
          , note := "Pain has spatial location (process-like)" }
        , { source := "MLO:7285"
          , pattern := "(rangeSubclass PainFn Pain)"
          , usageType := "process-like"
          , note := "PainFn returns subclasses of Pain" }
        , { source := "MLO:21098-21102"
          , pattern := "(instance ?P1 Pain) (WhenFn ?P1)"
          , usageType := "process-like"
          , note := "Pain has temporal extent (WhenFn)" }
        , { source := "MLO:various"
          , pattern := "(instance ?P1 Pain) (experiencer ?P1 ?A)"
          , usageType := "process-like"
          , note := "Pain has an experiencer (process-like)" }
        , { source := "emotion.kif:1071"
          , pattern := "(contraryAttribute Pleasure Pain)"
          , usageType := "attribute-like"
          , note := "contraryAttribute expects Attribute arguments — only Attribute-like use" }
        ]
    , similarityPeers := ["Pleasure", "Anger", "Fear", "Happiness", "EmotionalState"]
    , enacheDecision := some ("Silent reclassification: Pain : Ind EmotionalState " ++
        "(MidLevelOntology.gf:4402). Moved from Process branch to Attribute branch.")
    , causalRole := some "effect"
    , recommendation := "Enache's reclassification is defensible: Pain is a sensation " ++
        "(effect of PathologicProcess), not the process itself. However, this was " ++
        "undocumented. Our encoding faithfully follows SUMO (Process) and detects " ++
        "the conflict automatically. Recommended: split Pain into PainProcess (Process) " ++
        "and PainSensation (EmotionalState)."
    , automatable := false }
  ]

/-! ## Census Summary -/

#eval! do
  IO.println "=== AXIOM CENSUS SUMMARY ==="
  IO.println ""
  IO.println s!"Flagged concepts analyzed: {flaggedConceptEvidence.length}"
  IO.println ""

  let automatable := flaggedConceptEvidence.filter fun (e : ConceptEvidence) => e.automatable
  let manual := flaggedConceptEvidence.filter fun (e : ConceptEvidence) => !e.automatable
  IO.println s!"Fully automatable recommendations: {automatable.length}"
  IO.println s!"Requires human judgment: {manual.length}"
  IO.println ""

  for e in flaggedConceptEvidence do
    IO.println (toString e)

  IO.println "=== AUTOMATION SUMMARY ==="
  IO.println ""
  IO.println "Automatable (rule-based):"
  for e in automatable do
    IO.println s!"  {e.concept}: {e.recommendation.take 60}..."
  IO.println ""
  IO.println "Requires judgment:"
  for e in manual do
    IO.println s!"  {e.concept}: {e.recommendation.take 60}..."

end Mettapedia.Languages.GF.SUMO.AxiomCensus
