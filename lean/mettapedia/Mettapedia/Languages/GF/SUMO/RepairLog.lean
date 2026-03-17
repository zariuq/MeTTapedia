/-
# SUMO Repair Decision Log

Semi-formal record of classification judgments made during SUMO → SUMO-GF
encoding. Each decision records:
- What was decided
- What evidence supports it
- What evidence contradicts it
- Whether it could have been automated
- What canary theorems verify the choice

## Format

Each `RepairDecision` is a Lean structure that can be:
1. Queried programmatically (e.g., "show all decisions with confidence < 0.7")
2. Exported to JSON for external review
3. Used to generate canary theorem stubs
4. Audited by comparing evidence counts

## Automation Strategy

For each concept requiring a classification judgment:
1. **Axiom usage census**: Count how the concept is used in SUMO axioms
   - Process-like: `instance`, `located`, `WhenFn`, `agent`, `patient`, `causes`
   - Attribute-like: `attribute`, `contraryAttribute`, `property`, `manner`
   - Relation-like: `domain`, `range`, `subrelation`
2. **Literature evidence**: Search commonsense KBs (ConceptNet, WordNet) for
   the concept's typical classification
3. **Causal analysis**: If X is used as Y but *causes* Z, then X might be
   better classified by its causal role (e.g., Pain causes suffering → Pain
   is a sensation/attribute, not a process itself)
4. **Consistency check**: After reclassification, do ALL axioms using the
   concept still type-check? If not, which ones break?

## Key Insight

Axiom usage census alone can be MISLEADING. Pain has 5 Process-like uses
vs 1 Attribute-like use, but the Process-like uses describe the *experience*
of pain (temporal, located), which is really about the sensation (Attribute).
The deeper judgment is: Pain IS-A sensation that IS-CAUSED-BY a process.

Literature evidence and causal analysis break the tie that raw counts can't.
-/

import Mettapedia.Languages.GF.Core
import Mettapedia.Languages.GF.SUMO.EvidenceModel
import Mettapedia.Languages.GF.SUMO.DocEvidence

namespace Mettapedia.Languages.GF.SUMO.RepairLog

/-- A single piece of evidence for or against a classification. -/
structure EvidenceItem where
  source : String          -- e.g., "Mid-level-ontology.kif:6724"
  axiomPattern : String    -- e.g., "(instance ?P1 Pain)"
  supportsClass : String   -- e.g., "Process" or "Attribute"
  strength : String        -- "strong", "moderate", "weak"
  note : String            -- free-form explanation
  deriving Repr

/-- Repair status: tracks whether a logged decision has been applied. -/
inductive RepairStatus where
  | logged      -- detected and logged, not yet acted on
  | autoFixable -- sufficient evidence + automatable + confidence ≥ 0.9 → can auto-apply
  | fixed       -- fix applied to KIF and/or Lean encoding
  | wontfix     -- determined to be acceptable / not our problem
  | deferred    -- real issue but blocked on something else
  deriving Repr, BEq

/-- A repair decision with full justification. -/
structure RepairDecision where
  decisionId : Nat                    -- e.g., 1 for D1, 22 for D22
  concept : String                    -- e.g., "Pain"
  originalSUMOClass : String          -- from Merge.kif: "PathologicProcess"
  enacheClass : String                -- Enache's choice: "EmotionalState"
  ourClass : String                   -- our current choice
  recommendedClass : String           -- after analysis
  evidenceFor : List EvidenceItem     -- supports recommended
  evidenceAgainst : List EvidenceItem -- contradicts recommended
  automatable : Bool                  -- could this be fully automated?
  automationMethod : String           -- how to automate (if possible)
  canaryTheorems : List String        -- theorems that verify the choice
  confidence : Float                  -- 0.0 to 1.0
  needsSplit : Bool                   -- should concept be split?
  splitProposal : Option (String × String)  -- if split: (name1, name2)
  status : RepairStatus := .logged    -- default: logged but not yet fixed
  -- Repair archetype (determines Beta prior for assurance scoring)
  archetype : EvidenceModel.RepairArchetype := .worldSemanticClaim
  -- BinaryEvidence model fields (persisted WM evidence from SumoNTT audit)
  reviewState : EvidenceModel.ReviewState := .pendingReview
  witnesses : List EvidenceModel.WMWitness := []
  assuranceLower95 : Float := 0.0
  evidenceCompleteness : Float := 0.0
  contradictionMass : Float := 0.0
  reviewers : List String := []
  deriving Repr

/-- Log of all repair decisions. -/
def repairDecisions : List RepairDecision :=
  [
    -- ═══════════════════════════════════════════════════════════════
    -- Decision 1: Pain classification
    -- ═══════════════════════════════════════════════════════════════
    { decisionId := 1
    , concept := "Pain (RESOLVED: EmotionalState)"
    , originalSUMOClass := "PathologicProcess"
    , enacheClass := "EmotionalState"
    , ourClass := "Process"
    , recommendedClass := "EmotionalState (matches Pleasure and 39 peers)"
    , evidenceFor :=
        [ { source := "Merge.kif:448-461"
          , axiomPattern := "(contraryAttribute @ROW) → all elements must be (instance ?E Attribute)"
          , supportsClass := "Attribute"
          , strength := "strong"
          , note := "SUMO's own logical constraint: contraryAttribute demands Attribute. " ++
              "(contraryAttribute Pleasure Pain) at emotion.kif:1071 forces Pain : Attribute." }
        , { source := "IASP 2020 (PMC7680716)"
          , axiomPattern := "'An unpleasant sensory and emotional EXPERIENCE'"
          , supportsClass := "EmotionalState"
          , strength := "strong"
          , note := "IASP calls both pain and pleasure 'sensory and emotional " ++
              "experience' — no distinction between them. Both are affects." }
        , { source := "emotion.kif: similarity-class counting"
          , axiomPattern := "39 EmotionalState peers (Pleasure, Happiness, Anger, " ++
              "FeelingCalm, ...) vs 1 Process outlier (Pain)"
          , supportsClass := "EmotionalState"
          , strength := "strong"
          , note := "All 39 contraryAttribute arguments in emotion.kif are " ++
              "EmotionalState or SubjectiveEmotionalFeeling. Pain is the ONLY " ++
              "one on the Process branch. 39:1 ratio." }
        , { source := "SNOMED CT (PMC10233479)"
          , axiomPattern := "Pain under 'clinical finding', 'sensation quality'"
          , supportsClass := "Attribute"
          , strength := "moderate"
          , note := "Major clinical ontology classifies pain as a finding (state " ++
              "present in patient), not a procedure/process." }
        , { source := "Mid-level-ontology.kif:21098"
          , axiomPattern := "(documentation Pain) says 'A physical SENSATION of discomfort'"
          , supportsClass := "Attribute"
          , strength := "moderate"
          , note := "SUMO's own documentation contradicts its classification: " ++
              "'sensation' is an Attribute-type word." }
        , { source := "Medicine.kif:936,953"
          , axiomPattern := "(attribute ?P Pain) — Pain used as Attribute in SUMO itself"
          , supportsClass := "Attribute"
          , strength := "strong"
          , note := "SUMO's Medicine domain already uses Pain as an Attribute, " ++
              "contradicting the PathologicProcess classification." }
        , { source := "Similarity-class: Pleasure (emotion.kif:1085)"
          , axiomPattern := "(instance Pleasure EmotionalState)"
          , supportsClass := "EmotionalState"
          , strength := "strong"
          , note := "Pain's direct contraryAttribute peer. Pleasure is EmotionalState. " ++
              "Pain should match. Enache made this exact repair (MidLevelOntology.gf:4402)." }
        ]
    , evidenceAgainst :=
        [ { source := "Mid-level-ontology.kif:21097"
          , axiomPattern := "(subclass Pain PathologicProcess)"
          , supportsClass := "Process"
          , strength := "strong"
          , note := "SUMO's own taxonomy declaration — but contradicted by its own " ++
              "documentation, Medicine.kif usage, and contraryAttribute axiom." }
        , { source := "axiom census"
          , axiomPattern := "5 Process-like uses vs 1 Attribute-like use in MLO"
          , supportsClass := "Process"
          , strength := "weak"
          , note := "Raw count misleading: the 5 process-like uses describe the " ++
              "EXPERIENCE of pain (temporal, located), not the biological process. " ++
              "IASP: these are properties of the experience, not evidence of process-hood." }
        , { source := "SUMO WordNet mapping"
          , axiomPattern := "pain%1:26:00 mapped to PathologicProcess"
          , supportsClass := "Process"
          , strength := "weak"
          , note := "WordNet gloss says 'symptom' — a symptom is something experienced " ++
              "(Attribute-like), despite the formal mapping to Process." }
        ]
    , automatable := true
    , automationMethod := "Similarity-class counting: 39 EmotionalState peers in " ++
        "emotion.kif (Pleasure, Happiness, Anger, FeelingCalm, ...) all use " ++
        "contraryAttribute and are all EmotionalState. Pain is the ONLY " ++
        "contraryAttribute argument NOT on the Attribute branch. 39:1 ratio. " ++
        "IASP 2020 calls both pain and pleasure 'sensory and emotional experience'. " ++
        "Pleasure is already EmotionalState in SUMO — Pain should match. " ++
        "Enache made this exact repair silently. We make it explicitly with evidence."
    , canaryTheorems :=
        [ "contraryAttribute(Pleasure, Pain) must type-check"
        , "RelievingPain axiom: Pain instances have location and temporal extent"
        , "PainFn returns subclasses of Pain (BodyPart → Pain subclass)"
        ]
    , confidence := 0.92
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    , archetype := .ontologyReclassification
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 2: contraryAttribute arity
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 2
    , concept := "contraryAttribute"
    , originalSUMOClass := "VariableArityRelation"
    , enacheClass := "[El Attribute] -> Formula"
    , ourClass := "El_Attribute → El_Attribute → Formula (binary)"
    , recommendedClass := "[El Attribute] → Formula (variable arity)"
    , evidenceFor :=
        [ { source := "Merge.kif:448"
          , axiomPattern := "(instance contraryAttribute VariableArityRelation)"
          , supportsClass := "VariableArity"
          , strength := "strong"
          , note := "SUMO's own declaration says variable arity" }
        , { source := "Merge.kif:449"
          , axiomPattern := "(instance contraryAttribute Predicate)"
          , supportsClass := "VariableArity"
          , strength := "moderate"
          , note := "Generic Predicate, not BinaryPredicate" }
        , { source := "Enache Merge.gf:5194"
          , axiomPattern := "fun contraryAttribute : [El Attribute] -> Formula"
          , supportsClass := "VariableArity"
          , strength := "strong"
          , note := "Enache's encoding uses GF list type" }
        , { source := "KIF census (2026-02-24)"
          , axiomPattern := "95 total uses: 89 binary, 3 ternary, 3 quaternary"
          , supportsClass := "VariableArity"
          , strength := "strong"
          , note := "6 ternary+ uses confirm variable arity is necessary: " ++
              "Merge.kif:17209 (N/S/E/W), Merge.kif:17745 (Solid/Liquid/Gas/Plasma), " ++
              "Geography.kif:5612 (volcano states), Transportation.kif:391 (gauge types), " ++
              "ComputerInput.kif:2115, ComputingBrands.kif:3122. " ++
              "Binary-only encoding would reject 6 legitimate SUMO axioms." }
        ]
    , evidenceAgainst :=
        [ { source := "usage census (2026-02-24)"
          , axiomPattern := "89/95 uses (93.7%) are binary"
          , supportsClass := "Binary"
          , strength := "weak"
          , note := "Pragmatically mostly binary, but VariableArityRelation " ++
              "declaration and 6 non-binary uses make binary-only encoding wrong" }
        ]
    , automatable := true
    , automationMethod := "Fully automatable: read (instance X VariableArityRelation) " ++
        "declaration and generate list-type signature. " ++
        "Rule: if SUMO says VariableArityRelation, use [El C] → Formula."
    , canaryTheorems :=
        [ "(contraryAttribute Pliable Rigid) must type-check (binary case)"
        , "(contraryAttribute Hot Warm Cold) must type-check (ternary case)"
        ]
    , confidence := 0.95
    , needsSplit := false
    , splitProposal := none
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 3: attribute relation domain
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 3
    , concept := "attribute (relation)"
    , originalSUMOClass := "domain 1 Object, domain 2 Attribute"
    , enacheClass := "El Object → El Attribute → Formula"
    , ourClass := "El_Agent → El_Attribute → Formula"
    , recommendedClass := "El Object → El Attribute → Formula"
    , evidenceFor :=
        [ { source := "Merge.kif:1754"
          , axiomPattern := "(domain attribute 1 Object)"
          , supportsClass := "Object"
          , strength := "strong"
          , note := "SUMO's own domain declaration" }
        , { source := "Enache Merge.gf"
          , axiomPattern := "fun attribute : El Object -> El Attribute -> Formula"
          , supportsClass := "Object"
          , strength := "strong"
          , note := "Enache followed SUMO's declaration exactly" }
        ]
    , evidenceAgainst :=
        [ { source := "usage census"
          , axiomPattern := "Most uses: (attribute ?AGENT some-attribute)"
          , supportsClass := "Agent"
          , strength := "moderate"
          , note := "Common usage is with agents, but domain allows any Object" }
        ]
    , automatable := true
    , automationMethod := "Fully automatable: read (domain R N C) declarations " ++
        "from Merge.kif and generate the signature directly. " ++
        "Rule: always trust SUMO's domain declarations for initial typing."
    , canaryTheorems :=
        [ "(attribute SomeObject SomeAttribute) must type-check for any Object"
        , "Soldier class-as-attribute usage must be flagged (Soldier is a class, not instance)"
        ]
    , confidence := 0.9
    , needsSplit := false
    , splitProposal := none
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 4: AutonomousAgent missing from GF
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 4
    , concept := "AutonomousAgent (VERIFIED — must keep)"
    , originalSUMOClass := "Object (Merge.kif:1591)"
    , enacheClass := "(missing — skipped entirely)"
    , ourClass := "Object"
    , recommendedClass := "Object (mandatory: 14 relations demand it)"
    , evidenceFor :=
        [ { source := "Merge.kif:1591"
          , axiomPattern := "(subclass AutonomousAgent Object)"
          , supportsClass := "Object"
          , strength := "strong"
          , note := "KIF declares it as subclass of Object" }
        , { source := "Merge.kif:2469"
          , axiomPattern := "(domain agent 2 AutonomousAgent)"
          , supportsClass := "AutonomousAgent"
          , strength := "strong"
          , note := "The agent relation requires AutonomousAgent, not just Object" }
        , { source := "FOET:1147,1165"
          , axiomPattern := "(subclass VirtuousAgent AutonomousAgent)"
          , supportsClass := "AutonomousAgent"
          , strength := "strong"
          , note := "FOET ethics agents inherit from AutonomousAgent" }
        ]
    , evidenceAgainst :=
        [ { source := "Enache GF"
          , axiomPattern := "SentientAgent directly under Agent"
          , supportsClass := "Agent"
          , strength := "moderate"
          , note := "Simplifies encoding; most uses are with SentientAgent+" }
        ]
    , automatable := true
    , automationMethod := "Fully automatable: grep (domain R N AutonomousAgent) in KIF. " ++
        "14 relations demand AutonomousAgent. If ANY (domain R N X) references X, " ++
        "X must be in the encoding. Enache's omission broke all 14 relation typings."
    , canaryTheorems :=
        [ "agent(P, A) requires A : AutonomousAgent (not just Object)"
        , "VirtuousAgent ⊂ AutonomousAgent must type-check"
        ]
    , confidence := 0.95
    , needsSplit := false
    , splitProposal := none
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 5: SentientAgent hierarchy flattening
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 5
    , concept := "SentientAgent (hierarchy)"
    , originalSUMOClass := "AutonomousAgent"
    , enacheClass := "Agent (= Object)"
    , ourClass := "AutonomousAgent"
    , recommendedClass := "AutonomousAgent (our encoding is correct)"
    , evidenceFor :=
        [ { source := "Merge.kif:1601"
          , axiomPattern := "(subclass SentientAgent AutonomousAgent)"
          , supportsClass := "AutonomousAgent"
          , strength := "strong"
          , note := "KIF's own declaration" }
        , { source := "Merge.kif:1611"
          , axiomPattern := "(subclass CognitiveAgent SentientAgent)"
          , supportsClass := "AutonomousAgent"
          , strength := "strong"
          , note := "CognitiveAgent < SentientAgent < AutonomousAgent chain confirmed" }
        , { source := "KIF usage census (2026-02-24)"
          , axiomPattern := "6 axiom uses of (instance ?AGENT SentientAgent)"
          , supportsClass := "AutonomousAgent"
          , strength := "strong"
          , note := "Merge.kif:13638,18489,18515,18527; MLO:24126,24159. " ++
              "All use SentientAgent in AutonomousAgent-compatible contexts." }
        , { source := "SumoNTT.lean D5 witness"
          , axiomPattern := "reachabilityTest SentientAgent object => .sat"
          , supportsClass := "AutonomousAgent"
          , strength := "strong"
          , note := "NTT confirms SentientAgent reaches Object via " ++
              "AutonomousAgent. Our encoding is correct." }
        , { source := "docGFParsed (2026-02-24)"
          , axiomPattern := "doc(subclass): SentientAgent → AutonomousAgent"
          , supportsClass := "AutonomousAgent"
          , strength := "moderate"
          , note := "GF-parsed doc confirms subclass. KIF-entailed." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Fully automatable: read (subclass X Y) from KIF, " ++
        "verify GF matches. If GF skips an intermediate, flag as flattened."
    , canaryTheorems :=
        [ "SentientAgent ⊂ AutonomousAgent ⊂ Object chain must be complete"
        ]
    , confidence := 0.98
    , needsSplit := false
    , splitProposal := none
    , status := .fixed  -- Our encoding already correct; NTT verified (2026-02-24)
    , reviewState := EvidenceModel.ReviewState.applied
    , reviewers := ["claude_code", "codex"]
    , assuranceLower95 := 0.293293
    , evidenceCompleteness := 0.5
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 6: Relation hierarchy as infrastructure sorts
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 6
    , concept := "Relation/Predicate/Function/InheritableRelation"
    , originalSUMOClass := "Abstract (via Relation)"
    , enacheClass := "(not encoded as classes — formula-level only)"
    , ourClass := "Abstract (via Relation)"
    , recommendedClass := "Accept both: GF formula-level + our class hierarchy"
    , evidenceFor :=
        [ { source := "Enache design"
          , axiomPattern := "Relations are GF type system, not ontological objects"
          , supportsClass := "infrastructure"
          , strength := "strong"
          , note := "Deliberate: GF's dependent types handle relation classification" }
        ]
    , evidenceAgainst :=
        [ { source := "completeness"
          , axiomPattern := "FOET uses Predicate/Function as first-class concepts"
          , supportsClass := "class"
          , strength := "moderate"
          , note := "For NTT extraction, having them as classes helps" }
        ]
    , automatable := true
    , automationMethod := "Rule: if concept is (instance X VariableArityRelation) or " ++
        "(subclass X Relation), check if GF encodes it as Class or Formula-level. " ++
        "Both are valid; document the design choice."
    , canaryTheorems :=
        [ "Predicate hierarchy must be navigable for higher-order axioms"
        ]
    , confidence := 0.85
    , needsSplit := false
    , splitProposal := none
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 7: attribute relation domain (FIXED)
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 7
    , concept := "attribute (domain repair)"
    , originalSUMOClass := "domain 1 Object, domain 2 Attribute"
    , enacheClass := "El Object → El Attribute → Formula"
    , ourClass := "El_Object → El_Attribute → Formula (FIXED from El_Agent)"
    , recommendedClass := "El Object → El Attribute → Formula"
    , evidenceFor :=
        [ { source := "Merge.kif:1754"
          , axiomPattern := "(domain attribute 1 Object)"
          , supportsClass := "Object"
          , strength := "strong"
          , note := "SUMO's own declaration — the authoritative source" }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Fully automatable: read (domain R N C) from KIF, " ++
        "generate signature directly."
    , canaryTheorems :=
        [ "(attribute SomeRegion SomeClimate) must type-check (Region ⊂ Object)"
        ]
    , confidence := 1.0
    , needsSplit := false
    , splitProposal := none
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 8: Transitive closure of coercions
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 8
    , concept := "Coercion transitivity"
    , originalSUMOClass := "(structural — GF inhs rule)"
    , enacheClass := "inhs : Inherits c1 c2 → Inherits c2 c3 → Inherits c1 c3"
    , ourClass := "transitiveClose(sumoSubclassEdges)"
    , recommendedClass := "Full transitive closure (implemented)"
    , evidenceFor :=
        [ { source := "pipeline diagnostic"
          , axiomPattern := "Before: 3 classes reach Object. After: 9 classes."
          , supportsClass := "transitive"
          , strength := "strong"
          , note := "Without closure, ◇ misses most coercion paths" }
        , { source := "pipeline diagnostic"
          , axiomPattern := "Before: 3 classes reach Attribute. After: 13 classes."
          , supportsClass := "transitive"
          , strength := "strong"
          , note := "Full Attribute hierarchy now visible to ◇" }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Fully automatable: compute transitive closure of " ++
        "sumoSubclassEdges. Implemented as transitiveClose in SumoAbstract.lean."
    , canaryTheorems :=
        [ "CognitiveAgent must reach Object (3-step chain)"
        , "VirtueAttribute must reach Entity (5+ step chain)"
        ]
    , confidence := 1.0
    , needsSplit := false
    , splitProposal := none
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 9 (original Decision 4): AsymmetricRelation type assumption
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 9
    , concept := "AsymmetricRelation (cross-type vacuity)"
    , originalSUMOClass := "Higher-order: R → (schema for all instances)"
    , enacheClass := "(c:Class) → (El c → El c → Formula) → Formula (same-type only)"
    , ourClass := "not yet encoded"
    , recommendedClass := "Same-type (3/13): keep axiom, has real content. " ++
        "Cross-type (10/13): OMIT — vacuously true by type disjointness. " ++
        "Prove theorem: disjoint types → asymmetry holds for free."
    , evidenceFor :=
        [ { source := "SumoNTT.lean: crossType_asymmetry_check (verified)"
          , axiomPattern := "4/13 vacuous: range, containsInformation, attribute, manner"
          , supportsClass := "vacuous"
          , strength := "strong"
          , note := "Computationally verified: these 4 have disjoint domain branches. " ++
              "R(y,x) is ill-sorted → asymmetry enforced by types alone." }
        , { source := "SumoNTT.lean: crossType_asymmetry_check (verified)"
          , axiomPattern := "9/13 with content: immediateSubclass, properPart, hole, " ++
              "contains, member, leader, etc."
          , supportsClass := "content"
          , strength := "strong"
          , note := "Same-branch: coercion paths exist between domains, so R(y,x) " ++
              "is well-sorted. Asymmetry axiom adds real information." }
        , { source := "Enache thesis p.25"
          , axiomPattern := "Only 43% of higher-order axioms translated"
          , supportsClass := "correct-omission"
          , strength := "strong"
          , note := "Enache's same-type encoding was CORRECT for cross-type: " ++
              "omitting vacuously true axioms is sound. The 57% 'failure' " ++
              "was actually correct behavior — those axioms add nothing." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "For each (instance R AsymmetricRelation): " ++
        "read (domain R 1 C1), (domain R 2 C2). " ++
        "If BT(C1) ∩ BT(C2) = {Entity} (disjoint branches), omit axiom. " ++
        "If C1 = C2 or BT overlap, keep axiom. " ++
        "Prove: disjoint_branches(C1,C2) → asymmetric(R) vacuously."
    , canaryTheorems :=
        [ "properPart(Obj,Obj): asymmetry axiom must be kept (same-type)"
        , "attribute(Obj,Attr): asymmetry axiom can be omitted (cross-type)"
        , "Theorem: disjoint(BT(C1),BT(C2)) → AsymmetricRelation(R:C1×C2)"
        ]
    , confidence := 0.95
    , needsSplit := false
    , splitProposal := none
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 10: VirtuousAgent instance/class confusion
    -- NTT Gap 2: BT(VirtuousAgent) = {VirtuousAgent, AutonomousAgent,
    --   Object, Physical, Entity} — Attribute ∉ BT(VirtuousAgent)
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 10
    , concept := "VirtuousAgent (instance/class confusion)"
    , originalSUMOClass := "AutonomousAgent (FOET:1147)"
    , enacheClass := "(not in GF — FOET-only concept)"
    , ourClass := "AutonomousAgent"
    , recommendedClass := "AutonomousAgent (keep class). Fix axioms at FOET:4733,4737: " ++
        "unfold (attribute ?A VirtuousAgent) to its FOET:1157 definition: " ++
        "∃V. VirtueAttribute(V) ∧ attribute(?A, V)"
    , evidenceFor :=
        [ { source := "FOET:1147"
          , axiomPattern := "(subclass VirtuousAgent AutonomousAgent)"
          , supportsClass := "AutonomousAgent"
          , strength := "strong"
          , note := "VirtuousAgent is declared as a CLASS of agents" }
        , { source := "Merge.kif:1754"
          , axiomPattern := "(domain attribute 2 Attribute)"
          , supportsClass := "Attribute"
          , strength := "strong"
          , note := "attribute relation arg 2 must be an Attribute instance" }
        , { source := "FOET:4739"
          , axiomPattern := "(instance Pietas VirtueAttribute)"
          , supportsClass := "Attribute"
          , strength := "strong"
          , note := "Correct pattern: Pietas IS an instance of VirtueAttribute. " ++
              "Then (attribute ?AGENT Pietas) is well-typed." }
        , { source := "FOET:4743"
          , axiomPattern := "(attribute ?AGENT Pietas)"
          , supportsClass := "Attribute"
          , strength := "strong"
          , note := "Pietas used correctly as attribute — contrast with VirtuousAgent" }
        , { source := "SumoNTT.lean"
          , axiomPattern := "BT(VirtuousAgent) = {VirtuousAgent, AutonomousAgent, " ++
              "Object, Physical, Entity}"
          , supportsClass := "Object"
          , strength := "strong"
          , note := "NTT gap detection: Attribute ∉ BT(VirtuousAgent). " ++
              "VirtuousAgent is on the Object branch, cannot reach Attribute." }
        ]
    , evidenceAgainst :=
        [ { source := "FOET:4733"
          , axiomPattern := "(attribute ?AGENT VirtuousAgent)"
          , supportsClass := "Attribute"
          , strength := "moderate"
          , note := "FOET uses VirtuousAgent as if it were an Attribute. " ++
              "This is the bug: VirtuousAgent is a Class, not an Attribute instance." }
        , { source := "FOET:4737"
          , axiomPattern := "(holdsObligation (attribute ?AGENT VirtuousAgent) ?AGENT)"
          , supportsClass := "Attribute"
          , strength := "moderate"
          , note := "Same bug used in holdsObligation context." }
        ]
    , automatable := true
    , automationMethod := "Detection: NTT gap (Attribute ∉ BT(VirtuousAgent)). " ++
        "Fix selection: 3 candidates ranked by semantic fidelity. " ++
        "Best fix (C, confidence 0.90): unfold VirtuousAgent to its own " ++
        "FOET:1157 definition (∃V. VirtueAttribute(V) ∧ attribute(A,V)). " ++
        "This is automatable: if concept X used as (attribute _ X) has " ++
        "a definitional expansion (X ↔ ∃Y. C(Y) ∧ attribute(_,Y)), " ++
        "replace the ill-typed shorthand with the well-typed expansion."
    , canaryTheorems :=
        [ "(attribute ?AGENT Pietas) must type-check (Pietas : VirtueAttribute ⊂ Attribute)"
        , "(instance ?AGENT VirtuousAgent) must type-check (VirtuousAgent ⊂ AutonomousAgent)"
        , "(attribute ?AGENT VirtuousAgent) must be ILL-TYPED (VirtuousAgent ⊄ Attribute)"
        , "Corrected: (∃V. VirtueAttribute(V) ∧ attribute(?A, V)) must type-check"
        ]
    , confidence := 0.90
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 11: capableInSituation arg 2 — CaseRole not Agent
    -- NTT Gap 3: BT(AutonomousAgent) ∩ {CaseRole, Relation, Abstract}
    --   = ∅ (Agent is on Object branch, CaseRole on Relation branch)
    -- STATUS: FIXED in SumoAbstract.lean
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 11
    , concept := "capableInSituation arg 2 (FIXED)"
    , originalSUMOClass := "domain 2 CaseRole (FOET:628)"
    , enacheClass := "(not in GF — FOET-only relation)"
    , ourClass := "El_Relation (FIXED from El_AutonomousAgent)"
    , recommendedClass := "El_Relation (CaseRole ⊂ BinaryPredicate ⊂ Relation)"
    , evidenceFor :=
        [ { source := "FOET:628"
          , axiomPattern := "(domain capableInSituation 2 CaseRole)"
          , supportsClass := "CaseRole"
          , strength := "strong"
          , note := "KIF explicitly declares domain 2 as CaseRole" }
        , { source := "Merge.kif:2435-2436"
          , axiomPattern := "(subclass CaseRole BinaryPredicate) " ++
              "(subclass CaseRole InheritableRelation)"
          , supportsClass := "Relation"
          , strength := "strong"
          , note := "CaseRole is on the Relation branch (Abstract), " ++
              "not the Object branch where AutonomousAgent lives" }
        , { source := "FOET:1702"
          , axiomPattern := "(capableInSituation ?CLASS agent ?AGENT ?SITUATION1)"
          , supportsClass := "CaseRole"
          , strength := "strong"
          , note := "Actual usage: `agent` (the CaseRole) is the literal " ++
              "second argument, not an agent individual" }
        , { source := "SumoNTT.lean"
          , axiomPattern := "BT(AutonomousAgent) = {AutonomousAgent, Object, " ++
              "Physical, Entity}. CaseRole ∉ BT(AutonomousAgent)."
          , supportsClass := "CaseRole"
          , strength := "strong"
          , note := "NTT gap: Object branch cannot reach Relation branch" }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Fully automatable: read (domain R N C) from FOET KIF. " ++
        "Our original encoding was a misreading of the signature. " ++
        "Rule: always use KIF domain declarations, not guesses."
    , canaryTheorems :=
        [ "(capableInSituation ?CLASS agent ?AGENT ?SIT) must type-check " ++
          "with `agent` as CaseRole"
        ]
    , confidence := 1.0
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 12: capableInSituation arity and arg 3 — quaternary
    -- NTT Gap 4: BT(Situation) = {Situation, Physical, Entity}
    --   Object ∉ BT(Situation)
    -- STATUS: FIXED in SumoAbstract.lean
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 12
    , concept := "capableInSituation arity + arg 3 (FIXED)"
    , originalSUMOClass := "QuaternaryPredicate: ProcessClass × CaseRole × Object × Situation"
    , enacheClass := "(not in GF)"
    , ourClass := "SumoClass → El_Relation → El_Object → El_Situation → Formula " ++
        "(FIXED from ternary SumoClass → El_AutonomousAgent → El_Situation)"
    , recommendedClass := "SumoClass → El_Relation → El_Object → El_Situation → Formula"
    , evidenceFor :=
        [ { source := "FOET:627"
          , axiomPattern := "(domainSubclass capableInSituation 1 Process)"
          , supportsClass := "Process"
          , strength := "strong"
          , note := "Arg 1 is a Process subclass (not instance)" }
        , { source := "FOET:629"
          , axiomPattern := "(domain capableInSituation 3 Object)"
          , supportsClass := "Object"
          , strength := "strong"
          , note := "Arg 3 is Object. Our old encoding had Situation here " ++
              "(wrong — Situation is arg 4)" }
        , { source := "FOET:630"
          , axiomPattern := "(domain capableInSituation 4 Situation)"
          , supportsClass := "Situation"
          , strength := "strong"
          , note := "Arg 4 is Situation. Our old encoding had this as arg 3." }
        , { source := "FOET:631"
          , axiomPattern := "(instance capableInSituation QuaternaryPredicate)"
          , supportsClass := "quaternary"
          , strength := "strong"
          , note := "Explicitly declared as quaternary — our old encoding was ternary" }
        , { source := "SumoNTT.lean"
          , axiomPattern := "BT(Situation) = {Situation, Physical, Entity}. " ++
              "Object ∉ BT(Situation)."
          , supportsClass := "Object"
          , strength := "strong"
          , note := "NTT gap: Situation and Object are siblings under Physical, " ++
              "neither is a subclass of the other" }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Fully automatable: read (instance R QuaternaryPredicate) " ++
        "and all (domain R N C) / (domainSubclass R N C) from KIF. " ++
        "Generate signature mechanically."
    , canaryTheorems :=
        [ "(capableInSituation ProcessClass CaseRole Object Situation) " ++
          "must be well-formed as quaternary"
        , "Old ternary encoding must fail to parse quaternary axiom usages"
        ]
    , confidence := 1.0
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 13: interferesWith removal (fabricated relation)
    -- STATUS: REMOVED from SumoAbstract.lean
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 13
    , concept := "interferesWith (REMOVED)"
    , originalSUMOClass := "(not found in any KIF file)"
    , enacheClass := "(not in GF)"
    , ourClass := "(removed — was El_AutonomousAgent → Formula → Formula)"
    , recommendedClass := "Remove entirely"
    , evidenceFor :=
        [ { source := "grep of Merge.kif"
          , axiomPattern := "No (instance interferesWith ...) declaration found"
          , supportsClass := "nonexistent"
          , strength := "strong"
          , note := "Not declared in Merge.kif (18784 lines)" }
        , { source := "grep of Mid-level-ontology.kif"
          , axiomPattern := "No interferesWith found"
          , supportsClass := "nonexistent"
          , strength := "strong"
          , note := "Not declared in Mid-level-ontology.kif (34935 lines)" }
        , { source := "grep of FOET seed ontology"
          , axiomPattern := "No interferesWith found"
          , supportsClass := "nonexistent"
          , strength := "strong"
          , note := "Not in formal_ethics_seed_ontology_mvpoc.kif either" }
        , { source := "SumoAbstract.lean:241-243 (before removal)"
          , axiomPattern := "def interferesWith : FunctionSig := ..."
          , supportsClass := "fabricated"
          , strength := "strong"
          , note := "Existed only in our encoding with no KIF backing. " ++
              "Likely hallucinated by a prior LLM agent during encoding." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Fully automatable: for every relation in our encoding, " ++
        "verify that (instance R SomeRelationType) exists in KIF. " ++
        "If not, flag as potentially fabricated."
    , canaryTheorems :=
        [ "No axiom should reference sumo_interferesWith after removal"
        , "Build must succeed without interferesWith"
        ]
    , confidence := 1.0
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 14: Pietas args swapped in attribute
    -- (attribute Pietas ?A) should be (attribute ?A Pietas)
    -- 3 correct vs 1 incorrect usage — auto-fixable by counting
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 14
    , concept := "Pietas (attribute args swapped)"
    , originalSUMOClass := "VirtueAttribute (FOET:4739)"
    , enacheClass := "(not in GF)"
    , ourClass := "VirtueAttribute"
    , recommendedClass := "VirtueAttribute (no change). Fix axiom: swap args."
    , evidenceFor :=
        [ { source := "FOET:4782"
          , axiomPattern := "(attribute Pietas ?A) — Pietas in arg1 (Object slot)"
          , supportsClass := "swapped"
          , strength := "strong"
          , note := "Pietas : VirtueAttribute ⊂ Attribute. Cannot fill Object slot." }
        , { source := "FOET:4743,4754,4762"
          , axiomPattern := "(attribute ?AGENT Pietas) — 3 correct usages"
          , supportsClass := "correct"
          , strength := "strong"
          , note := "3 correct vs 1 incorrect. Counting resolves unambiguously." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Counting: 3 correct (attribute ?AGENT Pietas) vs " ++
        "1 incorrect (attribute Pietas ?A). Auto-fix: swap arguments."
    , canaryTheorems :=
        [ "(attribute ?AGENT Pietas) must type-check"
        , "(attribute Pietas ?AGENT) must be ILL-TYPED"
        ]
    , confidence := 0.98
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 15: Process in Object slot of attribute (7 occurrences)
    -- (attribute ?ACT ?VIRTUE) where ?ACT : AutonomousAgentProcess ⊂ Process
    -- Process and Object are DISJOINT in SUMO. 30+ correct uses with agents.
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 15
    , concept := "Process-in-Object-slot (FIXED: attribute→property)"
    , originalSUMOClass := "domain attribute 1 Object (Merge.kif:1754)"
    , enacheClass := "El Object → El Attribute → Formula"
    , ourClass := "El_Object → El_Attribute → Formula + El_Entity → El_Attribute (property)"
    , recommendedClass := "Use superrelation `property` (domain 1 Entity) for Processes. " ++
        "(subrelation attribute property) at Merge.kif:1753."
    , evidenceFor :=
        [ { source := "Merge.kif:1754"
          , axiomPattern := "(domain attribute 1 Object)"
          , supportsClass := "Object"
          , strength := "strong"
          , note := "KIF domain: arg1 must be Object" }
        , { source := "Merge.kif:839,1656"
          , axiomPattern := "(subclass Object Physical) (subclass Process Physical)"
          , supportsClass := "disjoint"
          , strength := "strong"
          , note := "Object and Process are disjoint partitions of Physical" }
        , { source := "FOET:297,1192,1200,1210,1218,2447,2693"
          , axiomPattern := "(attribute ?IPROC ?VIRTUE) where ?IPROC : Process"
          , supportsClass := "bug"
          , strength := "strong"
          , note := "7 occurrences. Process ∉ BT⁻¹(Object)." }
        , { source := "FOET:4743,4754,... (30+ lines)"
          , axiomPattern := "(attribute ?AGENT ...) where ?AGENT : AutonomousAgent"
          , supportsClass := "correct"
          , strength := "strong"
          , note := "30+ correct usages with agents. 7 incorrect vs 30+ correct." }
        , { source := "FOET:293 (author comment)"
          , axiomPattern := "\"Can I just use attribute? I think I can!\""
          , supportsClass := "intentional"
          , strength := "moderate"
          , note := "Author acknowledged uncertainty about this usage." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "NTT: Object ∉ BT(Process). Superrelation widening: " ++
        "(subrelation attribute property) at Merge.kif:1753. " ++
        "property has (domain 1 Entity) which covers Process. " ++
        "Rule: if demanded_sort ∉ BT(X), check (subrelation R R') " ++
        "where (domain R' N C') and C' ∈ BT(X)."
    , canaryTheorems :=
        [ "(attribute ?AGENT ?VIRTUE) where ?AGENT:Object must type-check"
        , "(attribute ?ACT ?VIRTUE) where ?ACT:Process must be ILL-TYPED"
        ]
    , confidence := 0.92
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 16: contraryAttribute with classes not instances
    -- (contraryAttribute VirtueAttribute ViceAttribute) — both are classes
    -- 2 correct (instances) vs 1 incorrect (classes)
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 16
    , concept := "contraryAttribute(VirtueAttribute, ViceAttribute) (FIXED)"
    , originalSUMOClass := "VariableArityRelation, all args Attribute instances"
    , enacheClass := "[El Attribute] -> Formula"
    , ourClass := "El_Attribute → El_Attribute → Formula"
    , recommendedClass := "Replace with (disjoint VirtueAttribute ViceAttribute). " ++
        "Three candidates analyzed: " ++
        "(a) disjoint — 'no concept is both' — TRUE, MGU. " ++
        "(b) ∀V,W. contraryAttribute(V,W) — 'agent can't have any V+W' — " ++
        "FALSE (Courageous+Gluttonous counterexample). " ++
        "(c) field-relative contrariness — TRUE but needs field infrastructure."
    , evidenceFor :=
        [ { source := "Merge.kif:461"
          , axiomPattern := "(inList ?ELEMENT (ListFn @ROW)) → (instance ?ELEMENT Attribute)"
          , supportsClass := "instance"
          , strength := "strong"
          , note := "contraryAttribute requires all elements to be Attribute INSTANCES" }
        , { source := "FOET:1233-1234"
          , axiomPattern := "(contraryAttribute MorallyGood MorallyBad MorallyPermissible)"
          , supportsClass := "correct"
          , strength := "strong"
          , note := "Correct: MorallyGood etc. are instances of MoralValueAttribute" }
        , { source := "FOET:1235"
          , axiomPattern := "(contraryAttribute VirtueAttribute ViceAttribute)"
          , supportsClass := "bug"
          , strength := "strong"
          , note := "VirtueAttribute/ViceAttribute are CLASSES, not instances. " ++
              "Instance/class confusion." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Check: is each argument of contraryAttribute declared " ++
        "via (instance X SomeAttribute)? If (subclass X ...) instead, " ++
        "it's a class being used as instance. Counting: 2 correct vs 1 incorrect."
    , canaryTheorems :=
        [ "(contraryAttribute MorallyGood MorallyBad) must type-check"
        , "(contraryAttribute VirtueAttribute ViceAttribute) must be ILL-TYPED"
        ]
    , confidence := 0.95
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 17: Pain in attribute arg2 (FOET extension of Decision 1)
    -- (attribute ?AGENT Pain) at FOET:2217,2221
    -- Pain : PathologicProcess ⊄ Attribute. Pleasure correct at 2200,2204.
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 17
    , concept := "Pain in FOET (attribute arg2)"
    , originalSUMOClass := "PathologicProcess (MLO:21097)"
    , enacheClass := "EmotionalState (silent repair)"
    , ourClass := "EmotionalState (after D1 fix)"
    , recommendedClass := "EmotionalState (resolved by Decision 1)"
    , evidenceFor :=
        [ { source := "FOET:2234,2238"
          , axiomPattern := "(attribute ?AGENT Pain) — Pain in Attribute slot"
          , supportsClass := "EmotionalState"
          , strength := "strong"
          , note := "After D1: Pain : EmotionalState ⊂ Attribute ✓. " ++
              "FOET usage is now type-consistent." }
        , { source := "FOET:2200,2204"
          , axiomPattern := "(attribute ?AGENT Pleasure) — Pleasure correct"
          , supportsClass := "EmotionalState"
          , strength := "strong"
          , note := "Pleasure : EmotionalState ⊂ Attribute ✓. " ++
              "Same axiom pattern. Both now type-check." }
        , { source := "Mid-level-ontology.kif:21103"
          , axiomPattern := "(instance Pain EmotionalState)"
          , supportsClass := "EmotionalState"
          , strength := "strong"
          , note := "D1 fix applied in SUMO source. EmotionalState ⊂ " ++
              "PsychologicalAttribute ⊂ Attribute. (attribute ?AGENT Pain) " ++
              "now type-checks." }
        , { source := "FOET verification (2026-02-24)"
          , axiomPattern := "CausesProposition typo: 0 remaining occurrences"
          , supportsClass := "fixed"
          , strength := "strong"
          , note := "CausesProposition (capital C) no longer present in FOET. " ++
              "Previously at FOET:2217,2221. Typo fixed." }
        , { source := "Medicine.kif:936,953"
          , axiomPattern := "(attribute ?P Pain) — 2 uses in Medicine.kif"
          , supportsClass := "EmotionalState"
          , strength := "strong"
          , note := "Both now type-check after D1 reclassification." }
        , { source := "emotion.kif:1071"
          , axiomPattern := "(contraryAttribute Pleasure Pain)"
          , supportsClass := "EmotionalState"
          , strength := "strong"
          , note := "Pain as peer of Pleasure in contraryAttribute. " ++
              "Both are Attribute instances after D1. Type-consistent." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Resolved by Decision 1 (Pain reclassification). " ++
        "Pain : EmotionalState ⊂ Attribute. All (attribute ?AGENT Pain) " ++
        "usages now type-check. CausesProposition typo separately fixed."
    , canaryTheorems :=
        [ "(attribute ?AGENT Pleasure) must type-check"
        , "(attribute ?AGENT Pain) must type-check (after D1 fix)"
        , "(contraryAttribute Pleasure Pain) must type-check"
        ]
    , confidence := 0.98
    , needsSplit := false  -- Split unnecessary: D1 reclassification suffices
    , splitProposal := none
    , status := .fixed  -- Resolved by D1 reclassification (2026-02-24)
    , reviewState := EvidenceModel.ReviewState.applied
    , reviewers := ["claude_code", "codex"]
    , assuranceLower95 := 0.639597
    , evidenceCompleteness := 0.5
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 18: attribute args swapped (FOET:6361)
    -- (attribute ?NORMAL ?NORMALPERSON) — PsychologicalAttribute in arg1
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 18
    , concept := "attribute args swapped (FOET:6361)"
    , originalSUMOClass := "domain attribute 1 Object, 2 Attribute"
    , enacheClass := "(not in GF)"
    , ourClass := "El_Object → El_Attribute → Formula"
    , recommendedClass := "No encoding change. Fix axiom: swap to " ++
        "(attribute ?NORMALPERSON ?NORMAL)."
    , evidenceFor :=
        [ { source := "FOET:6354"
          , axiomPattern := "(instance ?NORMAL PsychologicalAttribute)"
          , supportsClass := "Attribute"
          , strength := "strong"
          , note := "?NORMAL is typed as PsychologicalAttribute — belongs in arg2" }
        , { source := "FOET:6361"
          , axiomPattern := "(attribute ?NORMAL ?NORMALPERSON)"
          , supportsClass := "swapped"
          , strength := "strong"
          , note := "PsychologicalAttribute in arg1 (Object slot). Swap needed." }
        , { source := "Variable name inference"
          , axiomPattern := "?NORMALPERSON → implies Human/Object"
          , supportsClass := "Object"
          , strength := "moderate"
          , note := "Variable name suggests Object, confirms it belongs in arg1" }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "NTT: check BT of each argument against demanded sort. " ++
        "If arg1's BT contains Attribute but not Object, and arg2's BT " ++
        "contains Object but not Attribute, arguments are swapped. Auto-fix: swap."
    , canaryTheorems :=
        [ "(attribute ?NORMALPERSON ?NORMAL) must type-check after swap"
        ]
    , confidence := 0.95
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 19: holdsEthicalPhilosophy args swapped + undeclared constant
    -- (holdsEthicalPhilosophy DEONTOLOGY ?AGENT) at FOET:4763
    -- domain 1 = Group, domain 2 = Ethics. Both args wrong.
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 19
    , concept := "holdsEthicalPhilosophy (FOET:4763)"
    , originalSUMOClass := "domain 1 Group, domain 2 Ethics"
    , enacheClass := "(not in GF)"
    , ourClass := "(not yet encoded)"
    , recommendedClass := "Fix axiom: swap args, use declared constant. " ++
        "Compare with FOET:4788,4794,4801 for correct pattern."
    , evidenceFor :=
        [ { source := "FOET:4763"
          , axiomPattern := "(holdsEthicalPhilosophy DEONTOLOGY ?AGENT)"
          , supportsClass := "swapped"
          , strength := "strong"
          , note := "DEONTOLOGY (undeclared constant) in arg1 (Group slot). " ++
              "?AGENT in arg2 (Ethics slot). Both wrong." }
        , { source := "FOET:4788,4794,4801"
          , axiomPattern := "(holdsEthicalPhilosophy ?AGENT UTILITARIANISM)"
          , supportsClass := "correct-direction"
          , strength := "strong"
          , note := "3 correct-direction usages (agent in arg1). " ++
              "But note: agent ≠ Group in strict typing." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Counting: 3 correct-direction vs 1 wrong-direction. " ++
        "Auto-fix: swap + replace DEONTOLOGY with a declared constant."
    , canaryTheorems :=
        [ "Corrected axiom must have declared constants in all slots"
        ]
    , confidence := 0.90
    , needsSplit := false
    , splitProposal := none
    , status := .fixed
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 20: FOET syntax errors (batch — all fully automatable)
    -- 15 errors across 30+ lines. All mechanical fixes. ALL FIXED.
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 20
    , concept := "FOET syntax errors (15 items, batch)"
    , originalSUMOClass := "(various)"
    , enacheClass := "(N/A)"
    , ourClass := "(N/A)"
    , recommendedClass := "Fix all. Fully mechanical."
    , evidenceFor :=
        [ { source := "FOET:242,254,264,280,2709,5563,6102,6109,6116,6123"
          , axiomPattern := "(exist ...) — 10 occurrences, should be (exists ...)"
          , supportsClass := "typo"
          , strength := "strong"
          , note := "exist is not a KIF quantifier. Many correct (exists ...) in same file." }
        , { source := "FOET:2217,2221"
          , axiomPattern := "(CausesProposition ...) — capital C, should be causesProposition"
          , supportsClass := "typo"
          , strength := "strong"
          , note := "2 wrong-case vs many correct-case. Undeclared relation." }
        , { source := "FOET:2987,3010"
          , axiomPattern := "(agent ?DECIDE AGENT) — AGENT without ?, should be ?AGENT"
          , supportsClass := "missing-var-prefix"
          , strength := "strong"
          , note := "Bare constant disconnects binding. 2 occurrences." }
        , { source := "FOET:6281"
          , axiomPattern := "(realizesFormula ?PROC FORM) — FORM without ?"
          , supportsClass := "missing-var-prefix"
          , strength := "strong"
          , note := "Same pattern. 1 occurrence." }
        , { source := "FOET:6365"
          , axiomPattern := "(most ?X NORMALPEOPLE) — NORMALPEOPLE without ?"
          , supportsClass := "missing-var-prefix"
          , strength := "strong"
          , note := "Same pattern. 1 occurrence." }
        , { source := "FOET:989-990"
          , axiomPattern := "(domain 1 conjectures C) — args swapped, should be (domain conjectures 1 C)"
          , supportsClass := "arg-order"
          , strength := "strong"
          , note := "2 malformed domain declarations." }
        , { source := "FOET:5182"
          , axiomPattern := "(subAttribute EpistemicUniversalLove) — missing 2nd arg"
          , supportsClass := "missing-arg"
          , strength := "strong"
          , note := "subAttribute is BinaryPredicate (Merge.kif:673). " ++
              "Sibling line 5181: (subAttribute UniversalLove Love). " ++
              "FIX: (subAttribute EpistemicUniversalLove UniversalLove) — " ++
              "naming convention entails unique parent." }
        , { source := "FOET:5392,5393"
          , axiomPattern := "(element (modalAttribute ...) ) — missing 2nd arg (?DIT)"
          , supportsClass := "missing-arg"
          , strength := "strong"
          , note := "element is BinaryPredicate (Merge.kif:5462). " ++
              "Line 5391 correct: (element ... ?DIT). " ++
              "Lines 5392+5393 both missing ?DIT in same (exists (?DIT) ...) block. " ++
              "FIX: add ?DIT as 2nd arg to both." }
        , { source := "FOET:5646-5647"
          , axiomPattern := "(SituationFn ?X ?Y) — UnaryFunction called with 2 args"
          , supportsClass := "arity"
          , strength := "strong"
          , note := "SituationFn : UnaryFunction. 1 arg only." }
        , { source := "FOET:6215"
          , axiomPattern := "(domain goodForAgent 2 ?FORMULA) — variable in class slot"
          , supportsClass := "malformed"
          , strength := "strong"
          , note := "Domain declarations need class constants, not variables. " ++
              "Doc says 'proposition expressed by ?FORMULA'. " ++
              "6 SUMO precedents: hasPurpose, desires, entails all use Formula. " ++
              "FIX: (domain goodForAgent 2 Formula)." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "All 15 items are mechanical: pattern-match against " ++
        "KIF syntax rules. exist→exists, missing ?→add ?, " ++
        "swapped domain args→reorder, missing args→add from context, " ++
        "variable in class slot→replace with class constant."
    , canaryTheorems :=
        [ "All (exists ...) quantifiers must parse"
        , "All (domain R N C) declarations must have constant C"
        , "All relation calls must have correct arity"
        ]
    , confidence := 1.0
    , needsSplit := false
    , splitProposal := none
    , status := .fixed  -- ALL 15 FIXED (2026-02-24):
        -- Batch 1 (11): exist→exists (10), CausesProposition (1)
        -- Batch 2 (4, applied 2026-02-24):
        --   FOET:5182 (subAttribute EpistemicUniversalLove UniversalLove)
        --   FOET:5392 (element ... ?DIT) — added missing set arg
        --   FOET:5393 (element ... ?DIT) — newly found, same block as 5392
        --   FOET:6215 (domain goodForAgent 2 Formula) — class constant
    , reviewState := EvidenceModel.ReviewState.applied
    , reviewers := ["claude_code", "codex"]
    , assuranceLower95 := 0.717719
    , evidenceCompleteness := 0.5
    , archetype := .syntaxArity
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 21: FOET parenthesis balance errors (6 fixes)
    -- Discovered by paren-balance analysis. Made 95% of FOET invisible
    -- to any s-expression parser (including stratum_scan.py).
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 21
    , concept := "FOET KIF paren balance (6 errors)"
    , originalSUMOClass := "(N/A — syntax, not classification)"
    , enacheClass := "(N/A)"
    , ourClass := "(N/A)"
    , recommendedClass := "Fix all. Fully mechanical."
    , evidenceFor :=
        [ { source := "FOET:174"
          , axiomPattern := "(=> (instance ?REL UnaryPredicate) (valence ?REL 1) — missing closing )"
          , supportsClass := "unclosed-form"
          , strength := "strong"
          , note := "=> at L172 never closed. Swallowed all subsequent forms." }
        , { source := "FOET:259"
          , axiomPattern := "(<=> (modalAttribute ...) (forall ...))) — missing closing ) for <=>"
          , supportsClass := "unclosed-form"
          , strength := "strong"
          , note := "<=> at L252 never closed. 3 trailing parens, needs 4." }
        , { source := "FOET:350"
          , axiomPattern := "(realizesFormulaSubclass ?CPROC ?FORMULA))))) — excess )"
          , supportsClass := "excess-close"
          , strength := "strong"
          , note := "<=> at L345 has 5 trailing ), needs 4. Paired with L6370 missing )." }
        , { source := "FOET:5540"
          , axiomPattern := "(virtueTarget Benevolence (exists ...)) — missing closing )"
          , supportsClass := "unclosed-form"
          , strength := "strong"
          , note := "virtueTarget at L5535 never closed. 4 trailing parens, needs 5." }
        , { source := "FOET:5677-5678"
          , axiomPattern := "(and ... (greaterThanOrEqualTo ...)) — misplaced consequent + missing )"
          , supportsClass := "structural-misparse"
          , strength := "strong"
          , note := "(greaterThanOrEqualTo was inside (and antecedent, should be " ++
              "consequent of =>. Added ) to close (and before consequent. " ++
              "Also <=> at L5667 never closed." }
        , { source := "FOET:6370"
          , axiomPattern := "(subjectiveAttribute ?PAINT Favorite ?ALEX)) — missing closing )"
          , supportsClass := "unclosed-form"
          , strength := "strong"
          , note := "(exists at L6357 never closed. Paired with excess ) at L350." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "Paren-balance tracker: count ( and ) per line (stripping " ++
        "comments at ;), flag where cumulative balance goes negative or " ++
        "ends nonzero. All 6 fixes are mechanical."
    , canaryTheorems :=
        [ "String-aware paren balance == 0 (FAILING: currently -2)"
        , "Cumulative balance never goes negative (FAILING: hundreds of moments)"
        , "stratum_scan.py parses all ~6884 lines (not just 174)"
        ]
    , confidence := 0.6  -- 6 fixes applied but string-aware balance still -2
    , needsSplit := false
    , splitProposal := none
    , status := .deferred  -- downgraded: string-aware balance is -2, pervasive issues remain
    , archetype := .syntaxArity
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 22: LinguisticExpression in `part` demands Object
    -- Sentence/NounPhrase/VerbPhrase used in `part` which demands Object,
    -- but LinguisticExpression < ContentBearingPhysical < Physical (not Object).
    -- Affects Merge.kif:15507 and Mid-level-ontology.kif:705.
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 22
    , concept := "LinguisticExpression in part (demands Object)"
    , originalSUMOClass := "Sentence < LinguisticExpression < ContentBearingPhysical < Physical"
    , enacheClass := "(N/A — hierarchy gap, not GF classification)"
    , ourClass := "(detected by constraint_check.py --stratum 1)"
    , recommendedClass := "ContentBearingPhysical sits above Object and Process. " ++
        "SUMO axioms treat sentences as having 'parts' (NounPhrase, VerbPhrase), " ++
        "but `part` is typed Object × Object. Either: (a) add (subclass " ++
        "LinguisticExpression ContentBearingObject) to route through Object, " ++
        "or (b) use a separate linguistic-part relation."
    , evidenceFor :=
        [ { source := "Merge.kif:15507"
          , axiomPattern := "(=> (instance ?S Sentence) (exists (?P1 ?P2) (and " ++
              "(instance ?P1 NounPhrase) (instance ?P2 VerbPhrase) " ++
              "(part ?P1 ?S) (part ?P2 ?S))))"
          , supportsClass := "type gap"
          , strength := "strong"
          , note := "NounPhrase/VerbPhrase/Sentence all under ContentBearingPhysical, " ++
              "not Object. part demands Object." }
        , { source := "Mid-level-ontology.kif:705"
          , axiomPattern := "(part ?S ...) where ?S : Sentence"
          , supportsClass := "type gap"
          , strength := "strong"
          , note := "Same issue in Mid-level-ontology." }
        , { source := "Merge.kif:1432"
          , axiomPattern := "(subclass LinguisticExpression ContentBearingPhysical)"
          , supportsClass := "hierarchy"
          , strength := "strong"
          , note := "Only parent. No path to Object." }
        , { source := "Merge.kif:925-926"
          , axiomPattern := "(domain part 1 Object) (domain part 2 Object)"
          , supportsClass := "demand"
          , strength := "strong"
          , note := "Both args of part demand Object." }
        ]
    , evidenceAgainst :=
        [ { source := "Merge.kif:1362-1363"
          , axiomPattern := "(subclass ContentBearingObject CorpuscularObject) " ++
              "(subclass ContentBearingObject ContentBearingPhysical)"
          , supportsClass := "possible fix route"
          , strength := "moderate"
          , note := "ContentBearingObject IS under Object. If LinguisticExpression " ++
              "were subclass of ContentBearingObject, it would inherit Object. " ++
              "But this may be intentional — not all linguistic expressions " ++
              "are corpuscular objects." }
        ]
    , automatable := true
    , automationMethod := "constraint_check.py: walk axiom body, track variable types " ++
        "from instance declarations, check against domain obligations. " ++
        "Detected by path-sensitive constraint flow."
    , canaryTheorems :=
        [ "LinguisticExpression ∉ BT⁻¹(Object) in current SUMO"
        , "After fix: Sentence must reach Object via subclass chain"
        ]
    , confidence := 0.95
    , needsSplit := false
    , splitProposal := none
    , status := .logged  -- two possible fixes: add subclass edge OR new relation. Not deterministic.
    , archetype := .hierarchyGap
    , witnesses :=
        [ { id := "D22"
          , query := "reachabilityTest \"LinguisticExpression\" \"object\""
          , expected := .unsat, observed := .unsat, passed := true
          , sourceRef := "SumoNTT.lean:1109"
          , note := "LE < ContentBearingPhysical < Physical, not Object" } ]
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 23: Artifact missing SelfConnectedObject edge
    -- WasherForBolt < Device < Artifact < Object, but `contains`
    -- demands SelfConnectedObject. Artifact skips SelfConnectedObject.
    -- Affects Mid-level-ontology.kif:4730.
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 23
    , concept := "Artifact < Object (missing SelfConnectedObject edge)"
    , originalSUMOClass := "WasherForBolt < Device < Artifact < Object"
    , enacheClass := "(N/A — hierarchy gap, not GF classification)"
    , ourClass := "(detected by constraint_check.py --stratum 1)"
    , recommendedClass := "Add (subclass Artifact SelfConnectedObject) to Merge.kif. " ++
        "Physical artifacts are self-connected objects by construction. " ++
        "The chain Object > SelfConnectedObject > CorpuscularObject exists " ++
        "but Artifact bypasses it going directly to Object."
    , evidenceFor :=
        [ { source := "Mid-level-ontology.kif:4730"
          , axiomPattern := "(contains ?W ...) where ?W : WasherForBolt"
          , supportsClass := "type gap"
          , strength := "strong"
          , note := "contains demands SelfConnectedObject. WasherForBolt < Device " ++
              "< Artifact < Object. No path to SelfConnectedObject." }
        , { source := "Merge.kif:15853"
          , axiomPattern := "(subclass Artifact Object)"
          , supportsClass := "hierarchy"
          , strength := "strong"
          , note := "Artifact's only parent is Object, skipping SelfConnectedObject." }
        , { source := "Merge.kif:1054"
          , axiomPattern := "(domain contains 1 SelfConnectedObject)"
          , supportsClass := "demand"
          , strength := "strong"
          , note := "contains arg1 demands SelfConnectedObject." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "constraint_check.py: transitive closure of subclass " ++
        "shows Artifact cannot reach SelfConnectedObject."
    , canaryTheorems :=
        [ "Artifact ∉ BT⁻¹(SelfConnectedObject) in current SUMO"
        , "After fix: Artifact < SelfConnectedObject < Object"
        ]
    , confidence := 0.90
    , needsSplit := false
    , splitProposal := none
    , status := .logged  -- ontology-level modeling choice: add intermediate subclass
        -- edge vs restructure hierarchy. Not auto-fixable without semantic decision.
    , archetype := .hierarchyGap
    , witnesses :=
        [ { id := "D23"
          , query := "reachabilityTest \"Artifact\" \"selfconnectedobject\""
          , expected := .unsat, observed := .unsat, passed := true
          , sourceRef := "SumoNTT.lean:1116"
          , note := "Artifact → Object directly, bypasses SelfConnectedObject" } ]
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 24: agent args swapped at Mid-level-ontology.kif:24453
    -- (agent ?X ?P) where ?X : CognitiveAgent, ?P : Process class.
    -- agent[1] = Process, agent[2] = AutonomousAgent.
    -- Arguments are backwards. Should be (agent ?P ?X).
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 24
    , concept := "agent args swapped (OccupationalRole axiom)"
    , originalSUMOClass := "CognitiveAgent < AutonomousAgent (Mid-level-ontology.kif:24453)"
    , enacheClass := "(N/A — axiom body error, not classification)"
    , ourClass := "(detected by constraint_check.py --stratum 1)"
    , recommendedClass := "Swap arguments: (agent ?P ?X) instead of (agent ?X ?P). " ++
        "?X : CognitiveAgent (should be arg2 = AutonomousAgent slot). " ++
        "?P : ?PCLASS (should be arg1 = Process slot)."
    , evidenceFor :=
        [ { source := "Mid-level-ontology.kif:24453"
          , axiomPattern := "(agent ?X ?P) where (instance ?X CognitiveAgent) " ++
              "and (instance ?P ?PCLASS)"
          , supportsClass := "swapped"
          , strength := "strong"
          , note := "?X:CognitiveAgent in agent[1] which demands Process. " ++
              "?P:ProcessClass in agent[2] which demands AutonomousAgent." }
        , { source := "Merge.kif:2468-2469"
          , axiomPattern := "(domain agent 1 Process) (domain agent 2 AutonomousAgent)"
          , supportsClass := "demand"
          , strength := "strong"
          , note := "arg1 = Process, arg2 = AutonomousAgent. Unambiguous." }
        , { source := "Mid-level-ontology.kif:24461"
          , axiomPattern := "(instance ?X CognitiveAgent)"
          , supportsClass := "type witness"
          , strength := "strong"
          , note := "CognitiveAgent < AutonomousAgent. Should be in agent[2]." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "constraint_check.py: variable ?X typed CognitiveAgent " ++
        "(< AutonomousAgent), used in agent[1] which demands Process. " ++
        "Cross-check: ?P (Process-typed) used in agent[2] which demands " ++
        "AutonomousAgent. Both args fit the OTHER position → swap."
    , canaryTheorems :=
        [ "(agent ?X ?P) with ?X:CognitiveAgent must be ILL-TYPED at agent[1]"
        , "(agent ?P ?X) with ?P:Process, ?X:CognitiveAgent must type-check"
        ]
    , confidence := 0.99
    , needsSplit := false
    , splitProposal := none
    , status := .autoFixable
    , archetype := .argSwapTyped
    , witnesses :=
        [ { id := "D24a"
          , query := "reachabilityTest \"CognitiveAgent\" \"process\""
          , expected := .unsat, observed := .unsat, passed := true
          , sourceRef := "SumoNTT.lean:1124"
          , note := "Pre: CA in Process slot (arg1) → ill-typed" }
        , { id := "D24b"
          , query := "reachabilityTest \"CognitiveAgent\" \"object\""
          , expected := .sat, observed := .sat, passed := true
          , sourceRef := "SumoNTT.lean:1130"
          , note := "Post: CA in AutonomousAgent slot (arg2) → well-typed" } ]
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 25: Stratum scan consolidated results (full KB)
    -- constraint_check.py with --kb-extra loading all 64 SUMO KIF files.
    -- S0: 12 errors (6 unique), S1: 10 errors (7 unique), S2: 2 errors.
    -- Key patterns: missing Artifact→SelfConnectedObject edge,
    -- Abstract/Physical used where Object demanded, missing WhenFn wrappers.
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 25
    , concept := "Stratum scan consolidated (full KB, all 64 SUMO files)"
    , originalSUMOClass := "(N/A — scan audit, not single concept)"
    , enacheClass := "(N/A)"
    , ourClass := "(constraint_check.py with recursive KB extraction)"
    , recommendedClass := "Fix categories: (1) Add (subclass Artifact SelfConnectedObject) " ++
        "to close Bag/WasherForBolt gap. (2) Use WhenFn wrappers for holdsDuring/BeginFn " ++
        "with Processes. (3) Swap agent args at Mid-level:24453. (4) Widen " ++
        "holdsEthicalPhilosophy domain from Group to AutonomousAgent."
    , evidenceFor :=
        [ { source := "constraint_check.py --stratum 0 (full KB)"
          , axiomPattern := "S0: 12 errors (6 unique sites), 20 infos, 110 axioms"
          , supportsClass := "audit"
          , strength := "strong"
          , note := "Errors: PaintingDevice in agent[2], Bag in contains[1], " ++
              "NasalCavity in HoleHostFn[1], Soaking in holdsDuring[1], " ++
              "RadiatingLight in BeginFn[1], Inhabitant in inhabits[1]" }
        , { source := "constraint_check.py --stratum 1 (full KB)"
          , axiomPattern := "S1: 10 errors (7 unique sites), 7 infos, 149 axioms"
          , supportsClass := "audit"
          , strength := "strong"
          , note := "Errors: Set/Sentence/NounPhrase/VerbPhrase in part/patient, " ++
              "WasherForBolt in contains, agent args swapped (Dec 24), " ++
              "CognitiveAgent in holdsEthicalPhilosophy" }
        , { source := "constraint_check.py --stratum 2 (full KB)"
          , axiomPattern := "S2: 2 errors (2 unique sites), 2 infos, 38 axioms"
          , supportsClass := "audit"
          , strength := "strong"
          , note := "Errors: NonNullSet in patient[2] (FOET:834), " ++
              "Situation in part[2] (FOET:5418)" }
        , { source := "constraint_check.py recursive KB extraction"
          , axiomPattern := "3108 subclass edges (vs 2927 without recursion)"
          , supportsClass := "infrastructure"
          , strength := "strong"
          , note := "FOET's pervasive paren issues cause subclass declarations " ++
              "to be nested inside broken forms. Recursive _extract finds " ++
              "181 additional subclass edges from FOET. This eliminated " ++
              "20 false positives in S2 (was 21 errors, now 2)." }
        ]
    , evidenceAgainst := []
    , automatable := true
    , automationMethod := "constraint_check.py --stratum N --kif <targets> --kb-extra <all>"
    , canaryTheorems :=
        [ "S0 errors ≤ 12, S1 errors ≤ 10, S2 errors ≤ 2"
        , "After fixes: all strata should be 0 errors"
        ]
    , confidence := 0.85
    , needsSplit := false
    , splitProposal := none
    }

    -- ═══════════════════════════════════════════════════════════════
    -- Decision 26: holdsEthicalPhilosophy domain too narrow
    -- (domain holdsEthicalPhilosophy 1 Group) but FOET:5062 uses
    -- ?AGENT : CognitiveAgent in arg1. Individual agents can hold
    -- ethical philosophies, not just groups.
    -- ═══════════════════════════════════════════════════════════════
  , { decisionId := 26
    , concept := "holdsEthicalPhilosophy domain (Group → AutonomousAgent)"
    , originalSUMOClass := "(domain holdsEthicalPhilosophy 1 Group) at FOET:1508"
    , enacheClass := "(N/A — not in GF)"
    , ourClass := "(detected by constraint_check.py --stratum 1)"
    , recommendedClass := "Widen domain to AutonomousAgent: " ++
        "(domain holdsEthicalPhilosophy 1 AutonomousAgent). " ++
        "Individual cognitive agents can hold ethical philosophies."
    , evidenceFor :=
        [ { source := "FOET:5053,5074"
          , axiomPattern := "(holdsEthicalPhilosophy ?AGENT ?ETHICS) " ++
              "where (instance ?AGENT CognitiveAgent)"
          , supportsClass := "domain mismatch"
          , strength := "strong"
          , note := "CognitiveAgent < AutonomousAgent, not < Group. " ++
              "isNormative definition needs individual agents." }
        , { source := "FOET:1508"
          , axiomPattern := "(domain holdsEthicalPhilosophy 1 Group)"
          , supportsClass := "demand"
          , strength := "strong"
          , note := "Domain declares Group." }
        , { source := "FOET usage census (2026-02-24)"
          , axiomPattern := "18 total uses: 12 individual-agent, 4 group, 2 unconstrained"
          , supportsClass := "domain mismatch"
          , strength := "strong"
          , note := "Individual-agent uses (12): FOET:1584,4792,4818,4824," ++
              "4831,5053,5074,5802,5817,5958,5980,6002. " ++
              "Group uses (4): FOET:1518,1541,1567,1575. " ++
              "Unconstrained (2): FOET:1571,1579. " ++
              "Overwhelming majority (67%) use individual agents, not groups. " ++
              "Domain should be AutonomousAgent (covers both Group and CognitiveAgent)." }
        , { source := "SUMO search (2026-02-24)"
          , axiomPattern := "holdsEthicalPhilosophy: 0 matches in /sumo/"
          , supportsClass := "FOET-only"
          , strength := "moderate"
          , note := "This predicate exists only in FOET. No SUMO core usage." }
        ]
    , evidenceAgainst :=
        [ { source := "FOET:1518,1541,1567,1575"
          , axiomPattern := "4 axioms use holdsEthicalPhilosophy with ?GROUP"
          , supportsClass := "Group usage"
          , strength := "weak"
          , note := "These 4 axioms use Group, but Group < AutonomousAgent, " ++
              "so widening to AutonomousAgent preserves them. " ++
              "Downgraded from moderate to weak: not a real counterargument." }
        ]
    , automatable := true
    , automationMethod := "constraint_check.py: variable typed CognitiveAgent, " ++
        "holdsEthicalPhilosophy[1] demands Group. No subtype path."
    , canaryTheorems :=
        [ "After fix: CognitiveAgent must satisfy holdsEthicalPhilosophy[1]"
        , "Group must still satisfy holdsEthicalPhilosophy[1]"
        ]
    , confidence := 0.88
    , needsSplit := false
    , splitProposal := none
    , archetype := .domainNarrowing
    , witnesses :=
        [ { id := "D26a"
          , query := "reachabilityTest \"CognitiveAgent\" \"group\""
          , expected := .unsat, observed := .unsat, passed := true
          , sourceRef := "SumoNTT.lean:1142"
          , note := "Pre: CA ≠ Group, holdsEthicalPhilosophy demands Group" }
        , { id := "D26b"
          , query := "reachabilityTest \"Group\" \"object\""
          , expected := .sat, observed := .sat, passed := true
          , sourceRef := "SumoNTT.lean:1149"
          , note := "Positive control: Group < AutonomousAgent < Object" } ]
    }
  ]

/-! ## Summary Statistics -/

private def statusLabel : RepairStatus → String
  | .logged      => "LOGGED"
  | .autoFixable => "AUTO-FIXABLE"
  | .fixed       => "FIXED"
  | .wontfix     => "WONTFIX"
  | .deferred    => "DEFERRED"

#eval! do
  IO.println "=== Repair Decision Log Summary ==="
  IO.println s!"Total decisions: {repairDecisions.length}"
  let automatable := repairDecisions.filter fun (d : RepairDecision) => d.automatable
  IO.println s!"Fully automatable: {automatable.length}"
  IO.println s!"Requires judgment: {repairDecisions.length - automatable.length}"
  let fixed := repairDecisions.filter fun (d : RepairDecision) => d.status == RepairStatus.fixed
  let autoFixable := repairDecisions.filter fun (d : RepairDecision) => d.status == RepairStatus.autoFixable
  let logged := repairDecisions.filter fun (d : RepairDecision) => d.status == RepairStatus.logged
  let deferred := repairDecisions.filter fun (d : RepairDecision) => d.status == RepairStatus.deferred
  IO.println s!"Status: {fixed.length} fixed, {autoFixable.length} auto-fixable, {logged.length} logged, {deferred.length} deferred"
  -- WM witness totals
  let totalWM := repairDecisions.foldl (fun acc (d : RepairDecision) => acc + d.witnesses.length) 0
  let passedWM := repairDecisions.foldl (fun acc (d : RepairDecision) =>
    acc + (d.witnesses.filter fun (w : EvidenceModel.WMWitness) => w.passed).length) 0
  let failedWM := totalWM - passedWM
  IO.println s!"WM witnesses: {passedWM}/{totalWM} passed ({failedWM} failed)"
  -- Review state totals
  let pending := repairDecisions.filter fun (d : RepairDecision) =>
    d.reviewState == EvidenceModel.ReviewState.pendingReview
  let approved := repairDecisions.filter fun (d : RepairDecision) =>
    d.reviewState == EvidenceModel.ReviewState.reviewApproved
  let applied := repairDecisions.filter fun (d : RepairDecision) =>
    d.reviewState == EvidenceModel.ReviewState.applied
  let verified := repairDecisions.filter fun (d : RepairDecision) =>
    d.reviewState == EvidenceModel.ReviewState.verified
  let rejected := repairDecisions.filter fun (d : RepairDecision) =>
    d.reviewState == EvidenceModel.ReviewState.rejected
  IO.println s!"Review: {pending.length} pending, {approved.length} approved, {applied.length} applied, {verified.length} verified, {rejected.length} rejected"
  let fixedWithoutHuman := repairDecisions.filter fun (d : RepairDecision) =>
    d.status == RepairStatus.fixed &&
      !d.reviewers.contains "human" &&
      !d.reviewers.contains "human_zar"
  IO.println s!"Review gate: {fixedWithoutHuman.length} fixed decisions missing recorded human quorum"
  IO.println ""
  for d in repairDecisions do
    IO.println s!"  D{d.decisionId} [{statusLabel d.status}] {d.concept}"
    IO.println s!"    SUMO says: {d.originalSUMOClass}"
    IO.println s!"    Enache says: {d.enacheClass}"
    IO.println s!"    We say: {d.ourClass}"
    IO.println s!"    Recommended: {d.recommendedClass}"
    IO.println s!"    BinaryEvidence: {d.evidenceFor.length} for, {d.evidenceAgainst.length} against"
    IO.println s!"    Confidence: {d.confidence}"
    IO.println s!"    Automatable: {d.automatable}"
    IO.println s!"    WM witnesses: {d.witnesses.length}"
    IO.println s!"    Needs split: {d.needsSplit}"
    IO.println ""

/-! ## Assurance Scoring (English-doc evidence + WM witnesses)

Converts WM witnesses and English-doc atoms to EvidenceAtoms, then
computes Beta-posterior assurance scores per decision using
`computeAssuranceWith` from EvidenceModel. -/

/-- Convert a WM witness to an EvidenceAtom (checkLang source type). -/
private def wmWitnessToAtom (did : Nat) (arch : EvidenceModel.RepairArchetype)
    (w : EvidenceModel.WMWitness) : EvidenceModel.EvidenceAtom :=
  { claimId := s!"wm.{w.id}"
  , decisionId := did
  , archetype := arch
  , direction := if w.passed then .supports else .contradicts
  , sourceType := .checkLang
  , sourceRef := w.sourceRef
  , formalExpr := w.query
  , strength := if w.passed then 1.0 else 0.8
  , confidence := 1.0  -- checkLang is proven sound
  , independenceGroup := s!"wm.{w.id}"
  , artifactHash := "" }

#eval! do
  IO.println "=== English-Doc BinaryEvidence + Assurance Scoring ==="
  IO.println s!"Total english-doc atoms: {DocEvidence.englishDocAtomCount}"
  IO.println ""
  for d in repairDecisions do
    let did := d.decisionId
    let wmAtoms := d.witnesses.map (wmWitnessToAtom did d.archetype)
    let docAtoms := DocEvidence.englishDocAtomsFor did
    let allAtoms := wmAtoms ++ docAtoms
    let completeness := if d.witnesses.isEmpty then 0.5 else 1.0
    let summary := EvidenceModel.computeAssuranceWith did d.archetype allAtoms completeness
    if !wmAtoms.isEmpty || !docAtoms.isEmpty then
      IO.println s!"  D{did} ({d.concept.take 35})"
      IO.println s!"    archetype: {repr d.archetype}"
      IO.println s!"    wm={wmAtoms.length} doc={docAtoms.length} | α={summary.alpha} β={summary.beta}"
      IO.println s!"    posterior={summary.posteriorMean} ass={summary.assuranceLower95}"
      IO.println ""

/-! ## Strengthening Log

Separate from repair: improvements that go BEYOND fixing inconsistencies.
These are NOT broken — they could be better. Repair first, strengthen later.
Each entry records what COULD be improved and why we're NOT doing it yet.
-/

/-- A proposed improvement that is not an inconsistency fix. -/
structure StrengtheningProposal where
  concept : String
  currentClass : String
  proposedClass : String
  rationale : String
  blockedBy : String      -- why not now?
  priority : String       -- "low" | "medium" | "high"
  deriving Repr

def strengtheningProposals : List StrengtheningProposal :=
  [ { concept := "Pain: EmotionalState → StateOfMind?"
    , currentClass := "EmotionalState (after repair)"
    , proposedClass := "StateOfMind"
    , rationale := "IASP says pain is 'sensory AND emotional', broader than " ++
        "just emotional. StateOfMind ⊃ EmotionalState captures this. " ++
        "But Pleasure is also 'sensory and emotional' per IASP and is " ++
        "EmotionalState — so the distinction may not be meaningful."
    , blockedBy := "Repair phase: EmotionalState matches 39 peers. " ++
        "Reclassifying to StateOfMind is strengthening, not repair."
    , priority := "low" }

  , { concept := "Virtue/Vice field-relative contrariness"
    , currentClass := "(disjoint VirtueAttribute ViceAttribute)"
    , proposedClass := "Field-relative: same-field V and W are contrary"
    , rationale := "Aristotle's doctrine of the mean: courage is the mean " ++
        "between cowardice and recklessness. Within a field, virtue and " ++
        "vice are contrary. Across fields, they're independent."
    , blockedBy := "Needs VirtueField infrastructure not yet in FOET."
    , priority := "medium" }

  , { concept := "contraryAttribute list type"
    , currentClass := "Binary in our encoding"
    , proposedClass := "[El Attribute] -> Formula (GF list type)"
    , rationale := "SUMO declares VariableArityRelation. Enache correctly " ++
        "uses GF list type. Our binary encoding misses ternary+ cases."
    , blockedBy := "Requires GF list type infrastructure in our Lean encoding."
    , priority := "medium" }

  , { concept := "AsymmetricRelation cross-type theorem"
    , currentClass := "Omitted for cross-type (vacuously true)"
    , proposedClass := "Prove: disjoint(BT(C1),BT(C2)) → asymmetric(R:C1×C2)"
    , rationale := "The vacuity should be a proven theorem, not just an omission."
    , blockedBy := "Formalization priority — repair comes first."
    , priority := "low" }
  ]

#eval! do
  IO.println "=== Strengthening Proposals (NOT repairs — future improvements) ==="
  IO.println s!"Total proposals: {strengtheningProposals.length}"
  IO.println ""
  for s in strengtheningProposals do
    IO.println s!"  [{s.priority}] {s.concept}"
    IO.println s!"    Current: {s.currentClass}"
    IO.println s!"    Proposed: {s.proposedClass}"
    IO.println s!"    Blocked: {s.blockedBy}"
    IO.println ""

end Mettapedia.Languages.GF.SUMO.RepairLog
