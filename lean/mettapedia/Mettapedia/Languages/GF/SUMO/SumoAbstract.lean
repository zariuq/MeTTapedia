/-
# SUMO-GF Abstract Syntax

Encodes the abstract syntax of the SUMO-GF grammar (Enache & Angelov 2012,
distributed with GF 3.3) in our `Category`/`FunctionSig` framework.

The original SUMO-GF uses dependent types:
  cat Class; El Class; Ind Class; Var Class; SubClass (c1,c2 : Class); ...

We flatten these to concrete sort names for each FOET-relevant SUMO class:
  El_Entity, El_Physical, El_Agent, Ind_Human, Var_Process, ...

This shallow flattening loses parametric polymorphism but gains compatibility
with the existing GF→OSLF→WM pipeline (same as English/Czech).

## Source

- Basic.gf from https://hackage-content.haskell.org/package/gf-3.3/src/examples/SUMO/
- Merge.gf (class/relation declarations)
- Scope: FOET Stratum 0-1 (~50 classes from Appendix A of the paper)

## References

- Enache & Angelov, "Typeful Ontologies with Direct Multilingual Verbalization" (2012)
- Brown, Pease & Urban, "Translating SUMO-K to Higher-Order Set Theory" (2023)
-/

import Mettapedia.Languages.GF.Core
import Mettapedia.Languages.GF.Abstract

namespace Mettapedia.Languages.GF.SUMO.SumoAbstract

open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract

/-! ## SUMO-GF Categories

From Basic.gf:
  cat Class; El Class; Ind Class; SubClass (c1,c2:Class);
      Inherits Class Class; Formula; Desc Class; Var Class; Stmt;

We flatten dependent categories: for each SUMO class C in the FOET fragment,
we create `El_C`, `Ind_C`, `Var_C` as concrete base categories.
-/

namespace SumoCategory

-- Core structural categories (class-independent)
def SumoClass : Category := .base "SumoClass"
def Formula : Category := .base "SumoFormula"
def Stmt : Category := .base "SumoStmt"

-- Helper: build flattened category names for a SUMO class
def El (c : String) : Category := .base s!"El_{c}"
def Ind (c : String) : Category := .base s!"Ind_{c}"
def Var (c : String) : Category := .base s!"Var_{c}"
def SubClassCat (c1 c2 : String) : Category := .base s!"SubClass_{c1}_{c2}"
def InheritsCat (c1 c2 : String) : Category := .base s!"Inherits_{c1}_{c2}"
def Desc (c : String) : Category := .base s!"Desc_{c}"

end SumoCategory

/-! ## FOET-Relevant SUMO Classes (Strata 0-2)

From Appendix A of the paper: the upward closure from FOET leaf concepts
to Entity.  ~50 classes organized in 3 strata.
-/

/-- Stratum 0: Upper ontology core (9 classes) -/
def stratum0Classes : List String :=
  [ "Entity", "Physical", "Abstract"
  , "Object", "Process", "Attribute"
  , "SetOrClass", "Relation", "Proposition" ]

/-- Stratum 1: Mid-level anchors (~20 classes) -/
def stratum1Classes : List String :=
  [ -- Agent chain
    "AutonomousAgent", "SentientAgent", "CognitiveAgent"
    -- Object subtypes
  , "SelfConnectedObject", "CorpuscularObject", "ContentBearingObject"
    -- Physical subtypes
  , "ContentBearingPhysical", "LinguisticExpression", "Sentence"
    -- Attribute hierarchy
  , "InternalAttribute", "BiologicalAttribute", "PsychologicalAttribute"
  , "RelationalAttribute", "NormativeAttribute", "ObjectiveNorm"
    -- Abstract subtypes
  , "Set", "Class", "Predicate", "Function"
  , "List", "SingleValuedRelation", "InheritableRelation"
    -- Propositions
  , "Argument", "Formula"
    -- Additional sorts for D23/D26 checkLang evidence
  , "Group", "Artifact" ]

/-- Stratum 2: FOET-specific classes (~20 classes) -/
def stratum2Classes : List String :=
  [ -- Ethical attributes
    "MoralAttribute", "MoralValueAttribute", "DeonticAttribute"
  , "MoralVirtueAttribute", "VirtueAttribute", "ViceAttribute"
    -- Agents and processes
  , "VirtuousAgent", "ViciousAgent"
  , "AutonomousAgentProcess", "VirtuousAct", "ViciousAct"
  , "ChoicePoint", "Situation"
    -- Propositions/theories
  , "ActionFormula", "Conjecture", "EthicalTheory"
    -- Values
  , "Value", "UtilityFormulaFn"
    -- Ethics paradigms + needed intermediates
  , "Consequentialism", "Ethics"
    -- Intermediate classes needed for complete parent chains (from FOET KIF):
  , "Theory", "Philosophy" ]

/-- All FOET-relevant SUMO classes. -/
def allFOETClasses : List String :=
  stratum0Classes ++ stratum1Classes ++ stratum2Classes

/-! ## Category Generation

For each SUMO class, we generate: El_C, Ind_C, Var_C categories.
Plus structural categories and cross-class SubClass/Inherits for known hierarchy edges.
-/

/-- All categories in the flattened SUMO-GF grammar. -/
def sumoAllCategoryNames : List String :=
  -- Structural categories
  ["SumoClass", "SumoFormula", "SumoStmt"]
  -- Per-class categories
  ++ (allFOETClasses.flatMap fun c => [s!"El_{c}", s!"Ind_{c}", s!"Var_{c}", s!"Desc_{c}"])

def sumoAllCategories : List Category :=
  sumoAllCategoryNames.map Category.base

/-! ## SUMO-GF Function Signatures

Encoding of Basic.gf's `data`/`fun` declarations plus Merge.gf relation
signatures, flattened for each concrete SUMO class pair.
-/

namespace SumoFunctionSig

open SumoCategory

private abbrev arr := Category.arrow

/-! ### Basic.gf: Class-forming operations -/

/-- `both : Class → Class → Class` -/
def bothClass : FunctionSig := ⟨"sumo_both", arr SumoClass (arr SumoClass SumoClass)⟩

/-- `either : Class → Class → Class` -/
def eitherClass : FunctionSig := ⟨"sumo_either", arr SumoClass (arr SumoClass SumoClass)⟩

/-! ### Basic.gf: Logical connectives -/

def negation : FunctionSig := ⟨"sumo_not", arr Formula Formula⟩
def conjunction : FunctionSig := ⟨"sumo_and", arr Formula (arr Formula Formula)⟩
def disjunction : FunctionSig := ⟨"sumo_or", arr Formula (arr Formula Formula)⟩
def implication : FunctionSig := ⟨"sumo_impl", arr Formula (arr Formula Formula)⟩
def equivalence : FunctionSig := ⟨"sumo_equiv", arr Formula (arr Formula Formula)⟩

/-! ### Basic.gf: Statements -/

def formStm : FunctionSig := ⟨"sumo_formStm", arr Formula Stmt⟩

/-! ### Quantifiers (flattened per class)

Original: `forall : (c : Class) → (Var c → Formula) → Formula`
Flattened: for each class C, `forall_C : Var_C → Formula → Formula`

We use TermParam.abstraction to represent the (Var c → Formula) binder.
But in our flat encoding, we represent it as an arrow type.
-/

/-- Generate `forall_C : Var_C → Formula` for a class C.

In the original GF, this is `forall : (c:Class) → (Var c → Formula) → Formula`
with a higher-order binder.  We flatten it: `forall_C` takes a Var_C argument
and a Formula body (the body implicitly binds the variable). -/
def forallClass (c : String) : FunctionSig :=
  ⟨s!"sumo_forall_{c}", arr (Var c) (arr Formula Formula)⟩

/-- Generate `exists_C : Var_C → Formula` -/
def existsClass (c : String) : FunctionSig :=
  ⟨s!"sumo_exists_{c}", arr (Var c) (arr Formula Formula)⟩

/-! ### Coercions (flattened per known subclass edge)

Original: `el : (c1,c2:Class) → Inherits c1 c2 → Ind c1 → El c2`
Flattened: for each known edge (c1 ⊑ c2), generate `el_c1_c2 : Ind_c1 → El_c2`

We generate these for the known SUMO subclass hierarchy.
-/

/-- Generate coercion `el_c1_c2 : Ind_c1 → El_c2` -/
def elCoercion (c1 c2 : String) : FunctionSig :=
  ⟨s!"sumo_el_{c1}_{c2}", arr (Ind c1) (El c2)⟩

/-- Generate coercion `var_c1_c2 : Var_c1 → El_c2` -/
def varCoercion (c1 c2 : String) : FunctionSig :=
  ⟨s!"sumo_var_{c1}_{c2}", arr (Var c1) (El c2)⟩

/-- Reflexive coercion: `el_C_C : Ind_C → El_C` (from inhz) -/
def elRefl (c : String) : FunctionSig :=
  ⟨s!"sumo_el_{c}_{c}", arr (Ind c) (El c)⟩

/-- Reflexive var coercion: `var_C_C : Var_C → El_C` -/
def varRefl (c : String) : FunctionSig :=
  ⟨s!"sumo_var_{c}_{c}", arr (Var c) (El c)⟩

/-! ### SUMO Relations (from Merge.gf / FOET KIF)

These are the typed predicate signatures for SUMO relations used by FOET.
Original GF: `fun attribute : El Agent → El Attribute → Formula`
Flattened: `sumo_attribute : El_Agent → El_Attribute → Formula`
-/

/-- `instance : El_C → SumoClass → Formula` (reified: C is a class constant) -/
def instanceRel (c : String) : FunctionSig :=
  ⟨s!"sumo_instance_{c}", arr (El c) (arr SumoClass Formula)⟩

/-- `subclass : SumoClass → SumoClass → Formula` -/
def subclassRel : FunctionSig :=
  ⟨"sumo_subclass", arr SumoClass (arr SumoClass Formula)⟩

/-- `attribute : El_Object → El_Attribute → Formula`
  KIF: `(domain attribute 1 Object)` (Merge.kif:1754)
  Enache: `El Object -> El Attribute -> Formula`
  Previously we had El_Agent (too tight). Fixed to match KIF/GF. -/
def attributeRel : FunctionSig :=
  ⟨"sumo_attribute", arr (El "Object") (arr (El "Attribute") Formula)⟩

/-- `property : El_Entity → El_Attribute → Formula`
  KIF: `(domain property 1 Entity)` `(domain property 2 Attribute)` (Merge.kif:1742-1743)
  Superrelation of `attribute`: `(subrelation attribute property)` (Merge.kif:1753)
  Use `property` when arg 1 may be a Process (not just Object).
  Decision 15: FOET uses (attribute ?ACT ?VIRTUE) where ?ACT : Process.
  Process ⊄ Object but Process ⊂ Entity, so `property` is the correct relation. -/
def propertyRel : FunctionSig :=
  ⟨"sumo_property", arr (El "Entity") (arr (El "Attribute") Formula)⟩

/-- `agent : El_Process → El_AutonomousAgent → Formula`
  KIF: `(domain agent 1 Process)` `(domain agent 2 AutonomousAgent)` (Merge.kif:2468-2469)
  Enache uses `Agent` (= Object) because AutonomousAgent is missing from GF.
  We correctly use AutonomousAgent per KIF. -/
def hasAgent : FunctionSig :=
  ⟨"sumo_agent", arr (El "Process") (arr (El "AutonomousAgent") Formula)⟩

/-- `desires : El_CognitiveAgent → Formula → Formula` -/
def desires : FunctionSig :=
  ⟨"sumo_desires", arr (El "CognitiveAgent") (arr Formula Formula)⟩

/-- `holdsObligation : Formula → El_Agent → Formula` -/
def holdsObligation : FunctionSig :=
  ⟨"sumo_holdsObligation", arr Formula (arr (El "AutonomousAgent") Formula)⟩

/-- `contraryAttribute : El_Attribute → El_Attribute → Formula`
  KIF: `(instance contraryAttribute VariableArityRelation)` (Merge.kif:448)
  Enache: `[El Attribute] -> Formula` (variable-arity GF list type)
  We encode as binary for simplicity. This is a known simplification.
  CANARY: `(contraryAttribute Hot Warm Cold)` must be expressible in full encoding.
  BUG WITNESS: `(contraryAttribute Pleasure Pain)` exposes Pain/Attribute confusion
  since Pain : Process but contraryAttribute expects Attribute arguments. -/
def contraryAttribute : FunctionSig :=
  ⟨"sumo_contraryAttribute", arr (El "Attribute") (arr (El "Attribute") Formula)⟩

/-- `holdsValue : El_Agent → El_Value → Formula` -/
def holdsValue : FunctionSig :=
  ⟨"sumo_holdsValue", arr (El "AutonomousAgent") (arr (El "Value") Formula)⟩

/-- `realizes : El_Process → Formula → Formula` -/
def realizesFormula : FunctionSig :=
  ⟨"sumo_realizesFormula", arr (El "Process") (arr Formula Formula)⟩

/-- `capableInSituation : SumoClass → El_Relation → El_Object → El_Situation → Formula`
  KIF: `(domainSubclass capableInSituation 1 Process)`
       `(domain capableInSituation 2 CaseRole)` — CaseRole ⊂ Relation (Abstract branch)
       `(domain capableInSituation 3 Object)`
       `(domain capableInSituation 4 Situation)`
  (FOET:627-631)
  Previously had El_AutonomousAgent for arg 2 and El_Situation for arg 3 — both wrong.
  NTT gap detection found: CaseRole ∉ BT(AutonomousAgent), Object ∉ BT(Situation). -/
def capableInSituation : FunctionSig :=
  ⟨"sumo_capableInSituation",
   arr SumoClass (arr (El "Relation") (arr (El "Object") (arr (El "Situation") Formula)))⟩

/-! ### FOET-specific relations -/

/-- `virtueDesire : El_VirtueAttribute → Formula → Formula` -/
def virtueDesire : FunctionSig :=
  ⟨"sumo_virtueDesire", arr (El "VirtueAttribute") (arr Formula Formula)⟩

/-- `morallyGood : Formula → Formula`
    (simplified: MorallyGood as a unary predicate on formulas) -/
def morallyGood : FunctionSig :=
  ⟨"sumo_morallyGood", arr Formula Formula⟩

/-- `morallyBad : Formula → Formula` -/
def morallyBad : FunctionSig :=
  ⟨"sumo_morallyBad", arr Formula Formula⟩

/-! ### Statement constructors -/

/-- `subClassStm_c1_c2 : SubClass_c1_c2 → Stmt`
  For known hierarchy edges. We simplify to just constants. -/
def subClassStmConst (c1 c2 : String) : FunctionSig :=
  ⟨s!"sumo_subClassStm_{c1}_{c2}", Stmt⟩

/-- `instStm_C : Ind_C → Stmt` -/
def instStmClass (c : String) : FunctionSig :=
  ⟨s!"sumo_instStm_{c}", arr (Ind c) Stmt⟩

end SumoFunctionSig

/-! ## Known SUMO Subclass Edges

The subclass hierarchy edges from Merge.kif that are in the FOET upward closure.
Each edge (c1, c2) means `subclass c1 c2`.
-/

/-- Direct (one-step) subclass edges from KIF/FOET. -/
def sumoSubclassEdges : List (String × String) :=
  [ -- Stratum 0: top level
    ("Physical", "Entity"), ("Abstract", "Entity")
  , ("Object", "Physical"), ("Process", "Physical")
  , ("Attribute", "Abstract"), ("SetOrClass", "Abstract")
  , ("Relation", "Abstract"), ("Proposition", "Abstract")
    -- Stratum 1: Object subtypes
  , ("SelfConnectedObject", "Object")
  , ("CorpuscularObject", "SelfConnectedObject")
  , ("ContentBearingObject", "CorpuscularObject")
    -- Agent chain
  , ("AutonomousAgent", "Object")
  , ("SentientAgent", "AutonomousAgent")
  , ("CognitiveAgent", "SentientAgent")
    -- Physical subtypes
  , ("ContentBearingPhysical", "Physical")
  , ("LinguisticExpression", "ContentBearingPhysical")
  , ("Sentence", "LinguisticExpression")
  , ("Situation", "Physical")
    -- Formula/Sentence
  , ("Formula", "Sentence")
    -- Attribute hierarchy
  , ("InternalAttribute", "Attribute")
  , ("BiologicalAttribute", "InternalAttribute")
  , ("PsychologicalAttribute", "BiologicalAttribute")
  , ("RelationalAttribute", "Attribute")
  , ("NormativeAttribute", "RelationalAttribute")
  , ("ObjectiveNorm", "NormativeAttribute")
    -- Abstract subtypes
  , ("Set", "SetOrClass"), ("Class", "SetOrClass")
  , ("Predicate", "Relation"), ("Predicate", "InheritableRelation")
  , ("Function", "SingleValuedRelation"), ("Function", "InheritableRelation")
  , ("SingleValuedRelation", "Relation")
  , ("InheritableRelation", "Relation")
  , ("List", "Abstract")
  , ("Argument", "Proposition")
    -- Stratum 2: FOET-specific
  , ("MoralAttribute", "NormativeAttribute")
  , ("MoralValueAttribute", "MoralAttribute")
  , ("DeonticAttribute", "ObjectiveNorm")
  , ("DeonticAttribute", "MoralAttribute")
  , ("MoralVirtueAttribute", "MoralAttribute")
  , ("VirtueAttribute", "MoralVirtueAttribute")
  , ("VirtueAttribute", "PsychologicalAttribute")
  , ("ViceAttribute", "MoralVirtueAttribute")
  , ("ViceAttribute", "PsychologicalAttribute")
  , ("VirtuousAgent", "AutonomousAgent")
  , ("ViciousAgent", "AutonomousAgent")
  , ("AutonomousAgentProcess", "Process")
  , ("VirtuousAct", "AutonomousAgentProcess")
  , ("ViciousAct", "AutonomousAgentProcess")
  , ("ChoicePoint", "Set")
  , ("ActionFormula", "Formula")
  , ("Conjecture", "Sentence")
  , ("Value", "Abstract")
  , ("Consequentialism", "Ethics")
    -- EthicalTheory ⊂ Theory ⊂ Set (FOET:1421, 1311)
  , ("EthicalTheory", "Theory")
  , ("Theory", "Set")
    -- Ethics ⊂ Philosophy ⊂ FieldOfStudy ⊂ Proposition (MLO, Merge.kif:16966)
    -- Philosophy is a FieldOfStudy which is a Proposition (a body of propositions)
  , ("Ethics", "Philosophy")
  , ("Philosophy", "Proposition")
    -- UtilityFormulaFn ⊂ UnaryFunction ⊂ Function (Function IS in our classes)
  , ("UtilityFormulaFn", "Function")
    -- D23 evidence: (subclass Artifact Object) per Merge.kif:15853
    -- The gap: `contains` demands SelfConnectedObject, but Artifact's
    -- parent is Object directly (no intermediate SelfConnectedObject edge).
  , ("Artifact", "Object")
    -- D26 evidence: Group has dual inheritance (Merge.kif:16423-16424)
    -- (subclass Group Collection) AND (subclass Group AutonomousAgent)
  , ("Group", "AutonomousAgent")  -- Merge.kif:16424
  ]

/-! ## Transitive Closure of Subclass Edges

The class hierarchy is a rewrite system: `el_c1_c2(x)` rewrites an `Ind c1`
to an `El c2`. For ◇ to see all reachable types in one step, we need the
transitive closure. This corresponds to GF's `inhs` (transitive inheritance):

  `inhs(c1, c2, c3, p12, p23) : Inherits c1 c3`

given `p12 : Inherits c1 c2` and `p23 : Inherits c2 c3`.

For ~50 classes with ~54 direct edges, the closure is small and finite.
-/

/-- Compute transitive closure of a relation on strings.
    Uses a simple fixed-point iteration (bounded by edge count). -/
def transitiveClose (edges : List (String × String)) : List (String × String) :=
  let rec go (fuel : Nat) (current : List (String × String)) : List (String × String) :=
    match fuel with
    | 0 => current
    | fuel + 1 =>
      let new := current.flatMap fun ⟨a, b⟩ =>
        (current.filter fun ⟨c, _⟩ => c == b).filterMap fun ⟨_, d⟩ =>
          if current.contains (a, d) then none else some (a, d)
      if new.isEmpty then current
      else go fuel (current ++ new)
  go edges.length edges

/-- All subclass edges including transitive closure.
    E.g., includes (CognitiveAgent, Object) via CognitiveAgent → SentientAgent
    → AutonomousAgent → Object. -/
def sumoSubclassEdgesClosed : List (String × String) :=
  transitiveClose sumoSubclassEdges

/-! ## Assembling All Function Signatures -/

open SumoFunctionSig in
/-- All SUMO-GF function signatures for the FOET fragment. -/
def sumoAllFunctions : List FunctionSig :=
  -- Class-forming
  [ bothClass, eitherClass ]
  -- Logical connectives
  ++ [ negation, conjunction, disjunction, implication, equivalence, formStm ]
  -- Quantifiers (per class)
  ++ (allFOETClasses.flatMap fun c => [forallClass c, existsClass c])
  -- Reflexive coercions (per class)
  ++ (allFOETClasses.flatMap fun c => [elRefl c, varRefl c])
  -- Subclass coercions (per transitive closure of hierarchy)
  -- Uses closed edges so ◇ sees full reachability in one step.
  -- This models GF's `inhs` transitivity: Inherits c1 c3 from Inherits c1 c2 + Inherits c2 c3.
  ++ (sumoSubclassEdgesClosed.flatMap fun ⟨c1, c2⟩ => [elCoercion c1 c2, varCoercion c1 c2])
  -- SUMO relations
  ++ [ subclassRel, attributeRel, propertyRel, hasAgent, desires
     , holdsObligation, contraryAttribute
     , holdsValue, realizesFormula, capableInSituation
     , virtueDesire, morallyGood, morallyBad ]
  -- Instance relations (per class)
  ++ (allFOETClasses.map instanceRel)
  -- Subclass statement constants (per known edge)
  ++ (sumoSubclassEdges.map fun ⟨c1, c2⟩ => subClassStmConst c1 c2)
  -- Instance statement constructors (per class)
  ++ (allFOETClasses.map instStmClass)

/-! ## Class Constants

Each SUMO class name is also a constant of type SumoClass.
-/

/-- Class name constants: `Entity : SumoClass`, `Physical : SumoClass`, etc. -/
def sumoClassConstants : List FunctionSig :=
  allFOETClasses.map fun c => ⟨s!"sumo_class_{c}", SumoCategory.SumoClass⟩

/-! ## Individual Constants (SUMO instances)

Named individuals from SUMO and FOET (MorallyGood, MorallyBad, etc.)
-/

def sumoIndividualConstants : List FunctionSig :=
  [ -- Moral value attributes
    ⟨"sumo_ind_MorallyGood", SumoCategory.Ind "MoralValueAttribute"⟩
  , ⟨"sumo_ind_MorallyBad", SumoCategory.Ind "MoralValueAttribute"⟩
  , ⟨"sumo_ind_MorallyPermissible", SumoCategory.Ind "MoralValueAttribute"⟩
    -- Pain: reclassified from Process to EmotionalState (Decision 1, RESOLVED)
    -- BinaryEvidence: IASP 2020, similarity-class 39:1, checkLang proven inconsistent
  , ⟨"sumo_ind_Pain", SumoCategory.Ind "Attribute"⟩     -- REPAIRED: EmotionalState ⊂ Attribute
  , ⟨"sumo_ind_Pleasure", SumoCategory.Ind "Attribute"⟩ -- EmotionalState ⊂ Attribute
    -- Schwartz values
  , ⟨"sumo_ind_ValuingBenevolence", SumoCategory.Ind "Value"⟩
  , ⟨"sumo_ind_ValuingPower", SumoCategory.Ind "Value"⟩
  , ⟨"sumo_ind_ValuingAchievement", SumoCategory.Ind "Value"⟩
  ]

/-- Complete function signature list. -/
def sumoAllFunctionsFull : List FunctionSig :=
  sumoAllFunctions ++ sumoClassConstants ++ sumoIndividualConstants

end Mettapedia.Languages.GF.SUMO.SumoAbstract
