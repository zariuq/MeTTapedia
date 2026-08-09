import Mettapedia.GSLT.LanguageDef.ProofGSLTDAGTransport

/-!
# Versioned wire semantics for chronological proof articles

The article ABI shared by the Lean checker, the executable reference
checker, and native replay: a versioned, chronological node list in which
every node carries a stable rule identifier, its exact arguments in
authored order, and exact child references; the target judgment and the
checked root are stored redundantly and checked, never inferred.

The wire carrier is the symbolic S-expression layer (`WireTerm`) on which
the executable reference checker and the native candidate already operate;
byte transport of that carrier is a separate, lower layer.

Contents:

* total canonical encoders and fail-closed decoders for patterns, rule
  instances, DAG references, nodes, and whole articles;
* **round trip** — decoding a rendered value yields the value;
* **canonicality** — a wire term that decodes at all *is* the canonical
  rendering of its value, so each value has exactly one wire form;
* **digest identity** — equality of canonical renderings is equality of
  articles;
* the versioned article checker `checkWireArticle`, its fail-closed
  version gate, and **exact checker correspondence**: an article is
  accepted exactly when its target has a closed derivation
  (soundness via the chronological DAG checker's exact reconstruction,
  completeness via linearization of a derivation into an article).
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## The wire carrier -/

/-- Symbolic S-expression wire terms. -/
inductive WireTerm where
  | symbol (name : String)
  | natural (value : Nat)
  | list (items : List WireTerm)
deriving Repr

/-! ## Encoders

Encoders are total and canonical: one wire form per value. -/

def encodeOptionString : Option String → WireTerm
  | none => .symbol "ONone"
  | some name => .list [.symbol "OSome", .symbol name]

def encodeCollType : CollType → WireTerm
  | .vec => .symbol "CVec"
  | .hashBag => .symbol "CHashBag"
  | .hashSet => .symbol "CHashSet"

mutual

def encodePattern : Pattern → WireTerm
  | .fvar name => .list [.symbol "PFVar", .symbol name]
  | .bvar index => .list [.symbol "PBVar", .natural index]
  | .apply constructor arguments =>
      .list [.symbol "PApply", .symbol constructor,
        .list (encodePatternList arguments)]
  | .lambda binder body =>
      .list [.symbol "PLambda", encodeOptionString binder,
        encodePattern body]
  | .multiLambda arity binders body =>
      .list [.symbol "PMultiLambda", .natural arity,
        .list (binders.map WireTerm.symbol), encodePattern body]
  | .subst body replacement =>
      .list [.symbol "PSubst", encodePattern body,
        encodePattern replacement]
  | .collection collectionType elements rest =>
      .list [.symbol "PCollection", encodeCollType collectionType,
        .list (encodePatternList elements), encodeOptionString rest]
termination_by pattern => sizeOf pattern

def encodePatternList : List Pattern → List WireTerm
  | [] => []
  | pattern :: patterns => encodePattern pattern :: encodePatternList patterns
termination_by patterns => sizeOf patterns

end

def encodeRuleInstance (ruleInstance : RuleInstance) : WireTerm :=
  .list [.symbol "WRuleInst", .symbol ruleInstance.ruleId.value,
    .list (encodePatternList ruleInstance.arguments)]

def encodeReference : OpenDAGReference → WireTerm
  | .premise index => .list [.symbol "RPremise", .natural index]
  | .node id => .list [.symbol "RNode", .natural id]

def encodeReferenceList : List OpenDAGReference → List WireTerm
  | [] => []
  | reference :: references =>
      encodeReference reference :: encodeReferenceList references

def encodeNode (node : OpenDAGNode) : WireTerm :=
  .list [.symbol "WNode", .natural node.id,
    encodeRuleInstance node.ruleInstance,
    .list (encodeReferenceList node.children)]

def encodeNodeList : List OpenDAGNode → List WireTerm
  | [] => []
  | node :: nodes => encodeNode node :: encodeNodeList nodes

/-- One versioned chronological proof article. -/
structure WireArticle where
  version : Nat
  nodes : List OpenDAGNode
  rootId : Nat
  target : Pattern
deriving Repr

def encodeArticle (article : WireArticle) : WireTerm :=
  .list [.symbol "WArticle", .natural article.version,
    .list (encodeNodeList article.nodes), .natural article.rootId,
    encodePattern article.target]

/-! ## Decoders

Decoders are fail-closed: any shape outside the canonical grammar yields
`none`. -/

def decodeOptionString : WireTerm → Option (Option String)
  | .symbol "ONone" => some none
  | .list [.symbol "OSome", .symbol name] => some (some name)
  | _ => none

def decodeCollType : WireTerm → Option CollType
  | .symbol "CVec" => some .vec
  | .symbol "CHashBag" => some .hashBag
  | .symbol "CHashSet" => some .hashSet
  | _ => none

def decodeSymbolList : List WireTerm → Option (List String)
  | [] => some []
  | .symbol name :: items => do
      let rest ← decodeSymbolList items
      some (name :: rest)
  | _ => none

mutual

def decodePattern : WireTerm → Option Pattern
  | .list [.symbol "PFVar", .symbol name] => some (.fvar name)
  | .list [.symbol "PBVar", .natural index] => some (.bvar index)
  | .list [.symbol "PApply", .symbol constructor, .list arguments] => do
      let decoded ← decodePatternList arguments
      some (.apply constructor decoded)
  | .list [.symbol "PLambda", binder, body] => do
      let decodedBinder ← decodeOptionString binder
      let decodedBody ← decodePattern body
      some (.lambda decodedBinder decodedBody)
  | .list [.symbol "PMultiLambda", .natural arity, .list binders, body] => do
      let decodedBinders ← decodeSymbolList binders
      let decodedBody ← decodePattern body
      some (.multiLambda arity decodedBinders decodedBody)
  | .list [.symbol "PSubst", body, replacement] => do
      let decodedBody ← decodePattern body
      let decodedReplacement ← decodePattern replacement
      some (.subst decodedBody decodedReplacement)
  | .list [.symbol "PCollection", collectionType, .list elements, rest] => do
      let decodedType ← decodeCollType collectionType
      let decodedElements ← decodePatternList elements
      let decodedRest ← decodeOptionString rest
      some (.collection decodedType decodedElements decodedRest)
  | _ => none
termination_by term => sizeOf term

def decodePatternList : List WireTerm → Option (List Pattern)
  | [] => some []
  | item :: items => do
      let head ← decodePattern item
      let tail ← decodePatternList items
      some (head :: tail)
termination_by items => sizeOf items

end

def decodeRuleInstance : WireTerm → Option RuleInstance
  | .list [.symbol "WRuleInst", .symbol ruleId, .list arguments] => do
      let decoded ← decodePatternList arguments
      some ⟨⟨ruleId⟩, decoded⟩
  | _ => none

def decodeReference : WireTerm → Option OpenDAGReference
  | .list [.symbol "RPremise", .natural index] => some (.premise index)
  | .list [.symbol "RNode", .natural id] => some (.node id)
  | _ => none

def decodeReferenceList : List WireTerm → Option (List OpenDAGReference)
  | [] => some []
  | item :: items => do
      let head ← decodeReference item
      let tail ← decodeReferenceList items
      some (head :: tail)

def decodeNode : WireTerm → Option OpenDAGNode
  | .list [.symbol "WNode", .natural id, ruleInstance, .list children] => do
      let decodedInstance ← decodeRuleInstance ruleInstance
      let decodedChildren ← decodeReferenceList children
      some ⟨id, decodedInstance, decodedChildren⟩
  | _ => none

def decodeNodeList : List WireTerm → Option (List OpenDAGNode)
  | [] => some []
  | item :: items => do
      let head ← decodeNode item
      let tail ← decodeNodeList items
      some (head :: tail)

def decodeArticle : WireTerm → Option WireArticle
  | .list [.symbol "WArticle", .natural version, .list nodes,
      .natural rootId, target] => do
      let decodedNodes ← decodeNodeList nodes
      let decodedTarget ← decodePattern target
      some ⟨version, decodedNodes, rootId, decodedTarget⟩
  | _ => none

/-! ## Round trips: decoding a rendered value yields the value -/

@[simp] theorem decodeOptionString_encodeOptionString
    (binder : Option String) :
    decodeOptionString (encodeOptionString binder) = some binder := by
  cases binder <;> rfl

@[simp] theorem decodeCollType_encodeCollType (collectionType : CollType) :
    decodeCollType (encodeCollType collectionType) = some collectionType := by
  cases collectionType <;> rfl

@[simp] theorem decodeSymbolList_map (names : List String) :
    decodeSymbolList (names.map WireTerm.symbol) = some names := by
  induction names with
  | nil => rfl
  | cons name rest inductionHypothesis =>
      simp [decodeSymbolList, inductionHypothesis]

mutual

@[simp] theorem decodePattern_encodePattern (pattern : Pattern) :
    decodePattern (encodePattern pattern) = some pattern := by
  cases pattern with
  | fvar name => simp [encodePattern, decodePattern]
  | bvar index => simp [encodePattern, decodePattern]
  | apply constructor arguments =>
      simp [encodePattern, decodePattern,
        decodePatternList_encodePatternList arguments]
  | lambda binder body =>
      simp [encodePattern, decodePattern,
        decodePattern_encodePattern body]
  | multiLambda arity binders body =>
      simp [encodePattern, decodePattern,
        decodePattern_encodePattern body]
  | subst body replacement =>
      simp [encodePattern, decodePattern,
        decodePattern_encodePattern body,
        decodePattern_encodePattern replacement]
  | collection collectionType elements rest =>
      simp [encodePattern, decodePattern,
        decodePatternList_encodePatternList elements]
termination_by sizeOf pattern

@[simp] theorem decodePatternList_encodePatternList
    (patterns : List Pattern) :
    decodePatternList (encodePatternList patterns) = some patterns := by
  cases patterns with
  | nil => simp [encodePatternList, decodePatternList]
  | cons pattern rest =>
      simp [encodePatternList, decodePatternList,
        decodePattern_encodePattern pattern,
        decodePatternList_encodePatternList rest]
termination_by sizeOf patterns

end

@[simp] theorem decodeRuleInstance_encodeRuleInstance
    (ruleInstance : RuleInstance) :
    decodeRuleInstance (encodeRuleInstance ruleInstance) =
      some ruleInstance := by
  simp [encodeRuleInstance, decodeRuleInstance]

@[simp] theorem decodeReference_encodeReference
    (reference : OpenDAGReference) :
    decodeReference (encodeReference reference) = some reference := by
  cases reference <;> rfl

@[simp] theorem decodeReferenceList_encodeReferenceList
    (references : List OpenDAGReference) :
    decodeReferenceList (encodeReferenceList references) =
      some references := by
  induction references with
  | nil => rfl
  | cons reference rest inductionHypothesis =>
      simp [encodeReferenceList, decodeReferenceList, inductionHypothesis]

@[simp] theorem decodeNode_encodeNode (node : OpenDAGNode) :
    decodeNode (encodeNode node) = some node := by
  simp [encodeNode, decodeNode]

@[simp] theorem decodeNodeList_encodeNodeList (nodes : List OpenDAGNode) :
    decodeNodeList (encodeNodeList nodes) = some nodes := by
  induction nodes with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      simp [encodeNodeList, decodeNodeList, inductionHypothesis]

@[simp] theorem decodeArticle_encodeArticle (article : WireArticle) :
    decodeArticle (encodeArticle article) = some article := by
  simp [encodeArticle, decodeArticle]

/-! ## Canonicality: each value has exactly one wire form -/

theorem decodeOptionString_canonical {term : WireTerm}
    {binder : Option String}
    (decoded : decodeOptionString term = some binder) :
    term = encodeOptionString binder := by
  rw [decodeOptionString.eq_def] at decoded
  split at decoded
  · injection decoded with valueEq
    subst valueEq
    rfl
  · injection decoded with valueEq
    subst valueEq
    rfl
  · cases decoded

theorem decodeCollType_canonical {term : WireTerm}
    {collectionType : CollType}
    (decoded : decodeCollType term = some collectionType) :
    term = encodeCollType collectionType := by
  rw [decodeCollType.eq_def] at decoded
  split at decoded
  · injection decoded with valueEq
    subst valueEq
    rfl
  · injection decoded with valueEq
    subst valueEq
    rfl
  · injection decoded with valueEq
    subst valueEq
    rfl
  · cases decoded

theorem decodeSymbolList_canonical :
    ∀ {items : List WireTerm} {names : List String},
      decodeSymbolList items = some names →
      items = names.map WireTerm.symbol := by
  intro items
  induction items with
  | nil =>
      intro names decoded
      have namesEq : some ([] : List String) = some names := decoded
      rw [← Option.some.inj namesEq]
      rfl
  | cons item rest inductionHypothesis =>
      intro names decoded
      cases item with
      | symbol name =>
          simp only [decodeSymbolList] at decoded
          cases restDecoded : decodeSymbolList rest with
          | none => rw [restDecoded] at decoded; cases decoded
          | some restNames =>
              rw [restDecoded] at decoded
              have namesEq : some (name :: restNames) = some names := decoded
              rw [← Option.some.inj namesEq]
              simp only [List.map_cons, List.cons.injEq, true_and]
              exact inductionHypothesis restDecoded
      | natural value => simp [decodeSymbolList] at decoded
      | list items => simp [decodeSymbolList] at decoded

mutual

theorem decodePattern_canonical :
    ∀ (term : WireTerm) {pattern : Pattern},
      decodePattern term = some pattern → term = encodePattern pattern := by
  intro term pattern decoded
  rw [decodePattern.eq_def] at decoded
  split at decoded
  · rename_i name
    have patternEq : some (Pattern.fvar name) = some pattern := decoded
    rw [← Option.some.inj patternEq]
    simp [encodePattern]
  · rename_i index
    have patternEq : some (Pattern.bvar index) = some pattern := decoded
    rw [← Option.some.inj patternEq]
    simp [encodePattern]
  · rename_i constructor arguments
    cases argumentsDecoded : decodePatternList arguments with
    | none => rw [argumentsDecoded] at decoded; cases decoded
    | some decodedArguments =>
        rw [argumentsDecoded] at decoded
        have patternEq :
            some (Pattern.apply constructor decodedArguments) =
              some pattern := decoded
        rw [← Option.some.inj patternEq]
        simp [encodePattern,
          decodePatternList_canonical arguments argumentsDecoded]
  · rename_i binder body
    cases binderDecoded : decodeOptionString binder with
    | none => rw [binderDecoded] at decoded; cases decoded
    | some decodedBinder =>
        rw [binderDecoded] at decoded
        cases bodyDecoded : decodePattern body with
        | none => rw [bodyDecoded] at decoded; cases decoded
        | some decodedBody =>
            rw [bodyDecoded] at decoded
            have patternEq :
                some (Pattern.lambda decodedBinder decodedBody) =
                  some pattern := decoded
            rw [← Option.some.inj patternEq]
            simp [encodePattern, decodeOptionString_canonical binderDecoded,
              decodePattern_canonical body bodyDecoded]
  · rename_i arity binders body
    cases bindersDecoded : decodeSymbolList binders with
    | none => rw [bindersDecoded] at decoded; cases decoded
    | some decodedBinders =>
        rw [bindersDecoded] at decoded
        cases bodyDecoded : decodePattern body with
        | none => rw [bodyDecoded] at decoded; cases decoded
        | some decodedBody =>
            rw [bodyDecoded] at decoded
            have patternEq :
                some (Pattern.multiLambda arity decodedBinders
                  decodedBody) = some pattern := decoded
            rw [← Option.some.inj patternEq]
            simp [encodePattern, decodeSymbolList_canonical bindersDecoded,
              decodePattern_canonical body bodyDecoded]
  · rename_i body replacement
    cases bodyDecoded : decodePattern body with
    | none => rw [bodyDecoded] at decoded; cases decoded
    | some decodedBody =>
        rw [bodyDecoded] at decoded
        cases replacementDecoded : decodePattern replacement with
        | none => rw [replacementDecoded] at decoded; cases decoded
        | some decodedReplacement =>
            rw [replacementDecoded] at decoded
            have patternEq :
                some (Pattern.subst decodedBody decodedReplacement) =
                  some pattern := decoded
            rw [← Option.some.inj patternEq]
            simp [encodePattern, decodePattern_canonical body bodyDecoded,
              decodePattern_canonical replacement replacementDecoded]
  · rename_i collectionType elements rest
    cases typeDecoded : decodeCollType collectionType with
    | none => rw [typeDecoded] at decoded; cases decoded
    | some decodedType =>
        rw [typeDecoded] at decoded
        cases elementsDecoded : decodePatternList elements with
        | none => rw [elementsDecoded] at decoded; cases decoded
        | some decodedElements =>
            rw [elementsDecoded] at decoded
            cases restDecoded : decodeOptionString rest with
            | none => rw [restDecoded] at decoded; cases decoded
            | some decodedRest =>
                rw [restDecoded] at decoded
                have patternEq :
                    some (Pattern.collection decodedType decodedElements
                      decodedRest) = some pattern := decoded
                rw [← Option.some.inj patternEq]
                simp [encodePattern, decodeCollType_canonical typeDecoded,
                  decodePatternList_canonical elements elementsDecoded,
                  decodeOptionString_canonical restDecoded]
  · cases decoded
termination_by term => sizeOf term

theorem decodePatternList_canonical :
    ∀ (items : List WireTerm) {patterns : List Pattern},
      decodePatternList items = some patterns →
      items = encodePatternList patterns := by
  intro items patterns decoded
  cases items with
  | nil =>
      simp only [decodePatternList] at decoded
      have patternsEq : some ([] : List Pattern) = some patterns := decoded
      rw [← Option.some.inj patternsEq]
      simp [encodePatternList]
  | cons item rest =>
      simp only [decodePatternList] at decoded
      cases headDecoded : decodePattern item with
      | none => rw [headDecoded] at decoded; cases decoded
      | some head =>
          rw [headDecoded] at decoded
          cases restDecoded : decodePatternList rest with
          | none => rw [restDecoded] at decoded; cases decoded
          | some tail =>
              rw [restDecoded] at decoded
              have patternsEq : some (head :: tail) = some patterns :=
                decoded
              rw [← Option.some.inj patternsEq]
              simp [encodePatternList,
                decodePattern_canonical item headDecoded,
                decodePatternList_canonical rest restDecoded]
termination_by items => sizeOf items

end

theorem decodeRuleInstance_canonical {term : WireTerm}
    {ruleInstance : RuleInstance}
    (decoded : decodeRuleInstance term = some ruleInstance) :
    term = encodeRuleInstance ruleInstance := by
  rw [decodeRuleInstance.eq_def] at decoded
  split at decoded
  · rename_i ruleId arguments
    cases argumentsDecoded : decodePatternList arguments with
    | none => rw [argumentsDecoded] at decoded; cases decoded
    | some decodedArguments =>
        rw [argumentsDecoded] at decoded
        have instanceEq :
            some (⟨⟨ruleId⟩, decodedArguments⟩ : RuleInstance) =
              some ruleInstance := decoded
        rw [← Option.some.inj instanceEq]
        simp [encodeRuleInstance,
          decodePatternList_canonical arguments argumentsDecoded]
  · cases decoded

theorem decodeReference_canonical {term : WireTerm}
    {reference : OpenDAGReference}
    (decoded : decodeReference term = some reference) :
    term = encodeReference reference := by
  rw [decodeReference.eq_def] at decoded
  split at decoded
  · injection decoded with valueEq
    subst valueEq
    rfl
  · injection decoded with valueEq
    subst valueEq
    rfl
  · cases decoded

theorem decodeReferenceList_canonical :
    ∀ {items : List WireTerm} {references : List OpenDAGReference},
      decodeReferenceList items = some references →
      items = encodeReferenceList references := by
  intro items
  induction items with
  | nil =>
      intro references decoded
      have referencesEq : some [] = some references := decoded
      rw [← Option.some.inj referencesEq]
      rfl
  | cons item rest inductionHypothesis =>
      intro references decoded
      simp only [decodeReferenceList] at decoded
      cases headDecoded : decodeReference item with
      | none => rw [headDecoded] at decoded; cases decoded
      | some head =>
          rw [headDecoded] at decoded
          cases restDecoded : decodeReferenceList rest with
          | none => rw [restDecoded] at decoded; cases decoded
          | some tail =>
              rw [restDecoded] at decoded
              have referencesEq : some (head :: tail) = some references :=
                decoded
              rw [← Option.some.inj referencesEq]
              simp [encodeReferenceList,
                decodeReference_canonical headDecoded,
                inductionHypothesis restDecoded]

theorem decodeNode_canonical {term : WireTerm} {node : OpenDAGNode}
    (decoded : decodeNode term = some node) :
    term = encodeNode node := by
  rw [decodeNode.eq_def] at decoded
  split at decoded
  · rename_i id ruleInstance children
    cases instanceDecoded : decodeRuleInstance ruleInstance with
    | none => rw [instanceDecoded] at decoded; cases decoded
    | some decodedInstance =>
        rw [instanceDecoded] at decoded
        cases childrenDecoded : decodeReferenceList children with
        | none => rw [childrenDecoded] at decoded; cases decoded
        | some decodedChildren =>
            rw [childrenDecoded] at decoded
            have nodeEq :
                some (⟨id, decodedInstance, decodedChildren⟩ :
                  OpenDAGNode) = some node := decoded
            rw [← Option.some.inj nodeEq]
            simp [encodeNode, decodeRuleInstance_canonical instanceDecoded,
              decodeReferenceList_canonical childrenDecoded]
  · cases decoded

theorem decodeNodeList_canonical :
    ∀ {items : List WireTerm} {nodes : List OpenDAGNode},
      decodeNodeList items = some nodes →
      items = encodeNodeList nodes := by
  intro items
  induction items with
  | nil =>
      intro nodes decoded
      have nodesEq : some [] = some nodes := decoded
      rw [← Option.some.inj nodesEq]
      rfl
  | cons item rest inductionHypothesis =>
      intro nodes decoded
      simp only [decodeNodeList] at decoded
      cases headDecoded : decodeNode item with
      | none => rw [headDecoded] at decoded; cases decoded
      | some head =>
          rw [headDecoded] at decoded
          cases restDecoded : decodeNodeList rest with
          | none => rw [restDecoded] at decoded; cases decoded
          | some tail =>
              rw [restDecoded] at decoded
              have nodesEq : some (head :: tail) = some nodes := decoded
              rw [← Option.some.inj nodesEq]
              simp [encodeNodeList, decodeNode_canonical headDecoded,
                inductionHypothesis restDecoded]

theorem decodeArticle_canonical {term : WireTerm} {article : WireArticle}
    (decoded : decodeArticle term = some article) :
    term = encodeArticle article := by
  rw [decodeArticle.eq_def] at decoded
  split at decoded
  · rename_i version nodes rootId target
    cases nodesDecoded : decodeNodeList nodes with
    | none => rw [nodesDecoded] at decoded; cases decoded
    | some decodedNodes =>
        rw [nodesDecoded] at decoded
        cases targetDecoded : decodePattern target with
        | none => rw [targetDecoded] at decoded; cases decoded
        | some decodedTarget =>
            rw [targetDecoded] at decoded
            have articleEq :
                some (⟨version, decodedNodes, rootId, decodedTarget⟩ :
                  WireArticle) = some article := decoded
            rw [← Option.some.inj articleEq]
            simp [encodeArticle, decodeNodeList_canonical nodesDecoded,
              decodePattern_canonical target targetDecoded]
  · cases decoded

/-! ## Digest identity: canonical renderings identify articles -/

theorem encodePattern_inj {left right : Pattern}
    (encodingEq : encodePattern left = encodePattern right) : left = right := by
  have := decodePattern_encodePattern left
  rw [encodingEq, decodePattern_encodePattern right] at this
  exact (Option.some.inj this).symm

/-- The canonical rendering is a content digest: two articles render
identically exactly when they are equal. -/
theorem encodeArticle_inj_iff (left right : WireArticle) :
    encodeArticle left = encodeArticle right ↔ left = right := by
  constructor
  · intro encodingEq
    have := decodeArticle_encodeArticle left
    rw [encodingEq, decodeArticle_encodeArticle right] at this
    exact (Option.some.inj this).symm
  · intro articleEq
    rw [articleEq]

/-! ## The versioned article checker -/

/-- The current article ABI version. -/
def wireArticleVersion : Nat := 1

/-- Check one versioned closed article: the version gate, then the
chronological DAG checker over the empty premise context with the stored
root and the redundantly stored target. -/
def checkWireArticle (presentation : ValidatedPresentation)
    (article : WireArticle) : Bool :=
  decide (article.version = wireArticleVersion) &&
    checkOpenDAGBlocks presentation [] article.target article.rootId
      [article.nodes]

/-- Check a rendered wire term: decode, then check.  Terms outside the
canonical grammar fail closed. -/
def checkWireTerm (presentation : ValidatedPresentation)
    (term : WireTerm) : Bool :=
  match decodeArticle term with
  | some article => checkWireArticle presentation article
  | none => false

@[simp] theorem checkWireTerm_encodeArticle
    (presentation : ValidatedPresentation) (article : WireArticle) :
    checkWireTerm presentation (encodeArticle article) =
      checkWireArticle presentation article := by
  simp [checkWireTerm]

/-- A conservative rule-table refinement preserves acceptance of the exact
same versioned article.  The article, node identifiers, rule instances, child
order, and sharing are unchanged; only the presentation against which the
artifact is replayed grows.  No converse is claimed for rule deletion or
semantic revision. -/
theorem checkWireArticle_true_of_ruleLookupRefines
    {source target : ValidatedPresentation}
    (refines : RuleLookupRefines source target) {article : WireArticle}
    (checked : checkWireArticle source article = true) :
    checkWireArticle target article = true := by
  simp only [checkWireArticle, Bool.and_eq_true] at checked ⊢
  exact ⟨checked.1,
    checkOpenDAGBlocks_true_of_ruleLookupRefines refines checked.2⟩

/-- Conservative refinement also preserves acceptance through the symbolic
decode-then-check boundary. -/
theorem checkWireTerm_true_of_ruleLookupRefines
    {source target : ValidatedPresentation}
    (refines : RuleLookupRefines source target) {term : WireTerm}
    (checked : checkWireTerm source term = true) :
    checkWireTerm target term = true := by
  cases decoded : decodeArticle term with
  | none => simp [checkWireTerm, decoded] at checked
  | some article =>
      have sourceChecked : checkWireArticle source article = true := by
        simpa [checkWireTerm, decoded] using checked
      simpa [checkWireTerm, decoded] using
        checkWireArticle_true_of_ruleLookupRefines refines sourceChecked

/-- Unknown versions are rejected before any node is examined. -/
theorem checkWireArticle_version_gate
    {presentation : ValidatedPresentation} {article : WireArticle}
    (wrongVersion : article.version ≠ wireArticleVersion) :
    checkWireArticle presentation article = false := by
  simp [checkWireArticle, wrongVersion]

/-- Soundness: an accepted article's target has a closed derivation. -/
theorem checkWireArticle_sound {presentation : ValidatedPresentation}
    {article : WireArticle}
    (accepted : checkWireArticle presentation article = true) :
    Nonempty (Derivation presentation article.target) := by
  simp only [checkWireArticle, Bool.and_eq_true, decide_eq_true_eq]
    at accepted
  obtain ⟨proof, derivation, -, -⟩ :=
    checkOpenDAGBlocks_exact_derivation accepted.2
  exact ⟨derivation.close⟩

/-! ## Linearization: every derivation has an accepted article -/

mutual

/-- Linearize a closed derivation into chronological nodes with sequential
fresh identifiers: the nodes emitted, the root identifier, and the next
unused identifier. -/
def Derivation.linearize {presentation : ValidatedPresentation} :
    {goal : Pattern} → Derivation presentation goal → Nat →
      List OpenDAGNode × Nat × Nat
  | _, .byRule ruleInstance _ children, nextId =>
      let result := DerivationList.linearize children nextId
      (result.1 ++
        [⟨result.2.2, ruleInstance,
          result.2.1.map OpenDAGReference.node⟩],
        result.2.2, result.2.2 + 1)

/-- Linearize ordered child derivations: the nodes emitted, the child root
identifiers in order, and the next unused identifier. -/
def DerivationList.linearize {presentation : ValidatedPresentation} :
    {goals : List Pattern} → DerivationList presentation goals → Nat →
      List OpenDAGNode × List Nat × Nat
  | _, .nil, nextId => ([], [], nextId)
  | _, .cons head tail, nextId =>
      let headResult := Derivation.linearize head nextId
      let tailResult := DerivationList.linearize tail headResult.2.2
      (headResult.1 ++ tailResult.1, headResult.2.1 :: tailResult.2.1,
        tailResult.2.2)

end

private theorem findOpenDAGEntry?_none_of_bound :
    ∀ {entries : List OpenDAGEntry} {bound id : Nat},
      (∀ entry ∈ entries, entry.id < bound) → bound ≤ id →
      findOpenDAGEntry? entries id = none := by
  intro entries
  induction entries with
  | nil => intro bound id _ _; rfl
  | cons entry rest inductionHypothesis =>
      intro bound id entriesBound le
      have entryBound := entriesBound entry (List.mem_cons_self ..)
      have entryNe : entry.id ≠ id := by omega
      simp only [findOpenDAGEntry?, if_neg entryNe]
      exact inductionHypothesis
        (fun e member => entriesBound e (List.mem_cons_of_mem _ member)) le

private theorem checkOpenDAGNodes?_append
    (presentation : ValidatedPresentation) (context : List Pattern) :
    ∀ (first second : List OpenDAGNode) (entries : List OpenDAGEntry),
      checkOpenDAGNodes? presentation context entries (first ++ second) =
        (checkOpenDAGNodes? presentation context entries first).bind
          (fun middle =>
            checkOpenDAGNodes? presentation context middle second) := by
  intro first
  induction first with
  | nil =>
      intro second entries
      simp [checkOpenDAGNodes?]
  | cons node rest inductionHypothesis =>
      intro second entries
      simp only [List.cons_append, checkOpenDAGNodes?]
      cases headCheck : checkOpenDAGNode? presentation context entries node
        with
      | none => rfl
      | some middle => exact inductionHypothesis second middle

/-- Resolve node references whose identifiers map to entries carrying
exactly the expected goals. -/
private theorem resolveOpenDAGChildren?_of_forall₂
    {entries : List OpenDAGEntry} :
    ∀ {childIds : List Nat} {goals : List Pattern},
      List.Forall₂ (fun id goal => ∃ ghost,
        findOpenDAGEntry? entries id =
          some ⟨id, goal, ghost⟩) childIds goals →
      ∃ proofs, resolveOpenDAGChildren? [] entries goals
        (childIds.map OpenDAGReference.node) = some proofs := by
  intro childIds goals correspondence
  induction correspondence with
  | nil => exact ⟨[], rfl⟩
  | cons headFact tailFacts inductionHypothesis =>
      rename_i id goal restIds restGoals
      obtain ⟨ghost, found⟩ := headFact
      obtain ⟨restProofs, restResolved⟩ := inductionHypothesis
      refine ⟨ghost :: restProofs, ?_⟩
      simp [resolveOpenDAGChildren?, resolveOpenDAGReference?, found,
        restResolved]

mutual

/-- Checking the linearized nodes of a derivation extends any bounded
environment, preserves bounded lookups, and installs the root goal at the
root identifier. -/
private theorem linearize_checks {presentation : ValidatedPresentation}
    {goal : Pattern} (derivation : Derivation presentation goal)
    (nextId : Nat) (entries : List OpenDAGEntry)
    (entriesBound : ∀ entry ∈ entries, entry.id < nextId) :
    ∃ entries',
      checkOpenDAGNodes? presentation [] entries
          (Derivation.linearize derivation nextId).1 = some entries' ∧
      nextId ≤ (Derivation.linearize derivation nextId).2.2 ∧
      (Derivation.linearize derivation nextId).2.1 <
        (Derivation.linearize derivation nextId).2.2 ∧
      nextId ≤ (Derivation.linearize derivation nextId).2.1 ∧
      (∀ entry ∈ entries',
        entry.id < (Derivation.linearize derivation nextId).2.2) ∧
      (∀ id : Nat, id < nextId →
        findOpenDAGEntry? entries' id = findOpenDAGEntry? entries id) ∧
      ∃ ghost, findOpenDAGEntry? entries'
          (Derivation.linearize derivation nextId).2.1 =
        some ⟨(Derivation.linearize derivation nextId).2.1, goal, ghost⟩ := by
  cases derivation with
  | byRule ruleInstance application children =>
      rcases childLin : DerivationList.linearize children nextId with
        ⟨childNodes, childIds, afterChildren⟩
      obtain ⟨entries₁, childrenChecked, nextLe, -, -, entriesBound₁,
          findPreserve₁, rootsFound⟩ :=
        linearizeList_checks children nextId entries entriesBound
      rw [childLin] at childrenChecked nextLe entriesBound₁ rootsFound
      dsimp only at childrenChecked nextLe entriesBound₁ rootsFound
      have instantiated :=
        instantiateRule?_eq_some_iff_application.mpr application
      have freshMiss : findOpenDAGEntry? entries₁ afterChildren = none :=
        findOpenDAGEntry?_none_of_bound entriesBound₁ (Nat.le_refl _)
      obtain ⟨proofs, resolved⟩ :=
        resolveOpenDAGChildren?_of_forall₂ rootsFound
      have nodeChecked : checkOpenDAGNode? presentation [] entries₁
          ⟨afterChildren, ruleInstance,
            childIds.map OpenDAGReference.node⟩ =
          some (⟨afterChildren, goal,
            .node ruleInstance proofs⟩ :: entries₁) := by
        simp [checkOpenDAGNode?, freshMiss, instantiated, resolved]
      refine ⟨(⟨afterChildren, goal,
        .node ruleInstance proofs⟩ : OpenDAGEntry) :: entries₁,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Derivation.linearize, childLin]
        rw [checkOpenDAGNodes?_append presentation [] childNodes _ entries,
          childrenChecked]
        simp [checkOpenDAGNodes?, nodeChecked]
      · simp only [Derivation.linearize, childLin]
        omega
      · simp only [Derivation.linearize, childLin]
        omega
      · simp only [Derivation.linearize, childLin]
        omega
      · simp only [Derivation.linearize, childLin]
        intro entry member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact Nat.lt_succ_self afterChildren
        · have := entriesBound₁ entry tailMember
          omega
      · intro id idLt
        have idNe : afterChildren ≠ id := by omega
        simp only [findOpenDAGEntry?, if_neg idNe]
        exact findPreserve₁ id idLt
      · simp only [Derivation.linearize, childLin]
        refine ⟨.node ruleInstance proofs, ?_⟩
        simp [findOpenDAGEntry?]
termination_by sizeOf derivation

/-- Checking linearized child derivations installs every child root goal
at its identifier. -/
private theorem linearizeList_checks {presentation : ValidatedPresentation}
    {goals : List Pattern} (derivations : DerivationList presentation goals)
    (nextId : Nat) (entries : List OpenDAGEntry)
    (entriesBound : ∀ entry ∈ entries, entry.id < nextId) :
    ∃ entries',
      checkOpenDAGNodes? presentation [] entries
          (DerivationList.linearize derivations nextId).1 = some entries' ∧
      nextId ≤ (DerivationList.linearize derivations nextId).2.2 ∧
      (∀ id ∈ (DerivationList.linearize derivations nextId).2.1,
        id < (DerivationList.linearize derivations nextId).2.2) ∧
      (∀ id ∈ (DerivationList.linearize derivations nextId).2.1,
        nextId ≤ id) ∧
      (∀ entry ∈ entries',
        entry.id < (DerivationList.linearize derivations nextId).2.2) ∧
      (∀ id : Nat, id < nextId →
        findOpenDAGEntry? entries' id = findOpenDAGEntry? entries id) ∧
      List.Forall₂ (fun id goal => ∃ ghost,
          findOpenDAGEntry? entries' id = some ⟨id, goal, ghost⟩)
        (DerivationList.linearize derivations nextId).2.1 goals := by
  cases derivations with
  | nil =>
      refine ⟨entries, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [DerivationList.linearize, checkOpenDAGNodes?]
      · simp [DerivationList.linearize]
      · simp [DerivationList.linearize]
      · simp [DerivationList.linearize]
      · simpa [DerivationList.linearize] using entriesBound
      · exact fun id _ => rfl
      · simp only [DerivationList.linearize]
        exact List.Forall₂.nil
  | cons head tail =>
      rcases headLin : Derivation.linearize head nextId with
        ⟨headNodes, headRoot, afterHead⟩
      obtain ⟨entries₁, headChecked, headLe, headRootLt, headRootGe,
          entriesBound₁, findPreserve₁, headFound⟩ :=
        linearize_checks head nextId entries entriesBound
      rw [headLin] at headChecked headLe headRootLt headRootGe entriesBound₁ headFound
      dsimp only at headChecked headLe headRootLt headRootGe entriesBound₁ headFound
      rcases tailLin : DerivationList.linearize tail afterHead with
        ⟨tailNodes, tailRoots, afterTail⟩
      obtain ⟨entries₂, tailChecked, tailLe, tailRootsLt, tailRootsGe,
          entriesBound₂, findPreserve₂, tailFound⟩ :=
        linearizeList_checks tail afterHead entries₁ entriesBound₁
      rw [tailLin] at tailChecked tailLe tailRootsLt tailRootsGe entriesBound₂ tailFound
      dsimp only at tailChecked tailLe tailRootsLt tailRootsGe entriesBound₂ tailFound
      obtain ⟨headGhost, headEntryFound⟩ := headFound
      refine ⟨entries₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [DerivationList.linearize, headLin, tailLin]
        rw [checkOpenDAGNodes?_append presentation [] headNodes tailNodes
          entries, headChecked]
        simpa using tailChecked
      · simp only [DerivationList.linearize, headLin, tailLin]
        omega
      · simp only [DerivationList.linearize, headLin, tailLin]
        intro id member
        rcases List.mem_cons.mp member with rfl | tailMember
        · omega
        · exact tailRootsLt id tailMember
      · simp only [DerivationList.linearize, headLin, tailLin]
        intro id member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact headRootGe
        · have := tailRootsGe id tailMember
          omega
      · simp only [DerivationList.linearize, headLin, tailLin]
        exact entriesBound₂
      · intro id idLt
        rw [findPreserve₂ id (by omega)]
        exact findPreserve₁ id idLt
      · simp only [DerivationList.linearize, headLin, tailLin]
        refine List.Forall₂.cons ⟨headGhost, ?_⟩ tailFound
        rw [findPreserve₂ headRoot (by omega)]
        exact headEntryFound
termination_by sizeOf derivations

end

/-- The canonical accepted article of a closed derivation. -/
def articleOfDerivation {presentation : ValidatedPresentation}
    {goal : Pattern} (derivation : Derivation presentation goal) :
    WireArticle :=
  ⟨wireArticleVersion, (Derivation.linearize derivation 0).1,
    (Derivation.linearize derivation 0).2.1, goal⟩

/-- Completeness: the linearized article of a derivation is accepted, with
the derivation's goal as its stored target. -/
theorem checkWireArticle_articleOfDerivation
    {presentation : ValidatedPresentation} {goal : Pattern}
    (derivation : Derivation presentation goal) :
    checkWireArticle presentation (articleOfDerivation derivation) =
      true := by
  obtain ⟨entries, checked, -, -, -, -, -, ghost, rootFound⟩ :=
    linearize_checks derivation 0 [] (by intro entry member; cases member)
  have blocksOk : checkOpenDAGBlocks presentation [] goal
      (Derivation.linearize derivation 0).2.1
      [(Derivation.linearize derivation 0).1] = true := by
    simp [checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
      checked, rootFound]
  simp [checkWireArticle, articleOfDerivation, wireArticleVersion, blocksOk]

/-- Exact correspondence: some accepted version-1 article carries a goal
exactly when the goal has a closed derivation. -/
theorem wireArticle_correspondence (presentation : ValidatedPresentation)
    (goal : Pattern) :
    (∃ article : WireArticle, article.target = goal ∧
        checkWireArticle presentation article = true) ↔
      Nonempty (Derivation presentation goal) := by
  constructor
  · rintro ⟨article, rfl, accepted⟩
    exact checkWireArticle_sound accepted
  · rintro ⟨derivation⟩
    exact ⟨articleOfDerivation derivation, rfl,
      checkWireArticle_articleOfDerivation derivation⟩

end Mettapedia.GSLT.LanguageDef.ProofGSLT
