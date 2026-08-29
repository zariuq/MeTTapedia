import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.DerivationCheckMachineLanguageDef
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# A compact word-stream presentation derived from the derivation-check machine

`DerivationWordMachine` is the target language of a mechanical representation
change.  Each semantic `DerivationCheckMachine` transition is retained, but its
instruction-list head is replaced by a compact word record.  The added
`DWMDecodeRecord` premise recovers the exact instruction pattern expected by
the source transition.  It performs bounded record decoding only; all node,
relevance, calculus, service-state, root, and final checks remain the original
authored premises.

This separation is intentional.  A native backend may fuse decoding with the
retained transition, while the presentation still exposes which source
instruction and which semantic premises determine every target step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineLanguageDef

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

def query (relation : String) (arguments : List Pattern) : Premise :=
  .relationQuery relation arguments

def wordsNil : Pattern := a "dwm:words-nil"

def wordsCons (word rest : Pattern) : Pattern :=
  a "dwm:words-cons" [word, rest]

def recordsNil : Pattern := a "dwm:records-nil"

def recordsCons (record rest : Pattern) : Pattern :=
  a "dwm:records-cons" [record, rest]

def decoded (instruction : Pattern) : Pattern :=
  a "dwm:decoded" [instruction]

def decodeRejected : Pattern := a "dwm:decode-rejected"

def run (records nodes nextId root serviceState : Pattern) : Pattern :=
  a "dwm:run" [records, nodes, nextId, root, serviceState]

def halted (outcome nodes : Pattern) : Pattern :=
  a "dwm:halted" [outcome, nodes]

def liftTypeExpr : TypeExpr → TypeExpr
  | .base "Instructions" => .base "Records"
  | .base name => .base name
  | .arrow domain codomain => .arrow (liftTypeExpr domain) (liftTypeExpr codomain)
  | .multiBinder body => .multiBinder (liftTypeExpr body)
  | .collection kind element => .collection kind (liftTypeExpr element)

def liftContext (context : List (String × TypeExpr)) :
    List (String × TypeExpr) :=
  context.map fun entry => (entry.1, liftTypeExpr entry.2)

def liftPattern : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply "dcm:run" arguments => .apply "dwm:run" (arguments.map liftPattern)
  | .apply "dcm:halted" arguments =>
      .apply "dwm:halted" (arguments.map liftPattern)
  | .apply label arguments => .apply label (arguments.map liftPattern)
  | .lambda name body => .lambda name (liftPattern body)
  | .multiLambda count names body =>
      .multiLambda count names (liftPattern body)
  | .subst body replacement =>
      .subst (liftPattern body) (liftPattern replacement)
  | .collection kind elements rest =>
      .collection kind (elements.map liftPattern) rest

def liftPremise : Premise → Premise
  | .freshness condition =>
      .freshness { condition with term := liftPattern condition.term }
  | .congruence left right =>
      .congruence (liftPattern left) (liftPattern right)
  | .relationQuery relation arguments =>
      .relationQuery relation (arguments.map liftPattern)
  | .forAll collection parameter body =>
      .forAll collection parameter (liftPremise body)

/-- Recover the instruction matched by a source transition, when it consumes
one instruction.  The missing-finish transition is the unique `none` case. -/
def sourceInstruction? (left : Pattern) : Option Pattern :=
  match left with
  | .apply "dcm:run"
      (.apply "dcm:instructions-cons" (instruction :: _rest :: []) :: _) =>
      some instruction
  | _ => none

def liftLeft (left : Pattern) : Pattern :=
  match left with
  | .apply "dcm:run"
      (.apply "dcm:instructions-nil" [] :: nodes :: nextId :: root ::
        serviceState :: []) =>
      run recordsNil (liftPattern nodes) (liftPattern nextId)
        (liftPattern root) (liftPattern serviceState)
  | .apply "dcm:run"
      (.apply "dcm:instructions-cons"
        (_instruction ::
          .apply "dcm:instructions-cons" (_next :: rest :: []) :: []) ::
        nodes :: nextId :: root :: serviceState :: []) =>
      run (recordsCons (v "record")
        (recordsCons (v "nextRecord") (liftPattern rest)))
        (liftPattern nodes) (liftPattern nextId) (liftPattern root)
        (liftPattern serviceState)
  | .apply "dcm:run"
      (.apply "dcm:instructions-cons"
        (_instruction :: .apply "dcm:instructions-nil" [] :: []) ::
        nodes :: nextId :: root :: serviceState :: []) =>
      run (recordsCons (v "record") recordsNil)
        (liftPattern nodes) (liftPattern nextId) (liftPattern root)
        (liftPattern serviceState)
  | .apply "dcm:run"
      (.apply "dcm:instructions-cons" (_instruction :: rest :: []) ::
        nodes :: nextId :: root :: serviceState :: []) =>
      run (recordsCons (v "record") (liftPattern rest))
        (liftPattern nodes) (liftPattern nextId) (liftPattern root)
        (liftPattern serviceState)
  | other => liftPattern other

/-- Lift one authored semantic transition to the compact record carrier. -/
def liftRewrite (rewrite : RewriteRule) : RewriteRule :=
  let instruction? := sourceInstruction? rewrite.left
  {
    name := "dwm:lift:" ++ rewrite.name
    typeContext :=
      (if instruction?.isSome then [("record", .base "Words")] else []) ++
        (if rewrite.name = "dcm:finish-trailing" then
          [("nextRecord", .base "Words")]
        else []) ++
        liftContext rewrite.typeContext
    premises :=
      (match instruction? with
      | none => []
      | some instruction =>
          [query "DWMDecodeRecord" [v "record", decoded instruction]]) ++
        rewrite.premises.map liftPremise
    left := liftLeft rewrite.left
    right := liftPattern rewrite.right
  }

def liftedTransitions : List RewriteRule :=
  DerivationCheckMachineLanguageDef.transitions.map liftRewrite

/-- A malformed record is an explicit machine outcome rather than a stuck
term.  A decoder implementation may produce this decision only after checking
that none of the five record layouts is admitted. -/
def malformedRecordTransition : RewriteRule := {
  name := "dwm:malformed-record"
  typeContext := [
    ("record", .base "Words"), ("rest", .base "Records"),
    ("nodes", .base "Nodes"), ("nextId", .base "Index"),
    ("root", .base "RootState"),
    ("serviceState", .base "ServiceState")]
  premises := [query "DWMDecodeRecord" [v "record", decodeRejected]]
  left := run (recordsCons (v "record") (v "rest")) (v "nodes")
    (v "nextId") (v "root") (v "serviceState")
  right := halted
    (a "dcm:outcome-fault" [a "dcm:fault-malformed-record"])
    (v "nodes")
}

def transitions : List RewriteRule :=
  malformedRecordTransition :: liftedTransitions

def retainedSourceTerm (rule : GrammarRule) : Bool :=
  rule.label != "dcm:instructions-nil" &&
    rule.label != "dcm:instructions-cons" &&
    rule.label != "dcm:run" &&
    rule.label != "dcm:halted"

def terms : List GrammarRule :=
  DerivationCheckMachineLanguageDef.terms.filter retainedSourceTerm ++ [
    /- The compact target owns finite-arena references for every semantic
    payload carried by an instruction or service decision.  The referenced
    values remain in separately validated source/calculus components; these
    constructors are the relocation layer consumed by the word machine. -/
    ctor "dwm:formula-ref" "Formula" [("index", "Index")],
    ctor "dwm:rule-ref" "Rule" [("index", "Index")],
    ctor "dwm:evidence-ref" "Evidence" [("index", "Index")],
    ctor "dwm:provenance-ref" "Provenance" [("index", "Index")],
    ctor "dwm:obligation-ref" "Obligation" [("index", "Index")],
    ctor "dwm:service-state-ref" "ServiceState" [("index", "Index")],
    ctor "dwm:word" "Word" [("value", "Integer")],
    ctor "dwm:words-nil" "Words" [],
    ctor "dwm:words-cons" "Words" [("word", "Word"), ("rest", "Words")],
    ctor "dwm:records-nil" "Records" [],
    ctor "dwm:records-cons" "Records"
      [("record", "Words"), ("rest", "Records")],
    ctor "dwm:decoded" "DecodeDecision" [("instruction", "Instruction")],
    ctor "dwm:decode-rejected" "DecodeDecision" [],
    ctor "dwm:run" "Config" [
      ("records", "Records"), ("nodes", "Nodes"),
      ("nextId", "Index"), ("root", "RootState"),
      ("serviceState", "ServiceState")] (some .rewrite),
    ctor "dwm:halted" "Config" [("outcome", "Outcome"), ("nodes", "Nodes")]
  ]

def retainedSourceType (declaration : TypeDecl) : Bool :=
  declaration.name != "Instructions"

/-- The compact target is generated from the source signature and transition
table.  The instruction-list carrier and the two source control terms are
replaced; semantic payloads are represented by explicit finite-arena
references while all authored machine transitions remain shared. -/
def language : LanguageDef := {
  name := "DerivationWordMachine"
  types :=
    DerivationCheckMachineLanguageDef.language.types.filter retainedSourceType ++
      [TypeDecl.plain "Word", TypeDecl.plain "Words",
       TypeDecl.plain "Records", TypeDecl.plain "DecodeDecision"]
  terms := terms
  equations := []
  rewrites := transitions
}

theorem lifted_transition_count : liftedTransitions.length = 20 := by decide

theorem transition_count : transitions.length = 21 := by decide

theorem every_source_transition_is_lifted (rewrite : RewriteRule)
    (membership : rewrite ∈ DerivationCheckMachineLanguageDef.transitions) :
    liftRewrite rewrite ∈ liftedTransitions := by
  exact List.mem_map.mpr ⟨rewrite, membership, rfl⟩

theorem decode_premise_is_load_bearing :
    (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition).premises.head? =
      some (query "DWMDecodeRecord" [v "record", decoded
        (a "dcm:input" [v "id", v "formula", v "provenance", v "relevance"])]) := by
  rfl

/-! ## Compositional canonical-wire support -/

private theorem liftTypeExpr_supported (type : TypeExpr) :
    CanonicalWire.typeExprSupported (liftTypeExpr type) =
      CanonicalWire.typeExprSupported type := by
  cases type with
  | base name =>
      by_cases instructions : name = "Instructions"
      · subst name
        rfl
      · simp [liftTypeExpr, CanonicalWire.typeExprSupported]
  | arrow => rfl
  | multiBinder => rfl
  | collection => rfl

private theorem patternListSupported_map_of_pointwise
    (transform : Pattern → Pattern) (patterns : List Pattern)
    (preserves : ∀ pattern ∈ patterns,
      CanonicalWire.patternSupported (transform pattern) =
        CanonicalWire.patternSupported pattern) :
    CanonicalWire.patternListSupported (patterns.map transform) =
      CanonicalWire.patternListSupported patterns := by
  induction patterns with
  | nil => simp [CanonicalWire.patternListSupported]
  | cons pattern patterns inductionHypothesis =>
      simp only [List.map_cons, CanonicalWire.patternListSupported]
      rw [preserves pattern (by simp)]
      rw [inductionHypothesis]
      intro tail member
      exact preserves tail (by simp [member])

private theorem liftPattern_supported (pattern : Pattern) :
    CanonicalWire.patternSupported (liftPattern pattern) =
      CanonicalWire.patternSupported pattern := by
  fun_induction liftPattern <;>
    simp_all [CanonicalWire.patternSupported,
      patternListSupported_map_of_pointwise]

private theorem liftPremise_supported (premise : Premise) :
    CanonicalWire.premiseSupported (liftPremise premise) =
      CanonicalWire.premiseSupported premise := by
  cases premise with
  | freshness => rfl
  | congruence => rfl
  | relationQuery relation arguments =>
      simp only [liftPremise, CanonicalWire.premiseSupported]
      apply patternListSupported_map_of_pointwise
      intro pattern _
      exact liftPattern_supported pattern
  | forAll => rfl

private theorem liftContext_supported (context : List (String × TypeExpr)) :
    (liftContext context).all CanonicalWire.typeBindingSupported =
      context.all CanonicalWire.typeBindingSupported := by
  induction context with
  | nil => rfl
  | cons binding context inductionHypothesis =>
      rcases binding with ⟨name, type⟩
      simp only [liftContext, List.map_cons, List.all_cons,
        CanonicalWire.typeBindingSupported]
      change (CanonicalWire.typeExprSupported (liftTypeExpr type) &&
          (liftContext context).all CanonicalWire.typeBindingSupported) = _
      rw [liftTypeExpr_supported, inductionHypothesis]

private theorem liftPremises_supported (premises : List Premise) :
    (premises.map liftPremise).all CanonicalWire.premiseSupported =
      premises.all CanonicalWire.premiseSupported := by
  induction premises with
  | nil => rfl
  | cons premise premises inductionHypothesis =>
      simp [liftPremise_supported, inductionHypothesis]

private theorem liftLeft_supported (left : Pattern)
    (supported : CanonicalWire.patternSupported left) :
    CanonicalWire.patternSupported (liftLeft left) := by
  cases left with
  | bvar index => simp [CanonicalWire.patternSupported] at supported
  | fvar name => simp [liftLeft, liftPattern, CanonicalWire.patternSupported]
  | lambda name body => simp [CanonicalWire.patternSupported] at supported
  | multiLambda count names body =>
      simp [CanonicalWire.patternSupported] at supported
  | subst body replacement =>
      simp [CanonicalWire.patternSupported] at supported
  | collection kind elements rest =>
      simp [CanonicalWire.patternSupported] at supported
  | apply label arguments =>
      simp only [liftLeft]
      split
      · rename_i nodes nextId root serviceState patternEquality
        cases patternEquality
        simp [run, recordsNil, a, CanonicalWire.patternSupported,
          CanonicalWire.patternListSupported, liftPattern_supported]
          at supported ⊢
        aesop
      · rename_i instruction next rest nodes nextId root serviceState
          patternEquality
        cases patternEquality
        simp [run, recordsCons, a, v, CanonicalWire.patternSupported,
          CanonicalWire.patternListSupported, liftPattern_supported]
          at supported ⊢
        aesop
      · rename_i instruction nodes nextId root serviceState patternEquality
        cases patternEquality
        simp [run, recordsCons, recordsNil, a, v,
          CanonicalWire.patternSupported,
          CanonicalWire.patternListSupported, liftPattern_supported]
          at supported ⊢
        aesop
      · rename_i instruction rest nodes nextId root serviceState
          notCons notNil patternEquality
        cases patternEquality
        simp [run, recordsCons, a, v, CanonicalWire.patternSupported,
          CanonicalWire.patternListSupported, liftPattern_supported]
          at supported ⊢
        aesop
      · rw [liftPattern_supported]
        exact supported

private theorem sourceInstruction?_supported
    {left instruction : Pattern}
    (decodedInstruction : sourceInstruction? left = some instruction)
    (leftSupported : CanonicalWire.patternSupported left) :
    CanonicalWire.patternSupported instruction := by
  cases left with
  | bvar => simp [sourceInstruction?] at decodedInstruction
  | fvar => simp [sourceInstruction?] at decodedInstruction
  | lambda => simp [sourceInstruction?] at decodedInstruction
  | multiLambda => simp [sourceInstruction?] at decodedInstruction
  | subst => simp [sourceInstruction?] at decodedInstruction
  | collection => simp [sourceInstruction?] at decodedInstruction
  | apply label arguments =>
      simp only [sourceInstruction?] at decodedInstruction
      split at decodedInstruction
      · rename_i instructionPattern rest patternEquality
        cases patternEquality
        cases decodedInstruction
        simp [CanonicalWire.patternSupported,
          CanonicalWire.patternListSupported] at leftSupported
        exact leftSupported.1.1
      · contradiction

/-- The word-machine transformation preserves canonical-wire support for
every source transition, not merely for the current finite transition table. -/
theorem liftRewrite_supported (rewrite : RewriteRule)
    (supported : CanonicalWire.rewriteSupported rewrite) :
    CanonicalWire.rewriteSupported (liftRewrite rewrite) := by
  simp only [CanonicalWire.rewriteSupported, Bool.and_eq_true] at supported
  have liftedContext :
      (liftContext rewrite.typeContext).all
        CanonicalWire.typeBindingSupported := by
    rw [liftContext_supported]
    exact supported.1.1.1
  have liftedPremises :
      (rewrite.premises.map liftPremise).all
        CanonicalWire.premiseSupported := by
    rw [liftPremises_supported]
    exact supported.1.1.2
  have liftedLeft :
      CanonicalWire.patternSupported (liftLeft rewrite.left) := by
    exact liftLeft_supported rewrite.left supported.1.2
  have liftedRight :
      CanonicalWire.patternSupported (liftPattern rewrite.right) := by
    rw [liftPattern_supported]
    exact supported.2
  have leftSupported : CanonicalWire.patternSupported rewrite.left := by
    exact supported.1.2
  cases instruction : sourceInstruction? rewrite.left with
  | none =>
      by_cases trailing : rewrite.name = "dcm:finish-trailing"
      · simp [liftRewrite, instruction, trailing,
          CanonicalWire.rewriteSupported,
          CanonicalWire.typeBindingSupported,
          CanonicalWire.typeExprSupported, liftedContext,
          liftedPremises, liftedLeft, liftedRight]
      · simp [liftRewrite, instruction, trailing,
          CanonicalWire.rewriteSupported, liftedContext,
          liftedPremises, liftedLeft, liftedRight]
  | some instructionPattern =>
      have instructionSupported :=
        sourceInstruction?_supported instruction leftSupported
      by_cases trailing : rewrite.name = "dcm:finish-trailing"
      · simp [liftRewrite, instruction, trailing,
          CanonicalWire.rewriteSupported, CanonicalWire.typeBindingSupported,
          CanonicalWire.typeExprSupported, CanonicalWire.premiseSupported,
          CanonicalWire.patternListSupported, CanonicalWire.patternSupported,
          decoded, a, v, query, instructionSupported, liftedContext,
          liftedPremises, liftedLeft, liftedRight]
      · simp [liftRewrite, instruction, trailing,
          CanonicalWire.rewriteSupported, CanonicalWire.typeBindingSupported,
          CanonicalWire.typeExprSupported, CanonicalWire.premiseSupported,
          CanonicalWire.patternListSupported, CanonicalWire.patternSupported,
          decoded, a, v, query, instructionSupported, liftedContext,
          liftedPremises, liftedLeft, liftedRight]

private theorem source_language_supported :
    CanonicalWire.languageSupported
      DerivationCheckMachineLanguageDef.language := by
  rw [← CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact DerivationCheckMachineLanguageDef.wire_isSome

private theorem terms_supported :
    terms.all CanonicalWire.grammarRuleSupported := by
  have sourceSupported := source_language_supported
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true] at sourceSupported
  have sourceTerms :
      DerivationCheckMachineLanguageDef.terms.all
        CanonicalWire.grammarRuleSupported := by
    exact sourceSupported.1.2
  have retainedTerms :
      (DerivationCheckMachineLanguageDef.terms.filter retainedSourceTerm).all
        CanonicalWire.grammarRuleSupported := by
    apply List.all_eq_true.mpr
    intro rule membership
    exact List.all_eq_true.mp sourceTerms rule
      (List.mem_of_mem_filter membership)
  simp only [terms, List.all_append, Bool.and_eq_true]
  refine ⟨retainedTerms, ?_⟩
  simp [ctor, CanonicalWire.grammarRuleSupported,
    CanonicalWire.termParamSupported, CanonicalWire.typeExprSupported,
    CanonicalWire.syntaxItemSupported]

private theorem transitions_supported :
    transitions.all CanonicalWire.rewriteSupported := by
  have sourceSupported := source_language_supported
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true] at sourceSupported
  have sourceRewrites :
      DerivationCheckMachineLanguageDef.transitions.all
        CanonicalWire.rewriteSupported := by
    exact sourceSupported.2
  apply List.all_eq_true.mpr
  intro rewrite membership
  simp only [transitions, List.mem_cons] at membership
  rcases membership with rfl | membership
  · simp [malformedRecordTransition, query, v, a, run, halted,
      recordsCons, decodeRejected, CanonicalWire.rewriteSupported,
      CanonicalWire.typeBindingSupported, CanonicalWire.typeExprSupported,
      CanonicalWire.premiseSupported, CanonicalWire.patternSupported,
      CanonicalWire.patternListSupported]
  · rcases List.mem_map.mp membership with ⟨source, sourceMembership, rfl⟩
    exact liftRewrite_supported source
      (List.all_eq_true.mp sourceRewrites source sourceMembership)

/-- The generated compact target lies in the canonical wire fragment because
the transformation preserves support and every newly introduced row is
supported. -/
theorem language_supported : CanonicalWire.languageSupported language := by
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true]
  exact ⟨⟨rfl, terms_supported⟩, transitions_supported⟩

/-- Canonical wire generation succeeds by compositional preservation, not by
whole-language evaluation. -/
theorem wire_isSome : (CanonicalWire.renderLanguage? language).isSome := by
  rw [CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact language_supported

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 100000 in
private theorem rewrites_validate :
    ∀ rewrite ∈ language.rewrites,
      LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite membership
  change rewrite ∈ transitions at membership
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := { maxSteps := 4000000 })
      [LanguageDef.validateRewrite, language, terms, retainedSourceTerm,
      retainedSourceType, malformedRecordTransition, liftRewrite,
      sourceInstruction?, liftContext, liftTypeExpr, liftPremise, liftPattern,
      liftLeft, a, v, query, run, halted, recordsNil, recordsCons, decoded,
      decodeRejected,
      DerivationCheckMachineLanguageDef.ctor,
      DerivationCheckMachineLanguageDef.typed,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.query,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.halted,
      DerivationCheckMachineLanguageDef.instructionsNil,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.nodesCons,
      DerivationCheckMachineLanguageDef.node,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.rootSome,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.decisionState,
      DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.commonContext,
      DerivationCheckMachineLanguageDef.missingFinishTransition,
      DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
      DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
      DerivationCheckMachineLanguageDef.inputAcceptTransition,
      DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
      DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.inferParentFaultTransition,
      DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
      DerivationCheckMachineLanguageDef.inferAcceptTransition,
      DerivationCheckMachineLanguageDef.dropFaultTransition,
      DerivationCheckMachineLanguageDef.dropAcceptTransition,
      DerivationCheckMachineLanguageDef.duplicateRootTransition,
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.rootAcceptTransition,
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition,
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition,
      DerivationCheckMachineLanguageDef.language,
      DerivationCheckMachineLanguageDef.terms,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
      LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain,
      TypeExpr.baseNames]

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 100000 in
theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals first
  | exact rewrites_validate
  | (simp (config := { maxSteps := 4000000 })
      [language, terms, retainedSourceTerm, retainedSourceType,
      DerivationCheckMachineLanguageDef.language,
      DerivationCheckMachineLanguageDef.terms,
      DerivationCheckMachineLanguageDef.ctor,
      DerivationCheckMachineLanguageDef.transitions,
      DerivationCheckMachineLanguageDef.typed,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.query,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.halted,
      DerivationCheckMachineLanguageDef.instructionsNil,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.nodesCons,
      DerivationCheckMachineLanguageDef.node,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.rootSome,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.decisionState,
      DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.commonContext,
      DerivationCheckMachineLanguageDef.missingFinishTransition,
      DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
      DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
      DerivationCheckMachineLanguageDef.inputAcceptTransition,
      DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
      DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.inferParentFaultTransition,
      DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
      DerivationCheckMachineLanguageDef.inferAcceptTransition,
      DerivationCheckMachineLanguageDef.dropFaultTransition,
      DerivationCheckMachineLanguageDef.dropAcceptTransition,
      DerivationCheckMachineLanguageDef.duplicateRootTransition,
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.rootAcceptTransition,
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition,
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition,
      transitions, liftedTransitions, liftRewrite, sourceInstruction?,
      liftContext, liftTypeExpr, liftPremise, liftPattern, liftLeft,
      malformedRecordTransition, a, v, query, run, halted, recordsNil,
      recordsCons, decoded, decodeRejected,
      LanguageDef.concreteSyntaxRowsValid,
      LanguageDef.concreteSyntaxItemAllowed, LanguageDef.typeNames,
      TermParam.typeExpr, TypeExpr.baseNames, TypeDecl.plain])

def validated : ValidatedLanguageDef where
  language := language
  valid := language_validate

def indexZero : Pattern := a "dcm:index" [a (toString (0 : Nat))]

def nodesNil : Pattern := a "dcm:nodes-nil"

def rootNone : Pattern := a "dcm:root-none"

def serviceStateInitial : Pattern := a "dcm:service-state-initial"

def missingFinishStart : Pattern :=
  run recordsNil nodesNil indexZero rootNone serviceStateInitial

def missingFinishDone : Pattern :=
  halted (a "dcm:outcome-fault" [a "dcm:fault-missing-finish"]) nodesNil

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
theorem missingFinishStart_has_type :
    CarrierWellSorted.checkHasType language
      WellSorted.FreeTypeContext.empty [] missingFinishStart
      (.base "Config") = true := by
  apply (CarrierWellSorted.checkHasType_eq_true_iff ?_).2
  · have recordsTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          recordsNil (.base "Records") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dwm:records-nil" "Records" [])
      · simp [language, terms, retainedSourceTerm,
          DerivationCheckMachineLanguageDef.terms]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .nil
    have nodesTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          nodesNil (.base "Nodes") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dcm:nodes-nil" "Nodes" [])
      · simp [language, terms, retainedSourceTerm,
          DerivationCheckMachineLanguageDef.terms,
          DerivationCheckMachineLanguageDef.ctor]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .nil
    have integerTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          (a (toString (0 : Nat))) (.base "Integer") := by
      apply CarrierWellSorted.HasType.builtinAtom
      let declaration : TypeDecl :=
        { name := "Integer", carrier := .builtinInt }
      refine ⟨declaration, ?_, rfl, ?_⟩
      · change List.Mem declaration (declaration :: _)
        exact .head _
      · simp [declaration, CarrierWellSorted.carrierAcceptsAtom,
          Nat.toInt?_repr]
    have indexTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          indexZero (.base "Index") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dcm:index" "Index" [("value", "Integer")])
      · simp [language, terms, retainedSourceTerm,
          DerivationCheckMachineLanguageDef.terms,
          DerivationCheckMachineLanguageDef.ctor]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .cons trivial rfl integerTyped .nil
    have rootTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          rootNone (.base "RootState") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dcm:root-none" "RootState" [])
      · simp [language, terms, retainedSourceTerm,
          DerivationCheckMachineLanguageDef.terms,
          DerivationCheckMachineLanguageDef.ctor]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .nil
    have serviceStateTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          serviceStateInitial (.base "ServiceState") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dcm:service-state-initial" "ServiceState" [])
      · simp [language, terms, retainedSourceTerm,
          DerivationCheckMachineLanguageDef.terms,
          DerivationCheckMachineLanguageDef.ctor]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .nil
    apply CarrierWellSorted.HasType.constructor
      (rule := ctor "dwm:run" "Config" [
        ("records", "Records"), ("nodes", "Nodes"),
        ("nextId", "Index"), ("root", "RootState"),
        ("serviceState", "ServiceState")] (some .rewrite))
    · simp [language, terms]
    · simp [WellSorted.UsesBareCollection, ctor]
    · exact .cons trivial rfl recordsTyped
        (.cons trivial rfl nodesTyped
          (.cons trivial rfl indexTyped
            (.cons trivial rfl rootTyped
              (.cons trivial rfl serviceStateTyped .nil))))
  · rfl

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/- The premise-free missing-finish transition remains operational after the
compact representation change.  This computation is proved in the defining
module so that the private mechanical-lifting helpers are transparent to the
kernel reduction. -/
set_option maxHeartbeats 30000000 in
set_option maxRecDepth 100000 in
theorem missingFinishStep_exact :
    rewriteAt (engineBasePremises RelationEnv.empty) language 1
      missingFinishStart = [missingFinishDone] := by
  simp (config := { maxSteps := 2000000 })
    [rewriteAt, applyRuleUsing, premisesUsing, premiseStepUsing,
    engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, RelationEnv.empty,
    language, transitions, liftedTransitions,
    malformedRecordTransition, liftRewrite,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRuleUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    sourceInstruction?, liftLeft, liftPattern, liftContext, liftPremise,
    query, v, a, run, halted, recordsNil, recordsCons, decoded,
    DerivationCheckMachineLanguageDef.typed,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.query,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.nodesCons,
    DerivationCheckMachineLanguageDef.node,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.commonContext,
    DerivationCheckMachineLanguageDef.transitions,
    DerivationCheckMachineLanguageDef.missingFinishTransition,
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
    DerivationCheckMachineLanguageDef.inputAcceptTransition,
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.inferParentFaultTransition,
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
    DerivationCheckMachineLanguageDef.inferAcceptTransition,
    DerivationCheckMachineLanguageDef.dropFaultTransition,
    DerivationCheckMachineLanguageDef.dropAcceptTransition,
    DerivationCheckMachineLanguageDef.duplicateRootTransition,
    DerivationCheckMachineLanguageDef.rootFaultTransition,
    DerivationCheckMachineLanguageDef.rootAcceptTransition,
    DerivationCheckMachineLanguageDef.finishTrailingTransition,
    DerivationCheckMachineLanguageDef.finishMissingRootTransition,
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.finishRootFaultTransition,
    DerivationCheckMachineLanguageDef.finishVerifiedTransition]
  simp [missingFinishStart, missingFinishDone, indexZero, nodesNil,
    rootNone, serviceStateInitial, a, run, halted, recordsNil,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
    Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
    Mettapedia.OSLF.MeTTaIL.Match.mergeBindings,
    Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

/- A compact halted configuration has no outgoing target transition. -/
set_option maxHeartbeats 30000000 in
set_option maxRecDepth 100000 in
theorem missingFinishDone_irreducible :
    rewriteAt (engineBasePremises RelationEnv.empty) language 1
      missingFinishDone = [] := by
  simp (config := { maxSteps := 2000000 })
    [rewriteAt, applyRuleUsing, premisesUsing, premiseStepUsing,
    engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, RelationEnv.empty,
    language, transitions, liftedTransitions,
    malformedRecordTransition, liftRewrite,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRuleUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing,
    sourceInstruction?, liftLeft, liftPattern, liftContext, liftPremise,
    query, v, a, run, halted, recordsNil, recordsCons, decoded,
    DerivationCheckMachineLanguageDef.typed,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.query,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.nodesCons,
    DerivationCheckMachineLanguageDef.node,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.commonContext,
    DerivationCheckMachineLanguageDef.transitions,
    DerivationCheckMachineLanguageDef.missingFinishTransition,
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
    DerivationCheckMachineLanguageDef.inputAcceptTransition,
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.inferParentFaultTransition,
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
    DerivationCheckMachineLanguageDef.inferAcceptTransition,
    DerivationCheckMachineLanguageDef.dropFaultTransition,
    DerivationCheckMachineLanguageDef.dropAcceptTransition,
    DerivationCheckMachineLanguageDef.duplicateRootTransition,
    DerivationCheckMachineLanguageDef.rootFaultTransition,
    DerivationCheckMachineLanguageDef.rootAcceptTransition,
    DerivationCheckMachineLanguageDef.finishTrailingTransition,
    DerivationCheckMachineLanguageDef.finishMissingRootTransition,
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.finishRootFaultTransition,
    DerivationCheckMachineLanguageDef.finishVerifiedTransition]
  simp [missingFinishDone, nodesNil, a, halted,
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern]

#print axioms lifted_transition_count
#print axioms transition_count
#print axioms every_source_transition_is_lifted
#print axioms decode_premise_is_load_bearing
#print axioms liftRewrite_supported
#print axioms language_supported
#print axioms wire_isSome
#print axioms language_validate
#print axioms missingFinishStart_has_type
#print axioms missingFinishStep_exact
#print axioms missingFinishDone_irreducible

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
