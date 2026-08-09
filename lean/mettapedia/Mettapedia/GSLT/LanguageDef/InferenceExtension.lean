import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.GSLT.Core.Composition
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Proof calculi as a coGSLT-authored language-definition extension

Judgment declarations, inference-rule schemas, and an optional rooted
conversion interface are not fields of the term language.  They form an
authored proof-presentation layer over it.

This module gives that layer its own GSLT.  The calculus syntax includes one
piece of genuine sugar, `axiom`, whose GSLT rewrite expands it to an ordinary
zero-premise rule.  Elaboration is total on well-shaped syntax declarations,
rejects conflicting conversion roots, is invariant under the sugar rewrite,
and has canonical quotation as a section.

The layer is intentionally independent of any checker, compiler, or runtime.
Those are staged realizations of the elaborated `ProofCalculus`, not
components of either language definition.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceExtension

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The proof-presentation payload attached to a term language. -/
structure ProofCalculus where
  judgments : List JudgmentDecl := []
  rules : List RuleSchema := []
  conversion : Option ConversionDecl := none
deriving Repr, DecidableEq

namespace ProofCalculus

/-- Empty proof presentation. -/
def empty : ProofCalculus := {}

/-- Append independent declarations, failing when both sides claim a rooted
conversion interface.  The conflict is data-authority ambiguity, not a
compiler preference. -/
def append? (first second : ProofCalculus) : Option ProofCalculus :=
  match first.conversion, second.conversion with
  | some _, some _ => none
  | firstConversion, secondConversion =>
      some
        { judgments := first.judgments ++ second.judgments
          rules := first.rules ++ second.rules
          conversion := secondConversion <|> firstConversion }

@[simp] theorem empty_append (extension : ProofCalculus) :
    empty.append? extension = some extension := by
  cases extension with
  | mk judgments rules conversion =>
      cases conversion <;> simp [empty, append?]

@[simp] theorem append_empty (extension : ProofCalculus) :
    extension.append? empty = some extension := by
  cases extension with
  | mk judgments rules conversion =>
      cases conversion <;> simp [empty, append?]

/-- Appending is associative whenever both staged append operations succeed.
The statement retains the intermediate successes so conversion-root conflicts
cannot be hidden by reassociation. -/
theorem append_assoc_of_success
    {first second third firstSecond secondThird : ProofCalculus}
    (leftSuccess : first.append? second = some firstSecond)
    (rightSuccess : second.append? third = some secondThird) :
    firstSecond.append? third = first.append? secondThird := by
  cases first with
  | mk firstJudgments firstRules firstConversion =>
    cases second with
    | mk secondJudgments secondRules secondConversion =>
      cases third with
      | mk thirdJudgments thirdRules thirdConversion =>
        cases firstConversion <;> cases secondConversion <;>
          cases thirdConversion <;>
          simp [append?] at leftSuccess rightSuccess ⊢
        all_goals
          subst firstSecond
          subst secondThird
          simp [List.append_assoc]

/-- Appending proof-calculus declarations is associative as a partial
operation: both bracketings fail together when more than one rooted conversion
authority is present, and otherwise produce the same declaration lists. -/
theorem append_assoc (first second third : ProofCalculus) :
    (first.append? second).bind (fun merged => merged.append? third) =
      (second.append? third).bind (fun merged => first.append? merged) := by
  cases first with
  | mk firstJudgments firstRules firstConversion =>
    cases second with
    | mk secondJudgments secondRules secondConversion =>
      cases third with
      | mk thirdJudgments thirdRules thirdConversion =>
        cases firstConversion <;> cases secondConversion <;>
          cases thirdConversion <;>
          simp [append?, List.append_assoc]

end ProofCalculus

/-! ## The authored meta-language -/

/-- Structural syntax for locally nameless patterns in the proof-extension
meta-language.  This is deliberately not a wrapper around `Pattern`: binder
indices, constructor arguments, and collection rests are visible authored
syntax. -/
inductive PatternSyntax where
  | bvar (index : Nat)
  | fvar (name : String)
  | apply (constructor : String) (arguments : List PatternSyntax)
  | lambda (binder : Option String) (body : PatternSyntax)
  | multiLambda (arity : Nat) (binders : List String) (body : PatternSyntax)
  | subst (body replacement : PatternSyntax)
  | collection (collectionType : CollType) (elements : List PatternSyntax)
      (rest : Option String)
deriving Repr

mutual

/-- Quote a checker pattern into structural extension syntax. -/
def encodePattern : Pattern → PatternSyntax
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply constructor arguments =>
      .apply constructor (encodePatternList arguments)
  | .lambda binder body => .lambda binder (encodePattern body)
  | .multiLambda arity binders body =>
      .multiLambda arity binders (encodePattern body)
  | .subst body replacement =>
      .subst (encodePattern body) (encodePattern replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (encodePatternList elements) rest
termination_by pattern => sizeOf pattern

def encodePatternList : List Pattern → List PatternSyntax
  | [] => []
  | pattern :: patterns => encodePattern pattern :: encodePatternList patterns
termination_by patterns => sizeOf patterns

end

mutual

/-- Interpret structural extension syntax as a checker pattern. -/
def decodePattern : PatternSyntax → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply constructor arguments =>
      .apply constructor (decodePatternList arguments)
  | .lambda binder body => .lambda binder (decodePattern body)
  | .multiLambda arity binders body =>
      .multiLambda arity binders (decodePattern body)
  | .subst body replacement =>
      .subst (decodePattern body) (decodePattern replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (decodePatternList elements) rest
termination_by pattern => sizeOf pattern

def decodePatternList : List PatternSyntax → List Pattern
  | [] => []
  | pattern :: patterns => decodePattern pattern :: decodePatternList patterns
termination_by patterns => sizeOf patterns

end


mutual

@[simp] theorem decodePattern_encodePattern (pattern : Pattern) :
    decodePattern (encodePattern pattern) = pattern := by
  cases pattern with
  | bvar index => simp [encodePattern, decodePattern]
  | fvar name => simp [encodePattern, decodePattern]
  | apply constructor arguments =>
      simp [encodePattern, decodePattern,
        decodePatternList_encodePatternList arguments]
  | lambda binder body =>
      simp [encodePattern, decodePattern, decodePattern_encodePattern body]
  | multiLambda arity binders body =>
      simp [encodePattern, decodePattern, decodePattern_encodePattern body]
  | subst body replacement =>
      simp [encodePattern, decodePattern, decodePattern_encodePattern body,
        decodePattern_encodePattern replacement]
  | collection collectionType elements rest =>
      simp [encodePattern, decodePattern,
        decodePatternList_encodePatternList elements]
termination_by sizeOf pattern

@[simp] theorem decodePatternList_encodePatternList (patterns : List Pattern) :
    decodePatternList (encodePatternList patterns) = patterns := by
  cases patterns with
  | nil => simp [encodePatternList, decodePatternList]
  | cons pattern patterns =>
      simp [encodePatternList, decodePatternList,
        decodePattern_encodePattern pattern,
        decodePatternList_encodePatternList patterns]
termination_by sizeOf patterns

end


mutual

@[simp] theorem encodePattern_decodePattern (pattern : PatternSyntax) :
    encodePattern (decodePattern pattern) = pattern := by
  cases pattern with
  | bvar index => simp [encodePattern, decodePattern]
  | fvar name => simp [encodePattern, decodePattern]
  | apply constructor arguments =>
      simp [encodePattern, decodePattern,
        encodePatternList_decodePatternList arguments]
  | lambda binder body =>
      simp [encodePattern, decodePattern, encodePattern_decodePattern body]
  | multiLambda arity binders body =>
      simp [encodePattern, decodePattern, encodePattern_decodePattern body]
  | subst body replacement =>
      simp [encodePattern, decodePattern, encodePattern_decodePattern body,
        encodePattern_decodePattern replacement]
  | collection collectionType elements rest =>
      simp [encodePattern, decodePattern,
        encodePatternList_decodePatternList elements]
termination_by sizeOf pattern

@[simp] theorem encodePatternList_decodePatternList
    (patterns : List PatternSyntax) :
    encodePatternList (decodePatternList patterns) = patterns := by
  cases patterns with
  | nil => simp [encodePatternList, decodePatternList]
  | cons pattern patterns =>
      simp [encodePatternList, decodePatternList,
        encodePattern_decodePattern pattern,
        encodePatternList_decodePatternList patterns]
termination_by sizeOf patterns

end


/-- Structural syntax for generic rule-side conditions. -/
inductive RuleSideConditionSyntax where
  | explicitSubstitution
      (ambientDepth bodyArgument replacementArgument resultArgument : Nat)
  | unusedBinderElimination
      (ambientDepth bodyArgument resultArgument : Nat)
deriving Repr, DecidableEq

def encodeRuleSideCondition : RuleSideCondition → RuleSideConditionSyntax
  | .explicitSubstitution ambientDepth bodyArgument replacementArgument resultArgument =>
      .explicitSubstitution ambientDepth bodyArgument replacementArgument resultArgument
  | .unusedBinderElimination ambientDepth bodyArgument resultArgument =>
      .unusedBinderElimination ambientDepth bodyArgument resultArgument

def decodeRuleSideCondition : RuleSideConditionSyntax → RuleSideCondition
  | .explicitSubstitution ambientDepth bodyArgument replacementArgument resultArgument =>
      .explicitSubstitution ambientDepth bodyArgument replacementArgument resultArgument
  | .unusedBinderElimination ambientDepth bodyArgument resultArgument =>
      .unusedBinderElimination ambientDepth bodyArgument resultArgument

@[simp] theorem decodeRuleSideCondition_encodeRuleSideCondition
    (condition : RuleSideCondition) :
    decodeRuleSideCondition (encodeRuleSideCondition condition) = condition := by
  cases condition <;> rfl

@[simp] theorem encodeRuleSideCondition_decodeRuleSideCondition
    (condition : RuleSideConditionSyntax) :
    encodeRuleSideCondition (decodeRuleSideCondition condition) = condition := by
  cases condition <;> rfl

/-- Structural syntax for a rule schema.  Metavariable occurrence depths remain
explicit data, so elaboration cannot accidentally identify same-named binders
at different depths. -/
structure RuleSchemaSyntax where
  id : String
  metavariables : List (String × Nat)
  premises : List PatternSyntax
  conclusion : PatternSyntax
  sideConditions : List RuleSideConditionSyntax := []
deriving Repr

def encodeRuleSchema (schema : RuleSchema) : RuleSchemaSyntax :=
  { id := schema.id.value
    metavariables := schema.metavariables
    premises := schema.premises.map encodePattern
    conclusion := encodePattern schema.conclusion
    sideConditions := schema.sideConditions.map encodeRuleSideCondition }

def decodeRuleSchema (code : RuleSchemaSyntax) : RuleSchema :=
  { id := ⟨code.id⟩
    metavariables := code.metavariables
    premises := code.premises.map decodePattern
    conclusion := decodePattern code.conclusion
    sideConditions := code.sideConditions.map decodeRuleSideCondition }

@[simp] theorem decodeRuleSchema_encodeRuleSchema (schema : RuleSchema) :
    decodeRuleSchema (encodeRuleSchema schema) = schema := by
  cases schema
  simp [encodeRuleSchema, decodeRuleSchema, Function.comp_def]

@[simp] theorem encodeRuleSchema_decodeRuleSchema (code : RuleSchemaSyntax) :
    encodeRuleSchema (decodeRuleSchema code) = code := by
  cases code
  simp [encodeRuleSchema, decodeRuleSchema, Function.comp_def]

/-- Structural syntax for declarations. -/
structure JudgmentSyntax where
  head : String
  arity : Nat
deriving Repr, DecidableEq

structure ConversionSyntax where
  judgmentHead : String
  version : String
deriving Repr, DecidableEq

def encodeJudgment (declaration : JudgmentDecl) : JudgmentSyntax :=
  ⟨declaration.head, declaration.arity⟩

def decodeJudgment (code : JudgmentSyntax) : JudgmentDecl :=
  ⟨code.head, code.arity⟩

def encodeConversion (declaration : ConversionDecl) : ConversionSyntax :=
  ⟨declaration.judgmentHead, declaration.version⟩

def decodeConversion (code : ConversionSyntax) : ConversionDecl :=
  ⟨code.judgmentHead, code.version⟩

@[simp] theorem decodeJudgment_encodeJudgment (declaration : JudgmentDecl) :
    decodeJudgment (encodeJudgment declaration) = declaration := by
  cases declaration
  rfl

@[simp] theorem encodeJudgment_decodeJudgment (code : JudgmentSyntax) :
    encodeJudgment (decodeJudgment code) = code := by
  cases code
  rfl

@[simp] theorem decodeConversion_encodeConversion (declaration : ConversionDecl) :
    decodeConversion (encodeConversion declaration) = declaration := by
  cases declaration
  rfl

@[simp] theorem encodeConversion_decodeConversion (code : ConversionSyntax) :
    encodeConversion (decodeConversion code) = code := by
  cases code
  rfl

/-- Canonical declarations of the proof-presentation language. -/
inductive CanonicalDeclaration where
  | judgment (declaration : JudgmentSyntax)
  | rule (schema : RuleSchemaSyntax)
  | conversion (declaration : ConversionSyntax)
deriving Repr

/-- Atomic syntax of the proof-presentation language.  `axiom` is syntax sugar
for an ordinary rule with no metavariables, premises, or side conditions. -/
inductive CalculusDeclarationSyntax where
  | canonical (declaration : CanonicalDeclaration)
  | axiom (id : String) (conclusion : PatternSyntax)
deriving Repr

/-- The one primitive rewrite of the atomic calculus-syntax GSLT. -/
inductive CalculusDeclarationStep :
    CalculusDeclarationSyntax → CalculusDeclarationSyntax → Prop where
  | axiom (id : String) (conclusion : PatternSyntax) :
      CalculusDeclarationStep (.axiom id conclusion)
        (.canonical (.rule
          { id
            metavariables := []
            premises := []
            conclusion
            sideConditions := [] }))

/-- Atomic proof-calculus declarations as a GSLT. -/
def calculusDeclarationGSLT : GSLT where
  Term := CalculusDeclarationSyntax
  equations :=
    { r := Eq
      iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩ }
  rewrites := CalculusDeclarationStep
  rewrites_resp_left := by
    intro source source' target sourceEq step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step targetEq
    subst target'
    exact step

/-- Authored calculus documents are the free document GSLT on atomic
declarations.  Empty document and concatenation are therefore part of `T`,
their algebraic laws live in `E`, and an atomic rewrite is available at every
declaration occurrence through `R`. -/
def calculusSyntax : GSLT.Compositional :=
  GSLT.freeDocumentCompositional calculusDeclarationGSLT

/-- The underlying `(T,E,R)` theory of authored calculus documents. -/
def calculusSyntaxGSLT : GSLT := calculusSyntax.theory

/-- A calculus document is an ordinary list term of `calculusSyntaxGSLT`. -/
abbrev CalculusSyntax := List CalculusDeclarationSyntax

/-- Elaborate one canonical declaration. -/
def elaborateCanonical : CanonicalDeclaration → ProofCalculus
  | .judgment declaration => { judgments := [decodeJudgment declaration] }
  | .rule schema => { rules := [decodeRuleSchema schema] }
  | .conversion declaration => { conversion := some (decodeConversion declaration) }

/-- Elaborate one atomic declaration. -/
def elaborateDeclaration : CalculusDeclarationSyntax → ProofCalculus
  | .canonical declaration => elaborateCanonical declaration
  | .axiom id conclusion =>
      { rules :=
          [{ id := ⟨id⟩
             metavariables := []
             premises := []
             conclusion := decodePattern conclusion
             sideConditions := [] }] }

/-- Elaborate a calculus document by folding its declarations through the
partial append operation.  Multiple rooted conversion declarations fail
closed. -/
def elaborate : CalculusSyntax → Option ProofCalculus
  | [] => some .empty
  | declaration :: declarations => do
      let tail ← elaborate declarations
      (elaborateDeclaration declaration).append? tail

/-- Canonical quotation into one flat calculus document. -/
def quote (extension : ProofCalculus) : CalculusSyntax :=
  (extension.judgments.map fun declaration =>
      CalculusDeclarationSyntax.canonical (.judgment (encodeJudgment declaration))) ++
    (extension.rules.map fun schema =>
      CalculusDeclarationSyntax.canonical (.rule (encodeRuleSchema schema))) ++
    (extension.conversion.toList.map fun declaration =>
      CalculusDeclarationSyntax.canonical (.conversion (encodeConversion declaration)))

@[simp] theorem elaborate_judgments (judgments : List JudgmentDecl)
    (tail : CalculusSyntax) :
    elaborate
        (judgments.map (fun declaration =>
          CalculusDeclarationSyntax.canonical
            (.judgment (encodeJudgment declaration))) ++ tail) =
      (elaborate tail).map fun rest =>
        { rest with judgments := judgments ++ rest.judgments } := by
  induction judgments with
  | nil => simp
  | cons judgment judgments inductionHypothesis =>
      simp only [List.map_cons, List.cons_append, elaborate]
      rw [inductionHypothesis]
      cases result : elaborate tail with
      | none => simp
      | some rest =>
          cases rest
          simp [elaborateDeclaration, elaborateCanonical, ProofCalculus.append?]

@[simp] theorem elaborate_rules (rules : List RuleSchema)
    (tail : CalculusSyntax) :
    elaborate
        (rules.map (fun schema =>
          CalculusDeclarationSyntax.canonical
            (.rule (encodeRuleSchema schema))) ++ tail) =
      (elaborate tail).map fun rest =>
        { rest with rules := rules ++ rest.rules } := by
  induction rules with
  | nil => simp
  | cons rule rules inductionHypothesis =>
      simp only [List.map_cons, List.cons_append, elaborate]
      rw [inductionHypothesis]
      cases result : elaborate tail with
      | none => simp
      | some rest =>
          cases rest
          simp [elaborateDeclaration, elaborateCanonical,
            ProofCalculus.append?]

@[simp] theorem elaborate_empty : elaborate ([] : CalculusSyntax) = some .empty :=
  rfl

@[simp] theorem elaborate_conversion (declaration : ConversionDecl) :
    elaborate
        [CalculusDeclarationSyntax.canonical
          (.conversion (encodeConversion declaration))] =
      some { conversion := some declaration } := by
  simp [elaborate, elaborateDeclaration, elaborateCanonical,
    ProofCalculus.append?, ProofCalculus.empty]

/-- Elaboration is a homomorphism from document concatenation to partial
proof-calculus append. -/
theorem elaborate_append (first second : CalculusSyntax) :
    elaborate (first ++ second) =
      (elaborate first).bind fun left =>
        (elaborate second).bind fun right => left.append? right := by
  induction first with
  | nil =>
      cases result : elaborate second with
      | none => simp [elaborate, result]
      | some extension =>
          simp [elaborate, result, ProofCalculus.empty_append]
  | cons declaration declarations inductionHypothesis =>
      simp only [List.cons_append, elaborate, inductionHypothesis]
      cases tailResult : elaborate declarations with
      | none => simp
      | some tail =>
          cases secondResult : elaborate second with
          | none => simp
          | some right =>
              exact
                (ProofCalculus.append_assoc
                  (elaborateDeclaration declaration) tail right).symm

/-- Quotation is a section of elaboration. -/
@[simp] theorem elaborate_quote (extension : ProofCalculus) :
    elaborate (quote extension) = some extension := by
  cases extension with
  | mk judgments rules conversion =>
      cases conversion with
      | none =>
          simp only [quote, Option.toList_none, List.map_nil,
            List.append_nil]
          rw [elaborate_judgments judgments]
          have rulesOnly :
              elaborate
                  (rules.map (fun schema =>
                    CalculusDeclarationSyntax.canonical
                      (.rule (encodeRuleSchema schema)))) =
                some
                  { judgments := []
                    rules := rules
                    conversion := none } := by
            simpa [ProofCalculus.empty] using elaborate_rules rules []
          rw [rulesOnly]
          simp
      | some declaration =>
          simp only [quote, Option.toList_some, List.map_cons]
          rw [List.append_assoc]
          rw [elaborate_judgments judgments]
          simp only [List.map_nil]
          have rulesThenConversion :
              elaborate
                  (rules.map (fun schema =>
                      CalculusDeclarationSyntax.canonical
                        (.rule (encodeRuleSchema schema))) ++
                    [CalculusDeclarationSyntax.canonical
                      (.conversion (encodeConversion declaration))]) =
                some
                  { judgments := []
                    rules := rules
                    conversion := some declaration } := by
            rw [elaborate_rules rules]
            simp
          rw [rulesThenConversion]
          simp

/-- Atomic axiom notation and its canonical expansion elaborate identically. -/
@[simp] theorem elaborateDeclaration_axiom (id : String)
    (conclusion : PatternSyntax) :
    elaborateDeclaration (.axiom id conclusion) =
      elaborateDeclaration
        (.canonical (.rule
          { id
            metavariables := []
            premises := []
            conclusion
            sideConditions := [] })) :=
  by simp [elaborateDeclaration, elaborateCanonical, decodeRuleSchema]

/-- Replacing one atomic declaration by an authored atomic rewrite does not
change its elaborated calculus fragment. -/
theorem elaborateDeclaration_rewrite {source target}
    (step : calculusDeclarationGSLT.Step source target) :
    elaborateDeclaration source = elaborateDeclaration target := by
  cases step
  exact elaborateDeclaration_axiom _ _

private theorem elaborate_document_equiv :
    ∀ {source target : CalculusSyntax},
      GSLT.DocumentEquiv calculusDeclarationGSLT source target →
        elaborate source = elaborate target
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      change _ = _ at head
      cases head
      simp only [elaborate]
      rw [elaborate_document_equiv tail]

/-- A pointwise calculus-document equation preserves elaboration. -/
theorem elaborate_equation {source target : CalculusSyntax}
    (equivalent : calculusSyntaxGSLT.Equiv source target) :
    elaborate source = elaborate target :=
  elaborate_document_equiv equivalent

private theorem elaborate_raw_rewrite :
    ∀ {source target : CalculusSyntax},
      GSLT.RawDocumentStep calculusDeclarationGSLT source target →
        elaborate source = elaborate target
  | _, _, .head rewrite => by
      simp only [elaborate]
      rw [elaborateDeclaration_rewrite rewrite]
  | _, _, .tail rewrite => by
      simp only [elaborate]
      rw [elaborate_raw_rewrite rewrite]

/-- Elaboration respects every contextual rewrite of the authored document
GSLT. -/
theorem elaborate_rewrite {source target : CalculusSyntax}
    (step : calculusSyntaxGSLT.Step source target) :
    elaborate source = elaborate target := by
  change GSLT.DocumentStep calculusDeclarationGSLT source target at step
  rcases step with
    ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetTarget⟩
  calc
    elaborate source = elaborate middleSource := elaborate_equation sourceMiddle
    _ = elaborate middleTarget := elaborate_raw_rewrite rewrite
    _ = elaborate target := elaborate_equation middleTargetTarget

/-! ## The indexed extension layer -/

/-- Every term language admits an independently authored inference layer. -/
def layer : CoGSLTLayer LanguageDef where
  Fiber := fun _ => ProofCalculus
  sourceGSLT := fun _ => calculusSyntaxGSLT
  elaborate := fun _ => elaborate
  quote := fun _ => quote
  elaborate_quote := fun _ => elaborate_quote
  elaborate_equation := fun _ => elaborate_equation
  elaborate_rewrite := fun _ => elaborate_rewrite

/-- Attaching a proof calculus does not change the term language. -/
@[simp] theorem erase_attached (language : LanguageDef)
    (extension : ProofCalculus) :
    layer.erase (layer.attach language extension) = language :=
  rfl

/-! ## Positive and negative canaries -/

private def canaryLanguage : LanguageDef := LanguageDef.empty "inference-layer-canary"
private def canaryJudgment : JudgmentDecl := ⟨"Canary", 1⟩
private def emptyAttached : layer.Total :=
  layer.attach canaryLanguage .empty
private def judgmentAttached : layer.Total :=
  layer.attach canaryLanguage { judgments := [canaryJudgment] }

/-- One term language supports distinct authored proof calculi. -/
def inferenceLayerNonTrivialFiber :
    NonTrivialFiber layer.erase (fun attached => attached.2) where
  left := emptyAttached
  right := judgmentAttached
  sameShadow := rfl
  differentValue := by
    intro equality
    have judgmentEquality := congrArg ProofCalculus.judgments equality
    simp [emptyAttached, judgmentAttached, ProofCalculus.empty,
      canaryJudgment, layer, ExtensionLayer.attach] at judgmentEquality

/-- An authored proof calculus is not generally derivable from the five-field
term-language base. -/
theorem authored_inference_not_determined_by_language :
    ¬ Factors layer.erase (fun attached => attached.2) :=
  inferenceLayerNonTrivialFiber.not_factors

/-- Conflicting rooted conversion authorities are rejected. -/
example (first second : ConversionDecl) :
    elaborate
        [.canonical (.conversion (encodeConversion first)),
         .canonical (.conversion (encodeConversion second))] = none := by
  rfl

/-- A certified realization can specialize the generic elaborator without
becoming part of the extension language.  Here the artifact and observation
are both the rule count, while the authored payload remains the full calculus. -/
private def ruleCountRealization :
    CoGSLTLayer.Realization layer (fun _ => Nat) (fun _ => Nat) where
  compile := fun _ extension => extension.rules.length
  observeSource := fun _ extension => extension.rules.length
  observeArtifact := fun _ count => count
  adequate := fun _ _ => rfl

example (id : String) :
    ruleCountRealization.compileTerm? canaryLanguage
        [.axiom id (.apply "answer" [])] = some 1 := by
  simp [CoGSLTLayer.Realization.compileTerm?, elaborate,
    elaborateDeclaration, layer, ruleCountRealization]

/-- A compiler that inflates every rule count cannot satisfy the same
observation contract.  The adequacy field therefore excludes a real wrong
backend rather than merely recording a compilation function. -/
theorem inflated_rule_count_not_adequate :
    ¬ ∀ calculus : ProofCalculus,
      calculus.rules.length + 1 = calculus.rules.length := by
  intro claimed
  have emptyClaim := claimed .empty
  simp [ProofCalculus.empty] at emptyClaim

end Mettapedia.GSLT.LanguageDef.InferenceExtension
