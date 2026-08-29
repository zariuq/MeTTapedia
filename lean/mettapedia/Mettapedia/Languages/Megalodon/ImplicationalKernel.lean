import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Megalodon implicational-kernel authority

This module isolates the `Imp`, `Hyp`, `PPfAp`, and `PLam` fragment of
Megalodon's checked `Mathdata` proof terms.  It gives the fragment an authored
CertificateGSLT definition and compiles its intrinsic proof terms to generic NIK
articles.  The result is an exact fragment authority, not a claim of adequacy
for the full Megalodon parser, dynamic-operator environment, polymorphism,
definitions, or HOTG theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ImplicationalKernel

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Propositions in the countably generated implicational fragment. -/
inductive Formula where
  | atom : Nat → Formula
  | imp : Formula → Formula → Formula
deriving DecidableEq, Repr

/-- The corresponding fragment of Megalodon's `Mathdata.pf`. -/
inductive Proof where
  | hyp : Nat → Proof
  | app : Proof → Proof → Proof
  | lam : Formula → Proof → Proof
deriving DecidableEq, Repr

/-- Algorithmic proposition synthesis for the fragment. -/
def infer : List Formula → Proof → Option Formula
  | context, .hyp index => context[index]?
  | context, .app function argument => do
      let .imp domain codomain ← infer context function | none
      let actual ← infer context argument
      if actual = domain then some codomain else none
  | context, .lam domain body => do
      let codomain ← infer (domain :: context) body
      some (.imp domain codomain)

private def expressionType : TypeDecl := TypeDecl.plain "MegalodonImpExpr"

private def expressionConstructor (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := "MegalodonImpExpr"
    params := (List.range arity).map fun index =>
      .simple s!"argument{index}" (.base "MegalodonImpExpr")
    syntaxPattern := [] }

def encodeNat : Nat → Pattern
  | 0 => .apply "MZero" []
  | index + 1 => .apply "MSucc" [encodeNat index]

theorem encodeNat_ground (index : Nat) :
    (encodeNat index).isGroundAt 0 = true := by
  induction index with
  | zero =>
      simp [encodeNat, Pattern.isGroundAt, Pattern.isGroundListAt]
  | succ index indexIH =>
      simp [encodeNat, Pattern.isGroundAt, Pattern.isGroundListAt, indexIH]

theorem encodeNat_canonical (index : Nat) :
    (encodeNat index).hasCanonicalBinderMetadata = true := by
  induction index with
  | zero =>
      simp [encodeNat, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | succ index indexIH =>
      simp [encodeNat, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, indexIH]

def encodeFormula : Formula → Pattern
  | .atom index => .apply "MAtom" [encodeNat index]
  | .imp domain codomain =>
      .apply "MImp" [encodeFormula domain, encodeFormula codomain]

def encodeContext : List Formula → Pattern
  | [] => .apply "MCtxNil" []
  | formula :: context =>
      .apply "MCtxCons" [encodeFormula formula, encodeContext context]

theorem encodeFormula_ground (formula : Formula) :
    (encodeFormula formula).isGroundAt 0 = true := by
  induction formula with
  | atom index =>
      simp [encodeFormula, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeNat_ground]
  | imp domain codomain domainIH codomainIH =>
      simp [encodeFormula, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, codomainIH]

theorem encodeFormula_canonical (formula : Formula) :
    (encodeFormula formula).hasCanonicalBinderMetadata = true := by
  induction formula with
  | atom index =>
      simp [encodeFormula, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_canonical]
  | imp domain codomain domainIH codomainIH =>
      simp [encodeFormula, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, codomainIH]

theorem encodeContext_ground (context : List Formula) :
    (encodeContext context).isGroundAt 0 = true := by
  induction context with
  | nil =>
      simp [encodeContext, Pattern.isGroundAt, Pattern.isGroundListAt]
  | cons formula context contextIH =>
      simp [encodeContext, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeFormula_ground, contextIH]

theorem encodeContext_canonical (context : List Formula) :
    (encodeContext context).hasCanonicalBinderMetadata = true := by
  induction context with
  | nil =>
      simp [encodeContext, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons formula context contextIH =>
      simp [encodeContext, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeFormula_canonical,
        contextIH]

private def proves (context formula : Pattern) : Pattern :=
  .apply "MProves" [context, formula]

private def ruleId (value : String) : RuleId := ⟨value⟩

private def hypZeroRule : RuleSchema :=
  { id := ruleId "megalodon-hyp-zero"
    metavariables := [("context", 0), ("formula", 0)]
    premises := []
    conclusion :=
      proves
        (.apply "MCtxCons" [.fvar "formula", .fvar "context"])
        (.fvar "formula") }

private def weakenRule : RuleSchema :=
  { id := ruleId "megalodon-weaken"
    metavariables :=
      [("context", 0), ("formula", 0), ("head", 0)]
    premises := [proves (.fvar "context") (.fvar "formula")]
    conclusion :=
      proves
        (.apply "MCtxCons" [.fvar "head", .fvar "context"])
        (.fvar "formula") }

private def implicationIntroductionRule : RuleSchema :=
  { id := ruleId "megalodon-imp-intro"
    metavariables :=
      [("context", 0), ("domain", 0), ("codomain", 0)]
    premises :=
      [proves
        (.apply "MCtxCons" [.fvar "domain", .fvar "context"])
        (.fvar "codomain")]
    conclusion :=
      proves (.fvar "context")
        (.apply "MImp" [.fvar "domain", .fvar "codomain"]) }

private def implicationEliminationRule : RuleSchema :=
  { id := ruleId "megalodon-imp-elim"
    metavariables :=
      [("context", 0), ("domain", 0), ("codomain", 0)]
    premises :=
      [ proves (.fvar "context")
          (.apply "MImp" [.fvar "domain", .fvar "codomain"]),
        proves (.fvar "context") (.fvar "domain") ]
    conclusion := proves (.fvar "context") (.fvar "codomain") }

def definition : CalculusLanguageDef :=
  { name := "megalodon-implicational-kernel-v1"
    types := [expressionType]
    terms :=
      [ expressionConstructor "MZero" 0,
        expressionConstructor "MSucc" 1,
        expressionConstructor "MAtom" 1,
        expressionConstructor "MImp" 2,
        expressionConstructor "MCtxNil" 0,
        expressionConstructor "MCtxCons" 2 ]
    equations := []
    rewrites := []
    judgments := [{ head := "MProves", arity := 2 }]
    rules :=
      [ hypZeroRule, weakenRule, implicationIntroductionRule,
        implicationEliminationRule ] }

/-- The Megalodon fragment exposed through the canonical coGSLT-indexed
calculus authoring layer. -/
def coGSLTDefinition : ExtendedLanguageDef calculusLayer :=
  definition.toExtended

/-- The authored Megalodon calculus document is a term of the canonical
calculus-authoring GSLT. -/
def coGSLTSource : coGSLTDefinition.authoredGSLT.Term :=
  coGSLTDefinition.authoredSource

@[simp] theorem coGSLT_source_theory :
    coGSLTDefinition.authoredGSLT =
      InferenceExtension.calculusSyntaxGSLT :=
  rfl

/-- Elaborating the coGSLT source recovers exactly the calculus later consumed
by the generic NIK checker. -/
@[simp] theorem coGSLT_source_elaborates :
    calculusLayer.elaborate definition.toLanguageDef coGSLTSource =
      some definition.toCalculus :=
  definition.toExtended_elaborate_authoredSource

private theorem language_validate : definition.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [definition, expressionType, expressionConstructor,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames]

theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    simpa [definition] using language_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [definition, definition, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid, CalculusLanguageDef.lookupJudgment?,
    RuleSchema.isValidIn, RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, expressionType, expressionConstructor, hypZeroRule,
    weakenRule, implicationIntroductionRule, implicationEliminationRule,
    proves, ruleId]
  decide

def validated : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

/-- The admitted fragment denotes one semantic GSLT.  Since the fragment has
no object-language equations, its equation-compatibility law is immediate. -/
def semanticGSLT : Mettapedia.GSLT.GSLT :=
  definition.toGSLTOfNoEquations definition_valid rfl

private def ruleInstance (id : String) (arguments : List Pattern) :
    RuleInstance :=
  { ruleId := ruleId id, arguments }

private def hypZeroArticle (context formula : Pattern) : RawProof :=
  .node (ruleInstance "megalodon-hyp-zero" [context, formula]) []

private def weakenArticle (context formula head : Pattern)
    (child : RawProof) : RawProof :=
  .node (ruleInstance "megalodon-weaken" [context, formula, head]) [child]

private def implicationIntroductionArticle
    (context domain codomain : Pattern) (child : RawProof) : RawProof :=
  .node
    (ruleInstance "megalodon-imp-intro" [context, domain, codomain])
    [child]

private def implicationEliminationArticle
    (context domain codomain : Pattern)
    (function argument : RawProof) : RawProof :=
  .node
    (ruleInstance "megalodon-imp-elim" [context, domain, codomain])
    [function, argument]

private theorem hypZero_instantiates
    (context : List Formula) (formula : Formula) :
    instantiateRule? validated
      (ruleInstance "megalodon-hyp-zero"
        [encodeContext context, encodeFormula formula]) =
      some ([],
        proves (encodeContext (formula :: context)) (encodeFormula formula)) := by
  simp [validated, definition, definition, hypZeroRule, weakenRule,
    implicationIntroductionRule, implicationEliminationRule, ruleInstance,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, proves, encodeContext, encodeFormula_ground,
    encodeFormula_canonical, encodeContext_ground, encodeContext_canonical,
    ruleId]

private theorem weaken_instantiates
    (context : List Formula) (formula head : Formula) :
    instantiateRule? validated
      (ruleInstance "megalodon-weaken"
        [encodeContext context, encodeFormula formula, encodeFormula head]) =
      some
        ([proves (encodeContext context) (encodeFormula formula)],
          proves (encodeContext (head :: context)) (encodeFormula formula)) := by
  simp [validated, definition, definition, hypZeroRule, weakenRule,
    implicationIntroductionRule, implicationEliminationRule, ruleInstance,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, proves, encodeContext, encodeFormula_ground,
    encodeFormula_canonical, encodeContext_ground, encodeContext_canonical,
    ruleId]

private theorem implicationIntroduction_instantiates
    (context : List Formula) (domain codomain : Formula) :
    instantiateRule? validated
      (ruleInstance "megalodon-imp-intro"
        [encodeContext context, encodeFormula domain, encodeFormula codomain]) =
      some
        ([proves (encodeContext (domain :: context)) (encodeFormula codomain)],
          proves (encodeContext context) (encodeFormula (.imp domain codomain))) := by
  simp [validated, definition, definition, hypZeroRule, weakenRule,
    implicationIntroductionRule, implicationEliminationRule, ruleInstance,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, proves, encodeFormula, encodeContext,
    encodeFormula_ground, encodeFormula_canonical, encodeContext_ground,
    encodeContext_canonical, ruleId]

private theorem implicationElimination_instantiates
    (context : List Formula) (domain codomain : Formula) :
    instantiateRule? validated
      (ruleInstance "megalodon-imp-elim"
        [encodeContext context, encodeFormula domain, encodeFormula codomain]) =
      some
        ([ proves (encodeContext context) (encodeFormula (.imp domain codomain)),
           proves (encodeContext context) (encodeFormula domain) ],
          proves (encodeContext context) (encodeFormula codomain)) := by
  simp [validated, definition, definition, hypZeroRule, weakenRule,
    implicationIntroductionRule, implicationEliminationRule, ruleInstance,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, proves, encodeFormula, encodeFormula_ground,
    encodeFormula_canonical, encodeContext_ground, encodeContext_canonical,
    ruleId]

/-- Compile an intrinsic fragment proof to its inferred proposition and one
generic NIK article. -/
def compile : (context : List Formula) → Proof → Option (Formula × RawProof)
  | [], .hyp _ => none
  | formula :: context, .hyp 0 =>
      some (formula,
        hypZeroArticle (encodeContext context) (encodeFormula formula))
  | head :: context, .hyp (index + 1) => do
      let (formula, child) ← compile context (.hyp index)
      some (formula,
        weakenArticle (encodeContext context) (encodeFormula formula)
          (encodeFormula head) child)
  | context, .lam domain body => do
      let (codomain, child) ← compile (domain :: context) body
      some (.imp domain codomain,
        implicationIntroductionArticle (encodeContext context)
          (encodeFormula domain) (encodeFormula codomain) child)
  | context, .app function argument => do
      let (functionType, functionArticle) ← compile context function
      let .imp domain codomain := functionType | none
      let (actual, argumentArticle) ← compile context argument
      if actual = domain then
        some (codomain,
          implicationEliminationArticle (encodeContext context)
            (encodeFormula domain) (encodeFormula codomain)
            functionArticle argumentArticle)
      else
        none

private theorem hypZero_checked (context : List Formula) (formula : Formula) :
    checkRaw validated
      (proves (encodeContext (formula :: context)) (encodeFormula formula))
      (hypZeroArticle (encodeContext context) (encodeFormula formula)) = true := by
  simp [checkRaw, checkRawChildren, hypZeroArticle,
    hypZero_instantiates]

private theorem weaken_checked
    (context : List Formula) (formula head : Formula) (child : RawProof)
    (hchild :
      checkRaw validated
        (proves (encodeContext context) (encodeFormula formula)) child = true) :
    checkRaw validated
      (proves (encodeContext (head :: context)) (encodeFormula formula))
      (weakenArticle (encodeContext context) (encodeFormula formula)
        (encodeFormula head) child) = true := by
  simp [checkRaw, checkRawChildren, weakenArticle, weaken_instantiates,
    hchild]

private theorem implicationIntroduction_checked
    (context : List Formula) (domain codomain : Formula) (child : RawProof)
    (hchild :
      checkRaw validated
        (proves (encodeContext (domain :: context)) (encodeFormula codomain))
        child = true) :
    checkRaw validated
      (proves (encodeContext context) (encodeFormula (.imp domain codomain)))
      (implicationIntroductionArticle (encodeContext context)
        (encodeFormula domain) (encodeFormula codomain) child) = true := by
  simp [checkRaw, checkRawChildren, implicationIntroductionArticle,
    implicationIntroduction_instantiates, hchild]

private theorem implicationElimination_checked
    (context : List Formula) (domain codomain : Formula)
    (function argument : RawProof)
    (hfunction :
      checkRaw validated
        (proves (encodeContext context)
          (encodeFormula (.imp domain codomain))) function = true)
    (hargument :
      checkRaw validated
        (proves (encodeContext context) (encodeFormula domain))
        argument = true) :
    checkRaw validated
      (proves (encodeContext context) (encodeFormula codomain))
      (implicationEliminationArticle (encodeContext context)
        (encodeFormula domain) (encodeFormula codomain)
        function argument) = true := by
  simp [checkRaw, checkRawChildren, implicationEliminationArticle,
    implicationElimination_instantiates, hfunction, hargument]

private theorem compile_hyp_checked
    {context : List Formula} {index : Nat} {formula : Formula}
    {article : RawProof}
    (compiled : compile context (.hyp index) = some (formula, article)) :
    checkRaw validated
      (proves (encodeContext context) (encodeFormula formula)) article = true := by
  induction context generalizing index formula article with
  | nil => simp [compile] at compiled
  | cons head tail tailIH =>
      cases index with
      | zero =>
          simp [compile] at compiled
          rcases compiled with ⟨rfl, rfl⟩
          exact hypZero_checked tail head
      | succ index =>
          simp only [compile] at compiled
          cases hrecursive : compile tail (.hyp index) with
          | none => simp [hrecursive] at compiled
          | some result =>
              rcases result with ⟨resultFormula, resultArticle⟩
              simp [hrecursive] at compiled
              rcases compiled with ⟨rfl, rfl⟩
              exact weaken_checked tail resultFormula head resultArticle
                (tailIH hrecursive)

/-- Every article emitted by the fragment compiler is accepted by the exact
authored CertificateGSLT definition at the same inferred endpoint. -/
theorem compile_checked
    {context : List Formula} {proof : Proof} {formula : Formula}
    {article : RawProof}
    (compiled : compile context proof = some (formula, article)) :
    checkRaw validated
      (proves (encodeContext context) (encodeFormula formula)) article = true := by
  induction proof generalizing context formula article with
  | hyp index => exact compile_hyp_checked compiled
  | app function argument functionIH argumentIH =>
      simp only [compile] at compiled
      cases hfunction : compile context function with
      | none => simp [hfunction] at compiled
      | some functionResult =>
          rcases functionResult with ⟨functionType, functionArticle⟩
          cases functionType with
          | atom => simp [hfunction] at compiled
          | imp domain codomain =>
              cases hargument : compile context argument with
              | none => simp [hfunction, hargument] at compiled
              | some argumentResult =>
                  rcases argumentResult with ⟨actual, argumentArticle⟩
                  by_cases heq : actual = domain
                  · subst actual
                    simp [hfunction, hargument] at compiled
                    rcases compiled with ⟨rfl, rfl⟩
                    exact implicationElimination_checked context domain codomain
                      functionArticle argumentArticle
                      (functionIH hfunction) (argumentIH hargument)
                  · simp [hfunction, hargument, heq] at compiled
  | lam domain body bodyIH =>
      simp only [compile] at compiled
      cases hbody : compile (domain :: context) body with
      | none => simp [hbody] at compiled
      | some bodyResult =>
          rcases bodyResult with ⟨codomain, child⟩
          simp [hbody] at compiled
          rcases compiled with ⟨rfl, rfl⟩
          exact implicationIntroduction_checked context domain codomain child
            (bodyIH hbody)

def identityProof : Proof := .lam (.atom 0) (.hyp 0)

def identityGoal : Pattern :=
  proves (encodeContext []) (encodeFormula (.imp (.atom 0) (.atom 0)))

def identityArticle : RawProof :=
  implicationIntroductionArticle (encodeContext [])
    (encodeFormula (.atom 0)) (encodeFormula (.atom 0))
    (hypZeroArticle (encodeContext []) (encodeFormula (.atom 0)))

theorem identity_compiles :
    compile [] identityProof =
      some (.imp (.atom 0) (.atom 0), identityArticle) := by
  simp [compile, identityProof, identityArticle]

theorem identity_accepted :
    checkRaw validated identityGoal identityArticle = true := by
  exact compile_checked identity_compiles

def modusPonensProof : Proof :=
  .lam (.imp (.atom 0) (.atom 1))
    (.lam (.atom 0) (.app (.hyp 1) (.hyp 0)))

def modusPonensGoal : Pattern :=
  proves (encodeContext [])
    (encodeFormula
      (.imp (.imp (.atom 0) (.atom 1))
        (.imp (.atom 0) (.atom 1))))

def modusPonensArticle : RawProof :=
  let atom0 := encodeFormula (.atom 0)
  let atom1 := encodeFormula (.atom 1)
  let implication := encodeFormula (.imp (.atom 0) (.atom 1))
  implicationIntroductionArticle (encodeContext []) implication implication
    (implicationIntroductionArticle
      (encodeContext [.imp (.atom 0) (.atom 1)]) atom0 atom1
      (implicationEliminationArticle
        (encodeContext [.atom 0, .imp (.atom 0) (.atom 1)]) atom0 atom1
        (weakenArticle
          (encodeContext [.imp (.atom 0) (.atom 1)]) implication atom0
          (hypZeroArticle (encodeContext []) implication))
        (hypZeroArticle
          (encodeContext [.imp (.atom 0) (.atom 1)]) atom0)))

theorem modus_ponens_compiles :
    compile [] modusPonensProof =
      some
        (.imp (.imp (.atom 0) (.atom 1)) (.imp (.atom 0) (.atom 1)),
          modusPonensArticle) := by
  simp [compile, modusPonensProof, modusPonensArticle]

theorem modus_ponens_accepted :
    checkRaw validated modusPonensGoal modusPonensArticle = true := by
  exact compile_checked modus_ponens_compiles

/-- The checked modus-ponens article is also a reduction to the empty goal
state in the GSLT denoted by the authored Megalodon calculus. -/
theorem modus_ponens_semantic_reachability :
    semanticGSLT.MultiStep
      (TotalGSLT.inCalculus [modusPonensGoal])
      (TotalGSLT.inCalculus []) := by
  rcases checkRaw_exists_derivation_with_exact_erasure
      modus_ponens_accepted with ⟨derivation, _⟩
  have derivations :
      DerivationList validated [modusPonensGoal] :=
    .cons derivation .nil
  exact (definition.toGSLT_derivability definition_valid
    (TotalGSLT.ReductionRespectsEquations.of_no_equations rfl)
    [modusPonensGoal]).mp ⟨derivations⟩

def wrongExactGoal : Pattern :=
  proves (encodeContext [])
    (encodeFormula (.imp (.atom 0) (.imp (.atom 0) (.atom 0))))

theorem wrong_exact_rejected :
    checkRaw validated wrongExactGoal identityArticle = false := by
  cases hcheck : checkRaw validated wrongExactGoal identityArticle with
  | false => rfl
  | true =>
      exfalso
      have hgoals : identityGoal = wrongExactGoal :=
        checkRaw_goal_unique identity_accepted hcheck
      simp [identityGoal, wrongExactGoal, proves, encodeContext,
        encodeFormula, encodeNat] at hgoals

end Mettapedia.Languages.Megalodon.ImplicationalKernel
