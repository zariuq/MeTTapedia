import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionNamedDAG
import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
import Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo

/-!
# One-pass ground-resolution verification from official TPTP data

This module connects the official all-family semantic carrier to the existing
authored ground-resolution calculus.  It is deliberately a partial semantic
projection: only ground CNF inputs and explicit `resolution` records with
`status(thm)` are supported.  Every other official family or inference rule
returns `incomplete`; malformed carrier data or a false derivation returns
`rejected`.

The verifier does not search for a proof.  It decodes one topologically ordered
semantic derivation, resolves parent names left-to-right, reconstructs only the
finite local pivot evidence required by the authored calculus, and invokes the
generic whole-problem checker once.  A successful result contains the checker
acceptance proof, so semantic soundness is obtained without a second runtime
replay.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionVerifier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
open Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionNamedDAG
open Mettapedia.Languages.TPTP.GroundCNFAuthority

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

/-! ## Ground-CNF semantic decoding -/

def decodeInitialRole? (role : Pattern) : Option InputRole := do
  match <- decodeRoleLexeme? role with
  | "axiom" => some .axiom
  | "hypothesis" => some .hypothesis
  | "negated_conjecture" => some .negatedConjecture
  | _ => none

mutual
  /-- Official first-order syntax is logically ground exactly when it contains
  no object-variable constructor and no MeTTa binder or metavariable. -/
  def isGroundOfficial : Pattern -> Bool
    | .apply label arguments =>
        label != "tptp92-ast:variable:alt-1" &&
          isGroundOfficialList arguments
    | _ => false

  def isGroundOfficialList : List Pattern -> Bool
    | [] => true
    | pattern :: patterns =>
        isGroundOfficial pattern && isGroundOfficialList patterns
end

def falseAtomicFormula : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-2" [
    a "tptp92-ast:fof-defined-atomic-formula:alt-1" [
      a "tptp92-ast:fof-defined-plain-formula:alt-1" [
        a "tptp92-ast:fof-defined-plain-term:alt-1" [
          a "tptp92-ast:defined-constant:alt-1" [
            a "tptp92-ast:defined-functor:alt-1" [
              a "tptp92-ast:atomic-defined-word:alt-1" [
                a "tptp92-ast:token:dollar-word" [a "$false"]]]]]]]]

/-- Recognize the official `$false` atom structurally.  Keeping this as a
constructor match avoids making semantic decoding depend on whole-tree
decidable equality. -/
def isFalseAtomicFormula : Pattern -> Bool
  | .apply "tptp92-ast:fof-atomic-formula:alt-2" [
      .apply "tptp92-ast:fof-defined-atomic-formula:alt-1" [
        .apply "tptp92-ast:fof-defined-plain-formula:alt-1" [
          .apply "tptp92-ast:fof-defined-plain-term:alt-1" [
            .apply "tptp92-ast:defined-constant:alt-1" [
              .apply "tptp92-ast:defined-functor:alt-1" [
                .apply "tptp92-ast:atomic-defined-word:alt-1" [
                  .apply "tptp92-ast:token:dollar-word" [
                    .apply "$false" []]]]]]]]] => true
  | _ => false

def decodeLiteral? : Pattern -> Option SemanticLiteral
  | .apply "tptp92-ast:cnf-literal:alt-1" [atom] => do
      if isFalseAtomicFormula atom then none
      else if isGroundOfficial atom then some (.positive atom)
      else none
  | .apply "tptp92-ast:cnf-literal:alt-2" [atom]
  | .apply "tptp92-ast:cnf-literal:alt-3" [atom] => do
      if isFalseAtomicFormula atom then none
      else if isGroundOfficial atom then some (.negative atom)
      else none
  | .apply "tptp92-ast:cnf-literal:alt-4" [infixFormula] => do
      if isGroundOfficial infixFormula then some (.positive infixFormula)
      else none
  | .apply "tptp92-ast:cnf-literal:corpus-parenthesized" [literal] =>
      decodeLiteral? literal
  | _ => none

def isFalseDisjunction : Pattern -> Bool
  | .apply "tptp92-ast:cnf-disjunction:alt-1"
      [.apply "tptp92-ast:cnf-literal:alt-1" [atom]] =>
      isFalseAtomicFormula atom
  | _ => false

def decodeDisjunction? : Pattern -> Option SemanticClause
  | .apply "tptp92-ast:cnf-disjunction:alt-1" [literal] => do
      let decoded <- decodeLiteral? literal
      some [decoded]
  | .apply "tptp92-ast:cnf-disjunction:alt-2" [left, literal] => do
      let decodedLeft <- decodeDisjunction? left
      let decodedLiteral <- decodeLiteral? literal
      some (decodedLeft ++ [decodedLiteral])
  | _ => none

def decodeCnfFormula? : Pattern -> Option SemanticClause
  | .apply "tptp92-ast:cnf-formula:alt-1" [disjunction] =>
      if isFalseDisjunction disjunction then some []
      else decodeDisjunction? disjunction
  | .apply "tptp92-ast:cnf-formula:alt-2" [body] =>
      decodeCnfFormula? body
  | _ => none

def decodeNamedParent? : Pattern -> Option String
  | .apply "tptp92-ast:parent-info:alt-1" [
      .apply "tptp92-ast:source:alt-1" [
        .apply "tptp92-ast:dag-source:alt-1" [name]], _] =>
      decodeName? name
  | _ => none

def decodeCommaParent? : Pattern -> Option String
  | .apply "tptp92-ast:comma-parent-info:alt-1" [parent] =>
      decodeNamedParent? parent
  | _ => none

def decodeCommaParents? : Pattern -> Option (List String)
  | .apply "tptp92-ast:list:tptp92ast-comma-parent-info:nil" [] => some []
  | .apply "tptp92-ast:list:tptp92ast-comma-parent-info:cons"
      [parent, rest] => do
      let decodedParent <- decodeCommaParent? parent
      let decodedRest <- decodeCommaParents? rest
      some (decodedParent :: decodedRest)
  | _ => none

def decodeParents? : Pattern -> Option (List String)
  | .apply "tptp92-ast:parents:alt-2" [
      .apply "tptp92-ast:parent-list:alt-1" [first, rest]] => do
      let decodedFirst <- decodeNamedParent? first
      let decodedRest <- decodeCommaParents? rest
      some (decodedFirst :: decodedRest)
  | .apply "tptp92-ast:parents:alt-1" [] => some []
  | _ => none

structure DecodedInference where
  rule : String
  parents : List String
deriving DecidableEq, Repr

def decodeInference? : Pattern -> Option DecodedInference
  | .apply "tptp92-ast:annotations:alt-1" [
      .apply "tptp92-ast:source:alt-1" [
        .apply "tptp92-ast:dag-source:alt-2" [
          .apply "tptp92-ast:inference-record:alt-1"
            [rule, usefulInfo, parents]]], _] => do
      if decodeUniqueStatus? usefulInfo != some .thm then none else
      match rule with
      | .apply "tptp92-ast:inference-rule:alt-1" [word] => do
          let decodedRule <- decodeAtomicWord? word
          let decodedParents <- decodeParents? parents
          some { rule := decodedRule, parents := decodedParents }
      | _ => none
  | _ => none

inductive DecodedSource where
  | initial (role : InputRole)
  | inference (record : DecodedInference)
deriving DecidableEq, Repr

structure DecodedCnfInput where
  occurrence : Pattern
  name : String
  clause : SemanticClause
  source : DecodedSource
  span : Pattern
deriving DecidableEq, Repr

def decodeCnfInput? (input : AnnotatedInputView) : Option DecodedCnfInput := do
  let annotated <- match input.payload with
    | .cnf annotated => some annotated
    | _ => none
  match annotated with
  | .apply "tptp92-ast:cnf-annotated:alt-1"
      [name, role, formula, annotations] =>
      let source <- match annotations with
        | .apply "tptp92-ast:annotations:alt-2" [] =>
            (decodeInitialRole? role).map .initial
        | _ => (decodeInference? annotations).map .inference
      let decodedName <- decodeName? name
      let decodedClause <- decodeCnfFormula? formula
      some {
        occurrence := input.occurrence
        name := decodedName
        clause := decodedClause
        source := source
        span := input.span
      }
  | _ => none

/-! ## Semantic derivation decoding and chronological lowering -/

def decodeSourceInputs? (source : Pattern) :
    List AnnotatedInputView -> Option (List DecodedCnfInput)
  | [] => some []
  | input :: inputs => do
      if !occurrenceBelongsToSource source input.occurrence then
        none
      else
        let decodedInput <- decodeCnfInput? input
        let decodedRest <- decodeSourceInputs? source inputs
        some (decodedInput :: decodedRest)

structure DecodedDerivation where
  sourceDigest : String
  inputs : List DecodedCnfInput
deriving DecidableEq, Repr

def decodeDerivation? : Pattern -> Option DecodedDerivation
  | .apply "tptp-semantic:derivation" [source, nodes] => do
      let sourceDigest <- decodeSourceDigest? source
      let nodeViews <- decodeNodeViews? nodes
      let inputs <- decodeSourceInputs? source nodeViews
      some {
        sourceDigest := sourceDigest
        inputs := inputs
      }
  | _ => none

structure LowerState where
  clausesRev : List
    (Mettapedia.Languages.TPTP.GroundCNFAuthority.ParsedClause Pattern)
  nodesRev : List NamedInference
  nextInitialId : Nat
  derivedSeen : Bool
  lastDerived : Option (String × SemanticClause)

def lowerInput? (state : LowerState) (input : DecodedCnfInput) :
    Option LowerState :=
  match input.source with
  | .initial role => do
      if state.derivedSeen then none else
      some {
        state with
        clausesRev := {
          id := state.nextInitialId
          name := input.name
          role := role
          literals := input.clause
        } :: state.clausesRev
        nextInitialId := state.nextInitialId + 1
      }
  | .inference record => do
      if record.rule != "resolution" then none else
      some {
        state with
        nodesRev := {
          name := input.name
          key := TptpGroundResolutionProblemAuthority.resolutionKey
          parents := record.parents
          inferred := .clause input.clause
          evidence := .reconstruct
        } :: state.nodesRev
        derivedSeen := true
        lastDerived := some (input.name, input.clause)
      }

def lowerInputs? : LowerState -> List DecodedCnfInput -> Option LowerState
  | state, [] => some state
  | state, input :: inputs => do
      let next <- lowerInput? state input
      lowerInputs? next inputs

structure LoweredRefutation where
  submission : NamedSubmission
  expectedEmpty : submission.expected = .clause []

def lowerRefutation? (term : Pattern) : Option LoweredRefutation := do
  let decoded <- decodeDerivation? term
  let final <- lowerInputs? {
    clausesRev := []
    nodesRev := []
    nextInitialId := 0
    derivedSeen := false
    lastDerived := none
  } decoded.inputs
  let (root, finalClause) <- final.lastDerived
  if finalClause != [] then none else
  some {
    submission := {
      problem := {
        sourceDigest := decoded.sourceDigest
        clauses := final.clausesRev.reverse
      }
      nodes := final.nodesRev.reverse
      root := root
      expected := .clause []
    }
    expectedEmpty := rfl
  }

/-! ## Proof-carrying single-pass result -/

inductive VerificationOutcome where
  | verified
  | incomplete
  | rejected
deriving DecidableEq, Repr

structure VerifiedRefutation where
  source : Pattern
  lowering : LoweredRefutation
  admitted : checkHasType language WellSorted.FreeTypeContext.empty [] source
    (.base "TptpSemantic:derivation") = true
  lowered : lowerRefutation? source = some lowering
  accepted : TptpGroundResolutionNamedDAG.verify lowering.submission = true

inductive VerificationResult where
  | verified (evidence : VerifiedRefutation)
  | incomplete
  | rejected

def VerificationResult.outcome : VerificationResult -> VerificationOutcome
  | .verified _ => .verified
  | .incomplete => .incomplete
  | .rejected => .rejected

/-- The calculus phase after carrier admission.  It is public separately so
the semantic lowering and the generic admission boundary have independent
positive and negative controls. -/
def verifyAdmittedPayload (source : Pattern) : VerificationOutcome :=
  match lowerRefutation? source with
  | none => .incomplete
  | some lowering =>
      if TptpGroundResolutionNamedDAG.verify lowering.submission then
        .verified
      else
        .rejected

/-- Verify a carrier-admitted ground refutation.  Unsupported formula families
or calculus rules are incomplete; malformed carriers and invalid proof DAGs
are rejected. -/
def verify (source : Pattern) : VerificationResult :=
  if admitted : checkHasType language WellSorted.FreeTypeContext.empty [] source
      (.base "TptpSemantic:derivation") = true then
    match lowered : lowerRefutation? source with
    | none => .incomplete
    | some lowering =>
        if accepted :
            TptpGroundResolutionNamedDAG.verify lowering.submission = true then
          .verified { source, lowering, admitted, lowered, accepted }
        else
          .rejected
  else
    .rejected

def ProblemUnsatisfiable
    (problem : TptpGroundResolutionProblemAuthority.ParsedProblem) : Prop :=
  ∀ valuation,
    ¬ (∀ formula, formula ∈ problem.formulas →
      Formula.Satisfies valuation formula)

theorem compile?_preserves_source {input : NamedSubmission}
    {compiled : CompiledSubmission}
    (compiledEq : TptpGroundResolutionNamedDAG.compile? input =
      some compiled) :
    compiled.submission.problem = input.problem ∧
      compiled.submission.derivation.expected = input.expected := by
  unfold TptpGroundResolutionNamedDAG.compile? at compiledEq
  repeat' split at compiledEq <;> simp_all
  generalize hNodes : TptpGroundResolutionNamedDAG.compileNodes _ input.nodes =
    compiledNodes at compiledEq
  cases compiledNodes with
  | none => simp at compiledEq
  | some final =>
      simp at compiledEq
      rcases compiledEq with ⟨_, _, compiledEq⟩
      generalize hRoot :
        TptpGroundResolutionNamedDAG.lookupName? final.names input.root = root
          at compiledEq
      cases root <;> simp_all
      subst compiled
      exact ⟨rfl, rfl⟩

theorem VerifiedRefutation.objective (result : VerifiedRefutation) :
    ∃ compiled,
      TptpGroundResolutionNamedDAG.compile? result.lowering.submission =
        some compiled ∧
      TptpGroundResolutionProblemAuthority.Objective compiled.submission :=
  TptpGroundResolutionNamedDAG.verify_sound result.accepted

theorem VerifiedRefutation.unsatisfiable (result : VerifiedRefutation) :
    ProblemUnsatisfiable result.lowering.submission.problem := by
  obtain ⟨compiled, compiledEq, sound⟩ :=
    TptpGroundResolutionNamedDAG.verify_sound result.accepted
  obtain ⟨compiledProblem, compiledExpected⟩ :=
    compile?_preserves_source compiledEq
  intro valuation allSatisfied
  have emptySatisfied : Formula.Satisfies valuation (.clause []) := by
    have compiledAll :
        (Formula.semantics (Atom := Pattern)).SatisfiesAll valuation
          compiled.submission.problem.formulas := by
      rw [compiledProblem]
      exact allSatisfied
    have expectedSatisfied := sound valuation compiledAll
    rw [compiledExpected, result.lowering.expectedEmpty] at expectedSatisfied
    exact expectedSatisfied
  rcases emptySatisfied with ⟨literal, member, _⟩
  simp at member

/-! ## Official ground-CNF controls -/

namespace Canary

def source : Pattern := a "tptp-semantic:source-digest" [a "fixture"]

def occurrence (index : Nat) : Pattern :=
  a "tptp-semantic:occurrence-id" [source, a (toString index)]

def span (index : Nat) : Pattern :=
  a "tptp92-ast:source-span"
    [a (toString (index * 10)), a (toString (index * 10 + 9))]

def atomicWord (value : String) : Pattern :=
  a "tptp92-ast:atomic-word:alt-1"
    [a "tptp92-ast:token:lower-word" [a value]]

def name (value : String) : Pattern :=
  a "tptp92-ast:name:alt-1" [atomicWord value]

def role (value : String) : Pattern :=
  a "tptp92-ast:formula-role:alt-1"
    [a "tptp92-ast:token:lower-word" [a value]]

def atom (value : String) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-1" [
    a "tptp92-ast:fof-plain-atomic-formula:alt-1" [
      a "tptp92-ast:fof-plain-term:alt-1" [
        a "tptp92-ast:constant:alt-1" [
          a "tptp92-ast:functor:alt-1" [atomicWord value]]]]]

theorem atom_injective : Function.Injective atom := by
  intro left right equal
  simpa [atom, atomicWord, a] using equal

def positive (value : String) : Pattern :=
  a "tptp92-ast:cnf-literal:alt-1" [atom value]

def negative (value : String) : Pattern :=
  a "tptp92-ast:cnf-literal:alt-2" [atom value]

def disjunction : List Pattern -> Pattern
  | [] => a "tptp92-ast:cnf-disjunction:alt-1"
      [a "tptp92-ast:cnf-literal:alt-1" [falseAtomicFormula]]
  | literal :: literals =>
      literals.foldl
        (fun left right =>
          a "tptp92-ast:cnf-disjunction:alt-2" [left, right])
        (a "tptp92-ast:cnf-disjunction:alt-1" [literal])

def formula (literals : List Pattern) : Pattern :=
  a "tptp92-ast:cnf-formula:alt-1" [disjunction literals]

def noAnnotations : Pattern := a "tptp92-ast:annotations:alt-2"

def parent (value : String) : Pattern :=
  a "tptp92-ast:parent-info:alt-1" [
    a "tptp92-ast:source:alt-1" [
      a "tptp92-ast:dag-source:alt-1" [name value]],
    a "tptp92-ast:parent-details:alt-2"]

def commaParents : List String -> Pattern
  | [] => a "tptp92-ast:list:tptp92ast-comma-parent-info:nil"
  | first :: rest =>
      a "tptp92-ast:list:tptp92ast-comma-parent-info:cons" [
        a "tptp92-ast:comma-parent-info:alt-1" [parent first],
        commaParents rest]

def parents : List String -> Pattern
  | [] => a "tptp92-ast:parents:alt-1"
  | first :: rest =>
      a "tptp92-ast:parents:alt-2" [
        a "tptp92-ast:parent-list:alt-1" [parent first, commaParents rest]]

def statusThm : Pattern :=
  let thmTerm :=
    a "tptp92-ast:general-term:alt-1" [
      a "tptp92-ast:general-data:alt-1" [atomicWord "thm"]]
  let argumentTerms :=
    a "tptp92-ast:general-terms:alt-1" [
      thmTerm,
      a "tptp92-ast:list:tptp92ast-comma-general-term:nil"]
  let statusTerm :=
    a "tptp92-ast:general-term:alt-1" [
      a "tptp92-ast:general-data:alt-2" [
        a "tptp92-ast:general-function:alt-1"
          [atomicWord "status", argumentTerms]]]
  a "tptp92-ast:useful-info:alt-1" [
    a "tptp92-ast:general-list:alt-2" [
      a "tptp92-ast:general-terms:alt-1" [
        statusTerm,
        a "tptp92-ast:list:tptp92ast-comma-general-term:nil"]]]

def inferenceAnnotations (rule : String) (parentNames : List String) : Pattern :=
  a "tptp92-ast:annotations:alt-1" [
    a "tptp92-ast:source:alt-1" [
      a "tptp92-ast:dag-source:alt-2" [
        a "tptp92-ast:inference-record:alt-1" [
          a "tptp92-ast:inference-rule:alt-1" [atomicWord rule],
          statusThm,
          parents parentNames]]],
    a "tptp92-ast:optional-info:alt-2"]

def annotated (formulaName roleName : String) (body annotations : Pattern) :
    Pattern :=
  a "tptp92-ast:cnf-annotated:alt-1"
    [name formulaName, role roleName, body, annotations]

def input (index : Nat) (formulaName roleName : String)
    (body annotations : Pattern) : Pattern :=
  encodeAnnotatedInput {
    occurrence := occurrence index
    payload := .cnf (annotated formulaName roleName body annotations)
    span := span index
  }

def derivationNodes : List Pattern -> Pattern
  | [] => a "tptp-semantic:derivation-nodes-nil"
  | first :: rest =>
      a "tptp-semantic:derivation-nodes-cons" [first, derivationNodes rest]

def derivationWith (firstRule : String)
    (firstParents : List String := ["p_or_q", "not_p"])
    (firstBody : Pattern := formula [positive "q"]) : Pattern :=
  a "tptp-semantic:derivation" [source, derivationNodes [
    input 0 "p_or_q" "axiom" (formula [positive "p", positive "q"])
      noAnnotations,
    input 1 "not_p" "axiom" (formula [negative "p"]) noAnnotations,
    input 2 "not_q" "axiom" (formula [negative "q"]) noAnnotations,
    input 3 "q" "plain" firstBody
      (inferenceAnnotations firstRule firstParents),
    input 4 "empty" "plain" (formula [])
      (inferenceAnnotations "resolution" ["q", "not_q"])
  ]]

def valid : Pattern := derivationWith "resolution"

def validLowering : LoweredRefutation where
  submission := {
    problem := {
      sourceDigest := "fixture"
      clauses := [
        { id := 0, name := "p_or_q", role := .axiom,
          literals := [.positive (atom "p"), .positive (atom "q")] },
        { id := 1, name := "not_p", role := .axiom,
          literals := [.negative (atom "p")] },
        { id := 2, name := "not_q", role := .axiom,
          literals := [.negative (atom "q")] }
      ]
    }
    nodes := [
      { name := "q", key := TptpGroundResolutionProblemAuthority.resolutionKey,
        parents := ["p_or_q", "not_p"], inferred := .clause [.positive (atom "q")],
        evidence := .reconstruct },
      { name := "empty", key := TptpGroundResolutionProblemAuthority.resolutionKey,
        parents := ["q", "not_q"], inferred := .clause [],
        evidence := .reconstruct }
    ]
    root := "empty"
    expected := .clause []
  }
  expectedEmpty := rfl

private def stringTypeIndex :
    Fin TptpOfficialAbstractSyntax.types.length := ⟨1, by decide⟩

private def stringTypeDeclaration : TypeDecl :=
  TptpOfficialAbstractSyntax.types.get stringTypeIndex

private theorem stringTypeDeclaration_shape :
    stringTypeDeclaration = { name := "String", carrier := .builtinString } := by
  rfl

private theorem stringTypeDeclaration_mem_language :
    List.Mem stringTypeDeclaration language.types :=
  List.IsPrefix.mem (List.get_mem _ stringTypeIndex) official_types_exact_prefix

private def sourceDigestRuleIndex : Fin addedTerms.length := ⟨0, by decide⟩
private def occurrenceRuleIndex : Fin addedTerms.length := ⟨1, by decide⟩
private def derivationNodesNilRuleIndex : Fin addedTerms.length := ⟨13, by decide⟩
private def derivationNodesConsRuleIndex : Fin addedTerms.length := ⟨14, by decide⟩

private def sourceDigestRule : GrammarRule :=
  addedTerms.get sourceDigestRuleIndex

private def occurrenceRule : GrammarRule :=
  addedTerms.get occurrenceRuleIndex

private def derivationNodesNilRule : GrammarRule :=
  addedTerms.get derivationNodesNilRuleIndex

private def derivationNodesConsRule : GrammarRule :=
  addedTerms.get derivationNodesConsRuleIndex

private theorem sourceDigestRule_shape : sourceDigestRule = {
    label := "tptp-semantic:source-digest"
    category := "TptpSemantic:source-digest"
    params := [.simple "value" (.base "String")]
    syntaxPattern := []
    evalPolicy? := none
  } := by rfl

private theorem occurrenceRule_shape : occurrenceRule = {
    label := "tptp-semantic:occurrence-id"
    category := "TptpSemantic:occurrence-id"
    params := [
      .simple "source" (.base "TptpSemantic:source-digest"),
      .simple "index" (.base "Integer")]
    syntaxPattern := []
    evalPolicy? := none
  } := by rfl

private theorem derivationNodesNilRule_shape : derivationNodesNilRule = {
    label := "tptp-semantic:derivation-nodes-nil"
    category := "TptpSemantic:derivation-nodes"
    params := []
    syntaxPattern := []
    evalPolicy? := none
  } := by rfl

private theorem derivationNodesConsRule_shape : derivationNodesConsRule = {
    label := "tptp-semantic:derivation-nodes-cons"
    category := "TptpSemantic:derivation-nodes"
    params := [
      .simple "first" (.base "TptpSemantic:annotated-input"),
      .simple "rest" (.base "TptpSemantic:derivation-nodes")]
    syntaxPattern := []
    evalPolicy? := none
  } := by rfl

private theorem cnfInputRule_literal : cnfInputRule = {
    label := "tptp-semantic:cnf-input"
    category := "TptpSemantic:annotated-input"
    params := [
      .simple "occurrence" (.base "TptpSemantic:occurrence-id"),
      .simple "formula" (.base "Tptp92Ast:cnf-annotated"),
      .simple "span" (.base "Tptp92Ast:source-span")]
    syntaxPattern := []
    evalPolicy? := none
  } := by rfl

private theorem derivationRule_literal : derivationRule = {
    label := "tptp-semantic:derivation"
    category := "TptpSemantic:derivation"
    params := [
      .simple "source" (.base "TptpSemantic:source-digest"),
      .simple "nodes" (.base "TptpSemantic:derivation-nodes")]
    syntaxPattern := []
    evalPolicy? := none
  } := by rfl

private theorem addedRule_mem_language (index : Fin addedTerms.length) :
    addedTerms.get index ∈ language.terms := by
  change addedTerms.get index ∈
    TptpOfficialAbstractSyntax.language.terms ++ addedTerms
  exact List.mem_append_right _ (List.get_mem _ index)

private theorem natAtomTyped (value : Nat) :
    HasType language WellSorted.FreeTypeContext.empty []
      (a (toString value)) (.base "Integer") := by
  apply HasType.builtinAtom
  refine ⟨TptpOfficialAbstractSyntax.integerTypeDeclaration,
    List.IsPrefix.mem
      TptpOfficialAbstractSyntax.integerTypeDeclaration_mem_language
      official_types_exact_prefix, ?_, ?_⟩
  · rw [TptpOfficialAbstractSyntax.integerTypeDeclaration_shape]
  · rw [TptpOfficialAbstractSyntax.integerTypeDeclaration_shape]
    simp [carrierAcceptsAtom, Nat.toInt?_repr]

private theorem stringAtomTyped (value : String) :
    HasType language WellSorted.FreeTypeContext.empty []
      (a value) (.base "String") := by
  apply HasType.builtinAtom
  refine ⟨stringTypeDeclaration, stringTypeDeclaration_mem_language, ?_, ?_⟩
  · rw [stringTypeDeclaration_shape]
  · rw [stringTypeDeclaration_shape]
    rfl

private theorem sourceDigestTyped (value : String) :
    HasType language WellSorted.FreeTypeContext.empty []
      (a "tptp-semantic:source-digest" [a value])
      (.base "TptpSemantic:source-digest") := by
  have argumentsTyped : ArgumentsHaveTypes language
      WellSorted.FreeTypeContext.empty [] [a value] sourceDigestRule.params := by
    rw [sourceDigestRule_shape]
    exact .cons (by trivial) rfl (stringAtomTyped value) .nil
  have typed := @HasType.constructor language WellSorted.FreeTypeContext.empty
    [] sourceDigestRule [a value]
    (addedRule_mem_language sourceDigestRuleIndex)
    (by
      rw [sourceDigestRule_shape]
      simp [WellSorted.UsesBareCollection])
    argumentsTyped
  simpa [sourceDigestRule_shape, a] using typed

private theorem occurrenceTyped (index : Nat) :
    HasType language WellSorted.FreeTypeContext.empty [] (occurrence index)
      (.base "TptpSemantic:occurrence-id") := by
  have argumentsTyped : ArgumentsHaveTypes language
      WellSorted.FreeTypeContext.empty []
      [source, a (toString index)] occurrenceRule.params := by
    rw [occurrenceRule_shape]
    exact .cons (by trivial) rfl (sourceDigestTyped "fixture")
      (.cons (by trivial) rfl (natAtomTyped index) .nil)
  have typed := @HasType.constructor language WellSorted.FreeTypeContext.empty
    [] occurrenceRule [source, a (toString index)]
    (addedRule_mem_language occurrenceRuleIndex)
    (by
      rw [occurrenceRule_shape]
      simp [WellSorted.UsesBareCollection])
    argumentsTyped
  simpa [occurrenceRule_shape, occurrence, source, a] using typed

private theorem sourceSpanTyped (start stop : Nat) :
    HasType language WellSorted.FreeTypeContext.empty []
      (a "tptp92-ast:source-span" [a (toString start), a (toString stop)])
      (.base "Tptp92Ast:source-span") := by
  have argumentsTyped : ArgumentsHaveTypes language
      WellSorted.FreeTypeContext.empty []
      [a (toString start), a (toString stop)]
      TptpOfficialAbstractSyntax.sourceSpanRule.params := by
    rw [TptpOfficialAbstractSyntax.sourceSpanRule_shape]
    exact .cons (by trivial) rfl (natAtomTyped start)
      (.cons (by trivial) rfl (natAtomTyped stop) .nil)
  have typed := HasType.constructor
    (List.IsPrefix.mem TptpOfficialAbstractSyntax.sourceSpanRule_mem_language
      official_terms_exact_prefix)
    (by
      rw [TptpOfficialAbstractSyntax.sourceSpanRule_shape]
      simp [WellSorted.UsesBareCollection])
    argumentsTyped
  simpa [TptpOfficialAbstractSyntax.sourceSpanRule_shape, a] using typed

private theorem canarySpanTyped (index : Nat) :
    HasType language WellSorted.FreeTypeContext.empty [] (span index)
      (.base "Tptp92Ast:source-span") := by
  simpa [span] using sourceSpanTyped (index * 10) (index * 10 + 9)

private theorem inputTyped (index : Nat) (formulaName roleName : String)
    (body annotations : Pattern)
    (annotatedTyped : HasType language WellSorted.FreeTypeContext.empty []
      (annotated formulaName roleName body annotations)
      (.base "Tptp92Ast:cnf-annotated")) :
    HasType language WellSorted.FreeTypeContext.empty []
      (input index formulaName roleName body annotations)
      (.base "TptpSemantic:annotated-input") := by
  have argumentsTyped : ArgumentsHaveTypes language
      WellSorted.FreeTypeContext.empty []
      [occurrence index, annotated formulaName roleName body annotations,
        span index] cnfInputRule.params := by
    rw [cnfInputRule_literal]
    exact .cons (by trivial) rfl (occurrenceTyped index)
      (.cons (by trivial) rfl annotatedTyped
        (.cons (by trivial) rfl (canarySpanTyped index) .nil))
  have typed := @HasType.constructor language WellSorted.FreeTypeContext.empty
    [] cnfInputRule
    [occurrence index, annotated formulaName roleName body annotations,
      span index]
    cnfInputRule_mem_language
    (by rw [cnfInputRule_literal]; simp [WellSorted.UsesBareCollection])
    argumentsTyped
  simpa [input, TptpOfficialSemanticCarrier.encodeAnnotatedInput, a,
    cnfInputRule_literal] using typed

private theorem derivationNodesTyped (nodes : List Pattern)
    (typedNodes : ∀ node ∈ nodes,
      HasType language WellSorted.FreeTypeContext.empty [] node
        (.base "TptpSemantic:annotated-input")) :
    HasType language WellSorted.FreeTypeContext.empty []
      (derivationNodes nodes) (.base "TptpSemantic:derivation-nodes") := by
  induction nodes with
  | nil =>
      have argumentsTyped : ArgumentsHaveTypes language
          WellSorted.FreeTypeContext.empty [] []
          derivationNodesNilRule.params := by
        rw [derivationNodesNilRule_shape]
        exact .nil
      have typed := @HasType.constructor language
        WellSorted.FreeTypeContext.empty [] derivationNodesNilRule []
        (addedRule_mem_language derivationNodesNilRuleIndex)
        (by
          rw [derivationNodesNilRule_shape]
          simp [WellSorted.UsesBareCollection])
        argumentsTyped
      simpa [derivationNodes, derivationNodesNilRule_shape, a] using typed
  | cons node nodes inductionHypothesis =>
      have restTyped := inductionHypothesis
        (fun other membership => typedNodes other (by simp [membership]))
      have argumentsTyped : ArgumentsHaveTypes language
          WellSorted.FreeTypeContext.empty [] [node, derivationNodes nodes]
          derivationNodesConsRule.params := by
        rw [derivationNodesConsRule_shape]
        exact .cons (by trivial) rfl (typedNodes node (by simp))
          (.cons (by trivial) rfl restTyped .nil)
      have typed := @HasType.constructor language
        WellSorted.FreeTypeContext.empty [] derivationNodesConsRule
        [node, derivationNodes nodes]
        (addedRule_mem_language derivationNodesConsRuleIndex)
        (by
          rw [derivationNodesConsRule_shape]
          simp [WellSorted.UsesBareCollection])
        argumentsTyped
      simpa [derivationNodes, derivationNodesConsRule_shape, a] using typed

theorem derivationWith_is_admitted
    (firstRule : String) (firstParents : List String) (firstBody : Pattern)
    (annotated3 : HasType language WellSorted.FreeTypeContext.empty []
      (annotated "q" "plain" firstBody
        (inferenceAnnotations firstRule firstParents))
      (.base "Tptp92Ast:cnf-annotated"))
    (object : WellSorted.isObjectPattern
      (derivationWith firstRule firstParents firstBody) = true) :
    checkHasType language WellSorted.FreeTypeContext.empty []
      (derivationWith firstRule firstParents firstBody)
      (.base "TptpSemantic:derivation") = true := by
  have annotated0 : HasType language WellSorted.FreeTypeContext.empty []
      (annotated "p_or_q" "axiom"
        (formula [positive "p", positive "q"]) noAnnotations)
      (.base "Tptp92Ast:cnf-annotated") :=
    checkHasType_sound (by decide +kernel)
  have annotated1 : HasType language WellSorted.FreeTypeContext.empty []
      (annotated "not_p" "axiom" (formula [negative "p"]) noAnnotations)
      (.base "Tptp92Ast:cnf-annotated") :=
    checkHasType_sound (by decide +kernel)
  have annotated2 : HasType language WellSorted.FreeTypeContext.empty []
      (annotated "not_q" "axiom" (formula [negative "q"]) noAnnotations)
      (.base "Tptp92Ast:cnf-annotated") :=
    checkHasType_sound (by decide +kernel)
  have annotated4 : HasType language WellSorted.FreeTypeContext.empty []
      (annotated "empty" "plain" (formula [])
        (inferenceAnnotations "resolution" ["q", "not_q"]))
      (.base "Tptp92Ast:cnf-annotated") :=
    checkHasType_sound (by decide +kernel)
  have node0 := inputTyped 0 "p_or_q" "axiom"
    (formula [positive "p", positive "q"]) noAnnotations annotated0
  have node1 := inputTyped 1 "not_p" "axiom"
    (formula [negative "p"]) noAnnotations annotated1
  have node2 := inputTyped 2 "not_q" "axiom"
    (formula [negative "q"]) noAnnotations annotated2
  have node3 := inputTyped 3 "q" "plain" firstBody
    (inferenceAnnotations firstRule firstParents) annotated3
  have node4 := inputTyped 4 "empty" "plain" (formula [])
    (inferenceAnnotations "resolution" ["q", "not_q"]) annotated4
  have nodesTyped := derivationNodesTyped [
    input 0 "p_or_q" "axiom" (formula [positive "p", positive "q"])
      noAnnotations,
    input 1 "not_p" "axiom" (formula [negative "p"]) noAnnotations,
    input 2 "not_q" "axiom" (formula [negative "q"]) noAnnotations,
    input 3 "q" "plain" firstBody
      (inferenceAnnotations firstRule firstParents),
    input 4 "empty" "plain" (formula [])
      (inferenceAnnotations "resolution" ["q", "not_q"])] (by
        intro node membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        rcases membership with h | h | h | h | h
        · subst node; exact node0
        · subst node; exact node1
        · subst node; exact node2
        · subst node; exact node3
        · subst node; exact node4)
  have argumentsTyped : ArgumentsHaveTypes language
      WellSorted.FreeTypeContext.empty []
      [source, derivationNodes [
        input 0 "p_or_q" "axiom" (formula [positive "p", positive "q"])
          noAnnotations,
        input 1 "not_p" "axiom" (formula [negative "p"]) noAnnotations,
        input 2 "not_q" "axiom" (formula [negative "q"]) noAnnotations,
        input 3 "q" "plain" firstBody
          (inferenceAnnotations firstRule firstParents),
        input 4 "empty" "plain" (formula [])
          (inferenceAnnotations "resolution" ["q", "not_q"])]]
      derivationRule.params := by
    rw [derivationRule_literal]
    exact .cons (by trivial) rfl (sourceDigestTyped "fixture")
      (.cons (by trivial) rfl nodesTyped .nil)
  have typed := @HasType.constructor language WellSorted.FreeTypeContext.empty
    [] derivationRule
    [source, derivationNodes [
      input 0 "p_or_q" "axiom" (formula [positive "p", positive "q"])
        noAnnotations,
      input 1 "not_p" "axiom" (formula [negative "p"]) noAnnotations,
      input 2 "not_q" "axiom" (formula [negative "q"]) noAnnotations,
      input 3 "q" "plain" firstBody
        (inferenceAnnotations firstRule firstParents),
      input 4 "empty" "plain" (formula [])
        (inferenceAnnotations "resolution" ["q", "not_q"])]]
    derivationRule_mem_language
    (by rw [derivationRule_literal]; simp [WellSorted.UsesBareCollection])
    argumentsTyped
  apply checkHasType_complete_of_object
  · simpa [derivationWith, derivationRule_literal, a] using typed
  · exact object

theorem valid_is_admitted :
    checkHasType language WellSorted.FreeTypeContext.empty [] valid
      (.base "TptpSemantic:derivation") = true := by
  apply derivationWith_is_admitted
  · exact checkHasType_sound (by decide +kernel)
  · decide +kernel

theorem valid_structural_admission_succeeds :
    (TptpOfficialDerivationAdmission.admit? valid).isSome := by
  simp [TptpOfficialDerivationAdmission.admit?, valid_is_admitted]
  rfl

theorem valid_lowering_exact : lowerRefutation? valid = some validLowering := by
  rfl

theorem valid_lowering_succeeds : (lowerRefutation? valid).isSome = true := by
  rw [valid_lowering_exact]
  rfl

theorem status_thm_decodes : decodeUniqueStatus? statusThm = some .thm := by
  rfl

theorem resolution_record_decodes :
    decodeInference? (inferenceAnnotations "resolution"
      ["p_or_q", "not_p"]) =
      some { rule := "resolution", parents := ["p_or_q", "not_p"] } := by
  rfl

def missingParent : Pattern :=
  derivationWith "resolution" ["missing", "not_p"]

def unknownRule : Pattern := derivationWith "magic"

def variableAtom (predicate variableName : String) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-1" [
    a "tptp92-ast:fof-plain-atomic-formula:alt-1" [
      a "tptp92-ast:fof-plain-term:alt-2" [
        a "tptp92-ast:functor:alt-1" [atomicWord predicate],
        a "tptp92-ast:fof-arguments:alt-1" [
          a "tptp92-ast:fof-term:alt-2" [
            a "tptp92-ast:variable:alt-1" [
              a "tptp92-ast:token:upper-word" [a variableName]]]]]]]

def nonground : Pattern :=
  derivationWith "resolution" ["p_or_q", "not_p"]
    (formula [positive "q",
      a "tptp92-ast:cnf-literal:alt-1" [variableAtom "r" "X"]])

theorem variable_atom_not_ground :
    isGroundOfficial (variableAtom "r" "X") = false := by
  rfl

end Canary

#print axioms VerifiedRefutation.objective
#print axioms VerifiedRefutation.unsatisfiable
#print axioms Canary.status_thm_decodes
#print axioms Canary.resolution_record_decodes
#print axioms Canary.valid_is_admitted
#print axioms Canary.valid_structural_admission_succeeds
#print axioms Canary.valid_lowering_exact
#print axioms Canary.valid_lowering_succeeds
#print axioms Canary.variable_atom_not_ground

end Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionVerifier
