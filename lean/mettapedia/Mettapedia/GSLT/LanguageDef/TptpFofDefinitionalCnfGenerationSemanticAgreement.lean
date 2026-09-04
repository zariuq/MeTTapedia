import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemanticAgreement

/-!
# Semantic agreement of authored definitional CNF generation

Typed definitionally named outputs induce executions of the authored CNF
LanguageDef.  An explicit alignment witness ties every definition row to the
introduced-predicate row carrying the same id and the enclosing variable
arity.  The final theorem identifies the engine result with the independent
three-clause semantics exactly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationSemanticAgreement

open LO FirstOrder
open scoped LO.FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemantics

namespace Semantic

open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationLanguageDef
open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationAgreement

/-- Pointwise evidence that the two naming ledgers describe the same fresh
predicates and that each predicate sees the complete enclosing environment. -/
inductive LedgerAlignment (depth : Nat) :
    List (Definition depth) → List IntroducedPredicate → Type
  | nil : LedgerAlignment depth [] []
  | cons (head : Definition depth) {definitions : List (Definition depth)}
      {introduced : List IntroducedPredicate}
      (tail : LedgerAlignment depth definitions introduced) :
      LedgerAlignment depth (head :: definitions)
        ({ id := head.id, arity := depth } :: introduced)

noncomputable def LedgerAlignment.append {depth : Nat}
    {leftDefinitions rightDefinitions : List (Definition depth)}
    {leftIntroduced rightIntroduced : List IntroducedPredicate}
    (left : LedgerAlignment depth leftDefinitions leftIntroduced)
    (right : LedgerAlignment depth rightDefinitions rightIntroduced) :
    LedgerAlignment depth (leftDefinitions ++ rightDefinitions)
      (leftIntroduced ++ rightIntroduced) := by
  induction left with
  | nil => exact right
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis

noncomputable def nameFrom_ledgerAlignment {depth : Nat}
    (source : Source.Formula depth) (quantifierFree : QuantifierFree source)
    (frontier : Nat) :
    LedgerAlignment depth
      (nameFrom source quantifierFree frontier).definitions
      (nameFrom source quantifierFree frontier).introduced := by
  induction source generalizing frontier with
  | verum =>
      simpa [nameFrom, leafOutput] using
        (LedgerAlignment.nil (depth := _))
  | falsum =>
      simpa [nameFrom, leafOutput] using
        (LedgerAlignment.nil (depth := _))
  | rel =>
      simpa [nameFrom, leafOutput] using
        (LedgerAlignment.nil (depth := _))
  | nrel =>
      simpa [nameFrom, leafOutput] using
        (LedgerAlignment.nil (depth := _))
  | and left right leftHypothesis rightHypothesis =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let current : Definition _ := {
        id := rightOutput.next
        source := .and left right
        connective := .and
        left := leftOutput.root
        right := rightOutput.root
      }
      have aligned := (LedgerAlignment.append
        (leftHypothesis quantifierFree.1 frontier)
        (rightHypothesis quantifierFree.2 leftOutput.next)).append
          (.cons current .nil)
      simpa [nameFrom, leftOutput, rightOutput, current] using aligned
  | or left right leftHypothesis rightHypothesis =>
      let leftOutput := nameFrom left quantifierFree.1 frontier
      let rightOutput := nameFrom right quantifierFree.2 leftOutput.next
      let current : Definition _ := {
        id := rightOutput.next
        source := .or left right
        connective := .or
        left := leftOutput.root
        right := rightOutput.root
      }
      have aligned := (LedgerAlignment.append
        (leftHypothesis quantifierFree.1 frontier)
        (rightHypothesis quantifierFree.2 leftOutput.next)).append
          (.cons current .nil)
      simpa [nameFrom, leftOutput, rightOutput, current] using aligned
  | all body => exact False.elim quantifierFree
  | ex body => exact False.elim quantifierFree

def variableTerms : Nat → Nat → Pattern
  | 0, _ => TptpFofSkolemLanguageDef.termsNil
  | remaining + 1, next =>
      TptpFofSkolemLanguageDef.termsCons
        (TptpFofSkolemLanguageDef.termVariable
          (TptpResolvedFofLanguageDef.encodeNatIndex next))
        (variableTerms remaining (next + 1))

@[simp] theorem encodeNatIndex_zero :
    TptpResolvedFofLanguageDef.encodeNatIndex 0 = indexZero := rfl

@[simp] theorem encodeNatIndex_succ (index : Nat) :
    TptpResolvedFofLanguageDef.encodeNatIndex (index + 1) =
      indexSucc (TptpResolvedFofLanguageDef.encodeNatIndex index) := rfl

@[simp] theorem generation_indexZero_eq_skolem :
    indexZero = TptpFofSkolemTermLanguageDef.indexZero := rfl

@[simp] theorem generation_indexSucc_eq_skolem (index : Pattern) :
    indexSucc index = TptpFofSkolemTermLanguageDef.indexSucc index := rfl

def variablesDerivation : (remaining next : Nat) →
    Derivation
      (variablesRequest
        (TptpResolvedFofLanguageDef.encodeNatIndex remaining)
        (TptpResolvedFofLanguageDef.encodeNatIndex next))
      (variablesResult
        (TptpResolvedFofLanguageDef.encodeNatIndex remaining)
        (TptpResolvedFofLanguageDef.encodeNatIndex next)
        (variableTerms remaining next))
  | 0, next => by
      simpa [variableTerms, encodeNatIndex_zero,
        generation_indexZero_eq_skolem] using
        Derivation.variablesZero
          (TptpResolvedFofLanguageDef.encodeNatIndex next)
  | remaining + 1, next => by
      simpa [variableTerms, encodeNatIndex_succ,
        generation_indexSucc_eq_skolem] using
        Derivation.variablesSucc (variablesDerivation remaining (next + 1))

theorem variableTerms_eq_naming (remaining next : Nat) :
    variableTerms remaining next =
      TptpFofDefinitionalNamingSemanticAgreement.Operational.variableTerms
        remaining next := by
  induction remaining generalizing next with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      simp only [variableTerms,
        TptpFofDefinitionalNamingSemanticAgreement.Operational.variableTerms]
      rw [inductionHypothesis]

theorem variableTerms_zero_exact (depth : Nat) :
    variableTerms depth 0 =
      TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms
        (fun index : Fin depth =>
          (LO.FirstOrder.Semiterm.bvar index : Term depth)) := by
  rw [variableTerms_eq_naming]
  exact
    TptpFofDefinitionalNamingSemanticAgreement.Operational.variableTerms_zero_exact
      depth

@[simp] theorem encode_definedReference_exact (depth id : Nat) :
    TptpFofDefinitionalCnfLanguageDef.encodeReference
        (definedReference depth id) =
      TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
        (TptpResolvedFofLanguageDef.encodeNatIndex id)
        (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms
          (fun index : Fin depth =>
            (LO.FirstOrder.Semiterm.bvar index : Term depth))) := by
  rfl

@[simp] theorem encode_negate_definedReference_exact (depth id : Nat) :
    TptpFofDefinitionalCnfLanguageDef.encodeReference
        (TptpFofDefinitionalCnfSemantics.negate
          (definedReference depth id)) =
      TptpFofDefinitionalCnfLanguageDef.refDefinedNegative
        (TptpResolvedFofLanguageDef.encodeNatIndex id)
        (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms
          (fun index : Fin depth =>
            (LO.FirstOrder.Semiterm.bvar index : Term depth))) := by
  rfl

noncomputable def negateDerivation {depth : Nat} :
    (reference : Reference depth) →
    Derivation
      (negateRequest
        (TptpFofDefinitionalCnfLanguageDef.encodeReference reference))
      (negateResult
        (TptpFofDefinitionalCnfLanguageDef.encodeReference reference)
        (TptpFofDefinitionalCnfLanguageDef.encodeReference
          (TptpFofDefinitionalCnfSemantics.negate reference)))
  | .verum => by
      simpa [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfSemantics.negate] using
        Derivation.negateVerum
  | .falsum => by
      simpa [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfSemantics.negate] using
        Derivation.negateFalsum
  | .positive (.original (.predicate predicate)) arguments => by
      simpa [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfSemantics.negate] using
        Derivation.negateOriginalPositive
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms arguments)
  | .positive (.original .equality) arguments => by
      simpa [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfSemantics.negate] using
        Derivation.negateEqual
          (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm (arguments 0))
          (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm (arguments 1))
  | .positive (.defined id) arguments => by
      simpa [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfSemantics.negate] using
        Derivation.negateDefinedPositive
          (TptpResolvedFofLanguageDef.encodeNatIndex id)
          (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms arguments)
  | .negative (.original (.predicate predicate)) arguments => by
      simpa [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfSemantics.negate] using
        Derivation.negateOriginalNegative
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms arguments)
  | .negative (.original .equality) arguments => by
      simpa [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfSemantics.negate] using
        Derivation.negateNotEqual
          (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm (arguments 0))
          (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm (arguments 1))
  | .negative (.defined id) arguments => by
      simpa [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfSemantics.negate] using
        Derivation.negateDefinedNegative
          (TptpResolvedFofLanguageDef.encodeNatIndex id)
          (TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms arguments)

noncomputable def clausesDerivation {depth : Nat}
    {definitions : List (Definition depth)}
    {introduced : List IntroducedPredicate}
    (alignment : LedgerAlignment depth definitions introduced)
    (quantifierFree : ∀ definition ∈ definitions,
      QuantifierFree definition.source)
    (root : Reference depth) :
    Derivation
      (clausesRequest
        (TptpFofDefinitionalCnfLanguageDef.encodeReference root)
        (TptpFofDefinitionalCnfLanguageDef.encodeDefinitions
          definitions quantifierFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeIntroduced introduced))
      (clausesResult
        (TptpFofDefinitionalCnfLanguageDef.encodeReference root)
        (TptpFofDefinitionalCnfLanguageDef.encodeDefinitions
          definitions quantifierFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeIntroduced introduced)
        (TptpFofDefinitionalCnfLanguageDef.encodeClauses
          (TptpFofDefinitionalCnfSemantics.clausesForDefinitions definitions ++
            [[root]]))) := by
  induction alignment with
  | nil =>
      simpa [TptpFofDefinitionalCnfLanguageDef.encodeDefinitions,
        TptpFofDefinitionalCnfLanguageDef.encodeIntroduced,
        TptpFofDefinitionalCnfLanguageDef.encodeClauses,
        TptpFofDefinitionalCnfLanguageDef.encodeClause,
        TptpFofDefinitionalCnfSemantics.clausesForDefinitions,
        unitClause] using
        Derivation.clausesNil
          (TptpFofDefinitionalCnfLanguageDef.encodeReference root)
  | cons head tail alignmentHypothesis =>
      let tailQuantifierFree := fun definition membership =>
        quantifierFree definition (List.mem_cons_of_mem head membership)
      have tailDerivation := alignmentHypothesis tailQuantifierFree
      cases head with
      | mk id source connective left right =>
          cases connective with
          | and =>
              let headQuantifierFree : QuantifierFree source :=
                quantifierFree
                  { id := id, source := source, connective := .and,
                    left := left, right := right }
                  (by simp)
              simpa [TptpFofDefinitionalCnfLanguageDef.encodeDefinitions,
                TptpFofDefinitionalCnfLanguageDef.encodeDefinition,
                TptpFofDefinitionalCnfLanguageDef.encodeIntroduced,
                TptpFofDefinitionalCnfLanguageDef.encodeIntroducedPredicate,
                TptpFofDefinitionalCnfLanguageDef.encodeClauses,
                TptpFofDefinitionalCnfLanguageDef.encodeClause,
                TptpFofDefinitionalCnfSemantics.clausesForDefinitions,
                TptpFofDefinitionalCnfSemantics.clausesForDefinition,
                variableTerms_zero_exact, encode_definedReference_exact,
                encode_negate_definedReference_exact,
                unitClause, binaryClause, ternaryClause, prependThree] using
                Derivation.clausesAnd
                  (id := TptpResolvedFofLanguageDef.encodeNatIndex id)
                  (source := TptpFofSkolemLanguageDef.encodeFormula source
                    headQuantifierFree.existentialFree)
                  (arity := TptpResolvedFofLanguageDef.encodeNatIndex depth)
                  (arguments := variableTerms depth 0)
                  (variablesDerivation depth 0)
                  (negateDerivation left) (negateDerivation right)
                  tailDerivation
          | or =>
              let headQuantifierFree : QuantifierFree source :=
                quantifierFree
                  { id := id, source := source, connective := .or,
                    left := left, right := right }
                  (by simp)
              simpa [TptpFofDefinitionalCnfLanguageDef.encodeDefinitions,
                TptpFofDefinitionalCnfLanguageDef.encodeDefinition,
                TptpFofDefinitionalCnfLanguageDef.encodeIntroduced,
                TptpFofDefinitionalCnfLanguageDef.encodeIntroducedPredicate,
                TptpFofDefinitionalCnfLanguageDef.encodeClauses,
                TptpFofDefinitionalCnfLanguageDef.encodeClause,
                TptpFofDefinitionalCnfSemantics.clausesForDefinitions,
                TptpFofDefinitionalCnfSemantics.clausesForDefinition,
                variableTerms_zero_exact, encode_definedReference_exact,
                encode_negate_definedReference_exact,
                unitClause, binaryClause, ternaryClause, prependThree] using
                Derivation.clausesOr
                  (id := TptpResolvedFofLanguageDef.encodeNatIndex id)
                  (source := TptpFofSkolemLanguageDef.encodeFormula source
                    headQuantifierFree.existentialFree)
                  (arity := TptpResolvedFofLanguageDef.encodeNatIndex depth)
                  (arguments := variableTerms depth 0)
                  (variablesDerivation depth 0)
                  (negateDerivation left) (negateDerivation right)
                  tailDerivation

noncomputable def generateDerivation {depth : Nat}
    (output : Output depth)
    (alignment : LedgerAlignment depth output.definitions output.introduced)
    (quantifierFree : ∀ definition ∈ output.definitions,
      QuantifierFree definition.source) :
    Derivation
      (generateRequest
        (TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput
          output quantifierFree))
      (generateResult
        (TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput
          output quantifierFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput
          output quantifierFree)) := by
  simpa [TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput,
    TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput,
    TptpFofDefinitionalCnfSemantics.clausesForOutput] using
    Derivation.generate (clausesDerivation alignment quantifierFree output.root)

theorem rewriteAt_generate_exact {depth : Nat}
    (output : Output depth)
    (alignment : LedgerAlignment depth output.definitions output.introduced)
    (quantifierFree : ∀ definition ∈ output.definitions,
      QuantifierFree definition.source)
    (fuel : Nat)
    (enough : (generateDerivation output alignment quantifierFree).height ≤ fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
      (generateRequest
        (TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput
          output quantifierFree)) =
      [generateResult
        (TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput
          output quantifierFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput
          output quantifierFree)] :=
  (generateDerivation output alignment quantifierFree).rewriteAt_exact fuel enough

theorem generate_no_invention {depth : Nat}
    (output : Output depth)
    (alignment : LedgerAlignment depth output.definitions output.introduced)
    (quantifierFree : ∀ definition ∈ output.definitions,
      QuantifierFree definition.source)
    (fuel : Nat)
    (enough : (generateDerivation output alignment quantifierFree).height ≤ fuel)
    (invented : Pattern)
    (membership : invented ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
      (generateRequest
        (TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput
          output quantifierFree))) :
    invented = generateResult
      (TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput
        output quantifierFree)
      (TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput
        output quantifierFree) :=
  (generateDerivation output alignment quantifierFree).no_invention
    fuel enough membership

namespace Canary

open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemantics.Canary

def output : Output 0 := nameFrom source source_quantifierFree 7

noncomputable def alignment :
    LedgerAlignment 0 output.definitions output.introduced :=
  nameFrom_ledgerAlignment source source_quantifierFree 7

def outputQuantifierFree : ∀ definition ∈ output.definitions,
    QuantifierFree definition.source :=
  nameFrom_definition_sources_quantifierFree source source_quantifierFree 7

theorem output_has_seven_clauses :
    (TptpFofDefinitionalCnfSemantics.clausesForOutput output).length = 7 := by
  simpa [output] using TptpFofDefinitionalCnfSemantics.Canary.nested_source_has_seven_clauses

theorem output_rewrites_to_one_canonical_cnf :
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language
      (generateDerivation output alignment outputQuantifierFree).height
      (generateRequest
        (TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput output
          outputQuantifierFree))).length = 1 := by
  rw [rewriteAt_generate_exact output alignment outputQuantifierFree
    (generateDerivation output alignment outputQuantifierFree).height
    (Nat.le_refl _)]
  simp

end Canary

#print axioms nameFrom_ledgerAlignment
#print axioms rewriteAt_generate_exact
#print axioms generate_no_invention
#print axioms Canary.output_rewrites_to_one_canonical_cnf

end Semantic

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationSemanticAgreement
