import Mettapedia.GSLT.LanguageDef.TptpOfficialFofClausificationBatchAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofCnfNameAllocationAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationReadiness
import Mathlib.Data.String.Lemmas

/-!
# Official FOF clausification through official CNF serialization

This module constructs the finite lexical plan from the allocation frontiers
owned by the semantic pipeline itself.  Clause, bound-variable, Skolem and
definition names are therefore consequences of source-derived bounds, not
unrelated witnesses supplied to the serializer.  Admitting every identity
strictly below a frontier also gives reserved identities their canonical
lexical representation without pretending that they were freshly introduced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofCnfSerializationPipelineAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open TptpFofCnfOfficialSerializationPlan
open TptpOfficialFofClausificationBatchAgreement

def indexedLexeme (stem : String) (marker : Char) (identity : Nat) : String :=
  stem ++ String.replicate identity marker

theorem indexedLexeme_injective (stem : String) (marker : Char) :
    Function.Injective (indexedLexeme stem marker) := by
  intro left right equality
  have lengths := congrArg String.length equality
  simpa [indexedLexeme] using lengths

private theorem planIndex_injective : Function.Injective index := by
  intro left right equality
  exact TptpFofClausificationBatchLanguageDef.encodeNatIndex_injective equality

private theorem quotedName_injective : Function.Injective quotedName := by
  intro left right equality
  simpa [quotedName, quotedAtomicWord, a] using equality

private theorem quotedFunctor_injective :
    Function.Injective quotedFunctor := by
  intro left right equality
  simpa [quotedFunctor, quotedAtomicWord, a] using equality

private theorem variableAst_injective : Function.Injective variableAst := by
  intro left right equality
  simpa [variableAst, a] using equality

def clauseName (identity : Nat) : Pattern :=
  quotedName (indexedLexeme "cnf_" 'c' identity)

def variableName (identity : Nat) : Pattern :=
  variableAst (indexedLexeme "X" 'x' identity)

def skolemFunctor (identity : Nat) : Pattern :=
  quotedFunctor (indexedLexeme "skolem_" 's' identity)

def definitionFunctor (identity : Nat) : Pattern :=
  quotedFunctor (indexedLexeme "definition_" 'd' identity)

theorem clauseName_injective : Function.Injective clauseName :=
  quotedName_injective.comp (indexedLexeme_injective "cnf_" 'c')

theorem variableName_injective : Function.Injective variableName :=
  variableAst_injective.comp (indexedLexeme_injective "X" 'x')

theorem skolemFunctor_injective : Function.Injective skolemFunctor :=
  quotedFunctor_injective.comp (indexedLexeme_injective "skolem_" 's')

theorem definitionFunctor_injective : Function.Injective definitionFunctor :=
  quotedFunctor_injective.comp
    (indexedLexeme_injective "definition_" 'd')

theorem skolemFunctor_ne_definitionFunctor (left right : Nat) :
    skolemFunctor left ≠ definitionFunctor right := by
  intro equality
  have lexemes := quotedFunctor_injective equality
  have heads := congrArg (fun value : String => value.toList.head?) lexemes
  simp [indexedLexeme] at heads

def tableFor (identities : List Nat) (target : Nat -> Pattern) : Table :=
  identities.map fun identity =>
    { source := index identity, target := target identity }

@[simp]
theorem tableFor_sourceKeys (identities : List Nat)
    (target : Nat -> Pattern) :
    (tableFor identities target).sourceKeys = identities.map index := by
  simp [tableFor, Table.sourceKeys]

@[simp]
theorem tableFor_targets (identities : List Nat) (target : Nat -> Pattern) :
    (tableFor identities target).targets = identities.map target := by
  simp [tableFor, Table.targets]

theorem tableFor_lookup_of_mem (identities : List Nat)
    (target : Nat -> Pattern) (identity : Nat)
    (membership : identity ∈ identities) :
    (tableFor identities target).lookup? (index identity) =
      some (target identity) := by
  induction identities with
  | nil => contradiction
  | cons head tail inductionHypothesis =>
      by_cases current : identity = head
      · subst head
        simp [tableFor, Table.lookup?]
      · have tailMembership : identity ∈ tail := by
          simpa [current] using membership
        simp only [tableFor, List.map_cons, Table.lookup?, List.find?_cons]
        have unequal : (index head == index identity) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro equality
          exact current (planIndex_injective equality).symm
        rw [unequal]
        exact inductionHypothesis tailMembership

theorem tableFor_validFor (identities : List Nat) (target : Nat -> Pattern)
    (targetSort : String) (identitiesNodup : identities.Nodup)
    (targetInjective : Function.Injective target)
    (targetInhabits : forall identity,
      inhabits TptpOfficialAbstractSyntax.language targetSort
        (target identity) = true) :
    (tableFor identities target).validFor targetSort = true := by
  have sourceKeysNodup :
      (tableFor identities target).sourceKeys.Nodup := by
    rw [tableFor_sourceKeys]
    exact identitiesNodup.map planIndex_injective
  have targetsNodup : (tableFor identities target).targets.Nodup := by
    rw [tableFor_targets]
    exact identitiesNodup.map targetInjective
  unfold Table.validFor
  simp only [Bool.and_eq_true]
  refine ⟨⟨decide_eq_true_eq.mpr sourceKeysNodup,
    decide_eq_true_eq.mpr targetsNodup⟩, ?_⟩
  apply List.all_eq_true.mpr
  intro row membership
  obtain ⟨identity, _, rfl⟩ := List.mem_map.mp membership
  rw [Bool.and_eq_true]
  exact ⟨index_inhabits identity, targetInhabits identity⟩

theorem skolemDefinitionTargets_disjoint
    (skolemIds definitionIds : List Nat) :
    targetsDisjoint (tableFor skolemIds skolemFunctor)
      (tableFor definitionIds definitionFunctor) = true := by
  unfold targetsDisjoint
  apply List.all_eq_true.mpr
  intro target targetMembership
  rw [tableFor_targets] at targetMembership
  obtain ⟨skolemId, _, rfl⟩ := List.mem_map.mp targetMembership
  rw [Bool.not_eq_true_eq_eq_false, List.contains_eq_mem,
    decide_eq_false_iff_not]
  intro definitionMembership
  rw [tableFor_targets] at definitionMembership
  obtain ⟨definitionId, _, equality⟩ := List.mem_map.mp definitionMembership
  exact skolemFunctor_ne_definitionFunctor skolemId definitionId equality.symm

def generatedLexicalPlan (variableDepth firstClause clauseCount : Nat)
    (skolemIds definitionIds : List Nat) :
    TptpFofCnfOfficialSerializationPlan.Plan where
  clauseNames :=
    tableFor (List.range' firstClause clauseCount) clauseName
  variableNames := tableFor (List.range variableDepth) variableName
  skolemFunctors := tableFor skolemIds skolemFunctor
  definitionFunctors := tableFor definitionIds definitionFunctor

theorem generatedPlan_valid (variableDepth firstClause clauseCount : Nat)
    (skolemIds definitionIds : List Nat)
    (skolemIdsNodup : skolemIds.Nodup)
    (definitionIdsNodup : definitionIds.Nodup) :
    (generatedLexicalPlan variableDepth firstClause clauseCount skolemIds
      definitionIds).valid = true := by
  unfold generatedLexicalPlan TptpFofCnfOfficialSerializationPlan.Plan.valid
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact tableFor_validFor _ _ _ List.nodup_range' clauseName_injective
      (fun identity => quotedName_inhabits _)
  · exact tableFor_validFor _ _ _ List.nodup_range variableName_injective
      (fun identity => variableAst_inhabits _)
  · exact tableFor_validFor _ _ _ skolemIdsNodup skolemFunctor_injective
      (fun identity => quotedFunctor_inhabits _)
  · exact tableFor_validFor _ _ _ definitionIdsNodup
      definitionFunctor_injective
      (fun identity => quotedFunctor_inhabits _)
  · exact skolemDefinitionTargets_disjoint skolemIds definitionIds

noncomputable def batchGeneratedPlan (input : BatchInput)
    (firstClause : Nat) : TptpFofCnfOfficialSerializationPlan.Plan :=
  generatedLexicalPlan input.namingEvidence.opened.depth firstClause
    (TptpFofDefinitionalCnfSemantics.clausesForOutput
      input.namedOutput).length
    (List.range input.skolemOutput.next)
    (List.range input.namedOutput.next)

theorem batchGeneratedPlan_valid (input : BatchInput)
    (firstClause : Nat) :
    (batchGeneratedPlan input firstClause).valid = true := by
  apply generatedPlan_valid
  · exact List.nodup_range
  · exact List.nodup_range

theorem batchGeneratedPlan_coverage (input : BatchInput)
    (firstClause : Nat) :
    TptpFofCnfOfficialSerializationReadiness.Coverage
      (batchGeneratedPlan input firstClause)
      input.namingEvidence.opened.depth input.skolemOutput.next
      input.namedOutput.next := by
  constructor
  · intro identity
    refine ⟨variableName identity.val, ?_⟩
    apply tableFor_lookup_of_mem
    exact List.mem_range.mpr identity.isLt
  · intro identity bounded
    refine ⟨skolemFunctor identity, ?_⟩
    apply tableFor_lookup_of_mem
    exact List.mem_range.mpr bounded
  · intro identity bounded
    refine ⟨definitionFunctor identity, ?_⟩
    apply tableFor_lookup_of_mem
    exact List.mem_range.mpr bounded

/-! ## Exact batch-to-allocation boundary -/

theorem encodeSourceEntries_encodedClauseEntriesFrom
    (occurrence : TptpFofClausificationBatchLanguageDef.SourceOccurrence)
    (localIndex : Nat) {depth : Nat}
    (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)) :
    TptpFofCnfNameAllocationAgreement.Allocated.encodeSourceEntries
        (TptpFofClausificationBatchLanguageDef.encodedClauseEntriesFrom
          occurrence localIndex clauses) =
      TptpFofClausificationBatchLanguageDef.encodeClauseEntriesFrom
        occurrence localIndex clauses := by
  induction clauses generalizing localIndex with
  | nil => rfl
  | cons clause clauses inductionHypothesis =>
      simp only [
        TptpFofClausificationBatchLanguageDef.encodedClauseEntriesFrom,
        TptpFofClausificationBatchLanguageDef.encodeClauseEntriesFrom,
        TptpFofCnfNameAllocationAgreement.Allocated.encodeSourceEntries,
        TptpFofClausificationBatchLanguageDef.encodeClauseEntry,
        TptpFofCnfNameAllocationLanguageDef.batchEntriesCons,
        TptpFofCnfNameAllocationLanguageDef.batchClauseEntry,
        TptpFofCnfNameAllocationLanguageDef.a]
      rw [inductionHypothesis]
      rfl

noncomputable def batchClauses (input : BatchInput) :=
  TptpFofDefinitionalCnfSemantics.clausesForOutput input.namedOutput

def BatchSerializationReady (input : BatchInput) : Prop :=
  ∀ clause, clause ∈ batchClauses input ->
    TptpFofCnfOfficialSerializationReadiness.ClauseReady
      input.skolemOutput.next input.namedOutput.next clause

theorem batchGeneratedPlan_clause_lookup (input : BatchInput)
    (firstClause offset : Nat)
    (bounded : offset < (batchClauses input).length) :
    (batchGeneratedPlan input firstClause).clauseNames.lookup?
        (index (firstClause + offset)) =
      some (clauseName (firstClause + offset)) := by
  apply tableFor_lookup_of_mem
  exact List.mem_range'.mpr ⟨offset, bounded, by omega⟩

noncomputable def batchEntries (input : BatchInput) :=
  TptpFofClausificationBatchLanguageDef.encodedClauseEntriesFrom
    input.occurrence 0 (batchClauses input)

theorem batchEntries_length (input : BatchInput) :
    (batchEntries input).length = (batchClauses input).length := by
  exact TptpFofClausificationBatchLanguageDef.encodedClauseEntriesFrom_length
    input.occurrence 0 (batchClauses input)

theorem encodedOutput_uses_exact_entries (input : BatchInput) :
    input.encodedOutput =
      TptpFofCnfNameAllocationLanguageDef.batchOutput
        (TptpFofClausificationBatchLanguageDef.encodeOccurrence
          input.occurrence)
        (TptpFofClausificationBatchLanguageDef.encodePolarity input.polarity)
        (TptpFofSkolemLanguageDef.encodeOutput input.skolemOutput
          input.namingEvidence.existentialFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput input.namedOutput
          input.definitionQuantifierFree)
        (TptpFofCnfNameAllocationAgreement.Allocated.encodeSourceEntries
          (batchEntries input)) := by
  unfold BatchInput.encodedOutput
  unfold TptpFofClausificationBatchLanguageDef.encodeOutput
  unfold batchEntries batchClauses
  rw [encodeSourceEntries_encodedClauseEntriesFrom]
  rfl

noncomputable def allocationDerivation (input : BatchInput)
    (firstClause : Nat) :=
  TptpFofCnfNameAllocationAgreement.outputDerivation
    (TptpFofClausificationBatchLanguageDef.encodeOccurrence input.occurrence)
    (TptpFofClausificationBatchLanguageDef.encodePolarity input.polarity)
    (TptpFofSkolemLanguageDef.encodeOutput input.skolemOutput
      input.namingEvidence.existentialFree)
    (TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput input.namedOutput
      input.definitionQuantifierFree)
    firstClause (batchEntries input)

noncomputable def allocatedOutput (input : BatchInput) (firstClause : Nat) :
    Pattern :=
  TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput input.encodedOutput
    (TptpResolvedFofLanguageDef.encodeNatIndex firstClause)
    (TptpResolvedFofLanguageDef.encodeNatIndex
      (firstClause + (batchEntries input).length))
    (TptpFofCnfAllocatedBatchLanguageDef.encodeAllocatedEntries
      (TptpFofCnfAllocatedBatchLanguageDef.allocateEncodedEntriesFrom
        firstClause (batchEntries input)))

private theorem serializeAllocatedEntriesFrom_exists
    (plan : TptpFofCnfOfficialSerializationPlan.Plan)
    {depth skolemBound definitionBound : Nat}
    (coverage : TptpFofCnfOfficialSerializationReadiness.Coverage plan
      depth skolemBound definitionBound)
    (occurrence : TptpFofClausificationBatchLanguageDef.SourceOccurrence)
    (localIndex firstName : Nat) (polarity : Bool) :
    ∀ (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)),
      (∀ clause, clause ∈ clauses ->
        TptpFofCnfOfficialSerializationReadiness.ClauseReady
          skolemBound definitionBound clause) ->
      (∀ offset, offset < clauses.length ->
        ∃ target, plan.clauseNames.lookup?
          (index (firstName + offset)) = some target) ->
      ∃ rendered,
        TptpFofCnfOfficialSerializationSemantics.serializeEntries? plan
          (TptpFofClausificationBatchLanguageDef.encodePolarity polarity)
          (TptpFofCnfAllocatedBatchLanguageDef.encodeAllocatedEntries
            (TptpFofCnfAllocatedBatchLanguageDef.allocateEncodedEntriesFrom
              firstName
              (TptpFofClausificationBatchLanguageDef.encodedClauseEntriesFrom
                occurrence localIndex clauses))) = some rendered
  | [], _, _ => ⟨[], rfl⟩
  | clause :: clauses, ready, names => by
      have clauseReady :
          TptpFofCnfOfficialSerializationReadiness.ClauseReady
            skolemBound definitionBound clause :=
        ready clause (by simp)
      have clausesReady : ∀ tailClause, tailClause ∈ clauses ->
          TptpFofCnfOfficialSerializationReadiness.ClauseReady
            skolemBound definitionBound tailClause := by
        intro tailClause membership
        exact ready tailClause (by simp [membership])
      obtain ⟨name, nameExact⟩ := names 0 (by simp)
      have nameExact' : plan.clauseNames.lookup?
          (TptpResolvedFofLanguageDef.encodeNatIndex firstName) =
            some name := by
        simpa only [Nat.add_zero, index] using nameExact
      obtain ⟨role, roleExact⟩ : ∃ role,
          TptpFofCnfOfficialSerializationSemantics.role?
            (TptpFofClausificationBatchLanguageDef.encodePolarity polarity) =
              some role := by
        cases polarity <;> exact ⟨_, rfl⟩
      obtain ⟨formula, formulaExact⟩ :=
        TptpFofCnfOfficialSerializationReadiness.serializeClause_exists
          plan coverage clause clauseReady
      have tailNames : ∀ offset, offset < clauses.length ->
          ∃ target, plan.clauseNames.lookup?
            (index ((firstName + 1) + offset)) = some target := by
        intro offset bounded
        obtain ⟨target, exact⟩ := names (offset + 1) (by simp; omega)
        refine ⟨target, ?_⟩
        simpa only [show firstName + (offset + 1) =
            (firstName + 1) + offset by omega] using exact
      obtain ⟨renderedTail, tailExact⟩ :=
        serializeAllocatedEntriesFrom_exists plan coverage occurrence
          (localIndex + 1) (firstName + 1) polarity clauses clausesReady
          tailNames
      refine ⟨{
        identity := TptpFofClausificationBatchLanguageDef.encodeClauseId
          occurrence localIndex
        name := name
        clause := TptpFofDefinitionalCnfLanguageDef.encodeClause clause
        annotated :=
          TptpFofCnfOfficialSerializationSemantics.annotatedCnf
            name role formula } :: renderedTail, ?_⟩
      simp only [
        TptpFofClausificationBatchLanguageDef.encodedClauseEntriesFrom,
        TptpFofCnfAllocatedBatchLanguageDef.allocateEncodedEntriesFrom,
        TptpFofCnfAllocatedBatchLanguageDef.encodeAllocatedEntries,
        TptpFofCnfAllocatedBatchLanguageDef.allocatedClauseEntry,
        TptpFofCnfAllocatedBatchLanguageDef.allocatedName,
        TptpFofCnfAllocatedBatchLanguageDef.entriesCons,
        TptpFofCnfAllocatedBatchLanguageDef.a,
        TptpFofCnfOfficialSerializationSemantics.serializeEntries?]
      rw [nameExact', roleExact, formulaExact, tailExact]
      rfl

theorem allocation_rewriteAt_exact (input : BatchInput)
    (firstClause : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofCnfNameAllocationLanguageDef.language
      (allocationDerivation input firstClause).height
      (TptpFofCnfNameAllocationLanguageDef.request input.encodedOutput
        (TptpResolvedFofLanguageDef.encodeNatIndex firstClause)) =
      [allocatedOutput input firstClause] := by
  rw [encodedOutput_uses_exact_entries]
  simpa only [allocationDerivation, allocatedOutput,
      encodedOutput_uses_exact_entries,
      TptpFofCnfNameAllocationAgreement.Allocated.encodeAllocatedEntries,
      TptpFofCnfNameAllocationAgreement.Allocated.allocateFrom] using
    TptpFofCnfNameAllocationAgreement.output_rewriteAt_exact
      (TptpFofClausificationBatchLanguageDef.encodeOccurrence input.occurrence)
      (TptpFofClausificationBatchLanguageDef.encodePolarity input.polarity)
      (TptpFofSkolemLanguageDef.encodeOutput input.skolemOutput
        input.namingEvidence.existentialFree)
      (TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput input.namedOutput
        input.definitionQuantifierFree)
      firstClause (batchEntries input)

/-! ## Composed execution through the official serializer -/

noncomputable def officialSerialization? (input : BatchInput)
    (firstClause : Nat) :=
  TptpFofCnfOfficialSerializationSemantics.serialize?
    (batchGeneratedPlan input firstClause) (allocatedOutput input firstClause)

theorem officialSerialization_exists_of_ready (input : BatchInput)
    (firstClause : Nat) (ready : BatchSerializationReady input) :
    ∃ result, officialSerialization? input firstClause = some result := by
  let plan := batchGeneratedPlan input firstClause
  have coverage : TptpFofCnfOfficialSerializationReadiness.Coverage plan
      input.namingEvidence.opened.depth input.skolemOutput.next
      input.namedOutput.next :=
    batchGeneratedPlan_coverage input firstClause
  have names : ∀ offset, offset < (batchClauses input).length ->
      ∃ target, plan.clauseNames.lookup?
        (index (firstClause + offset)) = some target := by
    intro offset bounded
    exact ⟨clauseName (firstClause + offset),
      batchGeneratedPlan_clause_lookup input firstClause offset bounded⟩
  obtain ⟨entries, entriesExact⟩ :=
    serializeAllocatedEntriesFrom_exists plan coverage input.occurrence 0
      firstClause input.polarity (batchClauses input) ready names
  refine ⟨{
    source := allocatedOutput input firstClause
    polarity :=
      TptpFofClausificationBatchLanguageDef.encodePolarity input.polarity
    entries := entries }, ?_⟩
  unfold officialSerialization?
  rw [show batchGeneratedPlan input firstClause = plan by rfl]
  unfold TptpFofCnfOfficialSerializationSemantics.serialize?
  rw [show plan.valid = true from batchGeneratedPlan_valid input firstClause]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, allocatedOutput,
    TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput,
    TptpFofCnfAllocatedBatchLanguageDef.a]
  rw [encodedOutput_uses_exact_entries input]
  simp only [TptpFofCnfNameAllocationLanguageDef.batchOutput,
    TptpFofCnfNameAllocationLanguageDef.a, batchEntries]
  rw [entriesExact]
  rfl

theorem batchSerializationReady_of_openedReady (input : BatchInput)
    (ready : TptpFofCnfOfficialSerializationReadiness.FormulaReady
      input.skolemOutput.next input.namingEvidence.opened.formula) :
    BatchSerializationReady input := by
  intro clause membership
  exact
    TptpFofCnfOfficialSerializationReadiness.nameFrom_clausesReady
      input.namingEvidence.opened.formula
      input.namingEvidence.opened.quantifierFree input.namingFrontier ready
      clause (by
        simpa [batchClauses, BatchInput.namedOutput,
          TptpFofDefinitionalPipelineAgreement.namedOutput] using membership)

theorem officialSerialization_exists_of_openedReady (input : BatchInput)
    (firstClause : Nat)
    (ready : TptpFofCnfOfficialSerializationReadiness.FormulaReady
      input.skolemOutput.next input.namingEvidence.opened.formula) :
    ∃ result, officialSerialization? input firstClause = some result :=
  officialSerialization_exists_of_ready input firstClause
    (batchSerializationReady_of_openedReady input ready)

def EndToEndExact (input : BatchInput) (firstClause : Nat)
    (result : TptpFofCnfOfficialSerializationSemantics.Result) : Prop :=
  rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language
      input.derivation.height input.encodedRequest = [input.encodedOutput] /\
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofCnfNameAllocationLanguageDef.language
      (allocationDerivation input firstClause).height
      (TptpFofCnfNameAllocationLanguageDef.request input.encodedOutput
        (TptpResolvedFofLanguageDef.encodeNatIndex firstClause)) =
        [allocatedOutput input firstClause] /\
    TptpFofCnfOfficialSerializationAgreement.EventuallyExact
      (batchGeneratedPlan input firstClause)
      (TptpFofCnfOfficialSerializationLanguageDef.serialize
        (allocatedOutput input firstClause))
      (TptpFofCnfOfficialSerializationAgreement.renderResult result)

theorem endToEndExact_of_serializes (input : BatchInput) (firstClause : Nat)
    (result : TptpFofCnfOfficialSerializationSemantics.Result)
    (serialized : officialSerialization? input firstClause = some result) :
    EndToEndExact input firstClause result := by
  refine ⟨input.rewriteAt_exact, allocation_rewriteAt_exact input firstClause,
    ?_⟩
  exact
    TptpFofCnfOfficialSerializationAgreement.serialize_eventuallyExact
      (batchGeneratedPlan input firstClause) (allocatedOutput input firstClause)
      result serialized

#print axioms indexedLexeme_injective
#print axioms generatedPlan_valid
#print axioms batchGeneratedPlan_valid
#print axioms encodeSourceEntries_encodedClauseEntriesFrom
#print axioms allocation_rewriteAt_exact
#print axioms officialSerialization_exists_of_ready
#print axioms batchSerializationReady_of_openedReady
#print axioms officialSerialization_exists_of_openedReady
#print axioms endToEndExact_of_serializes

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofCnfSerializationPipelineAgreement
