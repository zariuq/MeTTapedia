import Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
import Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission

/-!
# Operational simulation lemmas for the derivation-word machine

These lemmas connect the generic relation host to the actual contextual
rewrite relation of the authored `DerivationWordMachine` presentation.  The
constructive branch lemmas identify the exact authored transition and exact
relation rows.  Exact no-invention results are stated separately so that a
positive simulation cannot be mistaken for uniqueness.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}
variable [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState]

def inputStartBindings
    (record rest nodes nextId root serviceState : Pattern) : Bindings :=
  [("nodes", nodes), ("root", root), ("serviceState", serviceState),
   ("nextId", nextId), ("rest", rest), ("record", record)]

def inputDecodedBindings
    (record rest nodes nextId root serviceState id formula provenance
      relevance : Pattern) : Bindings :=
  [("formula", formula), ("relevance", relevance),
   ("provenance", provenance), ("id", id)] ++
    inputStartBindings record rest nodes nextId root serviceState

def inputDecodeMatchExtension
    (id formula provenance relevance : Pattern) : Bindings :=
  [("formula", formula), ("relevance", relevance),
   ("provenance", provenance), ("id", id)]

def inputDecodeQueryExtension
    (id formula provenance relevance : Pattern) : Bindings :=
  [("id", id), ("provenance", provenance),
   ("relevance", relevance), ("formula", formula)]

def inputDecodeArgumentBindings
    (record rest nodes nextId root serviceState id formula provenance
      relevance : Pattern) : Bindings :=
  inputDecodeQueryExtension id formula provenance relevance ++
    inputStartBindings record rest nodes nextId root serviceState

def inputIndexedBindings
    (record rest nodes nextId root serviceState id formula provenance
      relevance advanced : Pattern) : Bindings :=
  ("advanced", advanced) ::
    inputDecodedBindings record rest nodes nextId root serviceState id formula
      provenance relevance

def inputAcceptedBindings
    (record rest nodes nextId root serviceState id formula provenance
      relevance advanced nextServiceState : Pattern) : Bindings :=
  ("nextServiceState", nextServiceState) ::
    inputIndexedBindings record rest nodes nextId root serviceState id formula
      provenance relevance advanced

theorem applyBindings_fvar_of_lookup
    (bindings : Bindings) (name : String) (value : Pattern)
    (found : bindings.lookup name = some value) :
    applyBindings bindings (.fvar name) = value := by
  unfold Bindings.lookup at found
  cases foundPair : bindings.find? (fun entry => entry.1 == name) with
  | none => simp [foundPair] at found
  | some entry =>
      rcases entry with ⟨entryName, entryValue⟩
      simp only [foundPair, Option.map_some, Option.some.injEq] at found
      subst entryValue
      simp [applyBindings, foundPair]

theorem matchDecodedInput_exact
    (id formula provenance relevance : Pattern) :
    matchPattern
      (decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
        [v "id", v "formula", v "provenance", v "relevance"]))
      (decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
        [id, formula, provenance, relevance])) =
      [inputDecodeMatchExtension id formula provenance relevance] := by
  simp [decoded, DerivationWordMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.a, v, matchPattern, matchArgs,
    mergeBindings, inputDecodeMatchExtension]

theorem matchDecisionIndex_exact (advanced : Pattern) :
    matchPattern
      (DerivationCheckMachineLanguageDef.a "dcm:decision-index"
        [v "advanced"])
      (DerivationCheckMachineLanguageDef.a "dcm:decision-index"
        [advanced]) = [[("advanced", advanced)]] := by
  simp [DerivationCheckMachineLanguageDef.a, v, matchPattern, matchArgs,
    mergeBindings]

theorem matchDecisionAccept_exact :
    matchPattern
      (DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
      (DerivationCheckMachineLanguageDef.a "dcm:decision-accept") = [[]] := by
  simp [DerivationCheckMachineLanguageDef.a, matchPattern, matchArgs]

theorem liftedInputAccept_premises :
    (liftRewrite
      DerivationCheckMachineLanguageDef.inputAcceptTransition).premises =
    [query "DWMDecodeRecord" [v "record", decoded
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [v "id", v "formula", v "provenance", v "relevance"])],
     query "DCMIndexAdvance" [v "nextId", v "id",
       DerivationCheckMachineLanguageDef.a "dcm:decision-index"
         [v "advanced"]],
     query "DCMRelevanceShapeDecision" [v "id", v "relevance",
       DerivationCheckMachineLanguageDef.a "dcm:decision-accept"],
     query "DCMInputDecision" [v "id", v "serviceState", v "provenance",
       v "formula", DerivationCheckMachineLanguageDef.decisionState
         (v "nextServiceState")]] := by
  simp [liftRewrite, DerivationCheckMachineLanguageDef.inputAcceptTransition,
    sourceInstruction?, liftPremise, liftPattern,
    DerivationWordMachineLanguageDef.query,
    DerivationWordMachineLanguageDef.v,
    DerivationWordMachineLanguageDef.decoded,
    DerivationWordMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query]

theorem liftedInputAccept_left :
    (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition).left =
      run (recordsCons (v "record") (v "rest")) (v "nodes")
        (v "nextId") (v "root") (v "serviceState") := by
  simp [liftRewrite, DerivationCheckMachineLanguageDef.inputAcceptTransition,
    sourceInstruction?, liftLeft, liftPattern,
    DerivationWordMachineLanguageDef.run,
    DerivationWordMachineLanguageDef.recordsCons,
    DerivationWordMachineLanguageDef.v,
    DerivationWordMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v]

theorem liftedInputAccept_right :
    (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition).right =
      run (v "rest")
        (DerivationCheckMachineLanguageDef.nodesCons
          (DerivationCheckMachineLanguageDef.node (v "id") (v "formula")
            (v "relevance")
            (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
          (v "nodes"))
        (v "advanced") (v "root") (v "nextServiceState") := by
  simp [liftRewrite, DerivationCheckMachineLanguageDef.inputAcceptTransition,
    sourceInstruction?, liftPattern,
    DerivationWordMachineLanguageDef.run,
    DerivationWordMachineLanguageDef.v,
    DerivationWordMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.nodesCons,
    DerivationCheckMachineLanguageDef.node,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v]

theorem matchDecisionState_exact (nextServiceState : Pattern) :
    matchPattern
      (DerivationCheckMachineLanguageDef.decisionState
        (v "nextServiceState"))
      (DerivationCheckMachineLanguageDef.decisionState
        nextServiceState) = [[("nextServiceState", nextServiceState)]] := by
  simp [DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.a, v, matchPattern, matchArgs,
    mergeBindings]

theorem input_accept_step_mem
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern
      nextServiceStatePattern : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (serviceState : ServiceState)
    (provenance : Provenance) (formula : Formula)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (inputAccepted :
      inputDecision host actualId serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern) :
    run rest
        (DerivationCheckMachineLanguageDef.nodesCons
          (DerivationCheckMachineLanguageDef.node idPattern formulaPattern
            relevancePatternValue
            (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
          nodes)
        advancedPattern root nextServiceStatePattern ∈
      rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) := by
  let start := inputStartBindings record rest nodes nextIdPattern root
    serviceStatePattern
  let afterDecode := inputDecodedBindings record rest nodes nextIdPattern root
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue
  let afterIndex := inputIndexedBindings record rest nodes nextIdPattern root
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern
  let final := inputAcceptedBindings record rest nodes nextIdPattern root
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern nextServiceStatePattern
  have decodePremise :
      afterDecode ∈ premiseStepWithEnv (relationEnv host) language start
        (query "DWMDecodeRecord" [v "record", decoded
          (DerivationCheckMachineLanguageDef.a "dcm:input"
            [v "id", v "formula", v "provenance", v "relevance"])]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [record, decoded
        (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue])])
      (extension := inputDecodeQueryExtension idPattern formulaPattern
        provenancePattern relevancePatternValue)
    · have row : [record, decoded
          (DerivationCheckMachineLanguageDef.a "dcm:input"
            [idPattern, formulaPattern, provenancePattern,
             relevancePatternValue])] ∈
          relationTuples host "DWMDecodeRecord"
            [record, decoded
              (DerivationCheckMachineLanguageDef.a "dcm:input"
                [v "id", v "formula", v "provenance", v "relevance"])] := by
        simp [relationTuples, recordDecoded]
      simpa [relationEnv, start, inputStartBindings, applyBindings,
        DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, decoded] using row
    · apply matchRelationArgs_bound_cons
        (tailExtension := inputDecodeMatchExtension idPattern formulaPattern
          provenancePattern relevancePatternValue)
        (combined := inputDecodeQueryExtension idPattern formulaPattern
          provenancePattern relevancePatternValue)
        (found := by simp [start, inputStartBindings, Bindings.lookup])
        (combine := by simp [inputDecodeMatchExtension,
          inputDecodeQueryExtension, mergeBindings])
      apply matchRelationArgs_single
        (extension := inputDecodeMatchExtension idPattern formulaPattern
          provenancePattern relevancePatternValue)
        (extended := inputDecodeArgumentBindings record rest nodes
          nextIdPattern root serviceStatePattern idPattern formulaPattern
          provenancePattern relevancePatternValue)
      · have matched :
            inputDecodeMatchExtension idPattern formulaPattern
              provenancePattern relevancePatternValue ∈
            matchPattern
              (decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
                [v "id", v "formula", v "provenance", v "relevance"]))
              (decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
                [idPattern, formulaPattern, provenancePattern,
                 relevancePatternValue])) := by
          rw [matchDecodedInput_exact]
          simp
        simpa [matchRelationArgument, start, inputStartBindings, decoded,
          DerivationWordMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.a, v, applyBindings] using matched
      · simp [start, inputStartBindings, inputDecodeArgumentBindings,
          inputDecodeMatchExtension, inputDecodeQueryExtension,
          mergeBindings]
    · simp [start, afterDecode, inputStartBindings, inputDecodedBindings,
        inputDecodeQueryExtension, mergeBindings]
  have indexPremise :
      afterIndex ∈ premiseStepWithEnv (relationEnv host) language afterDecode
        (query "DCMIndexAdvance" [v "nextId", v "id",
          DerivationCheckMachineLanguageDef.a "dcm:decision-index"
            [v "advanced"]]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [nextIdPattern, idPattern,
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern]])
      (extension := [("advanced", advancedPattern)])
    · have row : [nextIdPattern, idPattern,
          DerivationCheckMachineLanguageDef.a "dcm:decision-index"
            [advancedPattern]] ∈
          relationTuples host "DCMIndexAdvance"
            [nextIdPattern, idPattern,
              DerivationCheckMachineLanguageDef.a "dcm:decision-index"
                [v "advanced"]] := by
        rw [indexAdvance_tuple_for_request host nextIdPattern idPattern
          (DerivationCheckMachineLanguageDef.a "dcm:decision-index"
            [v "advanced"])
          expectedId actualId nextIdDecoded idDecoded]
        rw [indexAccepted]
        simp
      simpa [relationEnv, afterDecode, inputDecodedBindings,
        inputStartBindings, DerivationCheckMachineLanguageDef.a, v,
        applyBindings] using row
    · apply matchRelationArgs_bound_cons
        (tailExtension := [("advanced", advancedPattern)])
        (combined := [("advanced", advancedPattern)])
        (found := by simp [afterDecode, inputDecodedBindings,
          inputStartBindings, Bindings.lookup])
        (combine := by simp [mergeBindings])
      apply matchRelationArgs_bound_cons
        (tailExtension := [("advanced", advancedPattern)])
        (combined := [("advanced", advancedPattern)])
        (found := by simp [afterDecode, inputDecodedBindings,
          inputStartBindings, Bindings.lookup])
        (combine := by simp [mergeBindings])
      apply matchRelationArgs_single
        (extension := [("advanced", advancedPattern)])
        (extended := afterIndex)
      · have matched : [("advanced", advancedPattern)] ∈
            matchPattern
              (DerivationCheckMachineLanguageDef.a "dcm:decision-index"
                [v "advanced"])
              (DerivationCheckMachineLanguageDef.a "dcm:decision-index"
                [advancedPattern]) := by
          rw [matchDecisionIndex_exact]
          simp
        simpa [matchRelationArgument, afterDecode, inputDecodedBindings,
          inputStartBindings, DerivationCheckMachineLanguageDef.a, v,
          applyBindings] using matched
      · simp [afterDecode, afterIndex, inputDecodedBindings,
          inputIndexedBindings, inputStartBindings, mergeBindings]
    · simp [afterDecode, afterIndex, inputDecodedBindings,
        inputIndexedBindings, inputStartBindings, mergeBindings]
  have relevancePremise :
      afterIndex ∈ premiseStepWithEnv (relationEnv host) language afterIndex
        (query "DCMRelevanceShapeDecision" [v "id", v "relevance",
          DerivationCheckMachineLanguageDef.a "dcm:decision-accept"]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [idPattern, relevancePatternValue,
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept"])
      (extension := [])
    · have row : [idPattern, relevancePatternValue,
          DerivationCheckMachineLanguageDef.a "dcm:decision-accept"] ∈
          relationTuples host "DCMRelevanceShapeDecision"
            [idPattern, relevancePatternValue,
              DerivationCheckMachineLanguageDef.a "dcm:decision-accept"] := by
        rw [relevanceShape_tuple_for_request host idPattern
          relevancePatternValue
          (DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
          actualId relevance idDecoded relevanceDecoded]
        rw [relevanceAccepted]
        simp
      simpa [relationEnv, afterIndex, inputIndexedBindings,
        inputDecodedBindings, inputStartBindings,
        DerivationCheckMachineLanguageDef.a, v, applyBindings] using row
    · apply matchRelationArgs_bound_cons
        (tailExtension := []) (combined := [])
        (found := by simp [afterIndex, inputIndexedBindings,
          inputDecodedBindings, inputStartBindings, Bindings.lookup])
        (combine := by simp [mergeBindings])
      apply matchRelationArgs_bound_cons
        (tailExtension := []) (combined := [])
        (found := by simp [afterIndex, inputIndexedBindings,
          inputDecodedBindings, inputStartBindings, Bindings.lookup])
        (combine := by simp [mergeBindings])
      apply matchRelationArgs_single
        (extension := []) (extended := afterIndex)
      · have matched : [] ∈
            matchPattern
              (DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
              (DerivationCheckMachineLanguageDef.a
                "dcm:decision-accept") := by
          rw [matchDecisionAccept_exact]
          simp
        simpa [matchRelationArgument, DerivationCheckMachineLanguageDef.a,
          applyBindings] using matched
      · simp [mergeBindings]
    · simp [mergeBindings]
  have inputPremise :
      final ∈ premiseStepWithEnv (relationEnv host) language afterIndex
        (query "DCMInputDecision" [v "id", v "serviceState",
          v "provenance", v "formula",
          DerivationCheckMachineLanguageDef.decisionState
            (v "nextServiceState")]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [idPattern, serviceStatePattern, provenancePattern,
        formulaPattern,
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern])
      (extension := [("nextServiceState", nextServiceStatePattern)])
    · have row : [idPattern, serviceStatePattern, provenancePattern,
          formulaPattern,
          DerivationCheckMachineLanguageDef.decisionState
            nextServiceStatePattern] ∈
          relationTuples host "DCMInputDecision"
            [idPattern, serviceStatePattern, provenancePattern,
              formulaPattern,
              DerivationCheckMachineLanguageDef.decisionState
                (v "nextServiceState")] := by
        rw [inputDecision_tuple_for_request host actualId idPattern
          serviceStatePattern provenancePattern formulaPattern
          (DerivationCheckMachineLanguageDef.decisionState
            (v "nextServiceState"))
          serviceState provenance formula idDecoded serviceStateDecoded
          provenanceDecoded formulaDecoded]
        rw [inputAccepted]
        simp
      simpa [relationEnv, afterIndex, inputIndexedBindings,
        inputDecodedBindings, inputStartBindings,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.decisionState, v,
        applyBindings] using row
    · apply matchRelationArgs_bound_cons
        (tailExtension := [("nextServiceState", nextServiceStatePattern)])
        (combined := [("nextServiceState", nextServiceStatePattern)])
        (found := by simp [afterIndex, inputIndexedBindings,
          inputDecodedBindings, inputStartBindings, Bindings.lookup])
        (combine := by simp [mergeBindings])
      apply matchRelationArgs_bound_cons
        (tailExtension := [("nextServiceState", nextServiceStatePattern)])
        (combined := [("nextServiceState", nextServiceStatePattern)])
        (found := by simp [afterIndex, inputIndexedBindings,
          inputDecodedBindings, inputStartBindings, Bindings.lookup])
        (combine := by simp [mergeBindings])
      apply matchRelationArgs_bound_cons
        (tailExtension := [("nextServiceState", nextServiceStatePattern)])
        (combined := [("nextServiceState", nextServiceStatePattern)])
        (found := by simp [afterIndex, inputIndexedBindings,
          inputDecodedBindings, inputStartBindings, Bindings.lookup])
        (combine := by simp [mergeBindings])
      apply matchRelationArgs_bound_cons
        (tailExtension := [("nextServiceState", nextServiceStatePattern)])
        (combined := [("nextServiceState", nextServiceStatePattern)])
        (found := by simp [afterIndex, inputIndexedBindings,
          inputDecodedBindings, inputStartBindings, Bindings.lookup])
        (combine := by simp [mergeBindings])
      apply matchRelationArgs_single
        (extension := [("nextServiceState", nextServiceStatePattern)])
        (extended := final)
      · have matched : [("nextServiceState", nextServiceStatePattern)] ∈
            matchPattern
              (DerivationCheckMachineLanguageDef.decisionState
                (v "nextServiceState"))
              (DerivationCheckMachineLanguageDef.decisionState
                nextServiceStatePattern) := by
          rw [matchDecisionState_exact]
          simp
        simpa [matchRelationArgument, afterIndex, inputIndexedBindings,
          inputDecodedBindings, inputStartBindings,
          DerivationCheckMachineLanguageDef.decisionState,
          DerivationCheckMachineLanguageDef.a, v, applyBindings] using matched
      · simp [afterIndex, final, inputIndexedBindings,
          inputAcceptedBindings, inputDecodedBindings, inputStartBindings,
          mergeBindings]
    · simp [afterIndex, final, inputIndexedBindings, inputAcceptedBindings,
        inputDecodedBindings, inputStartBindings, mergeBindings]
  have premiseEvidence :
      PremisesAt (engineBasePremises (relationEnv host)) language 0 start
        (liftRewrite
          DerivationCheckMachineLanguageDef.inputAcceptTransition).premises
        final := by
    rw [liftedInputAccept_premises]
    exact .cons (.relationQuery (by
        simpa [engineBasePremises, query] using decodePremise))
      (.cons (.relationQuery (by
          simpa [engineBasePremises, query] using indexPremise))
        (.cons (.relationQuery (by
            simpa [engineBasePremises, query] using relevancePremise))
          (.cons (.relationQuery (by
              simpa [engineBasePremises, query] using inputPremise))
            (.nil final))))
  apply mem_rewriteAt_iff_stepAt.mpr
  exact .rule
    (by simp [language, transitions, liftedTransitions,
      DerivationCheckMachineLanguageDef.transitions])
    (by
      rw [show
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
          language
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputAcceptTransition)
          (run (recordsCons record rest) nodes nextIdPattern root
            serviceStatePattern) =
        matchPattern
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputAcceptTransition).left
          (run (recordsCons record rest) nodes nextIdPattern root
            serviceStatePattern) by rfl]
      rw [liftedInputAccept_left]
      simp [start, inputStartBindings, run, recordsCons,
        DerivationWordMachineLanguageDef.a, v, matchPattern, matchArgs,
        mergeBindings])
    premiseEvidence
    (by
      rw [show
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
          language
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputAcceptTransition) final =
        applyBindings final
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputAcceptTransition).right
          by rfl]
      rw [liftedInputAccept_right]
      simp [final, inputAcceptedBindings, inputIndexedBindings,
        inputDecodedBindings, inputStartBindings, run,
        DerivationCheckMachineLanguageDef.nodesCons,
        DerivationCheckMachineLanguageDef.node,
        DerivationCheckMachineLanguageDef.a,
        DerivationWordMachineLanguageDef.a, v, applyBindings])

#print axioms input_accept_step_mem

theorem input_accept_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern
      nextServiceStatePattern : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (serviceState : ServiceState)
    (provenance : Provenance) (formula : Formula)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (inputAccepted :
      inputDecision host actualId serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) =
      [run rest
        (DerivationCheckMachineLanguageDef.nodesCons
          (DerivationCheckMachineLanguageDef.node idPattern formulaPattern
            relevancePatternValue
            (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
          nodes)
        advancedPattern root nextServiceStatePattern] := by
  let start := inputStartBindings record rest nodes nextIdPattern root
    serviceStatePattern
  let afterDecode := inputDecodedBindings record rest nodes nextIdPattern root
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue
  let afterIndex := inputIndexedBindings record rest nodes nextIdPattern root
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern
  let final := inputAcceptedBindings record rest nodes nextIdPattern root
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue advancedPattern nextServiceStatePattern
  have decodeExact :
      premiseStepWithEnv (relationEnv host) language start
        (query "DWMDecodeRecord" [v "record", decoded
          (DerivationCheckMachineLanguageDef.a "dcm:input"
            [v "id", v "formula", v "provenance", v "relevance"])]) =
        [afterDecode] := by
    simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      relationEnv, relationTuples, recordDecoded, start, afterDecode,
      inputStartBindings, inputDecodedBindings,
      query, v, decoded, DerivationWordMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.a, matchRelationArgs,
      matchRelationArgument, matchPattern, matchArgs, mergeBindings,
      applyBindings, Bindings.lookup]
  have indexExact :
      premiseStepWithEnv (relationEnv host) language afterDecode
        (query "DCMIndexAdvance" [v "nextId", v "id",
          DerivationCheckMachineLanguageDef.a "dcm:decision-index"
            [v "advanced"]]) = [afterIndex] := by
    simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      relationEnv, relationTuples, nextIdDecoded, idDecoded, indexAccepted,
      afterDecode, afterIndex, inputStartBindings, inputDecodedBindings,
      inputIndexedBindings, query, v,
      DerivationCheckMachineLanguageDef.a, matchRelationArgs,
      matchRelationArgument, matchPattern, matchArgs, mergeBindings,
      applyBindings, Bindings.lookup]
  have relevanceExact :
      premiseStepWithEnv (relationEnv host) language afterIndex
        (query "DCMRelevanceShapeDecision" [v "id", v "relevance",
          DerivationCheckMachineLanguageDef.a "dcm:decision-accept"]) =
        [afterIndex] := by
    simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      relationEnv, relationTuples, idDecoded, relevanceDecoded,
      relevanceAccepted, afterIndex, inputStartBindings,
      inputDecodedBindings, inputIndexedBindings, query, v,
      DerivationCheckMachineLanguageDef.a, matchRelationArgs,
      matchRelationArgument, matchPattern, matchArgs, mergeBindings,
      applyBindings, Bindings.lookup]
  have inputExact :
      premiseStepWithEnv (relationEnv host) language afterIndex
        (query "DCMInputDecision" [v "id", v "serviceState",
          v "provenance", v "formula",
          DerivationCheckMachineLanguageDef.decisionState
            (v "nextServiceState")]) = [final] := by
    simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      relationEnv, relationTuples, idDecoded, serviceStateDecoded,
      provenanceDecoded, formulaDecoded, inputAccepted, afterIndex, final,
      inputStartBindings, inputDecodedBindings, inputIndexedBindings,
      inputAcceptedBindings, query, v,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.decisionState, matchRelationArgs,
      matchRelationArgument, matchPattern, matchArgs, mergeBindings,
      applyBindings, Bindings.lookup]
  unfold applyRuleUsing
  rw [show
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
      language
      (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [start] by
      rw [show
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
          language
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputAcceptTransition)
          (run (recordsCons record rest) nodes nextIdPattern root
            serviceStatePattern) =
        matchPattern
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputAcceptTransition).left
          (run (recordsCons record rest) nodes nextIdPattern root
            serviceStatePattern) by rfl]
      rw [liftedInputAccept_left]
      simp [start, inputStartBindings, run, recordsCons,
        DerivationWordMachineLanguageDef.a, v, matchPattern, matchArgs,
        mergeBindings]]
  rw [liftedInputAccept_premises]
  have decodeStepExact :
      premiseStepUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) start
        (query "DWMDecodeRecord" [v "record", decoded
          (DerivationCheckMachineLanguageDef.a "dcm:input"
            [v "id", v "formula", v "provenance", v "relevance"])]) =
        [afterDecode] := by
    simpa only [query, premiseStepUsing, engineBasePremises] using decodeExact
  have indexStepExact :
      premiseStepUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) afterDecode
        (query "DCMIndexAdvance" [v "nextId", v "id",
          DerivationCheckMachineLanguageDef.a "dcm:decision-index"
            [v "advanced"]]) = [afterIndex] := by
    simpa only [query, premiseStepUsing, engineBasePremises] using indexExact
  have relevanceStepExact :
      premiseStepUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) afterIndex
        (query "DCMRelevanceShapeDecision" [v "id", v "relevance",
          DerivationCheckMachineLanguageDef.a "dcm:decision-accept"]) =
        [afterIndex] := by
    simpa only [query, premiseStepUsing, engineBasePremises] using relevanceExact
  have inputStepExact :
      premiseStepUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) afterIndex
        (query "DCMInputDecision" [v "id", v "serviceState",
          v "provenance", v "formula",
          DerivationCheckMachineLanguageDef.decisionState
            (v "nextServiceState")]) = [final] := by
    simpa only [query, premiseStepUsing, engineBasePremises] using inputExact
  have premisesExact :
      premisesUsing (engineBasePremises (relationEnv host)) language
        (fun _ => [])
        [query "DWMDecodeRecord" [v "record", decoded
            (DerivationCheckMachineLanguageDef.a "dcm:input"
              [v "id", v "formula", v "provenance", v "relevance"])],
          query "DCMIndexAdvance" [v "nextId", v "id",
            DerivationCheckMachineLanguageDef.a "dcm:decision-index"
              [v "advanced"]],
          query "DCMRelevanceShapeDecision" [v "id", v "relevance",
            DerivationCheckMachineLanguageDef.a "dcm:decision-accept"],
          query "DCMInputDecision" [v "id", v "serviceState",
            v "provenance", v "formula",
            DerivationCheckMachineLanguageDef.decisionState
              (v "nextServiceState")]] start = [final] := by
    simp only [premisesUsing, decodeStepExact, indexStepExact,
      relevanceStepExact, inputStepExact, List.flatMap_singleton]
  have outputExact :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language
        (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition)
        final =
      run rest
        (DerivationCheckMachineLanguageDef.nodesCons
          (DerivationCheckMachineLanguageDef.node idPattern formulaPattern
            relevancePatternValue
            (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
          nodes)
        advancedPattern root nextServiceStatePattern := by
    rw [show
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        language
        (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition)
        final =
      applyBindings final
        (liftRewrite
          DerivationCheckMachineLanguageDef.inputAcceptTransition).right
      by rfl]
    rw [liftedInputAccept_right]
    simp [final, inputAcceptedBindings, inputIndexedBindings,
      inputDecodedBindings, inputStartBindings, run,
      DerivationCheckMachineLanguageDef.nodesCons,
      DerivationCheckMachineLanguageDef.node,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineLanguageDef.a, v, applyBindings]
  simp only [List.flatMap_singleton, premisesExact, List.map_singleton,
    outputExact]

#print axioms input_accept_applyRule_exact

/-- A decoder row cannot satisfy a differently shaped decode decision.  The
statement is independent of any particular instruction tag and is the
no-invention boundary used to exclude unrelated lifted transitions. -/
theorem decode_query_empty_of_mismatch
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (bindings : Bindings) (record expectedInstruction actualInstruction : Pattern)
    (recordFound : bindings.lookup "record" = some record)
    (recordDecoded :
      decodeDecision host record = decoded actualInstruction)
    (mismatch :
      matchPattern
        (applyBindings bindings (decoded expectedInstruction))
        (decoded actualInstruction) = []) :
    premiseStepWithEnv (relationEnv host) language bindings
      (query "DWMDecodeRecord" [v "record", decoded expectedInstruction]) =
        [] := by
  have recordApplied : applyBindings bindings (v "record") = record := by
    simpa only [v] using
      applyBindings_fvar_of_lookup bindings "record" record recordFound
  have rowsExact :
      builtinRelationTuples language "DWMDecodeRecord"
          [record, applyBindings bindings (decoded expectedInstruction)] ++
        relationTuples host "DWMDecodeRecord"
          [record, applyBindings bindings (decoded expectedInstruction)] =
        [[record, decoded actualInstruction]] := by
    simp [builtinRelationTuples, relationTuples, recordDecoded]
  have argumentsMismatch :
      matchRelationArgs bindings
        [v "record", decoded expectedInstruction]
        [record, decoded actualInstruction] = [] := by
    have recordArgumentExact :
        matchRelationArgument bindings (v "record") record = [[]] := by
      simp only [v, matchRelationArgument, recordFound, ↓reduceIte]
    have decisionArgumentEmpty :
        matchRelationArgument bindings (decoded expectedInstruction)
          (decoded actualInstruction) = [] := by
      rw [show
        matchRelationArgument bindings (decoded expectedInstruction)
            (decoded actualInstruction) =
          matchPattern (applyBindings bindings (decoded expectedInstruction))
            (decoded actualInstruction) by rfl]
      exact mismatch
    simp only [matchRelationArgs, recordArgumentExact, List.flatMap_singleton]
    simp [mergeBindings, decisionArgumentEmpty]
  change relationQueryStep (relationEnv host) language bindings
      "DWMDecodeRecord" [v "record", decoded expectedInstruction] = []
  simp only [relationQueryStep]
  rw [show
    List.map (applyBindings bindings)
        [v "record", decoded expectedInstruction] =
      [record, applyBindings bindings (decoded expectedInstruction)] by
        simp only [List.map_cons, List.map_nil, recordApplied]]
  rw [show
    builtinRelationTuples language "DWMDecodeRecord"
          [record, applyBindings bindings (decoded expectedInstruction)] ++
        (relationEnv host).tuples "DWMDecodeRecord"
          [record, applyBindings bindings (decoded expectedInstruction)] =
      [[record, decoded actualInstruction]] by
        simpa [relationEnv] using rowsExact]
  simp [argumentsMismatch]

#print axioms decode_query_empty_of_mismatch

theorem applyRuleUsing_empty_of_decode_mismatch
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rule : RewriteRule) (term record expectedInstruction actualInstruction :
      Pattern)
    (remainingPremises : List Premise)
    (premisesStartWithDecode :
      rule.premises =
        query "DWMDecodeRecord" [v "record", decoded expectedInstruction] ::
          remainingPremises)
    (recordDecoded :
      decodeDecision host record = decoded actualInstruction)
    (matchedRecord : ∀ bindings,
      bindings ∈
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
          language rule term →
      bindings.lookup "record" = some record)
    (decodedShapesDisjoint : ∀ bindings,
      bindings ∈
        Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
          language rule term →
      matchPattern
        (applyBindings bindings (decoded expectedInstruction))
        (decoded actualInstruction) = []) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) rule term = [] := by
  unfold applyRuleUsing
  rw [List.flatMap_eq_nil_iff]
  intro bindings membership
  rw [premisesStartWithDecode]
  have decodeEmpty := decode_query_empty_of_mismatch host bindings record
    expectedInstruction actualInstruction (matchedRecord bindings membership)
    recordDecoded (decodedShapesDisjoint bindings membership)
  have headEmpty :
      premiseStepUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) bindings
        (query "DWMDecodeRecord" [v "record", decoded expectedInstruction]) =
        [] := by
    simpa only [query, premiseStepUsing, engineBasePremises] using decodeEmpty
  simp only [premisesUsing, headEmpty, List.flatMap_nil, List.map_nil]

#print axioms applyRuleUsing_empty_of_decode_mismatch

theorem generic_record_left_match_exact
    (rule : RewriteRule)
    (record rest nodes nextId root serviceState : Pattern)
    (leftExact : rule.left =
      run (recordsCons (v "record") (v "rest")) (v "nodes")
        (v "nextId") (v "root") (v "serviceState")) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language rule
        (run (recordsCons record rest) nodes nextId root serviceState) =
      [inputStartBindings record rest nodes nextId root serviceState] := by
  rw [show
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        language rule
        (run (recordsCons record rest) nodes nextId root serviceState) =
      matchPattern rule.left
        (run (recordsCons record rest) nodes nextId root serviceState) by rfl]
  rw [leftExact]
  simp [inputStartBindings, run, recordsCons,
    DerivationWordMachineLanguageDef.a, v, matchPattern, matchArgs,
    mergeBindings]

#print axioms generic_record_left_match_exact

theorem generic_record_rule_empty_of_decode_mismatch
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rule : RewriteRule)
    (record rest nodes nextId root serviceState expectedInstruction
      actualInstruction : Pattern)
    (remainingPremises : List Premise)
    (premisesStartWithDecode :
      rule.premises =
        query "DWMDecodeRecord" [v "record", decoded expectedInstruction] ::
          remainingPremises)
    (leftExact : rule.left =
      run (recordsCons (v "record") (v "rest")) (v "nodes")
        (v "nextId") (v "root") (v "serviceState"))
    (recordDecoded :
      decodeDecision host record = decoded actualInstruction)
    (mismatchAtStart :
      matchPattern
        (applyBindings
          (inputStartBindings record rest nodes nextId root serviceState)
          (decoded expectedInstruction))
        (decoded actualInstruction) = []) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) rule
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  apply applyRuleUsing_empty_of_decode_mismatch host rule
    (run (recordsCons record rest) nodes nextId root serviceState) record
    expectedInstruction actualInstruction remainingPremises
    premisesStartWithDecode recordDecoded
  · intro bindings membership
    rw [generic_record_left_match_exact rule record rest nodes nextId root
      serviceState leftExact] at membership
    simp only [List.mem_singleton] at membership
    subst bindings
    simp [inputStartBindings, Bindings.lookup]
  · intro bindings membership
    rw [generic_record_left_match_exact rule record rest nodes nextId root
      serviceState leftExact] at membership
    simp only [List.mem_singleton] at membership
    subst bindings
    exact mismatchAtStart

#print axioms generic_record_rule_empty_of_decode_mismatch

theorem generic_lifted_record_rule_empty_of_decode_mismatch
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState expectedInstruction
      actualInstruction : Pattern)
    (sourceInstructionExact :
      sourceInstruction? sourceRule.left = some expectedInstruction)
    (leftExact : liftLeft sourceRule.left =
      run (recordsCons (v "record") (v "rest")) (v "nodes")
        (v "nextId") (v "root") (v "serviceState"))
    (recordDecoded :
      decodeDecision host record = decoded actualInstruction)
    (mismatchAtStart :
      matchPattern
        (applyBindings
          (inputStartBindings record rest nodes nextId root serviceState)
          (decoded expectedInstruction))
        (decoded actualInstruction) = []) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  apply generic_record_rule_empty_of_decode_mismatch host
    (liftRewrite sourceRule) record rest nodes nextId root serviceState
    expectedInstruction actualInstruction (sourceRule.premises.map liftPremise)
  · simp [liftRewrite, sourceInstructionExact]
  · simpa [liftRewrite] using leftExact
  · exact recordDecoded
  · exact mismatchAtStart

#print axioms generic_lifted_record_rule_empty_of_decode_mismatch

theorem input_index_fault_applyRule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern :
      Pattern)
    (expectedId actualId : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inputIndexFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded, DerivationWordMachineLanguageDef.a,
    relationEnv, relationTuples, recordDecoded, nextIdDecoded, idDecoded,
    indexAccepted, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms input_index_fault_applyRule_empty

theorem input_index_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue faultPatternValue :
      Pattern)
    (expectedId actualId : Nat)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexFaulted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inputIndexFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, halted, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nextIdDecoded, idDecoded, indexFaulted,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    mergeBindings, applyBindings, Bindings.lookup]

#print axioms input_index_fault_applyRule_exact

def inputIndexSuccessSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
  DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
  DerivationCheckMachineLanguageDef.inputAcceptTransition
]

/-- Once index validation returns a fault, none of the later input rows can
run.  This keeps the faulting relation deterministic without rechecking later
semantic services. -/
theorem input_index_fault_excludes_later_rule
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue faultPatternValue :
      Pattern)
    (expectedId actualId : Nat)
    (membership : sourceRule ∈ inputIndexSuccessSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexFaulted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp only [inputIndexSuccessSourceRules, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl | rfl <;>
    simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
      DerivationCheckMachineLanguageDef.inputAcceptTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.decisionState,
      DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.halted,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, nextIdDecoded, idDecoded, indexFaulted,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
      mergeBindings, applyBindings, Bindings.lookup]

#print axioms input_index_fault_excludes_later_rule

theorem input_relevance_fault_applyRule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern :
      Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept") :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded, DerivationWordMachineLanguageDef.a,
    relationEnv, relationTuples, recordDecoded, nextIdDecoded, idDecoded,
    relevanceDecoded, indexAccepted, relevanceAccepted, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples, matchRelationArgs,
    matchRelationArgument, matchPattern, matchArgs, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms input_relevance_fault_applyRule_empty

theorem input_relevance_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern
      faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceFaulted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, halted, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
    indexAccepted, relevanceFaulted, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms input_relevance_fault_applyRule_exact

def inputRelevanceSuccessSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
  DerivationCheckMachineLanguageDef.inputAcceptTransition
]

theorem input_relevance_fault_excludes_later_rule
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern
      faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (membership : sourceRule ∈ inputRelevanceSuccessSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceFaulted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp only [inputRelevanceSuccessSourceRules, List.mem_cons,
    List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl <;>
    simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
      DerivationCheckMachineLanguageDef.inputAcceptTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.decisionState,
      DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.halted,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
      indexAccepted, relevanceFaulted, premiseStepWithEnv,
      relationQueryStep, builtinRelationTuples, matchRelationArgs,
      matchRelationArgument, matchPattern, matchArgs, mergeBindings,
      applyBindings, Bindings.lookup]

#print axioms input_relevance_fault_excludes_later_rule

theorem input_decision_fault_applyRule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern
      nextServiceStatePattern : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (serviceState : ServiceState) (provenance : Provenance)
    (formula : Formula)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (inputAccepted :
      inputDecision host actualId serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.inputDecisionFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded, DerivationWordMachineLanguageDef.a,
    relationEnv, relationTuples, recordDecoded, nextIdDecoded, idDecoded,
    relevanceDecoded, serviceStateDecoded, provenanceDecoded, formulaDecoded,
    indexAccepted, relevanceAccepted, inputAccepted, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples, matchRelationArgs,
    matchRelationArgument, matchPattern, matchArgs, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms input_decision_fault_applyRule_empty

theorem input_decision_fault_applyRule_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern
      faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (serviceState : ServiceState) (provenance : Provenance)
    (formula : Formula)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (inputFaulted :
      inputDecision host actualId serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite
        DerivationCheckMachineLanguageDef.inputDecisionFaultTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, halted, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
    serviceStateDecoded, provenanceDecoded, formulaDecoded, indexAccepted,
    relevanceAccepted, inputFaulted, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms input_decision_fault_applyRule_exact

theorem input_decision_fault_excludes_accept
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextIdPattern root serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern
      faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (serviceState : ServiceState) (provenance : Provenance)
    (formula : Formula)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (inputFaulted :
      inputDecision host actualId serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition)
      (run (recordsCons record rest) nodes nextIdPattern root
        serviceStatePattern) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern, liftPremise,
    DerivationCheckMachineLanguageDef.inputAcceptTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.decisionFault,
    DerivationCheckMachineLanguageDef.decisionState,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    DerivationCheckMachineLanguageDef.query,
    query, v, run, recordsCons, decoded,
    DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
    recordDecoded, nextIdDecoded, idDecoded, relevanceDecoded,
    serviceStateDecoded, provenanceDecoded, formulaDecoded, indexAccepted,
    relevanceAccepted, inputFaulted, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms input_decision_fault_excludes_accept

def genericNonInputSourceRules : List RewriteRule := [
  DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
  DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
  DerivationCheckMachineLanguageDef.inferParentFaultTransition,
  DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
  DerivationCheckMachineLanguageDef.inferAcceptTransition,
  DerivationCheckMachineLanguageDef.dropFaultTransition,
  DerivationCheckMachineLanguageDef.dropAcceptTransition
]

theorem generic_non_input_lifted_rule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId root serviceState id formula provenance
      relevance : Pattern)
    (membership : sourceRule ∈ genericNonInputSourceRules)
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [id, formula, provenance, relevance])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp only [genericNonInputSourceRules, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.inferIndexFaultTransition record rest
      nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [v "id", v "rule", v "parents", v "evidence", v "conclusion",
         v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [id, formula, provenance, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded, DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition record
      rest nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [v "id", v "rule", v "parents", v "evidence", v "conclusion",
         v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [id, formula, provenance, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded, DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.inferParentFaultTransition record rest
      nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [v "id", v "rule", v "parents", v "evidence", v "conclusion",
         v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [id, formula, provenance, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inferParentFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inferParentFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded, DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.inferRuleFaultTransition record rest
      nodes nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [v "id", v "rule", v "parents", v "evidence", v "conclusion",
         v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [id, formula, provenance, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded, DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.inferAcceptTransition record rest nodes
      nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:infer"
        [v "id", v "rule", v "parents", v "evidence", v "conclusion",
         v "relevance"])
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [id, formula, provenance, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.inferAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.inferAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded, DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.dropFaultTransition record rest nodes
      nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [v "id"])
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [id, formula, provenance, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.dropFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.dropFaultTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded, DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]
  · apply generic_lifted_record_rule_empty_of_decode_mismatch host
      DerivationCheckMachineLanguageDef.dropAcceptTransition record rest nodes
      nextId root serviceState
      (DerivationCheckMachineLanguageDef.a "dcm:drop" [v "id"])
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [id, formula, provenance, relevance])
    · simp [sourceInstruction?,
        DerivationCheckMachineLanguageDef.dropAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v,
        DerivationWordMachineLanguageDef.v]
    · simp [liftLeft, liftPattern,
        DerivationCheckMachineLanguageDef.dropAcceptTransition,
        DerivationCheckMachineLanguageDef.run,
        DerivationCheckMachineLanguageDef.instructionsCons,
        DerivationCheckMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.v, run, recordsCons, v,
        DerivationWordMachineLanguageDef.a]
    · exact recordDecoded
    · simp [inputStartBindings, decoded, DerivationWordMachineLanguageDef.a,
        DerivationCheckMachineLanguageDef.a, v, applyBindings, matchPattern,
        matchArgs]

#print axioms generic_non_input_lifted_rule_empty

theorem malformed_record_applyRule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceState actualInstruction : Pattern)
    (recordDecoded :
      decodeDecision host record = decoded actualInstruction) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) malformedRecordTransition
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    malformedRecordTransition, query, v, run, recordsCons, decoded,
    decodeRejected, DerivationWordMachineLanguageDef.a, relationEnv,
    relationTuples, recordDecoded, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms malformed_record_applyRule_empty

theorem missing_finish_applyRule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId root serviceState : Pattern) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.missingFinishTransition)
      (run (recordsCons record rest) nodes nextId root serviceState) = [] := by
  simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft, liftPattern,
    DerivationCheckMachineLanguageDef.missingFinishTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    run, recordsCons, recordsNil, DerivationWordMachineLanguageDef.a,
    matchPattern, matchArgs, mergeBindings]

#print axioms missing_finish_applyRule_empty

theorem duplicate_root_on_root_none_applyRule_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record rest nodes nextId serviceState : Pattern) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => [])
      (liftRewrite DerivationCheckMachineLanguageDef.duplicateRootTransition)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) = [] := by
  simp [applyRuleUsing, premisesUsing, premiseStepUsing, engineBasePremises,
    liftRewrite, sourceInstruction?, liftLeft, liftPattern,
    DerivationCheckMachineLanguageDef.duplicateRootTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    query, v, run, recordsCons, decoded, DerivationWordMachineLanguageDef.a,
    relationEnv, relationTuples, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples, matchRelationArgs,
    matchRelationArgument, matchPattern, matchArgs, mergeBindings,
    applyBindings, Bindings.lookup]

#print axioms duplicate_root_on_root_none_applyRule_empty

theorem root_rules_on_input_record_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId serviceState id formula provenance relevance :
      Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.rootAcceptTransition])
    (recordDecoded :
      decodeDecision host record =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [id, formula, provenance, relevance])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.rootFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, matchRelationArgs, matchRelationArgument,
      matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]
  · simp [applyRuleUsing, premisesUsing, premiseStepUsing,
      engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern, liftPremise,
      DerivationCheckMachineLanguageDef.rootAcceptTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      DerivationCheckMachineLanguageDef.query,
      query, v, run, recordsCons, decoded,
      DerivationWordMachineLanguageDef.a, relationEnv, relationTuples,
      recordDecoded, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, matchRelationArgs, matchRelationArgument,
      matchPattern, matchArgs, mergeBindings, applyBindings, Bindings.lookup]

#print axioms root_rules_on_input_record_empty

theorem finish_root_some_rules_on_root_none_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record rest nodes nextId serviceState : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition]) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons record rest) nodes nextId
        DerivationCheckMachineLanguageDef.rootNone serviceState) = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern,
      DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.instructionsNil,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.rootSome,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      run, recordsCons, recordsNil, DerivationWordMachineLanguageDef.a,
      matchPattern, matchArgs, mergeBindings]
  · simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern,
      DerivationCheckMachineLanguageDef.finishRootFaultTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.instructionsNil,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.rootSome,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      run, recordsCons, recordsNil, DerivationWordMachineLanguageDef.a,
      matchPattern, matchArgs, mergeBindings]
  · simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
      liftPattern,
      DerivationCheckMachineLanguageDef.finishVerifiedTransition,
      DerivationCheckMachineLanguageDef.run,
      DerivationCheckMachineLanguageDef.instructionsCons,
      DerivationCheckMachineLanguageDef.instructionsNil,
      DerivationCheckMachineLanguageDef.rootNone,
      DerivationCheckMachineLanguageDef.rootSome,
      DerivationCheckMachineLanguageDef.a,
      DerivationCheckMachineLanguageDef.v,
      run, recordsCons, recordsNil, DerivationWordMachineLanguageDef.a,
      matchPattern, matchArgs, mergeBindings]

#print axioms finish_root_some_rules_on_root_none_empty

theorem finish_shape_rules_on_input_record_empty
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sourceRule : RewriteRule)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextId serviceState id formula provenance relevance : Pattern)
    (membership : sourceRule ∈ [
      DerivationCheckMachineLanguageDef.finishTrailingTransition,
      DerivationCheckMachineLanguageDef.finishMissingRootTransition])
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [id, formula, provenance, relevance])) :
    applyRuleUsing (engineBasePremises (relationEnv host)) language
      (fun _ => []) (liftRewrite sourceRule)
      (run (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
        nodes nextId DerivationCheckMachineLanguageDef.rootNone serviceState) =
      [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  · cases remainingRecords with
    | nil =>
        simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishTrailingTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          run, recordsCons, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, matchPattern, matchArgs,
          mergeBindings]
    | cons nextRecord trailingRecords =>
        simp [applyRuleUsing, premisesUsing, premiseStepUsing,
          engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishTrailingTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          query, v, run, recordsCons, recordsPattern, decoded,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, relationEnv, relationTuples,
          recordDecoded, premiseStepWithEnv, relationQueryStep,
          builtinRelationTuples, matchRelationArgs, matchRelationArgument,
          matchPattern, matchArgs, mergeBindings, applyBindings,
          Bindings.lookup]
  · cases remainingRecords with
    | nil =>
        simp [applyRuleUsing, premisesUsing, premiseStepUsing,
          engineBasePremises, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishMissingRootTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.instructionsNil,
          DerivationCheckMachineLanguageDef.rootNone,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          query, v, run, recordsCons, recordsNil, recordsPattern, decoded,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, relationEnv, relationTuples,
          recordDecoded, premiseStepWithEnv, relationQueryStep,
          builtinRelationTuples, matchRelationArgs, matchRelationArgument,
          matchPattern, matchArgs, mergeBindings, applyBindings,
          Bindings.lookup]
    | cons nextRecord trailingRecords =>
        simp [applyRuleUsing, liftRewrite, sourceInstruction?, liftLeft,
          liftPattern,
          DerivationCheckMachineLanguageDef.finishMissingRootTransition,
          DerivationCheckMachineLanguageDef.run,
          DerivationCheckMachineLanguageDef.instructionsCons,
          DerivationCheckMachineLanguageDef.instructionsNil,
          DerivationCheckMachineLanguageDef.rootNone,
          DerivationCheckMachineLanguageDef.a,
          DerivationCheckMachineLanguageDef.v,
          run, recordsCons, recordsNil, recordsPattern,
          DerivationWordMachineLanguageDef.a,
          DerivationWordMachineRelationEnv.a, matchPattern, matchArgs,
          mergeBindings]

#print axioms finish_shape_rules_on_input_record_empty

/-- A decoded input record restricts the full authored transition table to the
four input rows.  This is the reusable no-invention partition: semantic input
cases need only decide which one of those four rows succeeds. -/
theorem input_record_rewriteAt_partition
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern formulaPattern
      provenancePattern relevancePatternValue : Pattern)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue])) :
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodes nextIdPattern DerivationCheckMachineLanguageDef.rootNone
      serviceStatePattern
    rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
      applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputIndexFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite
            DerivationCheckMachineLanguageDef.inputDecisionFaultTransition)
          source ++
        applyRuleUsing (engineBasePremises (relationEnv host)) language
          (fun _ => [])
          (liftRewrite DerivationCheckMachineLanguageDef.inputAcceptTransition)
          source := by
  dsimp only
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextIdPattern
          DerivationCheckMachineLanguageDef.rootNone
          serviceStatePattern)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    (DerivationCheckMachineLanguageDef.a "dcm:input"
      [idPattern, formulaPattern, provenancePattern, relevancePatternValue])
    recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [duplicate_root_on_root_none_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern serviceStatePattern]
  rw [root_rules_on_input_record_empty host
    DerivationCheckMachineLanguageDef.rootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp) recordDecoded]
  rw [root_rules_on_input_record_empty host
    DerivationCheckMachineLanguageDef.rootAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp) recordDecoded]
  rw [finish_shape_rules_on_input_record_empty host
    DerivationCheckMachineLanguageDef.finishTrailingTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue (by simp)
    recordDecoded]
  rw [finish_shape_rules_on_input_record_empty host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue (by simp)
    recordDecoded]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern (by simp)]
  simp

#print axioms input_record_rewriteAt_partition

/-- An index mismatch is the unique whole-relation successor for an input
record.  Later relevance and calculus services are not consulted. -/
theorem input_index_fault_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern formulaPattern
      provenancePattern relevancePatternValue faultPatternValue : Pattern)
    (expectedId actualId : Nat)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (indexFaulted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextIdPattern
        DerivationCheckMachineLanguageDef.rootNone serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  rw [input_record_rewriteAt_partition host record remainingRecords nodes
    nextIdPattern serviceStatePattern idPattern formulaPattern
    provenancePattern relevancePatternValue recordDecoded]
  rw [input_index_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue faultPatternValue
    expectedId actualId recordDecoded nextIdDecoded idDecoded indexFaulted]
  rw [input_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue faultPatternValue
    expectedId actualId (by simp [inputIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  rw [input_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue faultPatternValue
    expectedId actualId (by simp [inputIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  rw [input_index_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue faultPatternValue
    expectedId actualId (by simp [inputIndexSuccessSourceRules]) recordDecoded
    nextIdDecoded idDecoded indexFaulted]
  simp

#print axioms input_index_fault_rewriteAt_exact

/-- An input index mismatch commutes with the semantic machine and the actual
authored word-machine relation.  The semantic machine halts before relevance
or calculus services run, and the target retains the unchanged node receipt. -/
theorem input_index_fault_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (expectedId actualId : Nat) (formula : Formula)
    (provenance : Provenance) (relevance : RelevanceWitness)
    (serviceState : ServiceState)
    (formulaPattern provenancePattern serviceStatePattern nodesPatternValue :
      Pattern)
    (idsDiffer : actualId ≠ expectedId)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input actualId formula provenance relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (formulaEncoded : encodeFormula? host formula = some formulaPattern)
    (provenanceEncoded :
      encodeProvenance? host provenance = some provenancePattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .input actualId formula provenance relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := expectedId
      root? := none
      serviceState := serviceState
    }
    let failure := Fault.badNodeId expectedId actualId
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern expectedId)
      DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.halted (.fault failure))
        target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host
          (.input actualId formula provenance relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern actualId, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    simp [instructionPattern?, formulaEncoded, provenanceEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern actualId, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern actualId, formulaPattern, provenancePattern,
           relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.input actualId formula provenance relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [indexPattern actualId, formulaPattern, provenancePattern,
         relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have expectedIdDiffers : expectedId ≠ actualId := Ne.symm idsDiffer
  have indexFaulted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern (.badNodeId expectedId actualId)) := by
    simp [indexDecision, expectedIdDiffers, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · constructor
    · simp [DerivationCheckMachineBinary.decodeProgramUsing?,
        recordInstructionDecoded, remainingDecoded]
    · simp [runningPattern?, nodesEncoded, serviceStateEncoded, rootPattern?,
        recordsPattern, recordsCons, DerivationWordMachineLanguageDef.a,
        DerivationWordMachineRelationEnv.a]
  constructor
  · simp [step?, advance, replaceInstructions, haltFault, idsDiffer]
  constructor
  · exact input_index_fault_rewriteAt_exact host record remainingRecords
      nodesPatternValue (indexPattern expectedId) serviceStatePattern
      (indexPattern actualId) formulaPattern provenancePattern
      (relevancePattern relevance)
      (faultPattern (.badNodeId expectedId actualId)) expectedId actualId
      recordDecoded (decodeIndex_indexPattern expectedId)
      (decodeIndex_indexPattern actualId) indexFaulted
  · refine ⟨oldNodes, ?_⟩
    constructor
    simp [haltedPattern?, outcomePattern?, nodesEncoded, faultPattern,
      halted, DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]

#print axioms input_index_fault_semantic_square

theorem input_relevance_fault_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern formulaPattern
      provenancePattern relevancePatternValue advancedPattern
      faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceFaulted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextIdPattern
        DerivationCheckMachineLanguageDef.rootNone serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  rw [input_record_rewriteAt_partition host record remainingRecords nodes
    nextIdPattern serviceStatePattern idPattern formulaPattern
    provenancePattern relevancePatternValue recordDecoded]
  rw [input_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    expectedId actualId recordDecoded nextIdDecoded idDecoded indexAccepted]
  rw [input_relevance_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    faultPatternValue expectedId actualId relevance recordDecoded
    nextIdDecoded idDecoded relevanceDecoded indexAccepted relevanceFaulted]
  rw [input_relevance_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    faultPatternValue expectedId actualId relevance
    (by simp [inputRelevanceSuccessSourceRules]) recordDecoded nextIdDecoded
    idDecoded relevanceDecoded indexAccepted relevanceFaulted]
  rw [input_relevance_fault_excludes_later_rule host
    DerivationCheckMachineLanguageDef.inputAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    faultPatternValue expectedId actualId relevance
    (by simp [inputRelevanceSuccessSourceRules]) recordDecoded nextIdDecoded
    idDecoded relevanceDecoded indexAccepted relevanceFaulted]
  simp

#print axioms input_relevance_fault_rewriteAt_exact

theorem input_relevance_fault_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (id : Nat) (formula : Formula) (provenance : Provenance)
    (relevance : RelevanceWitness) (serviceState : ServiceState)
    (formulaPattern provenancePattern serviceStatePattern nodesPatternValue :
      Pattern)
    (relevanceMalformed : relevance.wellFormedFor id = false)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input id formula provenance relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (formulaEncoded : encodeFormula? host formula = some formulaPattern)
    (provenanceEncoded :
      encodeProvenance? host provenance = some provenancePattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .input id formula provenance relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := id
      root? := none
      serviceState := serviceState
    }
    let failure := Fault.malformedRelevance id
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern id)
      DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.halted (.fault failure))
        target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.input id formula provenance relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    simp [instructionPattern?, formulaEncoded, provenanceEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.input id formula provenance relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [indexPattern id, formulaPattern, provenancePattern,
         relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have indexAccepted :
      indexDecision id id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [indexPattern (id + 1)] := by
    simp [indexDecision, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have relevanceFaulted :
      relevanceDecision id relevance =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern (.malformedRelevance id)) := by
    simp [relevanceDecision, relevanceMalformed, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · constructor
    · simp [DerivationCheckMachineBinary.decodeProgramUsing?,
        recordInstructionDecoded, remainingDecoded]
    · simp [runningPattern?, nodesEncoded, serviceStateEncoded, rootPattern?,
        recordsPattern, recordsCons, DerivationWordMachineLanguageDef.a,
        DerivationWordMachineRelationEnv.a]
  constructor
  · simp [step?, advance, replaceInstructions, haltFault,
      relevanceMalformed]
  constructor
  · exact input_relevance_fault_rewriteAt_exact host record remainingRecords
      nodesPatternValue (indexPattern id) serviceStatePattern
      (indexPattern id) formulaPattern provenancePattern
      (relevancePattern relevance) (indexPattern (id + 1))
      (faultPattern (.malformedRelevance id)) id id relevance recordDecoded
      (decodeIndex_indexPattern id) (decodeIndex_indexPattern id)
      (decodeRelevance_relevancePattern relevance) indexAccepted
      relevanceFaulted
  · refine ⟨oldNodes, ?_⟩
    constructor
    simp [haltedPattern?, outcomePattern?, nodesEncoded, faultPattern,
      halted, DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]

#print axioms input_relevance_fault_semantic_square

theorem input_decision_fault_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern formulaPattern
      provenancePattern relevancePatternValue advancedPattern
      faultPatternValue : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (serviceState : ServiceState) (provenance : Provenance)
    (formula : Formula)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (inputFaulted :
      inputDecision host actualId serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionFault
          faultPatternValue) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextIdPattern
        DerivationCheckMachineLanguageDef.rootNone serviceStatePattern) =
      [halted
        (DerivationCheckMachineLanguageDef.outcomeFault faultPatternValue)
        nodes] := by
  rw [input_record_rewriteAt_partition host record remainingRecords nodes
    nextIdPattern serviceStatePattern idPattern formulaPattern
    provenancePattern relevancePatternValue recordDecoded]
  rw [input_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    expectedId actualId recordDecoded nextIdDecoded idDecoded indexAccepted]
  rw [input_relevance_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    expectedId actualId relevance recordDecoded nextIdDecoded idDecoded
    relevanceDecoded indexAccepted relevanceAccepted]
  rw [input_decision_fault_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    faultPatternValue expectedId actualId relevance serviceState provenance
    formula recordDecoded nextIdDecoded idDecoded relevanceDecoded
    serviceStateDecoded provenanceDecoded formulaDecoded indexAccepted
    relevanceAccepted inputFaulted]
  rw [input_decision_fault_excludes_accept host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    faultPatternValue expectedId actualId relevance serviceState provenance
    formula recordDecoded nextIdDecoded idDecoded relevanceDecoded
    serviceStateDecoded provenanceDecoded formulaDecoded indexAccepted
    relevanceAccepted inputFaulted]
  simp

#print axioms input_decision_fault_rewriteAt_exact

theorem input_decision_fault_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (id : Nat) (formula : Formula) (provenance : Provenance)
    (relevance : RelevanceWitness) (serviceState : ServiceState)
    (formulaPattern provenancePattern serviceStatePattern nodesPatternValue :
      Pattern)
    (relevanceWellFormed : relevance.wellFormedFor id = true)
    (serviceRejected :
      host.services.input serviceState provenance formula = none)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input id formula provenance relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (formulaEncoded : encodeFormula? host formula = some formulaPattern)
    (provenanceEncoded :
      encodeProvenance? host provenance = some provenancePattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .input id formula provenance relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := id
      root? := none
      serviceState := serviceState
    }
    let failure := Fault.inputRejected id
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern id)
      DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault (faultPattern failure))
      nodesPatternValue
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault failure)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.halted (.fault failure))
        target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.input id formula provenance relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    simp [instructionPattern?, formulaEncoded, provenanceEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.input id formula provenance relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [indexPattern id, formulaPattern, provenancePattern,
         relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have serviceStateDecoded :=
    decodeServiceState_encodeServiceState host serviceState
      serviceStatePattern serviceStateEncoded
  have formulaDecoded :=
    decodeFormula_encodeFormula host formula formulaPattern formulaEncoded
  have provenanceDecoded :=
    decodeProvenance_encodeProvenance host provenance provenancePattern
      provenanceEncoded
  have indexAccepted :
      indexDecision id id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [indexPattern (id + 1)] := by
    simp [indexDecision, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have relevanceAccepted :
      relevanceDecision id relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept" := by
    simp [relevanceDecision, relevanceWellFormed,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have inputFaulted :
      inputDecision host id serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionFault
          (faultPattern (.inputRejected id)) := by
    simp [inputDecision, serviceRejected, decisionFault,
      DerivationCheckMachineLanguageDef.decisionFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · constructor
    · simp [DerivationCheckMachineBinary.decodeProgramUsing?,
        recordInstructionDecoded, remainingDecoded]
    · simp [runningPattern?, nodesEncoded, serviceStateEncoded, rootPattern?,
        recordsPattern, recordsCons, DerivationWordMachineLanguageDef.a,
        DerivationWordMachineRelationEnv.a]
  constructor
  · simp [step?, advance, replaceInstructions, haltFault,
      relevanceWellFormed, serviceRejected]
  constructor
  · exact input_decision_fault_rewriteAt_exact host record remainingRecords
      nodesPatternValue (indexPattern id) serviceStatePattern
      (indexPattern id) formulaPattern provenancePattern
      (relevancePattern relevance) (indexPattern (id + 1))
      (faultPattern (.inputRejected id)) id id relevance serviceState
      provenance formula recordDecoded (decodeIndex_indexPattern id)
      (decodeIndex_indexPattern id)
      (decodeRelevance_relevancePattern relevance) serviceStateDecoded
      provenanceDecoded formulaDecoded indexAccepted relevanceAccepted
      inputFaulted
  · refine ⟨oldNodes, ?_⟩
    constructor
    simp [haltedPattern?, outcomePattern?, nodesEncoded, faultPattern,
      halted, DerivationCheckMachineLanguageDef.outcomeFault,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]

#print axioms input_decision_fault_semantic_square

/-- For an admitted input record, the whole authored one-step relation has
exactly the accepted successor.  This strengthens positive simulation to
no-invention: no fault or transition for another instruction contributes a
second reduct. -/
theorem input_accept_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (nodes nextIdPattern serviceStatePattern idPattern
      formulaPattern provenancePattern relevancePatternValue advancedPattern
      nextServiceStatePattern : Pattern)
    (expectedId actualId : Nat) (relevance : RelevanceWitness)
    (serviceState : ServiceState)
    (provenance : Provenance) (formula : Formula)
    (recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [idPattern, formulaPattern, provenancePattern,
           relevancePatternValue]))
    (nextIdDecoded : decodeIndex? nextIdPattern = some expectedId)
    (idDecoded : decodeIndex? idPattern = some actualId)
    (relevanceDecoded :
      decodeRelevance? relevancePatternValue = some relevance)
    (serviceStateDecoded :
      decodeServiceState? host serviceStatePattern = some serviceState)
    (provenanceDecoded :
      decodeProvenance? host provenancePattern = some provenance)
    (formulaDecoded : decodeFormula? host formulaPattern = some formula)
    (indexAccepted :
      indexDecision expectedId actualId =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [advancedPattern])
    (relevanceAccepted :
      relevanceDecision actualId relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept")
    (inputAccepted :
      inputDecision host actualId serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run (recordsCons (wordsPattern record)
        (recordsPattern remainingRecords)) nodes nextIdPattern
        DerivationCheckMachineLanguageDef.rootNone serviceStatePattern) =
      [run (recordsPattern remainingRecords)
        (DerivationCheckMachineLanguageDef.nodesCons
          (DerivationCheckMachineLanguageDef.node idPattern formulaPattern
            relevancePatternValue
            (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
          nodes)
        advancedPattern DerivationCheckMachineLanguageDef.rootNone
        nextServiceStatePattern] := by
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run (recordsCons (wordsPattern record)
          (recordsPattern remainingRecords)) nodes nextIdPattern
          DerivationCheckMachineLanguageDef.rootNone
          serviceStatePattern)) = _
  rw [show language.rewrites = transitions by rfl]
  simp only [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil]
  rw [malformed_record_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    (DerivationCheckMachineLanguageDef.a "dcm:input"
      [idPattern, formulaPattern, provenancePattern, relevancePatternValue])
    recordDecoded]
  rw [missing_finish_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern]
  rw [input_index_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    expectedId actualId recordDecoded nextIdDecoded idDecoded indexAccepted]
  rw [input_relevance_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    expectedId actualId relevance recordDecoded nextIdDecoded idDecoded
    relevanceDecoded indexAccepted relevanceAccepted]
  rw [input_decision_fault_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue advancedPattern
    nextServiceStatePattern expectedId actualId relevance serviceState
    provenance formula recordDecoded nextIdDecoded idDecoded relevanceDecoded
    serviceStateDecoded provenanceDecoded formulaDecoded indexAccepted
    relevanceAccepted inputAccepted]
  rw [input_accept_applyRule_exact host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern
    relevancePatternValue advancedPattern nextServiceStatePattern expectedId
    actualId relevance serviceState provenance formula recordDecoded
    nextIdDecoded idDecoded relevanceDecoded serviceStateDecoded
    provenanceDecoded formulaDecoded indexAccepted relevanceAccepted
    inputAccepted]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferParentFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.inferAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [generic_non_input_lifted_rule_empty host
    DerivationCheckMachineLanguageDef.dropAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    DerivationCheckMachineLanguageDef.rootNone serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue
    (by simp [genericNonInputSourceRules]) recordDecoded]
  rw [duplicate_root_on_root_none_applyRule_empty host (wordsPattern record)
    (recordsPattern remainingRecords) nodes nextIdPattern serviceStatePattern]
  rw [root_rules_on_input_record_empty host
    DerivationCheckMachineLanguageDef.rootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp) recordDecoded]
  rw [root_rules_on_input_record_empty host
    DerivationCheckMachineLanguageDef.rootAcceptTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern idPattern formulaPattern provenancePattern
    relevancePatternValue (by simp) recordDecoded]
  rw [finish_shape_rules_on_input_record_empty host
    DerivationCheckMachineLanguageDef.finishTrailingTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue (by simp)
    recordDecoded]
  rw [finish_shape_rules_on_input_record_empty host
    DerivationCheckMachineLanguageDef.finishMissingRootTransition record
    remainingRecords nodes nextIdPattern serviceStatePattern idPattern
    formulaPattern provenancePattern relevancePatternValue (by simp)
    recordDecoded]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishRootFaultTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern (by simp)]
  rw [finish_root_some_rules_on_root_none_empty host
    DerivationCheckMachineLanguageDef.finishVerifiedTransition
    (wordsPattern record) (recordsPattern remainingRecords) nodes nextIdPattern
    serviceStatePattern (by simp)]
  simp

#print axioms input_accept_rewriteAt_exact

/-- One accepted input record forms an exact operational square.  The compact
word stream decodes to the semantic instruction stream, the semantic machine
and the authored word-machine presentation take their respective steps, the
authored relation has exactly one reduct, and that reduct encodes the resulting
semantic state.  No fixture-specific evaluator normalization is involved. -/
theorem input_accept_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (record : DerivationCheckMachineBinary.WordRecord)
    (remainingRecords : DerivationCheckMachineBinary.WordProgram)
    (remainingInstructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (oldNodes : List (Node Formula))
    (id : Nat) (formula : Formula) (provenance : Provenance)
    (relevance : RelevanceWitness)
    (serviceState nextServiceState : ServiceState)
    (formulaPattern provenancePattern serviceStatePattern
      nextServiceStatePattern nodesPatternValue : Pattern)
    (recordInstructionDecoded :
      DerivationCheckMachineBinary.decodeInstructionUsing?
          host.codecs.decoders record =
        some (.input id formula provenance relevance))
    (remainingDecoded :
      DerivationCheckMachineBinary.decodeProgramUsing?
          host.codecs.decoders remainingRecords =
        some remainingInstructions)
    (formulaEncoded : encodeFormula? host formula = some formulaPattern)
    (provenanceEncoded :
      encodeProvenance? host provenance = some provenancePattern)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nextServiceStateEncoded :
      encodeServiceState? host nextServiceState =
        some nextServiceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue)
    (relevanceWellFormed : relevance.wellFormedFor id = true)
    (serviceAccepted :
      host.services.input serviceState provenance formula =
        some nextServiceState) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := .input id formula provenance relevance ::
        remainingInstructions
      nodes := oldNodes
      nextId := id
      root? := none
      serviceState := serviceState
    }
    let after :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := remainingInstructions
      nodes := { id, formula, relevance } :: oldNodes
      nextId := id + 1
      root? := none
      serviceState := nextServiceState
    }
    let source := run
      (recordsCons (wordsPattern record) (recordsPattern remainingRecords))
      nodesPatternValue (indexPattern id)
      DerivationCheckMachineLanguageDef.rootNone serviceStatePattern
    let target := run (recordsPattern remainingRecords)
      (DerivationCheckMachineLanguageDef.nodesCons
        (DerivationCheckMachineLanguageDef.node (indexPattern id)
          formulaPattern (relevancePattern relevance)
          (DerivationCheckMachineLanguageDef.a "dcm:unlinked"))
        nodesPatternValue)
      (indexPattern (id + 1)) DerivationCheckMachineLanguageDef.rootNone
      nextServiceStatePattern
    EncodesConfig host (record :: remainingRecords) (.running before) source ∧
      step? host.services (.running before) = some (.running after) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host remainingRecords (.running after) target := by
  dsimp only
  have instructionPatternEncoded :
      instructionPattern? host (.input id formula provenance relevance) =
        some (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    simp [instructionPattern?, formulaEncoded, provenanceEncoded,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have recordDecoded :
      decodeDecision host (wordsPattern record) =
        decoded (DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]) := by
    change decodeDecision host (wordsPattern record) =
      DerivationWordMachineRelationEnv.a "dwm:decoded"
        [DerivationCheckMachineLanguageDef.a "dcm:input"
          [indexPattern id, formulaPattern, provenancePattern,
           relevancePattern relevance]]
    exact decodeDecision_wordsPattern_exact host record
      (.input id formula provenance relevance)
      (DerivationCheckMachineLanguageDef.a "dcm:input"
        [indexPattern id, formulaPattern, provenancePattern,
         relevancePattern relevance])
      recordInstructionDecoded instructionPatternEncoded
  have serviceStateDecoded :=
    decodeServiceState_encodeServiceState host serviceState
      serviceStatePattern serviceStateEncoded
  have formulaDecoded :=
    decodeFormula_encodeFormula host formula formulaPattern formulaEncoded
  have provenanceDecoded :=
    decodeProvenance_encodeProvenance host provenance provenancePattern
      provenanceEncoded
  have indexAccepted :
      indexDecision id id =
        DerivationCheckMachineLanguageDef.a "dcm:decision-index"
          [indexPattern (id + 1)] := by
    simp [indexDecision, DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have relevanceAccepted :
      relevanceDecision id relevance =
        DerivationCheckMachineLanguageDef.a "dcm:decision-accept" := by
    simp [relevanceDecision, relevanceWellFormed,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  have inputAccepted :
      inputDecision host id serviceState provenance formula =
        DerivationCheckMachineLanguageDef.decisionState
          nextServiceStatePattern := by
    simp [inputDecision, serviceAccepted, nextServiceStateEncoded,
      DerivationCheckMachineLanguageDef.decisionState,
      DerivationCheckMachineLanguageDef.a,
      DerivationWordMachineRelationEnv.a]
  constructor
  · constructor
    · simp [DerivationCheckMachineBinary.decodeProgramUsing?,
        recordInstructionDecoded, remainingDecoded]
    · simp [runningPattern?, nodesEncoded, serviceStateEncoded, rootPattern?,
        recordsPattern, recordsCons, DerivationWordMachineLanguageDef.a,
        DerivationWordMachineRelationEnv.a]
  constructor
  · simp [step?, advance, replaceInstructions, relevanceWellFormed,
      serviceAccepted]
  constructor
  · exact input_accept_rewriteAt_exact host record remainingRecords
      nodesPatternValue (indexPattern id) serviceStatePattern
      (indexPattern id) formulaPattern provenancePattern
      (relevancePattern relevance) (indexPattern (id + 1))
      nextServiceStatePattern id id relevance serviceState provenance formula
      recordDecoded (decodeIndex_indexPattern id) (decodeIndex_indexPattern id)
      (decodeRelevance_relevancePattern relevance) serviceStateDecoded
      provenanceDecoded formulaDecoded indexAccepted relevanceAccepted
      inputAccepted
  · constructor
    · exact remainingDecoded
    · simp [runningPattern?, nodesPattern?, nodePattern?, formulaEncoded,
        nodesEncoded, nextServiceStateEncoded, rootPattern?, linkPattern,
        DerivationCheckMachineLanguageDef.nodesCons,
        DerivationCheckMachineLanguageDef.node,
        DerivationCheckMachineLanguageDef.a,
        DerivationWordMachineRelationEnv.a]

#print axioms input_accept_semantic_square

/-- Halted terms have no authored successor.  This is structural: every
transition is rooted at `dwm:run`, so no relation query or calculus service is
consulted. -/
theorem halted_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (outcome nodes : Pattern) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (halted outcome nodes) = [] := by
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule (halted outcome nodes)) = []
  rw [show language.rewrites = transitions by rfl]
  simp [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, applyRuleUsing,
    malformedRecordTransition, liftRewrite, liftLeft, liftPattern,
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
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v,
    run, halted, recordsNil, recordsCons,
    DerivationWordMachineLanguageDef.a, v, matchPattern]

#print axioms halted_rewriteAt_exact

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation
