import Mettapedia.Languages.Metamath.InferenceSourceAdmission
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

/-!
# MeTTa serialization for generated inference presentations

This executable renderer transports a validated generic inference definition
and its raw proof trees into the data format consumed by the operational MIK
checker.  Every source-backed export enters through canonical source admission.
-/

namespace Mettapedia.Languages.Metamath.InferenceMeTTaExport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceEncoding.Builder
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSourceAdmission

private structure RenderedDagNode where
  id : Nat
  ruleInstance : RuleInstance
  children : List Nat

private structure DagRenderState where
  cache : List (String × Nat) := []
  nodes : List RenderedDagNode := []

private def cachedNode? (cache : List (String × Nat)) (key : String) :
    Option Nat :=
  (cache.find? fun entry => entry.1 == key).map (·.2)

mutual

private def internRawProof : RawProof → DagRenderState → Nat × DagRenderState
  | proof, state =>
      let key := renderRawProof proof
      match cachedNode? state.cache key with
      | some id => (id, state)
      | none =>
          match proof with
          | .node ruleInstance children =>
              let (childIds, state) := internRawProofs children state
              let id := state.nodes.length
              let node : RenderedDagNode := { id, ruleInstance, children := childIds }
              (id,
                { cache := (key, id) :: state.cache
                  nodes := state.nodes ++ [node] })
termination_by proof _state => 2 * sizeOf proof
decreasing_by all_goals simp_wf; omega

private def internRawProofs :
    List RawProof → DagRenderState → List Nat × DagRenderState
  | proofs, state =>
      match proofs with
      | [] => ([], state)
      | proof :: proofs =>
          let (id, state) := internRawProof proof state
          let (ids, state) := internRawProofs proofs state
          (id :: ids, state)
termination_by proofs _state => 2 * sizeOf proofs + 1

end


private def dagNodeName (id : Nat) : String := s!"n{id}"

private def renderDagRefList : List Nat → String
  | [] => "DrNil"
  | id :: ids =>
      s!"(DrCons {quote (dagNodeName id)} {renderDagRefList ids})"

private def renderDagNode (node : RenderedDagNode) : String :=
  s!"(GDNode {quote (dagNodeName node.id)} " ++
    s!"{renderRuleInstance node.ruleInstance} " ++
    s!"{renderDagRefList node.children})"

private def renderDagNodes : List RenderedDagNode → String
  | [] => "DnNil"
  | node :: nodes =>
      s!"(DnCons {renderDagNode node} {renderDagNodes nodes})"

/-! ## Source-backed `demo0.mm` normal-proof lowering -/

private def proofNode (rule : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := { value := rule }, arguments } children

private def encodedBody (body : List RuntimeSym) : Pattern :=
  encodeListWith encodeSym body

private def encodedBindings
    (bindings : List (String × ConstantHeadedFormula)) : Pattern :=
  encodeListWith
    (fun binding =>
      Builder.binding (encodeString binding.1) (encodeFormula binding.2))
    bindings

private def concreteSubstitution
    (bindings : List (String × ConstantHeadedFormula)) : Pattern :=
  Builder.substitution (encodedBindings bindings)

private def appendProof : (left right : List RuntimeSym) → RawProof
  | [], right => proofNode "$mm.append.nil" [encodedBody right]
  | symbol :: left, right =>
      proofNode "$mm.append.cons"
        [ encodeSym symbol, encodedBody left, encodedBody right
        , encodedBody (left ++ right) ]
        [appendProof left right]

private def lookupBinding?
    (bindings : List (String × ConstantHeadedFormula))
    (variableName : String) : Option ConstantHeadedFormula :=
  bindings.find? (fun binding => binding.1 == variableName) |>.map (·.2)

private def lookupProof :
    (bindings : List (String × ConstantHeadedFormula)) →
    (variableName : String) → Except String (ConstantHeadedFormula × RawProof)
  | [], variableName =>
      throw s!"missing substitution binding for {variableName}"
  | binding :: bindings, variableName => do
      if binding.1 == variableName then
        pure
          (binding.2,
            proofNode "$mm.lookup.here"
              [ encodeString variableName, encodeString binding.2.typecode
              , encodedBody binding.2.body, encodedBindings bindings ])
      else
        let (image, child) ← lookupProof bindings variableName
        pure
          (image,
            proofNode "$mm.lookup.there"
              [ encodedBindings bindings, encodeString variableName
              , encodeString image.typecode, encodedBody image.body
              , encodeString binding.1, encodeString binding.2.typecode
              , encodedBody binding.2.body ]
              [child])

private def substBodyProof
    (bindings : List (String × ConstantHeadedFormula)) :
    (source : List RuntimeSym) → Except String (List RuntimeSym × RawProof)
  | [] =>
      let substitution := concreteSubstitution bindings
      pure ([], proofNode "$mm.subst-body.nil" [substitution])
  | .const constantName :: source => do
      let substitution := concreteSubstitution bindings
      let (result, child) ← substBodyProof bindings source
      pure
        (.const constantName :: result,
          proofNode "$mm.subst-body.const"
            [ substitution, encodeString constantName
            , encodedBody source, encodedBody result ]
            [child])
  | .var variableName :: source => do
      let substitution := concreteSubstitution bindings
      let (image, lookupChild) ← lookupProof bindings variableName
      let (tailResult, tailChild) ← substBodyProof bindings source
      let result := image.body ++ tailResult
      pure
        (result,
          proofNode "$mm.subst-body.var"
            [ substitution, encodeString variableName
            , encodeString image.typecode, encodedBody image.body
            , encodedBody source, encodedBody tailResult, encodedBody result ]
            [lookupChild, tailChild, appendProof image.body tailResult])

private def applySubstitutionProof
    (bindings : List (String × ConstantHeadedFormula))
    (source : ConstantHeadedFormula) :
    Except String (ConstantHeadedFormula × RawProof) := do
  let (resultBody, child) ← substBodyProof bindings source.body
  let result : ConstantHeadedFormula := ⟨source.typecode, resultBody⟩
  pure
    (result,
      proofNode "$mm.apply-subst.formula"
        [ concreteSubstitution bindings, encodeString source.typecode
        , encodedBody source.body, encodedBody resultBody ]
        [child])

private def variablesProof :
    (body : List RuntimeSym) -> List String × RawProof
  | [] => ([], proofNode "$mm.vars.nil" [])
  | .const constantName :: body =>
      let (variableNames, child) := variablesProof body
      (variableNames,
        proofNode "$mm.vars.const"
          [ encodeString constantName, encodedBody body
          , encodeListWith encodeString variableNames ]
          [child])
  | .var variableName :: body =>
      let (variableNames, child) := variablesProof body
      (variableName :: variableNames,
        proofNode "$mm.vars.var"
          [ encodeString variableName, encodedBody body
          , encodeListWith encodeString variableNames ]
          [child])

private def dvMemberProof (target : String × String) :
    (values : List (String × String)) -> Except String RawProof
  | [] =>
      throw s!"required disjoint-variable pair {target} is absent from the caller frame"
  | value :: values =>
      if value == target then
        pure <| proofNode "$mm.member.here"
          [encodeDVPair target, encodeListWith encodeDVPair values]
      else do
        let child <- dvMemberProof target values
        pure <| proofNode "$mm.member.there"
          [ encodeDVPair target, encodeDVPair value
          , encodeListWith encodeDVPair values ]
          [child]

private def dvRelationProof (callerDV : List (String × String))
    (left right : String) : Except String RawProof :=
  let encodedCallerDV := encodeListWith encodeDVPair callerDV
  match dvMemberProof (left, right) callerDV with
  | .ok child =>
      .ok <| proofNode "$mm.dv-rel.forward"
        [encodedCallerDV, encodeString left, encodeString right] [child]
  | .error _ => do
      let child <- dvMemberProof (right, left) callerDV
      pure <| proofNode "$mm.dv-rel.reverse"
        [encodedCallerDV, encodeString left, encodeString right] [child]

private def allWithDVProof (callerDV : List (String × String))
    (left : String) : (rights : List String) -> Except String RawProof
  | [] =>
      pure <| proofNode "$mm.all-with.nil"
        [encodeListWith encodeDVPair callerDV, encodeString left]
  | right :: rights => do
      let relation <- dvRelationProof callerDV left right
      let tail <- allWithDVProof callerDV left rights
      pure <| proofNode "$mm.all-with.cons"
        [ encodeListWith encodeDVPair callerDV, encodeString left
        , encodeString right, encodeListWith encodeString rights ]
        [relation, tail]

private def allPairsDVProof (callerDV : List (String × String)) :
    (lefts rights : List String) -> Except String RawProof
  | [], rights =>
      pure <| proofNode "$mm.all-pairs.nil"
        [ encodeListWith encodeDVPair callerDV
        , encodeListWith encodeString rights ]
  | left :: lefts, rights => do
      let head <- allWithDVProof callerDV left rights
      let tail <- allPairsDVProof callerDV lefts rights
      pure <| proofNode "$mm.all-pairs.cons"
        [ encodeListWith encodeDVPair callerDV, encodeString left
        , encodeListWith encodeString lefts
        , encodeListWith encodeString rights ]
        [head, tail]

private def dvListsProof
    (bindings : List (String × ConstantHeadedFormula))
    (callerDV : List (String × String)) :
    (calleeDV : List (String × String)) -> Except String RawProof
  | [] =>
      pure <| proofNode "$mm.dv-lists.nil"
        [ concreteSubstitution bindings
        , encodeListWith encodeDVPair callerDV ]
  | (left, right) :: calleeDV => do
      let (leftImage, leftLookup) <- lookupProof bindings left
      let (rightImage, rightLookup) <- lookupProof bindings right
      let (leftVariables, leftVariablesProof) := variablesProof leftImage.body
      let (rightVariables, rightVariablesProof) := variablesProof rightImage.body
      let pairwise <- allPairsDVProof callerDV leftVariables rightVariables
      let tail <- dvListsProof bindings callerDV calleeDV
      pure <| proofNode "$mm.dv-lists.cons"
        [ concreteSubstitution bindings
        , encodeListWith encodeDVPair callerDV
        , encodeString left, encodeString right
        , encodeListWith encodeDVPair calleeDV
        , encodeString leftImage.typecode, encodedBody leftImage.body
        , encodeString rightImage.typecode, encodedBody rightImage.body
        , encodeListWith encodeString leftVariables
        , encodeListWith encodeString rightVariables ]
        [ leftLookup, rightLookup, leftVariablesProof, rightVariablesProof
        , pairwise, tail ]

private def generatedDVProof
    (bindings : List (String × ConstantHeadedFormula))
    (callerFrame calleeFrame : RuntimeFrame) : Except String RawProof := do
  let child <- dvListsProof bindings callerFrame.dj.toList calleeFrame.dj.toList
  pure <| proofNode "$mm.dv-ok.frames"
    [ concreteSubstitution bindings
    , encodeListWith encodeDVPair callerFrame.dj.toList
    , encodeListWith encodeString callerFrame.hyps.toList
    , encodeListWith encodeDVPair calleeFrame.dj.toList
    , encodeListWith encodeString calleeFrame.hyps.toList ]
    [child]

private structure LoweredStackEntry where
  formula : ConstantHeadedFormula
  proof : RawProof

private structure ExpandedProofEntry where
  formula : ConstantHeadedFormula
  actions : List String

private inductive ExpandedHeapEntry where
  | formula (entry : ExpandedProofEntry) (savedIndex : Option Nat)
  | assertion (label : String)

private structure CompressedExpansion where
  runtime : Metamath.Verify.ProofState
  heap : Array ExpandedHeapEntry
  stack : List ExpandedProofEntry
  actions : List String
  phase : Metamath.Verify.CompressedPhase
  saves : Nat
  savedReferences : Nat

private structure ProofActionExtraction where
  actions : List String
  saves : Nat := 0
  savedReferences : Nat := 0

private structure ObservedProofIngress where
  anchor : Metamath.Verify.ParserState
  initial : Metamath.Verify.ProofState
  tokens : List ByteSlice

private def mandatoryBindings
    (hypotheses : List HypothesisView)
    (entries : List LoweredStackEntry) :
    Except String (List (String × ConstantHeadedFormula)) := do
  unless hypotheses.length == entries.length do
    throw "mandatory hypothesis/stack suffix length mismatch"
  let pairs := hypotheses.zip entries
  pairs.foldlM (init := []) fun bindings pair =>
    match pair.1 with
    | .floating _ expectedTypecode variableName => do
        unless pair.2.formula.typecode == expectedTypecode do
          throw s!"floating hypothesis typecode mismatch for {variableName}"
        unless (lookupBinding? bindings variableName).isNone do
          throw s!"duplicate substitution binding for {variableName}"
        pure (bindings ++ [(variableName, pair.2.formula)])
    | .essential _ _ => pure bindings

private def essentialCheckProofs
    (bindings : List (String × ConstantHeadedFormula)) :
    List (HypothesisView × LoweredStackEntry) →
    Except String (List RawProof)
  | [] => pure []
  | (hypothesis, entry) :: pairs => do
      let proofs ← essentialCheckProofs bindings pairs
      match hypothesis with
      | .floating _ _ _ => pure proofs
      | .essential label source => do
          let (result, proof) ← applySubstitutionProof bindings source
          unless result == entry.formula do
            throw s!"essential hypothesis substitution mismatch at {label}"
          pure (proof :: proofs)

private def runtimeStackViews
    (stack : Array RuntimeFormula) : Option (List ConstantHeadedFormula) :=
  stack.toList.mapM ConstantHeadedFormula.ofRuntime?

private def proofIngressOfBoundary {sourceBytes : ByteArray}
    {targetLabel : String}
    (boundary : TargetBoundary sourceBytes targetLabel) : ObservedProofIngress :=
  { anchor := boundary.first.before
    initial := boundary.first.proofState
    tokens := boundary.proofTokens }

private def proofIngressOfChunkedBoundary {sourceBytes : ByteArray}
    {targetLabel : String}
    (boundary : ChunkedTargetBoundary sourceBytes targetLabel) : ObservedProofIngress :=
  { anchor := boundary.first.before
    initial := boundary.first.proofState
    tokens := boundary.proofTokens }

private def proofIngressOfParsed {sourceBytes : ByteArray}
    {targetLabel : Option String} :
    ParsedSource sourceBytes targetLabel -> Except String ObservedProofIngress
  | .database =>
      .error "the theorem request unexpectedly produced database-only admission"
  | .target _ boundary => .ok (proofIngressOfBoundary boundary)
  | .chunkedTarget _ boundary =>
      .ok (proofIngressOfChunkedBoundary boundary)

private def labelOfToken (token : ByteSlice) :
    Except String String :=
  let converted := Metamath.Verify.toLabel token
  if converted.1 then pure converted.2
  else throw s!"invalid proof label token {converted.2}"

private def heapEntryForLabel (db : RuntimeDB) (label : String) :
    Except String ExpandedHeapEntry :=
  match db.find? label with
  | some (.hyp _ formula _) => do
      let view ← match ConstantHeadedFormula.ofRuntime? formula with
        | some value => pure value
        | none => throw s!"preloaded hypothesis {label} is not constant-headed"
      pure (.formula { formula := view, actions := [label] } none)
  | some (.assert ..) => pure (.assertion label)
  | _ => throw s!"preloaded proof label {label} is not a hypothesis or assertion"

private def stackMatchesRuntime
    (runtime : Metamath.Verify.ProofState)
    (stack : List ExpandedProofEntry) : Bool :=
  runtimeStackViews runtime.stack == some (stack.map (·.formula))

private def applyCompressedAction (db : RuntimeDB)
    (state : CompressedExpansion) : Metamath.Verify.ParserState.CompressedAction →
    Except String CompressedExpansion
  | .unknown => throw "unknown compressed proof action is outside the strict profile"
  | .save => do
      let top ← match state.stack.getLast? with
        | some value => pure value
        | none => throw "compressed save encountered an empty lowered stack"
      let runtime ← match state.runtime.save with
        | .ok value => pure value
        | .error error => throw s!"mm-lean4 rejected compressed save: {repr error}"
      unless runtime.heap.size == state.heap.size + 1 do
        throw "compressed save heap size diverged from mm-lean4"
      let savedIndex := state.saves
      pure
        { state with
          runtime
          heap := state.heap.push (.formula top (some savedIndex))
          saves := state.saves + 1 }
  | .step index => do
      let runtime ← match db.stepProof state.runtime index with
        | .ok value => pure value
        | .error error =>
            throw s!"mm-lean4 rejected compressed step {index}: {repr error}"
      let heapEntry ← match state.heap[index]? with
        | some value => pure value
        | none => throw s!"lowered compressed heap has no entry {index}"
      let (stack, emitted, savedIndex) ← match heapEntry with
        | .formula entry savedIndex =>
            pure (state.stack ++ [entry], entry.actions, savedIndex)
        | .assertion label => do
            let frame ← match db.find? label with
              | some (.assert _ value _) => pure value
              | _ => throw s!"compressed assertion {label} disappeared from the database"
            unless frame.hyps.size ≤ state.stack.length do
              throw s!"lowered compressed stack underflow at {label}"
            let retained := state.stack.take (state.stack.length - frame.hyps.size)
            let consumed := state.stack.drop (state.stack.length - frame.hyps.size)
            let result ← match runtime.stack.back? >>= ConstantHeadedFormula.ofRuntime? with
              | some value => pure value
              | none => throw s!"compressed assertion {label} produced no supported result"
            let entry : ExpandedProofEntry :=
              { formula := result
                actions := consumed.flatMap (·.actions) ++ [label] }
            pure (retained ++ [entry], [label], none)
      unless stackMatchesRuntime runtime stack do
        throw s!"expanded compressed stack diverged after heap step {index}"
      pure
        { state with
          runtime
          stack
          actions := state.actions ++ emitted
          savedReferences := state.savedReferences +
            (if savedIndex.isSome then 1 else 0) }

private def applyCompressedToken (db : RuntimeDB)
    (state : CompressedExpansion) (token : ByteSlice) :
    Except String CompressedExpansion := do
  let (actions, phase) ←
    match Metamath.Verify.ParserState.decodeCompressed token state.phase with
    | .ok value => pure value
    | .error error => throw s!"mm-lean4 rejected compressed token: {repr error}"
  let state ← actions.foldlM (applyCompressedAction db) state
  pure { state with phase }

private def splitCompressedTokens :
    List ByteSlice → Except String (List ByteSlice × List ByteSlice)
  | [] => throw "compressed proof has no closing parenthesis"
  | token :: tokens =>
      if token.eqArray ")".toAscii then pure ([], tokens)
      else do
        let (preloads, compressed) ← splitCompressedTokens tokens
        pure (token :: preloads, compressed)

private def expandCompressedProof (proof : ObservedProofIngress) :
    Except String ProofActionExtraction := do
  let tokens ← match proof.tokens with
    | first :: rest =>
        if first.eqArray "(".toAscii then pure rest
        else throw "compressed proof does not begin with an opening parenthesis"
    | [] => throw "compressed proof has no tokens"
  let (preloadTokens, compressedTokens) ← splitCompressedTokens tokens
  let preloadLabels ← preloadTokens.mapM labelOfToken
  let runtime ← match proof.anchor.db.preloadMandatoryHyps proof.initial with
    | .ok value => pure value
    | .error error => throw s!"mm-lean4 rejected mandatory preloads: {repr error}"
  let mandatoryLabels := proof.initial.frame.hyps.toList
  let mandatoryHeap ← mandatoryLabels.mapM (heapEntryForLabel proof.anchor.db)
  unless runtime.heap.size == mandatoryHeap.length do
    throw "mandatory compressed heap size diverged from mm-lean4"
  let initial : CompressedExpansion :=
    { runtime
      heap := mandatoryHeap.toArray
      stack := []
      actions := []
      phase := .betweenSteps
      saves := 0
      savedReferences := 0 }
  let preloaded ← preloadLabels.foldlM (fun state label => do
      let runtime ← match proof.anchor.db.preload state.runtime label with
        | .ok value => pure value
        | .error error => throw s!"mm-lean4 rejected preload {label}: {repr error}"
      let heapEntry ← heapEntryForLabel proof.anchor.db label
      unless runtime.heap.size == state.heap.size + 1 do
        throw s!"preload heap size diverged at {label}"
      pure { state with runtime, heap := state.heap.push heapEntry }) initial
  let expanded ← compressedTokens.foldlM
    (applyCompressedToken proof.anchor.db) preloaded
  match expanded.phase with
  | .openIndex _ =>
      throw "compressed proof ended with an incomplete numeric index"
  | .betweenSteps | .justCompletedStep => pure ()
  unless expanded.runtime.stack == #[proof.initial.fmla] do
    throw "compressed replay did not finish with exactly the target formula"
  unless expanded.stack.length == 1 do
    throw "expanded compressed replay did not finish with one result"
  pure
    { actions := expanded.actions
      saves := expanded.saves
      savedReferences := expanded.savedReferences }

private def extractProofActions (proof : ObservedProofIngress) :
    Except String ProofActionExtraction :=
  match proof.tokens with
  | [] => throw "observed proof ingress has no tokens"
  | first :: _ =>
      if first.eqArray "(".toAscii then expandCompressedProof proof
      else do
        let actions ← proof.tokens.mapM labelOfToken
        pure { actions }

private def lowerNormalToken (db : RuntimeDB) (callerFrame : RuntimeFrame)
    (runtimeState : Metamath.Verify.ProofState)
    (entries : List LoweredStackEntry) (label : String) :
    Except String
      (Metamath.Verify.ProofState × List LoweredStackEntry × RuleInstance) := do
  let stepped ← match db.stepNormal runtimeState label with
    | .ok value => pure value
    | .error error => throw s!"mm-lean4 rejected proof token {label}: {repr error}"
  let (nextEntries, ruleInstance) ← match db.find? label with
    | some (.hyp _ runtimeFormula _) => do
        let formula ← match ConstantHeadedFormula.ofRuntime? runtimeFormula with
          | some value => pure value
          | none => throw s!"hypothesis {label} is not constant-headed"
        pure
          (entries ++ [{ formula, proof := proofNode label [] }],
            { ruleId := { value := label }, arguments := [] })
    | some (.assert runtimeFormula frame embeddedLabel) => do
        let assertion ← match projectAssertion? db label runtimeFormula frame embeddedLabel with
          | some value => pure value
          | none => throw s!"assertion {label} failed projection"
        let count := assertion.hypotheses.length
        unless count ≤ entries.length do
          throw s!"proof stack underflow at {label}"
        let retained := entries.take (entries.length - count)
        let consumed := entries.drop (entries.length - count)
        let pairs := assertion.hypotheses.zip consumed
        let bindings ← mandatoryBindings assertion.hypotheses consumed
        let essentialProofs ← essentialCheckProofs bindings pairs
        let dvProof ← generatedDVProof bindings callerFrame assertion.frame
        let (result, resultProof) ←
          applySubstitutionProof bindings assertion.formula
        let arguments := consumed.map (encodedBody ·.formula.body) ++
          [encodedBody result.body]
        let proof :=
          proofNode label arguments
            (consumed.map (·.proof) ++ essentialProofs ++ [dvProof, resultProof])
        pure
          (retained ++ [{ formula := result, proof }],
            { ruleId := { value := label }, arguments })
    | _ => throw s!"proof token {label} is not a hypothesis or assertion"
  let expectedViews ← match runtimeStackViews stepped.stack with
    | some value => pure value
    | none => throw s!"runtime stack became non-constant-headed at {label}"
  unless expectedViews == nextEntries.map (·.formula) do
    throw s!"lowered stack diverged from mm-lean4 after {label}"
  pure (stepped, nextEntries, ruleInstance)

private structure LoweringReplayState where
  runtime : Metamath.Verify.ProofState
  entries : List LoweredStackEntry
  instances : List RuleInstance

private structure SourceLowering where
  sourcePackage : GSLTSource
  definition : CalculusLanguageDef
  goal : Pattern
  proof : RawProof
  actions : List String
  compressedSaves : Nat
  compressedSavedReferences : Nat

private def sourceMetadata : SourceMetadata :=
  { systemId := "metamath"
    revision := "mm-lean4-sound-default/inference-projection-v1"
    assumptions := { entries := [] }
    profiles :=
      { entries :=
          [{ name := "metamath-inference-projection"
             version := "v1"
             payload := .apply "ExactPremisesWithDV" [] }] } }

private def includeSourceMetadata : SourceMetadata :=
  { sourceMetadata with
    revision := "mm-lean4-sound-default/include-aware/inference-projection-v1" }

private def renderDatabaseOutput (kind : String) (rootBytes : ByteArray)
    (checked : CheckedGSLT) : String :=
  "!(import! &self gslt_checked_source_v1)\n\n" ++
    s!"(= (mm-database-source) {renderGSLTSource checked.source})\n\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-validation-v1 (mm-database-source))\n" ++
    "  SourceAcceptedV1)\n" ++
    s!"!(MMDatabaseSummary {quote kind} {rootBytes.size} " ++
      s!"{checked.source.definition.rules.length} 1 1 0)\n"

private def renderDatabaseBytes (sourceBytes : ByteArray) :
    Except String String := do
  let request : AdmissionRequest :=
    { sourceBytes
      targetLabel := none
      metadata := sourceMetadata }
  let input <- match prepareBytes request with
    | .ok value => pure value
    | .error error =>
        throw s!"canonical Metamath database admission failed: {repr error}"
  let checked <- match admit input with
    | .ok value => pure value
    | .error error =>
        throw s!"database checked-source validation failed: {repr error}"
  pure (renderDatabaseOutput "exact-bytes" sourceBytes checked)

private def renderIncludeDatabase (sourcePath verifiedDigest : String) :
    IO (Except String String) := do
  let prepared <- prepare <| .canonicalFile
    { sourcePath
      targetLabel := none
      verifiedArtifactDigest := verifiedDigest
      metadata := includeSourceMetadata }
  match prepared with
  | .error error =>
      pure <| .error s!"canonical include-aware admission failed: {repr error}"
  | .ok (.exactBytes _) =>
      pure <| .error "include-aware request returned the wrong admission variant"
  | .ok (.includeDatabase input) =>
      match admitInclude input with
      | .error error =>
          pure <| .error s!"include checked-source validation failed: {repr error}"
      | .ok checked =>
          pure <| .ok (renderDatabaseOutput "include-aware" input.rootBytes checked)

private def lowerSourceProof (source targetLabel : String) :
    Except String SourceLowering := do
  let request : AdmissionRequest :=
    { sourceBytes := source.toUTF8
      targetLabel := some targetLabel
      metadata := sourceMetadata }
  let input <- match prepareBytes request with
    | .ok value => pure value
    | .error error =>
        throw s!"canonical Metamath admission failed: {repr error}"
  let ingress <- proofIngressOfParsed input.parsed
  let extraction ← extractProofActions ingress
  let proofActions := extraction.actions
  let prefixDB := ingress.anchor.db
  let targetFormula := ingress.initial.fmla
  let targetFrame := ingress.initial.frame
  let targetView ← match ConstantHeadedFormula.ofRuntime? targetFormula with
    | some value => pure value
    | none => throw s!"{targetLabel} is not constant-headed"
  let definition := input.definition.1
  let initialRuntime :=
    prefixDB.mkProofState ingress.initial.pos targetLabel targetFormula targetFrame
  let replay ←
    proofActions.foldlM
      (fun state label => do
        let (runtime, entries, ruleInstance) ←
          lowerNormalToken prefixDB prefixDB.frame state.runtime state.entries label
        pure
          { runtime
            entries
            instances := state.instances ++ [ruleInstance] })
      ({ runtime := initialRuntime, entries := [], instances := [] } : LoweringReplayState)
  unless replay.runtime.stack == #[targetFormula] do
    throw s!"mm-lean4 proof replay did not finish with exactly {targetLabel}"
  let proof ← match replay.entries with
    | [entry] =>
        if entry.formula == targetView then pure entry.proof
        else throw s!"lowered proof result does not equal {targetLabel}"
    | _ => throw s!"lowered {targetLabel} proof did not finish with one result"
  let goal := proves (encodeFormula targetView)
  let checkedArtifact : CheckedTheoremArtifact <-
    match bindTheoremArtifact input goal proof with
    | .ok value => pure value
    | .error error =>
        throw s!"source-indexed Lean proof admission failed: {repr error}"
  pure <|
    (show SourceLowering from
    { sourcePackage := checkedArtifact.checked.source
      definition
      goal
      proof
      actions := proofActions
      compressedSaves := extraction.saves
      compressedSavedReferences := extraction.savedReferences })

private def renderDemo0 (source : String) : Except String String := do
  let lowering ← lowerSourceProof source "th1"
  let output :=
    "!(import! &self gslt_checked_source_v1)\n\n" ++
    s!"(= (demo0-source) {renderGSLTSource lowering.sourcePackage})\n\n" ++
    s!"(= (demo0-goal) {renderPattern lowering.goal})\n" ++
    s!"(= (demo0-proof) {renderRawProof lowering.proof})\n\n" ++
    "(= (demo0-wrong-goal)\n" ++
    "   (PApp \"$mm.j.vars\"\n" ++
    "     (LCons (PApp \"$mm.nil\" LNil)\n" ++
    "       (LCons (PApp \"$mm.nil\" LNil) LNil))))\n" ++
    "(= (demo0-drop-first-root-child (GProof $ri (PrCons $p $ps)))\n" ++
    "   (GProof $ri $ps))\n" ++
    "(= (demo0-missing-child-proof)\n" ++
    "   (demo0-drop-first-root-child (demo0-proof)))\n\n" ++
    "!(assertEqual (gslt-source-validation-v1 (demo0-source)) SourceAcceptedV1)\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-check-v1 (demo0-source) (demo0-goal) (demo0-proof))\n" ++
    "  True)\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-check-v1 (demo0-source) (demo0-goal)\n" ++
    "    (GProof (GRuleInst \"mp\" LNil) PrNil))\n" ++
    "  False)\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-check-v1 (demo0-source) (demo0-goal)\n" ++
    "    (demo0-missing-child-proof))\n" ++
    "  False)\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-check-v1 (demo0-source) (demo0-goal)\n" ++
    "    (GProof (GRuleInst \"th1\" LNil) PrNil))\n" ++
    "  False)\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-check-v1 (demo0-source) (demo0-wrong-goal)\n" ++
    "    (demo0-proof))\n" ++
    "  False)\n" ++
    s!"!(MMDEMO0Summary {source.toUTF8.size} {lowering.actions.length} 6 6 0)\n"
  pure output

private def renderHolTru (source : String) : Except String String := do
  let lowering ← lowerSourceProof source "tru"
  let output :=
    "!(import! &self gslt_checked_source_v1)\n\n" ++
    s!"(= (holmm-tru-source) {renderGSLTSource lowering.sourcePackage})\n\n" ++
    s!"(= (holmm-tru-goal) {renderPattern lowering.goal})\n" ++
    s!"(= (holmm-tru-proof) {renderRawProof lowering.proof})\n\n" ++
    "(= (holmm-drop-first-root-child (GProof $ri (PrCons $p $ps)))\n" ++
    "   (GProof $ri $ps))\n" ++
    "(= (holmm-tru-missing-child-proof)\n" ++
    "   (holmm-drop-first-root-child (holmm-tru-proof)))\n\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-check-batch-v1 (holmm-tru-source)\n" ++
    "    (CheckCons\n" ++
    "      (GCheck (holmm-tru-goal) (holmm-tru-proof) True)\n" ++
    "      (CheckCons\n" ++
    "        (GCheck (holmm-tru-goal)\n" ++
    "          (GProof (GRuleInst \"id\" LNil) PrNil) False)\n" ++
    "        (CheckCons\n" ++
    "          (GCheck (holmm-tru-goal)\n" ++
    "            (holmm-tru-missing-child-proof) False)\n" ++
    "          (CheckCons\n" ++
    "            (GCheck (holmm-tru-goal)\n" ++
    "              (GProof (GRuleInst \"tru\" LNil) PrNil) False)\n" ++
    "            CheckNil)))))\n" ++
    "  True)\n" ++
    s!"!(MMHOLTRUSummary {source.toUTF8.size} {lowering.actions.length} 5 5 0)\n"
  pure output

private def renderTarget (source targetLabel : String) : Except String String := do
  let lowering ← lowerSourceProof source targetLabel
  let output :=
    "!(import! &self gslt_checked_source_v1)\n\n" ++
    s!"(= (mm-target-source) {renderGSLTSource lowering.sourcePackage})\n\n" ++
    s!"(= (mm-target-goal) {renderPattern lowering.goal})\n" ++
    s!"(= (mm-target-proof) {renderRawProof lowering.proof})\n\n" ++
    "(= (mm-target-wrong-goal)\n" ++
    "   (PApp \"$mm.j.vars\"\n" ++
    "     (LCons (PApp \"$mm.nil\" LNil)\n" ++
    "       (LCons (PApp \"$mm.nil\" LNil) LNil))))\n" ++
    "(= (mm-target-child-cardinality-mutation (GProof $ri PrNil))\n" ++
    "   (GProof $ri\n" ++
    "     (PrCons (GProof (GRuleInst \"$mm.missing-rule\" LNil) PrNil) PrNil)))\n" ++
    "(= (mm-target-child-cardinality-mutation\n" ++
    "      (GProof $ri (PrCons $p $ps)))\n" ++
    "   (GProof $ri $ps))\n" ++
    "(= (mm-target-wrong-child-count-proof)\n" ++
    "   (mm-target-child-cardinality-mutation (mm-target-proof)))\n\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-check-batch-v1 (mm-target-source)\n" ++
    "    (CheckCons\n" ++
    "      (GCheck (mm-target-goal) (mm-target-proof) True)\n" ++
    "      (CheckCons\n" ++
    "        (GCheck (mm-target-goal)\n" ++
    "          (GProof (GRuleInst \"$mm.missing-rule\" LNil) PrNil) False)\n" ++
    "        (CheckCons\n" ++
    "          (GCheck (mm-target-goal)\n" ++
    "            (mm-target-wrong-child-count-proof) False)\n" ++
    "          (CheckCons\n" ++
    s!"            (GCheck (mm-target-goal)\n" ++
    s!"              (GProof (GRuleInst {quote targetLabel} LNil) PrNil) False)\n" ++
    "            (CheckCons\n" ++
    "              (GCheck (mm-target-wrong-goal)\n" ++
    "                (mm-target-proof) False)\n" ++
    "              CheckNil))))))\n" ++
    "  True)\n" ++
    s!"!(MMTARGETSummary {quote targetLabel} {source.toUTF8.size} " ++
      s!"{lowering.actions.length} 6 6 0)\n" ++
    s!"!(MMTARGETCompressedStats {quote targetLabel} " ++
      s!"{lowering.compressedSaves} {lowering.compressedSavedReferences})\n"
  pure output

private def renderTargetDag (source targetLabel : String) : Except String String := do
  let lowering ← lowerSourceProof source targetLabel
  let (rootId, dag) := internRawProof lowering.proof {}
  let output :=
    "!(import! &self gslt_checked_source_v1)\n\n" ++
    s!"(= (mm-target-dag-source) {renderGSLTSource lowering.sourcePackage})\n\n" ++
    s!"(= (mm-target-dag-goal) {renderPattern lowering.goal})\n" ++
    s!"(= (mm-target-dag-nodes) {renderDagNodes dag.nodes})\n\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-check-dag-v1 (mm-target-dag-source)\n" ++
    s!"    (mm-target-dag-goal) {quote (dagNodeName rootId)}\n" ++
    "    (mm-target-dag-nodes))\n" ++
    "  True)\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-check-dag-v1 (mm-target-dag-source)\n" ++
    "    (mm-target-dag-goal) \"$mm.missing-root\"\n" ++
    "    (mm-target-dag-nodes))\n" ++
    "  False)\n" ++
    s!"!(MMTARGETDAGSummary {quote targetLabel} {source.toUTF8.size} " ++
      s!"{lowering.actions.length} {dag.nodes.length} " ++
      s!"{lowering.compressedSaves} {lowering.compressedSavedReferences} " ++
      "3 3 0)\n"
  pure output

def main (arguments : List String) : IO UInt32 := do
  let renderedAndPath ← match arguments with
    | ["demo0", sourcePath, outputPath] =>
        pure (renderDemo0 (← IO.FS.readFile sourcePath), outputPath)
    | ["hol-tru", sourcePath, outputPath] =>
        pure (renderHolTru (← IO.FS.readFile sourcePath), outputPath)
    | ["target", sourcePath, targetLabel, outputPath] =>
        pure
          (renderTarget (← IO.FS.readFile sourcePath) targetLabel, outputPath)
    | ["target-dag", sourcePath, targetLabel, outputPath] =>
        pure
          (renderTargetDag (← IO.FS.readFile sourcePath) targetLabel, outputPath)
    | ["database", sourcePath, outputPath] =>
        pure (renderDatabaseBytes (← IO.FS.readBinFile sourcePath), outputPath)
    | ["database-include", sourcePath, verifiedDigest, outputPath] =>
        pure (← renderIncludeDatabase sourcePath verifiedDigest, outputPath)
    | _ =>
        IO.eprintln
          "usage: InferenceMeTTaExport demo0 <demo0.mm> <output.metta> | hol-tru <hol.mm> <output.metta> | target <source.mm> <label> <output.metta> | target-dag <source.mm> <label> <output.metta> | database <source.mm> <output.metta> | database-include <source.mm> <verified-digest> <output.metta>"
        return 2
  match renderedAndPath.1 with
  | .error error =>
      IO.eprintln s!"Metamath MeTTa export failed: {error}"
      return 1
  | .ok output =>
      IO.FS.writeFile renderedAndPath.2 output
      IO.println s!"wrote {output.length} bytes to {renderedAndPath.2}"
      return 0

end Mettapedia.Languages.Metamath.InferenceMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.InferenceMeTTaExport.main arguments
