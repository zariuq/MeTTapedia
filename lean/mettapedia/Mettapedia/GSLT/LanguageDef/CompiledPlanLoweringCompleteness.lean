import Mettapedia.GSLT.LanguageDef.CompiledPlanLowering

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanLowering

open CompiledPlanWireFormat CompiledPlanAdmission

mutual

theorem decodeTerm?_emitTerm
    (source : Term) (builder : Builder) (program : Program) (fuel : Nat)
    (wellFormed : builder.WellFormed)
    (sourceValid : termTextsValid source = true)
    (nodePrefix : (emitTerm source builder).2.nodes <+: program.nodes)
    (childPrefix : (emitTerm source builder).2.children <+: program.children)
    (nodesFit : (emitTerm source builder).2.nodeCount < UInt32.size)
    (childrenFit : (emitTerm source builder).2.childCount < UInt32.size)
    (fuelEnough : termDepth source < fuel) :
    ∃ decoded,
      decodeTerm? program fuel (emitTerm source builder).1.toNat =
          some decoded ∧
        DecodedTermMatchesSourceAt decoded source builder.nodeCount
          builder.childCount := by
  cases source with
  | symbol name =>
      let node := scalarNode 1 0 0 name
      have afterWellFormed :=
        emitTerm_wellFormed (.symbol name) builder wellFormed
      have selected := getElem?_eq_reverseHead_of_prefix
        (emitTerm (.symbol name) builder).2.nodesRev program.nodes node
        nodePrefix (by simp [emitTerm, appendNode, node])
      have rootIndex :=
        emitTerm_root_succ_eq_nodeCount (.symbol name) builder nodesFit
      have nodeLength :
          (emitTerm (.symbol name) builder).2.nodesRev.length =
            (emitTerm (.symbol name) builder).2.nodeCount :=
        afterWellFormed.1.symm
      have indexEq : (emitTerm (.symbol name) builder).1.toNat =
          (emitTerm (.symbol name) builder).2.nodesRev.length - 1 := by
        omega
      have lookup :
          program.nodes[(emitTerm (.symbol name) builder).1.toNat]? =
            some node := by
        rw [indexEq]
        exact selected
      cases fuel with
      | zero => omega
      | succ remaining =>
          refine ⟨DecodedTerm.leaf (.symbol name)
            (emitTerm (.symbol name) builder).1.toNat, ?_, ?_⟩
          · have localValid : node.locallyValid = true := by
              simp [termTextsValid, bytesNonempty, textEncodable?,
                bytesNulFree] at sourceValid
              simp [node, scalarNode, Node.locallyValid,
                scalarNodeFieldsAreZero, bytesNonempty, bytesNulFree,
                sourceValid]
            have localValid' :
                (scalarNode 1 0 0 name).locallyValid = true := by
              simpa [node] using localValid
            simp only [decodeTerm?, lookup]
            change
              (if (!(scalarNode 1 0 0 name).locallyValid) = true then none
                else _) = _
            rw [localValid']
            rfl
          · have rootExact :
                (emitTerm (.symbol name) builder).1.toNat =
                  builder.nodeCount := by
              change (emitTerm (.symbol name) builder).1.toNat + 1 =
                builder.nodeCount + 1 at rootIndex
              omega
            simp [DecodedTermMatchesSourceAt, DecodedTerm.leaf,
              termNodeCount, termChildSlotCount, termUsedVariables,
              termDepth, slotRange, rootExact]
  | «variable» slot =>
      let node := scalarNode 2 0 slot []
      have afterWellFormed :=
        emitTerm_wellFormed (.variable slot) builder wellFormed
      have selected := getElem?_eq_reverseHead_of_prefix
        (emitTerm (.variable slot) builder).2.nodesRev program.nodes node
        nodePrefix (by simp [emitTerm, appendNode, node])
      have rootIndex :=
        emitTerm_root_succ_eq_nodeCount (.variable slot) builder nodesFit
      have nodeLength :
          (emitTerm (.variable slot) builder).2.nodesRev.length =
            (emitTerm (.variable slot) builder).2.nodeCount :=
        afterWellFormed.1.symm
      have indexEq : (emitTerm (.variable slot) builder).1.toNat =
          (emitTerm (.variable slot) builder).2.nodesRev.length - 1 := by
        omega
      have lookup :
          program.nodes[(emitTerm (.variable slot) builder).1.toNat]? =
            some node := by
        rw [indexEq]
        exact selected
      cases fuel with
      | zero => omega
      | succ remaining =>
          refine ⟨DecodedTerm.leaf (.variable slot)
            (emitTerm (.variable slot) builder).1.toNat [slot.toNat], ?_, ?_⟩
          · have localValid :
                (scalarNode 2 0 slot []).locallyValid = true := by
              simp [scalarNode, Node.locallyValid, bytesNulFree]
            simp only [decodeTerm?, lookup]
            change
              (if (!(scalarNode 2 0 slot []).locallyValid) = true then none
                else _) = _
            rw [localValid]
            rfl
          · have rootExact :
                (emitTerm (.variable slot) builder).1.toNat =
                  builder.nodeCount := by
              change (emitTerm (.variable slot) builder).1.toNat + 1 =
                builder.nodeCount + 1 at rootIndex
              omega
            simp [DecodedTermMatchesSourceAt, DecodedTerm.leaf,
              termNodeCount, termChildSlotCount, termUsedVariables,
              termDepth, slotRange, rootExact]
  | «string» value =>
      let node := scalarNode 3 0 0 value
      have afterWellFormed :=
        emitTerm_wellFormed (.string value) builder wellFormed
      have selected := getElem?_eq_reverseHead_of_prefix
        (emitTerm (.string value) builder).2.nodesRev program.nodes node
        nodePrefix (by simp [emitTerm, appendNode, node])
      have rootIndex :=
        emitTerm_root_succ_eq_nodeCount (.string value) builder nodesFit
      have nodeLength :
          (emitTerm (.string value) builder).2.nodesRev.length =
            (emitTerm (.string value) builder).2.nodeCount :=
        afterWellFormed.1.symm
      have indexEq : (emitTerm (.string value) builder).1.toNat =
          (emitTerm (.string value) builder).2.nodesRev.length - 1 := by
        omega
      have lookup :
          program.nodes[(emitTerm (.string value) builder).1.toNat]? =
            some node := by
        rw [indexEq]
        exact selected
      cases fuel with
      | zero => omega
      | succ remaining =>
          refine ⟨DecodedTerm.leaf (.string value)
            (emitTerm (.string value) builder).1.toNat, ?_, ?_⟩
          · have localValid : node.locallyValid = true := by
              simp [termTextsValid, textEncodable?, bytesNulFree]
                at sourceValid
              simp [node, scalarNode, Node.locallyValid, bytesNulFree,
                sourceValid]
            have localValid' :
                (scalarNode 3 0 0 value).locallyValid = true := by
              simpa [node] using localValid
            simp only [decodeTerm?, lookup]
            change
              (if (!(scalarNode 3 0 0 value).locallyValid) = true then none
                else _) = _
            rw [localValid']
            rfl
          · have rootExact :
                (emitTerm (.string value) builder).1.toNat =
                  builder.nodeCount := by
              change (emitTerm (.string value) builder).1.toNat + 1 =
                builder.nodeCount + 1 at rootIndex
              omega
            simp [DecodedTermMatchesSourceAt, DecodedTerm.leaf,
              termNodeCount, termChildSlotCount, termUsedVariables,
              termDepth, slotRange, rootExact]
  | integer value =>
      let node := scalarNode 4 value 0 []
      have afterWellFormed :=
        emitTerm_wellFormed (.integer value) builder wellFormed
      have selected := getElem?_eq_reverseHead_of_prefix
        (emitTerm (.integer value) builder).2.nodesRev program.nodes node
        nodePrefix (by simp [emitTerm, appendNode, node])
      have rootIndex :=
        emitTerm_root_succ_eq_nodeCount (.integer value) builder nodesFit
      have nodeLength :
          (emitTerm (.integer value) builder).2.nodesRev.length =
            (emitTerm (.integer value) builder).2.nodeCount :=
        afterWellFormed.1.symm
      have indexEq : (emitTerm (.integer value) builder).1.toNat =
          (emitTerm (.integer value) builder).2.nodesRev.length - 1 := by
        omega
      have lookup :
          program.nodes[(emitTerm (.integer value) builder).1.toNat]? =
            some node := by
        rw [indexEq]
        exact selected
      cases fuel with
      | zero => omega
      | succ remaining =>
          refine ⟨DecodedTerm.leaf (.integer value)
            (emitTerm (.integer value) builder).1.toNat, ?_, ?_⟩
          · have localValid :
                (scalarNode 4 value 0 []).locallyValid = true := by
              simp [scalarNode, Node.locallyValid, bytesNulFree]
            simp only [decodeTerm?, lookup]
            change
              (if (!(scalarNode 4 value 0 []).locallyValid) = true then none
                else _) = _
            rw [localValid]
            rfl
          · have rootExact :
                (emitTerm (.integer value) builder).1.toNat =
                  builder.nodeCount := by
              change (emitTerm (.integer value) builder).1.toNat + 1 =
                builder.nodeCount + 1 at rootIndex
              omega
            simp [DecodedTermMatchesSourceAt, DecodedTerm.leaf,
              termNodeCount, termChildSlotCount, termUsedVariables,
              termDepth, slotRange, rootExact]
  | application head arguments =>
      cases emittedArguments : emitTerms arguments builder with
      | mk roots afterArguments =>
          let withChildren : Builder :=
            { afterArguments with
              childCount := afterArguments.childCount + roots.length
              childrenRev := roots.reverse ++ afterArguments.childrenRev }
          let node : Node :=
            { kind := 5
              childOffset := UInt32.ofNat afterArguments.childCount
              childCount := UInt32.ofNat roots.length
              integerValue := 0
              variableSlot := 0
              text := head }
          have emittedApplication :
              emitTerm (.application head arguments) builder =
                appendNode withChildren node := by
            simp [emitTerm, emittedArguments, withChildren, node]
          have argumentsCounts := emitTerms_counts arguments builder
          rw [emittedArguments] at argumentsCounts
          have rootsLength : roots.length = termsLength arguments := by
            simpa using argumentsCounts.1
          have afterArgumentsNodes : afterArguments.nodeCount =
              builder.nodeCount + termsNodeCount arguments := by
            simpa using argumentsCounts.2.1
          have afterArgumentsChildren : afterArguments.childCount =
              builder.childCount + termsChildSlotCount arguments := by
            simpa using argumentsCounts.2.2.1
          have argumentsWellFormed :=
            emitTerms_wellFormed arguments builder wellFormed
          rw [emittedArguments] at argumentsWellFormed
          have argumentsNodePrefix :
              afterArguments.nodes <+: program.nodes := by
            apply (show afterArguments.nodes <+:
                (emitTerm (.application head arguments) builder).2.nodes by
              simp [emittedApplication, appendNode, withChildren,
                Builder.nodes]).trans
            exact nodePrefix
          have argumentsChildPrefix :
              afterArguments.children <+: program.children := by
            apply (show afterArguments.children <+:
                (emitTerm (.application head arguments) builder).2.children by
              simp [emittedApplication, appendNode, withChildren,
                Builder.children, List.reverse_append]).trans
            exact childPrefix
          have argumentsNodesFit : afterArguments.nodeCount < UInt32.size := by
            have finalNodes : afterArguments.nodeCount + 1 < UInt32.size := by
              simpa [emittedApplication, appendNode, withChildren] using
                nodesFit
            omega
          have argumentsChildrenFit :
              afterArguments.childCount < UInt32.size := by
            have finalChildren :
                afterArguments.childCount + roots.length < UInt32.size := by
              simpa [emittedApplication, appendNode, withChildren] using
                childrenFit
            omega
          simp only [termTextsValid, Bool.and_eq_true] at sourceValid
          rcases sourceValid with
            ⟨⟨headNonempty, headEncodable⟩, argumentsValid⟩
          cases fuel with
          | zero =>
              simp [termDepth] at fuelEnough
          | succ remaining =>
              have argumentsFuel :
                  termsMaximumDepth arguments < remaining := by
                simp only [termDepth] at fuelEnough
                omega
              have argumentsNodePrefix' :
                  (emitTerms arguments builder).2.nodes <+: program.nodes := by
                rw [emittedArguments]
                exact argumentsNodePrefix
              have argumentsChildPrefix' :
                  (emitTerms arguments builder).2.children <+:
                    program.children := by
                rw [emittedArguments]
                exact argumentsChildPrefix
              have argumentsNodesFit' :
                  (emitTerms arguments builder).2.nodeCount < UInt32.size := by
                rw [emittedArguments]
                exact argumentsNodesFit
              have argumentsChildrenFit' :
                  (emitTerms arguments builder).2.childCount < UInt32.size := by
                rw [emittedArguments]
                exact argumentsChildrenFit
              rcases decodeTerms?_emitTerms arguments builder program remaining
                  wellFormed argumentsValid argumentsNodePrefix'
                  argumentsChildPrefix' argumentsNodesFit'
                  argumentsChildrenFit' argumentsFuel with
                ⟨decodedArguments, decodedArgumentsEq, argumentsMatch⟩
              rw [emittedArguments] at decodedArgumentsEq
              change decodeTerms? program remaining roots =
                some decodedArguments at decodedArgumentsEq
              let decoded : DecodedTerm :=
                { term := .application head (decodedTerms decodedArguments)
                  claimedNodes :=
                    .append
                      (.singleton
                        (emitTerm (.application head arguments) builder).1.toNat)
                      (concatDecodedTerms decodedArguments).1
                  claimedChildSlots :=
                    .append
                      (.ofList
                        (slotRange afterArguments.childCount roots.length))
                      (concatDecodedTerms decodedArguments).2.1
                  usedVariables :=
                    (concatDecodedTerms decodedArguments).2.2
                  depth := maximumDepth decodedArguments + 1 }
              have afterWellFormed := emitTerm_wellFormed
                (.application head arguments) builder wellFormed
              have selected := getElem?_eq_reverseHead_of_prefix
                (emitTerm (.application head arguments) builder).2.nodesRev
                program.nodes node nodePrefix (by
                  simp [emittedApplication, appendNode, node])
              have rootIndex := emitTerm_root_succ_eq_nodeCount
                (.application head arguments) builder nodesFit
              have nodeLength :
                  (emitTerm (.application head arguments) builder).2.nodesRev.length =
                    (emitTerm (.application head arguments) builder).2.nodeCount :=
                afterWellFormed.1.symm
              have indexEq :
                  (emitTerm (.application head arguments) builder).1.toNat =
                    (emitTerm (.application head arguments) builder).2.nodesRev.length -
                      1 := by
                omega
              have lookup :
                  program.nodes[
                    (emitTerm (.application head arguments) builder).1.toNat]? =
                      some node := by
                rw [indexEq]
                exact selected
              have rootExact :
                  (emitTerm (.application head arguments) builder).1.toNat =
                    afterArguments.nodeCount := by
                rw [emittedApplication] at rootIndex
                rw [emittedApplication]
                change (UInt32.ofNat withChildren.nodeCount).toNat =
                  afterArguments.nodeCount
                change (UInt32.ofNat withChildren.nodeCount).toNat + 1 =
                  withChildren.nodeCount + 1 at rootIndex
                have withChildrenNodes : withChildren.nodeCount =
                    afterArguments.nodeCount := rfl
                omega
              have offsetExact :
                  (UInt32.ofNat afterArguments.childCount).toNat =
                    afterArguments.childCount := by
                simp [Nat.mod_eq_of_lt argumentsChildrenFit]
              have rootsFit : roots.length < UInt32.size := by
                have finalChildren :
                    afterArguments.childCount + roots.length < UInt32.size := by
                  simpa [emittedApplication, appendNode, withChildren] using
                    childrenFit
                omega
              have countExact : (UInt32.ofNat roots.length).toNat =
                  roots.length := by
                simp [Nat.mod_eq_of_lt rootsFit]
              have segmentPrefix :
                  afterArguments.children ++ roots <+: program.children := by
                simpa [emittedApplication, appendNode, withChildren,
                  Builder.children, List.reverse_append] using childPrefix
              have sliceExact := slice?_of_append_prefix
                afterArguments.children roots program.children segmentPrefix
              have childrenLength : afterArguments.children.length =
                  afterArguments.childCount := by
                change afterArguments.WellFormed at argumentsWellFormed
                simpa [Builder.children] using
                  argumentsWellFormed.2.1.symm
              rw [childrenLength] at sliceExact
              have rootsBackward :
                  roots.all (fun child => child.toNat <
                    (emitTerm (.application head arguments) builder).1.toNat) =
                      true := by
                rw [List.all_eq_true]
                intro child member
                rw [rootExact]
                have rootsBound := emitTerms_roots_lt_nodeCount
                  arguments builder argumentsNodesFit'
                rw [emittedArguments] at rootsBound
                simpa using rootsBound child member
              have localValid : node.locallyValid = true := by
                simp [node, Node.locallyValid, bytesNonempty, bytesNulFree,
                  textEncodable?] at headNonempty headEncodable ⊢
                exact ⟨headEncodable.2, headNonempty⟩
              have decodedEq :
                  decodeTerm? program (remaining + 1)
                    (emitTerm (.application head arguments) builder).1.toNat =
                      some decoded := by
                simp only [decodeTerm?, lookup]
                change (if (!node.locallyValid) = true then none else _) = _
                rw [localValid]
                change
                  (slice? program.children
                    (UInt32.ofNat afterArguments.childCount).toNat
                    (UInt32.ofNat roots.length).toNat).bind _ = _
                rw [offsetExact, countExact, sliceExact]
                simp only [Option.bind_some]
                rw [show (!roots.all (fun child => child.toNat <
                    (emitTerm (.application head arguments) builder).1.toNat)) =
                    false by simp [rootsBackward]]
                simp only [Bool.false_eq_true, ↓reduceIte]
                rw [decodedArgumentsEq]
                rfl
              refine ⟨decoded, decodedEq, ?_⟩
              rcases argumentsMatch with
                ⟨argumentsMeaning, argumentsNodes, argumentsChildren,
                  argumentsVariables, argumentsDepth⟩
              unfold DecodedTermMatchesSourceAt
              dsimp only [decoded]
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · exact congrArg (Term.application head) argumentsMeaning
              · change
                  ((emitTerm (.application head arguments) builder).1.toNat ::
                    (concatDecodedTerms decodedArguments).1.toList).Perm
                    (slotRange builder.nodeCount
                      (termsNodeCount arguments + 1))
                rw [rootExact, afterArgumentsNodes]
                have rootFirst :=
                  (List.Perm.cons
                    (builder.nodeCount + termsNodeCount arguments)
                    argumentsNodes)
                have rootLast :
                    ((builder.nodeCount + termsNodeCount arguments) ::
                      slotRange builder.nodeCount
                        (termsNodeCount arguments)).Perm
                      (slotRange builder.nodeCount (termsNodeCount arguments) ++
                        [builder.nodeCount + termsNodeCount arguments]) := by
                  simpa only [List.singleton_append]
                    using (List.perm_append_comm :
                      ([builder.nodeCount + termsNodeCount arguments] ++
                        slotRange builder.nodeCount
                          (termsNodeCount arguments)).Perm _)
                exact rootFirst.trans <| rootLast.trans (by
                  simp [slotRange, List.range_succ])
              ·
                simp only [ClaimRope.toList_append,
                  ClaimRope.toList_ofList, termChildSlotCount]
                rw [afterArgumentsChildren, rootsLength]
                have directAndNested :=
                  (List.Perm.append_left
                    (slotRange
                      (builder.childCount + termsChildSlotCount arguments)
                      (termsLength arguments)) argumentsChildren)
                exact directAndNested.trans <|
                  (List.perm_append_comm.trans (by
                    rw [slotRange_append]))
              · exact argumentsVariables
              · rw [argumentsDepth]
                rfl
termination_by sizeOf source

theorem decodeTerms?_emitTerms
    (source : Terms) (builder : Builder) (program : Program) (fuel : Nat)
    (wellFormed : builder.WellFormed)
    (sourceValid : termsTextsValid source = true)
    (nodePrefix : (emitTerms source builder).2.nodes <+: program.nodes)
    (childPrefix : (emitTerms source builder).2.children <+: program.children)
    (nodesFit : (emitTerms source builder).2.nodeCount < UInt32.size)
    (childrenFit : (emitTerms source builder).2.childCount < UInt32.size)
    (fuelEnough : termsMaximumDepth source < fuel) :
    ∃ decoded,
      decodeTerms? program fuel (emitTerms source builder).1 = some decoded ∧
        DecodedTermsMatchSourceAt decoded source builder.nodeCount
          builder.childCount := by
  cases source with
  | nil =>
      refine ⟨[], by simp [emitTerms, decodeTerms?], ?_⟩
      simp [DecodedTermsMatchSourceAt, decodedTerms, Terms.ofList,
        concatDecodedTerms, termsNodeCount, termsChildSlotCount,
        termsUsedVariables, termsMaximumDepth, maximumDepth, slotRange]
  | cons head tail =>
      cases emittedHead : emitTerm head builder with
      | mk root afterHead =>
          cases emittedTail : emitTerms tail afterHead with
          | mk roots afterTail =>
              have combined : emitTerms (Terms.cons head tail) builder =
                  (root :: roots, afterTail) := by
                simp [emitTerms, emittedHead, emittedTail]
              rw [combined] at nodePrefix childPrefix nodesFit childrenFit
              change afterTail.nodeCount < UInt32.size at nodesFit
              change afterTail.childCount < UInt32.size at childrenFit
              have headCounts := emitTerm_counts head builder
              rw [emittedHead] at headCounts
              have afterHeadNodes : afterHead.nodeCount =
                  builder.nodeCount + termNodeCount head := by
                simpa using headCounts.1
              have afterHeadChildren : afterHead.childCount =
                  builder.childCount + termChildSlotCount head := by
                simpa using headCounts.2.1
              have tailCounts := emitTerms_counts tail afterHead
              rw [emittedTail] at tailCounts
              have afterTailNodes : afterTail.nodeCount =
                  afterHead.nodeCount + termsNodeCount tail := by
                simpa using tailCounts.2.1
              have afterTailChildren : afterTail.childCount =
                  afterHead.childCount + termsChildSlotCount tail := by
                simpa using tailCounts.2.2.1
              have headNodesFit :
                  (emitTerm head builder).2.nodeCount < UInt32.size := by
                rw [emittedHead]
                change afterHead.nodeCount < UInt32.size
                rw [afterTailNodes] at nodesFit
                omega
              have headChildrenFit :
                  (emitTerm head builder).2.childCount < UInt32.size := by
                rw [emittedHead]
                change afterHead.childCount < UInt32.size
                rw [afterTailChildren] at childrenFit
                omega
              have tailTablePrefix :=
                emitTerms_tablePrefixes tail afterHead
              rw [emittedTail] at tailTablePrefix
              have headNodePrefix :
                  (emitTerm head builder).2.nodes <+: program.nodes := by
                rw [emittedHead]
                exact tailTablePrefix.1.trans nodePrefix
              have headChildPrefix :
                  (emitTerm head builder).2.children <+: program.children := by
                rw [emittedHead]
                exact tailTablePrefix.2.trans childPrefix
              rw [termsTextsValid, Bool.and_eq_true] at sourceValid
              have headFuel : termDepth head < fuel := by
                simp only [termsMaximumDepth] at fuelEnough
                omega
              rcases decodeTerm?_emitTerm head builder program fuel wellFormed
                  sourceValid.1 headNodePrefix headChildPrefix headNodesFit
                  headChildrenFit headFuel with
                ⟨decodedHead, decodedHeadEq, headMatch⟩
              have afterHeadWellFormed :=
                emitTerm_wellFormed head builder wellFormed
              rw [emittedHead] at afterHeadWellFormed
              have tailFuel : termsMaximumDepth tail < fuel := by
                simp only [termsMaximumDepth] at fuelEnough
                omega
              have tailNodesFit :
                  (emitTerms tail afterHead).2.nodeCount < UInt32.size := by
                rw [emittedTail]
                exact nodesFit
              have tailChildrenFit :
                  (emitTerms tail afterHead).2.childCount < UInt32.size := by
                rw [emittedTail]
                exact childrenFit
              have tailNodePrefix :
                  (emitTerms tail afterHead).2.nodes <+: program.nodes := by
                rw [emittedTail]
                exact nodePrefix
              have tailChildPrefix :
                  (emitTerms tail afterHead).2.children <+: program.children := by
                rw [emittedTail]
                exact childPrefix
              rcases decodeTerms?_emitTerms tail afterHead program fuel
                  afterHeadWellFormed sourceValid.2 tailNodePrefix
                  tailChildPrefix tailNodesFit tailChildrenFit tailFuel with
                ⟨decodedTail, decodedTailEq, tailMatch⟩
              refine ⟨decodedHead :: decodedTail, ?_, ?_⟩
              · rw [emittedHead] at decodedHeadEq
                change decodeTerm? program fuel root.toNat =
                  some decodedHead at decodedHeadEq
                rw [emittedTail] at decodedTailEq
                change decodeTerms? program fuel roots =
                  some decodedTail at decodedTailEq
                rw [combined]
                simp [decodeTerms?, decodedHeadEq, decodedTailEq]
              · rcases headMatch with
                  ⟨headMeaning, headNodes, headChildren, headVariables,
                    headDepth⟩
                rcases tailMatch with
                  ⟨tailMeaning, tailNodes, tailChildren, tailVariables,
                    tailDepth⟩
                rw [afterHeadNodes] at tailNodes
                rw [afterHeadChildren] at tailChildren
                unfold DecodedTermsMatchSourceAt
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · change Terms.cons decodedHead.term
                    (decodedTerms decodedTail) = Terms.cons head tail
                  rw [headMeaning, tailMeaning]
                · simp only [concatDecodedTerms, List.foldr_cons,
                    ClaimRope.toList_append]
                  have combinedNodes := headNodes.append tailNodes
                  rw [slotRange_append] at combinedNodes
                  exact combinedNodes
                · simp only [concatDecodedTerms, List.foldr_cons,
                    ClaimRope.toList_append]
                  have combinedChildren := headChildren.append tailChildren
                  rw [slotRange_append] at combinedChildren
                  exact combinedChildren
                · change decodedHead.usedVariables.toList ++
                    (concatDecodedTerms decodedTail).2.2.toList =
                      termUsedVariables head ++ termsUsedVariables tail
                  rw [headVariables, tailVariables]
                · simp [maximumDepth, headDepth, tailDepth,
                    termsMaximumDepth]
termination_by sizeOf source

end

/-! ## Ordinary source lists -/

def termsToList : Terms -> List Term
  | .nil => []
  | .cons head tail => head :: termsToList tail

@[simp] theorem termsToList_ofList (source : List Term) :
    termsToList (Terms.ofList source) = source := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [Terms.ofList, termsToList, inductionHypothesis]

@[simp] theorem emitTerms_ofList (source : List Term) (builder : Builder) :
    emitTerms (Terms.ofList source) builder = emitTermList source builder := by
  induction source generalizing builder with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [Terms.ofList, emitTerms, emitTermList, inductionHypothesis]

@[simp] theorem termsTextsValid_ofList (source : List Term) :
    termsTextsValid (Terms.ofList source) = source.all termTextsValid := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [Terms.ofList, termsTextsValid, inductionHypothesis]

@[simp] theorem termsNodeCount_ofList (source : List Term) :
    termsNodeCount (Terms.ofList source) = termListNodeCount source := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [Terms.ofList, termsNodeCount, termListNodeCount,
        inductionHypothesis]

@[simp] theorem termsChildSlotCount_ofList (source : List Term) :
    termsChildSlotCount (Terms.ofList source) =
      termListChildSlotCount source := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [Terms.ofList, termsChildSlotCount, termListChildSlotCount,
        inductionHypothesis]

@[simp] theorem termsUsedVariables_ofList (source : List Term) :
    termsUsedVariables (Terms.ofList source) =
      source.flatMap termUsedVariables := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [Terms.ofList, termsUsedVariables, inductionHypothesis]

@[simp] theorem termsMaximumDepth_ofList (source : List Term) :
    termsMaximumDepth (Terms.ofList source) =
      termListMaximumDepth source := by
  induction source with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [Terms.ofList, termsMaximumDepth, termListMaximumDepth,
        inductionHypothesis]

/-- Semantic and ownership facts reconstructed for an ordinary emitted term
list, the representation used for rule bodies. -/
def DecodedTermListMatchesSourceAt (decoded : List DecodedTerm)
    (source : List Term) (nodeBase childBase : Nat) : Prop :=
  decoded.map DecodedTerm.term = source ∧
    (concatDecodedTerms decoded).1.toList.Perm
      (slotRange nodeBase (termListNodeCount source)) ∧
    (concatDecodedTerms decoded).2.1.toList.Perm
      (slotRange childBase (termListChildSlotCount source)) ∧
    (concatDecodedTerms decoded).2.2.toList =
      source.flatMap termUsedVariables ∧
    maximumDepth decoded = termListMaximumDepth source

theorem decodeTerms?_emitTermList
    (source : List Term) (builder : Builder) (program : Program) (fuel : Nat)
    (wellFormed : builder.WellFormed)
    (sourceValid : source.all termTextsValid = true)
    (nodePrefix : (emitTermList source builder).2.nodes <+: program.nodes)
    (childPrefix :
      (emitTermList source builder).2.children <+: program.children)
    (nodesFit : (emitTermList source builder).2.nodeCount < UInt32.size)
    (childrenFit :
      (emitTermList source builder).2.childCount < UInt32.size)
    (fuelEnough : termListMaximumDepth source < fuel) :
    ∃ decoded,
      decodeTerms? program fuel (emitTermList source builder).1 =
          some decoded ∧
        DecodedTermListMatchesSourceAt decoded source builder.nodeCount
          builder.childCount := by
  have decoded := decodeTerms?_emitTerms (Terms.ofList source) builder program
    fuel wellFormed (by simpa using sourceValid) (by simpa using nodePrefix)
    (by simpa using childPrefix) (by simpa using nodesFit)
    (by simpa using childrenFit) (by simpa using fuelEnough)
  rcases decoded with ⟨terms, decodedEq, matchFacts⟩
  refine ⟨terms, by simpa using decodedEq, ?_⟩
  rcases matchFacts with
    ⟨meaning, nodes, children, used, depth⟩
  unfold DecodedTermListMatchesSourceAt
  refine ⟨?_, by simpa using nodes, by simpa using children,
    by simpa using used, by simpa using depth⟩
  have listed := congrArg termsToList meaning
  simpa [decodedTerms] using listed

theorem termListMaximumDepth_le_termListNodeCount (source : List Term) :
    termListMaximumDepth source <= termListNodeCount source := by
  have bound := termsMaximumDepth_le_termsNodeCount (Terms.ofList source)
  simpa using bound

theorem decodedTerm_depth_le_maximumDepth {term : DecodedTerm}
    {terms : List DecodedTerm} (member : term ∈ terms) :
    term.depth <= maximumDepth terms := by
  induction terms with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [maximumDepth]
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst term
        exact Nat.le_max_left _ _
      · exact (inductionHypothesis member).trans (Nat.le_max_right _ _)

theorem emitTermList_roots_lt_nodeCount (source : List Term)
    (builder : Builder)
    (fits : (emitTermList source builder).2.nodeCount < UInt32.size) :
    ∀ root, root ∈ (emitTermList source builder).1 ->
      root.toNat < (emitTermList source builder).2.nodeCount := by
  have roots := emitTerms_roots_lt_nodeCount (Terms.ofList source) builder
    (by simpa using fits)
  simpa using roots

/-! ## One emitted rule -/

/-- The physical rule record emitted for one typed rule at a particular table
frontier.  It is data, not an independent implementation of rule semantics. -/
def emittedRuleRecord (builder : Builder) (source : TypedRule) : Rule :=
  let (head, afterHead) := emitTerm source.head builder
  let (body, _) := emitTermList source.body afterHead
  { head
    bodyOffset := UInt32.ofNat afterHead.bodyCount
    bodyCount := UInt32.ofNat body.length
    variableCount := source.variableCount
    name := source.name }

theorem emitRule_rules (builder : Builder) (source : TypedRule) :
    (emitRule builder source).rules =
      builder.rules ++ [emittedRuleRecord builder source] := by
  cases emittedHead : emitTerm source.head builder with
  | mk head afterHead =>
      have headRules := emitTerm_rulesRev_eq source.head builder
      rw [emittedHead] at headRules
      cases emittedBody : emitTermList source.body afterHead with
      | mk body afterBody =>
          have bodyRules := emitTermList_rulesRev_eq source.body afterHead
          rw [emittedBody] at bodyRules
          have afterRules : afterBody.rulesRev = builder.rulesRev :=
            bodyRules.trans headRules
          simp [emitRule, emittedRuleRecord, emittedHead, emittedBody,
            Builder.rules, afterRules]

theorem emitRule_bodies (builder : Builder) (source : TypedRule) :
    (emitRule builder source).bodies =
      builder.bodies ++ (emitTermList source.body
        (emitTerm source.head builder).2).1 := by
  cases emittedHead : emitTerm source.head builder with
  | mk head afterHead =>
      have headBodies := emitTerm_bodiesRev_eq source.head builder
      rw [emittedHead] at headBodies
      cases emittedBody : emitTermList source.body afterHead with
      | mk body afterBody =>
          have bodyBodies := emitTermList_bodiesRev_eq source.body afterHead
          rw [emittedBody] at bodyBodies
          have afterBodies : afterBody.bodiesRev = builder.bodiesRev :=
            bodyBodies.trans headBodies
          simp [emitRule, emittedHead, emittedBody, Builder.bodies,
            afterBodies, List.reverse_append]

/-- All local evidence consumed by structural rule admission, projected from
the single decidable source recognizer. -/
theorem TypedRule.locallySupported_admissionFacts (source : TypedRule)
    (supported : source.locallySupported = true) :
    bytesNonempty source.name = true ∧
      textEncodable? source.name = true ∧
      source.head.isApplication = true ∧
      termTextsValid source.head = true ∧
      source.body.all (fun term => term.isApplication) = true ∧
      source.body.all termTextsValid = true ∧
      termDepth source.head <= 4096 ∧
      termListMaximumDepth source.body <= 4096 ∧
      source.variableCount.toNat <= typedRuleNodeCount source ∧
      denseVariables source.variableCount.toNat
        (termUsedVariables source.head ++
          source.body.flatMap termUsedVariables) = true := by
  simp [TypedRule.locallySupported] at supported ⊢
  aesop

/-- Exact semantic and ownership result of independently reconstructing one
emitted rule. -/
def DecodedRuleMatchesSourceAt (decoded : DecodedRule) (source : TypedRule)
    (nodeBase childBase bodyBase : Nat) : Prop :=
  decoded.rule = source.toAdmitted ∧
    decoded.claimedNodes.toList.Perm
      (slotRange nodeBase (typedRuleNodeCount source)) ∧
    decoded.claimedChildSlots.toList.Perm
      (slotRange childBase (typedRuleChildSlotCount source)) ∧
    decoded.claimedBodySlots.toList =
      slotRange bodyBase source.body.length

theorem decodeRule?_emittedRuleRecord
    (builder : Builder) (source : TypedRule) (program : Program)
    (wellFormed : builder.WellFormed)
    (supported : source.locallySupported = true)
    (nodePrefix : (emitRule builder source).nodes <+: program.nodes)
    (childPrefix :
      (emitRule builder source).children <+: program.children)
    (bodyPrefix : (emitRule builder source).bodies <+: program.bodies)
    (nodesFit : (emitRule builder source).nodeCount < UInt32.size)
    (childrenFit : (emitRule builder source).childCount < UInt32.size)
    (bodiesFit : (emitRule builder source).bodyCount < UInt32.size) :
    ∃ decoded,
      decodeRule? program (emittedRuleRecord builder source) = some decoded ∧
        DecodedRuleMatchesSourceAt decoded source builder.nodeCount
          builder.childCount builder.bodyCount := by
  cases emittedHead : emitTerm source.head builder with
  | mk headRoot afterHead =>
      cases emittedBody : emitTermList source.body afterHead with
      | mk bodyRoots afterBody =>
          have facts := source.locallySupported_admissionFacts supported
          rcases facts with
            ⟨nameNonempty, nameEncodable, headApplication, headText,
              bodyApplications, bodyTexts, headDepthBound, bodyDepthBound,
              sourceVariableBound, sourceDense⟩
          have headCounts := emitTerm_counts source.head builder
          rw [emittedHead] at headCounts
          have headNodeCount : afterHead.nodeCount =
              builder.nodeCount + termNodeCount source.head := by
            simpa using headCounts.1
          have headChildCount : afterHead.childCount =
              builder.childCount + termChildSlotCount source.head := by
            simpa using headCounts.2.1
          have headBodyCount : afterHead.bodyCount = builder.bodyCount := by
            simpa using headCounts.2.2.2
          have bodyCounts := emitTermList_counts source.body afterHead
          rw [emittedBody] at bodyCounts
          have bodyRootsLength : bodyRoots.length = source.body.length := by
            simpa using bodyCounts.1
          have bodyNodeCount : afterBody.nodeCount =
              afterHead.nodeCount + termListNodeCount source.body := by
            simpa using bodyCounts.2.1
          have bodyChildCount : afterBody.childCount =
              afterHead.childCount + termListChildSlotCount source.body := by
            simpa using bodyCounts.2.2.1
          have bodyBodyCount : afterBody.bodyCount = afterHead.bodyCount := by
            simpa using bodyCounts.2.2.2.2
          have finalNodeCount : (emitRule builder source).nodeCount =
              afterBody.nodeCount := by
            simp [emitRule, emittedHead, emittedBody]
          have finalChildCount : (emitRule builder source).childCount =
              afterBody.childCount := by
            simp [emitRule, emittedHead, emittedBody]
          have finalBodyCount : (emitRule builder source).bodyCount =
              afterBody.bodyCount + bodyRoots.length := by
            simp [emitRule, emittedHead, emittedBody]
          have afterHeadWellFormed :=
            emitTerm_wellFormed source.head builder wellFormed
          rw [emittedHead] at afterHeadWellFormed
          have afterBodyWellFormed :=
            emitTermList_wellFormed source.body afterHead afterHeadWellFormed
          rw [emittedBody] at afterBodyWellFormed
          have finalWellFormed := emitRule_wellFormed builder source wellFormed
          have finalNodeLength :
              (emitRule builder source).nodes.length =
                (emitRule builder source).nodeCount := by
            simpa [Builder.WellFormed] using finalWellFormed.1.symm
          have programNodeBound :
              (emitRule builder source).nodeCount <= program.nodes.length := by
            rw [← finalNodeLength]
            exact nodePrefix.length_le
          have headNodesFit : afterHead.nodeCount < UInt32.size := by
            rw [finalNodeCount] at nodesFit
            rw [bodyNodeCount] at nodesFit
            omega
          have headChildrenFit : afterHead.childCount < UInt32.size := by
            rw [finalChildCount] at childrenFit
            rw [bodyChildCount] at childrenFit
            omega
          have bodyNodesFit : afterBody.nodeCount < UInt32.size := by
            simpa [finalNodeCount] using nodesFit
          have bodyChildrenFit : afterBody.childCount < UInt32.size := by
            simpa [finalChildCount] using childrenFit
          have bodyTablePrefix :=
            emitTermList_tablePrefixes source.body afterHead
          rw [emittedBody] at bodyTablePrefix
          have headNodePrefix : afterHead.nodes <+: program.nodes :=
            bodyTablePrefix.1.trans (by
              simpa [emitRule, emittedHead, emittedBody, Builder.nodes]
                using nodePrefix)
          have headChildPrefix : afterHead.children <+: program.children :=
            bodyTablePrefix.2.trans (by
              simpa [emitRule, emittedHead, emittedBody, Builder.children]
                using childPrefix)
          have bodyNodePrefix : afterBody.nodes <+: program.nodes := by
            simpa [emitRule, emittedHead, emittedBody, Builder.nodes]
              using nodePrefix
          have bodyChildPrefix : afterBody.children <+: program.children := by
            simpa [emitRule, emittedHead, emittedBody, Builder.children]
              using childPrefix
          have headFuel : termDepth source.head < program.nodes.length + 1 := by
            have depthBound := termDepth_le_termNodeCount source.head
            have ruleCount := emitRule_counts builder source
            have total : typedRuleNodeCount source <=
                (emitRule builder source).nodeCount := by
              rcases ruleCount with ⟨nodeCount, _, _, _⟩
              omega
            omega
          have bodyFuel : termListMaximumDepth source.body <
              program.nodes.length + 1 := by
            have depthBound :=
              termListMaximumDepth_le_termListNodeCount source.body
            have ruleCount := emitRule_counts builder source
            have total : termListNodeCount source.body <=
                (emitRule builder source).nodeCount := by
              rcases ruleCount with ⟨nodeCount, _, _, _⟩
              simp only [typedRuleNodeCount] at nodeCount
              omega
            omega
          rcases decodeTerm?_emitTerm source.head builder program
              (program.nodes.length + 1) wellFormed headText
              (by simpa [emittedHead] using headNodePrefix)
              (by simpa [emittedHead] using headChildPrefix)
              (by simpa [emittedHead] using headNodesFit)
              (by simpa [emittedHead] using headChildrenFit) headFuel with
            ⟨decodedHead, decodedHeadEq, headMatch⟩
          rw [emittedHead] at decodedHeadEq
          change decodeTerm? program (program.nodes.length + 1)
            headRoot.toNat = some decodedHead at decodedHeadEq
          rcases decodeTerms?_emitTermList source.body afterHead program
              (program.nodes.length + 1) afterHeadWellFormed
              bodyTexts
              (by simpa [emittedBody] using bodyNodePrefix)
              (by simpa [emittedBody] using bodyChildPrefix)
              (by simpa [emittedBody] using bodyNodesFit)
              (by simpa [emittedBody] using bodyChildrenFit) bodyFuel with
            ⟨decodedBody, decodedBodyEq, bodyMatch⟩
          rw [emittedBody] at decodedBodyEq
          change decodeTerms? program (program.nodes.length + 1) bodyRoots =
            some decodedBody at decodedBodyEq
          rcases headMatch with
            ⟨headMeaning, headNodes, headChildren, headVariables, headDepth⟩
          rcases bodyMatch with
            ⟨bodyMeaning, bodyNodes, bodyChildren, bodyVariables, bodyDepth⟩
          have totalBodyCount : (emitRule builder source).bodyCount =
              builder.bodyCount + source.body.length :=
            (emitRule_counts builder source).2.2.2
          have builderBodyBound : builder.bodyCount < UInt32.size := by
            rw [totalBodyCount] at bodiesFit
            omega
          have bodyRootsBound : bodyRoots.length < UInt32.size := by
            rw [bodyRootsLength]
            rw [totalBodyCount] at bodiesFit
            omega
          have bodyOffsetExact :
              (UInt32.ofNat afterHead.bodyCount).toNat = builder.bodyCount := by
            rw [headBodyCount]
            exact Nat.mod_eq_of_lt builderBodyBound
          have bodyLengthExact :
              (UInt32.ofNat bodyRoots.length).toNat = bodyRoots.length := by
            exact Nat.mod_eq_of_lt bodyRootsBound
          have builderBodyLength :
              builder.bodies.length = builder.bodyCount := by
            simpa [Builder.bodies] using wellFormed.2.2.2.symm
          have bodySlice :
              slice? program.bodies builder.bodyCount bodyRoots.length =
                some bodyRoots := by
            have emittedBodyPrefix :
                builder.bodies ++ bodyRoots <+: program.bodies := by
              rw [show builder.bodies ++ bodyRoots =
                  (emitRule builder source).bodies by
                rw [emitRule_bodies, emittedHead, emittedBody]]
              exact bodyPrefix
            simpa [builderBodyLength] using
              slice?_of_append_prefix builder.bodies bodyRoots program.bodies
                emittedBodyPrefix
          have variableBound :
              source.variableCount.toNat <= program.nodes.length := by
            have ruleCount := emitRule_counts builder source
            have total : typedRuleNodeCount source <=
                (emitRule builder source).nodeCount := by
              rcases ruleCount with ⟨nodeCount, _, _, _⟩
              omega
            exact sourceVariableBound.trans (total.trans programNodeBound)
          have recordEq : emittedRuleRecord builder source =
              { head := headRoot
                bodyOffset := UInt32.ofNat afterHead.bodyCount
                bodyCount := UInt32.ofNat bodyRoots.length
                variableCount := source.variableCount
                name := source.name } := by
            simp [emittedRuleRecord, emittedHead, emittedBody]
          let decoded : DecodedRule :=
            { rule := source.toAdmitted
              claimedNodes := .append decodedHead.claimedNodes
                (concatDecodedTerms decodedBody).1
              claimedChildSlots := .append decodedHead.claimedChildSlots
                (concatDecodedTerms decodedBody).2.1
              claimedBodySlots :=
                .ofList (slotRange builder.bodyCount bodyRoots.length) }
          refine ⟨decoded, ?_, ?_⟩
          · rw [recordEq]
            unfold decodeRule?
            have localValid :
                ({ head := headRoot
                   bodyOffset := UInt32.ofNat afterHead.bodyCount
                   bodyCount := UInt32.ofNat bodyRoots.length
                   variableCount := source.variableCount
                   name := source.name } : Rule).locallyValid = true := by
              simp [Rule.locallyValid, nameNonempty, textEncodable?,
                bytesNulFree] at nameEncodable ⊢
              exact nameEncodable.2
            rw [localValid]
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [if_neg (Nat.not_lt_of_ge variableBound)]
            simp only [decodedHeadEq, bodyOffsetExact, bodyLengthExact,
              bodySlice]
            change
              (decodeTerms? program (program.nodes.length + 1) bodyRoots).bind
                (fun body =>
                  if (!decodedHead.term.isApplication ||
                      !body.all fun decoded => decoded.term.isApplication) = true
                  then none
                  else if (decide (decodedHead.depth > 4096) ||
                      body.any fun decoded => decide (decoded.depth > 4096)) = true
                  then none
                  else
                    let ownership := concatDecodedTerms body
                    let usedVariables :=
                      (ClaimRope.append decodedHead.usedVariables
                        ownership.2.2).flatten
                    if !denseVariables source.variableCount.toNat
                        usedVariables then none
                    else some
                      { rule :=
                          { name := source.name
                            head := decodedHead.term
                            body := body.map DecodedTerm.term
                            variableCount := source.variableCount.toNat }
                        claimedNodes := .append decodedHead.claimedNodes
                          ownership.1
                        claimedChildSlots :=
                          .append decodedHead.claimedChildSlots ownership.2.1
                        claimedBodySlots := .ofList
                          (slotRange builder.bodyCount bodyRoots.length) }) =
                some decoded
            rw [decodedBodyEq]
            simp only [Option.bind_some]
            have decodedHeadApplication :
                decodedHead.term.isApplication = true := by
              rw [headMeaning]
              exact headApplication
            have decodedBodyApplications :
                decodedBody.all (fun term => term.term.isApplication) =
                  true := by
              rw [List.all_eq_true]
              intro term member
              have mapped : term.term ∈ decodedBody.map DecodedTerm.term :=
                List.mem_map.mpr ⟨term, member, rfl⟩
              rw [bodyMeaning] at mapped
              exact (List.all_eq_true.mp bodyApplications) term.term mapped
            rw [show (!decodedHead.term.isApplication ||
                !decodedBody.all fun term => term.term.isApplication) =
                false by
              rw [decodedHeadApplication, decodedBodyApplications]
              decide]
            simp only [Bool.false_eq_true, ↓reduceIte]
            have decodedHeadDepthBound : decodedHead.depth <= 4096 := by
              rw [headDepth]
              exact headDepthBound
            have decodedBodyTooDeep :
                decodedBody.any (fun term => term.depth > 4096) = false := by
              rw [List.any_eq_false]
              intro term member
              have eachDepth : term.depth <= maximumDepth decodedBody :=
                decodedTerm_depth_le_maximumDepth member
              rw [bodyDepth] at eachDepth
              simp only [decide_eq_true_eq]
              exact Nat.not_lt_of_ge (le_trans eachDepth bodyDepthBound)
            rw [show (decide (decodedHead.depth > 4096) ||
                decodedBody.any fun term => decide (term.depth > 4096)) =
                false by
              rw [decodedBodyTooDeep]
              simp [decodedHeadDepthBound]]
            simp only [Bool.false_eq_true, ↓reduceIte]
            have usedVariables :
                (ClaimRope.append decodedHead.usedVariables
                    (concatDecodedTerms decodedBody).2.2).flatten =
                  termUsedVariables source.head ++
                    source.body.flatMap termUsedVariables := by
              rw [ClaimRope.flatten_eq_toList,
                ClaimRope.toList_append, headVariables, bodyVariables]
            rw [usedVariables, sourceDense]
            simp [decoded, TypedRule.toAdmitted, headMeaning, bodyMeaning]
          · unfold DecodedRuleMatchesSourceAt
            dsimp only [decoded]
            refine ⟨rfl, ?_, ?_, ?_⟩
            · simp only [ClaimRope.toList_append, typedRuleNodeCount]
              rw [headNodeCount] at bodyNodes
              have combined := headNodes.append bodyNodes
              rw [slotRange_append] at combined
              exact combined
            · simp only [ClaimRope.toList_append,
                typedRuleChildSlotCount]
              rw [headChildCount] at bodyChildren
              have combined := headChildren.append bodyChildren
              rw [slotRange_append] at combined
              exact combined
            · simp [bodyRootsLength]

/-! ## Complete emitted rule inventory -/

def emittedRuleRecords : TypedProgram -> Builder -> List Rule
  | [], _ => []
  | source :: sources, builder =>
      emittedRuleRecord builder source ::
        emittedRuleRecords sources (emitRule builder source)

theorem emitRules_rules (source : TypedProgram) (builder : Builder) :
    (emitRules source builder).rules =
      builder.rules ++ emittedRuleRecords source builder := by
  induction source generalizing builder with
  | nil => simp [emitRules, emittedRuleRecords]
  | cons rule rules inductionHypothesis =>
      rw [emitRules, inductionHypothesis, emitRule_rules]
      simp [emittedRuleRecords, List.append_assoc]

def DecodedRulesMatchSourceAt (decoded : List DecodedRule)
    (source : TypedProgram) (nodeBase childBase bodyBase : Nat) : Prop :=
  decoded.map DecodedRule.rule = source.map TypedRule.toAdmitted ∧
    (concatDecodedRules decoded).1.toList.Perm
      (slotRange nodeBase (programNodeCount source)) ∧
    (concatDecodedRules decoded).2.1.toList.Perm
      (slotRange childBase (programChildSlotCount source)) ∧
    (concatDecodedRules decoded).2.2.toList.Perm
      (slotRange bodyBase (programBodySlotCount source))

theorem decodeRules?_emittedRuleRecords
    (source : TypedProgram) (builder : Builder) (program : Program)
    (wellFormed : builder.WellFormed)
    (supported : source.all TypedRule.locallySupported = true)
    (nodePrefix : (emitRules source builder).nodes <+: program.nodes)
    (childPrefix :
      (emitRules source builder).children <+: program.children)
    (bodyPrefix : (emitRules source builder).bodies <+: program.bodies)
    (nodesFit : (emitRules source builder).nodeCount < UInt32.size)
    (childrenFit : (emitRules source builder).childCount < UInt32.size)
    (bodiesFit : (emitRules source builder).bodyCount < UInt32.size) :
    ∃ decoded,
      (emittedRuleRecords source builder).mapM (decodeRule? program) =
          some decoded ∧
        DecodedRulesMatchSourceAt decoded source builder.nodeCount
          builder.childCount builder.bodyCount := by
  induction source generalizing builder with
  | nil =>
      refine ⟨[], by simp [emittedRuleRecords], ?_⟩
      simp [DecodedRulesMatchSourceAt, concatDecodedRules,
        programNodeCount, programChildSlotCount, programBodySlotCount,
        slotRange]
  | cons rule rules inductionHypothesis =>
      rw [List.all_cons, Bool.and_eq_true] at supported
      have restPrefixes := emitRules_tablePrefixes rules (emitRule builder rule)
      have firstNodePrefix :
          (emitRule builder rule).nodes <+: program.nodes := by
        exact restPrefixes.1.trans (by
          simpa [emitRules] using nodePrefix)
      have firstChildPrefix :
          (emitRule builder rule).children <+: program.children := by
        exact restPrefixes.2.1.trans (by
          simpa [emitRules] using childPrefix)
      have firstBodyPrefix :
          (emitRule builder rule).bodies <+: program.bodies := by
        exact restPrefixes.2.2.2.trans (by
          simpa [emitRules] using bodyPrefix)
      have ruleCounts := emitRule_counts builder rule
      have restCounts := emitRules_counts rules (emitRule builder rule)
      have firstNodesFit :
          (emitRule builder rule).nodeCount < UInt32.size := by
        rcases restCounts with ⟨restNodes, _, _, _⟩
        rw [emitRules] at nodesFit
        omega
      have firstChildrenFit :
          (emitRule builder rule).childCount < UInt32.size := by
        rcases restCounts with ⟨_, restChildren, _, _⟩
        rw [emitRules] at childrenFit
        omega
      have firstBodiesFit :
          (emitRule builder rule).bodyCount < UInt32.size := by
        rcases restCounts with ⟨_, _, _, restBodies⟩
        rw [emitRules] at bodiesFit
        omega
      rcases decodeRule?_emittedRuleRecord builder rule program wellFormed
          supported.1 firstNodePrefix firstChildPrefix firstBodyPrefix
          firstNodesFit firstChildrenFit firstBodiesFit with
        ⟨decodedRule, decodedRuleEq, ruleMatch⟩
      have afterWellFormed := emitRule_wellFormed builder rule wellFormed
      rcases inductionHypothesis (emitRule builder rule) afterWellFormed
          supported.2 (by simpa [emitRules] using nodePrefix)
          (by simpa [emitRules] using childPrefix)
          (by simpa [emitRules] using bodyPrefix)
          (by simpa [emitRules] using nodesFit)
          (by simpa [emitRules] using childrenFit)
          (by simpa [emitRules] using bodiesFit) with
        ⟨decodedRules, decodedRulesEq, rulesMatch⟩
      refine ⟨decodedRule :: decodedRules, ?_, ?_⟩
      · simp [emittedRuleRecords, decodedRuleEq, decodedRulesEq]
      · rcases ruleMatch with
          ⟨ruleMeaning, ruleNodes, ruleChildren, ruleBodies⟩
        rcases rulesMatch with
          ⟨rulesMeaning, rulesNodes, rulesChildren, rulesBodies⟩
        rcases ruleCounts with
          ⟨ruleNodeCount, ruleChildCount, ruleRuleCount, ruleBodyCount⟩
        rw [ruleNodeCount] at rulesNodes
        rw [ruleChildCount] at rulesChildren
        rw [ruleBodyCount] at rulesBodies
        unfold DecodedRulesMatchSourceAt
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [List.map_cons]
          rw [ruleMeaning, rulesMeaning]
        · simp only [concatDecodedRules, List.foldr_cons,
            ClaimRope.toList_append, programNodeCount]
          have combined := ruleNodes.append rulesNodes
          rw [slotRange_append] at combined
          exact combined
        · simp only [concatDecodedRules, List.foldr_cons,
            ClaimRope.toList_append, programChildSlotCount]
          have combined := ruleChildren.append rulesChildren
          rw [slotRange_append] at combined
          exact combined
        · simp only [concatDecodedRules, List.foldr_cons,
            ClaimRope.toList_append, programBodySlotCount]
          have ruleBodiesPermutation :
              decodedRule.claimedBodySlots.toList.Perm
                (slotRange builder.bodyCount rule.body.length) := by
            rw [ruleBodies]
          have combined := ruleBodiesPermutation.append rulesBodies
          rw [slotRange_append] at combined
          exact combined

theorem exactCover_eq_true_of_perm_slotRange_zero
    {width : Nat} {claims : List Nat}
    (permutation : claims.Perm (slotRange 0 width)) :
    exactCover width claims = true := by
  have rangeEquality : slotRange 0 width = List.range width := by
    simp [slotRange]
  have rangePermutation : claims.Perm (List.range width) := by
    simpa [rangeEquality] using permutation
  have lengthEquality : claims.length = width := by
    simpa using rangePermutation.length_eq
  have inRange : claims.all (fun claim => claim < width) = true := by
    rw [List.all_eq_true]
    intro claim member
    have rangeMember := rangePermutation.mem_iff.mp member
    exact decide_eq_true_iff.mpr (List.mem_range.mp rangeMember)
  have nodup : claims.Nodup :=
    (rangePermutation.nodup_iff.mpr List.nodup_range)
  simp [exactCover, lengthEquality, inRange, nodup]

/-! ## End-to-end compiler completeness -/

theorem compile_rules_eq_emittedRuleRecords (source : TypedProgram) :
    (compile source).rules = emittedRuleRecords source {} := by
  have emitted := emitRules_rules source ({} : Builder)
  simpa [compile, Builder.rules] using emitted

/-- Every source accepted by the decidable local recognizer is reconstructed
exactly by the independent structural admission pass. -/
theorem admit?_compile_of_locallySupported (source : TypedProgram)
    (supported : source.locallySupported = true) :
    admit? (compile source) = some source.toAdmitted := by
  have sourceFacts := source.locallySupported_emissionFacts supported
  rcases sourceFacts with
    ⟨sourceNonempty, rulesSupported, namesUnique, nodesFit,
      childrenFit, rulesFit, bodiesFit⟩
  have builderWellFormed := emitRules_wellFormed source ({} : Builder)
    Builder.empty_wellFormed
  have builderCounts := emitRules_counts source ({} : Builder)
  have emittedNodesFit :
      (emitRules source ({} : Builder)).nodeCount < UInt32.size := by
    have nodeCount : (emitRules source ({} : Builder)).nodeCount =
        programNodeCount source := by
      simpa using builderCounts.1
    rw [nodeCount]
    exact nodesFit
  have emittedChildrenFit :
      (emitRules source ({} : Builder)).childCount < UInt32.size := by
    have childCount : (emitRules source ({} : Builder)).childCount =
        programChildSlotCount source := by
      simpa using builderCounts.2.1
    rw [childCount]
    exact childrenFit
  have emittedBodiesFit :
      (emitRules source ({} : Builder)).bodyCount < UInt32.size := by
    have bodyCount : (emitRules source ({} : Builder)).bodyCount =
        programBodySlotCount source := by
      simpa using builderCounts.2.2.2
    rw [bodyCount]
    exact bodiesFit
  rcases decodeRules?_emittedRuleRecords source ({} : Builder)
      (compile source) Builder.empty_wellFormed rulesSupported
      (by simp [compile, Builder.nodes])
      (by simp [compile, Builder.children])
      (by simp [compile, Builder.bodies])
      emittedNodesFit emittedChildrenFit emittedBodiesFit with
    ⟨decoded, decodedEq, decodedMatch⟩
  rcases decodedMatch with
    ⟨rulesMeaning, nodesOwned, childrenOwned, bodiesOwned⟩
  have compiledRules := compile_rules_eq_emittedRuleRecords source
  have mapMEquality :
      (compile source).rules.mapM (decodeRule? (compile source)) =
        some decoded := by
    rw [compiledRules]
    exact decodedEq
  have nodesNonempty : (compile source).nodes.isEmpty = false := by
    rw [List.isEmpty_eq_false_iff]
    intro empty
    have zero : (compile source).nodes.length = 0 := by simp [empty]
    rw [(compile_table_lengths source).1] at zero
    exact (Nat.ne_of_gt (programNodeCount_positive sourceNonempty)) zero
  have rulesNonempty : (compile source).rules.isEmpty = false := by
    rw [List.isEmpty_eq_false_iff]
    intro empty
    have zero : (compile source).rules.length = 0 := by simp [empty]
    rw [(compile_table_lengths source).2.2.1] at zero
    cases source with
    | nil => simp at sourceNonempty
    | cons rule rules => simp at zero
  have admittedNamesUnique :
      ruleNamesUnique (decoded.map DecodedRule.rule) = true := by
    unfold ruleNamesUnique
    rw [rulesMeaning]
    have nameMap :
        (source.map TypedRule.toAdmitted).map AdmittedRule.name =
          source.map TypedRule.name := by
      simp [List.map_map, Function.comp_def, TypedRule.toAdmitted]
    rw [nameMap]
    exact decide_eq_true_iff.mpr namesUnique
  have nodesCover : exactCover (compile source).nodes.length
      (concatDecodedRules decoded).1.flatten = true := by
    rw [ClaimRope.flatten_eq_toList]
    rw [(compile_table_lengths source).1]
    exact exactCover_eq_true_of_perm_slotRange_zero nodesOwned
  have childrenCover : exactCover (compile source).children.length
      (concatDecodedRules decoded).2.1.flatten = true := by
    rw [ClaimRope.flatten_eq_toList]
    rw [(compile_table_lengths source).2.1]
    exact exactCover_eq_true_of_perm_slotRange_zero childrenOwned
  have bodiesCover : exactCover (compile source).bodies.length
      (concatDecodedRules decoded).2.2.flatten = true := by
    rw [ClaimRope.flatten_eq_toList]
    rw [(compile_table_lengths source).2.2.2]
    exact exactCover_eq_true_of_perm_slotRange_zero bodiesOwned
  unfold admit?
  rw [show ((compile source).nodes.isEmpty ||
      (compile source).rules.isEmpty) = false by
    simp [nodesNonempty, rulesNonempty]]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [mapMEquality]
  change
    (if (!ruleNamesUnique (decoded.map DecodedRule.rule)) = true then none
    else if (!exactCover (compile source).nodes.length
        (concatDecodedRules decoded).1.flatten) = true then none
    else if (!exactCover (compile source).children.length
        (concatDecodedRules decoded).2.1.flatten) = true then none
    else if (!exactCover (compile source).bodies.length
        (concatDecodedRules decoded).2.2.flatten) = true then none
    else some { rules := decoded.map DecodedRule.rule }) =
      some source.toAdmitted
  rw [admittedNamesUnique]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [nodesCover, childrenCover, bodiesCover]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact congrArg (fun rules => some ({ rules } : AdmittedProgram))
    rulesMeaning

theorem lower?_complete (source : TypedProgram)
    (supported : source.locallySupported = true) :
    lower? source = some source.toAdmitted := by
  have encodable := compile_encodable source supported
  have admission := admit?_compile_of_locallySupported source supported
  simp [lower?, validate?,
    (Program.encodable?_eq_true_iff (compile source)).mpr encodable,
    admission]

theorem compileBytes?_complete (source : TypedProgram)
    (supported : source.locallySupported = true) :
    compileBytes? source = some (encodeProgram (compile source)) := by
  unfold compileBytes?
  change (match validate? source (compile source) with
    | some _ => some (encodeProgram (compile source))
    | none => none) = some (encodeProgram (compile source))
  rw [show validate? source (compile source) = some source.toAdmitted by
    simpa [lower?] using lower?_complete source supported]

end Mettapedia.GSLT.LanguageDef.CompiledPlanLowering
