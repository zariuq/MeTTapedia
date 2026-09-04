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

end Mettapedia.GSLT.LanguageDef.CompiledPlanLowering
