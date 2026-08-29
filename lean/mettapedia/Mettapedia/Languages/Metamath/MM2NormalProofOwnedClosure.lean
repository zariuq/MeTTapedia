import Mettapedia.Languages.Metamath.MM2Transformation

/-!
# Owned-code closure for assembled normal-proof execution

The normal verifier stores variable-bearing MM2 rules in inert, verifier-owned
rows and reinstalls them through scheduled reload transitions.  The base
transformation proves that the dispatch reloader can only recover executable
rules from that owned inventory.  This module packages the corresponding
two-part closure result: the reloader preserves both the executable whitelist
and the protected-row invariant in every source-relative owned state.
-/

namespace Mettapedia.Languages.Metamath.MM2NormalProofOwnedClosure

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-! ## Generic matcher provenance used by opaque reload bundles -/

/-- A successful three-factor compatible match retains the three concrete
witness atoms and the exact substitution chain that produced the final row. -/
private theorem cmatchInputSpec_three_match_chain
    {space : List Atom} {first second third : Atom}
    {substitution : Subst}
    (member : substitution ∈
      (Conformance.Computable.cmatchInputSpec [] space
        (.compat (mkPattern [first, second, third]))).map Prod.fst) :
    ∃ afterFirst afterSecond firstAtom secondAtom thirdAtom,
      firstAtom ∈ space ∧ secondAtom ∈ space ∧ thirdAtom ∈ space ∧
        Conformance.Computable.cmatchAtom [] first firstAtom =
          some afterFirst ∧
        Conformance.Computable.cmatchAtom afterFirst second secondAtom =
          some afterSecond ∧
        Conformance.Computable.cmatchAtom afterSecond third thirdAtom =
          some substitution := by
  rw [List.mem_map] at member
  obtain ⟨⟨found, witnesses⟩, foundMember, foundEq⟩ := member
  change found = substitution at foundEq
  subst substitution
  simp only [Conformance.Computable.cmatchInputSpec, mkPattern,
    Conformance.Computable.cmatchPattern,
    Conformance.Computable.cmatchPattern.go, List.mem_flatMap] at foundMember
  obtain ⟨⟨afterFirst, firstAtom⟩, firstMatch,
    afterFirstMember⟩ := foundMember
  obtain ⟨⟨afterSecond, secondAtom⟩, secondMatch,
    afterSecondMember⟩ := afterFirstMember
  obtain ⟨⟨afterThird, thirdAtom⟩, thirdMatch,
    finished⟩ := afterSecondMember
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  rcases finished with ⟨substEq, _witnessEq⟩
  subst afterThird
  rw [List.mem_filterMap] at firstMatch secondMatch thirdMatch
  obtain ⟨firstCandidate, firstMember, firstResult⟩ := firstMatch
  obtain ⟨secondCandidate, secondMember, secondResult⟩ := secondMatch
  obtain ⟨thirdCandidate, thirdMember, thirdResult⟩ := thirdMatch
  simp only [Option.map_eq_some_iff] at firstResult secondResult thirdResult
  obtain ⟨firstSubst, firstMatched, firstEq⟩ := firstResult
  obtain ⟨secondSubst, secondMatched, secondEq⟩ := secondResult
  obtain ⟨thirdSubst, thirdMatched, thirdEq⟩ := thirdResult
  cases firstEq
  cases secondEq
  cases thirdEq
  exact ⟨afterFirst, afterSecond, firstAtom, secondAtom, thirdAtom,
    firstMember, secondMember, thirdMember,
    firstMatched, secondMatched, thirdMatched⟩

/-- A variable at an aligned list position is bound to the concrete atom at
that position in the final matcher substitution, even after the suffix has
introduced further bindings. -/
private theorem matchAtomList_variable_lookup
    (prefixPatterns prefixAtoms suffixPatterns suffixAtoms : List Atom)
    (initial final : Subst) (variableName : String) (value : Atom)
    (prefixLength : prefixPatterns.length = prefixAtoms.length)
    (matched :
      matchAtom.matchAtomList initial
          (prefixPatterns ++ .var variableName :: suffixPatterns)
          (prefixAtoms ++ value :: suffixAtoms) = some final) :
    final.lookup variableName = some value := by
  induction prefixPatterns generalizing prefixAtoms initial with
  | nil =>
      cases prefixAtoms with
      | nil =>
          simp only [List.nil_append, matchAtom.matchAtomList] at matched
          cases variableMatched : matchAtom initial (.var variableName) value with
          | none => simp [variableMatched] at matched
          | some afterVariable =>
              simp only [variableMatched] at matched
              have bound : afterVariable.lookup variableName = some value := by
                have relation := matchAtom_sound variableMatched
                cases relation with
                | var_fresh _ => simp [Subst.lookup]
                | var_bound lookup => exact lookup
              exact
                (matchAtom_lookupExtends.matchAtomList_lookupExtends matched)
                  variableName value bound
      | cons atom atoms =>
          simp at prefixLength
  | cons pattern patterns induction =>
      cases prefixAtoms with
      | nil => simp at prefixLength
      | cons atom atoms =>
          simp only [List.length_cons, Nat.succ.injEq] at prefixLength
          simp only [List.cons_append, matchAtom.matchAtomList] at matched
          cases headMatched : matchAtom initial pattern atom with
          | none => simp [headMatched] at matched
          | some afterHead =>
              simp only [headMatched] at matched
              exact induction atoms afterHead prefixLength matched

/-- The body reloader's self pattern can only match an executable shell at
its exact scheduler location, while retaining the two opaque byte fields. -/
private theorem matchAtom_bodyReload_self
    {result : Subst} {atom : Atom}
    (matched : matchAtom []
      (.expression
        [.symbol "exec",
          .expression [.symbol "11", .symbol "mm-normal-body-reload"],
          .var "body-reload-self-input",
          .var "body-reload-self-output"]) atom = some result) :
    ∃ input output,
      atom =
          .expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              input, output] ∧
        result.lookup "body-reload-self-input" = some input ∧
        result.lookup "body-reload-self-output" = some output := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons execMatch tail1 =>
      cases execMatch
      cases tail1 with
      | expr_cons locationMatch tail2 =>
          cases locationMatch with
          | expr_cons locationHead locationTail =>
              cases locationHead
              cases locationTail with
              | expr_cons locationName locationNil =>
                  cases locationName
                  cases locationNil
                  cases tail2 with
                  | expr_cons inputMatch tail3 =>
                      cases inputMatch with
                      | var_fresh _ =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  refine ⟨_, _, rfl, ?_, ?_⟩
                                  · simp [Subst.lookup]
                                  · simp [Subst.lookup]
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl,
                                    by simp [Subst.lookup], outputLookup⟩
                      | var_bound inputLookup =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    by simp [Subst.lookup]⟩
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    outputLookup⟩

/-- A successful body-bundle match fixes the complete six-cell carrier
shape.  The five payload atoms are still opaque at this point. -/
private theorem matchAtom_bodyReload_bundle_shape
    {before result : Subst} {atom : Atom}
    (matched : matchAtom before
      (.expression
        [.symbol "mm-internal-body-match-rules",
          .var "body-rule-const", .var "body-rule-variable",
          .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
          .var "body-rule-nil"]) atom = some result) :
    ∃ constRule variableRule prefixNilRule prefixConsRule nilRule,
      atom =
        .expression
          [.symbol "mm-internal-body-match-rules", constRule, variableRule,
            prefixNilRule, prefixConsRule, nilRule] := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatch tail1 =>
      cases headMatch
      cases tail1 with
      | expr_cons _ tail2 =>
          cases tail2 with
          | expr_cons _ tail3 =>
              cases tail3 with
              | expr_cons _ tail4 =>
                  cases tail4 with
                  | expr_cons _ tail5 =>
                      cases tail5 with
                      | expr_cons _ nilMatch =>
                          cases nilMatch
                          exact ⟨_, _, _, _, _, rfl⟩

/-- In an owned machine state, the body reloader's third matcher witness is
the one exact generated body-rule bundle.  A same-shaped row with altered
payloads is not authorized merely by its head symbol. -/
private theorem normalBodyReload_bundle_witness_exact
    {space : List Atom} (state : NormalProofMachineOwnedState space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst) :
    ∃ afterFirst afterSecond firstAtom secondAtom,
      firstAtom ∈
          (normalBodyReloadDirective.atom ::
            space.erase normalBodyReloadDirective.atom) ∧
        secondAtom ∈
          (normalBodyReloadDirective.atom ::
            space.erase normalBodyReloadDirective.atom) ∧
        Conformance.Computable.cmatchAtom []
            (.expression
              [.symbol "exec",
                .expression
                  [.symbol "11", .symbol "mm-normal-body-reload"],
                .var "body-reload-self-input",
                .var "body-reload-self-output"])
            firstAtom = some afterFirst ∧
        Conformance.Computable.cmatchAtom afterFirst
            (.expression
              [.symbol "mm-reload-body-match",
                .var "body-reload-proof", .var "body-reload-pc"])
            secondAtom = some afterSecond ∧
        Conformance.Computable.cmatchAtom afterSecond
            (.expression
              [.symbol "mm-internal-body-match-rules",
                .var "body-rule-const", .var "body-rule-variable",
                .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
                .var "body-rule-nil"])
            normalBodyMatchRuleBundle = some substitution := by
  have rowMember' : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        (.compat (mkPattern
          [(.expression
              [.symbol "exec",
                .expression
                  [.symbol "11", .symbol "mm-normal-body-reload"],
                .var "body-reload-self-input",
                .var "body-reload-self-output"] : Atom),
           .expression
              [.symbol "mm-reload-body-match",
                .var "body-reload-proof", .var "body-reload-pc"],
           .expression
              [.symbol "mm-internal-body-match-rules",
                .var "body-rule-const", .var "body-rule-variable",
                .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
                .var "body-rule-nil"]]))).map Prod.fst := by
    change substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst
    exact rowMember
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom, thirdAtom,
      firstMember, secondMember, thirdMember,
      firstMatched, secondMatched, thirdMatched⟩ :=
    cmatchInputSpec_three_match_chain rowMember'
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  obtain ⟨constRule, variableRule, prefixNilRule, prefixConsRule,
      nilRule, thirdEq⟩ :=
    matchAtom_bodyReload_bundle_shape thirdMatched
  have thirdInSpace : thirdAtom ∈ space := by
    rcases List.mem_cons.mp thirdMember with selected | erased
    · rw [thirdEq] at selected
      simp [normalBodyReloadDirective, normalBodyReloadRule] at selected
    · exact List.mem_of_mem_erase erased
  have authorized := state.2 thirdAtom thirdInSpace
  have internalShape : isVerifierOwnedInternalRowShape thirdAtom = true := by
    rw [thirdEq]
    rfl
  have authorizedMember := authorized internalShape
  have thirdExact : thirdAtom = normalBodyMatchRuleBundle := by
    rw [thirdEq] at authorizedMember
    simp [normalVerifierInternalRows, normalBodyMatchRuleBundle,
      normalBodyBuildRuleBundle, normalDispatchRuleRows,
      normalDispatchRuleRow] at authorizedMember
    rcases authorizedMember with
      ⟨rfl, rfl, rfl, rfl, rfl⟩
    simpa [normalBodyMatchRuleBundle] using thirdEq
  rw [thirdExact] at thirdMatched
  rw [← Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  exact ⟨afterFirst, afterSecond, firstAtom, secondAtom,
    firstMember, secondMember, firstMatched, secondMatched, thirdMatched⟩

/-- Exact ownership of the body-rule carrier determines all five final
matcher bindings.  These equalities are the authorization facts consumed by
the variable-valued add sinks. -/
private theorem normalBodyReload_bundle_lookups
    {space : List Atom} (state : NormalProofMachineOwnedState space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst) :
    substitution.lookup "body-rule-const" =
        some normalBodyMatchConstRule ∧
      substitution.lookup "body-rule-variable" =
        some normalBodyMatchVariableRule ∧
      substitution.lookup "body-rule-prefix-nil" =
        some normalBodyPrefixNilRule ∧
      substitution.lookup "body-rule-prefix-cons" =
        some normalBodyPrefixConsRule ∧
      substitution.lookup "body-rule-nil" =
        some normalBodyMatchNilRule := by
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom,
      _firstMember, _secondMember, _firstMatched, _secondMatched,
      thirdMatched⟩ := normalBodyReload_bundle_witness_exact state rowMember
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  have listMatched :
      matchAtom.matchAtomList afterSecond
        [.symbol "mm-internal-body-match-rules",
          .var "body-rule-const", .var "body-rule-variable",
          .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
          .var "body-rule-nil"]
        [.symbol "mm-internal-body-match-rules",
          normalBodyMatchConstRule, normalBodyMatchVariableRule,
          normalBodyPrefixNilRule, normalBodyPrefixConsRule,
          normalBodyMatchNilRule] = some substitution := by
    simpa [normalBodyMatchRuleBundle, matchAtom] using thirdMatched
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules"]
      [.symbol "mm-internal-body-match-rules"]
      [.var "body-rule-variable", .var "body-rule-prefix-nil",
        .var "body-rule-prefix-cons", .var "body-rule-nil"]
      [normalBodyMatchVariableRule, normalBodyPrefixNilRule,
        normalBodyPrefixConsRule, normalBodyMatchNilRule]
      afterSecond substitution "body-rule-const" normalBodyMatchConstRule
      rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules", .var "body-rule-const"]
      [.symbol "mm-internal-body-match-rules", normalBodyMatchConstRule]
      [.var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
        .var "body-rule-nil"]
      [normalBodyPrefixNilRule, normalBodyPrefixConsRule,
        normalBodyMatchNilRule]
      afterSecond substitution "body-rule-variable"
      normalBodyMatchVariableRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules", .var "body-rule-const",
        .var "body-rule-variable"]
      [.symbol "mm-internal-body-match-rules", normalBodyMatchConstRule,
        normalBodyMatchVariableRule]
      [.var "body-rule-prefix-cons", .var "body-rule-nil"]
      [normalBodyPrefixConsRule, normalBodyMatchNilRule]
      afterSecond substitution "body-rule-prefix-nil"
      normalBodyPrefixNilRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules", .var "body-rule-const",
        .var "body-rule-variable", .var "body-rule-prefix-nil"]
      [.symbol "mm-internal-body-match-rules", normalBodyMatchConstRule,
        normalBodyMatchVariableRule, normalBodyPrefixNilRule]
      [.var "body-rule-nil"] [normalBodyMatchNilRule]
      afterSecond substitution "body-rule-prefix-cons"
      normalBodyPrefixConsRule rfl listMatched
  · exact matchAtomList_variable_lookup
      [.symbol "mm-internal-body-match-rules", .var "body-rule-const",
        .var "body-rule-variable", .var "body-rule-prefix-nil",
        .var "body-rule-prefix-cons"]
      [.symbol "mm-internal-body-match-rules", normalBodyMatchConstRule,
        normalBodyMatchVariableRule, normalBodyPrefixNilRule,
        normalBodyPrefixConsRule]
      [] [] afterSecond substitution "body-rule-nil"
      normalBodyMatchNilRule rfl listMatched

/-- The body reloader's self shell is recovered from an executable witness
already present in the owned state (or from the selected directive prepended
to the read space).  It therefore cannot synthesize foreign executable code. -/
private theorem normalBodyReload_captured_self_raw_authorized
    {space : List Atom} {substitution : Subst} {captured : Atom}
    {raw : RawExecFact}
    (state : NormalProofMachineOwnedState space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution
        (.expression
          [.symbol "exec",
            .expression [.symbol "11", .symbol "mm-normal-body-reload"],
            .var "body-reload-self-input",
            .var "body-reload-self-output"]) = some captured)
    (extracts : extractRawExecFact captured = some raw) :
    raw ∈ normalProofMachineRawFacts := by
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom,
      firstMember, _secondMember, firstMatched, secondMatched,
      thirdMatched⟩ := normalBodyReload_bundle_witness_exact state rowMember
  rw [Conformance.cmatchAtom_eq_matchAtom] at firstMatched secondMatched
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  obtain ⟨input, output, firstEq, inputLookup, outputLookup⟩ :=
    matchAtom_bodyReload_self firstMatched
  have finalExtends : substitution.lookupExtends afterFirst :=
    Subst.lookupExtends_trans
      (matchAtom_lookupExtends secondMatched)
      (matchAtom_lookupExtends thirdMatched)
  have finalInputLookup :
      substitution.lookup "body-reload-self-input" = some input :=
    finalExtends "body-reload-self-input" input inputLookup
  have finalOutputLookup :
      substitution.lookup "body-reload-self-output" = some output :=
    finalExtends "body-reload-self-output" output outputLookup
  have applied :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              .var "body-reload-self-input",
              .var "body-reload-self-output"]) = captured := by
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · exact Option.some.inj instantiates
    · simp at instantiates
  have appliedFirst :
      applySubst substitution
          (.expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              .var "body-reload-self-input",
              .var "body-reload-self-output"]) = firstAtom := by
    rw [firstEq]
    change
      Atom.expression
          [.symbol "exec",
            .expression [.symbol "11", .symbol "mm-normal-body-reload"],
            (substitution.lookup "body-reload-self-input").getD
              (.var "body-reload-self-input"),
            (substitution.lookup "body-reload-self-output").getD
              (.var "body-reload-self-output")] =
        Atom.expression
          [.symbol "exec",
            .expression [.symbol "11", .symbol "mm-normal-body-reload"],
            input, output]
    rw [finalInputLookup, finalOutputLookup]
    rfl
  have capturedEq : captured = firstAtom := applied.symm.trans appliedFirst
  rw [capturedEq] at extracts
  rcases List.mem_cons.mp firstMember with selected | prior
  · rw [selected] at extracts
    exact List.mem_filterMap.mpr
      ⟨normalBodyReloadDirective.atom,
        by simp [normalBodyReloadDirective, normalProofMachineRules],
        extracts⟩
  · apply state.1.2 raw
    exact List.mem_filterMap.mpr
      ⟨firstAtom, List.mem_of_mem_erase prior, extracts⟩

/-- Every variable-valued body-rule add sink is fixed by the exact owned
bundle and therefore selects one of the five generated matcher rules. -/
private theorem normalBodyReload_captured_rule_authorized
    {space : List Atom} {substitution : Subst} {authored captured : Atom}
    (state : NormalProofMachineOwnedState space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalBodyReloadDirective.atom ::
          space.erase normalBodyReloadDirective.atom)
        normalBodyReloadDirective.rule.input).map Prod.fst)
    (authoredMember : authored ∈
      [(.var "body-rule-const" : Atom), .var "body-rule-variable",
        .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
        .var "body-rule-nil"])
    (instantiates :
      instantiateTemplateAtom? substitution authored = some captured) :
    captured ∈
      [normalBodyMatchConstRule, normalBodyMatchVariableRule,
        normalBodyPrefixNilRule, normalBodyPrefixConsRule,
        normalBodyMatchNilRule] := by
  obtain ⟨constLookup, variableLookup, prefixNilLookup,
      prefixConsLookup, nilLookup⟩ :=
    normalBodyReload_bundle_lookups state rowMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at authoredMember
  rcases authoredMember with rfl | rfl | rfl | rfl | rfl
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      constLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      variableLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      prefixNilLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      prefixConsLookup] at instantiates
    subst captured
    simp
  · simp [instantiateTemplateAtom?, templateCovered, applySubst,
      nilLookup] at instantiates
    subst captured
    simp

/-- Every executable atom introduced by the body-matcher reloader is either
its already-authorized self shell or one of the five rules reconstructed from
the exact owned bundle. -/
theorem normalBodyReload_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyReloadDirective.atom ::
        space.erase normalBodyReloadDirective.atom)
      normalBodyReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalBodyReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "11", .symbol "mm-normal-body-reload"],
          .var "body-reload-self-input", .var "body-reload-self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-reload-body-match", .var "body-reload-proof",
          .var "body-reload-pc"]),
     Sink.add (.var "body-rule-const"),
     Sink.add (.var "body-rule-variable"),
     Sink.add (.var "body-rule-prefix-nil"),
     Sink.add (.var "body-rule-prefix-cons"),
     Sink.add (.var "body-rule-nil")] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              .var "body-reload-self-input",
              .var "body-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "body-rule-const" : Atom), .var "body-rule-variable",
            .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
            .var "body-rule-nil"] := by
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    exact normalBodyReload_captured_self_raw_authorized state rowMember
      instantiates extracts
  · have authorized :=
      normalBodyReload_captured_rule_authorized state rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    exact List.mem_filterMap.mpr ⟨atom, machineMember, extracts⟩

/-- The same body-reload firing cannot create a reserved inert carrier: its
self shell and all five recovered payloads are executable verifier rules. -/
theorem normalBodyReload_additions_internal_closed
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyReloadDirective.atom ::
        space.erase normalBodyReloadDirective.atom)
      normalBodyReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalBodyReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "11", .symbol "mm-normal-body-reload"],
          .var "body-reload-self-input", .var "body-reload-self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-reload-body-match", .var "body-reload-proof",
          .var "body-reload-pc"]),
     Sink.add (.var "body-rule-const"),
     Sink.add (.var "body-rule-variable"),
     Sink.add (.var "body-rule-prefix-nil"),
     Sink.add (.var "body-rule-prefix-cons"),
     Sink.add (.var "body-rule-nil")] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "11", .symbol "mm-normal-body-reload"],
              .var "body-reload-self-input",
              .var "body-reload-self-output"] : Atom) ∨
        authored ∈
          [(.var "body-rule-const" : Atom), .var "body-rule-variable",
            .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
            .var "body-rule-nil"] := by
    simpa using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    unfold instantiateTemplateAtom? at instantiates
    split at instantiates
    · have applied := Option.some.inj instantiates
      have atomShape :
          ∃ input output,
            atom =
              .expression
                [.symbol "exec",
                  .expression
                    [.symbol "11", .symbol "mm-normal-body-reload"],
                  input, output] :=
        ⟨_, _, applied.symm⟩
      rcases atomShape with ⟨input, output, rfl⟩
      simp [isVerifierOwnedInternalRowShape,
        isVerifierOwnedInternalNamespace] at internalShape
    · simp at instantiates
  · have authorized :=
      normalBodyReload_captured_rule_authorized state rowMember ruleSink
        instantiates
    have machineMember : atom ∈ normalProofMachineRules := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at authorized
      rcases authorized with rfl | rfl | rfl | rfl | rfl <;>
        simp [normalProofMachineRules]
    have safe :=
      (List.all_eq_true.mp normalProofMachineRules_no_internal_row_shape)
        atom machineMember
    have notInternal : isVerifierOwnedInternalRowShape atom = false := by
      simpa only [Bool.not_eq_true'] using safe
    rw [notInternal] at internalShape
    contradiction

/-- The body reloader satisfies the complete owned-addition obligation in
every represented space. -/
theorem normalBodyReload_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalBodyReloadDirective.atom ::
        space.erase normalBodyReloadDirective.atom)
      normalBodyReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalBodyReloadDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalBodyReloadDirective.rule.tmpl := by
  exact ⟨normalBodyReload_additions_raw_closed state,
    normalBodyReload_additions_internal_closed state⟩

theorem NormalProofMachineOwnedState.fire_bodyReload
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space normalBodyReloadDirective) := by
  rcases normalBodyReload_owned_additions_closed state with
    ⟨rawClosed, internalClosed⟩
  exact state.fire normalBodyReloadDirective
    (by
      change normalBodyReloadDirective ∈
        normalProofMachineRules.filterMap extractSupportedSourceExecFact
      exact List.mem_filterMap.mpr
        ⟨normalBodyReloadRule,
          by simp [normalProofMachineRules],
          extract_normalBodyReloadRule_exact⟩)
    rawClosed internalClosed



/-- The dispatch reloader cannot introduce a protected inert row.  Its two
add sinks produce either its executable self shell or a rule recovered from
the exact verifier-owned dispatch relation; both have ordinary `exec` shape,
not a reserved inert-row head. -/
theorem normalDispatchReload_additions_internal_closed
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDispatchReloadDirective.atom ::
        space.erase normalDispatchReloadDirective.atom)
      normalDispatchReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
      normalDispatchReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  change Sink.add authored ∈
    [Sink.add
      (.expression
        [.symbol "exec",
          .expression [.symbol "32", .symbol "mm-normal-dispatch-reload"],
          .var "reload-self-input", .var "reload-self-output"]),
     Sink.remove
      (.expression
        [.symbol "mm-reload-normal-dispatch", .var "reload-proof"]),
     Sink.add (.var "reload-rule")] at sinkMember
  have authoredCases :
      authored =
          (.expression
            [.symbol "exec",
              .expression [.symbol "32", .symbol "mm-normal-dispatch-reload"],
              .var "reload-self-input", .var "reload-self-output"] : Atom) ∨
        authored = .var "reload-rule" := by
    simpa [normalDispatchReloadDirective] using sinkMember
  rcases authoredCases with selfSink | ruleSink
  · rw [selfSink] at instantiates
    have atomShape :
        ∃ input output,
          atom =
            .expression
              [.symbol "exec",
                .expression
                  [.symbol "32", .symbol "mm-normal-dispatch-reload"],
                input, output] := by
      unfold instantiateTemplateAtom? at instantiates
      split at instantiates
      · have applied := Option.some.inj instantiates
        refine ⟨_, _, applied.symm⟩
      · simp at instantiates
    rcases atomShape with ⟨input, output, rfl⟩
    simp [isVerifierOwnedInternalRowShape,
      isVerifierOwnedInternalNamespace] at internalShape
  · rw [ruleSink] at instantiates
    have authorized : atom ∈ normalProofMachineRules :=
      normalDispatchReload_captured_rule_authorized state rowMember
        instantiates
    have safe :=
      (List.all_eq_true.mp normalProofMachineRules_no_internal_row_shape)
        atom authorized
    have notInternal : isVerifierOwnedInternalRowShape atom = false := by
      simpa only [Bool.not_eq_true'] using safe
    rw [notInternal] at internalShape
    contradiction

/-- The selected dispatch-reload transition satisfies the complete local
owned-addition obligation, with no separately supplied authorization witness. -/
theorem normalDispatchReload_owned_additions_closed
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDispatchReloadDirective.atom ::
        space.erase normalDispatchReloadDirective.atom)
      normalDispatchReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        normalDispatchReloadDirective.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        normalDispatchReloadDirective.rule.tmpl := by
  exact ⟨normalDispatchReload_additions_raw_closed state,
    normalDispatchReload_additions_internal_closed state⟩

/-- Firing the actual dispatch reloader preserves the full owned normal-proof
machine invariant for an arbitrary represented space. -/
theorem NormalProofMachineOwnedState.fire_dispatchReload
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space normalDispatchReloadDirective) := by
  rcases normalDispatchReload_owned_additions_closed state with
    ⟨rawClosed, internalClosed⟩
  exact state.fire normalDispatchReloadDirective
    (by
      change normalDispatchReloadDirective ∈
        normalProofMachineRules.filterMap extractSupportedSourceExecFact
      exact List.mem_filterMap.mpr
        ⟨normalDispatchReloadRule,
          by simp [normalProofMachineRules],
          extract_normalDispatchReloadRule_exact⟩)
    rawClosed internalClosed

/-! ## Negative control -/

private def protectedCarrier : Atom :=
  .expression
    [.symbol "mm-internal-normal-dispatch-rule", .symbol "forged"]

/-- The protected-row conclusion is substantive: the reserved inert carrier
shape is recognized and therefore cannot be discharged by the executable-head
argument used for legitimate reload additions. -/
theorem protectedCarrier_is_internal :
    isVerifierOwnedInternalRowShape protectedCarrier = true := by
  rfl

#print axioms normalDispatchReload_additions_internal_closed
#print axioms normalDispatchReload_owned_additions_closed
#print axioms NormalProofMachineOwnedState.fire_dispatchReload
#print axioms protectedCarrier_is_internal

end Mettapedia.Languages.Metamath.MM2NormalProofOwnedClosure
