import Mettapedia.Languages.Metamath.InferenceGeneratedProvesForestAlgebra
import Mettapedia.Languages.Metamath.InferenceProjectionLookupCompleteness

/-!
# Proof-relevant reflection of one normal Metamath step

`NativeStackCertificate` retains the exact generated forest represented by a
normal-proof stack, the exact postfix labels already processed, and equality
of the complete runtime proof state with a fixed non-stack base state.  A
successful `DB.stepNormal` extends this certificate by one source label.

The assertion branch splits the retained forest at the exact consumed suffix.
Its children are therefore the original stored trees, not reconstructed
proofs.  Only the new assertion node is selected from the existing
proof-relevant runtime agreement theorem.

This is a one-step theorem conditional on a successful prefix projection.  It
does not infer parser chronology from the projection's label-sorted assertion
list and does not yet fold over a complete source proof.
-/

namespace Mettapedia.Languages.Metamath.InferenceNormalStepReflection

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceProjectionLookupCompleteness
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement
open Mettapedia.Languages.Metamath.InferenceRuntimeAssertionGraph
open Mettapedia.Languages.Metamath.InferenceAssertionStepAgreement
open Mettapedia.Languages.Metamath.InferenceAssertionStackInvariant
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Exact proof-state certificate -/

/-- A proof-relevant account of a normal-proof stack.  The external `base`
index fixes every non-stack field for the entire fold; `state_eq` is therefore
an equality of complete proof states rather than a stack-only relation. -/
structure NativeStackCertificate
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation) (base : RuntimeProofState)
    (processedLabels : List String) (state : RuntimeProofState) : Type where
  formulas : List ConstantHeadedFormula
  forest : GeneratedProvesForest projection target formulas
  labels_eq : forest.labels = processedLabels
  state_eq :
    state = {base with stack := runtimeFormulaArray formulas}
  stackRespects :
    Metamath.Kernel.StackRespectsFrame db db.frame state.stack

/-- The empty normal-proof prefix has an exact empty forest and an otherwise
unchanged fixed base state. -/
def NativeStackCertificate.empty
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation) (base : RuntimeProofState) :
    NativeStackCertificate db projection target base []
      {base with stack := #[]} :=
  { formulas := []
    forest := .nil
    labels_eq := rfl
    state_eq := by simp [runtimeFormulaArray]
    stackRespects := by
      intro index hindex
      simp at hindex }

theorem NativeStackCertificate.stack_eq
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {base : RuntimeProofState}
    {processedLabels : List String} {state : RuntimeProofState}
    (certificate : NativeStackCertificate db projection target base
      processedLabels state) :
    state.stack = runtimeFormulaArray certificate.formulas := by
  have hstate := congrArg (fun current : RuntimeProofState => current.stack)
    certificate.state_eq
  simpa using hstate

/-! ## Array/list boundaries for the consumed assertion suffix -/

theorem runtimeFormulaArray_append_singleton
    (formulas : List ConstantHeadedFormula)
    (formula : ConstantHeadedFormula) :
    runtimeFormulaArray (formulas ++ [formula]) =
      (runtimeFormulaArray formulas).push formula.toRuntime := by
  apply Array.ext'
  simp [runtimeFormulaArray]

/-- Split off an exact suffix of the requested length. -/
theorem exists_append_suffix_of_le_length
    (formulas : List ConstantHeadedFormula) (count : Nat)
    (hcount : count ≤ formulas.length) :
    ∃ prefixFormulas suffix : List ConstantHeadedFormula,
      formulas = prefixFormulas ++ suffix ∧ suffix.length = count := by
  refine ⟨formulas.take (formulas.length - count),
    formulas.drop (formulas.length - count), ?_, ?_⟩
  · exact (List.take_append_drop (formulas.length - count) formulas).symm
  · simp only [List.length_drop]
    omega

/-- Transport only the dependent formula-list index of a retained forest. -/
def castGeneratedProvesForestIndex
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {left right : List ConstantHeadedFormula} (hindex : left = right)
    (forest : GeneratedProvesForest projection target left) :
    GeneratedProvesForest projection target right := by
  subst right
  exact forest

@[simp] theorem labels_castGeneratedProvesForestIndex
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {left right : List ConstantHeadedFormula} (hindex : left = right)
    (forest : GeneratedProvesForest projection target left) :
    (castGeneratedProvesForestIndex hindex forest).labels = forest.labels := by
  subst right
  rfl

/-! ## Runtime conclusion decoding -/

/-- A successful substitution of a constant-headed runtime formula has a
unique constant-headed view. -/
theorem constantHeadedFormula_of_subst_ok
    (source : ConstantHeadedFormula)
    (substitution : Std.HashMap String RuntimeFormula)
    (conclusion : RuntimeFormula)
    (hsubst : source.toRuntime.subst substitution = .ok conclusion) :
    ∃ result : ConstantHeadedFormula,
      conclusion = result.toRuntime := by
  have hsourceWellFormed : Metamath.WF.WellFormedFormula source.toRuntime :=
    Metamath.WF.wellFormedFormula_of_hasConstHead
      source.hasConstHead_toRuntime
  have hhead : conclusion.hasConstHead = true :=
    Metamath.Kernel.subst_preserves_constHead'
      substitution source.toRuntime conclusion hsourceWellFormed hsubst
  obtain ⟨result, hdecode⟩ :=
    ConstantHeadedFormula.ofRuntime?_success_iff_hasConstHead conclusion |>.mpr
      hhead
  exact ⟨result,
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff conclusion result).mp
      hdecode⟩

/-! ## One arbitrary successful normal step -/

noncomputable section

/-- Reflect one arbitrary successful `stepNormal` transition into the exact
proof-relevant stack certificate.  The new assertion node is selected from
the existing runtime/native equivalence.  In contrast, its premise forest is
the exact right suffix split from `certificate.forest`.

The result is noncomputable because the existing reverse interfaces expose
the current step's projected view, suffix witnesses, and local assertion node
through Prop-valued `Exists`/`Nonempty`.  Choice never selects any prior tree,
and no executable proof extractor is claimed here. -/
def NativeStackCertificate.stepNormal
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {base state next : RuntimeProofState}
    {processedLabels : List String} (label : String)
    (hprojection : presentationOfProjection? projection = some target.1)
    (hproject : projectPrefix? db = some projection)
    (certificate : NativeStackCertificate db projection target base
      processedLabels state)
    (hstep : db.stepNormal state label = .ok next) :
    NativeStackCertificate db projection target base
      (processedLabels ++ [label]) next := by
  rcases certificate with
    ⟨formulas, forest, hlabels, hstate, hstack⟩
  cases hfind : db.find? label with
  | none =>
      simp [Metamath.Verify.DB.stepNormal, hfind] at hstep
  | some object =>
      cases object with
      | const name =>
          simp [Metamath.Verify.DB.stepNormal, hfind] at hstep
      | var name =>
          simp [Metamath.Verify.DB.stepNormal, hfind] at hstep
      | hyp essential runtimeFormula embeddedLabel =>
          have hscope : label ∈ db.frame.hyps.toList := by
            by_contra hout
            simp [Metamath.Verify.DB.stepNormal, hfind, hout] at hstep
          let reflectedHypothesis :=
            projectedActiveHypothesis_of_runtime_member db projection label
              embeddedLabel essential runtimeFormula hproject hscope hfind
          let hypothesis := Classical.choose reflectedHypothesis
          have hhypothesis := Classical.choose_spec reflectedHypothesis
          rcases hhypothesis with
            ⟨hmember, hhypothesisLabel, _hessential, _hformula,
              _hembedded⟩
          have hcanonicalStep :
              db.stepNormal state hypothesis.label =
                .ok (state.push hypothesis.formula.toRuntime) :=
            activeHypothesis_stepNormal db projection hypothesis state
              hproject hmember
          have hnext :
              next = state.push hypothesis.formula.toRuntime := by
            rw [hhypothesisLabel] at hcanonicalStep
            exact Except.ok.inj (hstep.symm.trans hcanonicalStep)
          let tree : GeneratedProvesTree projection target hypothesis.formula :=
            .active hypothesis hmember
          let singleton : GeneratedProvesForest projection target
              [hypothesis.formula] := .cons tree .nil
          refine
            { formulas := formulas ++ [hypothesis.formula]
              forest := forest.append singleton
              labels_eq := ?_
              state_eq := ?_
              stackRespects := ?_ }
          · simp [singleton, tree, hlabels,
              GeneratedProvesForest.labels,
              GeneratedProvesTree.labels]
            exact hhypothesisLabel
          · calc
              next = state.push hypothesis.formula.toRuntime := hnext
              _ = ({base with
                    stack := runtimeFormulaArray formulas} :
                    RuntimeProofState).push hypothesis.formula.toRuntime := by
                  rw [hstate]
              _ = {base with
                    stack := runtimeFormulaArray
                      (formulas ++ [hypothesis.formula])} := by
                  rw [runtimeFormulaArray_append_singleton]
                  rfl
          · rw [hnext]
            exact activeHypothesis_step_stackRespectsFrame db projection
              hypothesis state hproject hmember hstack
      | assert runtimeFormula runtimeFrame embeddedLabel =>
          let reflectedAssertion :=
            projectedAssertion_of_runtime_lookup db projection label
              embeddedLabel runtimeFormula runtimeFrame hproject hfind
          let assertion := Classical.choose reflectedAssertion
          have hassertion := Classical.choose_spec reflectedAssertion
          rcases hassertion with
            ⟨hmember, hassertionLabel, hformula, hframe, hembedded⟩
          have hlookupAssertion :
              db.find? assertion.label =
                some (.assert assertion.formula.toRuntime assertion.frame
                  assertion.label) := by
            calc
              db.find? assertion.label = db.find? label := by
                rw [hassertionLabel]
              _ = some (.assert runtimeFormula runtimeFrame embeddedLabel) :=
                hfind
              _ = some (.assert assertion.formula.toRuntime assertion.frame
                    assertion.label) := by
                apply congrArg some
                apply (Metamath.Verify.Object.assert.injEq _ _ _ _ _ _).mpr
                exact ⟨hformula, hframe,
                  hembedded.trans hassertionLabel.symm⟩
          have hstepAssertion :
              db.stepNormal state assertion.label = .ok next := by
            rw [hassertionLabel]
            exact hstep
          have hgraph :
              AssertionLabelStepGraph db state assertion.label next :=
            (assertionLabelStepGraph_iff_stepNormal_ok_of_lookup
              db state next assertion.label assertion.formula.toRuntime
                assertion.frame assertion.label hlookupAssertion).mpr
                  hstepAssertion
          let witness := Classical.choice hgraph
          have hobjects :
              some (Metamath.Verify.Object.assert witness.assertionFormula
                witness.assertionFrame witness.embeddedLabel) =
              some (Metamath.Verify.Object.assert assertion.formula.toRuntime
                assertion.frame assertion.label) := by
            rw [← witness.lookup, ← hlookupAssertion]
          obtain ⟨hwitnessFormula, hwitnessFrame, _hwitnessEmbedded⟩ :=
            Metamath.Verify.Object.assert.inj (Option.some.inj hobjects)
          have hconclusionView := constantHeadedFormula_of_subst_ok
            assertion.formula witness.substitution witness.conclusion
              (by simpa [hwitnessFormula] using witness.formula_subst_ok)
          let result := Classical.choose hconclusionView
          have hconclusion := Classical.choose_spec hconclusionView
          have hstackSize : state.stack.size = formulas.length := by
            have hstateStack := congrArg
              (fun current : RuntimeProofState => current.stack) hstate
            have hsize := congrArg Array.size hstateStack
            simpa using hsize
          have hcount : assertion.frame.hyps.size ≤ formulas.length := by
            rw [← hstackSize]
            simpa [hwitnessFrame] using witness.stackEnough
          let splitWitness := Classical.choose
            (exists_append_suffix_of_le_length formulas
              assertion.frame.hyps.size hcount)
          let prefixFormulas := splitWitness
          let actuals := Classical.choose
            (Classical.choose_spec
              (exists_append_suffix_of_le_length formulas
                assertion.frame.hyps.size hcount))
          have hsplitProperties := Classical.choose_spec
            (Classical.choose_spec
              (exists_append_suffix_of_le_length formulas
                assertion.frame.hyps.size hcount))
          have hformulaSplit :
              formulas = prefixFormulas ++ actuals := hsplitProperties.1
          have hactualsLength :
              actuals.length = assertion.frame.hyps.size :=
            hsplitProperties.2
          let indexedForest :=
            castGeneratedProvesForestIndex hformulaSplit forest
          let split := indexedForest.splitExact prefixFormulas actuals
          have hsplitReconstruct :
              split.leftForest.append split.rightForest = indexedForest :=
            split.append_eq
          have hsplitLabels :
              split.leftForest.labels ++ split.rightForest.labels =
                forest.labels := by
            calc
              split.leftForest.labels ++ split.rightForest.labels =
                  (split.leftForest.append split.rightForest).labels := by
                    rw [GeneratedProvesForest.labels_append]
              _ = indexedForest.labels := congrArg
                GeneratedProvesForest.labels hsplitReconstruct
              _ = forest.labels := by
                exact labels_castGeneratedProvesForestIndex hformulaSplit forest
          have hstateStack :
              state.stack =
                runtimeFormulaArray prefixFormulas ++
                  runtimeFormulaArray actuals := by
            have hstackImage := congrArg
              (fun current : RuntimeProofState => current.stack) hstate
            calc
              state.stack = runtimeFormulaArray formulas := by
                simpa using hstackImage
              _ = runtimeFormulaArray (prefixFormulas ++ actuals) := by
                exact congrArg runtimeFormulaArray hformulaSplit
              _ = runtimeFormulaArray prefixFormulas ++
                    runtimeFormulaArray actuals :=
                runtimeFormulaArray_append prefixFormulas actuals
          have hoffset :
              state.stack.size - assertion.frame.hyps.size =
                (runtimeFormulaArray prefixFormulas).size := by
            rw [hstateStack, Array.size_append]
            simp [hactualsLength]
          have hwindow :
              state.stack.extract
                  (state.stack.size - assertion.frame.hyps.size)
                  state.stack.size =
                runtimeFormulaArray actuals := by
            calc
              state.stack.extract
                    (state.stack.size - assertion.frame.hyps.size)
                    state.stack.size =
                  (runtimeFormulaArray prefixFormulas ++
                    runtimeFormulaArray actuals).extract
                      (runtimeFormulaArray prefixFormulas).size
                      (runtimeFormulaArray prefixFormulas ++
                        runtimeFormulaArray actuals).size := by
                          rw [hoffset, hstateStack]
              _ = runtimeFormulaArray actuals :=
                extract_append_suffix (runtimeFormulaArray prefixFormulas)
                  (runtimeFormulaArray actuals)
          have hnextCanonical :
              next =
                {state with
                  stack :=
                    (state.stack.shrink
                      (state.stack.size - assertion.frame.hyps.size)).push
                        result.toRuntime} := by
            calc
              next = {state with
                    stack := witness.stackPrefix.push witness.conclusion} :=
                witness.result_eq
              _ = {state with
                    stack :=
                      (state.stack.shrink
                        (state.stack.size - assertion.frame.hyps.size)).push
                          result.toRuntime} := by
                rw [witness.stackPrefix_eq, witness.offset_canonical,
                  hwitnessFrame, hconclusion]
          have hstepCanonical :
              db.stepNormal state assertion.label =
                .ok
                  {state with
                    stack :=
                      (state.stack.shrink
                        (state.stack.size - assertion.frame.hyps.size)).push
                          result.toRuntime} := by
            simpa [hnextCanonical] using hstepAssertion
          have hnodeNonempty :
              Nonempty
                (Σ substitution : FiniteSubstitution,
                  GeneratedAssertionNode projection target assertion actuals
                    result substitution) :=
            (generatedAssertionNode_nonempty_iff_stepNormal
              db projection target hprojection assertion state actuals result
                hproject hmember hwindow hstack).mpr hstepCanonical
          let selected := Classical.choice hnodeNonempty
          let substitution : FiniteSubstitution := selected.1
          let node : GeneratedAssertionNode projection target assertion
              actuals result substitution := selected.2
          let tree : GeneratedProvesTree projection target result :=
            .assertion hmember node split.rightForest
          let singleton : GeneratedProvesForest projection target [result] :=
            .cons tree .nil
          have hshrink :
              state.stack.shrink
                (state.stack.size - assertion.frame.hyps.size) =
                runtimeFormulaArray prefixFormulas := by
            rw [hoffset, hstateStack]
            exact shrink_append_prefix (runtimeFormulaArray prefixFormulas)
              (runtimeFormulaArray actuals)
          refine
            { formulas := prefixFormulas ++ [result]
              forest := split.leftForest.append singleton
              labels_eq := ?_
              state_eq := ?_
              stackRespects := ?_ }
          · simp [singleton, tree, GeneratedProvesForest.labels,
              GeneratedProvesTree.labels, ← List.append_assoc,
              hsplitLabels, hlabels, hassertionLabel]
          · calc
              next =
                  {state with
                    stack :=
                      (state.stack.shrink
                        (state.stack.size - assertion.frame.hyps.size)).push
                          result.toRuntime} := hnextCanonical
              _ = {state with
                    stack :=
                      (runtimeFormulaArray prefixFormulas).push
                        result.toRuntime} := by
                  rw [hshrink]
              _ = {base with
                    stack :=
                      (runtimeFormulaArray prefixFormulas).push
                        result.toRuntime} := by
                  rw [hstate]
              _ = {base with
                    stack := runtimeFormulaArray
                      (prefixFormulas ++ [result])} := by
                  rw [runtimeFormulaArray_append_singleton]
          · rw [hnextCanonical]
            exact generatedAssertionNode_stackResult_respects_callerFrame
              db projection target hprojection assertion state.stack actuals
                result hproject hmember hnodeNonempty hwindow hstack

end

/-! ## Positive and negative boundaries -/

/-- Positive boundary: the empty prefix certificate fixes every non-stack
field of the supplied base state and carries the unique empty forest. -/
example (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation) (base : RuntimeProofState) :
    NativeStackCertificate db projection target base []
      {base with stack := #[]} :=
  NativeStackCertificate.empty db projection target base

/-- The exact label index cannot be empty while the retained dependent forest
has a nonempty formula index. -/
theorem NativeStackCertificate.processedLabels_ne_nil_of_formulas_ne_nil
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {base state : RuntimeProofState}
    {processedLabels : List String}
    (certificate : NativeStackCertificate db projection target base
      processedLabels state)
    (hformulas : certificate.formulas ≠ []) :
    processedLabels ≠ [] := by
  intro hlabels
  apply hformulas
  apply certificate.forest.labels_eq_nil_iff.mp
  rw [certificate.labels_eq, hlabels]

/-- Negative boundary: a certificate excludes every unequal complete runtime
state, not only states with a different stack. -/
theorem NativeStackCertificate.state_ne
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {base state : RuntimeProofState}
    {processedLabels : List String}
    (certificate : NativeStackCertificate db projection target base
      processedLabels state)
    (wrong : RuntimeProofState)
    (hne : wrong ≠
      {base with stack := runtimeFormulaArray certificate.formulas}) :
    state ≠ wrong := by
  intro heq
  exact hne (heq ▸ certificate.state_eq)

end Mettapedia.Languages.Metamath.InferenceNormalStepReflection
