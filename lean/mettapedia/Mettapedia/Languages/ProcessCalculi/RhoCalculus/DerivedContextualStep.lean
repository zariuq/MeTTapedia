import Mettapedia.OSLF.MeTTaIL.DerivedContexts
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution

/-!
# Rho contextual reduction derived from the authored rules

The canonical rho `LanguageDef` already authors `Comm` and `ParCong`.
This module instantiates the generic least contextual relation and records its
paper boundary: parallel-bag closure is admitted, while free Drop, quotation
descent, and finite-set descent are not.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.MatchWithSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalSpec
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution

/-- Non-contextual premise behavior for canonical rho. -/
def rhoBasePremises : BasePremiseEvaluator :=
  engineBasePremises RelationEnv.empty

/-- Bounded authored-rule reduction for canonical rho. -/
abbrev RhoStepAt := StepAt rhoBasePremises rhoCalc

/-- The least finite authored-rule reduction for canonical rho. -/
abbrev RhoStep := Step rhoBasePremises rhoCalc

/-! ## The sole authored parallel frame -/

/-- The frame compiled from `ParCong`.  Its `rest` metavariable lets the
matcher select a component modulo rho's canonical parallel representation. -/
def rhoParallelContext : OneHoleContext :=
  .collection .hashBag [] .hole [] (some "rest")

/-- `ParCong` compiles to exactly the expected parallel frame. -/
theorem compile_rhoParCongRewrite :
    compileRuleContexts rhoParCongRewrite = [rhoParallelContext] := by
  decide +kernel

/-- Primitive COMM is not itself a contextual rule. -/
theorem compile_rhoCommRewrite_nil :
    compileRuleContexts rhoCommRewrite = [] := by
  decide +kernel

/-- The parallel frame is derived from the declared `PPar` constructor slot. -/
theorem rhoParallelContext_signature :
    SignatureContext rhoCalc "Proc" "Proc" rhoParallelContext := by
  refine SignatureContext.collectionElement
    (rule := rhoCalc.terms[3]) (parameterName := "ps")
    (elementSort := "Proc") ?_ ?_ (.hole "Proc")
  · decide +kernel
  · rfl

/-- The parallel frame has both signature provenance and explicit `ParCong`
authority. -/
theorem rhoParallelContext_authored :
    AuthoredContextFrame rhoCalc "Proc" "Proc" rhoParallelContext := by
  refine ⟨rhoParallelContext_signature, rhoParCongRewrite, ?_, ?_⟩
  · simp [rhoCalc]
  · rw [← mem_compileRuleContexts_iff_authorized]
    simp [compile_rhoParCongRewrite]

/-! ## Agreement of the derived context with paper PAR -/

/-- A concrete one-hole instance of the authored `ParCong` schema.  The
schema's `rest` metavariable is instantiated by the components before and
after the selected process; it does not make hash-bag representation itself
reduction-active. -/
def rhoParallelInstance (before after : List Pattern) : OneHoleContext :=
  .collection .hashBag before .hole after none

@[simp] theorem rhoParallelInstance_fill
    (before after : List Pattern) (process : Pattern) :
    (rhoParallelInstance before after).fill process =
      .collection .hashBag (before ++ process :: after) none := by
  rfl

/-- Every concrete instance of the context compiled from `ParCong` is exactly
the paper's `PAR_ANY` closure operation. -/
theorem rhoParallelInstance_sound
    {source target : Pattern} (before after : List Pattern)
    (step : Nonempty (Reduces source target)) :
    Nonempty
      (Reduces
        ((rhoParallelInstance before after).fill source)
        ((rhoParallelInstance before after).fill target)) := by
  obtain ⟨step⟩ := step
  refine ⟨?_⟩
  simpa [rhoParallelInstance, OneHoleContext.fill] using
    (Reduces.par_any (before := before) (after := after) step)

/-- The same agreement specialized to the front-position frame represented
directly by the authored `ParCong` left- and right-hand sides. -/
theorem rhoParallelFront_sound
    {source target : Pattern} (rest : List Pattern)
    (step : Nonempty (Reduces source target)) :
    Nonempty
      (Reduces
        (.collection .hashBag (source :: rest) none)
        (.collection .hashBag (target :: rest) none)) := by
  simpa using rhoParallelInstance_sound [] rest step

/-! ## Shape of a compiled COMM match -/

/-- Inverting the relational matcher exposes the two selected communication
partners and the unmatched parallel residue.  This lemma is deliberately
about matcher evidence; it does not assume that successful execution is its
own semantic justification. -/
private theorem rhoComm_match_shape
    {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPatternForRule rhoCalc rhoCommRewrite source) :
    ∃ (elements : List Pattern) (termRest : Option String)
      (inputIndex : Nat) (inputBound : inputIndex < elements.length)
      (outputIndex : Nat)
      (outputBound : outputIndex < (elements.eraseIdx inputIndex).length)
      (inputChannel body : Pattern) (inputBinder : Option String)
      (outputChannel payload : Pattern),
      source = .collection .hashBag elements termRest ∧
      elements[inputIndex] =
        .apply "PInput" [inputChannel, .lambda inputBinder body] ∧
      (elements.eraseIdx inputIndex)[outputIndex] =
        .apply "POutput" [outputChannel, payload] ∧
      rhoCanonicalEquivalent inputChannel outputChannel = true ∧
      bindings =
        [("q", payload),
         ("rest", .collection .hashBag
           ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
         ("p", body), ("n", inputChannel)] := by
  rw [LanguageDefAdequacy.matchPatternForRule_rhoComm_iff] at matched
  cases matched
  rename_i elements termRest bagMatch
  cases bagMatch
  rename_i inputBindings tailBindings inputIndex inputBound inputMatch tailMatch mergeAll
  generalize inputTermEq : elements[inputIndex] = inputTerm at inputMatch
  cases inputMatch
  rename_i inputTermArguments inputLength inputArgsMatch
  obtain ⟨inputChannel, inputLambda, inputArgumentsEq⟩ :=
    List.length_eq_two.mp inputLength.symm
  subst inputTermArguments
  cases inputArgsMatch
  rename_i headBindings tailInputBindings channelMatch inputTailMatch mergeInput
  cases channelMatch
  cases inputTailMatch
  rename_i lambdaBindings noInputBindings lambdaMatch inputArgsRest mergeLambda
  generalize inputLambdaEq : inputLambda = inputLambdaTerm at lambdaMatch
  cases lambdaMatch
  rename_i inputBinder bodyMatch
  cases bodyMatch
  rename_i bodyTerm
  cases inputArgsRest
  cases tailMatch
  rename_i outputBindings restBindings outputIndex outputBound outputMatch restMatch mergeTail
  generalize outputTermEq : (elements.eraseIdx inputIndex)[outputIndex] = outputTerm at outputMatch
  cases outputMatch
  rename_i outputTermArguments outputLength outputArgsMatch
  obtain ⟨outputChannel, payloadTerm, outputArgumentsEq⟩ :=
    List.length_eq_two.mp outputLength.symm
  subst outputTermArguments
  cases outputArgsMatch
  rename_i outputHeadBindings outputTailBindings outputChannelMatch outputTailMatch mergeOutput
  cases outputChannelMatch
  cases outputTailMatch
  rename_i payloadBindings noOutputBindings payloadMatch outputArgsRest mergePayload
  cases payloadMatch
  cases outputArgsRest
  cases restMatch
  rw [inputLambdaEq] at inputTermEq
  simp [mergeBindingsWith] at mergeLambda mergePayload
  subst tailInputBindings
  subst outputTailBindings
  simp [mergeBindingsWith] at mergeInput mergeOutput
  subst inputBindings
  subst outputBindings
  simp [mergeBindingsWith] at mergeTail
  subst tailBindings
  refine ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannel, bodyTerm, inputBinder, outputChannel, payloadTerm, rfl,
    inputTermEq, outputTermEq, ?_⟩
  simp [mergeBindingsWith] at mergeAll
  exact ⟨mergeAll.1, mergeAll.2.symm⟩

/-- The binding order produced by the relational matcher on a direct COMM
redex. Lookup is order-insensitive, but recording the actual order lets the
introduction theorem consume matcher evidence directly. -/
private def rhoCommMatchedBindings
    (channel body payload : Pattern) (rest : List Pattern) : Bindings :=
  [("q", payload),
   ("rest", .collection .hashBag rest none),
   ("p", body),
   ("n", channel)]

/-- A direct COMM redex is accepted by the matcher compiled from the authored
rule. -/
private theorem rhoComm_match_exact
    (channel body payload : Pattern) (rest : List Pattern) :
    rhoCommMatchedBindings channel body payload rest ∈
      matchPatternForRule rhoCalc rhoCommRewrite
        (.collection .hashBag
          ([.apply "PInput" [channel, .lambda none body],
            .apply "POutput" [channel, payload]] ++ rest) none) := by
  rw [LanguageDefAdequacy.matchPatternForRule_rhoComm_iff]
  apply MatchRelWith.collection
  apply MatchBagRelWith.cons 0 (by simp)
  · apply MatchRelWith.apply
    · apply MatchArgsRelWith.cons MatchRelWith.fvar
      · apply MatchArgsRelWith.cons
        · exact MatchRelWith.lambda MatchRelWith.fvar
        · exact MatchArgsRelWith.nil
        · rfl
      · rfl
    · rfl
  · apply MatchBagRelWith.cons 0 (by simp)
    · apply MatchRelWith.apply
      · apply MatchArgsRelWith.cons MatchRelWith.fvar
        · apply MatchArgsRelWith.cons MatchRelWith.fvar MatchArgsRelWith.nil
          rfl
        · rfl
      · rfl
    · exact MatchBagRelWith.nilRest
    · rfl
  · simp [rhoCommMatchedBindings, mergeBindingsWith,
      rhoCanonicalEquivalent, canonicalEquivalent]

/-- The matcher's concrete binding order has the same compiled contractum as
the presentation-facing binding package. -/
private theorem rhoComm_apply_exact
    (channel body payload : Pattern) (rest : List Pattern) :
    applyBindingsForRule rhoCalc rhoCommRewrite
        (rhoCommMatchedBindings channel body payload rest) =
      applyBindingsForRule rhoCalc rhoCommRewrite
        (LanguageDefAdequacy.rhoCommBindings channel body payload rest) := by
  rw [applyBindingsForRule, applyBindingsForRule,
    LanguageDefAdequacy.rhoComm_declaration_selected]
  simp [rhoCommMatchedBindings, LanguageDefAdequacy.rhoCommBindings,
    rhoCommRewrite, applyBindingsReflective, applyBindingsReflectiveList]

/-- Extracting two selected positions from a parallel list leaves exactly the
matcher residue, up to the permutation admitted by paper parallel
congruence. -/
private theorem perm_extract_two (elements : List Pattern)
    (first second : Nat) (firstBound : first < elements.length)
    (secondBound : second < (elements.eraseIdx first).length) :
    elements.Perm
      ([elements[first], (elements.eraseIdx first)[second]] ++
        (elements.eraseIdx first).eraseIdx second) := by
  have firstPermutation := (List.getElem_cons_eraseIdx_perm firstBound).symm
  have secondPermutation := (List.getElem_cons_eraseIdx_perm secondBound).symm
  exact firstPermutation.trans (secondPermutation.cons _)

/-- Structural congruence transports a rho output channel while leaving its
payload unchanged. -/
private theorem output_channel_congr
    {left right payload : Pattern}
    (channelCongruence : StructuralCongruence left right) :
    StructuralCongruence
      (.apply "POutput" [left, payload])
      (.apply "POutput" [right, payload]) := by
  refine StructuralCongruence.apply_cong "POutput"
    [left, payload] [right, payload] rfl ?_
  intro index leftBound rightBound
  cases index with
  | zero => simpa using channelCongruence
  | succ index =>
      simp at leftBound rightBound
      have : index = 0 := by omega
      subst index
      exact StructuralCongruence.refl payload

/-- Inversion of the derived rho process judgment at an input constructor. -/
private theorem rho_input_wellSorted_inv
    {free : FreeSortContext} {bound : List String}
    {channel body : Pattern} {binder : Option String}
    (typed : ProcWellSorted rhoReflectivePresentation free bound
      (.apply "PInput" [channel, .lambda binder body])) :
    binder = none ∧
      NameWellSorted rhoReflectivePresentation free bound channel ∧
      ProcWellSorted rhoReflectivePresentation free
        (rhoReflectivePresentation.nameSort :: bound) body := by
  generalize patternEq :
    (Pattern.apply "PInput" [channel, Pattern.lambda binder body]) = pattern at typed
  cases typed <;> simp [rhoReflectivePresentation] at patternEq
  rename_i channelTyped bodyTyped
  rcases patternEq with ⟨rfl, rfl, rfl⟩
  exact ⟨rfl, channelTyped, bodyTyped⟩

/-- Inversion of the derived rho process judgment at an output constructor. -/
private theorem rho_output_wellSorted_inv
    {free : FreeSortContext} {bound : List String}
    {channel payload : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free bound
      (.apply "POutput" [channel, payload])) :
    NameWellSorted rhoReflectivePresentation free bound channel ∧
      ProcWellSorted rhoReflectivePresentation free bound payload := by
  generalize patternEq :
    (Pattern.apply "POutput" [channel, payload]) = pattern at typed
  cases typed <;> simp [rhoReflectivePresentation] at patternEq
  rename_i channelTyped payloadTyped
  rcases patternEq with ⟨rfl, rfl⟩
  exact ⟨channelTyped, payloadTyped⟩

/-- A successful compiled COMM application on an authored, well-sorted rho
process is a step of the established `COMM`/`PAR`/`EQUIV` relation.  This is the
non-contextual adequacy fact needed by the derived `ParCong` interpreter. -/
theorem rhoComm_application_sound
    {free : FreeSortContext} {bound : List String}
    {source target : Pattern} {bindings : Bindings}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (matched : bindings ∈ matchPatternForRule rhoCalc rhoCommRewrite source)
    (targetEq : applyBindingsForRule rhoCalc rhoCommRewrite bindings = target) :
    Nonempty (Reduces source target) := by
  obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannel, body, inputBinder, outputChannel, payload, sourceEq,
    inputEq, outputEq, channelsEquivalent, bindingsEq⟩ :=
      rhoComm_match_shape matched
  subst source
  subst bindings
  cases sourceTyped
  rename_i elementsTyped
  have inputTyped := elementsTyped.getElem inputIndex inputBound
  rw [inputEq] at inputTyped
  obtain ⟨rfl, inputChannelTyped, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
  have outputTyped :=
    (elementsTyped.eraseIdx inputIndex).getElem outputIndex outputBound
  rw [outputEq] at outputTyped
  obtain ⟨outputChannelTyped, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
  have inputChannelFree := rhoNameWellSorted_hashSetFree inputChannelTyped
  have outputChannelFree := rhoNameWellSorted_hashSetFree outputChannelTyped
  have channelCongruence : StructuralCongruence inputChannel outputChannel :=
    (rhoCanonicalEquivalent_eq_true_iff
      inputChannelFree outputChannelFree).mp channelsEquivalent
  let residue := (elements.eraseIdx inputIndex).eraseIdx outputIndex
  have compiledAgreement :=
    LanguageDefAdequacy.applyBindingsForRule_rhoComm_agrees_derived
      bodyTyped payloadTyped inputChannel residue
  have targetShape :
      target = .collection .hashBag (semanticCommSubst body payload :: residue) none := by
    rw [← targetEq]
    have reordered :
        applyBindingsForRule rhoCalc rhoCommRewrite
            [("q", payload),
             ("rest", .collection .hashBag
               ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
             ("p", body), ("n", inputChannel)] =
          applyBindingsForRule rhoCalc rhoCommRewrite
            (LanguageDefAdequacy.rhoCommBindings inputChannel body payload residue) := by
      simp only [applyBindingsForRule,
        LanguageDefAdequacy.rhoComm_declaration_selected]
      simp [LanguageDefAdequacy.rhoCommBindings, residue,
        applyBindingsReflective, applyBindingsReflectiveList, rhoCommRewrite]
    rw [reordered]
    exact compiledAgreement
  have extracted := perm_extract_two elements inputIndex outputIndex inputBound outputBound
  rw [inputEq, outputEq] at extracted
  have sourcePermutation : StructuralCongruence
      (.collection .hashBag elements none)
      (.collection .hashBag
        ([.apply "PInput" [inputChannel, .lambda none body],
          .apply "POutput" [outputChannel, payload]] ++ residue) none) :=
    StructuralCongruence.par_perm _ _ extracted
  have outputAgreement : StructuralCongruence
      (.apply "POutput" [outputChannel, payload])
      (.apply "POutput" [inputChannel, payload]) :=
    output_channel_congr (StructuralCongruence.symm _ _ channelCongruence)
  have partnerAgreement : StructuralCongruence
      (.collection .hashBag
        ([.apply "PInput" [inputChannel, .lambda none body],
          .apply "POutput" [outputChannel, payload]] ++ residue) none)
      (.collection .hashBag
        ([.apply "PInput" [inputChannel, .lambda none body],
          .apply "POutput" [inputChannel, payload]] ++ residue) none) := by
    refine StructuralCongruence.par_cong _ _ rfl ?_
    intro index leftBound rightBound
    cases index with
    | zero => exact StructuralCongruence.refl _
    | succ index =>
        cases index with
        | zero => simpa using outputAgreement
        | succ index =>
            have residueBound : index < residue.length := by simpa using leftBound
            exact StructuralCongruence.refl (residue.get ⟨index, residueBound⟩)
  have orderAgreement : StructuralCongruence
      (.collection .hashBag
        ([.apply "PInput" [inputChannel, .lambda none body],
          .apply "POutput" [inputChannel, payload]] ++ residue) none)
      (.collection .hashBag
        ([.apply "POutput" [inputChannel, payload],
          .apply "PInput" [inputChannel, .lambda none body]] ++ residue) none) := by
    apply StructuralCongruence.par_perm
    exact List.Perm.swap _ _ _
  rw [targetShape]
  exact ⟨Reduces.equiv
    (StructuralCongruence.trans _ _ _ sourcePermutation
      (StructuralCongruence.trans _ _ _ partnerAgreement orderAgreement))
    (Reduces.comm (n := inputChannel) (q := payload) (p := body)
      (rest := residue))
    (StructuralCongruence.refl _)⟩

/-- The primitive COMM constructor of the least relation compiled from
`rhoCalc`. The well-sorted hypotheses are exactly those needed to identify the
compiled reflective substitution with semantic COMM substitution. -/
theorem RhoStep.comm
    {free : FreeSortContext} {bound : List String}
    (channel body payload : Pattern) (rest : List Pattern)
    (bodyTyped : ProcWellSorted rhoReflectivePresentation free
      (rhoReflectivePresentation.nameSort :: bound) body)
    (payloadTyped : ProcWellSorted rhoReflectivePresentation free bound payload) :
    RhoStep
      (.collection .hashBag
        ([.apply "PInput" [channel, .lambda none body],
          .apply "POutput" [channel, payload]] ++ rest) none)
      (.collection .hashBag (semanticCommSubst body payload :: rest) none) := by
  refine step_of_rule
    (relEnv := RelationEnv.empty)
    (rule := rhoCommRewrite)
    (initialBindings := rhoCommMatchedBindings channel body payload rest)
    (finalBindings := rhoCommMatchedBindings channel body payload rest)
    LanguageDefAdequacy.rhoCommRewrite_mem
    (rhoComm_match_exact channel body payload rest) ?_ ?_ ?_
  · exact .nil
  · simp [rhoCommRewrite, applyPremisesWithEnv]
  · rw [rhoComm_apply_exact,
      LanguageDefAdequacy.applyBindingsForRule_rhoComm_agrees_derived
        bodyTyped payloadTyped]

/-! ## Shape and meaning of an authored `ParCong` application -/

private theorem rhoParCong_no_declaration :
    declarationForRule? rhoCalc rhoParCongRewrite = none := by
  decide +kernel

/-- The structural matcher for `ParCong` selects one parallel component and
binds the remainder; no collection-wide semantic switch participates. -/
private theorem rhoParCong_match_shape
    {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPatternForRule rhoCalc rhoParCongRewrite source) :
    ∃ (elements : List Pattern) (termRest : Option String)
      (index : Nat) (indexBound : index < elements.length)
      (selected : Pattern),
      source = .collection .hashBag elements termRest ∧
      elements[index] = selected ∧
      bindings =
        [("rest", .collection .hashBag (elements.eraseIdx index) none),
         ("S", selected)] := by
  rw [matchPatternForRule_iff_matchRel_of_no_declaration
    rhoParCong_no_declaration] at matched
  cases matched
  rename_i elements termRest bagMatch
  cases bagMatch
  rename_i headBindings tailBindings index indexBound headMatch tailMatch mergeAll
  generalize selectedEq : elements[index] = selected at headMatch
  cases headMatch
  cases tailMatch
  simp [mergeBindings] at mergeAll
  refine ⟨elements, termRest, index, indexBound, selected, rfl, selectedEq, ?_⟩
  exact mergeAll.symm

/-- The front-position instance of `ParCong` is accepted by its ordinary
structural matcher. -/
private theorem rhoParCong_match_exact (process : Pattern) (rest : List Pattern) :
    [("rest", .collection .hashBag rest none), ("S", process)] ∈
      matchPatternForRule rhoCalc rhoParCongRewrite
        (.collection .hashBag (process :: rest) none) := by
  rw [matchPatternForRule_iff_matchRel_of_no_declaration
    rhoParCong_no_declaration]
  apply MatchRel.collection
  apply MatchBagRel.cons 0 (by simp) MatchRel.fvar MatchBagRel.nilRest
  rfl

/-- The authored parallel context transports every derived rho step. -/
theorem RhoStep.par {source target : Pattern} (rest : List Pattern)
    (step : RhoStep source target) :
    RhoStep
      (.collection .hashBag (source :: rest) none)
      (.collection .hashBag (target :: rest) none) := by
  refine step_of_single_congruence_rule
    (base := rhoBasePremises)
    (rule := rhoParCongRewrite)
    (initialBindings :=
      [("rest", .collection .hashBag rest none), ("S", source)])
    (finalBindings :=
      [("T", target),
       ("rest", .collection .hashBag rest none),
       ("S", source)])
    (premiseBindings := [("T", target)])
    (premiseSource := .fvar "S")
    (premiseTarget := .fvar "T")
    (candidate := target)
    (by simp [rhoCalc])
    (rhoParCong_match_exact source rest)
    rfl ?_ ?_ rfl ?_
  · simpa [applyBindings, Bindings.lookup] using step
  · simp [matchPattern]
  · rw [applyBindingsForRule, rhoParCong_no_declaration]
    simp [rhoParCongRewrite, applyBindings]

/-- Interpreting the single congruence premise of `ParCong` with a sound
recursive step yields an established rho reduction. -/
private theorem rhoParCong_application_sound
    {free : FreeSortContext} {bound : List String} {fuel : Nat}
    {source target : Pattern} {initial final : Bindings}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (matched : initial ∈ matchPatternForRule rhoCalc rhoParCongRewrite source)
    (premises : PremisesAt rhoBasePremises rhoCalc fuel initial
      rhoParCongRewrite.premises final)
    (targetEq : applyBindingsForRule rhoCalc rhoParCongRewrite final = target)
    (recursiveSound : ∀ {innerSource innerTarget : Pattern},
      ProcWellSorted rhoReflectivePresentation free bound innerSource →
      StepAt rhoBasePremises rhoCalc fuel innerSource innerTarget →
      Nonempty (Reduces innerSource innerTarget)) :
    Nonempty (Reduces source target) := by
  obtain ⟨elements, termRest, index, indexBound, selected, sourceEq,
    selectedEq, initialEq⟩ := rhoParCong_match_shape matched
  subst source
  subst initial
  cases sourceTyped
  rename_i elementsTyped
  have selectedTyped := elementsTyped.getElem index indexBound
  rw [selectedEq] at selectedTyped
  change PremisesAt rhoBasePremises rhoCalc fuel
    [("rest", .collection .hashBag (elements.eraseIdx index) none),
     ("S", selected)]
    [.congruence (.fvar "S") (.fvar "T")] final at premises
  cases premises
  rename_i middle firstPremise remainingPremises
  cases remainingPremises
  cases firstPremise
  rename_i premiseBindings candidate recursiveStep targetMatch merged
  simp [matchPattern] at targetMatch
  subst premiseBindings
  simp [mergeBindings] at merged
  subst final
  have innerStep : StepAt rhoBasePremises rhoCalc fuel selected candidate := by
    simpa [applyBindings, Bindings.lookup] using recursiveStep
  have innerPaper := recursiveSound selectedTyped innerStep
  have sourcePermutation : StructuralCongruence
      (.collection .hashBag elements none)
      (.collection .hashBag (selected :: elements.eraseIdx index) none) :=
    by
      have permutation := (List.getElem_cons_eraseIdx_perm indexBound).symm
      rw [selectedEq] at permutation
      exact StructuralCongruence.par_perm _ _ permutation
  have targetShape :
      target = .collection .hashBag (candidate :: elements.eraseIdx index) none := by
    rw [← targetEq]
    simp only [applyBindingsForRule, rhoParCong_no_declaration]
    simp [rhoParCongRewrite, applyBindings]
  rw [targetShape]
  obtain ⟨innerPaper⟩ := innerPaper
  exact ⟨Reduces.equiv sourcePermutation
    (Reduces.par (rest := elements.eraseIdx index) innerPaper)
    (StructuralCongruence.refl _)⟩

/-! ## Full derived-step soundness -/

/-- Every bounded step compiled from the authored pure-rho rules is a step of
the established COMM/PAR/EQUIV relation, provided its source inhabits the
derived rho syntax. -/
theorem rhoStepAt_sound
    {free : FreeSortContext} {bound : List String} :
    ∀ {fuel source target},
      ProcWellSorted rhoReflectivePresentation free bound source →
      RhoStepAt fuel source target →
      Nonempty (Reduces source target) := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target sourceTyped step
      cases step
  | succ fuel inductionHypothesis =>
      intro source target sourceTyped step
      cases step
      rename_i rule initial final ruleMember premises matched targetEq
      change rule ∈ [rhoCommRewrite, rhoParCongRewrite] at ruleMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ruleMember
      rcases ruleMember with ruleEq | ruleEq
      · subst rule
        cases premises
        exact rhoComm_application_sound sourceTyped matched targetEq
      · subst rule
        exact rhoParCong_application_sound
          sourceTyped matched premises targetEq
          (fun innerTyped innerStep =>
            inductionHypothesis innerTyped innerStep)

/-- Unbounded form: the least finite contextual relation compiled from the
authored rho `LanguageDef` is sound for the established `COMM`/`PAR`/`EQUIV` relation on the
derived well-sorted carrier. -/
theorem rhoStep_sound
    {free : FreeSortContext} {bound : List String}
    {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free bound source)
    (step : RhoStep source target) :
    Nonempty (Reduces source target) := by
  obtain ⟨fuel, bounded⟩ := step
  exact rhoStepAt_sound sourceTyped bounded

/-! ## Closed-syntax preservation -/

/-- A compiled COMM application preserves the closed, quote-aware process
fragment. -/
private theorem rhoComm_application_preserves_closed
    {free : FreeSortContext} {source target : Pattern} {bindings : Bindings}
    (sourceTyped :
      ProcWellSorted rhoReflectivePresentation free [] source)
    (sourceSafe : binderSafeAt "NQuote" 0 source = true)
    (matched : bindings ∈ matchPatternForRule rhoCalc rhoCommRewrite source)
    (targetEq : applyBindingsForRule rhoCalc rhoCommRewrite bindings = target) :
    ProcWellSorted rhoReflectivePresentation free [] target ∧
      binderSafeAt "NQuote" 0 target = true := by
  obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannel, body, inputBinder, outputChannel, payload, sourceEq,
    inputEq, outputEq, channelsEquivalent, bindingsEq⟩ :=
      rhoComm_match_shape matched
  subst source
  subst bindings
  cases sourceTyped
  rename_i elementsTyped
  have elementsSafe : binderSafeListAt "NQuote" 0 elements = true := by
    simpa [binderSafeAt, rhoReflectivePresentation] using sourceSafe
  have inputTyped := elementsTyped.getElem inputIndex inputBound
  rw [inputEq] at inputTyped
  obtain ⟨rfl, inputChannelTyped, bodyTyped⟩ :=
    rho_input_wellSorted_inv inputTyped
  have inputSafe :
      binderSafeAt "NQuote" 0
        (.apply "PInput" [inputChannel, .lambda none body]) = true := by
    have elementSafe := (binderSafeListAt_eq_true_iff _ _ _).mp elementsSafe
      elements[inputIndex] (List.getElem_mem inputBound)
    rw [inputEq] at elementSafe
    exact elementSafe
  have bodySafe : binderSafeAt "NQuote" 1 body = true := by
    have components :
        binderSafeAt "NQuote" 0 inputChannel = true ∧
          binderSafeAt "NQuote" 1 body = true := by
      simpa [binderSafeAt, binderSafeListAt] using inputSafe
    exact components.2
  have afterInputTyped := elementsTyped.eraseIdx inputIndex
  have afterInputSafe :=
    binderSafeListAt_eraseIdx "NQuote" 0 inputIndex elementsSafe
  have outputTyped := afterInputTyped.getElem outputIndex outputBound
  rw [outputEq] at outputTyped
  obtain ⟨outputChannelTyped, payloadTyped⟩ :=
    rho_output_wellSorted_inv outputTyped
  have outputSafe :
      binderSafeAt "NQuote" 0
        (.apply "POutput" [outputChannel, payload]) = true := by
    have elementSafe := (binderSafeListAt_eq_true_iff _ _ _).mp afterInputSafe
      (elements.eraseIdx inputIndex)[outputIndex]
        (List.getElem_mem outputBound)
    rw [outputEq] at elementSafe
    exact elementSafe
  have payloadSafe : binderSafeAt "NQuote" 0 payload = true := by
    have components :
        binderSafeAt "NQuote" 0 outputChannel = true ∧
          binderSafeAt "NQuote" 0 payload = true := by
      simpa [binderSafeAt, binderSafeListAt] using outputSafe
    exact components.2
  let residue := (elements.eraseIdx inputIndex).eraseIdx outputIndex
  have residueTyped :
      ProcListWellSorted rhoReflectivePresentation free [] residue := by
    exact afterInputTyped.eraseIdx outputIndex
  have residueSafe : binderSafeListAt "NQuote" 0 residue = true := by
    exact binderSafeListAt_eraseIdx "NQuote" 0 outputIndex afterInputSafe
  have contractumPreserved :=
    semanticCommSubst_preserves bodyTyped bodySafe payloadTyped payloadSafe
  have compiledAgreement :=
    LanguageDefAdequacy.applyBindingsForRule_rhoComm_agrees_derived
      bodyTyped payloadTyped inputChannel residue
  have targetShape :
      target =
        .collection .hashBag (semanticCommSubst body payload :: residue) none := by
    rw [← targetEq]
    have reordered :
        applyBindingsForRule rhoCalc rhoCommRewrite
            [("q", payload),
             ("rest", .collection .hashBag
               ((elements.eraseIdx inputIndex).eraseIdx outputIndex) none),
             ("p", body), ("n", inputChannel)] =
          applyBindingsForRule rhoCalc rhoCommRewrite
            (LanguageDefAdequacy.rhoCommBindings
              inputChannel body payload residue) := by
      simp only [applyBindingsForRule,
        LanguageDefAdequacy.rhoComm_declaration_selected]
      simp [LanguageDefAdequacy.rhoCommBindings, residue,
        applyBindingsReflective, applyBindingsReflectiveList, rhoCommRewrite]
    rw [reordered]
    exact compiledAgreement
  rw [targetShape]
  exact ⟨ProcWellSorted.parallel
      (.cons contractumPreserved.1 residueTyped),
    by
      simpa [binderSafeAt, binderSafeListAt] using
        And.intro contractumPreserved.2 residueSafe⟩

/-- A compiled `ParCong` application preserves the same closed fragment when
its recursive premise does. -/
private theorem rhoParCong_application_preserves_closed
    {free : FreeSortContext} {fuel : Nat}
    {source target : Pattern} {initial final : Bindings}
    (sourceTyped :
      ProcWellSorted rhoReflectivePresentation free [] source)
    (sourceSafe : binderSafeAt "NQuote" 0 source = true)
    (matched : initial ∈ matchPatternForRule rhoCalc rhoParCongRewrite source)
    (premises : PremisesAt rhoBasePremises rhoCalc fuel initial
      rhoParCongRewrite.premises final)
    (targetEq : applyBindingsForRule rhoCalc rhoParCongRewrite final = target)
    (recursivePreserves : ∀ {innerSource innerTarget : Pattern},
      ProcWellSorted rhoReflectivePresentation free [] innerSource →
      binderSafeAt "NQuote" 0 innerSource = true →
      StepAt rhoBasePremises rhoCalc fuel innerSource innerTarget →
      ProcWellSorted rhoReflectivePresentation free [] innerTarget ∧
        binderSafeAt "NQuote" 0 innerTarget = true) :
    ProcWellSorted rhoReflectivePresentation free [] target ∧
      binderSafeAt "NQuote" 0 target = true := by
  obtain ⟨elements, termRest, selectedIndex, selectedBound, selected, sourceEq,
    selectedEq, initialEq⟩ := rhoParCong_match_shape matched
  subst source
  subst initial
  cases sourceTyped
  rename_i elementsTyped
  have elementsSafe : binderSafeListAt "NQuote" 0 elements = true := by
    simpa [binderSafeAt, rhoReflectivePresentation] using sourceSafe
  have selectedTyped := elementsTyped.getElem selectedIndex selectedBound
  rw [selectedEq] at selectedTyped
  have selectedSafe : binderSafeAt "NQuote" 0 selected = true := by
    have elementSafe := (binderSafeListAt_eq_true_iff _ _ _).mp elementsSafe
      elements[selectedIndex] (List.getElem_mem selectedBound)
    rw [selectedEq] at elementSafe
    exact elementSafe
  change PremisesAt rhoBasePremises rhoCalc fuel
    [("rest", .collection .hashBag (elements.eraseIdx selectedIndex) none),
     ("S", selected)]
    [.congruence (.fvar "S") (.fvar "T")] final at premises
  cases premises
  rename_i middle firstPremise remainingPremises
  cases remainingPremises
  cases firstPremise
  rename_i premiseBindings candidate recursiveStep targetMatch merged
  simp [matchPattern] at targetMatch
  subst premiseBindings
  simp [mergeBindings] at merged
  subst final
  have innerStep : StepAt rhoBasePremises rhoCalc fuel selected candidate := by
    simpa [applyBindings, Bindings.lookup] using recursiveStep
  have candidatePreserved :=
    recursivePreserves selectedTyped selectedSafe innerStep
  have residueTyped := elementsTyped.eraseIdx selectedIndex
  have residueSafe :=
    binderSafeListAt_eraseIdx "NQuote" 0 selectedIndex elementsSafe
  have targetShape :
      target = .collection .hashBag
        (candidate :: elements.eraseIdx selectedIndex) none := by
    rw [← targetEq]
    simp only [applyBindingsForRule, rhoParCong_no_declaration]
    simp [rhoParCongRewrite, applyBindings]
  rw [targetShape]
  exact ⟨ProcWellSorted.parallel
      (.cons candidatePreserved.1 residueTyped),
    by
      simpa [binderSafeAt, binderSafeListAt] using
        And.intro candidatePreserved.2 residueSafe⟩

/-- Every bounded step compiled from the authored rho rules preserves the
closed, quote-aware process fragment. -/
theorem rhoStepAt_preserves_closed
    {free : FreeSortContext} :
    ∀ {fuel source target},
      ProcWellSorted rhoReflectivePresentation free [] source →
      binderSafeAt "NQuote" 0 source = true →
      RhoStepAt fuel source target →
      ProcWellSorted rhoReflectivePresentation free [] target ∧
        binderSafeAt "NQuote" 0 target = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target sourceTyped sourceSafe step
      cases step
  | succ fuel inductionHypothesis =>
      intro source target sourceTyped sourceSafe step
      cases step
      rename_i rule initial final ruleMember premises matched targetEq
      change rule ∈ [rhoCommRewrite, rhoParCongRewrite] at ruleMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ruleMember
      rcases ruleMember with ruleEq | ruleEq
      · subst rule
        cases premises
        exact rhoComm_application_preserves_closed
          sourceTyped sourceSafe matched targetEq
      · subst rule
        exact rhoParCong_application_preserves_closed
          sourceTyped sourceSafe matched premises targetEq
          (fun innerTyped innerSafe innerStep =>
            inductionHypothesis innerTyped innerSafe innerStep)

/-- Unbounded form: every finite authored rho step starting from a genuine
closed process ends at another genuine closed process. -/
theorem rhoStep_preserves_closed
    {free : FreeSortContext} {source target : Pattern}
    (sourceTyped :
      ProcWellSorted rhoReflectivePresentation free [] source)
    (sourceSafe : binderSafeAt "NQuote" 0 source = true)
    (step : RhoStep source target) :
    ProcWellSorted rhoReflectivePresentation free [] target ∧
      binderSafeAt "NQuote" 0 target = true := by
  obtain ⟨fuel, bounded⟩ := step
  exact rhoStepAt_preserves_closed sourceTyped sourceSafe bounded

/-! ## Positive and negative operational controls -/

def commRedex : Pattern :=
  .collection .hashBag
    [.apply "PInput" [.fvar "x", .lambda none (.apply "PZero" [])],
     .apply "POutput" [.fvar "x", .apply "PZero" []]] none

def commReduct : Pattern :=
  .collection .hashBag [.apply "PZero" []] none

def commInParallel : Pattern :=
  .collection .hashBag [commRedex, .apply "PZero" []] none

def commInParallelReduct : Pattern :=
  .collection .hashBag [commReduct, .apply "PZero" []] none

/-- Positive control: an authored `ParCong` layer transports COMM. -/
theorem commInParallel_mem :
    commInParallelReduct ∈
      rewriteAt rhoBasePremises rhoCalc 2 commInParallel := by
  decide +kernel

/-- Relational form of the positive parallel-context control. -/
theorem commInParallel_step : RhoStep commInParallel commInParallelReduct := by
  exact ⟨2, mem_rewriteAt_iff_stepAt.mp commInParallel_mem⟩

/-- Semantic witness for the same positive case.  The inner source is
permuted into the presentation order by EQUIV, COMM fires, and the authored
parallel context is interpreted by PAR. -/
theorem commInParallel_reduces :
    Nonempty (Reduces commInParallel commInParallelReduct) := by
  have inner : Nonempty (Reduces commRedex commReduct) := by
    refine ⟨Reduces.equiv
      (StructuralCongruence.par_comm
        (.apply "PInput" [.fvar "x", .lambda none (.apply "PZero" [])])
        (.apply "POutput" [.fvar "x", .apply "PZero" []]))
      (Reduces.comm (n := .fvar "x")
        (q := .apply "PZero" []) (p := .apply "PZero" []) (rest := []))
      ?_⟩
    exact StructuralCongruence.refl _
  exact rhoParallelFront_sound [.apply "PZero" []] inner

/-! ## Explicit finite contextual depth -/

/-- Nest a process under `depth` explicitly authored parallel frames. -/
def nestParallel : Nat → Pattern → Pattern
  | 0, process => process
  | depth + 1, process =>
      .collection .hashBag
        [nestParallel depth process, .apply "PZero" []] none

/-- Four authored `ParCong` frames followed by COMM form a finite derivation
of depth five.  Contextual depth is explicit evidence rather than a hidden
global cutoff. -/
theorem derived_executor_reaches_four_parallel_frames :
    nestParallel 4 commReduct ∈
      rewriteAt rhoBasePremises rhoCalc 5 (nestParallel 4 commRedex) := by
  decide +kernel

/-- Relational form of the depth-cap counterexample. -/
theorem derived_step_reaches_four_parallel_frames :
    RhoStep (nestParallel 4 commRedex) (nestParallel 4 commReduct) := by
  exact ⟨5, mem_rewriteAt_iff_stepAt.mp
    derived_executor_reaches_four_parallel_frames⟩

def freeDrop : Pattern :=
  .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]

def commUnderQuote : Pattern :=
  .apply "NQuote" [commRedex]

def commUnderSet : Pattern :=
  .collection .hashSet [commRedex] none

private theorem rhoComm_no_match_freeDrop :
    matchPatternForRule rhoCalc rhoCommRewrite freeDrop = [] := by
  decide +kernel

private theorem rhoParCong_no_match_freeDrop :
    matchPatternForRule rhoCalc rhoParCongRewrite freeDrop = [] := by
  decide +kernel

private theorem rhoComm_no_match_underQuote :
    matchPatternForRule rhoCalc rhoCommRewrite commUnderQuote = [] := by
  decide +kernel

private theorem rhoParCong_no_match_underQuote :
    matchPatternForRule rhoCalc rhoParCongRewrite commUnderQuote = [] := by
  decide +kernel

private theorem rhoComm_no_match_underSet :
    matchPatternForRule rhoCalc rhoCommRewrite commUnderSet = [] := by
  decide +kernel

private theorem rhoParCong_no_match_underSet :
    matchPatternForRule rhoCalc rhoParCongRewrite commUnderSet = [] := by
  decide +kernel

private theorem rhoCalc_rewrites :
    rhoCalc.rewrites = [rhoCommRewrite, rhoParCongRewrite] := rfl

/-- Free Drop is inert at every contextual depth. -/
theorem freeDrop_rewriteAt_nil (fuel : Nat) :
    rewriteAt rhoBasePremises rhoCalc fuel freeDrop = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [rewriteAt, rhoCalc_rewrites]
      simp [applyRuleUsing, rhoComm_no_match_freeDrop,
        rhoParCong_no_match_freeDrop]

/-- No authored rho rule descends under quotation. -/
theorem commUnderQuote_rewriteAt_nil (fuel : Nat) :
    rewriteAt rhoBasePremises rhoCalc fuel commUnderQuote = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [rewriteAt, rhoCalc_rewrites]
      simp [applyRuleUsing, rhoComm_no_match_underQuote,
        rhoParCong_no_match_underQuote]

/-- Pure rho has no finite-set context rule. -/
theorem commUnderSet_rewriteAt_nil (fuel : Nat) :
    rewriteAt rhoBasePremises rhoCalc fuel commUnderSet = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [rewriteAt, rhoCalc_rewrites]
      simp [applyRuleUsing, rhoComm_no_match_underSet,
        rhoParCong_no_match_underSet]

/-- Relational free-Drop boundary. -/
theorem no_freeDrop_step (target : Pattern) :
    ¬RhoStep freeDrop target := by
  intro step
  obtain ⟨fuel, bounded⟩ := step
  have member := mem_rewriteAt_iff_stepAt.mpr bounded
  rw [freeDrop_rewriteAt_nil] at member
  exact List.not_mem_nil member

/-- Relational quotation boundary. -/
theorem no_commUnderQuote_step (target : Pattern) :
    ¬RhoStep commUnderQuote target := by
  intro step
  obtain ⟨fuel, bounded⟩ := step
  have member := mem_rewriteAt_iff_stepAt.mpr bounded
  rw [commUnderQuote_rewriteAt_nil] at member
  exact List.not_mem_nil member

/-- Relational finite-set boundary. -/
theorem no_commUnderSet_step (target : Pattern) :
    ¬RhoStep commUnderSet target := by
  intro step
  obtain ⟨fuel, bounded⟩ := step
  have member := mem_rewriteAt_iff_stepAt.mpr bounded
  rw [commUnderSet_rewriteAt_nil] at member
  exact List.not_mem_nil member

/-! ## Sorting obstruction in the legacy raw congruence -/

private def sortingCounterexampleFree : FreeSortContext
  | "x" => some rhoReflectivePresentation.nameSort
  | _ => none

private def sortingCounterexampleSource : Pattern :=
  .apply "POutput" [.fvar "x", .apply "PZero" []]

private def sortingCounterexampleTarget : Pattern :=
  .apply "POutput"
    [.collection .hashBag [.fvar "x"] none, .apply "PZero" []]

private theorem sortingCounterexampleSource_wellSorted :
    ProcWellSorted rhoReflectivePresentation sortingCounterexampleFree []
      sortingCounterexampleSource := by
  exact .output (.fvar rfl) .unit

private theorem sortingCounterexampleTarget_not_wellSorted :
    ¬ProcWellSorted rhoReflectivePresentation sortingCounterexampleFree []
      sortingCounterexampleTarget := by
  intro typed
  generalize targetEq : sortingCounterexampleTarget = target at typed
  cases typed <;>
    simp_all [sortingCounterexampleTarget, rhoReflectivePresentation]
  next channel payload channelTyped payloadTyped =>
    cases channelTyped <;>
      simp_all

private theorem sortingCounterexample_structuralCongruence :
    StructuralCongruence sortingCounterexampleSource
      sortingCounterexampleTarget := by
  apply StructuralCongruence.apply_cong
    "POutput"
    [.fvar "x", .apply "PZero" []]
    [.collection .hashBag [.fvar "x"] none, .apply "PZero" []]
    rfl
  intro index sourceBound targetBound
  simp only [List.length_cons, List.length_nil] at sourceBound targetBound
  have index_cases : index = 0 ∨ index = 1 := by omega
  rcases index_cases with rfl | rfl
  · exact StructuralCongruence.symm _ _
      (StructuralCongruence.par_singleton (.fvar "x"))
  · exact StructuralCongruence.refl _

/-- Raw-pattern structural congruence is not closed on the rho presentation's
derived well-sorted processes: an unrestricted application-congruence step can
apply a parallel law in a name argument.  Consequently, an exact equivalence
theorem on the derived rho carrier must use a sort-respecting equation relation
rather than the unrestricted representation-level relation. -/
theorem structuralCongruence_not_preserving_procWellSorted :
    ∃ free source target,
      ProcWellSorted rhoReflectivePresentation free [] source ∧
      StructuralCongruence source target ∧
      ¬ProcWellSorted rhoReflectivePresentation free [] target := by
  exact ⟨sortingCounterexampleFree, sortingCounterexampleSource,
    sortingCounterexampleTarget, sortingCounterexampleSource_wellSorted,
    sortingCounterexample_structuralCongruence,
    sortingCounterexampleTarget_not_wellSorted⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
