import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

/-!
# Occurrence inversion for guarded core-rho frontiers

An active frontier is a finite list of input and output headers. Their
continuations and payloads are arbitrary well-sorted core processes. The
authored matcher cannot descend through these guards: every firing selects
an input position and an output position in the remaining list.

The inversion retains both selected positions, their actual channel
comparison, and the supplied contractum. Canonical sorting relocates these
positions but preserves the residual multiset, including duplicate headers.
No guest language or compiler simulation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness

/-- Active headers retain their suspended bodies as data. -/
inductive Header where
  | input (channel body : Pattern)
  | output (channel payload : Pattern)
  deriving DecidableEq

def Header.pattern : Header → Pattern
  | .input channel body => .apply "PInput" [channel, .lambda none body]
  | .output channel payload => .apply "POutput" [channel, payload]

def Header.Typed (free : FreeSortContext) : Header → Prop
  | .input channel body =>
      NameWellSorted rhoReflectivePresentation free [] channel ∧
        ProcWellSorted rhoReflectivePresentation free ["Name"] body
  | .output channel payload =>
      NameWellSorted rhoReflectivePresentation free [] channel ∧
        ProcWellSorted rhoReflectivePresentation free [] payload

def Header.Safe : Header → Prop
  | .input channel body =>
      binderSafeAt "NQuote" 0 channel = true ∧ binderSafeAt "NQuote" 1 body = true
  | .output channel payload =>
      binderSafeAt "NQuote" 0 channel = true ∧ binderSafeAt "NQuote" 0 payload = true

theorem Header.pattern_typed {free : FreeSortContext} {header : Header}
    (typed : header.Typed free) :
    ProcWellSorted rhoReflectivePresentation free [] header.pattern := by
  cases header with
  | input channel body => exact .input typed.1 typed.2
  | output channel payload => exact .output typed.1 typed.2

theorem Header.pattern_safe {header : Header} (safe : header.Safe) :
    binderSafeAt "NQuote" 0 header.pattern = true := by
  cases header <;> simpa [Header.Safe, Header.pattern, binderSafeAt,
    binderSafeListAt, Bool.and_eq_true] using safe

theorem Header.nonbag (header : Header) (elements : List Pattern) (rest : Option String) :
    header.pattern ≠ .collection .hashBag elements rest := by
  cases header <;> simp [Header.pattern]

theorem Header.canonical_nonbag (header : Header) (elements : List Pattern)
    (rest : Option String) :
    Canonical.canonicalize header.pattern ≠ .collection .hashBag elements rest := by
  cases header <;> simp [Header.pattern, canonicalize_input, canonicalize_output]

theorem Header.canonical_nonunit (header : Header) :
    Canonical.canonicalize header.pattern ≠ .apply "PZero" [] := by
  cases header <;> simp [Header.pattern, canonicalize_input, canonicalize_output]

private theorem input_shape {header : Header} {channel body : Pattern}
    {metadata : Option String}
    (shape : header.pattern = .apply "PInput" [channel, .lambda metadata body]) :
    header = .input channel body ∧ metadata = none := by
  cases header with
  | input subject handler =>
      simp only [Header.pattern, Pattern.apply.injEq, List.cons.injEq,
        Pattern.lambda.injEq] at shape
      rcases shape with ⟨_, rfl, ⟨⟨rfl, rfl⟩, _⟩⟩
      exact ⟨rfl, rfl⟩
  | output subject payload => simp [Header.pattern] at shape

private theorem output_shape {header : Header} {channel payload : Pattern}
    (shape : header.pattern = .apply "POutput" [channel, payload]) :
    header = .output channel payload := by
  cases header with
  | input subject handler => simp [Header.pattern] at shape
  | output subject value =>
      have equal : subject = channel ∧ value = payload := by
        simpa only [Header.pattern, Pattern.apply.injEq, List.cons.injEq,
          true_and, and_true] using shape
      rcases equal with ⟨rfl, rfl⟩
      rfl

def parallel (headers : List Header) : Pattern :=
  .collection .hashBag (headers.map Header.pattern) none

def canonicalParallel (headers : List Header) : Pattern :=
  Canonical.canonicalize (parallel headers)

theorem parallel_typed {free : FreeSortContext} {headers : List Header}
    (typed : ∀ header ∈ headers, header.Typed free) :
    ProcWellSorted rhoReflectivePresentation free [] (parallel headers) := by
  apply ProcWellSorted.parallel
  apply procListWellSorted_iff_forall_mem.mpr
  intro pattern member
  obtain ⟨header, membership, rfl⟩ := List.mem_map.mp member
  exact Header.pattern_typed (typed header membership)

theorem parallel_safe {headers : List Header} (safe : ∀ header ∈ headers, header.Safe) :
    binderSafeAt "NQuote" 0 (parallel headers) = true := by
  change binderSafeListAt "NQuote" 0 (headers.map Header.pattern) = true
  apply (binderSafeListAt_eq_true_iff _ _ _).mpr
  intro pattern member
  obtain ⟨header, membership, rfl⟩ := List.mem_map.mp member
  exact Header.pattern_safe (safe header membership)

/-- The output index addresses the list after removing the input. -/
structure Selection (headers : List Header) where
  inputIndex : Nat
  inputBound : inputIndex < headers.length
  outputIndex : Nat
  outputBound : outputIndex < (headers.eraseIdx inputIndex).length
  inputChannel : Pattern
  body : Pattern
  outputChannel : Pattern
  payload : Pattern
  inputEq : headers[inputIndex] = .input inputChannel body
  outputEq : (headers.eraseIdx inputIndex)[outputIndex] = .output outputChannel payload
  channels : rhoCanonicalEquivalent inputChannel outputChannel = true

def Selection.residue {headers : List Header} (selected : Selection headers) : List Header :=
  (headers.eraseIdx selected.inputIndex).eraseIdx selected.outputIndex

def Selection.contractum {headers : List Header} (selected : Selection headers) : Pattern :=
  .collection .hashBag
    (semanticCommSubst selected.body selected.payload :: selected.residue.map Header.pattern) none

/-- The selected substitution and untouched occurrences remain in the
sorted, scope-safe core domain. -/
theorem Selection.contractum_preserves {free : FreeSortContext} {headers : List Header}
    (selected : Selection headers) (typed : ∀ header ∈ headers, header.Typed free)
    (safe : ∀ header ∈ headers, header.Safe) :
    ProcWellSorted rhoReflectivePresentation free [] selected.contractum ∧
      binderSafeAt "NQuote" 0 selected.contractum = true := by
  have inputBound := selected.inputBound
  have outputBound := selected.outputBound
  have inputTyped := typed headers[selected.inputIndex] (List.getElem_mem inputBound)
  have inputSafe := safe headers[selected.inputIndex] (List.getElem_mem inputBound)
  rw [selected.inputEq] at inputTyped inputSafe
  have outputMember : (headers.eraseIdx selected.inputIndex)[selected.outputIndex] ∈ headers :=
    List.mem_of_mem_eraseIdx (List.getElem_mem outputBound)
  have outputTyped := typed _ outputMember
  have outputSafe := safe _ outputMember
  rw [selected.outputEq] at outputTyped outputSafe
  have opened := ScopedSemanticSubstitution.semanticCommSubst_preserves
    inputTyped.2 inputSafe.2 outputTyped.2 outputSafe.2
  have residueMember : ∀ header ∈ selected.residue, header ∈ headers := by
    intro header member
    exact List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member)
  have residueTyped := parallel_typed (fun header member => typed header (residueMember header member))
  have residueSafe := parallel_safe (fun header member => safe header (residueMember header member))
  refine ⟨ProcWellSorted.parallel (.cons opened.1 ?_), ?_⟩
  · exact (rho_parallel_wellSorted_inv residueTyped).2
  · change (binderSafeAt "NQuote" 0 (semanticCommSubst selected.body selected.payload) &&
      binderSafeListAt "NQuote" 0 (selected.residue.map Header.pattern)) = true
    change binderSafeListAt "NQuote" 0 (selected.residue.map Header.pattern) = true at residueSafe
    rw [opened.2, residueSafe]
    rfl

theorem Selection.contractum_typed {free : FreeSortContext} {headers : List Header}
    (selected : Selection headers) (typed : ∀ header ∈ headers, header.Typed free)
    (safe : ∀ header ∈ headers, header.Safe) :
    ProcWellSorted rhoReflectivePresentation free [] selected.contractum :=
  (selected.contractum_preserves typed safe).1

theorem Selection.contractum_safe {free : FreeSortContext} {headers : List Header}
    (selected : Selection headers) (typed : ∀ header ∈ headers, header.Typed free)
    (safe : ∀ header ∈ headers, header.Safe) :
    binderSafeAt "NQuote" 0 selected.contractum = true :=
  (selected.contractum_preserves typed safe).2

theorem Selection.contractum_hashSetFree {free : FreeSortContext} {headers : List Header}
    (selected : Selection headers) (typed : ∀ header ∈ headers, header.Typed free)
    (safe : ∀ header ∈ headers, header.Safe) : HashSetFree selected.contractum :=
  rhoProcWellSorted_hashSetFree (selected.contractum_typed typed safe)

/-- A nonbag supplies neither a root COMM nor parallel descent. -/
theorem nonbag_no_step {fuel : Nat} {source target : Pattern}
    (nonbag : ∀ elements rest, source ≠ .collection .hashBag elements rest)
    (step : RhoStepAt fuel source target) : False := by
  cases fuel with
  | zero => cases step
  | succ fuel =>
      rcases rhoStepAt_succ_inv step with comm | descent
      · obtain ⟨bindings, matched, _⟩ := comm
        obtain ⟨elements, rest, _, _, _, _, _, _, _, _, _, sourceEq, _⟩ :=
          rhoComm_match_shape matched
        exact nonbag elements rest sourceEq
      · obtain ⟨elements, rest, _, _, _, sourceEq, _⟩ := descent
        exact nonbag elements rest sourceEq

theorem step_top_level {headers : List Header} {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (parallel headers) target) :
    ∃ bindings, bindings ∈ matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite
      (parallel headers) ∧
      applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite bindings = target := by
  cases fuel with
  | zero => cases step
  | succ fuel =>
      rcases rhoStepAt_succ_inv step with comm | descent
      · exact comm
      · obtain ⟨elements, rest, index, bound, candidate, sourceEq, inner, _⟩ := descent
        change Pattern.collection .hashBag (headers.map Header.pattern) none = _ at sourceEq
        cases sourceEq
        have sourceBound : index < headers.length := by simpa using bound
        exact False.elim (nonbag_no_step (Header.nonbag headers[index])
          (by simpa using inner))

theorem selection_of_step {free : FreeSortContext} {headers : List Header}
    (typed : ∀ header ∈ headers, header.Typed free) {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (parallel headers) target) :
    ∃ selected : Selection headers, target = selected.contractum := by
  obtain ⟨bindings, matched, applied⟩ := step_top_level step
  obtain ⟨elements, rest, i, hi, j, hj, channel, body, metadata, other, payload,
    sourceEq, inputEq, outputEq, channels, bindingsEq⟩ := rhoComm_match_shape matched
  change Pattern.collection .hashBag (headers.map Header.pattern) none = _ at sourceEq
  cases sourceEq
  have ib : i < headers.length := by simpa using hi
  have jb : j < (headers.eraseIdx i).length := by simpa [List.eraseIdx_map] using hj
  have input : headers[i] = .input channel body ∧ metadata = none :=
    input_shape (by simpa using inputEq)
  have output : (headers.eraseIdx i)[j] = .output other payload :=
    output_shape (by simpa [List.eraseIdx_map] using outputEq)
  rcases input with ⟨input, rfl⟩
  let selected : Selection headers := ⟨i, ib, j, jb, channel, body, other, payload,
    input, output, channels⟩
  have bodyTyped : ProcWellSorted rhoReflectivePresentation free ["Name"] body := by
    have fact := typed headers[i] (List.getElem_mem ib)
    rw [input] at fact
    exact fact.2
  have payloadTyped : ProcWellSorted rhoReflectivePresentation free [] payload := by
    have fact := typed (headers.eraseIdx i)[j]
      (List.mem_of_mem_eraseIdx (List.getElem_mem jb))
    rw [output] at fact
    exact fact.2
  refine ⟨selected, ?_⟩
  rw [bindingsEq] at applied
  have application := apply_commBindingsAt bodyTyped payloadTyped
    (headers.map Header.pattern) i j channel
  simp only [commBindingsAt] at application
  rw [applied] at application
  simpa [selected, Selection.contractum, Selection.residue, List.eraseIdx_map] using application

/-- Every selected pair really fires by the authored COMM rule. -/
theorem Selection.authored {free : FreeSortContext} {headers : List Header}
    (selected : Selection headers) (typed : ∀ header ∈ headers, header.Typed free) :
    RhoStepAt 1 (parallel headers) selected.contractum := by
  have inputBound := selected.inputBound
  have outputBound := selected.outputBound
  have inputTyped := typed headers[selected.inputIndex] (List.getElem_mem selected.inputBound)
  have outputTyped := typed (headers.eraseIdx selected.inputIndex)[selected.outputIndex]
    (List.mem_of_mem_eraseIdx (List.getElem_mem selected.outputBound))
  rw [selected.inputEq] at inputTyped
  rw [selected.outputEq] at outputTyped
  have firing := rhoStepAt_one_comm
    (elements := headers.map Header.pattern) (inputIndex := selected.inputIndex)
    (outputIndex := selected.outputIndex) (by simpa using selected.inputBound)
    (by simpa [List.eraseIdx_map] using selected.outputBound)
    (inputChannel := selected.inputChannel) (body := selected.body)
    (outputChannel := selected.outputChannel) (payload := selected.payload)
    (by simpa only [List.getElem_map, Header.pattern] using congrArg Header.pattern selected.inputEq)
    (by simpa only [List.eraseIdx_map, List.getElem_map, Header.pattern] using
      congrArg Header.pattern selected.outputEq)
    selected.channels
  rw [apply_commBindingsAt inputTyped.2 outputTyped.2] at firing
  simpa [parallel, Selection.contractum, Selection.residue, List.eraseIdx_map] using firing

theorem canonicalParallel_eq (headers : List Header) :
    canonicalParallel headers = collapseBag
      (sortPatterns (headers.map (fun header => Canonical.canonicalize header.pattern))) := by
  rw [canonicalParallel, parallel, canonicalize_bag, normalizeBagElements_eq_sort_bagContents]
  have contents : bagContents ((headers.map Header.pattern).map Canonical.canonicalize) =
      (headers.map Header.pattern).map Canonical.canonicalize := by
    apply bagContents_eq_self
    · intro pattern membership
      obtain ⟨source, member, rfl⟩ := List.mem_map.mp membership
      obtain ⟨header, _, rfl⟩ := List.mem_map.mp member
      exact header.canonical_nonunit
    · intro pattern membership elements
      obtain ⟨source, member, rfl⟩ := List.mem_map.mp membership
      obtain ⟨header, _, rfl⟩ := List.mem_map.mp member
      exact header.canonical_nonbag elements none
  rw [contents, List.map_map]
  rfl

private theorem collapse_source {patterns elements : List Pattern} {rest : Option String}
    (nonbags : ∀ pattern ∈ patterns, ∀ elements rest,
      pattern ≠ .collection .hashBag elements rest)
    (equal : collapseBag patterns = .collection .hashBag elements rest) :
    rest = none ∧ patterns = elements := by
  cases patterns with
  | nil => simp [collapseBag] at equal
  | cons first tail =>
      cases tail with
      | nil => exact False.elim (nonbags first (by simp) elements rest equal)
      | cons second tail =>
          exact ⟨((Pattern.collection.inj equal).2.2).symm,
            (Pattern.collection.inj equal).2.1⟩

theorem canonical_step_is_frontier {headers : List Header} {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (canonicalParallel headers) target) :
    RhoStepAt 1 (canonicalParallel headers) target := by
  cases fuel with
  | zero => cases step
  | succ fuel =>
      rcases rhoStepAt_succ_inv step with comm | descent
      · obtain ⟨bindings, matched, applied⟩ := comm
        exact .rule rhoCommRewrite_mem matched (.nil _) applied
      · obtain ⟨elements, rest, index, bound, candidate, sourceEq, inner, _⟩ := descent
        let original := headers.map (fun header => Canonical.canonicalize header.pattern)
        have nonbags : ∀ pattern ∈ sortPatterns original, ∀ elements rest,
            pattern ≠ .collection .hashBag elements rest := by
          intro pattern member elements rest
          have unsorted := (Canonical.sortPatterns_perm original).mem_iff.mpr member
          obtain ⟨header, _, rfl⟩ := List.mem_map.mp unsorted
          exact header.canonical_nonbag elements rest
        rw [canonicalParallel_eq] at sourceEq
        obtain ⟨rfl, sortedEq⟩ := collapse_source nonbags sourceEq
        have member : elements[index] ∈ sortPatterns original := by
          rw [sortedEq]
          exact List.getElem_mem bound
        exact False.elim (nonbag_no_step (nonbags elements[index] member) inner)

private theorem canonical_input_shape {header : Header} {channel body : Pattern}
    {metadata : Option String}
    (shape : Canonical.canonicalize header.pattern =
      .apply "PInput" [channel, .lambda metadata body]) :
    ∃ originalChannel originalBody, header = .input originalChannel originalBody ∧
      metadata = none ∧ channel = Canonical.canonicalize originalChannel ∧
      body = Canonical.canonicalize originalBody := by
  cases header with
  | input subject handler =>
      have equal : Canonical.canonicalize subject = channel ∧ none = metadata ∧
          Canonical.canonicalize handler = body := by
        simpa only [Header.pattern, canonicalize_input, Pattern.apply.injEq,
          List.cons.injEq, Pattern.lambda.injEq, true_and, and_true] using shape
      rcases equal with ⟨rfl, rfl, rfl⟩
      exact ⟨subject, handler, rfl, rfl, rfl, rfl⟩
  | output subject payload =>
      simp [Header.pattern, canonicalize_output] at shape

private theorem canonical_output_shape {header : Header} {channel payload : Pattern}
    (shape : Canonical.canonicalize header.pattern = .apply "POutput" [channel, payload]) :
    ∃ originalChannel originalPayload, header = .output originalChannel originalPayload ∧
      channel = Canonical.canonicalize originalChannel ∧
      payload = Canonical.canonicalize originalPayload := by
  cases header with
  | input subject handler => simp [Header.pattern, canonicalize_input] at shape
  | output subject value =>
      have equal : Canonical.canonicalize subject = channel ∧
          Canonical.canonicalize value = payload := by
        simpa only [Header.pattern, canonicalize_output, Pattern.apply.injEq,
          List.cons.injEq, true_and, and_true] using shape
      rcases equal with ⟨rfl, rfl⟩
      exact ⟨subject, value, rfl, rfl, rfl⟩

/-- Canonical execution selects original occurrence positions. Only the
residual order is forgotten; the supplied endpoint's canonical form is
that of the original body's actual semantic substitution and residue. -/
theorem canonical_selection_of_step {free : FreeSortContext} {headers : List Header}
    (typed : ∀ header ∈ headers, header.Typed free)
    (safe : ∀ header ∈ headers, header.Safe) {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (canonicalParallel headers) target) :
    ∃ selected : Selection headers,
      Canonical.canonicalize target = Canonical.canonicalize selected.contractum := by
  obtain ⟨bindings, matched, applied⟩ := rhoStepAt_one_inv (canonical_step_is_frontier step)
  obtain ⟨elements, rest, inputIndex, inputBound, outputIndex, outputBound,
    channel, body, metadata, other, payload, sourceEq, inputEq, outputEq,
    channels, bindingsEq⟩ := rhoComm_match_shape matched
  let original := headers.map (fun header => Canonical.canonicalize header.pattern)
  have nonbags : ∀ pattern ∈ sortPatterns original, ∀ elements rest,
      pattern ≠ .collection .hashBag elements rest := by
    intro pattern member elements rest
    have unsorted := (Canonical.sortPatterns_perm original).mem_iff.mpr member
    obtain ⟨header, _, rfl⟩ := List.mem_map.mp unsorted
    exact header.canonical_nonbag elements rest
  rw [canonicalParallel_eq] at sourceEq
  obtain ⟨rfl, sortedEq⟩ := collapse_source nonbags sourceEq
  have consumed :
      (.apply "PInput" [channel, .lambda metadata body] ::
        .apply "POutput" [other, payload] ::
        (elements.eraseIdx inputIndex).eraseIdx outputIndex).Perm elements := by
    have second := List.getElem_cons_eraseIdx_perm outputBound
    have first := List.getElem_cons_eraseIdx_perm inputBound
    simpa [inputEq, outputEq] using (second.cons elements[inputIndex]).trans first
  have occurrences : original.Perm
      (.apply "PInput" [channel, .lambda metadata body] ::
        .apply "POutput" [other, payload] ::
        (elements.eraseIdx inputIndex).eraseIdx outputIndex) :=
    (Canonical.sortPatterns_perm original).trans (by simpa [sortedEq] using consumed.symm)
  obtain ⟨i, hi, j, hj, canonicalInput, canonicalOutput, residuePermutation⟩ := locate_pair occurrences
  have ib : i < headers.length := by simpa [original] using hi
  have jb : j < (headers.eraseIdx i).length := by simpa [original, List.eraseIdx_map] using hj
  have inputEncoded : Canonical.canonicalize headers[i].pattern =
      .apply "PInput" [channel, .lambda metadata body] := by
    simpa [original] using canonicalInput
  have outputEncoded : Canonical.canonicalize (headers.eraseIdx i)[j].pattern =
      .apply "POutput" [other, payload] := by
    simpa [original, List.eraseIdx_map] using canonicalOutput
  obtain ⟨sourceChannel, sourceBody, sourceInput, rfl, rfl, rfl⟩ :=
    canonical_input_shape inputEncoded
  obtain ⟨sourceOther, sourcePayload, sourceOutput, rfl, rfl⟩ :=
    canonical_output_shape outputEncoded
  have sourceChannels : rhoCanonicalEquivalent sourceChannel sourceOther = true := by
    rw [rhoCanonicalEquivalent_iff] at channels ⊢
    simpa only [Canonical.canonicalize_idempotent] using channels
  let selected : Selection headers :=
    ⟨i, ib, j, jb, sourceChannel, sourceBody, sourceOther, sourcePayload,
      sourceInput, sourceOutput, sourceChannels⟩
  have bodyTyped : ProcWellSorted rhoReflectivePresentation free ["Name"] sourceBody := by
    have fact := typed headers[i] (List.getElem_mem ib)
    rw [sourceInput] at fact
    exact fact.2
  have bodySafe : binderSafeAt "NQuote" 1 sourceBody = true := by
    have fact := safe headers[i] (List.getElem_mem ib)
    rw [sourceInput] at fact
    exact fact.2
  have payloadTyped : ProcWellSorted rhoReflectivePresentation free [] sourcePayload := by
    have fact := typed (headers.eraseIdx i)[j]
      (List.mem_of_mem_eraseIdx (List.getElem_mem jb))
    rw [sourceOutput] at fact
    exact fact.2
  let matcherResidue := (elements.eraseIdx inputIndex).eraseIdx outputIndex
  have exactTarget : target = .collection .hashBag
      (semanticCommSubst (Canonical.canonicalize sourceBody)
        (Canonical.canonicalize sourcePayload) :: matcherResidue) none := by
    rw [bindingsEq] at applied
    have application := apply_commBindingsAt
      (canonicalize_procWellSorted ["Name"] bodyTyped)
      (canonicalize_procWellSorted [] payloadTyped)
      elements inputIndex outputIndex (Canonical.canonicalize sourceChannel)
    simp only [commBindingsAt] at application
    rw [applied] at application
    exact application
  have heads := canonicalize_semanticCommSubst_canonicalize bodyTyped bodySafe
    (rhoProcWellSorted_hashSetFree payloadTyped)
  have tails : (bagContents (matcherResidue.map Canonical.canonicalize)).Perm
      (bagContents ((selected.residue.map Header.pattern).map Canonical.canonicalize)) := by
    have mapped := residuePermutation.symm.map Canonical.canonicalize
    have unchanged : (matcherResidue.map Canonical.canonicalize).Perm
        ((selected.residue.map Header.pattern).map Canonical.canonicalize) := by
      simpa only [original, selected, Selection.residue, matcherResidue, List.eraseIdx_map,
        List.map_map, Function.comp_def, Canonical.canonicalize_idempotent] using mapped
    exact bagContents_perm unchanged
  refine ⟨selected, ?_⟩
  rw [exactTarget]
  exact canonicalize_bag_cons_congr heads tails

/-- An actual authored step from any well-sorted representative of the
same frontier class selects the same original occurrence inventory. The
compiler invariant can therefore use canonical equality without prescribing
the runtime's concrete parallel bracketing or element order. -/
theorem representative_selection_of_step {free : FreeSortContext} {headers : List Header}
    (typed : ∀ header ∈ headers, header.Typed free)
    (safe : ∀ header ∈ headers, header.Safe) {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free [] source)
    (sourceSafe : binderSafeAt "NQuote" 0 source = true)
    (represented : Canonical.canonicalize source = canonicalParallel headers)
    (step : RhoStep source target) :
    ∃ selected : Selection headers,
      Canonical.canonicalize target = Canonical.canonicalize selected.contractum := by
  obtain ⟨canonicalTarget, canonicalStep, endpoint⟩ :=
    canonicalStep_complete_of_rhoStep sourceTyped sourceSafe step
  rw [represented] at canonicalStep
  obtain ⟨selected, contractum⟩ := canonical_selection_of_step typed safe canonicalStep
  exact ⟨selected, endpoint.symm.trans contractum⟩

/-- Structural equations supply that frontier class for typed pure-rho
representatives. No execution back-condition is assumed. -/
theorem equivalent_selection_of_step {free : FreeSortContext} {headers : List Header}
    (typed : ∀ header ∈ headers, header.Typed free)
    (safe : ∀ header ∈ headers, header.Safe) {source target : Pattern}
    (sourceTyped : ProcWellSorted rhoReflectivePresentation free [] source)
    (sourceSafe : binderSafeAt "NQuote" 0 source = true)
    (equations : StructuralCongruence source (parallel headers))
    (step : RhoStep source target) :
    ∃ selected : Selection headers,
      Canonical.canonicalize target = Canonical.canonicalize selected.contractum := by
  apply representative_selection_of_step typed safe sourceTyped sourceSafe ?_ step
  exact canonicalize_eq_of_structuralCongruence equations
    (rhoProcWellSorted_hashSetFree sourceTyped)
    (rhoProcWellSorted_hashSetFree (parallel_typed typed))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion
