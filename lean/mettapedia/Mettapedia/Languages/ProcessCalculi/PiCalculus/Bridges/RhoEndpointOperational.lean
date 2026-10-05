import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint
import Mettapedia.GSLT.Core.FunctionalBisimulation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-!
# Supplied rho firings and their named pi endpoints

The matcher and rule application used here are the authored rho operations.
The converse identifies the actual selected input, output and retained
occurrences. The returned source step is therefore tied to the supplied
target, up to rho's existing equations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus hiding StructuralCongruence NameEquiv
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
  (rhoStepAt_one_comm apply_commBindingsAt commBindingsAt rhoStepAt_succ_inv
    rhoStepAt_one_inv canonicalize_input canonicalize_output canonicalize_bag bagContents_eq_self
    canonicalize_bag_cons_congr locate_pair canonicalStep_complete_of_rhoStep)

local notation:50 p " ≡ᵨ " q =>
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p q

open private semanticSubstProc_dropPayload_SC_openBVar
  closeFVar_encode_rf_rhoProcCoreShape closeFVar_encode_rf_noBoundUnderQuote
  rhoPar_to_two from Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation

theorem rho_nonbag_no_step {fuel : Nat} {source target : Pattern}
    (nonbag : ∀ elements rest, source ≠ .collection .hashBag elements rest)
    (step : RhoStepAt fuel source target) : False :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion.nonbag_no_step nonbag step

private theorem atom_nonbag {process : Process} (atom : Atom process) (n v : String) :
    ∀ elements rest, encode process n v ≠ .collection .hashBag elements rest := by
  cases process <;> simp [Atom] at atom
  all_goals intro elements rest; simp [encode, rhoInput, rhoOutput]

theorem atom_no_step {process : Process} (atom : Atom process) (n v : String)
    {fuel : Nat} {target : Pattern} (step : RhoStepAt fuel (encode process n v) target) :
    False := rho_nonbag_no_step (atom_nonbag atom n v) step

/-- Any authored step of a flat compiled network is its actual top-level
COMM application. No guarded component supplies an internal parallel step. -/
theorem network_step_top_level {processes : List Process} (flat : Flat processes)
    (n v : String) {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (networkPattern processes n v) target) :
    ∃ bindings, bindings ∈ matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite
      (networkPattern processes n v) ∧
      applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite bindings = target := by
  cases fuel with
  | zero => cases step
  | succ fuel =>
      rcases rhoStepAt_succ_inv step with comm | parallel
      · exact comm
      · obtain ⟨elements, rest, index, hi, candidate, sourceEq, inner, _⟩ := parallel
        change Pattern.collection .hashBag (processes.map (fun p => encode p n v)) none = _ at sourceEq
        cases sourceEq
        have indexBound : index < processes.length := by simpa using hi
        have forbidden := atom_no_step (flat processes[index] (List.getElem_mem indexBound))
          n v (by simpa using inner)
        exact False.elim forbidden

private theorem decode_input {process : Process} (atom : Atom process) (n v : String)
    {channel body : Pattern} {metadata : Option String}
    (encoded : encode process n v = .apply "PInput" [channel, .lambda metadata body]) :
    ∃ sourceChannel binder continuation, process = .input sourceChannel binder continuation ∧
      channel = .fvar sourceChannel ∧ metadata = none ∧
      body = closeFVar 0 binder (encode continuation n v) := by
  cases process <;> simp [Atom] at atom
  case input sourceChannel binder continuation =>
    have shape : .fvar sourceChannel = channel ∧ none = metadata ∧
        closeFVar 0 binder (encode continuation n v) = body := by
      simpa [encode, rhoInput, piNameToRhoName] using encoded
    exact ⟨sourceChannel, binder, continuation, rfl, shape.1.symm, shape.2.1.symm,
      shape.2.2.symm⟩
  case output sourceChannel datum => simp [encode, rhoOutput] at encoded

private theorem decode_output {process : Process} (atom : Atom process) (n v : String)
    {channel payload : Pattern}
    (encoded : encode process n v = .apply "POutput" [channel, payload]) :
    ∃ sourceChannel datum, process = .output sourceChannel datum ∧
      channel = .fvar sourceChannel ∧ payload = .apply "PDrop" [.fvar datum] := by
  cases process <;> simp [Atom] at atom
  case input sourceChannel binder continuation => simp [encode, rhoInput] at encoded
  case output sourceChannel datum =>
    have shape : .fvar sourceChannel = channel ∧ .apply "PDrop" [.fvar datum] = payload := by
      simpa [encode, rhoOutput, rhoDrop, piNameToRhoName] using encoded
    exact ⟨sourceChannel, datum, rfl, shape.1.symm, shape.2.symm⟩

/-- The semantic COMM substitution, including its quote/drop administrative
equations, reaches the exact maintained encoding of named substitution. -/
theorem contractum_equations {body : Process} (free : RestrictionFree body)
    (binder datum : Name) (n v : String) (distinct : binder ≠ datum)
    (convention : BarendregtFor binder datum body) :
    semanticCommSubst (closeFVar 0 binder (encode body n v))
      (.apply "PDrop" [.fvar datum]) ≡ᵨ encode (body.substitute binder datum) n v := by
  have contracted : semanticCommSubst (closeFVar 0 binder (encode body n v))
      (.apply "PDrop" [.fvar datum]) ≡ᵨ
      openBVar 0 (.fvar datum) (closeFVar 0 binder (encode body n v)) := by
    have shaped := closeFVar_encode_rf_rhoProcCoreShape free 0 binder n v
    have opaqueQuote := closeFVar_encode_rf_noBoundUnderQuote free 0 binder n v 0
    simpa [semanticCommSubst, semanticNormalizeProc, semanticNormalizeName] using
      semanticSubstProc_dropPayload_SC_openBVar 0 datum shaped opaqueQuote
  rw [encode_rf_open_close_subst free binder datum n v distinct convention] at contracted
  exact contracted

private theorem bag_head_congr {first second : Pattern} (rest : List Pattern)
    (related : first ≡ᵨ second) :
    (.collection .hashBag (first :: rest) none) ≡ᵨ
      (.collection .hashBag (second :: rest) none) := by
  refine .par_cong _ _ rfl ?_
  intro index firstBound secondBound
  cases index with
  | zero => exact related
  | succ index => exact .refl _

/-- Releasing a continuation into its active communication components uses
only the maintained compiler's proved parallel equations. -/
theorem release_equations {body : Process} (free : RestrictionFree body)
    {rest : List Process} (flat : Flat rest) (n v : String) :
    (.collection .hashBag (encode body n v :: rest.map (fun p => encode p n v)) none) ≡ᵨ
      networkPattern (components body ++ rest) n v := by
  have releasedFlat : Flat (components body ++ rest) := by
    intro process membership
    rcases List.mem_append.mp membership with released | retained
    · exact components_flat free process released
    · exact flat process retained
  obtain ⟨append⟩ := assemble_append (components body) rest
  obtain ⟨bodyEquations⟩ := assemble_components body
  have joined : StructuralCongruenceRF (assemble (components body ++ rest))
      (.par body (assemble rest)) :=
    .trans _ _ _ append (.par_cong _ _ _ _ bodyEquations (.refl _))
  have encoded := encode_preserves_rfsc joined (assemble_restrictionFree releasedFlat) n v
  rw [encode_assemble releasedFlat] at encoded
  change networkPattern (components body ++ rest) n v ≡ᵨ
    rhoPar (encode body (n ++ "_L") v) (encode (assemble rest) (n ++ "_R") v) at encoded
  rw [encode_rf_ns_independent free (n ++ "_L") n v,
    encode_rf_ns_independent (assemble_restrictionFree flat) (n ++ "_R") n v,
    encode_assemble flat] at encoded
  have flattened : rhoPar (encode body n v) (networkPattern rest n v) ≡ᵨ
      (.collection .hashBag (encode body n v :: rest.map (fun p => encode p n v)) none) :=
    .trans _ _ _ (rhoPar_to_two _ _) (by simpa [networkPattern] using
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_flatten
        [encode body n v] (rest.map (fun p => encode p n v))))
  exact .symm _ _ (.trans _ _ _ encoded flattened)

/-- An authored rho firing at any contextual depth reflects its own selected
pair and its actual contractum, modulo the declared rho equations. -/
theorem rho_firing_reflects {processes : List Process} (flat : Flat processes)
    (safe : Safe processes) (n v : String) {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (networkPattern processes n v) target) :
    ∃ next, NetworkStep processes next ∧ target ≡ᵨ networkPattern next n v := by
  obtain ⟨bindings, matched, applied⟩ := network_step_top_level flat n v step
  obtain ⟨elements, rest, i, hi, j, hj, inputChannel, body, metadata,
    outputChannel, payload, sourceEq, inputEq, outputEq, channels, bindingsEq⟩ :=
    rhoComm_match_shape matched
  change Pattern.collection .hashBag (processes.map (fun p => encode p n v)) none = _ at sourceEq
  cases sourceEq
  have inputBound : i < processes.length := by simpa using hi
  have outputBound : j < (processes.eraseIdx i).length := by
    simpa [List.eraseIdx_map] using hj
  have inputEncoded : encode processes[i] n v = .apply "PInput" [inputChannel, .lambda metadata body] := by
    simpa using inputEq
  have outputEncoded : encode (processes.eraseIdx i)[j] n v = .apply "POutput" [outputChannel, payload] := by
    simpa [List.eraseIdx_map] using outputEq
  obtain ⟨channel, binder, continuation, sourceInput, rfl, rfl, rfl⟩ :=
    decode_input (flat processes[i] (List.getElem_mem inputBound)) n v inputEncoded
  obtain ⟨otherChannel, datum, sourceOutput, rfl, rfl⟩ :=
    decode_output (flat (processes.eraseIdx i)[j]
      (List.mem_of_mem_eraseIdx (List.getElem_mem outputBound))) n v outputEncoded
  have sameChannel : channel = otherChannel := by
    simpa [rhoCanonicalEquivalent, ReflectiveCanonical.canonicalEquivalent,
      ReflectiveCanonical.canonicalize] using channels
  subst otherChannel
  have bodyFree : RestrictionFree continuation := by
    have := flat processes[i] (List.getElem_mem inputBound)
    simpa [sourceInput, Atom] using this
  have commSafe := safe channel binder datum continuation
    (sourceInput ▸ List.getElem_mem inputBound)
    (sourceOutput ▸ List.mem_of_mem_eraseIdx (List.getElem_mem outputBound))
  let residue := (processes.eraseIdx i).eraseIdx j
  have residueFlat : Flat residue := fun process membership =>
    flat process (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx membership))
  have exactTarget : target = .collection .hashBag
      (semanticCommSubst (closeFVar 0 binder (encode continuation n v))
        (.apply "PDrop" [.fvar datum]) :: residue.map (fun p => encode p n v)) none := by
    rw [bindingsEq] at applied
    have application := apply_commBindingsAt (close_encode_procWellSorted bodyFree binder n v)
      (show ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext []
        (.apply "PDrop" [.fvar datum]) from .drop (.fvar rfl))
      (processes.map (fun p => encode p n v)) i j (.fvar channel)
    simp only [commBindingsAt] at application
    rw [applied] at application
    simpa [residue, List.eraseIdx_map] using application
  refine ⟨components (continuation.substitute binder datum) ++ residue,
    .comm i inputBound j outputBound channel binder datum continuation sourceInput sourceOutput, ?_⟩
  rw [exactTarget]
  exact .trans _ _ _
    (bag_head_congr _ (contractum_equations bodyFree binder datum n v commSafe.1 commSafe.2))
    (release_equations (rf_substitute bodyFree binder datum) residueFlat n v)

/-- Every selected source pair executes by the authored rho COMM rule. The
actual target retains the source's other occurrences and agrees with the
exact named continuation by the proved administrative equations. -/
theorem NetworkStep.rho_firing {source next : List Process}
    (step : NetworkStep source next) (flat : Flat source) (safe : Safe source) (n v : String) :
    ∃ target, RhoStepAt 1 (networkPattern source n v) target ∧
      target ≡ᵨ networkPattern next n v := by
  cases step with
  | comm i hi j hj channel binder datum body input output =>
      have bodyFree : RestrictionFree body := by
        have := flat source[i] (List.getElem_mem hi)
        simpa [input, Atom] using this
      have commSafe := safe channel binder datum body
        (input ▸ List.getElem_mem hi)
        (output ▸ List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      let residue := (source.eraseIdx i).eraseIdx j
      let target : Pattern := .collection .hashBag
        (semanticCommSubst (closeFVar 0 binder (encode body n v))
          (.apply "PDrop" [.fvar datum]) :: residue.map (fun p => encode p n v)) none
      have firing := rhoStepAt_one_comm
        (elements := source.map (fun p => encode p n v))
        (inputIndex := i) (outputIndex := j)
        (by simpa using hi) (by simpa [List.eraseIdx_map] using hj)
        (by simpa [encode, rhoInput, piNameToRhoName] using congrArg (fun p => encode p n v) input)
        (by simpa [List.eraseIdx_map, encode, rhoOutput, rhoDrop, piNameToRhoName] using
          congrArg (fun p => encode p n v) output)
        (by simp [rhoCanonicalEquivalent, ReflectiveCanonical.canonicalEquivalent])
      have application := apply_commBindingsAt (close_encode_procWellSorted bodyFree binder n v)
        (show ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext []
          (.apply "PDrop" [.fvar datum]) from .drop (.fvar rfl))
        (source.map (fun p => encode p n v)) i j (.fvar channel)
      have firingExact : RhoStepAt 1 (networkPattern source n v) target := by
        simpa only [application, List.eraseIdx_map, networkPattern, target, residue] using firing
      have residueFlat : Flat residue := fun process membership =>
        flat process (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx membership))
      exact ⟨target, firingExact, .trans _ _ _
        (bag_head_congr _ (contractum_equations bodyFree binder datum n v commSafe.1 commSafe.2))
        (release_equations (rf_substitute bodyFree binder datum) residueFlat n v)⟩

/-- This endpoint comparison reaches the source's already-authored pi GSLT,
in addition to its named semantics. -/
theorem rho_firing_reflects_authored {processes : List Process} (flat : Flat processes)
    (safe : Safe processes) (n v : String) {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (networkPattern processes n v) target) :
    ∃ next, NetworkStep processes next ∧ (target ≡ᵨ networkPattern next n v) ∧
      Mettapedia.GSLT.LanguageDef.EquationSemantics.StepModuloEquations
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
        PiCalcInstance.piCalc (PiCalcInstance.piToPattern (assemble processes))
          (PiCalcInstance.piToPattern (assemble next)) := by
  obtain ⟨next, selected, endpoint⟩ := rho_firing_reflects flat safe n v step
  obtain ⟨named, _⟩ := selected.named safe
  exact ⟨next, selected, endpoint, PiCalcInstance.reducesRF_authored_step named⟩

/-! ## Canonical runtime states -/

/-- The maintained compiler followed by rho's proved canonical section. -/
def canonicalNetwork (processes : List Process) (n v : String) : Pattern :=
  Canonical.canonicalize (networkPattern processes n v)

/-- An actual authored COMM frontier followed by the runtime's canonical
section. The relation is defined entirely by rho execution; it does not
consult a source process or a source-step certificate. -/
def CanonicalFiring (source target : Pattern) : Prop :=
  ∃ contractum, RhoStepAt 1 source contractum ∧ Canonical.canonicalize contractum = target

private theorem atom_canonical_plain {process : Process} (atom : Atom process) (n v : String) :
    Canonical.canonicalize (encode process n v) ≠ .apply "PZero" [] ∧
      ∀ elements rest, Canonical.canonicalize (encode process n v) ≠
        .collection .hashBag elements rest := by
  cases process <;> simp [Atom] at atom
  all_goals simp [encode, rhoInput, rhoOutput, piNameToRhoName, rhoDrop,
    canonicalize_input, canonicalize_output, Canonical.canonicalize, Canonical.canonicalizeList]

private theorem canonicalNetwork_eq {processes : List Process} (flat : Flat processes) (n v : String) :
    canonicalNetwork processes n v = collapseBag
      (sortPatterns (processes.map (fun p => Canonical.canonicalize (encode p n v)))) := by
  rw [canonicalNetwork, networkPattern, canonicalize_bag, normalizeBagElements_eq_sort_bagContents]
  have contents : bagContents
      ((processes.map (fun p => encode p n v)).map Canonical.canonicalize) =
      (processes.map (fun p => encode p n v)).map Canonical.canonicalize := by
    apply bagContents_eq_self
    · intro pattern membership
      obtain ⟨encoded, encodedMember, rfl⟩ := List.mem_map.mp membership
      obtain ⟨process, processMember, rfl⟩ := List.mem_map.mp encodedMember
      exact (atom_canonical_plain (flat process processMember) n v).1
    · intro pattern membership elements
      obtain ⟨encoded, encodedMember, rfl⟩ := List.mem_map.mp membership
      obtain ⟨process, processMember, rfl⟩ := List.mem_map.mp encodedMember
      exact (atom_canonical_plain (flat process processMember) n v).2 elements none
  rw [contents, List.map_map]
  rfl

private theorem collapseBag_source {patterns elements : List Pattern} {rest : Option String}
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
          simpa only [collapseBag, Pattern.collection.injEq, true_and] using
            And.intro ((Pattern.collection.inj equal).2.2).symm ((Pattern.collection.inj equal).2.1)

private theorem list_encode_pure {processes : List Process} (flat : Flat processes) (n v : String) :
    HashSetFreeList (processes.map (fun p => encode p n v)) := by
  induction processes with
  | nil => trivial
  | cons process rest ih =>
      exact ⟨encode_hashSetFree (atom_restrictionFree (flat process (by simp))) n v,
        ih (fun member membership => flat member (by simp [membership]))⟩

theorem network_pure {processes : List Process} (flat : Flat processes) (n v : String) :
    HashSetFree (networkPattern processes n v) := list_encode_pure flat n v

theorem network_procWellSorted {processes : List Process} (flat : Flat processes) (n v : String) :
    ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext [] (networkPattern processes n v) := by
  rw [← encode_assemble flat]
  exact encode_procWellSorted (assemble_restrictionFree flat) n v

theorem network_binderSafe {processes : List Process} (flat : Flat processes) (n v : String) :
    binderSafeAt "NQuote" 0 (networkPattern processes n v) = true := by
  rw [← encode_assemble flat]
  exact encode_binderSafe (assemble_restrictionFree flat) n v

private theorem firing_pure {processes : List Process} (flat : Flat processes) (n v : String)
    {fuel : Nat} {target : Pattern} (step : RhoStepAt fuel (networkPattern processes n v) target) :
    HashSetFree target := by
  obtain ⟨reduction⟩ := rhoStepAt_sound (network_procWellSorted flat n v) step
  exact hashSetFree_of_reduces reduction (network_pure flat n v)

/-- A selected named communication runs on the actual canonical rho state,
and its normalized endpoint is the compilation of that exact named reduct. -/
theorem NetworkStep.canonical_firing {source next : List Process}
    (step : NetworkStep source next) (flat : Flat source) (safe : Safe source) (n v : String) :
    CanonicalFiring (canonicalNetwork source n v) (canonicalNetwork next n v) := by
  obtain ⟨contractum, firing, equations⟩ := step.rho_firing flat safe n v
  obtain ⟨canonicalContractum, canonicalFiring, agreement⟩ := canonicalStep_complete_of_rhoStep
    (network_procWellSorted flat n v) (network_binderSafe flat n v) ⟨1, firing⟩
  have endpoint := canonicalize_eq_of_structuralCongruence equations
    (firing_pure flat n v firing) (network_pure (step.flat flat) n v)
  exact ⟨canonicalContractum, canonicalFiring, agreement.trans endpoint⟩

private theorem decode_canonical_input {process : Process} (atom : Atom process) (n v : String)
    {channel body : Pattern} {metadata : Option String}
    (encoded : Canonical.canonicalize (encode process n v) =
      .apply "PInput" [channel, .lambda metadata body]) :
    ∃ sourceChannel binder continuation, process = .input sourceChannel binder continuation ∧
      channel = .fvar sourceChannel ∧ metadata = none ∧
      body = Canonical.canonicalize (closeFVar 0 binder (encode continuation n v)) := by
  cases process <;> simp [Atom] at atom
  case input sourceChannel binder continuation =>
    have shape : .fvar sourceChannel = channel ∧ none = metadata ∧
        Canonical.canonicalize (closeFVar 0 binder (encode continuation n v)) = body := by
      simpa [encode, rhoInput, piNameToRhoName, canonicalize_input, Canonical.canonicalize] using encoded
    exact ⟨sourceChannel, binder, continuation, rfl, shape.1.symm, shape.2.1.symm,
      shape.2.2.symm⟩
  case output sourceChannel datum =>
    simp [encode, rhoOutput, rhoDrop, piNameToRhoName, canonicalize_output,
      Canonical.canonicalize, Canonical.canonicalizeList] at encoded

private theorem decode_canonical_output {process : Process} (atom : Atom process) (n v : String)
    {channel payload : Pattern}
    (encoded : Canonical.canonicalize (encode process n v) = .apply "POutput" [channel, payload]) :
    ∃ sourceChannel datum, process = .output sourceChannel datum ∧
      channel = .fvar sourceChannel ∧ payload = .apply "PDrop" [.fvar datum] := by
  cases process <;> simp [Atom] at atom
  case input sourceChannel binder continuation =>
    simp [encode, rhoInput, piNameToRhoName, canonicalize_input] at encoded
  case output sourceChannel datum =>
    have shape : .fvar sourceChannel = channel ∧ .apply "PDrop" [.fvar datum] = payload := by
      simpa [encode, rhoOutput, rhoDrop, piNameToRhoName, canonicalize_output,
        Canonical.canonicalize, Canonical.canonicalizeList] using encoded
    exact ⟨sourceChannel, datum, rfl, shape.1.symm, shape.2.symm⟩

/-- Every actual canonical rho COMM has a named source step at the supplied
endpoint. Sorting and duplicate occurrences affect only where the matcher
finds the partners; the returned source indices select those same partners. -/
theorem canonical_firing_contractum_reflects {processes : List Process}
    (flat : Flat processes) (safe : Safe processes) (n v : String) {target : Pattern}
    (step : RhoStepAt 1 (canonicalNetwork processes n v) target) :
    ∃ next, NetworkStep processes next ∧ Canonical.canonicalize target = canonicalNetwork next n v := by
  obtain ⟨bindings, matched, applied⟩ := rhoStepAt_one_inv step
  obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound,
    inputChannel, body, metadata, outputChannel, payload, sourceEq, inputEq, outputEq,
    channels, bindingsEq⟩ := rhoComm_match_shape matched
  let original := processes.map (fun p => Canonical.canonicalize (encode p n v))
  have originalNonbags : ∀ pattern ∈ original, ∀ elements rest,
      pattern ≠ .collection .hashBag elements rest := by
    intro pattern membership elements rest
    obtain ⟨process, member, rfl⟩ := List.mem_map.mp membership
    exact (atom_canonical_plain (flat process member) n v).2 elements rest
  have sortedNonbags : ∀ pattern ∈ sortPatterns original, ∀ elements rest,
      pattern ≠ .collection .hashBag elements rest := fun pattern membership =>
    originalNonbags pattern ((Canonical.sortPatterns_perm original).mem_iff.mpr membership)
  rw [canonicalNetwork_eq flat n v] at sourceEq
  obtain ⟨rfl, sortedEq⟩ := collapseBag_source sortedNonbags sourceEq
  have selectedPermutation :
      (.apply "PInput" [inputChannel, .lambda metadata body] ::
        .apply "POutput" [outputChannel, payload] ::
        (elements.eraseIdx inputIndex).eraseIdx outputIndex).Perm elements := by
    have second := List.getElem_cons_eraseIdx_perm outputBound
    have first := List.getElem_cons_eraseIdx_perm inputBound
    have both := (second.cons elements[inputIndex]).trans first
    simpa [inputEq, outputEq] using both
  have originalPermutation : original.Perm
      (.apply "PInput" [inputChannel, .lambda metadata body] ::
        .apply "POutput" [outputChannel, payload] ::
        (elements.eraseIdx inputIndex).eraseIdx outputIndex) := by
    exact ((Canonical.sortPatterns_perm original).trans (by simpa [sortedEq] using selectedPermutation.symm))
  obtain ⟨i, hi, j, hj, canonicalInput, canonicalOutput, residuePermutation⟩ :=
    locate_pair originalPermutation
  have sourceInputBound : i < processes.length := by simpa [original] using hi
  have sourceOutputBound : j < (processes.eraseIdx i).length := by
    simpa [original, List.eraseIdx_map] using hj
  have inputEncoded : Canonical.canonicalize (encode processes[i] n v) =
      .apply "PInput" [inputChannel, .lambda metadata body] := by
    simpa [original] using canonicalInput
  have outputEncoded : Canonical.canonicalize (encode (processes.eraseIdx i)[j] n v) =
      .apply "POutput" [outputChannel, payload] := by
    simpa [original, List.eraseIdx_map] using canonicalOutput
  obtain ⟨channel, binder, continuation, sourceInput, rfl, rfl, rfl⟩ :=
    decode_canonical_input (flat processes[i] (List.getElem_mem sourceInputBound)) n v inputEncoded
  obtain ⟨otherChannel, datum, sourceOutput, rfl, rfl⟩ :=
    decode_canonical_output (flat (processes.eraseIdx i)[j]
      (List.mem_of_mem_eraseIdx (List.getElem_mem sourceOutputBound))) n v outputEncoded
  have sameChannel : channel = otherChannel := by
    simpa [rhoCanonicalEquivalent, ReflectiveCanonical.canonicalEquivalent,
      ReflectiveCanonical.canonicalize] using channels
  subst otherChannel
  have bodyFree : RestrictionFree continuation := by
    have := flat processes[i] (List.getElem_mem sourceInputBound)
    simpa [sourceInput, Atom] using this
  have commSafe := safe channel binder datum continuation
    (sourceInput ▸ List.getElem_mem sourceInputBound)
    (sourceOutput ▸ List.mem_of_mem_eraseIdx (List.getElem_mem sourceOutputBound))
  let sourceResidue := (processes.eraseIdx i).eraseIdx j
  let matcherResidue := (elements.eraseIdx inputIndex).eraseIdx outputIndex
  have sourceResidueFlat : Flat sourceResidue := fun process membership =>
    flat process (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx membership))
  have exactTarget : target = .collection .hashBag
      (semanticCommSubst
        (Canonical.canonicalize (closeFVar 0 binder (encode continuation n v)))
        (.apply "PDrop" [.fvar datum]) :: matcherResidue) none := by
    rw [bindingsEq] at applied
    have application := apply_commBindingsAt
      (canonicalize_procWellSorted ["Name"] (close_encode_procWellSorted bodyFree binder n v))
      (show ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext []
        (.apply "PDrop" [.fvar datum]) from .drop (.fvar rfl))
      elements inputIndex outputIndex (.fvar channel)
    simp only [commBindingsAt] at application
    rw [applied] at application
    exact application
  let rawTarget := Pattern.collection .hashBag
    (semanticCommSubst (closeFVar 0 binder (encode continuation n v))
      (.apply "PDrop" [.fvar datum]) :: sourceResidue.map (fun p => encode p n v)) none
  have heads : Canonical.canonicalize
      (semanticCommSubst
        (Canonical.canonicalize (closeFVar 0 binder (encode continuation n v)))
        (.apply "PDrop" [.fvar datum])) =
      Canonical.canonicalize (semanticCommSubst (closeFVar 0 binder (encode continuation n v))
        (.apply "PDrop" [.fvar datum])) := by
    have commute := canonicalize_semanticCommSubst_canonicalize
      (close_encode_procWellSorted bodyFree binder n v) (close_encode_binderSafe bodyFree binder n v)
      (show HashSetFree (.apply "PDrop" [.fvar datum]) from ⟨trivial, trivial⟩)
    exact commute
  have tails : (bagContents (matcherResidue.map Canonical.canonicalize)).Perm
      (bagContents ((sourceResidue.map (fun p => encode p n v)).map Canonical.canonicalize)) := by
    have mapped := residuePermutation.symm.map Canonical.canonicalize
    have sameTails : (matcherResidue.map Canonical.canonicalize).Perm
        ((sourceResidue.map (fun p => encode p n v)).map Canonical.canonicalize) := by
      simpa only [original, sourceResidue, matcherResidue, List.eraseIdx_map,
        List.map_map, Function.comp_def, Canonical.canonicalize_idempotent] using mapped
    exact bagContents_perm sameTails
  have targetAgreement : Canonical.canonicalize target = Canonical.canonicalize rawTarget := by
    rw [exactTarget]
    exact canonicalize_bag_cons_congr heads tails
  let next := components (continuation.substitute binder datum) ++ sourceResidue
  have selected : NetworkStep processes next :=
    .comm i sourceInputBound j sourceOutputBound channel binder datum continuation sourceInput sourceOutput
  have rawEquations : rawTarget ≡ᵨ networkPattern next n v :=
    .trans _ _ _
      (bag_head_congr _ (contractum_equations bodyFree binder datum n v commSafe.1 commSafe.2))
      (release_equations (rf_substitute bodyFree binder datum) sourceResidueFlat n v)
  have rawPure : HashSetFree rawTarget :=
    ⟨hashSetFree_semanticCommSubst
        (rhoProcWellSorted_hashSetFree (close_encode_procWellSorted bodyFree binder n v))
        (show HashSetFree (.apply "PDrop" [.fvar datum]) from ⟨trivial, trivial⟩),
      list_encode_pure sourceResidueFlat n v⟩
  have endpoint := canonicalize_eq_of_structuralCongruence rawEquations rawPure
    (network_pure (selected.flat flat) n v)
  exact ⟨next, selected, targetAgreement.trans endpoint⟩

theorem canonical_firing_reflects {processes : List Process} (flat : Flat processes)
    (safe : Safe processes) (n v : String) {target : Pattern}
    (step : CanonicalFiring (canonicalNetwork processes n v) target) :
    ∃ next, NetworkStep processes next ∧ target = canonicalNetwork next n v := by
  obtain ⟨contractum, firing, rfl⟩ := step
  exact canonical_firing_contractum_reflects flat safe n v firing

/-- No deeper authored descent adds another execution in the compiled
canonical fragment. Thus the depth-one frontier used by `CanonicalFiring`
covers every contextual depth, with the supplied target unchanged. -/
theorem canonical_step_is_frontier {processes : List Process} (flat : Flat processes)
    (n v : String) {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (canonicalNetwork processes n v) target) :
    RhoStepAt 1 (canonicalNetwork processes n v) target := by
  cases fuel with
  | zero => cases step
  | succ fuel =>
      rcases rhoStepAt_succ_inv step with comm | parallel
      · obtain ⟨bindings, matched, applied⟩ := comm
        exact .rule (initialBindings := bindings) (finalBindings := bindings)
          rhoCommRewrite_mem matched (.nil _) applied
      · obtain ⟨elements, rest, index, indexBound, selected, sourceEq, inner, _⟩ := parallel
        let original := processes.map (fun p => Canonical.canonicalize (encode p n v))
        have originalNonbags : ∀ pattern ∈ original, ∀ elements rest,
            pattern ≠ .collection .hashBag elements rest := by
          intro pattern membership elements rest
          obtain ⟨process, member, rfl⟩ := List.mem_map.mp membership
          exact (atom_canonical_plain (flat process member) n v).2 elements rest
        have sortedNonbags : ∀ pattern ∈ sortPatterns original, ∀ elements rest,
            pattern ≠ .collection .hashBag elements rest := fun pattern membership =>
          originalNonbags pattern ((Canonical.sortPatterns_perm original).mem_iff.mpr membership)
        rw [canonicalNetwork_eq flat n v] at sourceEq
        obtain ⟨rfl, sortedEq⟩ := collapseBag_source sortedNonbags sourceEq
        have member : elements[index] ∈ sortPatterns original := by
          rw [sortedEq]
          exact List.getElem_mem indexBound
        exact False.elim (rho_nonbag_no_step (sortedNonbags elements[index] member) inner)

theorem canonical_authored_firing_reflects {processes : List Process} (flat : Flat processes)
    (safe : Safe processes) (n v : String) {fuel : Nat} {target : Pattern}
    (step : RhoStepAt fuel (canonicalNetwork processes n v) target) :
    ∃ next, NetworkStep processes next ∧ Canonical.canonicalize target = canonicalNetwork next n v :=
  canonical_firing_contractum_reflects flat safe n v (canonical_step_is_frontier flat n v step)

/-- The variable convention must hold at every reachable source prefix.
This is an independently stated source condition, not a target simulation
assumption. A one-step `Safe` hypothesis alone does not provide it. -/
def ReachableSafe (source : List Process) : Prop :=
  ∀ target, Relation.ReflTransGen NetworkStep source target → Safe target

theorem ReachableSafe.current {source : List Process} (safe : ReachableSafe source) :
    Safe source := safe source .refl

theorem ReachableSafe.after {source target : List Process} (safe : ReachableSafe source)
    (step : NetworkStep source target) : ReachableSafe target := by
  intro next path
  exact safe next ((Relation.ReflTransGen.single step).trans path)

theorem network_path_flat {source target : List Process}
    (path : Relation.ReflTransGen NetworkStep source target) (flat : Flat source) : Flat target := by
  induction path with
  | refl => exact flat
  | tail path step ih => exact step.flat ih

/-- Forward execution of every supplied source path, with the variable
convention checked at the source prefixes where each communication occurs. -/
theorem network_path_preserved {source target : List Process}
    (path : Relation.ReflTransGen NetworkStep source target)
    (flat : Flat source) (safe : ReachableSafe source) (n v : String) :
    Relation.ReflTransGen CanonicalFiring (canonicalNetwork source n v) (canonicalNetwork target n v) := by
  induction path with
  | refl => exact .refl
  | @tail middle target previous step ih =>
      exact ih.tail (step.canonical_firing (network_path_flat previous flat) (safe middle previous) n v)

/-- Reflection follows the actual supplied rho path and keeps its endpoint.
The image is closed at each prefix, so no separately chosen rho execution is
substituted for the path being reflected. -/
theorem canonical_path_reflects {source : List Process} (flat : Flat source)
    (safe : ReachableSafe source) (n v : String) {target : Pattern}
    (path : Relation.ReflTransGen CanonicalFiring (canonicalNetwork source n v) target) :
    ∃ next, Relation.ReflTransGen NetworkStep source next ∧ target = canonicalNetwork next n v := by
  generalize initialEq : canonicalNetwork source n v = initial at path
  induction path with
  | refl => exact ⟨source, .refl, initialEq.symm⟩
  | @tail middle target previous step ih =>
      obtain ⟨current, currentPath, middleEq⟩ := ih
      rw [middleEq] at step
      obtain ⟨next, selected, endpoint⟩ := canonical_firing_reflects
        (network_path_flat currentPath flat) (safe current currentPath) n v step
      exact ⟨next, currentPath.tail selected, endpoint⟩

/-- Two-sided finite-run correspondence for the existing compiler and rho
canonical runtime, including the actual supplied target state. -/
theorem canonical_path_iff {source : List Process} (flat : Flat source)
    (safe : ReachableSafe source) (n v : String) (target : Pattern) :
    Relation.ReflTransGen CanonicalFiring (canonicalNetwork source n v) target ↔
      ∃ next, Relation.ReflTransGen NetworkStep source next ∧ target = canonicalNetwork next n v := by
  constructor
  · exact canonical_path_reflects flat safe n v
  · rintro ⟨next, path, rfl⟩
    exact network_path_preserved path flat safe n v

/-- A finite parallel collection of sends, with no guarded receivers. -/
def SendsOnly : Process → Prop
  | .nil => True
  | .par first second => SendsOnly first ∧ SendsOnly second
  | .output _ _ => True
  | _ => False

private theorem sendsOnly_rf {process : Process} (sends : SendsOnly process) :
    RestrictionFree process := by
  induction process with
  | nil | output => trivial
  | par first second firstIH secondIH => exact ⟨firstIH sends.1, secondIH sends.2⟩
  | input | nu | replicate => exact False.elim sends

private theorem sendsOnly_convention {process : Process} (sends : SendsOnly process)
    (binder datum : Name) : BarendregtFor binder datum process := by
  induction process with
  | nil | output => trivial
  | par first second firstIH secondIH => exact ⟨firstIH sends.1, secondIH sends.2⟩
  | input | nu | replicate => exact False.elim sends

private def SendsAvoid (binder : Name) : Process → Prop
  | .nil => True
  | .par first second => SendsAvoid binder first ∧ SendsAvoid binder second
  | .output _ datum => datum ≠ binder
  | _ => False

private theorem sendsOnly_substitute_avoids {process : Process} (sends : SendsOnly process)
    (binder datum : Name) (different : datum ≠ binder) :
    SendsAvoid binder (process.substitute binder datum) := by
  induction process with
  | nil => simp [Process.substitute_nil, SendsAvoid]
  | par first second firstIH secondIH =>
      rw [Process.substitute_par]
      exact ⟨firstIH sends.1, secondIH sends.2⟩
  | output channel value =>
      by_cases equal : value = binder
      all_goals simp [Process.substitute_output, SendsAvoid, equal, different]
  | input | nu | replicate => exact False.elim sends

/-- Receivers share a binder and release only sends. Existing sends never
carry that binder as data. This concrete family has invariant source safety;
it is sufficient for genuine nonempty multi-step controls. -/
def OutputContinuationNetwork (binder : Name) (processes : List Process) : Prop :=
  ∀ process ∈ processes,
    match process with
    | .input _ bound body => bound = binder ∧ SendsOnly body
    | .output _ datum => datum ≠ binder
    | _ => False

private theorem sendsAvoid_components {body : Process} {binder : Name}
    (avoids : SendsAvoid binder body) : OutputContinuationNetwork binder (components body) := by
  induction body with
  | nil => intro process membership; simp [components] at membership
  | par first second firstIH secondIH =>
      intro process membership
      rcases List.mem_append.mp membership with fromFirst | fromSecond
      · exact firstIH avoids.1 process fromFirst
      · exact secondIH avoids.2 process fromSecond
  | output channel datum =>
      intro process membership
      obtain rfl := List.mem_singleton.mp membership
      exact avoids
  | input | nu | replicate => exact False.elim avoids

theorem OutputContinuationNetwork.flat {binder : Name} {processes : List Process}
    (network : OutputContinuationNetwork binder processes) : Flat processes := by
  intro process membership
  have property := network process membership
  cases process <;> simp only [Atom] <;> try exact False.elim property
  · exact sendsOnly_rf property.2

theorem OutputContinuationNetwork.safe {binder : Name} {processes : List Process}
    (network : OutputContinuationNetwork binder processes) : Safe processes := by
  intro channel bound datum body input output
  obtain ⟨rfl, sends⟩ := network (.input channel bound body) input
  exact ⟨(network (.output channel datum) output).symm, sendsOnly_convention sends bound datum⟩

theorem OutputContinuationNetwork.after {binder : Name} {source target : List Process}
    (network : OutputContinuationNetwork binder source) (step : NetworkStep source target) :
    OutputContinuationNetwork binder target := by
  cases step with
  | comm i hi j hj channel bound datum body input output =>
      have inputProperty := network source[i] (List.getElem_mem hi)
      rw [input] at inputProperty
      obtain ⟨rfl, sends⟩ := inputProperty
      have datumProperty := network (source.eraseIdx i)[j]
        (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [output] at datumProperty
      have released := sendsAvoid_components (sendsOnly_substitute_avoids sends bound datum datumProperty)
      intro process membership
      rcases List.mem_append.mp membership with fromBody | retained
      · exact released process fromBody
      · exact network process (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx retained))

theorem OutputContinuationNetwork.reachableSafe {binder : Name} {source : List Process}
    (network : OutputContinuationNetwork binder source) : ReachableSafe source := by
  intro target path
  have invariant : OutputContinuationNetwork binder target := by
    induction path with
    | refl => exact network
    | tail previous step ih => exact ih.after step
  exact invariant.safe

/-- A communication network whose variable convention is certified at all
reachable prefixes. The runtime comparison does not impose this certificate
on rho states outside the compiler's image. -/
def QualifiedNetwork := {processes : List Process // Flat processes ∧ ReachableSafe processes}

/-- The occurrence-bearing source transition system uses the existing named
network steps. Its equation carrier is discrete because occurrence order is
retained here; the compiler still uses rho's canonical equation section. -/
def networkSystem : Mettapedia.GSLT.GSLT where
  Term := QualifiedNetwork
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => NetworkStep source.val target.val
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- The actual authored firing followed by canonicalization is the runtime
transition. No additional source-indexed transition relation is introduced. -/
def canonicalRhoSystem : Mettapedia.GSLT.GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := CanonicalFiring
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

theorem canonical_zigzag (source : QualifiedNetwork) (n v : String) {target : Pattern}
    (step : canonicalRhoSystem.Step (canonicalNetwork source.val n v) target) :
    ∃ next : QualifiedNetwork, networkSystem.Step source next ∧
      target = canonicalNetwork next.val n v := by
  obtain ⟨next, selected, endpoint⟩ := canonical_firing_reflects
    source.property.1 source.property.2.current n v step
  exact ⟨⟨next, selected.flat source.property.1, source.property.2.after selected⟩, selected, endpoint⟩

/-- The established generic zig-zag theorem now transports source network
bisimilarity to the actual canonical rho runtime. -/
theorem bisimilar_canonical {source target : QualifiedNetwork}
    (equivalent : networkSystem.Bisimilar source target) (n v : String) :
    canonicalRhoSystem.Bisimilar (canonicalNetwork source.val n v) (canonicalNetwork target.val n v) := by
  apply Mettapedia.GSLT.GSLT.bisimilar_map_of_zigzag
    (source := networkSystem) (target := canonicalRhoSystem)
    (fun processes => canonicalNetwork processes.val n v) ?_ ?_ equivalent
  · intro first next selected
    exact selected.canonical_firing first.property.1 first.property.2.current n v
  · intro first target firing
    obtain ⟨next, selected, rfl⟩ := canonical_zigzag first n v firing
    exact ⟨next, selected, canonicalRhoSystem.bisimilar_refl _⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint
