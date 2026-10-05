import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchOwnership

/-!
# The selected declaration and lookup belong to the same source event

The constructor addresses below are computed from the existing source
certificates. Matching independently computed source actors constructs a
certificate whose declaration and lookup are the supplied actors. The result
retains occurrence identity as well as source authorization; equal channels
and equal guard bodies do not identify distinct declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchSelected

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingActiveOrigins NamePassingSourceInventory NamePassingFetchOwnership
open ActiveMarkedNames
open ActiveMarking ActiveHeaderInvariant ScopedCommunicationInversion

universe u

/-- The lookup address follows the retained, independently authored fetch
derivation through its actual active contexts. -/
def lookupOrigin : {Γ : Ctx sig} → {name : Var Γ Srt.nm} →
    {value source target : Expr Srt.nm Γ} →
    Environment.FetchCertificate name value source target → List Edge → Origin
  | _, _, _, _, _, .here _ _, address => ⟨.lookup, address⟩
  | _, _, _, _, _, .app _ selected, address => lookupOrigin selected (.function :: address)
  | _, _, _, _, _, .defn _ selected, address => lookupOrigin selected (.definitionBody :: address)
  | _, _, _, _, _, .carrier _ _ selected, address => lookupOrigin selected (.carrierBody :: address)

def inputOrigin : {kind : Environment.Action} → {Γ : Ctx sig} →
    {source target : Expr Srt.nm Γ} → Environment.EventCertificate kind source target →
    List Edge → Origin
  | _, _, _, _, .beta _ _, address => ⟨.lambda, .function :: address⟩
  | _, _, _, _, .carrierFetch _ _ _, address => ⟨.carrier, address⟩
  | _, _, _, _, .environmentFetch _ _, address => ⟨.definition, address⟩
  | _, _, _, _, .app _ event, address => inputOrigin event (.function :: address)
  | _, _, _, _, .defn _ event, address => inputOrigin event (.definitionBody :: address)
  | _, _, _, _, .carrier _ _ event, address => inputOrigin event (.carrierBody :: address)

def outputOrigin : {kind : Environment.Action} → {Γ : Ctx sig} →
    {source target : Expr Srt.nm Γ} → Environment.EventCertificate kind source target →
    List Edge → Origin
  | _, _, _, _, .beta _ _, address => ⟨.application, address⟩
  | _, _, _, _, .carrierFetch _ _ selected, address => lookupOrigin selected (.carrierBody :: address)
  | _, _, _, _, .environmentFetch _ selected, address => lookupOrigin selected (.definitionBody :: address)
  | _, _, _, _, .app _ event, address => outputOrigin event (.function :: address)
  | _, _, _, _, .defn _ event, address => outputOrigin event (.definitionBody :: address)
  | _, _, _, _, .carrier _ _ event, address => outputOrigin event (.carrierBody :: address)

/-- The actual selected lookup supplies its own source certificate and
keeps precisely the actor's original constructor address. -/
theorem lookup_selected {Key : Type u} (binderKey : Origin → Key)
    (keys : Function.Injective binderKey) {Γ : Ctx sig}
    (source : Expr Srt.nm Γ) (address : List Edge) (references : ReferenceKeys Key Γ)
    (discipline : ReferenceDiscipline binderKey address references)
    (result : Key) (origin : Origin) (fields : List Key)
    (name : Var Γ Srt.nm) (value : Expr Srt.nm Γ)
    (lookup : (⟨.output1, origin, references name, fields⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result) :
    ∃ (target : Expr Srt.nm Γ) (selected : Environment.FetchCertificate name value source target),
      lookupOrigin selected address = origin := by
  induction source generalizing address result with
  | var query =>
      simp only [inventory, Set.mem_singleton_iff, Observation.mk.injEq] at lookup
      have same := discipline.faithful lookup.2.2.1
      subst query
      exact ⟨value, .here name value, lookup.2.1.symm⟩
  | lam => simp [inventory, Observation.mk.injEq] at lookup
  | app function argument ih =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at lookup
      rcases lookup with inner | impossible
      · obtain ⟨target, selected, origin⟩ := ih (.function :: address) references
          (discipline.descend binderKey .function) _ name value inner
        exact ⟨.app target argument, .app argument selected, origin⟩
      · cases impossible.1
  | defn stored body storedIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at lookup
      rcases lookup with inner | impossible
      · obtain ⟨target, selected, origin⟩ := bodyIH (.definitionBody :: address) _
          (discipline.definition binderKey keys) result (.succ name)
          (Mettapedia.Languages.LambdaCalculus.NamePassing.weaken value) inner
        exact ⟨.defn stored target, .defn stored selected, origin⟩
      · cases impossible.1
  | carrier channel stored body storedIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at lookup
      rcases lookup with inner | impossible
      · obtain ⟨target, selected, origin⟩ := bodyIH (.carrierBody :: address) references
          (discipline.descend binderKey .carrierBody) result name value inner
        exact ⟨.carrier channel stored target, .carrier channel stored selected, origin⟩
      · cases impossible.1

/-- Selected same-channel actors construct one genuine source event with
both selected addresses, even when other declarations have equal bodies. -/
theorem matching_selected_event {Key : Type u} (binderKey : Origin → Key)
    (keys : Function.Injective binderKey) {Γ : Ctx sig}
    (source : Expr Srt.nm Γ) (address : List Edge) (references : ReferenceKeys Key Γ)
    (discipline : ReferenceDiscipline binderKey address references)
    (result channel : Key) (fields : List Key) (input output : Origin)
    (listener : (⟨.input1, input, channel, []⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result)
    (sender : (⟨.output1, output, channel, fields⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result) :
    ∃ (kind : Environment.Action) (target : Expr Srt.nm Γ)
      (event : Environment.EventCertificate kind source target),
      kind ≠ .beta ∧ inputOrigin event address = input ∧ outputOrigin event address = output := by
  induction source generalizing address result channel with
  | var => simp [inventory, Observation.mk.injEq] at listener
  | lam => simp [inventory, Observation.mk.injEq] at listener
  | app function argument ih =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at listener sender
      rcases listener with listener | impossible
      · rcases sender with sender | impossible
        · obtain ⟨kind, target, event, nonBeta, input, output⟩ := ih (.function :: address) references
            (discipline.descend binderKey .function) _ channel listener sender
          exact ⟨kind, .app target argument, .app argument event, nonBeta, input, output⟩
        · cases impossible.1
      · cases impossible.1
  | defn value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at listener sender
      rcases sender with sender | impossible
      · rcases listener with listener | definition
        · obtain ⟨kind, target, event, nonBeta, input, output⟩ := bodyIH (.definitionBody :: address) _
            (discipline.definition binderKey keys) result channel listener sender
          exact ⟨kind, .defn value target, .defn value event, nonBeta, input, output⟩
        · have same : channel = binderKey ⟨.privateReference, address⟩ := definition.2.2.1
          rw [same] at sender
          obtain ⟨target, selected, origin⟩ := lookup_selected binderKey keys body (.definitionBody :: address) _
            (discipline.definition binderKey keys) result output fields .zero
            (Mettapedia.Languages.LambdaCalculus.NamePassing.weaken value) sender
          exact ⟨.environmentFetch, .defn value target, .environmentFetch value selected,
            by decide, definition.2.1.symm, origin⟩
      · cases impossible.1
  | carrier name value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at listener sender
      rcases sender with sender | impossible
      · rcases listener with listener | declaration
        · obtain ⟨kind, target, event, nonBeta, input, output⟩ := bodyIH (.carrierBody :: address) references
            (discipline.descend binderKey .carrierBody) result channel listener sender
          exact ⟨kind, .carrier name value target, .carrier name value event, nonBeta, input, output⟩
        · have same : channel = references name := declaration.2.2.1
          rw [same] at sender
          obtain ⟨target, selected, origin⟩ := lookup_selected binderKey keys body (.carrierBody :: address) references
            (discipline.descend binderKey .carrierBody) result output fields name value sender
          exact ⟨.carrierFetch, target, .carrierFetch name value selected,
            by decide, declaration.2.1.symm, origin⟩
      · cases impossible.1

/-- The arbitrary target's selected declaration and lookup are the exact
two origins of this retained source certificate. -/
theorem traced_selected_event {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (ρ : Ren sig Γ Δ) (faithful : Function.Injective (ρ Srt.nm)) (result : Var Δ Srt.nm)
    {target : Proc Δ} (exposure : Exposure (compile source ρ result) target)
    (traced : TracedExposure (NamePassingActiveOrigins.mark source []) exposure)
    (unary : inputHeader exposure.selected = .input1) :
    ∃ (kind : Environment.Action) (successor : Expr Srt.nm Γ)
      (event : Environment.EventCertificate kind source successor),
      kind ≠ .beta ∧ inputOrigin event [] = traced.continuation.inputOrigin ∧
        outputOrigin event [] = traced.continuation.outputOrigin := by
  let binderKey : Origin → Sum (Var Δ Srt.nm) Origin := Sum.inr
  let ambientKeys : ActiveMarkedNames.Environment (Sum (Var Δ Srt.nm) Origin) Δ := Sum.inl
  have listener := ActiveMarkedNames.traced_input_observed binderKey traced ambientKeys
  have sender := ActiveMarkedNames.traced_output_observed binderKey traced ambientKeys
  rw [compile_inventory] at listener sender
  have discipline := physical_reference_discipline ρ faithful
  rcases exposure with ⟨world, scope, redex, reduct, selected, frame, before, after⟩
  rcases traced with ⟨binders, redexMarks, frameMarks, continuation, frameFits, transportedFits,
    transport, originalInput, originalOutput⟩
  cases selected with
  | binary => cases unary
  | unary channel datum body =>
      cases continuation with
      | unary _ _ _ input output marked continuationFits =>
          exact matching_selected_event binderKey (fun _ _ equal => Sum.inr.inj equal) source []
            (referenceKeys ρ ambientKeys) discipline (ambientKeys result) _ _ _ _ listener sender

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchSelected
