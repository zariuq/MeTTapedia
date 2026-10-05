import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSourceInventory
import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironmentEvents

/-!
# Actual source authorization of matching unary actors

Faithful source references remain distinct from private definitions introduced
below the current source address. A lookup on a reference therefore identifies
that exact active source occurrence. Matching an environment listener then
constructs the existing one-shot or persistent fetch certificate independently
of any target endpoint or operational simulation premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchOwnership

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingActiveOrigins NamePassingSourceInventory
open ActiveMarkedNames
open ActiveMarking ActiveHeaderInvariant ScopedCommunicationInversion

universe u

/-- The supplied references are faithful and cannot alias a definition
authored at the current address or below it. -/
structure ReferenceDiscipline {Key : Type u} (binderKey : Origin → Key) {Γ : Ctx sig}
    (address : List Edge) (references : ReferenceKeys Key Γ) : Prop where
  faithful : Function.Injective references
  fresh : ∀ owner : List Edge, address.length ≤ owner.length →
    ∀ name : Var Γ Srt.nm, references name ≠ binderKey ⟨.privateReference, owner⟩

theorem ReferenceDiscipline.descend {Key : Type u} (binderKey : Origin → Key) {Γ : Ctx sig}
    {address : List Edge} {references : ReferenceKeys Key Γ}
    (discipline : ReferenceDiscipline binderKey address references) (edge : Edge) :
    ReferenceDiscipline binderKey (edge :: address) references :=
  ⟨discipline.faithful, fun owner deeper name => discipline.fresh owner (by simpa only [List.length_cons] using Nat.le_of_succ_le deeper) name⟩

theorem ReferenceDiscipline.definition {Key : Type u} (binderKey : Origin → Key)
    (keys : Function.Injective binderKey) {Γ : Ctx sig}
    {address : List Edge} {references : ReferenceKeys Key Γ}
    (discipline : ReferenceDiscipline binderKey address references) :
    ReferenceDiscipline binderKey (.definitionBody :: address)
      (ActiveMarkedNames.extend (binderKey ⟨.privateReference, address⟩) references) := by
  constructor
  · intro first second same
    cases first with
    | zero =>
        cases second with
        | zero => rfl
        | succ old => exact False.elim (discipline.fresh address (Nat.le_refl _) old same.symm)
    | succ first =>
        cases second with
        | zero => exact False.elim (discipline.fresh address (Nat.le_refl _) first same)
        | succ second => exact congrArg Var.succ (discipline.faithful same)
  · intro owner deeper name equal
    cases name with
    | zero =>
        have same := congrArg Origin.address (keys equal)
        have lengths := congrArg List.length same
        change address.length = owner.length at lengths
        simp only [List.length_cons] at deeper
        omega
    | succ old =>
        exact discipline.fresh owner (by simpa only [List.length_cons] using Nat.le_of_succ_le deeper) old equal

/-- A selected lookup actor yields the genuine capture-avoiding source
fetch certificate for the supplied reference and value. -/
theorem lookup_fetch {Key : Type u} (binderKey : Origin → Key)
    (keys : Function.Injective binderKey) {Γ : Ctx sig}
    (source : Expr Srt.nm Γ) (address : List Edge) (references : ReferenceKeys Key Γ)
    (discipline : ReferenceDiscipline binderKey address references)
    (result : Key) (origin : Origin) (fields : List Key)
    (name : Var Γ Srt.nm) (value : Expr Srt.nm Γ)
    (lookup : (⟨.output1, origin, references name, fields⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result) :
    ∃ target : Expr Srt.nm Γ, Nonempty (Environment.FetchCertificate name value source target) := by
  induction source generalizing address result with
  | var query =>
      simp only [inventory, Set.mem_singleton_iff, Observation.mk.injEq] at lookup
      have same := discipline.faithful lookup.2.2.1
      subst query
      exact ⟨value, ⟨.here name value⟩⟩
  | lam => simp [inventory, Observation.mk.injEq] at lookup
  | app function argument ih =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at lookup
      rcases lookup with inner | impossible
      · obtain ⟨target, ⟨selected⟩⟩ := ih (.function :: address) references
          (discipline.descend binderKey .function) _ name value inner
        exact ⟨.app target argument, ⟨.app argument selected⟩⟩
      · cases impossible.1
  | defn stored body storedIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at lookup
      rcases lookup with inner | impossible
      · obtain ⟨target, ⟨selected⟩⟩ := bodyIH (.definitionBody :: address) _
          (discipline.definition binderKey keys) result (.succ name)
          (Mettapedia.Languages.LambdaCalculus.NamePassing.weaken value) inner
        exact ⟨.defn stored target, ⟨.defn stored selected⟩⟩
      · cases impossible.1
  | carrier channel stored body storedIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at lookup
      rcases lookup with inner | impossible
      · obtain ⟨target, ⟨selected⟩⟩ := bodyIH (.carrierBody :: address) references
          (discipline.descend binderKey .carrierBody) result name value inner
        exact ⟨.carrier channel stored target, ⟨.carrier channel stored selected⟩⟩
      · cases impossible.1

/-- A matching pair of independently computed source actors authorizes a
real existing source event. The source itself determines whether its selected
declaration is consumed or persists. -/
theorem matching_unary_event {Key : Type u} (binderKey : Origin → Key)
    (keys : Function.Injective binderKey) {Γ : Ctx sig}
    (source : Expr Srt.nm Γ) (address : List Edge) (references : ReferenceKeys Key Γ)
    (discipline : ReferenceDiscipline binderKey address references)
    (result channel : Key) (fields : List Key) (input output : Origin)
    (listener : (⟨.input1, input, channel, []⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result)
    (sender : (⟨.output1, output, channel, fields⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result) :
    ∃ (kind : Environment.Action) (target : Expr Srt.nm Γ),
      kind ≠ .beta ∧ Nonempty (Environment.EventCertificate kind source target) := by
  induction source generalizing address result channel with
  | var => simp [inventory, Observation.mk.injEq] at listener
  | lam => simp [inventory, Observation.mk.injEq] at listener
  | app function argument ih =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at listener sender
      rcases listener with listener | impossible
      · rcases sender with sender | impossible
        · obtain ⟨kind, target, nonBeta, ⟨selected⟩⟩ := ih (.function :: address) references
            (discipline.descend binderKey .function) _ channel listener sender
          exact ⟨kind, .app target argument, nonBeta, ⟨.app argument selected⟩⟩
        · cases impossible.1
      · cases impossible.1
  | defn value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at listener sender
      rcases sender with sender | impossible
      · rcases listener with listener | definition
        · obtain ⟨kind, target, nonBeta, ⟨selected⟩⟩ := bodyIH (.definitionBody :: address) _
            (discipline.definition binderKey keys) result channel listener sender
          exact ⟨kind, .defn value target, nonBeta, ⟨.defn value selected⟩⟩
        · have same : channel = binderKey ⟨.privateReference, address⟩ := definition.2.2.1
          rw [same] at sender
          obtain ⟨target, ⟨selected⟩⟩ := lookup_fetch binderKey keys body (.definitionBody :: address) _
            (discipline.definition binderKey keys) result output fields .zero
            (Mettapedia.Languages.LambdaCalculus.NamePassing.weaken value) sender
          exact ⟨.environmentFetch, .defn value target,
            ⟨by decide, ⟨.environmentFetch value selected⟩⟩⟩
      · cases impossible.1
  | carrier name value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at listener sender
      rcases sender with sender | impossible
      · rcases listener with listener | declaration
        · obtain ⟨kind, target, nonBeta, ⟨selected⟩⟩ := bodyIH (.carrierBody :: address) references
            (discipline.descend binderKey .carrierBody) result channel listener sender
          exact ⟨kind, .carrier name value target, nonBeta, ⟨.carrier name value selected⟩⟩
        · have same : channel = references name := declaration.2.2.1
          rw [same] at sender
          obtain ⟨target, ⟨selected⟩⟩ := lookup_fetch binderKey keys body (.carrierBody :: address) references
            (discipline.descend binderKey .carrierBody) result output fields name value sender
          exact ⟨.carrierFetch, target, ⟨by decide, ⟨.carrierFetch name value selected⟩⟩⟩
      · cases impossible.1

/-- Actual compiler reference names instantiate the abstract discipline.
Private definition names occupy a disjoint constructor from all ambient
images, including when the source is open. -/
theorem physical_reference_discipline {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    (faithful : Function.Injective (ρ Srt.nm)) :
    ReferenceDiscipline (fun origin => (Sum.inr origin : Sum (Var Δ Srt.nm) Origin)) []
      (referenceKeys ρ (fun name => Sum.inl name)) := by
  constructor
  · intro first second equal
    exact faithful (Sum.inl.inj equal)
  · intro owner deeper name impossible
    cases impossible

/-- An arbitrary actual unary exposure of a faithfully compiled source
authorizes an existing one-shot or persistent source event. Its selected
constructor derivation is retained, independently of the still separate
supplied-target endpoint comparison. -/
theorem traced_unary_event {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (ρ : Ren sig Γ Δ) (faithful : Function.Injective (ρ Srt.nm)) (result : Var Δ Srt.nm)
    {target : Proc Δ} (exposure : Exposure (compile source ρ result) target)
    (traced : TracedExposure (NamePassingActiveOrigins.mark source []) exposure)
    (unary : inputHeader exposure.selected = .input1) :
    ∃ (kind : Environment.Action) (successor : Expr Srt.nm Γ),
      kind ≠ .beta ∧ Nonempty (Environment.EventCertificate kind source successor) := by
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
          exact matching_unary_event binderKey (fun _ _ equal => Sum.inr.inj equal) source []
            (referenceKeys ρ ambientKeys) discipline (ambientKeys result) _ _ _ _ listener sender

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchOwnership
