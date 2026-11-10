import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EvidenceInterfaceFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EvidenceInterfaceNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SpacesInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PermissionsInterfaceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesRestriction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramHosts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullFibre
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullCount
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeInstance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGenericFirstOrder

/-!
# The feature × instance table of the one step

The calculus is one step, `Interface.Step` over `Interface.Frames`. This module states, for each
feature, the interface-level result and its instance at the **first-order** step
(`AnnotatedRuns.firstOrder`), the **contextual** steps over declaration frames (`Helpers.helperStep`,
the smallest one, and the native step `native` where the helper step lacks the feature), and the
**dependent full** step (`DependentFull.step`). Where a feature holds only on a restriction, the cell
names the restriction theorem, the separating control and the bridge.

| feature | interface | first-order | contextual | dependent full |
|---|---|---|---|---|
| frames and solutions | `Frames.Principal.models_iff` | `frames_firstOrder` | `frames_contextual` | `frames_dependent` |
| admission | `Interface.Step.admits_iff` | `admission_firstOrder` | `admission_helper`, `admission_native` | `admission_dependent` |
| runs | `Step.Run.models_start` | `runs_firstOrder` | `runs_helper`, `runs_native` | `runs_dependent` |
| the cut | `cut_preserved` | `cut_firstOrder` | `cut_helper`, `cut_native` | `cut_dependent` |
| guards | `holds_of_admitted` | `guards_firstOrder` | `guards_helper` | `guards_dependent` |
| predicate queries | `DependentFull.entails_absent_iff`, `Frames.Principal.entails_count_iff` | `absence_firstOrder`, `count_firstOrder` | `absence_contextual`, `count_contextual` (frames); the helper step has no queries; native: `admission_native` asks them | `absence_dependent`, `count_dependent` |
| spaces | `Spaces.run_executable`, `present_result_spaces` (any instance); independence: restriction `quiet` | `located_independent`, `located_static_independent`; bridge `exact_independent`; control `Spaces.Controls.shared_variable_crosses_spaces` | `spaces_helper`: no restriction (helper tells constrain only fresh helpers) | `dependent_independent`; control `SpacesInterface.Controls.dependent_shared_variable_crosses_spaces`; gap: located labels for queries |
| permissions | `refused_without_*`, `witness_present` (any instance); `absence_preserved` under `LabelLaw` | `old_owned_absence_preserved`, `old_owned_witness_present`; control `PermissionsInterface.Controls.relabel_spoils_absence` | `witness_helper`; absence: the helper step's rows carry no terms; native: gap | `dependent_absence_preserved`; controls `DependentControls.shared_absence_spoiled`, `owned_make_refused`, `owned_absence_survives` |
| disequations | `DisequalityFrames.frames`; `Interface.Step.withDisequations` over every step under `Reflects`, guards kept and asked at separating solutions | `oneFrame_admits_iff`; R92 controls | `diseq_helper`, `ContextualTell.control`; native: `diseq_native` (guarded native firings, `PreparedStep.nativeGuarded`); control `PreparedStep.Controls.control` | `diseq_dependent`, `DependentTell.control` |
| evidence rows | `not_admits_of_not_solvable`; `run_solvable` under `SettlesConservatively` (`RetractsSettlement` suffices) | `old_firstOrder_run_consistent`; `Evidence.Family.table` | `evidence_helper`, native `EvidenceInterface.Native.native_run_solvable`; four-way family: gap (the helper step has no reads or queries; native firings not built) | `dependent_run_solvable`; `EvidenceInterface.DependentFamily.table` |
| races and identity | `Race.Generic.bisimilar_of_same` | `races_firstOrder` | `races_helper` | `DependentFull.plain_bisimilar_of_same` (no helpers) |
| programs | gap: one core over the interface | R82, R89, R95 (first-order core) | R98, R100; joined by `step_join`, `absence_agrees`, `return_admitted_iff` | gap |

Restriction, separating control and bridge, for the features that do not hold on every instance:
* **spaces commute**: restriction `quiet` (`located_independent`, `dependent_independent`); control
  `shared_variable_crosses_spaces` and its dependent form; bridge `quiet_of_exact`, `exact_independent`
  (a syntactic condition a program checks), and `Controls.quiet_read_exact`;
* **absence under permissions**: restriction `LabelLaw` (`absence_preserved`); control
  `relabel_spoils_absence`; bridge `locatedLabels_law`, `dependentLabels_law`;
* **disequations**: restriction `Reflects` (`Interface.Step.withDisequations`, for every step); control
  `Restriction.guess_breaks_frame`, `guess_not_reflects`; bridge `firstOrder_reflects`,
  `Dependent.reflects`, `Contextual.reflects`, and for the native step, whose result is the solver's
  return, `PreparedStep.native_reflects` (`nativeGuarded`); control
  `PreparedStep.Controls.disequation_restriction_changes_guard`;
* **no run enters an inconsistent store**: restriction `SettlesConservatively` (`run_solvable`), with
  `RetractsSettlement` sufficient; control `EvidenceInterface.Controls.guess_enters_inconsistency`;
  bridge `firstOrder_retracts`, `dependent_retracts`, `helper_retracts`, `withDisequations_retracts`,
  and for the native step, whose settlement has no retraction, `Native.native_conservative`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InterfaceTable

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uOcc uS uF

/-! ## Interface-level statements -/

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)

/-- The admission condition of an explicitly guarded profile. -/
abbrev Admission [P.Guarded] {s : State} (f : Firing s) : Prop :=
  P.Shapes f ∧ Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
    X.Solvable (P.information f) ∧ X.Entails (P.information f) (P.Holds f)

/-- Knowledge refines along a run: every solution at its end pulls back to its start. -/
abbrev Refines {s : State} (r : P.Run s) : Prop :=
  ∀ (b : Obj) (σ : Hom (P.frame r.last) b), X.Models σ (P.knowledge r.last) →
    X.Models (X.comp σ r.toLast) (P.knowledge s)

/-- **The guards and predicate queries of an admitted firing hold at every solution of its
information.** -/
theorem holds_of_admitted [P.Guarded] {s : State} {f : Firing s} (admitted : P.Admits f) :
    X.Entails (P.information f) (P.Holds f) :=
  ((P.admits_iff f).mp admitted).2.2.2

/-- **Cut preservation**: what an admitted firing's guards and predicate queries answered at its cut
holds at every later solution. After any run from its result, every solution of the last knowledge,
read back to the firing's target frame, satisfies them. -/
theorem cut_preserved [P.Guarded] {s : State} {f : Firing s} (admitted : P.Admits f) (r : P.Run (P.result f admitted))
    {b : Obj} (τ : Hom (P.frame r.last) b) (solved : X.Models τ (P.knowledge r.last)) :
    P.Holds f b (X.comp (X.comp τ r.toLast) (P.settle f admitted)) := by
  have atResult := r.models_start τ solved
  exact holds_of_admitted P admitted b _ (P.result_refines f (P.prepares admitted) _ atResult)

end Generic

/-! ## The first-order step -/

section FirstOrder

universe uA uB uC

variable {T : Type uA} {S : Type uB} {O : Type uC} [DecidableEq O] (A : SubstitutionAction T S)
  (label : O → T)

theorem frames_firstOrder {store : EquationStore T} {answer : S}
    (principal : (Frames.ofSubstitution A).Principal (a := PUnit.unit) (m := PUnit.unit) store answer) (σ : S) :
    A.Models σ store ↔ ∃ residual : S, ∀ t, A.E (A.apply σ t) (A.apply (A.compose residual answer) t) :=
  Frames.Principal.models_iff principal (b := PUnit.unit) σ

theorem admission_firstOrder (C : Configuration T O) (f : AnnotatedRuns.Firing T S O) :
    (AnnotatedRuns.firstOrder A label).toStep.Admits (s := C) f ↔
      Admission (AnnotatedRuns.firstOrder A label).toStep (s := C) f :=
  (AnnotatedRuns.firstOrder A label).toStep.admits_iff f

theorem runs_firstOrder {C : Configuration T O} (r : (AnnotatedRuns.firstOrder A label).toStep.Run C) :
    Refines (AnnotatedRuns.firstOrder A label).toStep r :=
  fun _ σ solved => r.models_start σ solved

theorem cut_firstOrder {C : Configuration T O} {f : AnnotatedRuns.Firing T S O}
    (admitted : (AnnotatedRuns.firstOrder A label).toStep.Admits (s := C) f)
    (r : (AnnotatedRuns.firstOrder A label).toStep.Run ((AnnotatedRuns.firstOrder A label).toStep.result f admitted))
    (σ : S) (solved : A.Models σ r.last.equations) :
    (AnnotatedRuns.firstOrder A label).toStep.Holds (s := C) f PUnit.unit
      (A.compose (A.compose σ (Interface.Step.Run.toLast r)) A.identity) :=
  cut_preserved (AnnotatedRuns.firstOrder A label).toStep admitted r σ solved

theorem guards_firstOrder {C : Configuration T O} {f : AnnotatedRuns.Firing T S O}
    (admitted : (AnnotatedRuns.firstOrder A label).toStep.Admits (s := C) f) :
    (Frames.ofSubstitution A).Entails (a := PUnit.unit) ((AnnotatedRuns.firstOrder A label).toStep.information (s := C) f)
      ((AnnotatedRuns.firstOrder A label).toStep.Holds (s := C) f) :=
  holds_of_admitted _ admitted

omit [DecidableEq O] in
theorem absence_firstOrder {Occ : Type} (K : EquationStore T) (p : T) (present : Finset Occ) (row : Occ → T) :
    (Frames.ofSubstitution A).Entails (a := PUnit.unit) K
        (fun b τ => ∀ o ∈ present, ¬ (Frames.ofSubstitution A).E (a := b)
          ((Frames.ofSubstitution A).act (a := PUnit.unit) (b := b) τ p)
          ((Frames.ofSubstitution A).act (a := PUnit.unit) (b := b) τ (row o))) ↔
      ∀ o ∈ present, ¬ (Frames.ofSubstitution A).Solvable (a := PUnit.unit) (K ++ [(p, row o)]) :=
  Interface.DependentFull.entails_absent_iff (Frames.ofSubstitution A) K p present row

theorem count_firstOrder {K : EquationStore T} {answer : S}
    (principal : (Frames.ofSubstitution A).Principal (a := PUnit.unit) (m := PUnit.unit) K answer)
    (pattern : T) (present : Finset Nat) (row : Nat → T) (number : Nat) :
    (Frames.ofSubstitution A).Entails (a := PUnit.unit) K
        (fun b τ => ((Frames.ofSubstitution A).matchedAt (a := PUnit.unit) (b := b) τ pattern present
          row).card = number) ↔
      ((Frames.ofSubstitution A).matchedAt (a := PUnit.unit) (b := PUnit.unit) answer pattern present
          row).card = number ∧
        ∀ o ∈ present, o ∉ (Frames.ofSubstitution A).matchedAt (a := PUnit.unit) (b := PUnit.unit) answer
            pattern present row →
          ¬ (Frames.ofSubstitution A).Solvable (a := PUnit.unit) (K ++ [(pattern, row o)]) :=
  Interface.Frames.Principal.entails_count_iff principal pattern present row number

/-- Races: transport-equivalent configurations are bisimilar, for every program with invariant
labels. -/
theorem races_firstOrder {L : Type} (offers : L → (C : Configuration T O) → AnnotatedRuns.Firing T S O → Prop)
    (invariant : Race.Generic.Invariant (AnnotatedRuns.firstOrder A label).toStep offers
      (AnnotatedRuns.firstOrderTransport A label))
    {C D : Configuration T O} (same : (AnnotatedRuns.firstOrderTransport A label).Same C D) :
    Race.Generic.Bisimilar (AnnotatedRuns.firstOrder A label).toStep offers C D :=
  Race.Generic.bisimilar_of_same _ invariant same

end FirstOrder

/-! ## The contextual steps -/

section Contextual

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Helpers (helperStep helperTransport)

variable {S : Signature} {O : Type} [DecidableEq O]

theorem frames_contextual {F G M : Interface.Frames.Frame S}
    {store : EquationStore (Observation S F.arity)} {answer : Assignment F.arity M.arity}
    (principal : (Frames.contextual S).Principal store answer) (σ : Assignment F.arity G.arity) :
    (Frames.contextual S).Models σ store ↔ ∃ residual : Assignment M.arity G.arity,
      ∀ t, (Frames.contextual S).E ((Frames.contextual S).act σ t)
        ((Frames.contextual S).act ((Frames.contextual S).comp residual answer) t) :=
  Frames.Principal.models_iff principal σ

theorem admission_helper {s : Interface.Helpers.State S O} (f : Interface.Helpers.Firing s) :
    helperStep.Admits f ↔ Admission helperStep.toStep f :=
  helperStep.admits_iff f

theorem runs_helper {s : Interface.Helpers.State S O} (r : (helperStep (S := S) (O := O)).Run s) :
    Refines helperStep.toStep r :=
  fun _ σ solved => r.models_start σ solved

theorem cut_helper {s : Interface.Helpers.State S O} {f : Interface.Helpers.Firing s}
    (admitted : helperStep.Admits f) (r : (helperStep (S := S) (O := O)).Run (helperStep.result f admitted))
    {b : Interface.Frames.Frame S} (τ : Assignment (helperStep.frame r.last).arity b.arity)
    (solved : (Frames.contextual S).Models τ (helperStep.knowledge r.last)) :
    helperStep.Holds f b ((Frames.contextual S).comp ((Frames.contextual S).comp τ r.toLast)
      (helperStep.settle f admitted)) :=
  cut_preserved helperStep.toStep admitted r τ solved

theorem guards_helper {s : Interface.Helpers.State S O} {f : Interface.Helpers.Firing s}
    (admitted : helperStep.Admits f) :
    (Frames.contextual S).Entails (helperStep.information f) (helperStep.Holds f) :=
  holds_of_admitted _ admitted

omit [DecidableEq O] in
theorem absence_contextual {F : Interface.Frames.Frame S} (K : EquationStore (Observation S F.arity))
    (p : Observation S F.arity) (present : Finset O) (row : O → Observation S F.arity) :
    (Frames.contextual S).Entails K
        (fun _ τ => ∀ o ∈ present, ¬ (Frames.contextual S).E ((Frames.contextual S).act τ p)
          ((Frames.contextual S).act τ (row o))) ↔
      ∀ o ∈ present, ¬ (Frames.contextual S).Solvable (K ++ [(p, row o)]) :=
  Interface.DependentFull.entails_absent_iff (Frames.contextual S) K p present row

theorem count_contextual {F M : Interface.Frames.Frame S} {K : EquationStore (Observation S F.arity)}
    {answer : Assignment F.arity M.arity} (principal : (Frames.contextual S).Principal K answer)
    (pattern : Observation S F.arity) (present : Finset Nat) (row : Nat → Observation S F.arity)
    (number : Nat) :
    (Frames.contextual S).Entails K
        (fun _ τ => ((Frames.contextual S).matchedAt τ pattern present row).card = number) ↔
      ((Frames.contextual S).matchedAt answer pattern present row).card = number ∧
        ∀ o ∈ present, o ∉ (Frames.contextual S).matchedAt answer pattern present row →
          ¬ (Frames.contextual S).Solvable (K ++ [(pattern, row o)]) :=
  Interface.Frames.Principal.entails_count_iff principal pattern present row number

/-- **Spaces at the helper step need no restriction**: two helper firings that make their occurrences
at different spaces are independent exactly when the knowledge is solvable, the occurrences are fresh
and both firings' guards are asked by the knowledge. Helper tells constrain only fresh helpers, so
`quiet` always holds there. -/
theorem spaces_helper {H : Type} (space : O → H) {s : Interface.Helpers.State S O}
    {f g : Interface.Helpers.Firing s} (different : space f.made ≠ space g.made) :
    (helperTransport (S := S) (O := O)).Independent s f g ↔
      (Frames.contextual S).Solvable s.knowledge ∧ f.made ∉ s.present ∧ g.made ∉ s.present ∧
        (Frames.contextual S).Entails s.knowledge (fun _ σ => (Frames.contextual S).Models σ f.guards) ∧
        (Frames.contextual S).Entails s.knowledge (fun _ σ => (Frames.contextual S).Models σ g.guards) := by
  rw [Interface.Helpers.independent_iff]
  constructor
  · rintro ⟨solvable, freshF, freshG, -, guardsF, guardsG⟩
    exact ⟨solvable, freshF, freshG, guardsF, guardsG⟩
  · rintro ⟨solvable, freshF, freshG, guardsF, guardsG⟩
    exact ⟨solvable, freshF, freshG, fun same => different (congrArg space same), guardsF, guardsG⟩

/-- Permissions at the helper step: a witness without `receive` survives every permitted firing. -/
theorem witness_helper {H : Type} (space : O → H) (Γ : MeTTaCalculus.InteractionTypes.Rights H)
    {s : Interface.Helpers.State S O} {f : Interface.Helpers.Firing s} (admitted : helperStep.Admits f)
    (formed : Permissions.Permitted helperStep.toStep space Γ f) {o : O} (present : o ∈ s.present)
    (owned : Γ (space o) .receive = false) : o ∈ (helperStep.result f admitted).present :=
  PermissionsInterface.witness_present helperStep.toStep space Γ admitted formed present owned

theorem diseq_helper {s : (DisequalityFrames.Contextual.prestep S O).step.DState}
    (f : (DisequalityFrames.Contextual.prestep S O).step.DFiring s) :
    (DisequalityFrames.Contextual.withDisequations S O).Admits f ↔
      Admission (DisequalityFrames.Contextual.withDisequations S O) f :=
  (DisequalityFrames.Contextual.withDisequations S O).admits_iff f

/-- Evidence at the helper step: no run from solvable knowledge enters an inconsistent store. -/
theorem evidence_helper {s : Interface.Helpers.State S O} (r : (helperStep (S := S) (O := O)).Run s)
    (solvable : (Frames.contextual S).Solvable s.knowledge) :
    (Frames.contextual S).Solvable r.last.knowledge :=
  EvidenceInterface.run_solvable (EvidenceInterface.conservative_of_retracts EvidenceInterface.helper_retracts)
    r solvable

theorem races_helper {L : Type}
    (offers : L → (s : Interface.Helpers.State S O) → Interface.Helpers.Firing s → Prop)
    (invariant : Race.Generic.Invariant helperStep.toStep offers helperTransport)
    {s t : Interface.Helpers.State S O} (same : (helperTransport (S := S) (O := O)).Same s t) :
    Race.Generic.Bisimilar helperStep.toStep offers s t :=
  Race.Generic.bisimilar_of_same _ invariant same

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {Γ : Ctx S} {sort : S.Srt}

theorem admission_native {s : Interface.NativeState S O Γ sort} (f : Interface.NativeFiring s) :
    (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).Admits f ↔ Admission Interface.native.toStep f :=
  Interface.native.admits_iff f

theorem runs_native {s : Interface.NativeState S O Γ sort}
    (r : (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).Run s) :
    Refines Interface.native.toStep r :=
  fun _ σ solved => r.models_start σ solved

theorem cut_native {s : Interface.NativeState S O Γ sort} {f : Interface.NativeFiring s}
    (admitted : (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).Admits f)
    (r : (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).Run (Interface.native.result f admitted))
    {b : Interface.Frames.Frame S} (τ : Assignment (Interface.native.frame r.last).arity b.arity)
    (solved : (Frames.contextual S).Models τ (Interface.native.knowledge r.last)) :
    Interface.native.Holds f b ((Frames.contextual S).comp ((Frames.contextual S).comp τ r.toLast)
      (Interface.native.settle f admitted)) :=
  cut_preserved Interface.native.toStep admitted r τ solved

theorem diseq_native {s : (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).DState}
    (f : Interface.native.DFiring s) :
    (PreparedStep.nativeGuarded S O Γ sort).Admits f ↔ Admission (PreparedStep.nativeGuarded S O Γ sort) f :=
  (PreparedStep.nativeGuarded S O Γ sort).admits_iff f

theorem evidence_native {s : Interface.NativeState S O Γ sort}
    (r : (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).Run s)
    (solvable : (Frames.contextual S).Solvable (Interface.native.knowledge s)) :
    (Frames.contextual S).Solvable (Interface.native.knowledge r.last) :=
  EvidenceInterface.Native.native_run_solvable r solvable

end Contextual

/-! ## The dependent full step -/

section Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open Interface.DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  (levels : LevelModel rules L) (O : Type) [DecidableEq O]

theorem frames_dependent {Γ Δ M : Context rules} {store : EquationStore (TotalTerm Γ)} {answer : M ⟶ Γ}
    (principal : (ContextualDependentEta.frames levels).Principal store answer) (σ : Δ ⟶ Γ) :
    (ContextualDependentEta.frames levels).Models σ store ↔ ∃ residual : Δ ⟶ M,
      ∀ t, (ContextualDependentEta.frames levels).E ((ContextualDependentEta.frames levels).act σ t)
        ((ContextualDependentEta.frames levels).act ((ContextualDependentEta.frames levels).comp residual answer) t) :=
  Frames.Principal.models_iff principal σ

theorem admission_dependent {s : State rules O} (f : Firing levels s) :
    (step levels O).toStep.Admits f ↔ Admission (step levels O).toStep f :=
  (step levels O).toStep.admits_iff f

theorem runs_dependent {s : State rules O} (r : (step levels O).toStep.Run s) : Refines (step levels O).toStep r :=
  fun _ σ solved => r.models_start σ solved

theorem cut_dependent {s : State rules O} {f : Firing levels s} (admitted : (step levels O).toStep.Admits f)
    (r : (step levels O).toStep.Run ((step levels O).toStep.result f admitted)) {b : Context rules}
    (τ : b ⟶ r.last.frame) (solved : (ContextualDependentEta.frames levels).Models τ r.last.knowledge) :
    (step levels O).toStep.Holds f b ((ContextualDependentEta.frames levels).comp
      ((ContextualDependentEta.frames levels).comp τ r.toLast) ((step levels O).toStep.settle f admitted)) :=
  cut_preserved (step levels O).toStep admitted r τ solved

theorem guards_dependent {s : State rules O} {f : Firing levels s} (admitted : (step levels O).toStep.Admits f) :
    (ContextualDependentEta.frames levels).Entails f.information (fun _ τ => f.Holds τ) :=
  holds_of_admitted (step levels O).toStep admitted

omit [DecidableEq O] in
theorem absence_dependent {Δ : Context rules} (K : EquationStore (TotalTerm Δ)) (p : TotalTerm Δ)
    (present : Finset O) (row : O → TotalTerm Δ) :
    (ContextualDependentEta.frames levels).Entails K
        (fun _ τ => ∀ o ∈ present, ¬ (ContextualDependentEta.frames levels).E
          ((ContextualDependentEta.frames levels).act τ p) ((ContextualDependentEta.frames levels).act τ (row o))) ↔
      ∀ o ∈ present, ¬ (ContextualDependentEta.frames levels).Solvable (K ++ [(p, row o)]) :=
  entails_absent_iff (ContextualDependentEta.frames levels) K p present row

theorem count_dependent {Δ M : Context rules} {K : EquationStore (TotalTerm Δ)} {answer : M ⟶ Δ}
    (principal : (ContextualDependentEta.frames levels).Principal K answer) (pattern : TotalTerm Δ)
    (present : Finset Nat) (row : Nat → TotalTerm Δ) (number : Nat) :
    (ContextualDependentEta.frames levels).Entails K
        (fun _ τ => ((ContextualDependentEta.frames levels).matchedAt τ pattern present row).card = number) ↔
      ((ContextualDependentEta.frames levels).matchedAt answer pattern present row).card = number ∧
        ∀ o ∈ present, o ∉ (ContextualDependentEta.frames levels).matchedAt answer pattern present row →
          ¬ (ContextualDependentEta.frames levels).Solvable (K ++ [(pattern, row o)]) :=
  Interface.Frames.Principal.entails_count_iff principal pattern present row number

theorem diseq_dependent {s : (DisequalityFrames.Dependent.prestep levels O).step.DState}
    (f : (DisequalityFrames.Dependent.prestep levels O).step.DFiring s) :
    (DisequalityFrames.Dependent.withDisequations levels O).Admits f ↔
      Admission (DisequalityFrames.Dependent.withDisequations levels O) f :=
  (DisequalityFrames.Dependent.withDisequations levels O).admits_iff f

end Dependent

#print axioms holds_of_admitted
#print axioms cut_preserved
#print axioms frames_firstOrder
#print axioms admission_firstOrder
#print axioms runs_firstOrder
#print axioms cut_firstOrder
#print axioms guards_firstOrder
#print axioms absence_firstOrder
#print axioms count_firstOrder
#print axioms races_firstOrder
#print axioms frames_contextual
#print axioms admission_helper
#print axioms runs_helper
#print axioms cut_helper
#print axioms guards_helper
#print axioms absence_contextual
#print axioms count_contextual
#print axioms spaces_helper
#print axioms witness_helper
#print axioms diseq_helper
#print axioms evidence_helper
#print axioms races_helper
#print axioms admission_native
#print axioms runs_native
#print axioms cut_native
#print axioms diseq_native
#print axioms evidence_native
#print axioms frames_dependent
#print axioms admission_dependent
#print axioms runs_dependent
#print axioms cut_dependent
#print axioms guards_dependent
#print axioms absence_dependent
#print axioms count_dependent
#print axioms diseq_dependent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InterfaceTable
