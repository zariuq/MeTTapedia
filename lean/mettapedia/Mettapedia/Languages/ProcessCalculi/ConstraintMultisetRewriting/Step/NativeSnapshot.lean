import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeClosingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidualExample

/-!
# When reusable snapshots commute

A reusable output is published as a **snapshot**: its row matches exactly the source instances of
the output under the information at publication (`ContextualConditionalExecution.Firing.ordinary_matches_source`),
and it keeps that meaning at every later state (`NativeClosingControls.snapshot_retained`). So in the
order `g` then `h`, the snapshot of `g`'s output means the instances under `g`'s information; in the
order `h` then `g`, it means the instances under the information of `g` read after `h`.

## The condition

**`h` is conservative over `g`** (`Conservative`) when every solution of `g`'s information extends, in the
same frame, to a solution of `h`'s information that agrees with it on the state's names: `h` constrains
no name of the state beyond what `g` already knows.

* **Reading after a step only removes instances** (`instances_of_after`): every instance of a carried
  output under the residual's information is an instance under the firing's own.
* **Under conservativity it removes none** (`instances_after_iff`): every solution of `g`'s
  information amalgamates with `h`'s into a solution of the residual's information, at a frame with
  fresh names for the residual's dead names (`amalgamWide`), so no inhabitant is assumed.
* **So the snapshots commute** (`snapshots_commute`): the row a reusable output holds after `g` then `h`
  and the row it holds after `h` then `g` match the same patterns at every candidate.

## The obstruction

Without conservativity the snapshots need not commute (`snapshot_obstruction`): at the state with one
name `X`, a firing whose output is `X` and tells nothing has the instance `X = false`; read after the
teller of `X = true` it does not. Telling `X = true` is not conservative over the empty information
(`teller_not_conservative`), while a firing that tells nothing is conservative over every information
(`conservative_of_nil`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open NativeResidual
open ContextualPrefixModels (inclusion extended)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeSnapshot

variable {s : NativeState S O Γ sort}

/-- **One information is conservative over another**: every solution of the second extends, in the
same frame, to a solution of the first that agrees with it on the state's names. -/
def Conservative (s : NativeState S O Γ sort)
    (constraining base : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)) : Prop :=
  ∀ {W : Type} (next : W → MetaArity S) (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) next),
    ContextualResidual.Models σ base →
      ∃ τ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) next,
        ContextualResidual.Models τ constraining ∧
          Assignment.compose τ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
            Assignment.compose σ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **An empty information is conservative over every information.** -/
theorem conservative_of_nil
    (base : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)) :
    Conservative s [] base :=
  fun _ σ _ => ⟨σ, fun _ member => absurd member List.not_mem_nil, rfl⟩

section Amalgam

variable (G : ContextualConditionalExecution.Firing s.locals s.state)

/-- **Amalgamation at a wider frame**: the carried rule locals read the first solution, the published
frame the second, and the residual's dead names go to fresh names of the wider frame. -/
def amalgamWide {W : Type} {next : W → MetaArity S}
    (σ τ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) next) :
    Assignment (laterTarget G) (extended (laterTarget G) next)
  | .inl ⟨scope, .inl name⟩ => instantiate (inclusion (laterTarget G) next) (σ (.inl ⟨scope - shift G, name⟩))
  | .inl ⟨scope, .inr helper⟩ => generator (extended (laterTarget G) next) (.inl (.inl ⟨scope, .inr helper⟩))
  | .inr (.inl name) => instantiate (inclusion (laterTarget G) next) (τ name)
  | .inr (.inr helper) => generator (extended (laterTarget G) next) (.inl (.inr (.inr helper)))

theorem amalgamWide_carry {W : Type} {next : W → MetaArity S}
    (σ τ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) next)
    (agree : Assignment.compose τ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
      Assignment.compose σ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)) :
    Assignment.compose (amalgamWide G σ τ) (carry G) = Assignment.compose (inclusion (laterTarget G) next) σ := by
  funext name
  cases name with
  | inl name =>
      refine (instantiate_generator (amalgamWide G σ τ) (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name)))).trans ?_
      show instantiate (inclusion (laterTarget G) next) (σ (.inl ⟨name.scope + shift G - shift G, name.name⟩)) =
        instantiate (inclusion (laterTarget G) next) (σ (.inl name))
      rw [Nat.add_sub_cancel]
  | inr name =>
      have atName : τ (.inr name) = σ (.inr name) :=
        (instantiate_generator τ (.inr name)).symm.trans ((congrFun agree name).trans (instantiate_generator σ (.inr name)))
      exact (instantiate_generator (amalgamWide G σ τ) (.inr (.inl (.inr name)))).trans
        (congrArg (instantiate (inclusion (laterTarget G) next)) atName)

theorem amalgamWide_published {W : Type} {next : W → MetaArity S}
    (σ τ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) next) :
    Assignment.compose (Assignment.compose (amalgamWide G σ τ) (laterCaptured G))
        (ContextualComputedFreshFrame.includeSource G.update) =
      Assignment.compose (inclusion (laterTarget G) next) τ := by
  funext name
  exact (congrArg (instantiate (Assignment.compose (amalgamWide G σ τ) (laterCaptured G))) (includeSource_apply G name)).trans
    ((instantiate_generator (Assignment.compose (amalgamWide G σ τ) (laterCaptured G)) (.inl name)).trans
      (instantiate_generator (amalgamWide G σ τ) (.inr (.inl name))))

end Amalgam

/-- The extension of a pattern's frame by the residual's names. -/
def wideExtension (G : ContextualConditionalExecution.Firing s.locals s.state) {W : Type} {next : W → MetaArity S}
    (extension : ContextualGuardMatching.Extension next) : ContextualGuardMatching.Extension next :=
  ⟨_, extended (laterTarget G) extension.declarations, fun name => .inr (extension.name name),
    Sum.inr_injective.comp extension.injective, extension.preserves⟩

theorem wideExtension_assignment (G : ContextualConditionalExecution.Firing s.locals s.state) {W : Type}
    {next : W → MetaArity S} (extension : ContextualGuardMatching.Extension next) :
    (wideExtension G extension).assignment =
      Assignment.compose (inclusion (laterTarget G) extension.declarations) extension.assignment := by
  funext name
  show castMetaBody _ (generator _ _) =
    instantiate (inclusion (laterTarget G) extension.declarations) (castMetaBody _ (generator _ _))
  rw [instantiate_castMetaBody, instantiate_generator]
  rfl

/-- **Reading after a step only removes instances**: every instance of a carried output under the
residual's information is an instance of the output under the firing's own information. -/
theorem instances_of_after (G : ContextualConditionalExecution.Firing s.locals s.state) (g : LiveFiring s)
    (unmade : ∀ o ∈ g.selection.taken ++ g.selection.read, o ∉ G.selection.made)
    (output : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)
    {W : Type} (next : W → MetaArity S) (pattern : Term (signature S next) Γ sort)
    (after : ContextualPublication.SourceInstances (g.residualAt G).toNative.information
      (instantiate (carry G) output) next pattern) :
    ContextualPublication.SourceInstances g.toNative.information output next pattern := by
  obtain ⟨extension, ρ, solved, same⟩ := after
  exact ⟨extension, Assignment.compose ρ (carry G), (Joint.ofResidual (b := ⟨extension.Names, extension.declarations⟩) G g unmade ρ solved).left_models,
    (Assignment.instantiate_compose ρ (carry G) output).trans same⟩

/-- **Under conservativity, reading after a step removes no instance.** -/
theorem instances_after_iff (G : ContextualConditionalExecution.Firing s.locals s.state) (g : LiveFiring s)
    (unmade : ∀ o ∈ g.selection.taken ++ g.selection.read, o ∉ G.selection.made)
    (conservative : Conservative s (problemOf s G.selection G.rule) g.toNative.information)
    (output : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)
    {W : Type} (next : W → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (g.residualAt G).toNative.information (instantiate (carry G) output) next pattern ↔
      ContextualPublication.SourceInstances g.toNative.information output next pattern := by
  refine ⟨instances_of_after G g unmade output next pattern, ?_⟩
  rintro ⟨extension, σ, solved, same⟩
  obtain ⟨τ, solvedG, agree⟩ := conservative extension.declarations σ solved
  refine ⟨wideExtension G extension, amalgamWide G σ τ, ?_, ?_⟩
  · refine (residual_models_iff G g unmade (amalgamWide G σ τ)).mpr ⟨?_, ?_⟩
    · rw [amalgamWide_published]
      exact models_compose_left _ solvedG
    · rw [amalgamWide_carry G σ τ agree]
      exact models_compose_left _ ((models_problemOf_iff g.selection g.rule σ).mp solved).2
  · exact ((Assignment.instantiate_compose (amalgamWide G σ τ) (carry G) output).symm.trans
      ((congrArg (fun assignment => instantiate assignment output) (amalgamWide_carry G σ τ agree)).trans
        ((Assignment.instantiate_compose (inclusion (laterTarget G) extension.declarations) σ output).trans
          ((congrArg (instantiate (inclusion (laterTarget G) extension.declarations)) same).trans
            ((Assignment.instantiate_compose (inclusion (laterTarget G) extension.declarations)
              extension.assignment pattern).symm.trans
              (congrArg (fun assignment => instantiate assignment pattern) (wideExtension_assignment G extension)).symm)))))

/-- **Reusable snapshots commute under conservativity.** For a reusable output `o` of `g`, the row it
holds after `g` then `h` (any later execution `H'` that does not remake it) and the row it holds after
`h` then `g` (an execution `G'` of `g` read after `h`'s execution `H`) match the same patterns at every
candidate, when `h`'s information is conservative over `g`'s. -/
theorem snapshots_commute (G H : ContextualConditionalExecution.Firing s.locals s.state) (g : LiveFiring s)
    (runs : G.rule = g.rule ∧ G.selection = g.selection ∧ G.outputs = g.outputs)
    (H' : ContextualConditionalExecution.Firing (rawTarget G).locals (rawTarget G).state)
    (G' : ContextualConditionalExecution.Firing (rawTarget H).locals (rawTarget H).state)
    (runs' : G'.rule = (g.residualAt H).rule ∧ G'.selection = g.selection ∧ G'.outputs = (g.residualAt H).outputs)
    {o : O} (made : o ∈ g.selection.made) (reusable : G.reusable o = true) (reusable' : G'.reusable o = true)
    (notMade : o ∉ H'.selection.made)
    (unmade : ∀ x ∈ g.selection.taken ++ g.selection.read, x ∉ H.selection.made)
    (conservative : Conservative s (problemOf s H.selection H.rule) g.toNative.information)
    {W : Type} (next : W → MetaArity S) (first : Assignment H'.target.declarations next)
    (second : Assignment G'.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    ContextualConditionalRows.Matches (rawTarget H').locals H'.target.declarations first pattern (H'.target.rows o) ↔
      ContextualConditionalRows.Matches (ContextualPublication.privateFamily (rawTarget H).locals G'.update.declaration)
        G'.target.declarations second pattern (G'.target.rows o) := by
  obtain ⟨rule, selection, outputs⟩ := runs
  obtain ⟨rule', selection', outputs'⟩ := runs'
  have madeG : o ∈ G.selection.made := by rw [selection]; exact made
  have madeG' : o ∈ G'.selection.made := by rw [selection']; exact made
  have before : ContextualPublication.SourceInstances (problemOf s G.selection G.rule) (G.outputs o) next pattern ↔
      ContextualPublication.SourceInstances g.toNative.information (g.outputs o) next pattern := by
    rw [rule, selection, outputs]
    exact Iff.rfl
  have after : ContextualPublication.SourceInstances
      (ContextualConditionalExecution.information (rawTarget H).locals (rawTarget H).state.declarations
        (rawTarget H).state.occupied G'.selection G'.rule (rawTarget H).state.rows (rawTarget H).state.equations)
      (G'.outputs o) next pattern ↔
      ContextualPublication.SourceInstances (g.residualAt H).toNative.information
        (instantiate (carry H) (g.outputs o)) next pattern := by
    rw [rule', selection', outputs']
    exact Iff.rfl
  exact (NativeClosingControls.snapshot_retained G H' madeG reusable notMade first pattern).trans
    (before.trans ((instances_after_iff H g unmade conservative (g.outputs o) next pattern).symm.trans
      (after.symm.trans (G'.ordinary_matches_source o madeG' reusable' next second pattern).symm)))

/-! ## The obstruction -/

section Obstruction

open NativeResidualExample (tiny noLocals oneName bit initial maker maker_realized told_value)

/-- The state's name, as an output. -/
def nameOutput : Term (signature tiny (ContextualActivatedStep.target noLocals oneName)) ([] : Ctx tiny) () :=
  generator (ContextualActivatedStep.target noLocals oneName) (.inr ())

/-- A firing that makes the occurrence `5` with output `X` and tells nothing. -/
def reader : LiveFiring initial where
  rule := ⟨[], [], [], [], [generator (ContextualActivatedStep.source noLocals oneName) (.inr ())]⟩
  selection := ⟨[], [], [5]⟩
  outputs _ := nameOutput
  patterns := []
  fuel := 0

/-- The execution of the teller of `X = true`. -/
noncomputable abbrev tellerTrue : ContextualConditionalExecution.Firing initial.locals initial.state :=
  LiveFiring.execution (maker_realized 1 (some true))

theorem tellerTrue_problem :
    problemOf initial tellerTrue.selection tellerTrue.rule = (maker 1 (some true)).toNative.information := by
  rw [(LiveFiring.execution_data (maker_realized 1 (some true))).1,
    (LiveFiring.execution_data (maker_realized 1 (some true))).2.1]
  rfl

/-- A frame with no names. -/
def emptyFrame : Empty → MetaArity tiny := fun impossible => nomatch impossible

/-- A candidate giving `X` the value `false`, into a frame with no names. -/
def falseCandidate :
    Assignment (ContextualActivatedStep.target noLocals oneName) emptyFrame
  | .inl local_ => nomatch local_.name
  | .inr () => bit _ false

/-- **The snapshot obstruction**: before the teller of `X = true`, `X = false` is an instance of the
reader's output; read after the teller, it is not. -/
theorem snapshot_obstruction :
    ContextualPublication.SourceInstances reader.toNative.information nameOutput emptyFrame
        (bit _ false) ∧
      ¬ ContextualPublication.SourceInstances (reader.residualAt tellerTrue).toNative.information
        (instantiate (carry tellerTrue) nameOutput) emptyFrame (bit _ false) := by
  constructor
  · refine ⟨ContextualGuardMatching.Extension.identity _, falseCandidate,
      fun _ member => absurd member List.not_mem_nil, ?_⟩
    exact (instantiate_generator falseCandidate (.inr ())).trans rfl
  · rintro ⟨extension, ρ, solved, same⟩
    have unmade : ∀ o ∈ reader.selection.taken ++ reader.selection.read, o ∉ tellerTrue.selection.made :=
      fun _ member => absurd member List.not_mem_nil
    have rightModels : ContextualResidual.Models
        (Assignment.compose (Assignment.compose ρ (laterCaptured tellerTrue))
          (ContextualComputedFreshFrame.includeSource tellerTrue.update))
        (maker 1 (some true)).toNative.information :=
      Eq.mp (congrArg (ContextualResidual.Models _) tellerTrue_problem)
        ((residual_models_iff tellerTrue reader unmade ρ).mp solved).1
    have told := told_value _ 1 true rightModels
    have reads : instantiate ρ (instantiate (carry tellerTrue) nameOutput) =
        Assignment.compose (Assignment.compose ρ (laterCaptured tellerTrue))
          (ContextualComputedFreshFrame.includeSource tellerTrue.update) (.inr ()) :=
      ((congrArg (instantiate ρ) (instantiate_generator (carry tellerTrue) (.inr ()))).trans
        (instantiate_generator ρ (.inr (.inl (.inr ()))))).trans
      ((congrArg (instantiate (Assignment.compose ρ (laterCaptured tellerTrue)))
          (includeSource_apply tellerTrue (.inr ()))).trans
        ((instantiate_generator (Assignment.compose ρ (laterCaptured tellerTrue)) (.inl (.inr ()))).trans
          (instantiate_generator ρ (.inr (.inl (.inr ())))))).symm
    have clash := (reads.trans told).symm.trans same
    unfold bit at clash
    cases clash

/-- **Telling `X = true` is not conservative over the empty information.** -/
theorem teller_not_conservative :
    ¬ Conservative initial (problemOf initial tellerTrue.selection tellerTrue.rule) reader.toNative.information := by
  intro conservative
  obtain ⟨τ, solved, agree⟩ := conservative emptyFrame falseCandidate
    (fun _ member => absurd member List.not_mem_nil)
  rw [tellerTrue_problem] at solved
  have told := told_value τ 1 true solved
  have atName : τ (.inr ()) = falseCandidate (.inr ()) :=
    (instantiate_generator τ (.inr ())).symm.trans ((congrFun agree ()).trans (instantiate_generator falseCandidate (.inr ())))
  have clash := told.symm.trans atName
  unfold bit falseCandidate at clash
  cases clash

/-- **Positive control**: after the maker that tells nothing, the reader's snapshot keeps every
instance. -/
theorem snapshot_after_silent (pattern : Term (signature tiny emptyFrame) ([] : Ctx tiny) ()) :
    ContextualPublication.SourceInstances
        (reader.residualAt (LiveFiring.execution (maker_realized 1 none))).toNative.information
        (instantiate (carry (LiveFiring.execution (maker_realized 1 none))) nameOutput) emptyFrame pattern ↔
      ContextualPublication.SourceInstances reader.toNative.information nameOutput emptyFrame pattern := by
  have problem : problemOf initial (LiveFiring.execution (maker_realized 1 none)).selection
      (LiveFiring.execution (maker_realized 1 none)).rule = [] := by
    rw [(LiveFiring.execution_data (maker_realized 1 none)).1, (LiveFiring.execution_data (maker_realized 1 none)).2.1]
    rfl
  refine instances_after_iff _ reader (fun _ member => absurd member List.not_mem_nil) ?_ nameOutput _ pattern
  rw [problem]
  exact conservative_of_nil _

end Obstruction

end NativeSnapshot

#print axioms NativeSnapshot.conservative_of_nil
#print axioms NativeSnapshot.amalgamWide_carry
#print axioms NativeSnapshot.wideExtension_assignment
#print axioms NativeSnapshot.instances_of_after
#print axioms NativeSnapshot.instances_after_iff
#print axioms NativeSnapshot.snapshots_commute
#print axioms NativeSnapshot.snapshot_obstruction
#print axioms NativeSnapshot.teller_not_conservative
#print axioms NativeSnapshot.snapshot_after_silent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
